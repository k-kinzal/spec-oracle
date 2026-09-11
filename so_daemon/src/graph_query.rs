//! Storage-independent, read-only openCypher graph-pattern queries.
//!
//! The syntax is intentionally a subset of openCypher rather than a
//! spec-oracle-specific DSL. A query selects paths; callers project the union of
//! those paths into their own wire/domain graph. The parser is shared so the
//! Evidence graph and authored Specification graph can use the same language.

use std::collections::{BTreeMap, BTreeSet};

use sha2::{Digest, Sha256};
use thiserror::Error;
use tree_sitter::Node as SyntaxNode;

const MAX_EXPLICIT_STEPS: usize = 16;

#[derive(Clone, Debug, PartialEq)]
pub enum PropertyValue {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Null,
}

impl PropertyValue {
    fn as_string(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct QueryNode {
    pub id: String,
    pub labels: BTreeSet<String>,
    pub properties: BTreeMap<String, PropertyValue>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct QueryEdge {
    pub id: String,
    pub relation_type: String,
    pub source: String,
    pub target: String,
    pub properties: BTreeMap<String, PropertyValue>,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct PropertyGraph {
    pub nodes: BTreeMap<String, QueryNode>,
    pub edges: BTreeMap<String, QueryEdge>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryPath {
    pub id: String,
    pub node_ids: Vec<String>,
    pub edge_ids: Vec<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct QueryPage {
    pub paths: Vec<QueryPath>,
    pub node_ids: BTreeSet<String>,
    pub edge_ids: BTreeSet<String>,
    pub next_cursor: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphSchema {
    pub node_labels: BTreeSet<String>,
    pub relation_types: BTreeSet<String>,
    pub properties: BTreeSet<String>,
}

impl GraphSchema {
    pub fn new(
        node_labels: impl IntoIterator<Item = impl Into<String>>,
        relation_types: impl IntoIterator<Item = impl Into<String>>,
        properties: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        Self {
            node_labels: node_labels.into_iter().map(Into::into).collect(),
            relation_types: relation_types.into_iter().map(Into::into).collect(),
            properties: properties.into_iter().map(Into::into).collect(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Direction {
    Outgoing,
    Incoming,
    Undirected,
}

#[derive(Clone, Debug, PartialEq)]
struct NodePattern {
    variable: Option<String>,
    label: Option<String>,
    properties: BTreeMap<String, PropertyValue>,
}

#[derive(Clone, Debug, PartialEq)]
struct RelationshipPattern {
    variable: Option<String>,
    relation_types: BTreeSet<String>,
    direction: Direction,
    properties: BTreeMap<String, PropertyValue>,
}

#[derive(Clone, Debug, PartialEq)]
struct PathPattern {
    variable: String,
    nodes: Vec<NodePattern>,
    relationships: Vec<RelationshipPattern>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompareOp {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Clone, Debug, PartialEq)]
enum ValueExpression {
    Property { variable: String, property: String },
    Literal(PropertyValue),
}

#[derive(Clone, Debug, PartialEq)]
enum Predicate {
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Compare {
        left: ValueExpression,
        op: CompareOp,
        right: ValueExpression,
    },
    Contains {
        left: ValueExpression,
        right: ValueExpression,
    },
    StartsWith {
        left: ValueExpression,
        right: ValueExpression,
    },
    EndsWith {
        left: ValueExpression,
        right: ValueExpression,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct GraphQuery {
    path: PathPattern,
    predicate: Option<Predicate>,
    limit: Option<usize>,
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum GraphQueryError {
    #[error("invalid openCypher syntax near byte {byte}: {fragment}")]
    Syntax { byte: usize, fragment: String },
    #[error("only one read-only MATCH clause followed by RETURN is supported")]
    ReadOnlyMatch,
    #[error("MATCH must contain exactly one named path pattern, for example p=(a)-[r]->(b)")]
    OneNamedPath,
    #[error("RETURN must return the matched path variable '{0}'")]
    ReturnPath(String),
    #[error(
        "OPTIONAL MATCH, path search prefixes, and variable-length relationships are not supported"
    )]
    UnsupportedTraversal,
    #[error("a path may contain at most {MAX_EXPLICIT_STEPS} explicit relationship steps")]
    TooManySteps,
    #[error("unsupported openCypher expression '{0}'")]
    UnsupportedExpression(String),
    #[error("unknown node label '{0}' in this graph scope")]
    UnknownLabel(String),
    #[error("unknown relationship type '{0}' in this graph scope")]
    UnknownRelationType(String),
    #[error("unknown property '{0}' in this graph scope")]
    UnknownProperty(String),
    #[error("unbound or ambiguously typed variable '{0}'")]
    UnknownVariable(String),
    #[error("invalid integer LIMIT")]
    InvalidLimit,
}

impl GraphQuery {
    pub fn parse(source: &str) -> Result<Self, GraphQueryError> {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&tree_sitter_cypher::LANGUAGE.into())
            .expect("bundled Cypher grammar is loadable");
        let tree = parser
            .parse(source, None)
            .expect("tree-sitter returns a tree for finite input");
        let root = tree.root_node();
        if root.has_error() {
            let error = first_error(root).unwrap_or(root);
            let start = error.start_byte().min(source.len());
            let end = error.end_byte().min(source.len()).max(start);
            let fragment = source
                .get(start..end)
                .filter(|value| !value.is_empty())
                .unwrap_or("<end of query>")
                .to_string();
            return Err(GraphQueryError::Syntax {
                byte: start,
                fragment,
            });
        }

        let statements = direct_named(root, "statement");
        if statements.len() != 1 || root.named_child_count() != 1 {
            return Err(GraphQueryError::ReadOnlyMatch);
        }
        let statement = statements[0];
        let named: Vec<_> = named_children(statement).collect();
        let matches: Vec<_> = named
            .iter()
            .copied()
            .filter(|node| node.kind() == "match_clause")
            .collect();
        let returns: Vec<_> = named
            .iter()
            .copied()
            .filter(|node| node.kind() == "return_clause")
            .collect();
        if matches.len() != 1
            || returns.len() != 1
            || named
                .iter()
                .any(|node| !matches!(node.kind(), "match_clause" | "return_clause"))
        {
            return Err(GraphQueryError::ReadOnlyMatch);
        }
        let match_clause = matches[0];
        let match_text = text(match_clause, source);
        if starts_keyword(match_text, "OPTIONAL")
            || direct_named(match_clause, "path_search_prefix").len() > 0
        {
            return Err(GraphQueryError::UnsupportedTraversal);
        }
        let pattern = match_clause
            .child_by_field_name("pattern")
            .ok_or(GraphQueryError::OneNamedPath)?;
        let paths = direct_named(pattern, "path_pattern");
        if paths.len() != 1 {
            return Err(GraphQueryError::OneNamedPath);
        }
        let path_node = paths[0];
        let path_variable = path_node
            .child_by_field_name("variable")
            .map(|node| identifier(node, source))
            .transpose()?
            .ok_or(GraphQueryError::OneNamedPath)?;

        let mut node_patterns = Vec::new();
        let mut relationship_patterns = Vec::new();
        for child in named_children(path_node) {
            match child.kind() {
                "node_pattern" => node_patterns.push(parse_node_pattern(child, source)?),
                "relationship_pattern" => {
                    relationship_patterns.push(parse_relationship_pattern(child, source)?)
                }
                "quantified_path_primary" | "legacy_shortest_path_pattern" => {
                    return Err(GraphQueryError::UnsupportedTraversal)
                }
                _ => {}
            }
        }
        if node_patterns.is_empty()
            || node_patterns.len() != relationship_patterns.len().saturating_add(1)
        {
            return Err(GraphQueryError::OneNamedPath);
        }
        if relationship_patterns.len() > MAX_EXPLICIT_STEPS {
            return Err(GraphQueryError::TooManySteps);
        }

        let predicate = match_clause
            .child_by_field_name("where")
            .and_then(|where_clause| first_named(where_clause, "expression"))
            .map(|expression| parse_predicate(expression, source))
            .transpose()?;

        let return_clause = returns[0];
        let return_items = descendants(return_clause, "return_item");
        if return_items.len() != 1 {
            return Err(GraphQueryError::ReturnPath(path_variable));
        }
        let returned = first_named(return_items[0], "expression")
            .and_then(unwrap_expression)
            .filter(|node| matches!(node.kind(), "identifier" | "escaped_identifier"))
            .map(|node| identifier(node, source))
            .transpose()?;
        if returned.as_deref() != Some(path_variable.as_str()) {
            return Err(GraphQueryError::ReturnPath(path_variable));
        }

        let limit = descendants(return_clause, "limit_clause")
            .first()
            .map(|limit_clause| {
                descendants(*limit_clause, "integer_literal")
                    .first()
                    .and_then(|node| text(*node, source).replace('_', "").parse::<usize>().ok())
                    .filter(|value| *value > 0)
                    .ok_or(GraphQueryError::InvalidLimit)
            })
            .transpose()?;

        Ok(Self {
            path: PathPattern {
                variable: returned.expect("returned path checked above"),
                nodes: node_patterns,
                relationships: relationship_patterns,
            },
            predicate,
            limit,
        })
    }

    pub fn validate(&self, schema: &GraphSchema) -> Result<(), GraphQueryError> {
        let node_variables: BTreeSet<&str> = self
            .path
            .nodes
            .iter()
            .filter_map(|node| node.variable.as_deref())
            .collect();
        let edge_variables: BTreeSet<&str> = self
            .path
            .relationships
            .iter()
            .filter_map(|edge| edge.variable.as_deref())
            .collect();
        if let Some(variable) = node_variables.intersection(&edge_variables).next() {
            return Err(GraphQueryError::UnknownVariable((*variable).into()));
        }
        for node in &self.path.nodes {
            if let Some(label) = &node.label {
                if !schema.node_labels.contains(label) {
                    return Err(GraphQueryError::UnknownLabel(label.clone()));
                }
            }
            for property in node.properties.keys() {
                validate_property(property, schema)?;
            }
        }
        for relationship in &self.path.relationships {
            for relation_type in &relationship.relation_types {
                if !schema.relation_types.contains(relation_type) {
                    return Err(GraphQueryError::UnknownRelationType(relation_type.clone()));
                }
            }
            for property in relationship.properties.keys() {
                validate_property(property, schema)?;
            }
        }
        if let Some(predicate) = &self.predicate {
            validate_predicate(predicate, schema, &node_variables, &edge_variables)?;
        }
        Ok(())
    }

    pub fn execute(
        &self,
        graph: &PropertyGraph,
        after: Option<&str>,
        page_size: usize,
    ) -> QueryPage {
        let mut matches = Vec::new();
        let start = &self.path.nodes[0];
        for node in graph
            .nodes
            .values()
            .filter(|node| node_matches(start, node))
        {
            let mut binding = Binding::default();
            if !bind_node(&mut binding, start.variable.as_deref(), &node.id) {
                continue;
            }
            let mut node_ids = vec![node.id.clone()];
            let mut edge_ids = Vec::new();
            self.walk(
                graph,
                0,
                &mut binding,
                &mut node_ids,
                &mut edge_ids,
                &mut matches,
            );
        }
        matches.sort_by(|left, right| left.id.cmp(&right.id));
        matches.dedup_by(|left, right| left.id == right.id);
        if let Some(limit) = self.limit {
            matches.truncate(limit);
        }
        let mut page_matches: Vec<_> = matches
            .into_iter()
            .filter(|path| after.is_none_or(|cursor| path.id.as_str() > cursor))
            .take(page_size.saturating_add(1))
            .collect();
        let next_cursor = if page_matches.len() > page_size {
            page_matches.truncate(page_size);
            page_matches.last().map(|path| path.id.clone())
        } else {
            None
        };
        let mut page = QueryPage {
            paths: page_matches,
            next_cursor,
            ..QueryPage::default()
        };
        for path in &page.paths {
            page.node_ids.extend(path.node_ids.iter().cloned());
            page.edge_ids.extend(path.edge_ids.iter().cloned());
        }
        page
    }

    #[allow(clippy::too_many_arguments)]
    fn walk(
        &self,
        graph: &PropertyGraph,
        step: usize,
        binding: &mut Binding,
        node_ids: &mut Vec<String>,
        edge_ids: &mut Vec<String>,
        matches: &mut Vec<QueryPath>,
    ) {
        if step == self.path.relationships.len() {
            if self
                .predicate
                .as_ref()
                .is_none_or(|predicate| evaluate_predicate(predicate, binding, graph))
            {
                matches.push(QueryPath {
                    id: path_id(node_ids, edge_ids),
                    node_ids: node_ids.clone(),
                    edge_ids: edge_ids.clone(),
                });
            }
            return;
        }

        let current = node_ids
            .last()
            .expect("a path always has a current node")
            .clone();
        let relationship = &self.path.relationships[step];
        let next_pattern = &self.path.nodes[step + 1];
        for edge in graph.edges.values() {
            if edge_ids.contains(&edge.id) || !edge_matches(relationship, edge) {
                continue;
            }
            let next = match relationship.direction {
                Direction::Outgoing if edge.source == current => Some(edge.target.as_str()),
                Direction::Incoming if edge.target == current => Some(edge.source.as_str()),
                Direction::Undirected if edge.source == current => Some(edge.target.as_str()),
                Direction::Undirected if edge.target == current => Some(edge.source.as_str()),
                _ => None,
            };
            let Some(next) = next else {
                continue;
            };
            let Some(next_node) = graph.nodes.get(next) else {
                continue;
            };
            if !node_matches(next_pattern, next_node) {
                continue;
            }
            let mut next_binding = binding.clone();
            if !bind_edge(
                &mut next_binding,
                relationship.variable.as_deref(),
                &edge.id,
            ) || !bind_node(
                &mut next_binding,
                next_pattern.variable.as_deref(),
                &next_node.id,
            ) {
                continue;
            }
            edge_ids.push(edge.id.clone());
            node_ids.push(next_node.id.clone());
            self.walk(
                graph,
                step + 1,
                &mut next_binding,
                node_ids,
                edge_ids,
                matches,
            );
            node_ids.pop();
            edge_ids.pop();
        }
    }
}

#[derive(Clone, Debug, Default)]
struct Binding {
    nodes: BTreeMap<String, String>,
    edges: BTreeMap<String, String>,
}

fn bind_node(binding: &mut Binding, variable: Option<&str>, id: &str) -> bool {
    let Some(variable) = variable else {
        return true;
    };
    match binding.nodes.get(variable) {
        Some(bound) => bound == id,
        None => {
            binding.nodes.insert(variable.into(), id.into());
            true
        }
    }
}

fn bind_edge(binding: &mut Binding, variable: Option<&str>, id: &str) -> bool {
    let Some(variable) = variable else {
        return true;
    };
    match binding.edges.get(variable) {
        Some(bound) => bound == id,
        None => {
            binding.edges.insert(variable.into(), id.into());
            true
        }
    }
}

fn node_matches(pattern: &NodePattern, node: &QueryNode) -> bool {
    pattern
        .label
        .as_ref()
        .is_none_or(|label| node.labels.contains(label))
        && properties_match(&pattern.properties, &node.properties)
}

fn edge_matches(pattern: &RelationshipPattern, edge: &QueryEdge) -> bool {
    (pattern.relation_types.is_empty() || pattern.relation_types.contains(&edge.relation_type))
        && properties_match(&pattern.properties, &edge.properties)
}

fn properties_match(
    required: &BTreeMap<String, PropertyValue>,
    actual: &BTreeMap<String, PropertyValue>,
) -> bool {
    required
        .iter()
        .all(|(key, value)| actual.get(key).is_some_and(|actual| actual == value))
}

fn path_id(nodes: &[String], edges: &[String]) -> String {
    let mut digest = Sha256::new();
    for node in nodes {
        digest.update(b"n:");
        digest.update(node.as_bytes());
        digest.update(b"\0");
    }
    for edge in edges {
        digest.update(b"e:");
        digest.update(edge.as_bytes());
        digest.update(b"\0");
    }
    format!("path-{:x}", digest.finalize())
}

fn evaluate_predicate(predicate: &Predicate, binding: &Binding, graph: &PropertyGraph) -> bool {
    match predicate {
        Predicate::And(left, right) => {
            evaluate_predicate(left, binding, graph) && evaluate_predicate(right, binding, graph)
        }
        Predicate::Or(left, right) => {
            evaluate_predicate(left, binding, graph) || evaluate_predicate(right, binding, graph)
        }
        Predicate::Compare { left, op, right } => {
            let left = evaluate_value(left, binding, graph);
            let right = evaluate_value(right, binding, graph);
            compare(left.as_ref(), *op, right.as_ref())
        }
        Predicate::Contains { left, right } => {
            string_predicate(left, right, binding, graph, |a, b| a.contains(b))
        }
        Predicate::StartsWith { left, right } => {
            string_predicate(left, right, binding, graph, |a, b| a.starts_with(b))
        }
        Predicate::EndsWith { left, right } => {
            string_predicate(left, right, binding, graph, |a, b| a.ends_with(b))
        }
    }
}

fn string_predicate(
    left: &ValueExpression,
    right: &ValueExpression,
    binding: &Binding,
    graph: &PropertyGraph,
    predicate: impl FnOnce(&str, &str) -> bool,
) -> bool {
    let left = evaluate_value(left, binding, graph);
    let right = evaluate_value(right, binding, graph);
    match (
        left.as_ref().and_then(PropertyValue::as_string),
        right.as_ref().and_then(PropertyValue::as_string),
    ) {
        (Some(left), Some(right)) => predicate(left, right),
        _ => false,
    }
}

fn evaluate_value(
    expression: &ValueExpression,
    binding: &Binding,
    graph: &PropertyGraph,
) -> Option<PropertyValue> {
    match expression {
        ValueExpression::Literal(value) => Some(value.clone()),
        ValueExpression::Property { variable, property } => {
            if let Some(node_id) = binding.nodes.get(variable) {
                return graph
                    .nodes
                    .get(node_id)
                    .and_then(|node| node.properties.get(property))
                    .cloned();
            }
            binding.edges.get(variable).and_then(|edge_id| {
                graph
                    .edges
                    .get(edge_id)
                    .and_then(|edge| edge.properties.get(property))
                    .cloned()
            })
        }
    }
}

fn compare(left: Option<&PropertyValue>, op: CompareOp, right: Option<&PropertyValue>) -> bool {
    match op {
        CompareOp::Equal => left == right,
        CompareOp::NotEqual => left != right,
        CompareOp::Less | CompareOp::LessEqual | CompareOp::Greater | CompareOp::GreaterEqual => {
            let ordering = match (left, right) {
                (Some(PropertyValue::Integer(left)), Some(PropertyValue::Integer(right))) => {
                    left.partial_cmp(right)
                }
                (Some(PropertyValue::Float(left)), Some(PropertyValue::Float(right))) => {
                    left.partial_cmp(right)
                }
                (Some(PropertyValue::String(left)), Some(PropertyValue::String(right))) => {
                    left.partial_cmp(right)
                }
                _ => None,
            };
            ordering.is_some_and(|ordering| match op {
                CompareOp::Less => ordering.is_lt(),
                CompareOp::LessEqual => ordering.is_le(),
                CompareOp::Greater => ordering.is_gt(),
                CompareOp::GreaterEqual => ordering.is_ge(),
                _ => unreachable!(),
            })
        }
    }
}

fn validate_property(property: &str, schema: &GraphSchema) -> Result<(), GraphQueryError> {
    if schema.properties.contains(property) {
        Ok(())
    } else {
        Err(GraphQueryError::UnknownProperty(property.into()))
    }
}

fn validate_predicate(
    predicate: &Predicate,
    schema: &GraphSchema,
    node_variables: &BTreeSet<&str>,
    edge_variables: &BTreeSet<&str>,
) -> Result<(), GraphQueryError> {
    match predicate {
        Predicate::And(left, right) | Predicate::Or(left, right) => {
            validate_predicate(left, schema, node_variables, edge_variables)?;
            validate_predicate(right, schema, node_variables, edge_variables)
        }
        Predicate::Compare { left, right, .. }
        | Predicate::Contains { left, right }
        | Predicate::StartsWith { left, right }
        | Predicate::EndsWith { left, right } => {
            validate_value(left, schema, node_variables, edge_variables)?;
            validate_value(right, schema, node_variables, edge_variables)
        }
    }
}

fn validate_value(
    expression: &ValueExpression,
    schema: &GraphSchema,
    node_variables: &BTreeSet<&str>,
    edge_variables: &BTreeSet<&str>,
) -> Result<(), GraphQueryError> {
    match expression {
        ValueExpression::Property { variable, property } => {
            if !node_variables.contains(variable.as_str())
                && !edge_variables.contains(variable.as_str())
            {
                return Err(GraphQueryError::UnknownVariable(variable.clone()));
            }
            validate_property(property, schema)
        }
        ValueExpression::Literal(_) => Ok(()),
    }
}

fn parse_node_pattern(node: SyntaxNode<'_>, source: &str) -> Result<NodePattern, GraphQueryError> {
    let variable = node
        .child_by_field_name("variable")
        .map(|node| identifier(node, source))
        .transpose()?;
    let label = node
        .child_by_field_name("label")
        .map(|node| parse_single_label(node, source))
        .transpose()?;
    let properties = node
        .child_by_field_name("properties")
        .map(|node| parse_property_map(node, source))
        .transpose()?
        .unwrap_or_default();
    if node.child_by_field_name("where").is_some() {
        return Err(GraphQueryError::UnsupportedExpression(
            text(node, source).into(),
        ));
    }
    Ok(NodePattern {
        variable,
        label,
        properties,
    })
}

fn parse_relationship_pattern(
    node: SyntaxNode<'_>,
    source: &str,
) -> Result<RelationshipPattern, GraphQueryError> {
    let raw = text(node, source).trim();
    let direction = if raw.starts_with("<-") && raw.ends_with("->") {
        return Err(GraphQueryError::UnsupportedTraversal);
    } else if raw.starts_with("<-") {
        Direction::Incoming
    } else if raw.ends_with("->") {
        Direction::Outgoing
    } else {
        Direction::Undirected
    };
    let body = first_named(node, "relationship_body");
    let variable = body
        .and_then(|node| node.child_by_field_name("variable"))
        .map(|node| identifier(node, source))
        .transpose()?;
    let relation_types = body
        .and_then(|node| node.child_by_field_name("label"))
        .map(|node| parse_relation_types(node, source))
        .transpose()?
        .unwrap_or_default();
    let properties = body
        .and_then(|node| node.child_by_field_name("properties"))
        .map(|node| parse_property_map(node, source))
        .transpose()?
        .unwrap_or_default();
    if body.is_some_and(|node| {
        node.child_by_field_name("length").is_some() || node.child_by_field_name("where").is_some()
    }) {
        return Err(GraphQueryError::UnsupportedTraversal);
    }
    Ok(RelationshipPattern {
        variable,
        relation_types,
        direction,
        properties,
    })
}

fn parse_single_label(node: SyntaxNode<'_>, source: &str) -> Result<String, GraphQueryError> {
    let raw = text(node, source);
    if raw.contains('|') || raw.contains('&') || raw.contains('!') {
        return Err(GraphQueryError::UnsupportedExpression(raw.into()));
    }
    let labels = descendants(node, "identifier");
    if labels.len() != 1 {
        return Err(GraphQueryError::UnsupportedExpression(raw.into()));
    }
    identifier(labels[0], source)
}

fn parse_relation_types(
    node: SyntaxNode<'_>,
    source: &str,
) -> Result<BTreeSet<String>, GraphQueryError> {
    let raw = text(node, source);
    if raw.contains('&') || raw.contains('!') {
        return Err(GraphQueryError::UnsupportedExpression(raw.into()));
    }
    descendants(node, "identifier")
        .into_iter()
        .map(|node| identifier(node, source))
        .collect()
}

fn parse_property_map(
    node: SyntaxNode<'_>,
    source: &str,
) -> Result<BTreeMap<String, PropertyValue>, GraphQueryError> {
    if node.kind() == "parameter" {
        return Err(GraphQueryError::UnsupportedExpression(
            text(node, source).into(),
        ));
    }
    let mut properties = BTreeMap::new();
    for field in direct_named(node, "property_key_value") {
        let mut children = named_children(field);
        let key = children
            .next()
            .map(|node| identifier(node, source))
            .transpose()?
            .ok_or_else(|| GraphQueryError::UnsupportedExpression(text(field, source).into()))?;
        let expression = children
            .find(|node| node.kind() == "expression")
            .ok_or_else(|| GraphQueryError::UnsupportedExpression(text(field, source).into()))?;
        let value = parse_literal(expression, source)?;
        properties.insert(key, value);
    }
    Ok(properties)
}

fn parse_predicate(node: SyntaxNode<'_>, source: &str) -> Result<Predicate, GraphQueryError> {
    let node = unwrap_expression(node)
        .ok_or_else(|| GraphQueryError::UnsupportedExpression(text(node, source).into()))?;
    match node.kind() {
        "binary_expression" => {
            let left = node
                .child_by_field_name("left")
                .ok_or_else(|| unsupported(node, source))?;
            let right = node
                .child_by_field_name("right")
                .ok_or_else(|| unsupported(node, source))?;
            let operator = node
                .child_by_field_name("operator")
                .map(|operator| text(operator, source).to_ascii_uppercase())
                .ok_or_else(|| unsupported(node, source))?;
            match operator.as_str() {
                "AND" => Ok(Predicate::And(
                    Box::new(parse_predicate(left, source)?),
                    Box::new(parse_predicate(right, source)?),
                )),
                "OR" => Ok(Predicate::Or(
                    Box::new(parse_predicate(left, source)?),
                    Box::new(parse_predicate(right, source)?),
                )),
                "=" | "<>" | "<" | "<=" | ">" | ">=" => Ok(Predicate::Compare {
                    left: parse_value(left, source)?,
                    op: match operator.as_str() {
                        "=" => CompareOp::Equal,
                        "<>" => CompareOp::NotEqual,
                        "<" => CompareOp::Less,
                        "<=" => CompareOp::LessEqual,
                        ">" => CompareOp::Greater,
                        ">=" => CompareOp::GreaterEqual,
                        _ => unreachable!(),
                    },
                    right: parse_value(right, source)?,
                }),
                _ => Err(unsupported(node, source)),
            }
        }
        "contains_expression" | "starts_with_expression" | "ends_with_expression" => {
            let expressions = direct_named(node, "expression");
            if expressions.len() != 2 {
                return Err(unsupported(node, source));
            }
            let left = parse_value(expressions[0], source)?;
            let right = parse_value(expressions[1], source)?;
            Ok(match node.kind() {
                "contains_expression" => Predicate::Contains { left, right },
                "starts_with_expression" => Predicate::StartsWith { left, right },
                "ends_with_expression" => Predicate::EndsWith { left, right },
                _ => unreachable!(),
            })
        }
        _ => Err(unsupported(node, source)),
    }
}

fn parse_value(node: SyntaxNode<'_>, source: &str) -> Result<ValueExpression, GraphQueryError> {
    let node = unwrap_expression(node)
        .ok_or_else(|| GraphQueryError::UnsupportedExpression(text(node, source).into()))?;
    if node.kind() == "property_access" {
        let object = node
            .child_by_field_name("object")
            .and_then(unwrap_expression)
            .filter(|node| matches!(node.kind(), "identifier" | "escaped_identifier"))
            .ok_or_else(|| unsupported(node, source))?;
        let property = node
            .child_by_field_name("property")
            .ok_or_else(|| unsupported(node, source))?;
        return Ok(ValueExpression::Property {
            variable: identifier(object, source)?,
            property: identifier(property, source)?,
        });
    }
    parse_literal(node, source).map(ValueExpression::Literal)
}

fn parse_literal(node: SyntaxNode<'_>, source: &str) -> Result<PropertyValue, GraphQueryError> {
    let node = unwrap_expression(node)
        .ok_or_else(|| GraphQueryError::UnsupportedExpression(text(node, source).into()))?;
    let raw = text(node, source);
    match node.kind() {
        "string_literal" => Ok(PropertyValue::String(unescape_string(raw))),
        "integer_literal" => raw
            .replace('_', "")
            .parse()
            .map(PropertyValue::Integer)
            .map_err(|_| unsupported(node, source)),
        "float_literal" => raw
            .trim_end_matches(['f', 'F', 'd', 'D'])
            .replace('_', "")
            .parse()
            .map(PropertyValue::Float)
            .map_err(|_| unsupported(node, source)),
        "boolean_literal" => Ok(PropertyValue::Boolean(raw.eq_ignore_ascii_case("true"))),
        "null_literal" => Ok(PropertyValue::Null),
        _ => Err(unsupported(node, source)),
    }
}

fn unescape_string(raw: &str) -> String {
    let inner = raw
        .strip_prefix(['"', '\''])
        .and_then(|value| value.strip_suffix(['"', '\'']))
        .unwrap_or(raw);
    let mut result = String::with_capacity(inner.len());
    let mut escaped = false;
    for character in inner.chars() {
        if escaped {
            result.push(match character {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                other => other,
            });
            escaped = false;
        } else if character == '\\' {
            escaped = true;
        } else {
            result.push(character);
        }
    }
    if escaped {
        result.push('\\');
    }
    result
}

fn unsupported(node: SyntaxNode<'_>, source: &str) -> GraphQueryError {
    GraphQueryError::UnsupportedExpression(text(node, source).into())
}

fn identifier(node: SyntaxNode<'_>, source: &str) -> Result<String, GraphQueryError> {
    match node.kind() {
        "identifier" => Ok(text(node, source).into()),
        "escaped_identifier" => Ok(text(node, source)
            .strip_prefix('`')
            .and_then(|value| value.strip_suffix('`'))
            .unwrap_or(text(node, source))
            .into()),
        _ => Err(unsupported(node, source)),
    }
}

fn first_error(node: SyntaxNode<'_>) -> Option<SyntaxNode<'_>> {
    if node.is_error() || node.is_missing() {
        return Some(node);
    }
    named_children(node).find_map(first_error)
}

fn text<'a>(node: SyntaxNode<'_>, source: &'a str) -> &'a str {
    source.get(node.byte_range()).unwrap_or_default()
}

fn starts_keyword(source: &str, keyword: &str) -> bool {
    source
        .trim_start()
        .get(..keyword.len())
        .is_some_and(|prefix| prefix.eq_ignore_ascii_case(keyword))
}

fn named_children(node: SyntaxNode<'_>) -> impl Iterator<Item = SyntaxNode<'_>> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor)
        .collect::<Vec<_>>()
        .into_iter()
}

fn direct_named<'tree>(node: SyntaxNode<'tree>, kind: &str) -> Vec<SyntaxNode<'tree>> {
    named_children(node)
        .filter(|child| child.kind() == kind)
        .collect()
}

fn first_named<'tree>(node: SyntaxNode<'tree>, kind: &str) -> Option<SyntaxNode<'tree>> {
    named_children(node).find(|child| child.kind() == kind)
}

fn descendants<'tree>(node: SyntaxNode<'tree>, kind: &str) -> Vec<SyntaxNode<'tree>> {
    let mut found = Vec::new();
    let mut stack = vec![node];
    while let Some(current) = stack.pop() {
        for child in named_children(current) {
            if child.kind() == kind {
                found.push(child);
            }
            stack.push(child);
        }
    }
    found.sort_by_key(SyntaxNode::start_byte);
    found
}

fn unwrap_expression(mut node: SyntaxNode<'_>) -> Option<SyntaxNode<'_>> {
    while node.kind() == "expression" {
        node = named_children(node).next()?;
    }
    Some(node)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(id: &str, label: &str, properties: &[(&str, &str)]) -> QueryNode {
        let mut values = BTreeMap::from([("id".into(), PropertyValue::String(id.into()))]);
        values.extend(properties.iter().map(|(key, value)| {
            (
                (*key).to_string(),
                PropertyValue::String((*value).to_string()),
            )
        }));
        QueryNode {
            id: id.into(),
            labels: BTreeSet::from([label.into()]),
            properties: values,
        }
    }

    fn edge(id: &str, relation_type: &str, source: &str, target: &str) -> QueryEdge {
        QueryEdge {
            id: id.into(),
            relation_type: relation_type.into(),
            source: source.into(),
            target: target.into(),
            properties: BTreeMap::from([
                ("id".into(), PropertyValue::String(id.into())),
                (
                    "kind".into(),
                    PropertyValue::String(relation_type.to_ascii_lowercase()),
                ),
            ]),
        }
    }

    fn schema() -> GraphSchema {
        GraphSchema::new(
            ["Evidence", "Specification"],
            ["EVIDENCE_AFFIRMS", "EVIDENCE_DENIES"],
            ["id", "kind", "locator", "statement"],
        )
    }

    #[test]
    fn parses_and_executes_a_multi_hop_open_cypher_path() {
        let query = GraphQuery::parse(
            "MATCH p=(new:Evidence)-[:EVIDENCE_DENIES]->(old:Evidence) \
             -[:EVIDENCE_AFFIRMS]->(spec:Specification) \
             WHERE new.kind = 'testimonial' RETURN p",
        )
        .unwrap();
        query.validate(&schema()).unwrap();
        let graph = PropertyGraph {
            nodes: [
                node("new", "Evidence", &[("kind", "testimonial")]),
                node("old", "Evidence", &[("kind", "assertoric")]),
                node("spec", "Specification", &[("statement", "current")]),
            ]
            .into_iter()
            .map(|node| (node.id.clone(), node))
            .collect(),
            edges: [
                edge("denies", "EVIDENCE_DENIES", "new", "old"),
                edge("affirms", "EVIDENCE_AFFIRMS", "old", "spec"),
            ]
            .into_iter()
            .map(|edge| (edge.id.clone(), edge))
            .collect(),
        };
        let page = query.execute(&graph, None, 100);
        assert_eq!(page.paths.len(), 1);
        assert_eq!(page.paths[0].node_ids, ["new", "old", "spec"]);
        assert_eq!(page.paths[0].edge_ids, ["denies", "affirms"]);
    }

    #[test]
    fn supports_relationship_type_unions_directions_inline_properties_and_limit() {
        let query = GraphQuery::parse(
            "MATCH p=(target:Evidence)<-[r:EVIDENCE_AFFIRMS|EVIDENCE_DENIES]\
             -(source:Evidence {kind:'testimonial'}) RETURN p LIMIT 1",
        )
        .unwrap();
        query.validate(&schema()).unwrap();
        assert_eq!(query.limit, Some(1));
        assert_eq!(query.path.relationships[0].direction, Direction::Incoming);
        assert_eq!(query.path.relationships[0].relation_types.len(), 2);
    }

    #[test]
    fn rejects_mutation_unnamed_paths_and_unknown_schema_names() {
        assert_eq!(
            GraphQuery::parse("MATCH (e:Evidence) DELETE e"),
            Err(GraphQueryError::ReadOnlyMatch)
        );
        assert_eq!(
            GraphQuery::parse("MATCH (e:Evidence) RETURN e"),
            Err(GraphQueryError::OneNamedPath)
        );
        let query =
            GraphQuery::parse("MATCH p=(e:Evidence)-[:MADE_UP]->(s:Specification) RETURN p")
                .unwrap();
        assert_eq!(
            query.validate(&schema()),
            Err(GraphQueryError::UnknownRelationType("MADE_UP".into()))
        );
        let query =
            GraphQuery::parse("MATCH p=(e:Evidence) WHERE missing.id = 'x' RETURN p").unwrap();
        assert_eq!(
            query.validate(&schema()),
            Err(GraphQueryError::UnknownVariable("missing".into()))
        );
    }

    #[test]
    fn pages_deterministically_over_returned_paths() {
        let query = GraphQuery::parse(
            "MATCH p=(e:Evidence)-[:EVIDENCE_AFFIRMS]->(s:Specification) RETURN p",
        )
        .unwrap();
        let graph = PropertyGraph {
            nodes: [
                node("a", "Evidence", &[]),
                node("b", "Evidence", &[]),
                node("s", "Specification", &[]),
            ]
            .into_iter()
            .map(|node| (node.id.clone(), node))
            .collect(),
            edges: [
                edge("a-s", "EVIDENCE_AFFIRMS", "a", "s"),
                edge("b-s", "EVIDENCE_AFFIRMS", "b", "s"),
            ]
            .into_iter()
            .map(|edge| (edge.id.clone(), edge))
            .collect(),
        };
        let first = query.execute(&graph, None, 1);
        assert_eq!(first.paths.len(), 1);
        let second = query.execute(&graph, first.next_cursor.as_deref(), 1);
        assert_eq!(second.paths.len(), 1);
        assert_ne!(first.paths[0].id, second.paths[0].id);
        assert!(second.next_cursor.is_none());
    }
}
