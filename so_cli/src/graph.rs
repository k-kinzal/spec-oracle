//! Static terminal rendering for the one specification graph.
//!
//! Pagination is deliberately absent from this model: the caller combines all
//! wire pages first, then hands the resulting topology here. The layout is only
//! a presentation choice and never introduces a domain root or another graph.

use std::collections::{BTreeMap, HashMap};

use ratatui::buffer::Buffer;
use ratatui::layout::Rect;
use ratatui::style::Color;
use ratatui::symbols::Marker;
use ratatui::widgets::canvas::{Canvas, Line};
use ratatui::widgets::Widget;

use so_protocol::pb;

const MIN_WIDTH: u16 = 40;
const DEFAULT_WIDTH: u16 = 120;
const SLOT_WIDTH: u16 = 30;
const ROW_HEIGHT: u16 = 4;
const MAX_LABEL_CHARS: usize = 23;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NodeKind {
    Specification,
    Term,
    Evidence,
    Assumption,
    Guarantee,
    Contract,
    Entity,
    Behavior,
}

#[derive(Debug)]
struct Node {
    id: String,
    display_id: String,
    label: String,
    kind: NodeKind,
    current: bool,
    evaluation_state: String,
    policy_version: String,
    support_score: i32,
    structural_score: i32,
    evidence_score: i32,
    conflict_pressure: i32,
    contributions: Vec<Contribution>,
    exclusions: Vec<Exclusion>,
}

#[derive(Debug)]
struct Contribution {
    kind: String,
    points: i32,
    edge_id: String,
    detail: String,
}

#[derive(Debug)]
struct Exclusion {
    kind: String,
    competing_node_id: Option<String>,
    detail: String,
}

#[derive(Debug)]
struct Edge {
    source: usize,
    target: usize,
    relied: Option<usize>,
    family: String,
    kind: String,
    source_role: String,
    target_role: String,
    directed: bool,
    current: bool,
}

/// The complete topology collected by one `spec graph` invocation.
#[derive(Debug)]
pub(crate) struct Graph {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    specification_count: usize,
    current_specification_count: usize,
    term_count: usize,
    evidence_count: usize,
    assumption_count: usize,
    guarantee_count: usize,
    contract_count: usize,
    entity_count: usize,
    behavior_count: usize,
    scope: GraphScope,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GraphScope {
    Population,
    Current,
    Ledger,
}

impl Graph {
    pub(crate) fn from_wire(
        specifications: impl IntoIterator<Item = pb::Node>,
        terms: impl IntoIterator<Item = pb::TermNode>,
        derived: impl IntoIterator<Item = pb::DerivedNode>,
        edges: impl IntoIterator<Item = pb::Edge>,
    ) -> Result<Self, String> {
        let mut nodes_by_id = BTreeMap::new();
        let mut specification_count = 0;
        let mut current_specification_count = 0;
        let mut term_count = 0;
        let mut evidence_count = 0;
        let mut assumption_count = 0;
        let mut guarantee_count = 0;
        let mut contract_count = 0;
        let mut entity_count = 0;
        let mut behavior_count = 0;

        for specification in specifications {
            let selection = specification.selection.as_ref();
            let current = selection.is_none_or(|view| view.current);
            let node = Node {
                id: specification.id.clone(),
                display_id: String::new(),
                label: specification.statement,
                kind: NodeKind::Specification,
                current,
                evaluation_state: selection.map_or_else(
                    || {
                        if current {
                            "current".into()
                        } else {
                            "receded".into()
                        }
                    },
                    |view| view.evaluation_state.clone(),
                ),
                policy_version: selection
                    .map_or_else(String::new, |view| view.policy_version.clone()),
                support_score: selection.map_or(0, |view| view.support_score),
                structural_score: selection.map_or(0, |view| view.structural_score),
                evidence_score: selection.map_or(0, |view| view.evidence_score),
                conflict_pressure: selection.map_or(0, |view| view.conflict_pressure),
                contributions: selection.map_or_else(Vec::new, |view| {
                    view.contributions
                        .iter()
                        .map(|contribution| Contribution {
                            kind: contribution.kind.clone(),
                            points: contribution.points,
                            edge_id: contribution.edge_id.clone(),
                            detail: contribution.detail.clone(),
                        })
                        .collect()
                }),
                exclusions: selection.map_or_else(Vec::new, |view| {
                    view.exclusions
                        .iter()
                        .map(|exclusion| Exclusion {
                            kind: exclusion.kind.clone(),
                            competing_node_id: exclusion.competing_node_id.clone(),
                            detail: exclusion.detail.clone(),
                        })
                        .collect()
                }),
            };
            if nodes_by_id.insert(specification.id, node).is_some() {
                return Err("the graph contains a duplicate Node id".to_string());
            }
            specification_count += 1;
            current_specification_count += usize::from(current);
        }
        for term in terms {
            let node = Node {
                id: term.id.clone(),
                display_id: String::new(),
                label: term.form,
                kind: NodeKind::Term,
                current: true,
                evaluation_state: String::new(),
                policy_version: String::new(),
                support_score: 0,
                structural_score: 0,
                evidence_score: 0,
                conflict_pressure: 0,
                contributions: Vec::new(),
                exclusions: Vec::new(),
            };
            if nodes_by_id.insert(term.id, node).is_some() {
                return Err("Specification and Term Node ids must be disjoint".to_string());
            }
            term_count += 1;
        }
        for derived in derived {
            let (kind, label) = match derived.value {
                Some(pb::derived_node::Value::Evidence(value)) => {
                    evidence_count += 1;
                    let hash = value
                        .evidence
                        .and_then(|evidence| evidence.snapshot)
                        .map(|snapshot| snapshot.content_hash)
                        .unwrap_or_default();
                    (
                        NodeKind::Evidence,
                        format!("evidence {}", truncate(&hash, 12)),
                    )
                }
                Some(pb::derived_node::Value::Assumption(value)) => {
                    assumption_count += 1;
                    (NodeKind::Assumption, value.expression)
                }
                Some(pb::derived_node::Value::Guarantee(value)) => {
                    guarantee_count += 1;
                    (NodeKind::Guarantee, value.expression)
                }
                Some(pb::derived_node::Value::Contract(value)) => {
                    contract_count += 1;
                    (
                        NodeKind::Contract,
                        format!("{} A/G contract", value.operation),
                    )
                }
                Some(pb::derived_node::Value::Entity(value)) => {
                    entity_count += 1;
                    (NodeKind::Entity, value.display)
                }
                Some(pb::derived_node::Value::Behavior(_)) => {
                    behavior_count += 1;
                    (NodeKind::Behavior, "operational behavior".into())
                }
                None => return Err(format!("Derived Node {} has no value", derived.id)),
            };
            let node = Node {
                id: derived.id.clone(),
                display_id: String::new(),
                label,
                kind,
                current: true,
                evaluation_state: String::new(),
                policy_version: String::new(),
                support_score: 0,
                structural_score: 0,
                evidence_score: 0,
                conflict_pressure: 0,
                contributions: Vec::new(),
                exclusions: Vec::new(),
            };
            if nodes_by_id.insert(derived.id, node).is_some() {
                return Err("graph Node ids must be globally unique".to_string());
            }
        }

        let mut nodes: Vec<Node> = nodes_by_id.into_values().collect();
        let mut specification_number = 0;
        let mut term_number = 0;
        let mut evidence_number = 0;
        let mut assumption_number = 0;
        let mut guarantee_number = 0;
        let mut contract_number = 0;
        let mut entity_number = 0;
        let mut behavior_number = 0;
        for node in &mut nodes {
            node.display_id = match node.kind {
                NodeKind::Specification => {
                    specification_number += 1;
                    format!("S{specification_number:02}")
                }
                NodeKind::Term => {
                    term_number += 1;
                    format!("T{term_number:02}")
                }
                NodeKind::Evidence => {
                    evidence_number += 1;
                    format!("E{evidence_number:02}")
                }
                NodeKind::Assumption => {
                    assumption_number += 1;
                    format!("A{assumption_number:02}")
                }
                NodeKind::Guarantee => {
                    guarantee_number += 1;
                    format!("G{guarantee_number:02}")
                }
                NodeKind::Contract => {
                    contract_number += 1;
                    format!("C{contract_number:02}")
                }
                NodeKind::Entity => {
                    entity_number += 1;
                    format!("N{entity_number:02}")
                }
                NodeKind::Behavior => {
                    behavior_number += 1;
                    format!("B{behavior_number:02}")
                }
            };
        }
        let index: HashMap<&str, usize> = nodes
            .iter()
            .enumerate()
            .map(|(position, node)| (node.id.as_str(), position))
            .collect();
        let mut graph_edges = Vec::new();
        for edge in edges {
            let source = index.get(edge.source.as_str()).copied().ok_or_else(|| {
                format!(
                    "Edge {} refers to unavailable source Node {}",
                    edge.id, edge.source
                )
            })?;
            let target = index.get(edge.target.as_str()).copied().ok_or_else(|| {
                format!(
                    "Edge {} refers to unavailable target Node {}",
                    edge.id, edge.target
                )
            })?;
            let relied = edge
                .relied_spec_id
                .as_deref()
                .map(|id| {
                    index.get(id).copied().ok_or_else(|| {
                        format!("Edge {} refers to unavailable relied Node {}", edge.id, id)
                    })
                })
                .transpose()?;
            let (kind, directed) = edge_kind(edge.kind);
            graph_edges.push(Edge {
                source,
                target,
                relied,
                family: edge_family(edge.family).to_string(),
                kind: kind.to_string(),
                source_role: endpoint_role(edge.source_role).to_string(),
                target_role: endpoint_role(edge.target_role).to_string(),
                directed,
                current: edge.current,
            });
        }

        Ok(Self {
            nodes,
            edges: graph_edges,
            specification_count,
            current_specification_count,
            term_count,
            evidence_count,
            assumption_count,
            guarantee_count,
            contract_count,
            entity_count,
            behavior_count,
            scope: GraphScope::Population,
        })
    }

    pub(crate) fn with_scope(mut self, scope: GraphScope) -> Self {
        self.scope = scope;
        self
    }

    pub(crate) fn render(&self, requested_width: Option<u16>) -> String {
        let width = requested_width
            .or_else(terminal_width)
            .unwrap_or(DEFAULT_WIDTH)
            .max(MIN_WIDTH);
        let current_edge_count = self.edges.iter().filter(|edge| edge.current).count();
        let mut output = match self.scope {
            GraphScope::Population => format!(
                "Specification graph — {} current / {} candidate specification(s), {} term(s), {} evidence, {} assumption(s), {} guarantee(s), {} contract(s), {} entity kind(s), {} behavior(s), {} edge(s)\n",
                self.current_specification_count,
                self.specification_count,
                self.term_count,
                self.evidence_count,
                self.assumption_count,
                self.guarantee_count,
                self.contract_count,
                self.entity_count,
                self.behavior_count,
                self.edges.len()
            ),
            GraphScope::Current => format!(
                "Current specification graph — {} specification(s), {} term(s), {} evidence, {} assumption(s), {} guarantee(s), {} contract(s), {} entity kind(s), {} behavior(s), {} relationship(s)\n",
                self.specification_count,
                self.term_count,
                self.evidence_count,
                self.assumption_count,
                self.guarantee_count,
                self.contract_count,
                self.entity_count,
                self.behavior_count,
                self.edges.len()
            ),
            GraphScope::Ledger => format!(
                "Ledger graph — {} current / {} specification(s), {} term(s), {} evidence, {} assumption(s), {} guarantee(s), {} contract(s), {} entity kind(s), {} behavior(s), {} current / {} recorded edge(s)\n",
                self.current_specification_count,
                self.specification_count,
                self.term_count,
                self.evidence_count,
                self.assumption_count,
                self.guarantee_count,
                self.contract_count,
                self.entity_count,
                self.behavior_count,
                current_edge_count,
                self.edges.len()
            ),
        };
        if self.nodes.is_empty() {
            output.push_str("(empty)\n");
            return output;
        }

        let (positions, height) = self.layout(width);
        let area = Rect::new(0, 0, width, height);
        let mut buffer = Buffer::empty(area);
        let canvas = Canvas::default()
            .marker(Marker::Braille)
            .x_bounds([0.0, f64::from(width.saturating_sub(1))])
            .y_bounds([0.0, f64::from(height.saturating_sub(1))])
            .paint(|context| {
                for edge in &self.edges {
                    let (x1, y1) = positions[edge.source];
                    let (x2, y2) = positions[edge.target];
                    context.draw(&Line::new(
                        x1,
                        y1,
                        x2,
                        y2,
                        if edge.current {
                            Color::Reset
                        } else {
                            Color::DarkGray
                        },
                    ));
                    if edge.directed {
                        let dx = x2 - x1;
                        let dy = y2 - y1;
                        let arrow_position = if dy.abs() < 0.5 {
                            if dx >= 0.0 {
                                0.96
                            } else {
                                0.04
                            }
                        } else {
                            0.60
                        };
                        let arrow_x = x1 + dx * arrow_position;
                        let arrow_y = y1 + dy * arrow_position;
                        context.print(arrow_x, arrow_y, direction_arrow(dx, dy));
                    }
                }
                for (node, &(x, y)) in self.nodes.iter().zip(&positions) {
                    context.print(x, y, node_label(node));
                }
            });
        canvas.render(area, &mut buffer);
        output.push_str(&buffer_text(&buffer));
        output.push_str(
            "\n◆ current specification   ◇ non-current specification   ○ written term   ● evidence   △ assumption   ■ guarantee   dim edge = Ledger history\n",
        );

        let mut kinds: BTreeMap<(&str, &str, &str, &str, bool), usize> = BTreeMap::new();
        for edge in &self.edges {
            *kinds
                .entry((
                    edge.family.as_str(),
                    edge.kind.as_str(),
                    edge.source_role.as_str(),
                    edge.target_role.as_str(),
                    edge.directed,
                ))
                .or_default() += 1;
        }
        if !kinds.is_empty() {
            output.push_str("Edge kinds:");
            for ((family, kind, source_role, target_role, directed), count) in kinds {
                let glyph = if directed { "→" } else { "—" };
                output.push_str(&format!(
                    "  {glyph} {family}/{kind} [{source_role}{glyph}{target_role}] ({count})"
                ));
            }
            output.push('\n');
        }
        let pairings: Vec<&Edge> = self
            .edges
            .iter()
            .filter(|edge| edge.relied.is_some())
            .collect();
        if !pairings.is_empty() {
            output.push_str("Pairing reliances:\n");
            for edge in pairings {
                let relied = edge.relied.expect("filtered pairing has relied Node");
                output.push_str(&format!(
                    "  {} {} --{} / relies on {}--> {}\n",
                    if edge.current {
                        "[current]"
                    } else {
                        "[history]"
                    },
                    self.nodes[edge.source].display_id,
                    edge.kind,
                    self.nodes[relied].display_id,
                    self.nodes[edge.target].display_id,
                ));
            }
        }
        let specifications: Vec<&Node> = self
            .nodes
            .iter()
            .filter(|node| node.kind == NodeKind::Specification)
            .collect();
        if !specifications.is_empty() {
            let policy = specifications
                .iter()
                .map(|node| node.policy_version.as_str())
                .find(|version| !version.is_empty())
                .unwrap_or("unavailable");
            output.push_str(&format!("Selection fitness ({policy}):\n"));
            for node in specifications {
                output.push_str(&format!(
                    "  {} {} score={:+} (structural={:+}, evidence={:+}, conflict=-{}) {}\n",
                    if node.current {
                        "◆"
                    } else if node.evaluation_state == "unknown" {
                        "?"
                    } else {
                        "◇"
                    },
                    node.display_id,
                    node.support_score,
                    node.structural_score,
                    node.evidence_score,
                    node.conflict_pressure,
                    if node.evaluation_state.is_empty() {
                        if node.current {
                            "current"
                        } else {
                            "receded"
                        }
                    } else {
                        node.evaluation_state.as_str()
                    },
                ));
                output.push_str(&format!("      specification: {}\n", node.label));
                for contribution in &node.contributions {
                    output.push_str(&format!(
                        "      {:+} {} — {} [{}]\n",
                        contribution.points,
                        contribution.kind,
                        contribution.detail,
                        contribution.edge_id,
                    ));
                }
                for exclusion in &node.exclusions {
                    output.push_str(&format!(
                        "      excludes: {}{} — {}\n",
                        exclusion.kind,
                        exclusion
                            .competing_node_id
                            .as_deref()
                            .map_or_else(String::new, |id| format!(" by {id}")),
                        exclusion.detail,
                    ));
                }
            }
        }
        output
    }

    /// Lay connected components out from top to bottom. Within a component,
    /// high-incidence Nodes are placed first on a stable grid. This improves
    /// readability but gives no Node semantic authority or root status.
    fn layout(&self, width: u16) -> (Vec<(f64, f64)>, u16) {
        let mut adjacency = vec![Vec::new(); self.nodes.len()];
        for edge in &self.edges {
            adjacency[edge.source].push(edge.target);
            adjacency[edge.target].push(edge.source);
        }
        let mut seen = vec![false; self.nodes.len()];
        let mut components = Vec::new();
        for start in 0..self.nodes.len() {
            if seen[start] {
                continue;
            }
            let mut stack = vec![start];
            seen[start] = true;
            let mut component = Vec::new();
            while let Some(node) = stack.pop() {
                component.push(node);
                for &neighbor in &adjacency[node] {
                    if !seen[neighbor] {
                        seen[neighbor] = true;
                        stack.push(neighbor);
                    }
                }
            }
            component.sort_by(|&left, &right| {
                adjacency[right]
                    .len()
                    .cmp(&adjacency[left].len())
                    .then_with(|| self.nodes[left].id.cmp(&self.nodes[right].id))
            });
            components.push(component);
        }
        components.sort_by_key(|component| {
            component
                .iter()
                .map(|&node| self.nodes[node].id.as_str())
                .min()
                .unwrap_or("")
                .to_string()
        });

        let columns = (width / SLOT_WIDTH).max(1) as usize;
        let component_heights: Vec<u16> = components
            .iter()
            .map(|component| {
                let rows = component.len().div_ceil(columns) as u16;
                rows.saturating_mul(ROW_HEIGHT).saturating_add(2)
            })
            .collect();
        let height = component_heights
            .iter()
            .copied()
            .fold(1_u16, u16::saturating_add)
            .max(6);
        let mut positions = vec![(0.0, 0.0); self.nodes.len()];
        let mut top = 1_u16;
        for (component, component_height) in components.iter().zip(component_heights) {
            for (offset, &node) in component.iter().enumerate() {
                let column = offset % columns;
                let row = offset / columns;
                let x = (column as u16)
                    .saturating_mul(SLOT_WIDTH)
                    .saturating_add(1)
                    .min(width.saturating_sub(2));
                let terminal_y = top
                    .saturating_add((row as u16).saturating_mul(ROW_HEIGHT))
                    .saturating_add(1)
                    .min(height.saturating_sub(2));
                let canvas_y = height.saturating_sub(1).saturating_sub(terminal_y);
                positions[node] = (f64::from(x), f64::from(canvas_y));
            }
            top = top.saturating_add(component_height);
        }
        (positions, height)
    }
}

fn terminal_width() -> Option<u16> {
    std::env::var("COLUMNS").ok()?.parse().ok()
}

fn node_label(node: &Node) -> String {
    let marker = match node.kind {
        NodeKind::Specification if node.current => '◆',
        NodeKind::Specification => '◇',
        NodeKind::Term => '○',
        NodeKind::Evidence => '●',
        NodeKind::Assumption => '△',
        NodeKind::Guarantee => '■',
        NodeKind::Contract => '⬡',
        NodeKind::Entity => '◉',
        NodeKind::Behavior => '▣',
    };
    format!(
        "{marker} {} {}",
        node.display_id,
        truncate(&node.label, MAX_LABEL_CHARS)
    )
}

fn truncate(value: &str, maximum: usize) -> String {
    let mut chars = value.chars();
    let prefix: String = chars.by_ref().take(maximum).collect();
    if chars.next().is_some() {
        format!("{}…", prefix.trim_end())
    } else {
        prefix
    }
}

fn direction_arrow(dx: f64, dy: f64) -> &'static str {
    if dx.abs() >= dy.abs() {
        if dx >= 0.0 {
            "▶"
        } else {
            "◀"
        }
    } else if dy >= 0.0 {
        "▲"
    } else {
        "▼"
    }
}

fn buffer_text(buffer: &Buffer) -> String {
    let width = usize::from(buffer.area.width);
    let mut lines: Vec<String> = buffer
        .content()
        .chunks(width)
        .map(|row| {
            row.iter()
                .map(|cell| cell.symbol())
                .collect::<String>()
                .trim_end()
                .to_string()
        })
        .collect();
    while lines.last().is_some_and(String::is_empty) {
        lines.pop();
    }
    lines.join("\n")
}

fn edge_kind(kind: i32) -> (&'static str, bool) {
    match pb::EdgeKind::try_from(kind).unwrap_or(pb::EdgeKind::Unspecified) {
        pb::EdgeKind::MentionsTerm => ("mentions_term", true),
        pb::EdgeKind::SameLexeme => ("same_lexeme", false),
        pb::EdgeKind::Refines => ("refines", true),
        pb::EdgeKind::Equivalent => ("equivalent", false),
        pb::EdgeKind::HardContradiction => ("hard_contradiction", false),
        pb::EdgeKind::AdvisoryTension => ("advisory_tension", false),
        pb::EdgeKind::DescriptiveConflict => ("descriptive_conflict", false),
        pb::EdgeKind::EnvelopeConflict => ("envelope_conflict", false),
        pb::EdgeKind::OccurrenceReliance => ("occurrence_reliance", true),
        pb::EdgeKind::GuaranteeDischarge => ("guarantee_discharge", true),
        pb::EdgeKind::AdmissibilityEnvelope => ("admissibility_envelope", true),
        pb::EdgeKind::GroundedBy => ("grounded_by", true),
        pb::EdgeKind::EvidenceAffirms => ("evidence_affirms", true),
        pb::EdgeKind::EvidenceDenies => ("evidence_denies", true),
        pb::EdgeKind::HasAssumption => ("has_assumption", true),
        pb::EdgeKind::HasGuarantee => ("has_guarantee", true),
        pb::EdgeKind::HasContract => ("has_contract", true),
        pb::EdgeKind::ContractRefines => ("contract_refines", true),
        pb::EdgeKind::ContractEquivalent => ("contract_equivalent", false),
        pb::EdgeKind::CompositionOperand => ("composition_operand", true),
        pb::EdgeKind::QuotientDividend => ("quotient_dividend", true),
        pb::EdgeKind::QuotientDivisor => ("quotient_divisor", true),
        pb::EdgeKind::MergeOperand => ("merge_operand", true),
        pb::EdgeKind::HasBehavior => ("has_behavior", true),
        pb::EdgeKind::WitnessesEntity => ("witnesses_entity", true),
        pb::EdgeKind::EngagesEntity => ("engages_entity", true),
        pb::EdgeKind::Unspecified => ("unspecified", false),
    }
}

fn edge_family(family: i32) -> &'static str {
    match pb::EdgeFamily::try_from(family).unwrap_or(pb::EdgeFamily::Unspecified) {
        pb::EdgeFamily::Lexical => "lexical",
        pb::EdgeFamily::Semantic => "semantic",
        pb::EdgeFamily::Projection => "projection",
        pb::EdgeFamily::Epistemic => "epistemic",
        pb::EdgeFamily::Unspecified => "unspecified",
    }
}

fn endpoint_role(role: i32) -> &'static str {
    match pb::EdgeEndpointRole::try_from(role).unwrap_or(pb::EdgeEndpointRole::Unspecified) {
        pb::EdgeEndpointRole::Mentioner => "mentioner",
        pb::EdgeEndpointRole::MentionedTerm => "mentioned_term",
        pb::EdgeEndpointRole::LexemePeer => "lexeme_peer",
        pb::EdgeEndpointRole::Refiner => "refiner",
        pb::EdgeEndpointRole::Refined => "refined",
        pb::EdgeEndpointRole::EquivalentPeer => "equivalent_peer",
        pb::EdgeEndpointRole::ConflictPeer => "conflict_peer",
        pb::EdgeEndpointRole::GroundedSpecification => "grounded_specification",
        pb::EdgeEndpointRole::Evidence => "evidence",
        pb::EdgeEndpointRole::ContractSpecification => "contract_specification",
        pb::EdgeEndpointRole::Assumption => "assumption",
        pb::EdgeEndpointRole::Guarantee => "guarantee",
        pb::EdgeEndpointRole::RelianceEvidence => "reliance_evidence",
        pb::EdgeEndpointRole::ReliantContract => "reliant_contract",
        pb::EdgeEndpointRole::DischargingGuarantee => "discharging_guarantee",
        pb::EdgeEndpointRole::DischargedContract => "discharged_contract",
        pb::EdgeEndpointRole::AdmissibleEnvironment => "admissible_environment",
        pb::EdgeEndpointRole::BoundedContract => "bounded_contract",
        pb::EdgeEndpointRole::Contract => "contract",
        pb::EdgeEndpointRole::ContractRefiner => "contract_refiner",
        pb::EdgeEndpointRole::ContractRefined => "contract_refined",
        pb::EdgeEndpointRole::EquivalentContract => "equivalent_contract",
        pb::EdgeEndpointRole::CompositionOperand => "composition_operand",
        pb::EdgeEndpointRole::CompositionResult => "composition_result",
        pb::EdgeEndpointRole::QuotientDividend => "quotient_dividend",
        pb::EdgeEndpointRole::QuotientDivisor => "quotient_divisor",
        pb::EdgeEndpointRole::QuotientResult => "quotient_result",
        pb::EdgeEndpointRole::MergeOperand => "merge_operand",
        pb::EdgeEndpointRole::MergeResult => "merge_result",
        pb::EdgeEndpointRole::OperationalSpecification => "operational_specification",
        pb::EdgeEndpointRole::OperationalBehavior => "operational_behavior",
        pb::EdgeEndpointRole::WitnessingBehavior => "witnessing_behavior",
        pb::EdgeEndpointRole::WitnessedEntity => "witnessed_entity",
        pb::EdgeEndpointRole::EngagingBehavior => "engaging_behavior",
        pb::EdgeEndpointRole::EngagedEntity => "engaged_entity",
        pb::EdgeEndpointRole::AffirmingEvidence => "affirming_evidence",
        pb::EdgeEndpointRole::AffirmedSpecification => "affirmed_specification",
        pb::EdgeEndpointRole::AffirmedEvidence => "affirmed_evidence",
        pb::EdgeEndpointRole::DenyingEvidence => "denying_evidence",
        pb::EdgeEndpointRole::DeniedSpecification => "denied_specification",
        pb::EdgeEndpointRole::DeniedEvidence => "denied_evidence",
        pb::EdgeEndpointRole::Unspecified => "unspecified",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn specification(id: &str, statement: &str) -> pb::Node {
        pb::Node {
            id: id.to_string(),
            statement: statement.to_string(),
            ..Default::default()
        }
    }

    fn term(id: &str, form: &str) -> pb::TermNode {
        pb::TermNode {
            id: id.to_string(),
            form: form.to_string(),
            ..Default::default()
        }
    }

    fn edge(id: &str, source: &str, target: &str) -> pb::Edge {
        edge_with_kind(id, source, target, pb::EdgeKind::MentionsTerm)
    }

    fn edge_with_kind(id: &str, source: &str, target: &str, kind: pb::EdgeKind) -> pb::Edge {
        let (family, source_role, target_role) = match kind {
            pb::EdgeKind::MentionsTerm => (
                pb::EdgeFamily::Lexical,
                pb::EdgeEndpointRole::Mentioner,
                pb::EdgeEndpointRole::MentionedTerm,
            ),
            pb::EdgeKind::SameLexeme => (
                pb::EdgeFamily::Lexical,
                pb::EdgeEndpointRole::LexemePeer,
                pb::EdgeEndpointRole::LexemePeer,
            ),
            pb::EdgeKind::Refines => (
                pb::EdgeFamily::Semantic,
                pb::EdgeEndpointRole::Refiner,
                pb::EdgeEndpointRole::Refined,
            ),
            pb::EdgeKind::Equivalent => (
                pb::EdgeFamily::Semantic,
                pb::EdgeEndpointRole::EquivalentPeer,
                pb::EdgeEndpointRole::EquivalentPeer,
            ),
            pb::EdgeKind::HardContradiction
            | pb::EdgeKind::AdvisoryTension
            | pb::EdgeKind::DescriptiveConflict
            | pb::EdgeKind::EnvelopeConflict => (
                pb::EdgeFamily::Semantic,
                pb::EdgeEndpointRole::ConflictPeer,
                pb::EdgeEndpointRole::ConflictPeer,
            ),
            pb::EdgeKind::OccurrenceReliance => (
                pb::EdgeFamily::Semantic,
                pb::EdgeEndpointRole::RelianceEvidence,
                pb::EdgeEndpointRole::ReliantContract,
            ),
            pb::EdgeKind::GuaranteeDischarge => (
                pb::EdgeFamily::Semantic,
                pb::EdgeEndpointRole::DischargingGuarantee,
                pb::EdgeEndpointRole::DischargedContract,
            ),
            pb::EdgeKind::AdmissibilityEnvelope => (
                pb::EdgeFamily::Semantic,
                pb::EdgeEndpointRole::AdmissibleEnvironment,
                pb::EdgeEndpointRole::BoundedContract,
            ),
            pb::EdgeKind::GroundedBy => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::GroundedSpecification,
                pb::EdgeEndpointRole::Evidence,
            ),
            pb::EdgeKind::EvidenceAffirms => (
                pb::EdgeFamily::Epistemic,
                pb::EdgeEndpointRole::AffirmingEvidence,
                pb::EdgeEndpointRole::AffirmedEvidence,
            ),
            pb::EdgeKind::EvidenceDenies => (
                pb::EdgeFamily::Epistemic,
                pb::EdgeEndpointRole::DenyingEvidence,
                pb::EdgeEndpointRole::DeniedEvidence,
            ),
            pb::EdgeKind::HasAssumption => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::ContractSpecification,
                pb::EdgeEndpointRole::Assumption,
            ),
            pb::EdgeKind::HasGuarantee => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::ContractSpecification,
                pb::EdgeEndpointRole::Guarantee,
            ),
            pb::EdgeKind::HasContract => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::ContractSpecification,
                pb::EdgeEndpointRole::Contract,
            ),
            pb::EdgeKind::ContractRefines => (
                pb::EdgeFamily::Semantic,
                pb::EdgeEndpointRole::ContractRefiner,
                pb::EdgeEndpointRole::ContractRefined,
            ),
            pb::EdgeKind::ContractEquivalent => (
                pb::EdgeFamily::Semantic,
                pb::EdgeEndpointRole::EquivalentContract,
                pb::EdgeEndpointRole::EquivalentContract,
            ),
            pb::EdgeKind::CompositionOperand => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::CompositionOperand,
                pb::EdgeEndpointRole::CompositionResult,
            ),
            pb::EdgeKind::QuotientDividend => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::QuotientDividend,
                pb::EdgeEndpointRole::QuotientResult,
            ),
            pb::EdgeKind::QuotientDivisor => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::QuotientDivisor,
                pb::EdgeEndpointRole::QuotientResult,
            ),
            pb::EdgeKind::MergeOperand => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::MergeOperand,
                pb::EdgeEndpointRole::MergeResult,
            ),
            pb::EdgeKind::HasBehavior => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::OperationalSpecification,
                pb::EdgeEndpointRole::OperationalBehavior,
            ),
            pb::EdgeKind::WitnessesEntity => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::WitnessingBehavior,
                pb::EdgeEndpointRole::WitnessedEntity,
            ),
            pb::EdgeKind::EngagesEntity => (
                pb::EdgeFamily::Projection,
                pb::EdgeEndpointRole::EngagingBehavior,
                pb::EdgeEndpointRole::EngagedEntity,
            ),
            pb::EdgeKind::Unspecified => (
                pb::EdgeFamily::Unspecified,
                pb::EdgeEndpointRole::Unspecified,
                pb::EdgeEndpointRole::Unspecified,
            ),
        };
        pb::Edge {
            id: id.to_string(),
            source: source.to_string(),
            target: target.to_string(),
            kind: kind as i32,
            family: family as i32,
            source_role: source_role as i32,
            target_role: target_role as i32,
            current: true,
            ..Default::default()
        }
    }

    #[test]
    fn renders_topology_instead_of_node_and_edge_record_lists() {
        let graph = Graph::from_wire(
            [
                specification("spec-a", "The daemon shall stop."),
                specification("spec-b", "The daemon shall wait."),
            ],
            [term("term-daemon", "daemon")],
            [],
            [
                edge("edge-a", "spec-a", "term-daemon"),
                edge("edge-b", "spec-b", "term-daemon"),
            ],
        )
        .unwrap();

        let rendered = graph.render(Some(90));

        assert!(rendered.contains("The daemon shall stop."));
        assert!(rendered.contains("The daemon shall wait."));
        assert!(rendered.contains("daemon"));
        assert!(rendered.contains("◆ S"));
        assert!(rendered.contains("○ T"));
        assert!(rendered.contains("→ lexical/mentions_term [mentioner→mentioned_term] (2)"));
        assert!(
            rendered.contains('▶')
                || rendered.contains('◀')
                || rendered.contains('▼')
                || rendered.contains('▲')
        );
        assert!(!rendered.contains("Specification Nodes"));
        assert!(!rendered.contains("Edges ("));
    }

    #[test]
    fn renders_directed_and_symmetric_semantic_edge_kinds_distinctly() {
        let graph = Graph::from_wire(
            [
                specification("a", "The daemon shall stop."),
                specification("b", "The daemon shall not stop."),
            ],
            [],
            [],
            [
                edge_with_kind("refines", "a", "b", pb::EdgeKind::Refines),
                edge_with_kind("conflict", "a", "b", pb::EdgeKind::HardContradiction),
            ],
        )
        .unwrap();
        let rendered = graph.render(Some(100));
        assert!(rendered.contains("→ semantic/refines [refiner→refined] (1)"));
        assert!(
            rendered.contains("— semantic/hard_contradiction [conflict_peer—conflict_peer] (1)")
        );
    }

    #[test]
    fn renders_fitness_sum_and_exclusion_reasons() {
        let mut candidate = specification("candidate", "The daemon shall stop.");
        candidate.selection = Some(pb::SelectionView {
            current: false,
            policy_version: "selection/fitness-v6".into(),
            support_score: -4,
            structural_score: 4,
            evidence_score: -8,
            relation_score: 4,
            conflict_pressure: 0,
            evaluation_state: "receded".into(),
            contributions: vec![pb::ScoreContribution {
                kind: "counter_evidence".into(),
                points: -8,
                edge_id: "evidence-edge".into(),
                detail: "counter at report.md contributes -8 point(s)".into(),
                ..Default::default()
            }],
            exclusions: vec![pb::SelectionExclusion {
                kind: "counterevidence".into(),
                detail: "fitness -4 is below threshold 1".into(),
                ..Default::default()
            }],
            ..Default::default()
        });
        let graph = Graph::from_wire([candidate], [], [], []).unwrap();
        let rendered = graph.render(Some(90));
        assert!(rendered.contains("Selection fitness (selection/fitness-v6):"));
        assert!(rendered.contains("score=-4 (structural=+4, evidence=-8, conflict=-0) receded"));
        assert!(rendered.contains("specification: The daemon shall stop."));
        assert!(rendered.contains("-8 counter_evidence"));
        assert!(rendered.contains("excludes: counterevidence"));
    }

    #[test]
    fn rejects_an_edge_whose_endpoint_was_not_returned() {
        let error = Graph::from_wire(
            [specification("spec-a", "The daemon shall stop.")],
            [],
            [],
            [edge("edge-a", "spec-a", "missing")],
        )
        .unwrap_err();

        assert!(error.contains("unavailable target Node missing"));
    }

    #[test]
    fn empty_graph_is_still_a_valid_whole_graph() {
        let graph = Graph::from_wire([], [], [], []).unwrap();

        assert!(graph.render(Some(80)).contains("(empty)"));
    }

    #[test]
    fn current_scope_names_the_selected_topology_as_a_graph() {
        let graph = Graph::from_wire(
            [specification("current", "The daemon shall stop.")],
            [],
            [],
            [],
        )
        .unwrap()
        .with_scope(GraphScope::Current);

        assert!(graph
            .render(Some(80))
            .starts_with("Current specification graph — 1 specification(s)"));
    }
}
