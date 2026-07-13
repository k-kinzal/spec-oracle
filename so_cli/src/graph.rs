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
}

#[derive(Debug)]
struct Node {
    id: String,
    display_id: String,
    label: String,
    kind: NodeKind,
}

#[derive(Debug)]
struct Edge {
    source: usize,
    target: usize,
    kind: String,
}

/// The complete topology collected by one `spec graph` invocation.
#[derive(Debug)]
pub(crate) struct Graph {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    specification_count: usize,
    term_count: usize,
}

impl Graph {
    pub(crate) fn from_wire(
        specifications: impl IntoIterator<Item = pb::Node>,
        terms: impl IntoIterator<Item = pb::TermNode>,
        edges: impl IntoIterator<Item = pb::Edge>,
    ) -> Result<Self, String> {
        let mut nodes_by_id = BTreeMap::new();
        let mut specification_count = 0;
        let mut term_count = 0;

        for specification in specifications {
            let node = Node {
                id: specification.id.clone(),
                display_id: String::new(),
                label: specification.statement,
                kind: NodeKind::Specification,
            };
            if nodes_by_id.insert(specification.id, node).is_some() {
                return Err("the graph contains a duplicate Node id".to_string());
            }
            specification_count += 1;
        }
        for term in terms {
            let node = Node {
                id: term.id.clone(),
                display_id: String::new(),
                label: term.form,
                kind: NodeKind::Term,
            };
            if nodes_by_id.insert(term.id, node).is_some() {
                return Err("Specification and Term Node ids must be disjoint".to_string());
            }
            term_count += 1;
        }

        let mut nodes: Vec<Node> = nodes_by_id.into_values().collect();
        let mut specification_number = 0;
        let mut term_number = 0;
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
            graph_edges.push(Edge {
                source,
                target,
                kind: edge_kind(edge.kind).to_string(),
            });
        }

        Ok(Self {
            nodes,
            edges: graph_edges,
            specification_count,
            term_count,
        })
    }

    pub(crate) fn render(&self, requested_width: Option<u16>) -> String {
        let width = requested_width
            .or_else(terminal_width)
            .unwrap_or(DEFAULT_WIDTH)
            .max(MIN_WIDTH);
        let mut output = format!(
            "Specification graph — {} specification(s), {} term(s), {} edge(s)\n",
            self.specification_count,
            self.term_count,
            self.edges.len()
        );
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
                    context.draw(&Line::new(x1, y1, x2, y2, Color::Reset));
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
                    context.print(arrow_x, arrow_y, direction_arrow(x2 - x1, y2 - y1));
                }
                for (node, &(x, y)) in self.nodes.iter().zip(&positions) {
                    context.print(x, y, node_label(node));
                }
            });
        canvas.render(area, &mut buffer);
        output.push_str(&buffer_text(&buffer));
        output.push_str("\n◆ specification   ○ written term form\n");

        let mut kinds: BTreeMap<&str, usize> = BTreeMap::new();
        for edge in &self.edges {
            *kinds.entry(edge.kind.as_str()).or_default() += 1;
        }
        if !kinds.is_empty() {
            output.push_str("Directed Edge kinds:");
            for (kind, count) in kinds {
                output.push_str(&format!("  → {kind} ({count})"));
            }
            output.push('\n');
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
        NodeKind::Specification => '◆',
        NodeKind::Term => '○',
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

fn edge_kind(kind: i32) -> &'static str {
    match pb::EdgeKind::try_from(kind).unwrap_or(pb::EdgeKind::Unspecified) {
        pb::EdgeKind::MentionsTerm => "mentions_term",
        pb::EdgeKind::Unspecified => "unspecified",
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
        pb::Edge {
            id: id.to_string(),
            source: source.to_string(),
            target: target.to_string(),
            kind: pb::EdgeKind::MentionsTerm as i32,
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
        assert!(rendered.contains("→ mentions_term (2)"));
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
    fn rejects_an_edge_whose_endpoint_was_not_returned() {
        let error = Graph::from_wire(
            [specification("spec-a", "The daemon shall stop.")],
            [],
            [edge("edge-a", "spec-a", "missing")],
        )
        .unwrap_err();

        assert!(error.contains("unavailable target Node missing"));
    }

    #[test]
    fn empty_graph_is_still_a_valid_whole_graph() {
        let graph = Graph::from_wire([], [], []).unwrap();

        assert!(graph.render(Some(80)).contains("(empty)"));
    }
}
