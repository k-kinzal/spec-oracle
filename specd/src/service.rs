use crate::proto;
use spec_core::{EdgeKind, FileStore, NodeKind, SpecGraph};
use std::path::PathBuf;
use std::sync::Mutex;
use tonic::{Request, Response, Status};

pub struct SpecOracleService {
    graph: Mutex<SpecGraph>,
    store: FileStore,
}

impl SpecOracleService {
    pub fn new(store_path: PathBuf) -> Result<Self, Box<dyn std::error::Error>> {
        let store = FileStore::new(&store_path);
        let graph = store.load()?;
        Ok(Self {
            graph: Mutex::new(graph),
            store,
        })
    }

    fn save(&self, graph: &SpecGraph) -> Result<(), Status> {
        self.store
            .save(graph)
            .map_err(|e| Status::internal(format!("Failed to persist: {e}")))
    }
}

fn to_proto_node(n: &spec_core::SpecNodeData) -> proto::SpecNode {
    proto::SpecNode {
        id: n.id.clone(),
        content: n.content.clone(),
        kind: to_proto_node_kind(n.kind).into(),
        metadata: n.metadata.clone(),
    }
}

fn to_proto_node_kind(k: NodeKind) -> proto::SpecNodeKind {
    match k {
        NodeKind::Assertion => proto::SpecNodeKind::Assertion,
        NodeKind::Constraint => proto::SpecNodeKind::Constraint,
        NodeKind::Scenario => proto::SpecNodeKind::Scenario,
        NodeKind::Definition => proto::SpecNodeKind::Definition,
        NodeKind::Domain => proto::SpecNodeKind::Domain,
    }
}

fn from_proto_node_kind(k: i32) -> NodeKind {
    match proto::SpecNodeKind::try_from(k) {
        Ok(proto::SpecNodeKind::Assertion) => NodeKind::Assertion,
        Ok(proto::SpecNodeKind::Constraint) => NodeKind::Constraint,
        Ok(proto::SpecNodeKind::Scenario) => NodeKind::Scenario,
        Ok(proto::SpecNodeKind::Definition) => NodeKind::Definition,
        Ok(proto::SpecNodeKind::Domain) => NodeKind::Domain,
        _ => NodeKind::Assertion,
    }
}

fn to_proto_edge(e: &spec_core::SpecEdgeData, src: &str, tgt: &str) -> proto::SpecEdge {
    proto::SpecEdge {
        id: e.id.clone(),
        source_id: src.to_string(),
        target_id: tgt.to_string(),
        kind: to_proto_edge_kind(e.kind).into(),
        metadata: e.metadata.clone(),
    }
}

fn to_proto_edge_kind(k: EdgeKind) -> proto::SpecEdgeKind {
    match k {
        EdgeKind::Refines => proto::SpecEdgeKind::Refines,
        EdgeKind::DependsOn => proto::SpecEdgeKind::DependsOn,
        EdgeKind::Contradicts => proto::SpecEdgeKind::Contradicts,
        EdgeKind::DerivesFrom => proto::SpecEdgeKind::DerivesFrom,
        EdgeKind::Synonym => proto::SpecEdgeKind::Synonym,
        EdgeKind::Composes => proto::SpecEdgeKind::Composes,
    }
}

fn from_proto_edge_kind(k: i32) -> EdgeKind {
    match proto::SpecEdgeKind::try_from(k) {
        Ok(proto::SpecEdgeKind::Refines) => EdgeKind::Refines,
        Ok(proto::SpecEdgeKind::DependsOn) => EdgeKind::DependsOn,
        Ok(proto::SpecEdgeKind::Contradicts) => EdgeKind::Contradicts,
        Ok(proto::SpecEdgeKind::DerivesFrom) => EdgeKind::DerivesFrom,
        Ok(proto::SpecEdgeKind::Synonym) => EdgeKind::Synonym,
        Ok(proto::SpecEdgeKind::Composes) => EdgeKind::Composes,
        _ => EdgeKind::DependsOn,
    }
}

#[tonic::async_trait]
impl proto::spec_oracle_server::SpecOracle for SpecOracleService {
    async fn add_node(
        &self,
        request: Request<proto::AddNodeRequest>,
    ) -> Result<Response<proto::AddNodeResponse>, Status> {
        let req = request.into_inner();
        let mut graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let node = graph.add_node(
            req.content,
            from_proto_node_kind(req.kind),
            req.metadata,
        );
        let resp = proto::AddNodeResponse {
            node: Some(to_proto_node(node)),
        };
        self.save(&graph)?;
        Ok(Response::new(resp))
    }

    async fn get_node(
        &self,
        request: Request<proto::GetNodeRequest>,
    ) -> Result<Response<proto::GetNodeResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let node = graph
            .get_node(&req.id)
            .ok_or_else(|| Status::not_found(format!("Node {} not found", req.id)))?;
        Ok(Response::new(proto::GetNodeResponse {
            node: Some(to_proto_node(node)),
        }))
    }

    async fn list_nodes(
        &self,
        request: Request<proto::ListNodesRequest>,
    ) -> Result<Response<proto::ListNodesResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let filter = if req.kind_filter == 0 {
            None
        } else {
            Some(from_proto_node_kind(req.kind_filter))
        };
        let nodes: Vec<proto::SpecNode> = graph.list_nodes(filter).into_iter().map(to_proto_node).collect();
        Ok(Response::new(proto::ListNodesResponse { nodes }))
    }

    async fn remove_node(
        &self,
        request: Request<proto::RemoveNodeRequest>,
    ) -> Result<Response<proto::RemoveNodeResponse>, Status> {
        let req = request.into_inner();
        let mut graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        graph
            .remove_node(&req.id)
            .ok_or_else(|| Status::not_found(format!("Node {} not found", req.id)))?;
        self.save(&graph)?;
        Ok(Response::new(proto::RemoveNodeResponse {}))
    }

    async fn add_edge(
        &self,
        request: Request<proto::AddEdgeRequest>,
    ) -> Result<Response<proto::AddEdgeResponse>, Status> {
        let req = request.into_inner();
        let mut graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let edge = graph
            .add_edge(
                &req.source_id,
                &req.target_id,
                from_proto_edge_kind(req.kind),
                req.metadata,
            )
            .map_err(|e| Status::not_found(e.to_string()))?;
        let resp = proto::AddEdgeResponse {
            edge: Some(to_proto_edge(edge, &req.source_id, &req.target_id)),
        };
        self.save(&graph)?;
        Ok(Response::new(resp))
    }

    async fn list_edges(
        &self,
        request: Request<proto::ListEdgesRequest>,
    ) -> Result<Response<proto::ListEdgesResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let node_id = if req.node_id.is_empty() {
            None
        } else {
            Some(req.node_id.as_str())
        };
        let edges: Vec<proto::SpecEdge> = graph
            .list_edges(node_id)
            .into_iter()
            .map(|(e, src, tgt)| to_proto_edge(e, src, tgt))
            .collect();
        Ok(Response::new(proto::ListEdgesResponse { edges }))
    }

    async fn remove_edge(
        &self,
        request: Request<proto::RemoveEdgeRequest>,
    ) -> Result<Response<proto::RemoveEdgeResponse>, Status> {
        let req = request.into_inner();
        let mut graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        graph
            .remove_edge(&req.id)
            .ok_or_else(|| Status::not_found(format!("Edge {} not found", req.id)))?;
        self.save(&graph)?;
        Ok(Response::new(proto::RemoveEdgeResponse {}))
    }

    async fn query(
        &self,
        request: Request<proto::QueryRequest>,
    ) -> Result<Response<proto::QueryResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let matching: Vec<proto::SpecNode> = graph
            .search(&req.natural_language_query)
            .into_iter()
            .map(to_proto_node)
            .collect();
        let explanation = if matching.is_empty() {
            "No matching specifications found.".to_string()
        } else {
            format!("Found {} matching specification(s).", matching.len())
        };
        Ok(Response::new(proto::QueryResponse {
            matching_nodes: matching,
            explanation,
        }))
    }

    async fn detect_contradictions(
        &self,
        _request: Request<proto::DetectContradictionsRequest>,
    ) -> Result<Response<proto::DetectContradictionsResponse>, Status> {
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let contradictions: Vec<proto::Contradiction> = graph
            .detect_contradictions()
            .into_iter()
            .map(|c| proto::Contradiction {
                node_a: Some(to_proto_node(&c.node_a)),
                node_b: Some(to_proto_node(&c.node_b)),
                explanation: c.explanation,
            })
            .collect();
        Ok(Response::new(proto::DetectContradictionsResponse {
            contradictions,
        }))
    }

    async fn detect_omissions(
        &self,
        _request: Request<proto::DetectOmissionsRequest>,
    ) -> Result<Response<proto::DetectOmissionsResponse>, Status> {
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let omissions: Vec<proto::Omission> = graph
            .detect_omissions()
            .into_iter()
            .map(|o| proto::Omission {
                description: o.description,
                related_nodes: o.related_nodes.iter().map(to_proto_node).collect(),
            })
            .collect();
        Ok(Response::new(proto::DetectOmissionsResponse { omissions }))
    }

    async fn resolve_terminology(
        &self,
        request: Request<proto::ResolveTerminologyRequest>,
    ) -> Result<Response<proto::ResolveTerminologyResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let (defs, synonyms) = graph.resolve_term(&req.term);
        Ok(Response::new(proto::ResolveTerminologyResponse {
            definitions: defs.into_iter().map(to_proto_node).collect(),
            synonyms,
        }))
    }
}
