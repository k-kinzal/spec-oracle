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
        created_at: n.created_at,
        modified_at: n.modified_at,
        formality_layer: n.formality_layer as u32,
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
        created_at: e.created_at,
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
        EdgeKind::Formalizes => proto::SpecEdgeKind::Formalizes,
        EdgeKind::Transform => proto::SpecEdgeKind::Transform,
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
        Ok(proto::SpecEdgeKind::Formalizes) => EdgeKind::Formalizes,
        Ok(proto::SpecEdgeKind::Transform) => EdgeKind::Transform,
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

    async fn detect_layer_inconsistencies(
        &self,
        _request: Request<proto::DetectLayerInconsistenciesRequest>,
    ) -> Result<Response<proto::DetectLayerInconsistenciesResponse>, Status> {
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let inconsistencies: Vec<proto::LayerInconsistency> = graph
            .detect_layer_inconsistencies()
            .into_iter()
            .map(|i| proto::LayerInconsistency {
                source: Some(to_proto_node(&i.source)),
                target: Some(to_proto_node(&i.target)),
                explanation: i.explanation,
            })
            .collect();
        Ok(Response::new(proto::DetectLayerInconsistenciesResponse {
            inconsistencies,
        }))
    }

    async fn filter_by_layer(
        &self,
        request: Request<proto::FilterByLayerRequest>,
    ) -> Result<Response<proto::FilterByLayerResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let nodes: Vec<proto::SpecNode> = graph
            .filter_by_layer(req.min_layer as u8, req.max_layer as u8)
            .into_iter()
            .map(to_proto_node)
            .collect();
        Ok(Response::new(proto::FilterByLayerResponse { nodes }))
    }

    async fn find_formalizations(
        &self,
        request: Request<proto::FindFormalizationsRequest>,
    ) -> Result<Response<proto::FindFormalizationsResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let formalizations: Vec<proto::SpecNode> = graph
            .find_formalizations(&req.node_id)
            .into_iter()
            .map(to_proto_node)
            .collect();
        let natural_sources: Vec<proto::SpecNode> = graph
            .find_natural_source(&req.node_id)
            .into_iter()
            .map(to_proto_node)
            .collect();
        Ok(Response::new(proto::FindFormalizationsResponse {
            formalizations,
            natural_sources,
        }))
    }

    async fn find_related_terms(
        &self,
        request: Request<proto::FindRelatedTermsRequest>,
    ) -> Result<Response<proto::FindRelatedTermsResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let mut related = graph.find_related_terms(&req.term);

        if req.max_results > 0 && related.len() > req.max_results as usize {
            related.truncate(req.max_results as usize);
        }

        let nodes: Vec<proto::ScoredNode> = related
            .into_iter()
            .map(|(node, score)| proto::ScoredNode {
                node: Some(to_proto_node(node)),
                score,
            })
            .collect();

        Ok(Response::new(proto::FindRelatedTermsResponse { nodes }))
    }

    async fn detect_potential_synonyms(
        &self,
        request: Request<proto::DetectPotentialSynonymsRequest>,
    ) -> Result<Response<proto::DetectPotentialSynonymsResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let min_sim = if req.min_similarity > 0.0 {
            req.min_similarity
        } else {
            0.3
        };

        let candidates: Vec<proto::SynonymCandidate> = graph
            .detect_potential_synonyms()
            .into_iter()
            .filter(|(_, _, sim)| *sim >= min_sim)
            .map(|(node_a, node_b, similarity)| proto::SynonymCandidate {
                node_a: Some(to_proto_node(&node_a)),
                node_b: Some(to_proto_node(&node_b)),
                similarity,
            })
            .collect();

        Ok(Response::new(proto::DetectPotentialSynonymsResponse {
            candidates,
        }))
    }

    async fn generate_contract_template(
        &self,
        request: Request<proto::GenerateContractTemplateRequest>,
    ) -> Result<Response<proto::GenerateContractTemplateResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let template = graph
            .generate_contract_template(&req.node_id, &req.language)
            .ok_or_else(|| Status::not_found("Node not found or not testable"))?;

        let node = graph
            .get_node(&req.node_id)
            .ok_or_else(|| Status::not_found("Node not found"))?;

        let node_kind = match node.kind {
            spec_core::NodeKind::Constraint => "constraint",
            spec_core::NodeKind::Scenario => "scenario",
            _ => "unknown",
        };

        Ok(Response::new(proto::GenerateContractTemplateResponse {
            template,
            node_kind: node_kind.to_string(),
        }))
    }

    async fn get_test_coverage(
        &self,
        _request: Request<proto::GetTestCoverageRequest>,
    ) -> Result<Response<proto::GetTestCoverageResponse>, Status> {
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let coverage = graph.get_test_coverage();

        Ok(Response::new(proto::GetTestCoverageResponse {
            total_testable: coverage.total_testable as u32,
            with_tests: coverage.with_tests as u32,
            coverage_ratio: coverage.coverage_ratio,
            nodes_with_tests: coverage
                .nodes_with_tests
                .iter()
                .map(to_proto_node)
                .collect(),
            nodes_without_tests: coverage
                .nodes_without_tests
                .iter()
                .map(to_proto_node)
                .collect(),
        }))
    }

    async fn calculate_compliance(
        &self,
        request: Request<proto::CalculateComplianceRequest>,
    ) -> Result<Response<proto::CalculateComplianceResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let compliance = graph
            .calculate_compliance(&req.node_id, &req.code)
            .ok_or_else(|| Status::not_found("Node not found"))?;

        Ok(Response::new(proto::CalculateComplianceResponse {
            score: compliance.score,
            keyword_overlap: compliance.keyword_overlap,
            structural_match: compliance.structural_match,
            explanation: compliance.explanation,
        }))
    }

    async fn get_compliance_report(
        &self,
        _request: Request<proto::GetComplianceReportRequest>,
    ) -> Result<Response<proto::GetComplianceReportResponse>, Status> {
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let report = graph.get_compliance_report();

        let entries: Vec<proto::ComplianceEntry> = report
            .into_iter()
            .map(|(node, score)| proto::ComplianceEntry {
                node: Some(to_proto_node(&node)),
                score: score.score,
                keyword_overlap: score.keyword_overlap,
                structural_match: score.structural_match,
                explanation: score.explanation,
            })
            .collect();

        Ok(Response::new(proto::GetComplianceReportResponse {
            entries,
        }))
    }

    async fn query_at_timestamp(
        &self,
        request: Request<proto::QueryAtTimestampRequest>,
    ) -> Result<Response<proto::QueryAtTimestampResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let snapshot = graph.query_at_timestamp(req.timestamp);

        let nodes: Vec<proto::SpecNode> = snapshot.nodes.iter().map(to_proto_node).collect();

        let edges: Vec<proto::SpecEdge> = snapshot
            .edges
            .iter()
            .map(|e| {
                // For snapshot edges, we need source and target IDs
                // They're already in the snapshot, so we can use empty strings for now
                // (this is a limitation of the current design)
                proto::SpecEdge {
                    id: e.id.clone(),
                    source_id: String::new(),
                    target_id: String::new(),
                    kind: to_proto_edge_kind(e.kind).into(),
                    metadata: e.metadata.clone(),
                    created_at: e.created_at,
                }
            })
            .collect();

        Ok(Response::new(proto::QueryAtTimestampResponse {
            timestamp: snapshot.timestamp,
            nodes,
            edges,
            node_count: snapshot.node_count as u32,
            edge_count: snapshot.edge_count as u32,
        }))
    }

    async fn diff_timestamps(
        &self,
        request: Request<proto::DiffTimestampsRequest>,
    ) -> Result<Response<proto::DiffTimestampsResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let diff = graph.diff_timestamps(req.from_timestamp, req.to_timestamp);

        let added_nodes: Vec<proto::SpecNode> =
            diff.added_nodes.iter().map(to_proto_node).collect();

        let removed_nodes: Vec<proto::SpecNode> =
            diff.removed_nodes.iter().map(to_proto_node).collect();

        let modified_nodes: Vec<proto::NodeChange> = diff
            .modified_nodes
            .iter()
            .map(|(from, to)| proto::NodeChange {
                from_node: Some(to_proto_node(from)),
                to_node: Some(to_proto_node(to)),
            })
            .collect();

        let added_edges: Vec<proto::SpecEdge> = diff
            .added_edges
            .iter()
            .map(|e| proto::SpecEdge {
                id: e.id.clone(),
                source_id: String::new(),
                target_id: String::new(),
                kind: to_proto_edge_kind(e.kind).into(),
                metadata: e.metadata.clone(),
                created_at: e.created_at,
            })
            .collect();

        let removed_edges: Vec<proto::SpecEdge> = diff
            .removed_edges
            .iter()
            .map(|e| proto::SpecEdge {
                id: e.id.clone(),
                source_id: String::new(),
                target_id: String::new(),
                kind: to_proto_edge_kind(e.kind).into(),
                metadata: e.metadata.clone(),
                created_at: e.created_at,
            })
            .collect();

        Ok(Response::new(proto::DiffTimestampsResponse {
            from_timestamp: diff.from_timestamp,
            to_timestamp: diff.to_timestamp,
            added_nodes,
            removed_nodes,
            modified_nodes,
            added_edges,
            removed_edges,
        }))
    }

    async fn get_node_history(
        &self,
        request: Request<proto::GetNodeHistoryRequest>,
    ) -> Result<Response<proto::GetNodeHistoryResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let history = graph
            .get_node_history(&req.node_id)
            .ok_or_else(|| Status::not_found("Node not found"))?;

        let events: Vec<proto::HistoryEvent> = history
            .events
            .iter()
            .map(|e| proto::HistoryEvent {
                timestamp: e.timestamp,
                event_type: e.event_type.clone(),
                description: e.description.clone(),
            })
            .collect();

        Ok(Response::new(proto::GetNodeHistoryResponse {
            node: Some(to_proto_node(&history.node)),
            events,
        }))
    }

    async fn get_compliance_trend(
        &self,
        request: Request<proto::GetComplianceTrendRequest>,
    ) -> Result<Response<proto::GetComplianceTrendResponse>, Status> {
        let req = request.into_inner();
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let trend = graph
            .get_compliance_trend(&req.node_id)
            .ok_or_else(|| Status::not_found("Node not found or no compliance data"))?;

        let data_points: Vec<proto::ComplianceDataPoint> = trend
            .data_points
            .iter()
            .map(|d| proto::ComplianceDataPoint {
                timestamp: d.timestamp,
                score: d.score,
            })
            .collect();

        Ok(Response::new(proto::GetComplianceTrendResponse {
            node: Some(to_proto_node(&trend.node)),
            data_points,
            trend_direction: trend.trend_direction,
        }))
    }

    async fn detect_inter_universe_inconsistencies(
        &self,
        _request: Request<proto::DetectInterUniverseInconsistenciesRequest>,
    ) -> Result<Response<proto::DetectInterUniverseInconsistenciesResponse>, Status> {
        let graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;
        let inconsistencies: Vec<proto::InterUniverseInconsistency> = graph
            .detect_inter_universe_inconsistencies()
            .into_iter()
            .map(|i| proto::InterUniverseInconsistency {
                universe_a: i.universe_a,
                universe_b: i.universe_b,
                spec_a: Some(to_proto_node(&i.spec_a)),
                spec_b: Some(to_proto_node(&i.spec_b)),
                transform_path: i.transform_path,
                explanation: i.explanation,
            })
            .collect();
        Ok(Response::new(
            proto::DetectInterUniverseInconsistenciesResponse { inconsistencies },
        ))
    }

    async fn set_node_universe(
        &self,
        request: Request<proto::SetNodeUniverseRequest>,
    ) -> Result<Response<proto::SetNodeUniverseResponse>, Status> {
        let req = request.into_inner();
        let mut graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let node = graph
            .update_node_metadata(&req.node_id, "universe".to_string(), req.universe)
            .ok_or_else(|| Status::not_found("Node not found"))?;

        if let Err(e) = self.store.save(&*graph) {
            eprintln!("Failed to persist after setting universe: {}", e);
        }

        Ok(Response::new(proto::SetNodeUniverseResponse {
            node: Some(to_proto_node(&node)),
        }))
    }

    async fn infer_all_relationships(
        &self,
        _request: Request<proto::InferAllRelationshipsRequest>,
    ) -> Result<Response<proto::InferAllRelationshipsResponse>, Status> {
        let mut graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let report = graph.infer_all_relationships();

        if let Err(e) = self.store.save(&*graph) {
            eprintln!("Failed to persist after relationship inference: {}", e);
        }

        let suggestions: Vec<String> = report.suggestions.iter()
            .map(|s| format!("{} --{:?}-> {} (confidence: {:.2})",
                s.source_id, s.kind, s.target_id, s.confidence))
            .collect();

        Ok(Response::new(proto::InferAllRelationshipsResponse {
            edges_created: report.edges_created as u32,
            suggestions_count: suggestions.len() as u32,
            suggestions,
        }))
    }

    async fn infer_all_relationships_with_ai(
        &self,
        request: Request<proto::InferAllRelationshipsWithAiRequest>,
    ) -> Result<Response<proto::InferAllRelationshipsResponse>, Status> {
        let req = request.into_inner();
        let mut graph = self.graph.lock().map_err(|e| Status::internal(e.to_string()))?;

        let report = graph.infer_all_relationships_with_ai(req.min_confidence);

        if let Err(e) = self.store.save(&*graph) {
            eprintln!("Failed to persist after AI relationship inference: {}", e);
        }

        let suggestions: Vec<String> = report.suggestions.iter()
            .map(|s| format!("{} --{:?}-> {} (confidence: {:.2}): {}",
                s.source_id, s.kind, s.target_id, s.confidence, s.explanation))
            .collect();

        Ok(Response::new(proto::InferAllRelationshipsResponse {
            edges_created: report.edges_created as u32,
            suggestions_count: suggestions.len() as u32,
            suggestions,
        }))
    }
}
