//! Model Service Implementation for specd
//!
//! Implements gRPC operations for managing the UDA/f model
//! (Universe, Domain, AdmissibleSet, Transform).
//! This is an internal service module of specd.

use crate::project::ProjectManager;
use crate::proto;
use spec_core::formal::{
    AdmissibleSet, AdmissibleSetMetadata, Constraint, ConstraintKind,
    Domain, DomainId, ModelSync, RootSpace, SpecId, TransformFunction,
    TransformId, TransformKind, TransformStrategy, UDAFModel, UniverseId,
};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tonic::{Request, Response, Status};

/// In-memory state for the UDA/f model
#[derive(Debug)]
pub struct ModelState {
    model: UDAFModel,
}

impl ModelState {
    fn new() -> Self {
        Self {
            model: UDAFModel::new(),
        }
    }
}

/// Model service implementation for specd
///
/// Manages the UDA/f model state and provides operations for
/// Universe, Domain, AdmissibleSet, and Transform.
/// All model operations are delegated here from SpecOracleService.
#[derive(Debug)]
pub struct ModelServiceImpl {
    project_manager: Arc<Mutex<ProjectManager>>,
    model_state: Arc<Mutex<ModelState>>,
}

impl ModelServiceImpl {
    pub fn new(project_manager: Arc<Mutex<ProjectManager>>) -> Self {
        Self {
            project_manager,
            model_state: Arc::new(Mutex::new(ModelState::new())),
        }
    }

    // ==========================================
    // Universe Operations
    // ==========================================

    pub async fn create_universe(
        &self,
        request: Request<proto::CreateUniverseRequest>,
    ) -> Result<Response<proto::CreateUniverseResponse>, Status> {
        let req = request.into_inner();
        let mut state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let layer = req.layer as u8;
        if layer == 0 {
            return Err(Status::invalid_argument("Layer 0 is reserved for U0 (root universe). Use layer >= 1."));
        }

        let universe_id = state.model.add_universe(layer, req.name.clone(), req.description.clone())
            .map_err(|e| Status::invalid_argument(format!("Failed to create universe: {}", e)))?;

        let universe = state.model.universes.get(&universe_id)
            .ok_or_else(|| Status::internal("Universe created but not found"))?;

        Ok(Response::new(proto::CreateUniverseResponse {
            universe: Some(to_proto_universe(&universe_id, universe)),
        }))
    }

    pub async fn get_universe(
        &self,
        request: Request<proto::GetUniverseRequest>,
    ) -> Result<Response<proto::GetUniverseResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let universe_id = UniverseId::parse(&req.id)
            .map_err(|e| Status::invalid_argument(format!("Invalid universe ID: {}", e)))?;

        let universe = state.model.universes.get(&universe_id)
            .ok_or_else(|| Status::not_found(format!("Universe not found: {}", req.id)))?;

        Ok(Response::new(proto::GetUniverseResponse {
            universe: Some(to_proto_universe(&universe_id, universe)),
        }))
    }

    pub async fn list_universes(
        &self,
        _request: Request<proto::ListUniversesRequest>,
    ) -> Result<Response<proto::ListUniversesResponse>, Status> {
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let universes: Vec<proto::UdafUniverse> = state.model.universes.iter()
            .map(|(id, u)| to_proto_universe(id, u))
            .collect();

        Ok(Response::new(proto::ListUniversesResponse { universes }))
    }

    pub async fn delete_universe(
        &self,
        request: Request<proto::DeleteUniverseRequest>,
    ) -> Result<Response<proto::DeleteUniverseResponse>, Status> {
        let req = request.into_inner();
        let mut state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let universe_id = UniverseId::parse(&req.id)
            .map_err(|e| Status::invalid_argument(format!("Invalid universe ID: {}", e)))?;

        if universe_id.layer() == 0 {
            return Err(Status::invalid_argument("Cannot delete U0 (root universe)"));
        }

        state.model.universes.remove(&universe_id)
            .ok_or_else(|| Status::not_found(format!("Universe not found: {}", req.id)))?;

        Ok(Response::new(proto::DeleteUniverseResponse {}))
    }

    // ==========================================
    // Domain Operations
    // ==========================================

    pub async fn create_domain(
        &self,
        request: Request<proto::CreateDomainRequest>,
    ) -> Result<Response<proto::CreateDomainResponse>, Status> {
        let req = request.into_inner();
        let mut state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let universe_id = UniverseId::parse(&req.universe_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid universe ID: {}", e)))?;

        if !state.model.universes.contains_key(&universe_id) {
            return Err(Status::not_found(format!("Universe not found: {}", req.universe_id)));
        }

        let domain = Domain::new(req.name.clone(), req.description.clone(), universe_id);
        let domain_id = state.model.add_domain(domain);

        let domain_ref = state.model.domains.get(&domain_id)
            .ok_or_else(|| Status::internal("Domain created but not found"))?;

        Ok(Response::new(proto::CreateDomainResponse {
            domain: Some(to_proto_domain(&domain_id, domain_ref)),
        }))
    }

    pub async fn get_domain(
        &self,
        request: Request<proto::GetDomainRequest>,
    ) -> Result<Response<proto::GetDomainResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let domain_id = DomainId::parse(&req.id)
            .map_err(|e| Status::invalid_argument(format!("Invalid domain ID: {}", e)))?;

        let domain = state.model.domains.get(&domain_id)
            .ok_or_else(|| Status::not_found(format!("Domain not found: {}", req.id)))?;

        Ok(Response::new(proto::GetDomainResponse {
            domain: Some(to_proto_domain(&domain_id, domain)),
        }))
    }

    pub async fn list_domains(
        &self,
        request: Request<proto::ListDomainsRequest>,
    ) -> Result<Response<proto::ListDomainsResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let domains: Vec<proto::UdafDomain> = state.model.domains.iter()
            .filter(|(_, d)| {
                if req.universe_id.is_empty() {
                    return true;
                }
                // Check meta first, fall back to old field
                if let Some(meta) = &d.meta {
                    if let Some(uid) = meta.get_str("universe_id") {
                        return *uid == req.universe_id;
                    }
                }
                if let Some(uid) = &d.universe_id {
                    return uid.as_str() == req.universe_id;
                }
                false
            })
            .map(|(id, d)| to_proto_domain(id, d))
            .collect();

        Ok(Response::new(proto::ListDomainsResponse { domains }))
    }

    pub async fn update_domain_constraints(
        &self,
        request: Request<proto::UpdateDomainConstraintsRequest>,
    ) -> Result<Response<proto::UpdateDomainConstraintsResponse>, Status> {
        let req = request.into_inner();
        let mut state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let domain_id = DomainId::parse(&req.domain_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid domain ID: {}", e)))?;

        let domain = state.model.domains.get_mut(&domain_id)
            .ok_or_else(|| Status::not_found(format!("Domain not found: {}", req.domain_id)))?;

        for proto_constraint in &req.constraints {
            let constraint = from_proto_constraint(proto_constraint);
            domain.add_constraint(constraint);
        }

        let domain_ref = state.model.domains.get(&domain_id)
            .ok_or_else(|| Status::internal("Domain lost after update"))?;

        Ok(Response::new(proto::UpdateDomainConstraintsResponse {
            domain: Some(to_proto_domain(&domain_id, domain_ref)),
        }))
    }

    // ==========================================
    // AdmissibleSet Operations
    // ==========================================

    pub async fn create_admissible_set(
        &self,
        request: Request<proto::CreateAdmissibleSetRequest>,
    ) -> Result<Response<proto::CreateAdmissibleSetResponse>, Status> {
        let req = request.into_inner();
        let mut state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let universe_id = UniverseId::parse(&req.universe_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid universe ID: {}", e)))?;

        if !state.model.universes.contains_key(&universe_id) {
            return Err(Status::not_found(format!("Universe not found: {}", req.universe_id)));
        }

        let spec_id = SpecId::new();
        let mut admissible_set = AdmissibleSet::new(spec_id.clone(), universe_id.clone());

        for proto_constraint in &req.constraints {
            let constraint = from_proto_constraint(proto_constraint);
            admissible_set.add_constraint(constraint);
        }

        // Add to universe's specification set
        if let Some(universe) = state.model.universes.get_mut(&universe_id) {
            universe.specifications.insert(spec_id.clone());
        }

        state.model.add_admissible_set(admissible_set);

        let aset = state.model.admissible_sets.get(&spec_id)
            .ok_or_else(|| Status::internal("AdmissibleSet created but not found"))?;

        Ok(Response::new(proto::CreateAdmissibleSetResponse {
            admissible_set: Some(to_proto_admissible_set(&spec_id, aset)),
        }))
    }

    pub async fn get_admissible_set(
        &self,
        request: Request<proto::GetAdmissibleSetRequest>,
    ) -> Result<Response<proto::GetAdmissibleSetResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let spec_id = SpecId::parse(&req.spec_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid spec ID: {}", e)))?;

        let aset = state.model.admissible_sets.get(&spec_id)
            .ok_or_else(|| Status::not_found(format!("AdmissibleSet not found: {}", req.spec_id)))?;

        Ok(Response::new(proto::GetAdmissibleSetResponse {
            admissible_set: Some(to_proto_admissible_set(&spec_id, aset)),
        }))
    }

    pub async fn list_admissible_sets(
        &self,
        request: Request<proto::ListAdmissibleSetsRequest>,
    ) -> Result<Response<proto::ListAdmissibleSetsResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let admissible_sets: Vec<proto::UdafAdmissibleSet> = state.model.admissible_sets.iter()
            .filter(|(_, a)| {
                if req.universe_id.is_empty() {
                    return true;
                }
                // Check meta first, fall back to old field
                if let Some(meta) = &a.meta {
                    return meta.universe_id.as_str() == req.universe_id;
                }
                if let Some(uid) = &a.universe_id {
                    return uid.as_str() == req.universe_id;
                }
                false
            })
            .map(|(id, a)| to_proto_admissible_set(id, a))
            .collect();

        Ok(Response::new(proto::ListAdmissibleSetsResponse { admissible_sets }))
    }

    // ==========================================
    // Verification Operations
    // ==========================================

    pub async fn verify_consistency(
        &self,
        request: Request<proto::VerifyConsistencyRequest>,
    ) -> Result<Response<proto::VerifyConsistencyResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let spec_a_id = SpecId::parse(&req.spec_a_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid spec A ID: {}", e)))?;
        let spec_b_id = SpecId::parse(&req.spec_b_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid spec B ID: {}", e)))?;

        let aset_a = state.model.admissible_sets.get(&spec_a_id)
            .ok_or_else(|| Status::not_found(format!("AdmissibleSet not found: {}", req.spec_a_id)))?;
        let aset_b = state.model.admissible_sets.get(&spec_b_id)
            .ok_or_else(|| Status::not_found(format!("AdmissibleSet not found: {}", req.spec_b_id)))?;

        // Heuristic consistency check: look for obvious constraint conflicts
        let (is_consistent, steps) = heuristic_consistency_check(aset_a, aset_b);

        let status = if is_consistent {
            proto::UdafProofStatus::Proven
        } else {
            proto::UdafProofStatus::Refuted
        };

        let proof = proto::UdafProofResult {
            id: uuid::Uuid::new_v4().to_string(),
            status: status.into(),
            property_type: "consistency".to_string(),
            steps,
            method: "heuristic".to_string(),
            metadata: HashMap::new(),
        };

        Ok(Response::new(proto::VerifyConsistencyResponse {
            proof: Some(proof),
            is_consistent,
        }))
    }

    pub async fn verify_implication(
        &self,
        request: Request<proto::VerifyImplicationRequest>,
    ) -> Result<Response<proto::VerifyImplicationResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let _antecedent_id = SpecId::parse(&req.antecedent_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid antecedent ID: {}", e)))?;
        let _consequent_id = SpecId::parse(&req.consequent_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid consequent ID: {}", e)))?;

        // Without Z3, we can only return Unknown
        let proof = proto::UdafProofResult {
            id: uuid::Uuid::new_v4().to_string(),
            status: proto::UdafProofStatus::Unknown.into(),
            property_type: "implication".to_string(),
            steps: vec![proto::UdafProofStep {
                description: "Implication checking requires SMT solver (Z3)".to_string(),
                justification: "Z3 solver not available in this build".to_string(),
            }],
            method: "heuristic".to_string(),
            metadata: HashMap::new(),
        };

        Ok(Response::new(proto::VerifyImplicationResponse {
            proof: Some(proof),
            implies: false,
        }))
    }

    // ==========================================
    // Transform Operations
    // ==========================================

    #[allow(deprecated)]
    pub async fn create_transform(
        &self,
        request: Request<proto::CreateTransformRequest>,
    ) -> Result<Response<proto::CreateTransformResponse>, Status> {
        let req = request.into_inner();
        let mut state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let source_universe = UniverseId::parse(&req.source_universe)
            .map_err(|e| Status::invalid_argument(format!("Invalid source universe: {}", e)))?;
        let target_universe = UniverseId::parse(&req.target_universe)
            .map_err(|e| Status::invalid_argument(format!("Invalid target universe: {}", e)))?;

        if !state.model.universes.contains_key(&source_universe) {
            return Err(Status::not_found(format!("Source universe not found: {}", req.source_universe)));
        }
        if !state.model.universes.contains_key(&target_universe) {
            return Err(Status::not_found(format!("Target universe not found: {}", req.target_universe)));
        }

        let kind = from_proto_transform_kind(req.kind());
        let strategy = from_proto_strategy(&req.strategy);

        let transform = match kind {
            TransformKind::Inverse => {
                TransformFunction::inverse(source_universe, req.description.clone(), strategy)
            }
            TransformKind::Forward | TransformKind::Parallel => {
                TransformFunction::forward(source_universe, target_universe, req.description.clone(), strategy)
            }
        };

        let transform_id = state.model.add_transform(transform);

        let transform_ref = state.model.transforms.get(&transform_id)
            .ok_or_else(|| Status::internal("Transform created but not found"))?;

        Ok(Response::new(proto::CreateTransformResponse {
            transform: Some(to_proto_transform(&transform_id, transform_ref)),
        }))
    }

    pub async fn get_transform(
        &self,
        request: Request<proto::GetTransformRequest>,
    ) -> Result<Response<proto::GetTransformResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let transform_id = TransformId::parse(&req.id)
            .map_err(|e| Status::invalid_argument(format!("Invalid transform ID: {}", e)))?;

        let transform = state.model.transforms.get(&transform_id)
            .ok_or_else(|| Status::not_found(format!("Transform not found: {}", req.id)))?;

        Ok(Response::new(proto::GetTransformResponse {
            transform: Some(to_proto_transform(&transform_id, transform)),
        }))
    }

    pub async fn list_transforms(
        &self,
        request: Request<proto::ListTransformsRequest>,
    ) -> Result<Response<proto::ListTransformsResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let transforms: Vec<proto::UdafTransform> = state.model.transforms.iter()
            .filter(|(_, t)| {
                if req.universe_id.is_empty() {
                    return true;
                }
                t.source_universe.as_str() == req.universe_id
            })
            .map(|(id, t)| to_proto_transform(id, t))
            .collect();

        Ok(Response::new(proto::ListTransformsResponse { transforms }))
    }

    pub async fn verify_transform_soundness(
        &self,
        request: Request<proto::VerifyTransformSoundnessRequest>,
    ) -> Result<Response<proto::VerifyTransformSoundnessResponse>, Status> {
        let req = request.into_inner();
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let transform_id = TransformId::parse(&req.transform_id)
            .map_err(|e| Status::invalid_argument(format!("Invalid transform ID: {}", e)))?;

        let _transform = state.model.transforms.get(&transform_id)
            .ok_or_else(|| Status::not_found(format!("Transform not found: {}", req.transform_id)))?;

        // Without Z3, we can only return Unknown
        let proof = proto::UdafProofResult {
            id: uuid::Uuid::new_v4().to_string(),
            status: proto::UdafProofStatus::Unknown.into(),
            property_type: "soundness".to_string(),
            steps: vec![proto::UdafProofStep {
                description: "Transform soundness checking requires SMT solver (Z3)".to_string(),
                justification: "Z3 solver not available in this build".to_string(),
            }],
            method: "heuristic".to_string(),
            metadata: HashMap::new(),
        };

        Ok(Response::new(proto::VerifyTransformSoundnessResponse {
            proof: Some(proof),
            is_sound: false,
        }))
    }

    // ==========================================
    // Projection Operations
    // ==========================================

    pub async fn construct_u0(
        &self,
        request: Request<proto::ConstructU0Request>,
    ) -> Result<Response<proto::ConstructU0Response>, Status> {
        let req = request.into_inner();
        let mut state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        // Create RootSpace from source paths
        let mut root = RootSpace::new_artifact_bundle();

        // Add source paths as metadata
        for (i, path) in req.source_paths.iter().enumerate() {
            root.meta.inner_mut().insert(
                format!("source_path_{}", i),
                path.clone(),
            );
        }
        root.proof_data.artifact_count = req.source_paths.len();

        // Add all non-U0 universes as source universes
        for universe_id in state.model.universes.keys() {
            if universe_id.layer() > 0 {
                root.proof_data.add_source_universe(universe_id.as_str().to_string());
            }
        }

        // Load repository for construct_u0
        let pm = self.project_manager.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;
        let current = pm.current_project()
            .ok_or_else(|| Status::failed_precondition("No current project set"))?;
        let project = pm.load_project(&current)
            .map_err(|e| Status::internal(format!("Failed to load project: {}", e)))?;

        let mut messages = Vec::new();

        match state.model.construct_u0(&root, &project.repository) {
            Ok(specs) => {
                messages.push(format!("Successfully constructed U0 with {} extracted specifications", specs.len()));
            }
            Err(e) => {
                messages.push(format!("Warning during U0 construction: {}", e));
            }
        }

        // Get U0 for response
        let u0_id = UniverseId::root();
        let u0 = state.model.universes.get(&u0_id)
            .ok_or_else(|| Status::internal("U0 not found after construction"))?;

        let specs_count = u0.specifications.len() as u32;

        Ok(Response::new(proto::ConstructU0Response {
            u0: Some(to_proto_universe(&u0_id, u0)),
            specs_extracted: specs_count,
            messages,
        }))
    }

    pub async fn sync_model(
        &self,
        request: Request<proto::SyncModelRequest>,
    ) -> Result<Response<proto::SyncModelResponse>, Status> {
        let req = request.into_inner();
        let mut state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let pm = self.project_manager.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;
        let current = pm.current_project()
            .ok_or_else(|| Status::failed_precondition("No current project set"))?;
        let mut project = pm.load_project(&current)
            .map_err(|e| Status::internal(format!("Failed to load project: {}", e)))?;

        let mut messages = Vec::new();

        // Sync from repository to model
        ModelSync::sync_from_repository(&mut state.model, &project.repository)
            .map_err(|e| Status::internal(format!("Sync failed: {}", e)))?;

        messages.push("Synchronized UDA/f model from repository".to_string());

        // Optionally export proof metadata back
        if req.export_proof_metadata {
            ModelSync::export_proof_metadata(&state.model, &mut project.repository)
                .map_err(|e| Status::internal(format!("Export failed: {}", e)))?;

            // Save updated repository
            pm.save_project(&project)
                .map_err(|e| Status::internal(format!("Failed to save project: {}", e)))?;

            messages.push("Exported proof metadata to repository".to_string());
        }

        Ok(Response::new(proto::SyncModelResponse {
            universes_count: state.model.universes.len() as u32,
            domains_count: state.model.domains.len() as u32,
            admissible_sets_count: state.model.admissible_sets.len() as u32,
            transforms_count: state.model.transforms.len() as u32,
            messages,
        }))
    }

    pub async fn validate_model(
        &self,
        _request: Request<proto::ValidateModelRequest>,
    ) -> Result<Response<proto::ValidateModelResponse>, Status> {
        let state = self.model_state.lock()
            .map_err(|e| Status::internal(format!("Lock error: {}", e)))?;

        let (is_valid, errors) = match state.model.validate() {
            Ok(()) => (true, vec![]),
            Err(e) => (false, e.split('\n').map(|s| s.to_string()).collect()),
        };

        Ok(Response::new(proto::ValidateModelResponse {
            is_valid,
            errors,
            universes_count: state.model.universes.len() as u32,
            domains_count: state.model.domains.len() as u32,
            admissible_sets_count: state.model.admissible_sets.len() as u32,
            transforms_count: state.model.transforms.len() as u32,
        }))
    }
}

// ==========================================
// Proto <-> Core type conversion helpers
// ==========================================

fn to_proto_universe(id: &UniverseId, u: &spec_core::formal::Universe) -> proto::UdafUniverse {
    let spec_ids: Vec<String> = u.specifications.iter()
        .map(|s| s.as_str().to_string())
        .collect();

    let metadata: HashMap<String, String> = u.metadata.inner().clone();

    proto::UdafUniverse {
        id: id.as_str().to_string(),
        name: u.name.clone(),
        description: u.description.clone(),
        layer: u.layer() as u32,
        spec_ids,
        metadata,
    }
}

fn to_proto_domain(id: &DomainId, d: &Domain) -> proto::UdafDomain {
    let name = d.name.clone().unwrap_or_default();
    let description = d.description.clone().unwrap_or_default();
    let universe_id = d.universe_id.as_ref()
        .map(|uid| uid.as_str().to_string())
        .unwrap_or_default();

    let constraints: Vec<proto::UdafConstraint> = if let Some(proof_data) = &d.proof_data {
        proof_data.constraints.iter().map(to_proto_constraint).collect()
    } else {
        vec![]
    };

    let covered_by: Vec<String> = if let Some(proof_data) = &d.proof_data {
        proof_data.covered_by.iter().map(|s| s.as_str().to_string()).collect()
    } else if let Some(covered_by) = &d.covered_by {
        covered_by.iter().map(|s| s.as_str().to_string()).collect()
    } else {
        vec![]
    };

    let subdomain_ids: Vec<String> = if let Some(subdomains) = &d.subdomains {
        subdomains.iter().map(|s| s.as_str().to_string()).collect()
    } else {
        vec![]
    };

    let metadata: HashMap<String, String> = if let Some(meta) = &d.meta {
        meta.inner().clone()
    } else if let Some(meta) = &d.metadata {
        meta.inner().clone()
    } else {
        HashMap::new()
    };

    proto::UdafDomain {
        id: id.as_str().to_string(),
        name,
        description,
        universe_id,
        constraints,
        covered_by,
        subdomain_ids,
        metadata,
    }
}

fn to_proto_admissible_set(spec_id: &SpecId, a: &AdmissibleSet) -> proto::UdafAdmissibleSet {
    let universe_id = if let Some(meta) = &a.meta {
        meta.universe_id.as_str().to_string()
    } else if let Some(uid) = &a.universe_id {
        uid.as_str().to_string()
    } else {
        String::new()
    };

    let constraints: Vec<proto::UdafConstraint> = if let Some(proof_data) = &a.proof_data {
        proof_data.constraints.iter().map(to_proto_constraint).collect()
    } else if let Some(constraints) = &a.constraints {
        constraints.iter().map(to_proto_constraint).collect()
    } else {
        vec![]
    };

    let contradicts: Vec<String> = if let Some(proof_data) = &a.proof_data {
        proof_data.contradicts.iter().map(|s| s.as_str().to_string()).collect()
    } else if let Some(contradicts) = &a.contradicts {
        contradicts.iter().map(|s| s.as_str().to_string()).collect()
    } else {
        vec![]
    };

    let metadata: HashMap<String, String> = if let Some(meta) = &a.meta {
        meta.extra.clone()
    } else if let Some(meta) = &a.metadata {
        meta.inner().clone()
    } else {
        HashMap::new()
    };

    proto::UdafAdmissibleSet {
        spec_id: spec_id.as_str().to_string(),
        universe_id,
        constraints,
        contradicts,
        metadata,
    }
}

fn to_proto_constraint(c: &Constraint) -> proto::UdafConstraint {
    let kind = match c.kind {
        ConstraintKind::Universal => proto::UdafConstraintKind::Universal,
        ConstraintKind::Existential => proto::UdafConstraintKind::Existential,
        ConstraintKind::Implication => proto::UdafConstraintKind::Implication,
        ConstraintKind::Equivalence => proto::UdafConstraintKind::Equivalence,
    };

    let description = c.description.clone().unwrap_or_default();
    let metadata: HashMap<String, String> = if let Some(meta) = &c.meta {
        meta.inner().clone()
    } else if let Some(meta) = &c.metadata {
        meta.inner().clone()
    } else {
        HashMap::new()
    };

    proto::UdafConstraint {
        formal: c.formal.clone().unwrap_or_default(),
        kind: kind.into(),
        description,
        metadata,
    }
}

fn from_proto_constraint(c: &proto::UdafConstraint) -> Constraint {
    let kind = match proto::UdafConstraintKind::try_from(c.kind) {
        Ok(proto::UdafConstraintKind::Universal) => ConstraintKind::Universal,
        Ok(proto::UdafConstraintKind::Existential) => ConstraintKind::Existential,
        Ok(proto::UdafConstraintKind::Implication) => ConstraintKind::Implication,
        Ok(proto::UdafConstraintKind::Equivalence) => ConstraintKind::Equivalence,
        _ => ConstraintKind::Universal,
    };

    let formal = if c.formal.is_empty() { None } else { Some(c.formal.clone()) };
    let description = if c.description.is_empty() { None } else { Some(c.description.clone()) };

    Constraint {
        formal,
        kind,
        description: description.clone(),
        metadata: None,
        meta: None,
    }
}

#[allow(deprecated)]
fn to_proto_transform(id: &TransformId, t: &TransformFunction) -> proto::UdafTransform {
    let kind = match t.kind {
        TransformKind::Forward => proto::UdafTransformKind::Forward,
        TransformKind::Inverse => proto::UdafTransformKind::Inverse,
        TransformKind::Parallel => proto::UdafTransformKind::Parallel,
    };

    let strategy = match &t.strategy {
        TransformStrategy::ASTAnalysis { language, extractor_config } => {
            let mut config = extractor_config.clone();
            config.insert("language".to_string(), language.clone());
            proto::UdafTransformStrategy {
                strategy_type: "ast_analysis".to_string(),
                config,
            }
        }
        TransformStrategy::NLPInference { model, prompt_template } => {
            let mut config = HashMap::new();
            config.insert("model".to_string(), model.clone());
            config.insert("prompt_template".to_string(), prompt_template.clone());
            proto::UdafTransformStrategy {
                strategy_type: "nlp_inference".to_string(),
                config,
            }
        }
        TransformStrategy::FormalVerification { tool, verification_config } => {
            let mut config = verification_config.clone();
            config.insert("tool".to_string(), tool.clone());
            proto::UdafTransformStrategy {
                strategy_type: "formal_verification".to_string(),
                config,
            }
        }
        TransformStrategy::TypeAnalysis { type_system } => {
            let mut config = HashMap::new();
            config.insert("type_system".to_string(), type_system.clone());
            proto::UdafTransformStrategy {
                strategy_type: "type_analysis".to_string(),
                config,
            }
        }
        TransformStrategy::Manual { description } => {
            let mut config = HashMap::new();
            config.insert("description".to_string(), description.clone());
            proto::UdafTransformStrategy {
                strategy_type: "manual".to_string(),
                config,
            }
        }
        TransformStrategy::Composed { .. } => {
            proto::UdafTransformStrategy {
                strategy_type: "composed".to_string(),
                config: HashMap::new(),
            }
        }
    };

    let metadata: HashMap<String, String> = t.metadata.inner().clone();

    proto::UdafTransform {
        id: id.as_str().to_string(),
        source_universe: t.source_universe.as_str().to_string(),
        target_universe: t.target_universe.as_str().to_string(),
        description: t.description.clone(),
        kind: kind.into(),
        strategy: Some(strategy),
        metadata,
    }
}

fn from_proto_transform_kind(k: proto::UdafTransformKind) -> TransformKind {
    match k {
        proto::UdafTransformKind::Inverse => TransformKind::Inverse,
        proto::UdafTransformKind::Forward => TransformKind::Forward,
        proto::UdafTransformKind::Parallel => TransformKind::Parallel,
        _ => TransformKind::Forward,
    }
}

#[allow(deprecated)]
fn from_proto_strategy(strategy: &Option<proto::UdafTransformStrategy>) -> TransformStrategy {
    match strategy {
        Some(s) => match s.strategy_type.as_str() {
            "ast_analysis" => {
                let language = s.config.get("language").cloned().unwrap_or_else(|| "rust".to_string());
                let mut extractor_config = s.config.clone();
                extractor_config.remove("language");
                TransformStrategy::ASTAnalysis { language, extractor_config }
            }
            "nlp_inference" => {
                let model = s.config.get("model").cloned().unwrap_or_default();
                let prompt_template = s.config.get("prompt_template").cloned().unwrap_or_default();
                TransformStrategy::NLPInference { model, prompt_template }
            }
            "formal_verification" => {
                let tool = s.config.get("tool").cloned().unwrap_or_default();
                let mut verification_config = s.config.clone();
                verification_config.remove("tool");
                TransformStrategy::FormalVerification { tool, verification_config }
            }
            "type_analysis" => {
                let type_system = s.config.get("type_system").cloned().unwrap_or_default();
                TransformStrategy::TypeAnalysis { type_system }
            }
            _ => {
                let description = s.config.get("description").cloned().unwrap_or_else(|| s.strategy_type.clone());
                TransformStrategy::Manual { description }
            }
        },
        None => TransformStrategy::Manual {
            description: "No strategy specified".to_string(),
        },
    }
}

// ==========================================
// Heuristic verification helpers
// ==========================================

/// Heuristic consistency check between two admissible sets
///
/// Looks for obvious constraint conflicts like min/max contradictions.
/// Returns (is_consistent, proof_steps).
fn heuristic_consistency_check(
    a: &AdmissibleSet,
    b: &AdmissibleSet,
) -> (bool, Vec<proto::UdafProofStep>) {
    let mut steps = Vec::new();
    let mut is_consistent = true;

    // Get constraints from both sets
    let constraints_a: Vec<&Constraint> = if let Some(pd) = &a.proof_data {
        pd.constraints.iter().collect()
    } else if let Some(c) = &a.constraints {
        c.iter().collect()
    } else {
        vec![]
    };

    let constraints_b: Vec<&Constraint> = if let Some(pd) = &b.proof_data {
        pd.constraints.iter().collect()
    } else if let Some(c) = &b.constraints {
        c.iter().collect()
    } else {
        vec![]
    };

    steps.push(proto::UdafProofStep {
        description: format!("Checking {} constraints from A against {} constraints from B", constraints_a.len(), constraints_b.len()),
        justification: "Heuristic pairwise constraint analysis".to_string(),
    });

    // Check for min/max conflicts
    for ca in &constraints_a {
        if let Some(formal_a) = &ca.formal {
            for cb in &constraints_b {
                if let Some(formal_b) = &cb.formal {
                    if let Some(conflict) = detect_min_max_conflict(formal_a, formal_b) {
                        is_consistent = false;
                        steps.push(proto::UdafProofStep {
                            description: format!("Constraint conflict detected: {} vs {}", formal_a, formal_b),
                            justification: conflict,
                        });
                    }
                }
            }
        }
    }

    if is_consistent {
        steps.push(proto::UdafProofStep {
            description: "No obvious constraint conflicts found".to_string(),
            justification: "Heuristic analysis passed (not a formal proof)".to_string(),
        });
    }

    (is_consistent, steps)
}

/// Detect obvious min/max conflicts between two formal constraints
fn detect_min_max_conflict(formal_a: &str, formal_b: &str) -> Option<String> {
    let min_a = extract_min_value(formal_a);
    let max_b = extract_max_value(formal_b);

    if let (Some(min), Some(max)) = (min_a, max_b) {
        if min > max {
            return Some(format!("Minimum {} exceeds maximum {}", min, max));
        }
    }

    let min_b = extract_min_value(formal_b);
    let max_a = extract_max_value(formal_a);

    if let (Some(min), Some(max)) = (min_b, max_a) {
        if min > max {
            return Some(format!("Minimum {} exceeds maximum {}", min, max));
        }
    }

    None
}

fn extract_min_value(formal: &str) -> Option<i64> {
    if formal.starts_with(">=") {
        formal[2..].trim().parse().ok()
    } else if formal.starts_with("> ") || formal.starts_with(">") {
        formal.trim_start_matches('>').trim().parse::<i64>().ok().map(|v| v + 1)
    } else {
        None
    }
}

fn extract_max_value(formal: &str) -> Option<i64> {
    if formal.starts_with("<=") {
        formal[2..].trim().parse().ok()
    } else if formal.starts_with("< ") || formal.starts_with("<") {
        formal.trim_start_matches('<').trim().parse::<i64>().ok().map(|v| v - 1)
    } else {
        None
    }
}
