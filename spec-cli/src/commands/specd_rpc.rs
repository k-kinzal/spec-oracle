//! specd RPC Operations Commands
//!
//! CLI command implementations for specd's RPC operations.
//! These operations manage the UDA/f model (Universe, Domain, AdmissibleSet, Transform).

use crate::proto::spec_oracle_client::SpecOracleClient;
use crate::proto;
use tonic::Request;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

// ==========================================
// Universe Operations
// ==========================================

pub async fn execute_universe_create(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    layer: u32,
    name: String,
    description: String,
) -> Result<()> {
    let req = proto::CreateUniverseRequest {
        layer,
        name: name.clone(),
        description: description.clone(),
    };

    let resp = client.create_universe(Request::new(req)).await?;
    let universe = resp.into_inner().universe.unwrap_or_default();

    println!("✅ Created Universe:");
    println!("  ID: {}", universe.id);
    println!("  Layer: U{}", universe.layer);
    println!("  Name: {}", universe.name);
    println!("  Description: {}", universe.description);

    Ok(())
}

pub async fn execute_universe_list(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
) -> Result<()> {
    let req = proto::ListUniversesRequest {};
    let resp = client.list_universes(Request::new(req)).await?;
    let universes = resp.into_inner().universes;

    if universes.is_empty() {
        println!("No universes found (only U0 exists by default)");
        return Ok(());
    }

    println!("Universes ({}):", universes.len());
    for universe in universes {
        println!(
            "  U{} - {} - {}",
            universe.layer, universe.name, universe.description
        );
    }

    Ok(())
}

pub async fn execute_universe_get(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    id: String,
) -> Result<()> {
    let req = proto::GetUniverseRequest { id: id.clone() };
    let resp = client.get_universe(Request::new(req)).await?;
    let universe = resp.into_inner().universe.unwrap_or_default();

    println!("Universe {}:", universe.id);
    println!("  Layer: U{}", universe.layer);
    println!("  Name: {}", universe.name);
    println!("  Description: {}", universe.description);

    Ok(())
}

pub async fn execute_universe_delete(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    id: String,
) -> Result<()> {
    let req = proto::DeleteUniverseRequest { id: id.clone() };
    client.delete_universe(Request::new(req)).await?;
    println!("✅ Deleted universe: {}", id);

    Ok(())
}

// ==========================================
// Domain Operations
// ==========================================

pub async fn execute_domain_create(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    universe_id: String,
    name: String,
    description: String,
) -> Result<()> {
    let req = proto::CreateDomainRequest {
        universe_id: universe_id.clone(),
        name: name.clone(),
        description: description.clone(),
    };

    let resp = client.create_domain(Request::new(req)).await?;
    let domain = resp.into_inner().domain.unwrap_or_default();

    println!("✅ Created Domain:");
    println!("  ID: {}", domain.id);
    println!("  Universe: {}", domain.universe_id);
    println!("  Name: {}", domain.name);
    println!("  Description: {}", domain.description);

    Ok(())
}

pub async fn execute_domain_get(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    id: String,
) -> Result<()> {
    let req = proto::GetDomainRequest { id: id.clone() };
    let resp = client.get_domain(Request::new(req)).await?;
    let domain = resp.into_inner().domain.unwrap_or_default();

    println!("Domain {}:", domain.id);
    println!("  Universe: {}", domain.universe_id);
    println!("  Name: {}", domain.name);
    println!("  Description: {}", domain.description);
    println!("  Constraints: {}", domain.constraints.len());

    Ok(())
}

pub async fn execute_domain_list(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    universe_id: Option<String>,
) -> Result<()> {
    let req = proto::ListDomainsRequest {
        universe_id: universe_id.unwrap_or_default(),
    };
    let resp = client.list_domains(Request::new(req)).await?;
    let domains = resp.into_inner().domains;

    if domains.is_empty() {
        println!("No domains found");
        return Ok(());
    }

    println!("Domains ({}):", domains.len());
    for domain in domains {
        println!("  {} - {} (Universe: {})", domain.id, domain.name, domain.universe_id);
        println!("    {}", domain.description);
    }

    Ok(())
}

pub async fn execute_domain_update_constraints(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    domain_id: String,
    constraints: Vec<String>,
) -> Result<()> {
    // Convert string constraints to proto Constraint messages
    let proto_constraints = constraints
        .into_iter()
        .map(|desc| proto::UdafConstraint {
            formal: desc.clone(),
            kind: 1, // UNIVERSAL by default
            description: desc,
            metadata: std::collections::HashMap::new(),
        })
        .collect();

    let req = proto::UpdateDomainConstraintsRequest {
        domain_id: domain_id.clone(),
        constraints: proto_constraints,
    };

    let resp = client.update_domain_constraints(Request::new(req)).await?;
    let domain = resp.into_inner().domain.unwrap_or_default();

    println!("✅ Updated Domain Constraints:");
    println!("  Domain ID: {}", domain.id);
    println!("  Total Constraints: {}", domain.constraints.len());
    for constraint in &domain.constraints {
        println!("    - {}", constraint.description);
    }

    Ok(())
}

// ==========================================
// Transform Operations
// ==========================================

pub async fn execute_transform_create(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    source: String,
    target: String,
    kind: String,
) -> Result<()> {
    // Parse kind string to proto enum
    let kind_value = match kind.to_lowercase().as_str() {
        "forward" => 1,  // FORWARD
        "inverse" => 2,  // INVERSE
        "parallel" => 3, // PARALLEL
        _ => {
            eprintln!("Invalid transform kind: {}. Use forward, inverse, or parallel", kind);
            return Err(format!("Invalid transform kind: {}", kind).into());
        }
    };

    let req = proto::CreateTransformRequest {
        source_universe: source.clone(),
        target_universe: target.clone(),
        description: format!("Transform from {} to {}", source, target),
        kind: kind_value,
        strategy: Some(proto::UdafTransformStrategy {
            strategy_type: "manual".to_string(),
            config: std::collections::HashMap::new(),
        }),
    };

    let resp = client.create_transform(Request::new(req)).await?;
    let transform = resp.into_inner().transform.unwrap_or_default();

    println!("✅ Created Transform:");
    println!("  ID: {}", transform.id);
    println!("  {} → {}", transform.source_universe, transform.target_universe);
    println!("  Description: {}", transform.description);

    Ok(())
}

pub async fn execute_transform_get(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    id: String,
) -> Result<()> {
    let req = proto::GetTransformRequest { id: id.clone() };
    let resp = client.get_transform(Request::new(req)).await?;
    let transform = resp.into_inner().transform.unwrap_or_default();

    println!("Transform {}:", transform.id);
    println!("  {} → {}", transform.source_universe, transform.target_universe);
    println!("  Description: {}", transform.description);
    println!("  Kind: {}", transform.kind);

    Ok(())
}

pub async fn execute_transform_list(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
) -> Result<()> {
    let req = proto::ListTransformsRequest {
        universe_id: String::new(),
    };
    let resp = client.list_transforms(Request::new(req)).await?;
    let transforms = resp.into_inner().transforms;

    if transforms.is_empty() {
        println!("No transforms found");
        return Ok(());
    }

    println!("Transforms ({}):", transforms.len());
    for transform in transforms {
        println!(
            "  {} → {} ({})",
            transform.source_universe, transform.target_universe, transform.id
        );
    }

    Ok(())
}

pub async fn execute_transform_verify_soundness(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    transform_id: String,
) -> Result<()> {
    let req = proto::VerifyTransformSoundnessRequest {
        transform_id: transform_id.clone(),
    };

    let resp = client.verify_transform_soundness(Request::new(req)).await?;
    let result = resp.into_inner();

    if result.is_sound {
        println!("✅ Transform {} is sound", transform_id);
    } else {
        println!("❌ Transform {} is NOT sound", transform_id);
    }

    if let Some(proof) = result.proof {
        println!("  Status: {:?}", proof.status);
        println!("  Property: {}", proof.property_type);
        println!("  Method: {}", proof.method);

        if !proof.steps.is_empty() {
            println!("  Proof Steps:");
            for (i, step) in proof.steps.iter().enumerate() {
                println!("    {}. {}", i + 1, step.description);
                if !step.justification.is_empty() {
                    println!("       Justification: {}", step.justification);
                }
            }
        }
    }

    Ok(())
}

// ==========================================
// AdmissibleSet Operations
// ==========================================

pub async fn execute_admissible_set_create(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    spec: String,
    constraint: Vec<String>,
) -> Result<()> {
    // Convert string constraints to proto Constraint messages
    let proto_constraints = constraint
        .into_iter()
        .map(|desc| proto::UdafConstraint {
            formal: desc.clone(),
            kind: 1, // UNIVERSAL by default
            description: desc,
            metadata: std::collections::HashMap::new(),
        })
        .collect();

    let req = proto::CreateAdmissibleSetRequest {
        universe_id: spec.clone(),
        constraints: proto_constraints,
        metadata: std::collections::HashMap::new(),
    };

    let resp = client.create_admissible_set(Request::new(req)).await?;
    let admissible_set = resp.into_inner().admissible_set.unwrap_or_default();

    println!("✅ Created AdmissibleSet:");
    println!("  Spec ID: {}", admissible_set.spec_id);
    println!("  Universe: {}", admissible_set.universe_id);
    println!("  Constraints: {}", admissible_set.constraints.len());

    Ok(())
}

pub async fn execute_admissible_set_get(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    spec: String,
) -> Result<()> {
    let req = proto::GetAdmissibleSetRequest {
        spec_id: spec.clone(),
    };
    let resp = client.get_admissible_set(Request::new(req)).await?;
    let admissible_set = resp.into_inner().admissible_set.unwrap_or_default();

    println!("AdmissibleSet for {}:", admissible_set.spec_id);
    println!("  Universe: {}", admissible_set.universe_id);
    println!("  Constraints ({}):", admissible_set.constraints.len());
    for constraint in &admissible_set.constraints {
        println!("    - {}", constraint.description);
    }

    if !admissible_set.contradicts.is_empty() {
        println!("  Contradicts:");
        for spec_id in &admissible_set.contradicts {
            println!("    - {}", spec_id);
        }
    }

    Ok(())
}

pub async fn execute_admissible_set_list(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
) -> Result<()> {
    let req = proto::ListAdmissibleSetsRequest {
        universe_id: String::new(),
    };
    let resp = client.list_admissible_sets(Request::new(req)).await?;
    let sets = resp.into_inner().admissible_sets;

    if sets.is_empty() {
        println!("No admissible sets found");
        return Ok(());
    }

    println!("AdmissibleSets ({}):", sets.len());
    for set in sets {
        println!(
            "  Spec {} - {} constraint(s)",
            set.spec_id,
            set.constraints.len()
        );
    }

    Ok(())
}

pub async fn execute_admissible_set_verify_consistency(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    spec_a_id: String,
    spec_b_id: String,
) -> Result<()> {
    let req = proto::VerifyConsistencyRequest {
        spec_a_id: spec_a_id.clone(),
        spec_b_id: spec_b_id.clone(),
    };

    let resp = client.verify_consistency(Request::new(req)).await?;
    let result = resp.into_inner();

    if result.is_consistent {
        println!("✅ Specifications {} and {} are CONSISTENT", spec_a_id, spec_b_id);
        println!("   A₁ ∩ A₂ ≠ ∅ (admissible sets have non-empty intersection)");
    } else {
        println!("❌ Specifications {} and {} are INCONSISTENT", spec_a_id, spec_b_id);
        println!("   A₁ ∩ A₂ = ∅ (admissible sets are disjoint)");
    }

    if let Some(proof) = result.proof {
        println!("\n  Proof Details:");
        println!("    Status: {:?}", proof.status);
        println!("    Property: {}", proof.property_type);
        println!("    Method: {}", proof.method);

        if !proof.steps.is_empty() {
            println!("    Steps:");
            for (i, step) in proof.steps.iter().enumerate() {
                println!("      {}. {}", i + 1, step.description);
            }
        }
    }

    Ok(())
}

pub async fn execute_admissible_set_verify_implication(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    antecedent_id: String,
    consequent_id: String,
) -> Result<()> {
    let req = proto::VerifyImplicationRequest {
        antecedent_id: antecedent_id.clone(),
        consequent_id: consequent_id.clone(),
    };

    let resp = client.verify_implication(Request::new(req)).await?;
    let result = resp.into_inner();

    if result.implies {
        println!("✅ {} IMPLIES {}", antecedent_id, consequent_id);
        println!("   A_antecedent ⊆ A_consequent");
    } else {
        println!("❌ {} does NOT IMPLY {}", antecedent_id, consequent_id);
        println!("   A_antecedent ⊄ A_consequent");
    }

    if let Some(proof) = result.proof {
        println!("\n  Proof Details:");
        println!("    Status: {:?}", proof.status);
        println!("    Property: {}", proof.property_type);
        println!("    Method: {}", proof.method);

        if !proof.steps.is_empty() {
            println!("    Steps:");
            for (i, step) in proof.steps.iter().enumerate() {
                println!("      {}. {}", i + 1, step.description);
            }
        }
    }

    Ok(())
}

// ==========================================
// Projection Operations
// ==========================================

pub async fn execute_construct_u0(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
    artifact: Vec<String>,
) -> Result<()> {
    let req = proto::ConstructU0Request {
        source_paths: artifact.clone(),
    };

    let resp = client.construct_u0(Request::new(req)).await?;
    let result = resp.into_inner();

    println!("✅ Constructed U0:");
    if let Some(u0) = result.u0 {
        println!("  Universe ID: {}", u0.id);
        println!("  Name: {}", u0.name);
        println!("  Specifications: {}", u0.spec_ids.len());
    }
    println!("  Specs Extracted: {}", result.specs_extracted);

    if !result.messages.is_empty() {
        println!("\nMessages:");
        for msg in &result.messages {
            println!("  - {}", msg);
        }
    }

    Ok(())
}

pub async fn execute_sync_model(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
) -> Result<()> {
    let req = proto::SyncModelRequest {
        export_proof_metadata: false,
    };

    let resp = client.sync_model(Request::new(req)).await?;
    let result = resp.into_inner();

    println!("✅ Model Synced:");
    println!("  Universes: {}", result.universes_count);
    println!("  Domains: {}", result.domains_count);
    println!("  AdmissibleSets: {}", result.admissible_sets_count);
    println!("  Transforms: {}", result.transforms_count);

    if !result.messages.is_empty() {
        println!("\nMessages:");
        for msg in &result.messages {
            println!("  - {}", msg);
        }
    }

    Ok(())
}

pub async fn execute_validate_model(
    client: &mut SpecOracleClient<tonic::transport::Channel>,
) -> Result<()> {
    let req = proto::ValidateModelRequest {};

    let resp = client.validate_model(Request::new(req)).await?;
    let result = resp.into_inner();

    if result.is_valid {
        println!("✅ Model is valid");
        println!("  Universes: {}", result.universes_count);
        println!("  Domains: {}", result.domains_count);
        println!("  AdmissibleSets: {}", result.admissible_sets_count);
        println!("  Transforms: {}", result.transforms_count);
    } else {
        println!("❌ Model is invalid");
        if !result.errors.is_empty() {
            println!("\nErrors:");
            for error in &result.errors {
                println!("  - {}", error);
            }
        }
    }

    Ok(())
}
