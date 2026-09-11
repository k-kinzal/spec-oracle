//! Pure operational structure derived from constrained specification sentences.
//!
//! Logical implication answers whether one assertion entails another.
//! Operational structure preserves the grammatical roles needed to judge a
//! different relation: whether a lower-layer behavior realizes an upper-layer
//! behavior. Shared words and Entity identity remain discovery signals; they
//! do not establish support without compatible action, actor, object, means,
//! scope, and direction.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use so_lang::ast::{
    ClauseBody, ClauseGroup, Conj, Core, Det, Frame, Np, NpGroup, RolePp, Sentence, Vp, VpGroup,
};

use crate::semantics::{
    claim_polarity, denote, force, np_full, speech_act, subject_skeleton_of, Claim, Denotation,
    Force, Polarity, Quantifier, SpeechAct,
};

pub const OPERATIONAL_METHOD: &str = "so-reason.operational-profile";
pub const OPERATIONAL_VERSION: &str = "so-reason/operational-profile-v2";

/// Determiner-free, full-fidelity identity of one entity kind.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct EntityRef {
    pub full: String,
    pub head: String,
    pub display: String,
}

impl EntityRef {
    fn from_np(np: &Np) -> Self {
        Self {
            full: np_full(np),
            head: np.head.to_lowercase(),
            display: np.render(),
        }
    }

    fn from_surface(full: &str, display: &str) -> Self {
        let head = concept_token_sequence(full)
            .into_iter()
            .last()
            .unwrap_or_else(|| full.to_lowercase());
        Self {
            full: full.trim().to_lowercase(),
            head,
            display: display.trim().to_string(),
        }
    }
}

/// Boolean grouping written at one engagement site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GroupConjunction {
    Single,
    And,
    Or,
}

impl From<Option<Conj>> for GroupConjunction {
    fn from(value: Option<Conj>) -> Self {
        match value {
            None => Self::Single,
            Some(Conj::And) => Self::And,
            Some(Conj::Or) => Self::Or,
        }
    }
}

/// Where the dependent specification engages an entity kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EngagementSite {
    Subject,
    Means,
    Trigger,
    StateGuard,
    ScopeGuard,
}

/// An affirmative binding claim whose object requires at least one instance.
///
/// This is not a claim that the verb creates the object.  It records the
/// weaker and grammar-grounded fact that satisfying the claim involves an
/// instance of the object entity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Witness {
    pub entity: EntityRef,
    pub quantifier: Quantifier,
    pub anchor: String,
}

/// One entity kind governed by a claim or one of its applicability guards.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Engagement {
    pub entity: EntityRef,
    pub site: EngagementSite,
    pub group: String,
    pub conjunction: GroupConjunction,
    pub position: usize,
    pub anchor: String,
}

/// One object constrained by an affirmative binding action.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BindingObject {
    pub entity: EntityRef,
    pub quantifier: Quantifier,
    pub anchor: String,
}

/// The action, responsible actor, object and explicitly written means of one
/// affirmative binding claim.  Unlike a Term index this retains grammatical
/// roles, so a view can assess whether a lower-layer behavior realizes an
/// upper-layer behavior instead of treating shared words as support.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationalClaim {
    pub action: Vec<String>,
    pub actors: Vec<EntityRef>,
    pub objects: Vec<BindingObject>,
    pub means: Vec<EntityRef>,
}

/// The operational view of one authored sentence.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationalProfile {
    pub witnesses: Vec<Witness>,
    pub engagements: Vec<Engagement>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub claim: Option<OperationalClaim>,
}

/// Derive operational witnesses and engagements without environmental I/O.
pub fn operational_profile(sentence: &Sentence) -> OperationalProfile {
    let mut profile = OperationalProfile::default();
    profile.claim = derive_operational_claim(sentence);
    if let Some(claim) = &profile.claim {
        profile
            .witnesses
            .extend(claim.objects.iter().map(|object| Witness {
                entity: object.entity.clone(),
                quantifier: object.quantifier,
                anchor: object.anchor.clone(),
            }));
    }
    derive_core_engagements(sentence, &mut profile.engagements);
    derive_means_engagements(sentence, &mut profile.engagements);
    if let Some(trigger) = &sentence.frames.trigger {
        derive_clause_group_engagements(
            &trigger.clause,
            EngagementSite::Trigger,
            "trigger",
            &mut profile.engagements,
        );
    }
    for (index, frame) in sentence.frames.states.iter().enumerate() {
        derive_frame_engagements(
            frame,
            EngagementSite::StateGuard,
            &format!("state:{index}"),
            &mut profile.engagements,
        );
    }
    for (index, frame) in sentence.frames.scopes.iter().enumerate() {
        derive_frame_engagements(
            frame,
            EngagementSite::ScopeGuard,
            &format!("scope:{index}"),
            &mut profile.engagements,
        );
    }
    profile
        .witnesses
        .sort_by(|left, right| (&left.entity, &left.anchor).cmp(&(&right.entity, &right.anchor)));
    profile.witnesses.dedup();
    profile.engagements.sort_by(|left, right| {
        (
            left.group.as_str(),
            left.position,
            &left.entity,
            &left.anchor,
        )
            .cmp(&(
                right.group.as_str(),
                right.position,
                &right.entity,
                &right.anchor,
            ))
    });
    profile.engagements.dedup();
    profile
}

fn derive_operational_claim(sentence: &Sentence) -> Option<OperationalClaim> {
    if speech_act(sentence) != SpeechAct::Obligation || force(sentence) != Some(Force::Binding) {
        return None;
    }
    let Denotation::Behavior(assertion) = denote(sentence) else {
        return None;
    };
    if claim_polarity(&assertion.claim, &assertion.subject) != Polarity::Affirmative {
        return None;
    }
    let Claim::Action { vp, .. } = &assertion.claim else {
        return None;
    };
    // A written choice witnesses neither branch by itself.
    let VpGroup::Single(vp) = vp else {
        return None;
    };
    let Core::Deontic { subject, .. } = &sentence.core else {
        return None;
    };
    let actors = np_items(subject)
        .iter()
        .filter(|np| engages(np))
        .map(|np| EntityRef::from_np(np))
        .collect();
    let mut action = vec![vp.verb.to_lowercase()];
    action.extend(vp.particle.iter().map(|particle| particle.to_lowercase()));
    let (objects, recovered_means) = derive_binding_objects(vp);
    let mut means: Vec<EntityRef> = vp
        .roles
        .iter()
        .filter_map(|role| match role {
            RolePp::Means { np, .. } => Some(np_items(np)),
            _ => None,
        })
        .flatten()
        .map(|np| EntityRef::from_np(np))
        .chain(recovered_means)
        .collect();
    means.sort();
    means.dedup();
    Some(OperationalClaim {
        action,
        actors,
        objects,
        means,
    })
}

fn derive_binding_objects(vp: &Vp) -> (Vec<BindingObject>, Vec<EntityRef>) {
    let Some(objects) = &vp.object else {
        return (Vec::new(), Vec::new());
    };
    let items = match objects {
        NpGroup::Single(np) => std::slice::from_ref(np),
        NpGroup::Coordinated {
            conj: Conj::And,
            items,
            ..
        } => items.as_slice(),
        NpGroup::Coordinated { conj: Conj::Or, .. } => return (Vec::new(), Vec::new()),
    };
    let mut derived = Vec::new();
    let mut means = Vec::new();
    for np in items {
        let Some(quantifier) = existential_object_quantifier(&np.det) else {
            continue;
        };
        let (entity, recovered_means) = split_surface_through_means(np);
        if let Some(recovered_means) = recovered_means {
            means.push(recovered_means);
        }
        derived.push(BindingObject {
            anchor: entity.display.clone(),
            entity,
            quantifier,
        });
    }
    (derived, means)
}

/// The v0.2 grammar deliberately reserves `via` and `using` as structured
/// means.  Historical accepted specifications also contain the unambiguous
/// bounded form ``<object> through `<identifier>` ``.  Recover only that
/// backticked final identifier; arbitrary open-class `through` text remains
/// part of the object and cannot silently become a support relation.
fn split_surface_through_means(np: &Np) -> (EntityRef, Option<EntityRef>) {
    let full = np_full(np);
    let Some((object_full, means_full)) = full.rsplit_once(" through ") else {
        return (EntityRef::from_np(np), None);
    };
    if !(means_full.starts_with('`')
        && means_full.ends_with('`')
        && means_full[1..means_full.len() - 1].contains(char::is_whitespace))
    {
        return (EntityRef::from_np(np), None);
    }
    let rendered = np.render();
    let rendered_lower = rendered.to_lowercase();
    let Some(boundary) = rendered_lower.rfind(" through ") else {
        return (EntityRef::from_np(np), None);
    };
    let object_display = &rendered[..boundary];
    let means_display = &rendered[boundary + " through ".len()..];
    (
        EntityRef::from_surface(object_full, object_display),
        Some(EntityRef::from_surface(means_full, means_display)),
    )
}

fn existential_object_quantifier(det: &Option<Det>) -> Option<Quantifier> {
    match det {
        Some(Det::A) | Some(Det::An) => Some(Quantifier::Existential),
        Some(Det::AtLeast { n }) if *n >= 1 => Some(Quantifier::Count {
            op: crate::semantics::CountOp::AtLeast,
            n: *n,
        }),
        Some(Det::Exactly { n }) if *n >= 1 => Some(Quantifier::Count {
            op: crate::semantics::CountOp::Exactly,
            n: *n,
        }),
        _ => None,
    }
}

fn derive_core_engagements(sentence: &Sentence, engagements: &mut Vec<Engagement>) {
    let subject = match &sentence.core {
        Core::Definition { .. } => return,
        Core::Description { subject, .. } | Core::Deontic { subject, .. } => subject,
    };
    derive_np_group_engagements(subject, EngagementSite::Subject, "subject", engagements);
}

fn derive_means_engagements(sentence: &Sentence, engagements: &mut Vec<Engagement>) {
    let Some(claim) = derive_operational_claim(sentence) else {
        return;
    };
    for (position, entity) in claim.means.into_iter().enumerate() {
        engagements.push(Engagement {
            anchor: entity.display.clone(),
            entity,
            site: EngagementSite::Means,
            group: "means".to_string(),
            conjunction: GroupConjunction::Single,
            position,
        });
    }
}

fn derive_frame_engagements(
    frame: &Frame,
    site: EngagementSite,
    group: &str,
    engagements: &mut Vec<Engagement>,
) {
    derive_clause_group_engagements(&frame.clause, site, group, engagements);
}

fn derive_clause_group_engagements(
    clauses: &ClauseGroup,
    site: EngagementSite,
    group: &str,
    engagements: &mut Vec<Engagement>,
) {
    let conjunction = if clauses.items.len() == 1 {
        match &clauses.items[0].subject {
            NpGroup::Single(_) => GroupConjunction::from(clauses.conj),
            NpGroup::Coordinated { conj, .. } => GroupConjunction::from(Some(*conj)),
        }
    } else {
        GroupConjunction::from(clauses.conj)
    };
    let mut position = 0;
    for (clause_index, clause) in clauses.items.iter().enumerate() {
        let elided_head = coordinated_elided_head(clauses, clause_index);
        for np in np_items(&clause.subject) {
            if !engages(np) {
                continue;
            }
            let mut entity = EntityRef::from_np(np);
            if let Some(head) = elided_head {
                entity.full = format!("{} {}", entity.full, head.to_lowercase());
                entity.head = head.to_lowercase();
                entity.display = format!("{} {head}", entity.display);
            }
            engagements.push(Engagement {
                anchor: entity.display.clone(),
                entity,
                site,
                group: group.to_string(),
                conjunction,
                position,
            });
            position += 1;
        }
    }
}

/// Recover a coordinated compound-noun head that the open-class grammar must
/// otherwise read as the first clause's verb:
///
/// `a NodeAdded Event or EvidenceRequestsReplaced Event is delivered`
///
/// parses the first arm as subject `a NodeAdded`, verb `Event`.  The sibling
/// arm makes the ellipsis checkable: its subject's head is the same word and
/// it has a copular body.  No Event/Command vocabulary is hard-coded here.
fn coordinated_elided_head(clauses: &ClauseGroup, index: usize) -> Option<&str> {
    clauses.conj?;
    let clause = clauses.items.get(index)?;
    let ClauseBody::Verbal {
        verb,
        particle: None,
        manner,
        object: None,
        roles,
        content: None,
    } = &clause.body
    else {
        return None;
    };
    if !manner.is_empty() || !roles.is_empty() {
        return None;
    }
    clauses.items.iter().skip(index + 1).find_map(|sibling| {
        if !matches!(sibling.body, ClauseBody::Copular { .. }) {
            return None;
        }
        np_items(&sibling.subject)
            .iter()
            .any(|np| np.head.eq_ignore_ascii_case(verb))
            .then_some(verb.as_str())
    })
}

fn derive_np_group_engagements(
    group: &NpGroup,
    site: EngagementSite,
    group_name: &str,
    engagements: &mut Vec<Engagement>,
) {
    let conjunction = match group {
        NpGroup::Single(_) => GroupConjunction::Single,
        NpGroup::Coordinated { conj, .. } => GroupConjunction::from(Some(*conj)),
    };
    for (position, np) in np_items(group).iter().enumerate() {
        if !engages(np) {
            continue;
        }
        engagements.push(Engagement {
            entity: EntityRef::from_np(np),
            site,
            group: group_name.to_string(),
            conjunction,
            position,
            anchor: np.render(),
        });
    }
}

fn np_items(group: &NpGroup) -> &[Np] {
    match group {
        NpGroup::Single(np) => std::slice::from_ref(np),
        NpGroup::Coordinated { items, .. } => items,
    }
}

fn engages(np: &Np) -> bool {
    match subject_skeleton_of(np).quantifier {
        Quantifier::Universal | Quantifier::Definite => true,
        Quantifier::Count { n, .. } => n >= 1,
        Quantifier::Existential | Quantifier::None | Quantifier::Negative => false,
    }
}

/// Stable lexical atoms for comparing already structured operational roles.
///
/// These tokens never establish support on their own.  They are consulted
/// only after action, actor/object role and direction gates have succeeded.
pub fn concept_tokens(value: &str) -> Vec<String> {
    let mut normalized = concept_token_sequence(value);
    normalized.sort();
    normalized.dedup();
    normalized
}

fn concept_token_sequence(value: &str) -> Vec<String> {
    let mut words = Vec::new();
    let mut current = String::new();
    let mut previous_lower_or_digit = false;
    for character in value.chars() {
        let boundary = character.is_uppercase() && previous_lower_or_digit && !current.is_empty();
        if boundary {
            words.push(std::mem::take(&mut current));
        }
        if character.is_alphanumeric() {
            current.extend(character.to_lowercase());
            previous_lower_or_digit = character.is_lowercase() || character.is_ascii_digit();
        } else {
            if !current.is_empty() {
                words.push(std::mem::take(&mut current));
            }
            previous_lower_or_digit = false;
        }
    }
    if !current.is_empty() {
        words.push(current);
    }
    words
        .into_iter()
        .map(|word| {
            if word == "spec" {
                "specification".to_string()
            } else {
                word
            }
        })
        .filter(|word| {
            !matches!(
                word.as_str(),
                "a" | "an"
                    | "the"
                    | "of"
                    | "to"
                    | "in"
                    | "on"
                    | "at"
                    | "by"
                    | "for"
                    | "from"
                    | "with"
                    | "through"
                    | "and"
                    | "or"
            )
        })
        .collect()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RealizationBasis {
    ExplicitMeans,
    ObjectRefinement,
}

/// A checkable lower-layer-to-upper-layer realization judgment.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LayeredRealization {
    pub basis: RealizationBasis,
    pub action: Vec<String>,
    pub shared_object_tokens: Vec<String>,
    pub scope_tokens: Vec<String>,
    pub strength: f64,
}

/// Why one lower-layer specification structurally composes an upper one
/// through an exact operational Entity.
///
/// This is not logical implication. It is a graph-grounded constitutive
/// relation: the upper behavior binds an instance of an Entity, while the
/// lower behavior specifies that exact Entity as its responsible subject or
/// as the trigger of a downstream reaction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EntityCompositionBasis {
    SubjectElaboration,
    TriggerContinuation,
}

/// One exact Entity bridge from a lower specification to an upper
/// specification.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EntityComposition {
    pub basis: EntityCompositionBasis,
    pub entity: EntityRef,
    pub strength: f64,
}

/// Derive lower-layer→upper-layer constitutive relations through exact
/// operational roles.
///
/// `upper` must affirmatively bind an object instance. `lower` must engage the
/// exact same full-fidelity Entity either as its subject (the Entity's own
/// behavior elaborates the upper claim) or as a trigger (a downstream
/// reaction continues the upper behavior). Means and state/scope guards are
/// deliberately excluded: merely using or being conditional on the same
/// Entity establishes relatedness, not constitutive support.
pub fn assess_entity_composition(
    lower: &OperationalProfile,
    upper: &OperationalProfile,
) -> Vec<EntityComposition> {
    if lower.claim.is_none() || upper.claim.is_none() {
        return Vec::new();
    }
    let upper_witnesses: BTreeSet<(String, String)> = upper
        .witnesses
        .iter()
        .map(|witness| (witness.entity.full.clone(), witness.entity.head.clone()))
        .collect();
    if upper_witnesses.is_empty() {
        return Vec::new();
    }
    let mut relations: Vec<EntityComposition> = lower
        .engagements
        .iter()
        .filter_map(|engagement| {
            if !upper_witnesses.contains(&(
                engagement.entity.full.clone(),
                engagement.entity.head.clone(),
            )) {
                return None;
            }
            let (basis, strength) = match engagement.site {
                EngagementSite::Subject => (EntityCompositionBasis::SubjectElaboration, 0.65),
                EngagementSite::Trigger => (EntityCompositionBasis::TriggerContinuation, 0.55),
                EngagementSite::Means | EngagementSite::StateGuard | EngagementSite::ScopeGuard => {
                    return None
                }
            };
            Some(EntityComposition {
                basis,
                entity: engagement.entity.clone(),
                strength,
            })
        })
        .collect();
    relations.sort_by(|left, right| (left.basis, &left.entity).cmp(&(right.basis, &right.entity)));
    relations.dedup_by(|left, right| left.basis == right.basis && left.entity == right.entity);
    relations
}

/// Assess one possible constitutive direction.
///
/// `candidate` is the proposed lower-layer behavior and `target` is the
/// behavior it realizes.  The judgment is deliberately conservative:
///
/// * an explicitly named means anchors the first layer; or
/// * a more specific object claim may refine an already anchored actor domain.
///
/// The caller is responsible for the accumulation rule: object refinements
/// become support only when their target is already anchored by an explicit
/// means path.
pub fn assess_layered_realization(
    candidate: &OperationalProfile,
    target: &OperationalProfile,
) -> Option<LayeredRealization> {
    let candidate = candidate.claim.as_ref()?;
    let target = target.claim.as_ref()?;
    if candidate.action != target.action
        || candidate.actors.len() != 1
        || target.actors.len() != 1
        || candidate.objects.len() != 1
        || target.objects.len() != 1
    {
        return None;
    }
    let candidate_object = &candidate.objects[0];
    let target_object = &target.objects[0];
    let candidate_object_tokens: BTreeSet<String> = concept_tokens(&candidate_object.entity.full)
        .into_iter()
        .collect();
    let target_object_tokens: BTreeSet<String> = concept_tokens(&target_object.entity.full)
        .into_iter()
        .collect();
    let shared_object_tokens: Vec<String> = candidate_object_tokens
        .intersection(&target_object_tokens)
        .cloned()
        .collect();
    if shared_object_tokens.is_empty() {
        return None;
    }
    let candidate_actor = &candidate.actors[0];
    let target_actor = &target.actors[0];
    let candidate_domain = actor_domain_tokens(candidate_actor);
    if target.means.iter().any(|means| {
        let means_tokens: BTreeSet<String> = concept_tokens(&means.full).into_iter().collect();
        !means_tokens.is_empty() && means_tokens == candidate_domain
    }) {
        return Some(LayeredRealization {
            basis: RealizationBasis::ExplicitMeans,
            action: candidate.action.clone(),
            shared_object_tokens,
            scope_tokens: candidate_domain.into_iter().collect(),
            strength: 0.8,
        });
    }
    if !target.means.is_empty() {
        return None;
    }
    let target_domain = actor_domain_tokens(target_actor);
    let domains_are_nested = !candidate_domain.is_empty()
        && !target_domain.is_empty()
        && (candidate_domain.is_subset(&target_domain)
            || target_domain.is_subset(&candidate_domain));
    let quantifier_refines =
        quantifier_refines(candidate_object.quantifier, target_object.quantifier);
    let object_refines = target_object_tokens.is_subset(&candidate_object_tokens)
        && (target_object_tokens != candidate_object_tokens
            || candidate_object.quantifier != target_object.quantifier)
        && quantifier_refines;
    if candidate_actor.head == target_actor.head || !domains_are_nested || !object_refines {
        return None;
    }
    Some(LayeredRealization {
        basis: RealizationBasis::ObjectRefinement,
        action: candidate.action.clone(),
        shared_object_tokens,
        scope_tokens: candidate_domain
            .intersection(&target_domain)
            .cloned()
            .collect(),
        strength: 0.7,
    })
}

fn actor_domain_tokens(actor: &EntityRef) -> BTreeSet<String> {
    let head: BTreeSet<String> = concept_tokens(&actor.head).into_iter().collect();
    concept_tokens(&actor.full)
        .into_iter()
        .filter(|token| !head.contains(token))
        .collect()
}

fn quantifier_refines(candidate: Quantifier, target: Quantifier) -> bool {
    use crate::semantics::CountOp;

    if candidate == target {
        return true;
    }
    match (candidate, target) {
        (Quantifier::Count { n, .. }, Quantifier::Existential) => n >= 1,
        (
            Quantifier::Count {
                op: CountOp::Exactly,
                n: candidate,
            },
            Quantifier::Count {
                op: CountOp::AtLeast,
                n: target,
            },
        ) => candidate >= target,
        (
            Quantifier::Count {
                op: CountOp::Exactly,
                n: candidate,
            },
            Quantifier::Count {
                op: CountOp::AtMost,
                n: target,
            },
        ) => candidate <= target,
        (
            Quantifier::Count {
                op: CountOp::AtLeast,
                n: candidate,
            },
            Quantifier::Count {
                op: CountOp::AtLeast,
                n: target,
            },
        ) => candidate >= target,
        (
            Quantifier::Count {
                op: CountOp::AtMost,
                n: candidate,
            },
            Quantifier::Count {
                op: CountOp::AtMost,
                n: target,
            },
        ) => candidate <= target,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn profile(statement: &str) -> OperationalProfile {
        let parsed = so_lang::parse::parse(statement).unwrap();
        operational_profile(&parsed.sentences[0])
    }

    #[test]
    fn pipeline_object_witnesses_the_next_subject_and_trigger_identity() {
        let submitted = profile("an AddSpecification RPC shall submit an AddNode Command.");
        assert_eq!(submitted.witnesses[0].entity.full, "addnode command");

        let command = profile("the AddNode Command shall cause a NodeAdded Event.");
        assert_eq!(command.engagements[0].entity.full, "addnode command");
        assert_eq!(command.witnesses[0].entity.full, "nodeadded event");

        let consumer = profile(
            "When a NodeAdded Event or EvidenceRequestsReplaced Event is delivered, the evidence capture Consumer shall submit a CaptureEvidence Command.",
        );
        let trigger: Vec<_> = consumer
            .engagements
            .iter()
            .filter(|item| item.site == EngagementSite::Trigger)
            .collect();
        assert_eq!(trigger.len(), 2);
        assert!(trigger
            .iter()
            .all(|item| item.conjunction == GroupConjunction::Or));
        assert_eq!(trigger[0].entity.full, "nodeadded event");
        assert_eq!(trigger[1].entity.full, "evidencerequestsreplaced event");
    }

    #[test]
    fn negative_permission_recommendation_and_disjunction_do_not_witness() {
        assert!(
            profile("the daemon shall not submit a CaptureEvidence Command.")
                .witnesses
                .is_empty()
        );
        assert!(profile("the daemon may submit a CaptureEvidence Command.")
            .witnesses
            .is_empty());
        assert!(
            profile("the daemon should submit a CaptureEvidence Command.")
                .witnesses
                .is_empty()
        );
        assert!(
            profile("the daemon shall submit either a report or an invoice.")
                .witnesses
                .is_empty()
        );
        assert!(
            profile("the daemon shall either submit a report or submit an invoice.")
                .witnesses
                .is_empty()
        );
    }

    #[test]
    fn exact_identity_preserves_restrictive_modifiers() {
        let source = profile("the Consumer shall submit a CaptureEvidence Command.");
        let target = profile(
            "the applicable CaptureEvidence Command shall cause an EvidenceCaptured Event.",
        );
        assert_ne!(
            source.witnesses[0].entity.full,
            target.engagements[0].entity.full
        );
    }

    #[test]
    fn and_objects_witness_each_item_but_or_objects_witness_neither() {
        let both = profile("the daemon shall create a report and an invoice.");
        assert_eq!(both.witnesses.len(), 2);
        let either = profile("the daemon shall create a report or an invoice.");
        assert!(either.witnesses.is_empty());
    }

    #[test]
    fn historical_through_identifier_is_split_into_object_and_means() {
        let target = profile(
            "The system shall accept a constrained natural-language specification through `spec add`.",
        );
        let claim = target.claim.as_ref().unwrap();
        assert_eq!(
            claim.objects[0].entity.full,
            "constrained natural-language specification"
        );
        assert_eq!(claim.objects[0].entity.head, "specification");
        assert_eq!(claim.means[0].full, "`spec add`");
        assert_eq!(claim.means[0].head, "add");
        assert!(target.engagements.iter().any(|engagement| {
            engagement.site == EngagementSite::Means && engagement.entity.full == "`spec add`"
        }));
    }

    #[test]
    fn explicit_means_establishes_lower_to_upper_realization_direction() {
        let lower = profile("The `spec add` operation shall accept exactly one language sentence.");
        let upper = profile(
            "The system shall accept a constrained natural-language specification through `spec add`.",
        );
        let relation = assess_layered_realization(&lower, &upper).unwrap();
        assert_eq!(relation.basis, RealizationBasis::ExplicitMeans);
        assert!(assess_layered_realization(&upper, &lower).is_none());
    }

    #[test]
    fn object_refinement_extends_an_anchored_realization_path() {
        let lower = profile(
            "The Add RPC shall accept exactly one constrained-language specification sentence.",
        );
        let upper = profile("The `spec add` operation shall accept exactly one language sentence.");
        let relation = assess_layered_realization(&lower, &upper).unwrap();
        assert_eq!(relation.basis, RealizationBasis::ObjectRefinement);
        assert!(assess_layered_realization(&upper, &lower).is_none());
    }

    #[test]
    fn exact_object_to_subject_bridge_establishes_constitutive_direction() {
        let upper = profile("The command-line frontend shall expose an Add subcommand.");
        let lower = profile("The Add subcommand shall accept a repeatable Evidence option.");

        let relations = assess_entity_composition(&lower, &upper);

        assert_eq!(relations.len(), 1);
        assert_eq!(
            relations[0].basis,
            EntityCompositionBasis::SubjectElaboration
        );
        assert_eq!(relations[0].entity.full, "add subcommand");
        assert!(assess_entity_composition(&upper, &lower).is_empty());
    }

    #[test]
    fn exact_object_to_trigger_bridge_establishes_operational_continuation() {
        let upper = profile("the AddNode Command shall cause a NodeAdded Event.");
        let lower = profile(
            "When a NodeAdded Event is delivered, the term projection Consumer shall submit a ProjectNodeTerms Command.",
        );

        let relations = assess_entity_composition(&lower, &upper);

        assert_eq!(relations.len(), 1);
        assert_eq!(
            relations[0].basis,
            EntityCompositionBasis::TriggerContinuation
        );
        assert_eq!(relations[0].entity.full, "nodeadded event");
    }

    #[test]
    fn means_and_guards_do_not_become_constitutive_support() {
        let upper = profile("The daemon shall create a report.");
        let means_only = profile("The renderer shall display a page using a report.");
        let guard_only = profile("While a report is ready, the renderer shall display a page.");

        assert!(assess_entity_composition(&means_only, &upper).is_empty());
        assert!(assess_entity_composition(&guard_only, &upper).is_empty());
    }

    #[test]
    fn surface_similarity_does_not_replace_exact_entity_identity() {
        let upper = profile("The daemon shall create a report.");
        let lower = profile("The detailed report shall preserve an identity.");

        assert!(assess_entity_composition(&lower, &upper).is_empty());
    }
}
