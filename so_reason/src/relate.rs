//! The minimal relation engine: conservative structural judgments over
//! formulas, so that *implies*, *contradicts*, and *refines* are computed
//! relations rather than decorative vocabulary.
//!
//! Everything here is DELIBERATELY SYNTACTIC AND CONSERVATIVE. A judgment is
//! a [`Ternary`]: `Yes` and `No` are proofs by structural rule; [`Ternary::Unknown`]
//! is the honest first-class answer for everything the rules cannot see —
//! and it must NEVER be treated as `No`. The rules are:
//!
//! * Boolean structure: constant folding, idempotence, and syntactic
//!   absorption over `And`/`Or`/`Not`/`Top`/`Bottom`; identical (simplified)
//!   formulas imply each other; `Not` is handled by contraposition.
//! * Atoms compare by their [`Proposition`] — the logical key (subject digest
//!   plus behavior kernel, without act/force/anchor). The key is therefore
//!   FORCE-BLIND by design: `The pump should stop.` and `The pump shall
//!   stop.` carry the same proposition, so `implies` holds `Yes` between
//!   their claims. A consumer relating sentences of different acts or
//!   forces must re-apply that context itself — a recommendation's claim
//!   entailing an obligation's claim does not make the recommendation
//!   discharge the obligation. (Round 6 adds [`assess`], the force-AWARE
//!   end-to-end judgment; the force-blind core remains available and its
//!   blindness remains by design.)
//! * Lossiness-awareness (round 6): proposition identity includes the
//!   full-fidelity `full` strings of the subject and every object/role
//!   noun phrase, so a `Yes` at atom level requires the full renders to
//!   match wherever the coarse digests match. A coarse match with a full
//!   mismatch (`the owner of the file` vs `the owner of the bucket`;
//!   `request that is authenticated` vs `request that is unauthenticated`)
//!   is `Unknown` — never `Yes`, and never `No` (disjointness of the
//!   restrictions is not provable syntactically). The same rule covers the
//!   CONJUNCTION of a coordinated object/role group (round 6 follow-up):
//!   `notify the admin or the owner` and `notify the admin and the owner`
//!   share every item digest and differ only in the group's `and`/`or`, so
//!   they are `Unknown` — never a mutual Yes. Round 8 extends the rule to
//!   CLAUSAL role values (`before`/`after`/`until`): the value carries the
//!   full nested clause skeleton plus its full render, so a coarse match
//!   without a full match — `after no backup completes` vs `after the
//!   backup completes` — is `Unknown`, never `Yes`. A polarity mismatch in
//!   the nested skeleton is enough for `Unknown`; there is deliberately NO
//!   nested-clause contradiction logic yet (a nested denial is a temporal
//!   boundary condition, not a claim in guarantee position — relating
//!   nested clauses across sentences is future work, noted in the roadmap).
//! * One refinement hook: two atoms whose propositions are identical except
//!   a single Deadline/Duration role measure, or except the numbers of a
//!   comparison predicate (`at most 3` vs `at most 5`), with the SAME unit
//!   and parseable numbers — numeric ordering decides. There is no unit
//!   normalization: `5 seconds` vs `5000 ms` is `Unknown`, documented, not
//!   guessed.
//!
//! SMT grounding and natural-language entailment are future strengthenings
//! that can only turn some `Unknown`s into `Yes`/`No`; they will never be
//! needed to trust a `Yes` produced here.

use crate::formula::{
    applicability, claim_formula, contract_formula, AtomRef, ContractFormula, Formula, Proposition,
};
use crate::semantics::{
    force, speech_act, ComparisonSkeleton, CountOp, Force, MeasureSkeleton, ObjectSkeleton,
    Quantifier, RoleKind, RoleSkeleton, RoleValue, SpeechAct,
};
use serde::{Deserialize, Serialize};
use so_lang::ast::{ComparisonOp, Sentence};

/// Version of the graph-facing [`assess`] rules.
///
/// Persisted callers must record this value with every derived relationship
/// and bump it whenever a rule change can alter an [`Outcome`]. Old results can
/// then remain as history while a current graph view selects this version.
pub const ASSESS_VERSION: &str = "so-reason/assess-v1";

/// A conservative three-valued judgment. `Unknown` means "the structural
/// rules cannot decide" — it is not evidence of absence and MUST never be
/// collapsed into `No`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Ternary {
    Yes,
    No,
    Unknown,
}

/// Does `a` entail `b`? Conservative: `Yes`/`No` only by structural rule,
/// `Unknown` otherwise (module docs).
pub fn implies(a: &Formula, b: &Formula) -> Ternary {
    implies_s(&simplify(a), &simplify(b))
}

/// Do `a` and `b` contradict? `Yes` when `implies(a, ¬b)` (or symmetrically
/// `implies(b, ¬a)`) is `Yes`; `No` when the two formulas are syntactically
/// equal; `Unknown` otherwise.
///
/// COUNT SUBJECTS (round 7 attack fix): a `Not` over a count-subject atom
/// is a PER-INDIVIDUAL denial — the subject quantifier out-scopes it
/// (formula.rs, § Quantifier scope convention) — so `At least 3 replicas
/// shall not run.` means "≥3 replicas refrain", not the complement of
/// "≥3 replicas run". The generic ¬-wrapper route below reads `Not` as
/// classical outer negation and is therefore CLOSED to count-subject
/// atoms (the implication rules return `Unknown` for them); the sound
/// count exclusion — two POSITIVE count atoms with disjoint intervals —
/// is judged directly on the atoms, where no `Not` needs a reading. An
/// obligation and a count prohibition (`at least 5 shall run` vs `at
/// least 3 shall not run`) are jointly satisfiable and stay `Unknown`.
///
/// CAVEAT (documented, not decided): the syntactic-equality `No` presumes
/// the formula is satisfiable. A formula that is unsatisfiable on its own —
/// e.g. a conjunction of `at least 5` and `at most 3` over one proposition,
/// a shape a paired assumption can take — still compares equal to itself
/// and returns `No`, though it logically self-contradicts. Satisfiability
/// is not checked here (that is SMT territory, a future strengthening);
/// `No` therefore means "these two are the same claim", not "this claim is
/// consistent". Round 9: the grammar no longer produces the one such
/// formula it used to — a written DESCENDING `between` (`between 6 and
/// 4`) is now [`so_lang::parse::ParseError::DescendingBetween`], the
/// typo-shield at parse time — but a HAND-BUILT empty interval still
/// self-contradicts at `Yes` (the exclusion rule fires before the
/// syntactic-equality `No`) and vacuously implies every same-subject
/// comparison: both sound for an unsatisfiable claim, both documented in
/// semantics.md, and the satisfiability machinery keeps covering
/// hand-built trees.
///
/// SCOPE (round 7 — supersedes the round-6 asymmetry): the
/// disjoint-interval rule reads comparison PREDICATES and same-kind
/// Deadline/Duration ROLE measures (`for at least 30 days` vs `for less
/// than 10 days` now contradict at `Yes`). The round-6 conservatism —
/// role intervals grounding implication but not contradiction — is
/// retired with justification: the interval reading is the one the
/// containment rule already trusts, and an empty intersection over one
/// unit is a proof by the same rule, not a guess. Mixed kinds (a Deadline
/// against a Duration) and unit mismatches still never ground — `Unknown`.
pub fn contradicts(a: &Formula, b: &Formula) -> Ternary {
    // Two positive atoms that provably exclude each other contradict
    // directly (round 7 attack fix): the ¬-wrapper route below cannot
    // carry count-subject exclusions, because `Not` over a count-subject
    // atom means a per-individual denial, never the complement (module
    // docs above).
    if let (Formula::Atom { atom: x }, Formula::Atom { atom: y }) = (&simplify(a), &simplify(b)) {
        if atoms_exclude(x, y) {
            return Ternary::Yes;
        }
    }
    // The classical complement of a count-subject atom cannot be WRITTEN:
    // `Not{atom}` over such an atom already means the per-individual denial
    // (a prohibition's claim takes exactly that spelling), so wrapping the
    // atom would collide with it — `Exactly 3 replicas shall not run.`
    // must not compare equal to the constructed ¬(exactly 3 run). The
    // wrapper route is therefore closed on that side; the direct
    // atom-exclusion check above already carries everything it can prove.
    let not = |f: &Formula| -> Option<Formula> {
        if count_subject_atom(&simplify(f)) {
            return None;
        }
        Some(Formula::Not {
            inner: Box::new(f.clone()),
        })
    };
    if not(b).is_some_and(|nb| implies(a, &nb) == Ternary::Yes)
        || not(a).is_some_and(|na| implies(b, &na) == Ternary::Yes)
    {
        return Ternary::Yes;
    }
    if a == b {
        return Ternary::No;
    }
    Ternary::Unknown
}

/// Does `concrete` refine `abstract_`? Per the assume-guarantee theory, on
/// saturated forms: the assumption may only WEAKEN (`abstract_`'s assumption
/// implies `concrete`'s) and the saturated guarantee may only STRENGTHEN
/// (`concrete`'s saturated form implies `abstract_`'s). The two judgments
/// combine conservatively: `Yes` + `Yes` = `Yes`, any `No` = `No`, else
/// `Unknown`.
///
/// VACUITY GUARD (round 11, change 4 — the verification doctrine, defined
/// at [`crate::formula::ContractFormula::well_formed`]): when either
/// side's FORMED assumption is refuted ([`assumption_satisfiable`] ==
/// `No`), the saturated form `G ∨ ¬A` of that side is a tautology, so any
/// implication over it is vacuous — a "refinement" proven through it says
/// nothing about behavior. The judgment returns `Unknown` instead of
/// reporting a vacuous proof as a relation; `Unknown` satisfiability
/// leaves the judgment to the structural rules, and the result carries
/// that caveat (not disproven, never certified).
pub fn refines(concrete: &ContractFormula, abstract_: &ContractFormula) -> Ternary {
    if assumption_satisfiable(concrete) == Ternary::No
        || assumption_satisfiable(abstract_) == Ternary::No
    {
        return Ternary::Unknown;
    }
    let assumption = implies(&abstract_.assumption, &concrete.assumption);
    let guarantee = implies(&concrete.saturated(), &abstract_.saturated());
    match (assumption, guarantee) {
        (Ternary::Yes, Ternary::Yes) => Ternary::Yes,
        (Ternary::No, _) | (_, Ternary::No) => Ternary::No,
        _ => Ternary::Unknown,
    }
}

// ---- guard-aware decomposition (round 7) ----------------------------------------------

/// The guarded decomposition of a sentence: its (applicability, claim)
/// pair, both simplified — the two pieces a guarantee is assembled from
/// (`applicability → claim`) BEFORE the assembly hides the guard inside an
/// `Or`. Exposed through [`crate::formula::applicability`] and
/// [`crate::formula::claim_formula`], which are the accessors the round-7
/// guard-aware rules rely on. `None` for definitions (no claim).
fn guarded_parts(sentence: &Sentence) -> Option<(Formula, Formula)> {
    let claim = claim_formula(sentence)?;
    Some((simplify(&applicability(sentence)), simplify(&claim)))
}

/// Do two SIMPLIFIED guards witness a shared applicability region?
/// LEGISLATED (round 7, extended round 9): three cases count —
/// syntactically equal guards UP TO COMMUTATIVE NORMALIZATION (round 9:
/// both sides are canonicalized — `And`/`Or` operand lists sorted by a
/// deterministic structural key — so `Where A, While B,` and `Where B,
/// While A,` over the same clause set witness one region; duplicates
/// already collapsed via the simplifier's idempotence), a `Top` guard on
/// either side (`Top` is the everywhere-guard, so the other guard's own
/// region is exactly the overlap; a sentence asserts under its own guard,
/// so its own region is what its claim is in force over), and — round 9 —
/// the INTERVAL OVERLAP WITNESS: both guards are single copular
/// comparison clauses over the same subject full identity (same rendered
/// subject + copula, no roles, no negation) whose intervals share one
/// unit and have a provably NON-EMPTY intersection. That case is
/// constructive — an interior point of the intersection is a state
/// satisfying both guards — so it is a proof of shared region, not a
/// containment guess. A one-way guard implication (an extra conjunct, a
/// contained interval over DIFFERENT shapes) still proves CONTAINMENT of
/// regions but NOT satisfiability of the overlap, so it deliberately does
/// not count, and other differing guards stay `Unknown` territory: never
/// `Yes`. An EMPTY intersection continues to refuse.
///
/// CAVEAT (documented, mirroring the one on [`contradicts`]): the witness
/// is one shared WRITTEN condition, not a proof that the condition is
/// reachable. Guard SATISFIABILITY is not checked — a hand-built guard
/// whose clause can never hold (the descending empty interval; the
/// written form is a parse error since round 9) still witnesses through
/// the equality case, so a `Yes` downstream of this witness presumes the
/// shared guard region is nonempty, exactly as the syntactic-equality
/// `No` of [`contradicts`] presumes satisfiability. (The round-9 interval
/// overlap witness is stricter: it checks its OWN intervals for
/// emptiness, refusing empty operands and empty intersections.)
/// The ONE emptiness the engine can already see syntactically IS policed:
/// a region provably empty by its own shape (`g ∧ ¬g`, a trigger equal to
/// its own exception — [`region_provably_empty`]) never witnesses (round 7
/// attack fix).
///
/// ROLE-AWARE (round 10, superseding the round-7 pinned scope that read
/// the frame family and trigger kind as NOT part of guard identity): a
/// guard atom now carries its [`crate::formula::GuardRole`], and role
/// equality is REQUIRED for any atom-level guard match — the canonical
/// equality case sees it through atom identity, and the interval overlap
/// witness gates on it explicitly. `While X` never witnesses against
/// `When X` even over identical words. CONSERVATIVE RATIONALE: a `While`
/// region is a span the condition holds throughout and a `When` region is
/// the instant the condition becomes true; the round-7 pin argued the
/// instant lies inside the span, but that argument is a temporal-semantics
/// claim the engine does not model (edge-triggered vs level-sensitive
/// readings genuinely diverge — the instant X BECOMES true is not
/// guaranteed to be a state in which a `While X` obligation and a `When X`
/// obligation are both in force under every discretization), so the
/// cross-role witness is retired in the only safe direction: fewer `Yes`
/// proofs, more `Unknown`. Same-role pairs are unchanged.
fn guards_witness_overlap(a: &Formula, b: &Formula) -> bool {
    if region_provably_empty(a) || region_provably_empty(b) {
        return false;
    }
    if *a == Formula::Top || *b == Formula::Top {
        return true;
    }
    if canonical(a) == canonical(b) {
        return true;
    }
    // The interval overlap witness (round 9): two single comparison guards
    // over one subject whose intersection is provably non-empty. Round 10:
    // the roles must match — the witness point satisfies both WRITTEN
    // conditions only when both are conditions of the same frame family.
    if let (
        Formula::Atom {
            atom:
                AtomRef::Guard {
                    clause: ca,
                    source: sa,
                    role: ra,
                },
        },
        Formula::Atom {
            atom:
                AtomRef::Guard {
                    clause: cb,
                    source: sb,
                    role: rb,
                },
        },
    ) = (a, b)
    {
        return ra == rb && comparison_guards_overlap(ca, sa, cb, sb);
    }
    false
}

/// Canonicalize a formula for guard comparison (round 9): recursively sort
/// `And`/`Or` operand lists by a deterministic structural key (the derived
/// `Debug` render — total and stable over the data-only formula tree).
/// Conjunction and disjunction are commutative, so reordered operand lists
/// denote one region; duplicates are already gone (the simplifier's
/// idempotence), so sorting alone finishes the normalization.
fn canonical(f: &Formula) -> Formula {
    match f {
        Formula::And { items } => Formula::And {
            items: canonical_items(items),
        },
        Formula::Or { items } => Formula::Or {
            items: canonical_items(items),
        },
        Formula::Not { inner } => Formula::Not {
            inner: Box::new(canonical(inner)),
        },
        other => other.clone(),
    }
}

fn canonical_items(items: &[Formula]) -> Vec<Formula> {
    let mut items: Vec<Formula> = items.iter().map(canonical).collect();
    items.sort_by_key(|item| format!("{item:?}"));
    items
}

/// The round-9 interval overlap witness: both guard clauses are copular
/// COMPARISON clauses — a structured comparison digest, no roles (an agent
/// digests into the role tail, so it refuses too), no subject negation —
/// over the SAME subject full identity, read off the guard anchors: each
/// anchor is the clause's canonical render `<subject> <copula>
/// <comparison>`, so stripping the comparison render (the digest's own
/// words) leaves the full subject + copula, which must match
/// case-insensitively. Then a provably NON-EMPTY interval intersection
/// over one unit witnesses the shared region constructively: a point of
/// the intersection — an interior point, or the single shared value when
/// two CLOSED bounds merely touch (`at most 3` / `at least 3` share
/// exactly 3) — is a state satisfying both written guards. Anything else
/// — empty on either side or in the intersection, unit mismatch,
/// ungroundable bounds — refuses.
fn comparison_guards_overlap(
    ca: &crate::semantics::ClauseSkeleton,
    sa: &str,
    cb: &crate::semantics::ClauseSkeleton,
    sb: &str,
) -> bool {
    if !ca.roles.is_empty()
        || !cb.roles.is_empty()
        || ca.polarity.is_some()
        || cb.polarity.is_some()
    {
        return false;
    }
    let (Some(compa), Some(compb)) = (&ca.comparison, &cb.comparison) else {
        return false;
    };
    // Same subject full identity (+ copula): the anchor minus the
    // comparison's own render.
    let prefix = |source: &str, words: &[String]| -> Option<String> {
        source
            .to_lowercase()
            .strip_suffix(words.join(" ").as_str())
            .map(str::to_string)
    };
    let (Some(pa), Some(pb)) = (prefix(sa, &ca.words), prefix(sb, &cb.words)) else {
        return false;
    };
    if pa != pb {
        return false;
    }
    let (Some((ia, ua)), Some((ib, ub))) = (interval_of(compa), interval_of(compb)) else {
        return false;
    };
    same_unit(ua.as_deref(), ub.as_deref())
        && !ia.disjoint(&ia)
        && !ib.disjoint(&ib)
        && !ia.disjoint(&ib)
}

/// Is a SIMPLIFIED guard's region provably EMPTY by the syntactic means
/// the engine already trusts? `Bottom`, or a conjunction containing some
/// conjunct together with its own negation (`When X, …, unless X.` has
/// applicability `g ∧ ¬g` over one guard atom). A sentence whose
/// applicability region is empty asserts nothing anywhere, so its guard
/// witnesses no overlap — the Top-witness rationale ("its own region is
/// what its claim is in force over") presumes the region nonempty.
/// ROLE-BLIND for guard atoms (round 10, deliberate): `When X, …, unless
/// X.` conjoins a Trigger-role atom with the negation of an
/// Exception-role atom over the SAME written clause, and the region is
/// still genuinely empty — the exception is evaluated wherever the
/// sentence would apply, and at any such point (the trigger instant, a
/// `While` span, a `Where` scope) the clause X holds, so the carve-out
/// `¬X` fails there. Unlike the cross-role OVERLAP witness (retired,
/// see [`guards_witness_overlap`]), this cross-role match only BLOCKS
/// proofs downstream (an empty region witnesses nothing), and the
/// same-words argument is sound for every role, so the round-7 attack fix
/// keeps its teeth under role-carrying atoms.
fn region_provably_empty(f: &Formula) -> bool {
    let negation_of = |y: &Formula, x: &Formula| -> bool {
        let Formula::Not { inner } = y else {
            return false;
        };
        if **inner == *x {
            return true;
        }
        // Guard atoms match ignoring their role (documented above).
        if let (
            Formula::Atom {
                atom:
                    AtomRef::Guard {
                        clause: ca,
                        source: sa,
                        ..
                    },
            },
            Formula::Atom {
                atom:
                    AtomRef::Guard {
                        clause: cb,
                        source: sb,
                        ..
                    },
            },
        ) = (&**inner, x)
        {
            return ca == cb && sa == sb;
        }
        false
    };
    match f {
        Formula::Bottom => true,
        Formula::And { items } => items
            .iter()
            .any(|x| items.iter().any(|y| negation_of(y, x))),
        _ => false,
    }
}

/// A CONDITIONAL contradiction (round 7 — the guard-aware rule): the two
/// sentences' guards witness a shared applicability region
/// ([`guards_witness_overlap`]) and their claims provably contradict, so
/// the pair is in conflict whenever the shared guard holds. This is what
/// the structural [`contradicts`] over assembled guarantees cannot see:
/// a guarantee is `¬guard ∨ claim`, and the claim-level conflict hides
/// inside the `Or`.
fn conditional_contradiction(a: &Sentence, b: &Sentence) -> bool {
    let (Some((ga, ca)), Some((gb, cb))) = (guarded_parts(a), guarded_parts(b)) else {
        return false;
    };
    guards_witness_overlap(&ga, &gb) && contradicts(&ca, &cb) == Ternary::Yes
}

/// Does `other` FORBID exactly what `permission` admits (round 7)? True
/// when `other` carries a single NEGATED behavior atom — a prohibition, a
/// subject-`no` obligation, or a negative description; a recommendation
/// does not bound, so it never conflicts here — whose proposition (full
/// identities included) equals the permission's admissibility atom, under
/// guards that witness a shared region. Behavior and admissibility atoms
/// deliberately never compare inside [`implies`]/[`contradicts`]
/// (requirement vs tolerance are different modalities); this is the ONE
/// judgment that crosses the species, and it crosses by proposition only.
fn envelope_conflict(permission: &Sentence, other: &Sentence) -> bool {
    if force(other) == Some(Force::Recommended) {
        return false;
    }
    let (Some((gp, cp)), Some((go, co))) = (guarded_parts(permission), guarded_parts(other)) else {
        return false;
    };
    if !guards_witness_overlap(&gp, &go) {
        return false;
    }
    let Formula::Atom {
        atom: AtomRef::Admissibility { behavior: admitted },
    } = cp
    else {
        return false;
    };
    let Formula::Not { inner } = co else {
        return false;
    };
    let Formula::Atom {
        atom: AtomRef::Behavior {
            behavior: forbidden,
        },
    } = *inner
    else {
        return false;
    };
    // Count subjects never conflict here (round 7 attack fix): `at least 3
    // clients may retry` and `at least 3 clients shall not retry` can pick
    // DIFFERENT witness sets (six clients: three tolerated retriers, three
    // refrainers), so the prohibition does not forbid exactly what the
    // permission admits — only Definite/Universal subjects make the two
    // atoms co-referential.
    if matches!(admitted.subject.quantifier, Quantifier::Count { .. }) {
        return false;
    }
    admitted.proposition() == forbidden.proposition()
}

// ---- assumption satisfiability (round 8) ----------------------------------------------

/// Is the paired assumption SATISFIABLE — can the conjoined
/// CONTRACT-FORMING reliances of `c` all hold at once? Individually valid
/// reliances can conjoin into an unsatisfiable A (`at least 5 replicas
/// run` ∧ `at most 3 replicas run`), and an unsatisfiable A relieves the
/// guarantee EVERYWHERE: the saturated form `G ∨ ¬A` becomes a tautology
/// before saturation is even computed. Round 9: the judged set is exactly
/// the set [`ContractFormula::paired`] conjoins — non-envelope AND proven,
/// and (round 10) not merely recommended AND responsible-subject keys
/// disjoint ([`crate::formula::AssumptionSource::contract_forming`]) — so the
/// verdict is about the assumption the contract actually formed; a
/// candidate (unproven) source cannot make A unsatisfiable, because it
/// never entered A.
///
/// ASYMMETRY DOCTRINE (legislated, round 8): the check is structural, and
/// satisfiability is NOT provable syntactically — only UNsatisfiability
/// is, and only for the fragments the engine already understands. The
/// returned [`Ternary`] therefore answers "satisfiable?" with only two
/// values ever produced:
///
/// * [`Ternary::No`] — PROVEN unsatisfiable: the simplified conjunction is
///   `Bottom`, or two conjuncts provably contradict by the structural
///   rules ([`contradicts`] == `Yes`) — an atom against its own negation
///   over one proposition (full identities included), disjoint
///   count-quantifier intervals over one subject or object, disjoint
///   comparison or Deadline/Duration role-measure intervals over one unit.
/// * [`Ternary::Unknown`] — nothing proven. This is NOT evidence of
///   satisfiability; it is the honest "the rules cannot see a
///   contradiction".
///
/// [`Ternary::Yes`] is NEVER returned: a `Yes` would claim a model exists,
/// which no syntactic rule here can witness. Callers must treat `Unknown`
/// as the good case ("not disproven") and must never await a `Yes`.
///
/// Envelope sources ([`crate::formula::EdgeKind::AdmissibilityEnvelope`])
/// are EXCLUDED: they never enter the paired assumption formula (round 6),
/// so they cannot make it unsatisfiable — their own judgment is
/// [`envelope_compatible`]. The check reads [`ContractFormula::sources`];
/// a hand-built contract whose `assumption` was set directly (no sources)
/// is judged over that assumption formula instead.
pub fn assumption_satisfiable(c: &ContractFormula) -> Ternary {
    let relied: Vec<Formula> = c
        .sources
        .iter()
        .filter(|s| s.contract_forming())
        .map(|s| s.relied.clone())
        .collect();
    let conjunction = if relied.is_empty() {
        c.assumption.clone()
    } else {
        Formula::And { items: relied }
    };
    let conjunction = simplify(&conjunction);
    if conjunction == Formula::Bottom {
        return Ternary::No;
    }
    let items: Vec<Formula> = match conjunction {
        Formula::And { items } => items,
        other => vec![other],
    };
    for (i, a) in items.iter().enumerate() {
        for b in &items[i + 1..] {
            if contradicts(a, b) == Ternary::Yes {
                return Ternary::No;
            }
        }
    }
    Ternary::Unknown
}

// ---- envelope compatibility (round 8) --------------------------------------------------

/// Is the paired contract COMPATIBLE with its retained admissibility
/// envelopes — or does its own guarantee forbid exactly what an envelope
/// admits? Envelope sources never enter the assumption formula (round 6),
/// so until now they were retained without any formal check against the
/// guarantee they ride on.
///
/// The rule reuses the round-7 EnvelopeConflict machinery, one level down:
/// decompose the guarantee and each envelope source's formula into their
/// (guard, claim) parts; where the guards witness a shared region
/// ([`guards_witness_overlap`]) and the guarantee's claim is a single
/// NEGATED behavior atom whose proposition (full identities included)
/// equals the envelope's admissibility atom, the envelope is violated —
/// [`Ternary::No`]. Count subjects never ground (the round-7 witness-set
/// argument), and a merely RECOMMENDED prohibition does not bound, exactly
/// as in [`assess`]'s envelope rule.
///
/// ASYMMETRY DOCTRINE (same as [`assumption_satisfiable`]): only the
/// violation is provable syntactically. [`Ternary::No`] is a proof;
/// [`Ternary::Unknown`] means "nothing provable" and is the good case;
/// [`Ternary::Yes`] is NEVER returned — compatibility (the absence of any
/// conflict) cannot be witnessed by these rules. Paired guarantees should
/// be checked through this judgment by the graph layer whenever an
/// envelope source is retained.
///
/// REACHABILITY (round 10, superseding the round-8 note): the
/// proposition-equality rule includes the subject's full render, so the
/// only provable `No` is a SAME-SUBJECT envelope. Since round 10 the
/// validated constructor no longer rejects shared subject keys (they are
/// recorded as `SubjectRelation::SharedKeys` — candidate data), so a
/// same-subject envelope CAN arrive through
/// [`crate::formula::AssumptionSource::for_guarantee`] and this check's
/// `No` arm is reachable through every construction path: the check is
/// now the formal guard the round-6/8 rejection used to approximate.
/// When `No` fires it is a real proof, no false `Yes` exists either way,
/// and the same-subject head-to-head case between two STATEMENTS (rather
/// than a retained source) is already caught by [`assess`]'s
/// `EnvelopeConflict`.
///
/// # The compatibility calculus (round 11, change 5)
///
/// Refutation-only, three rules:
///
/// * **Prohibition conflicts refute.** A guarantee whose claim FORBIDS a
///   behavior atom — a single `¬atom`, or EACH `¬atom` conjunct of a
///   conjunction (a coordinated and-subject prohibition puts every
///   conjunct in force; a conjunct binds regardless of its siblings, so
///   a hand-built mixed conjunction `¬a ∧ b` still forbids `a` — parsed
///   prohibition/negative-description claims are uniformly negated, so
///   the mixed shape only arises hand-built) — refutes an envelope that
///   admits exactly that
///   proposition. Negative DESCRIPTIONS bound the same way (`is never
///   logged` forbids `may be logged` — the claim shapes meet at one
///   negated atom); a merely RECOMMENDED prohibition does not bound, and
///   count subjects never ground (witness sets can differ, round 7).
/// * **Obligations never refute.** An obligation whose atom MATCHES the
///   admitted behavior is compatible EVIDENCE — obligation implies
///   admissibility — but the judgment still answers `Unknown`, never
///   `Yes`: certifying compatibility is graph work, and this calculus
///   only ever proves violations (the claim is not a `Not`, so the
///   decomposition below deliberately finds nothing to refute with).
/// * **The branch rule (VP alternatives).** An envelope whose
///   admissibility claim is an `either … or …` disjunction of atoms is
///   violated only when EVERY branch's atom is prohibited by the
///   guarantee — with all alternatives forbidden, the permission is
///   entirely revoked; when only SOME branch conflicts, the permission
///   can route around through another alternative, so the judgment stays
///   `Unknown`. (LEGISLATED, round 11: the branches read from the
///   ENVELOPE side — a guarded alternative permission whose simplified
///   formula flattens past the `¬guard ∨ …` shape is skipped, staying
///   `Unknown`: conservative, never a false `No`.)
pub fn envelope_compatible(c: &ContractFormula) -> Ternary {
    let (g_guard, g_claim) = guarded_split(&simplify(&c.guarantee));
    // The FORBIDDEN propositions: a single negated behavior atom, or
    // each negated behavior conjunct of a conjunction (a conjunct is in
    // force regardless of its siblings — non-negated conjuncts are
    // skipped, never disqualifying).
    // Recommended and count-subject prohibitions do not bound and are
    // dropped from the set (round 7 doctrine, round 7 attack fix).
    let negated_behavior = |f: &Formula| -> Option<crate::formula::BehaviorAtom> {
        let Formula::Not { inner } = f else {
            return None;
        };
        let Formula::Atom {
            atom: AtomRef::Behavior { behavior },
        } = &**inner
        else {
            return None;
        };
        Some(behavior.clone())
    };
    let conjuncts: Vec<Formula> = match &g_claim {
        Formula::And { items } => items.clone(),
        other => vec![other.clone()],
    };
    let mut forbidden: Vec<Proposition> = Vec::new();
    for conjunct in &conjuncts {
        let Some(behavior) = negated_behavior(conjunct) else {
            continue;
        };
        if behavior.force == Some(Force::Recommended)
            || matches!(behavior.subject.quantifier, Quantifier::Count { .. })
        {
            continue;
        }
        forbidden.push(behavior.proposition());
    }
    if forbidden.is_empty() {
        return Ternary::Unknown;
    }
    for source in &c.sources {
        if source.kind != crate::formula::EdgeKind::AdmissibilityEnvelope {
            continue;
        }
        let (p_guard, p_claim) = guarded_split(&simplify(&source.formula));
        if !guards_witness_overlap(&g_guard, &p_guard) {
            continue;
        }
        // The ADMITTED branches: one admissibility atom, or the `either …
        // or …` disjunction of admissibility atoms (round 11 branch rule).
        let admissibility = |f: &Formula| -> Option<crate::formula::BehaviorAtom> {
            let Formula::Atom {
                atom: AtomRef::Admissibility { behavior },
            } = f
            else {
                return None;
            };
            Some(behavior.clone())
        };
        let branch_formulas: Vec<Formula> = match &p_claim {
            Formula::Or { items } => items.clone(),
            other => vec![other.clone()],
        };
        let branches: Vec<crate::formula::BehaviorAtom> =
            branch_formulas.iter().filter_map(admissibility).collect();
        if branches.len() != branch_formulas.len() || branches.is_empty() {
            // Not a pure admissibility claim (e.g. a flattened guarded
            // alternative): conservative skip.
            continue;
        }
        // Every branch must be non-count AND provably forbidden; a single
        // surviving branch routes around (`Unknown`).
        let all_refuted = branches.iter().all(|admitted| {
            !matches!(admitted.subject.quantifier, Quantifier::Count { .. })
                && forbidden.contains(&admitted.proposition())
        });
        if all_refuted {
            return Ternary::No;
        }
    }
    Ternary::Unknown
}

/// Split a SIMPLIFIED guarded claim `¬guard ∨ claim` back into its
/// (guard, claim) parts. The shape is exactly what
/// [`crate::formula::contract_formula`] and the assumption-source
/// constructors assemble — a two-item `Or` whose first item is the negated
/// applicability; anything else reads as unguarded (`Top`, the
/// everywhere-guard). A hand-built formula that happens to match the shape
/// decomposes the same way — the consumers above only ever turn the parts
/// into `Unknown`-or-proof, so a misread shape cannot manufacture a false
/// verdict on its own.
fn guarded_split(f: &Formula) -> (Formula, Formula) {
    if let Formula::Or { items } = f {
        if items.len() == 2 {
            if let Formula::Not { inner } = &items[0] {
                return ((**inner).clone(), items[1].clone());
            }
        }
    }
    (Formula::Top, f.clone())
}

// ---- force-aware assessment (round 6) ------------------------------------------------

/// The force-AWARE outcome of relating two sentences end-to-end. The
/// force-blind core ([`implies`]/[`contradicts`]/[`refines`]) stays
/// available and stays blind BY DESIGN (it compares propositions); this
/// enum is where act and force re-enter, so a recommendation crossing an
/// obligation is named tension, not contradiction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Outcome {
    /// Two BINDING sentences whose guarantees provably contradict: the
    /// specification set cannot be satisfied as written.
    HardContradiction,
    /// A provable conflict with a RECOMMENDED side: following the
    /// recommendation would violate the other sentence — tension to
    /// resolve, not unsatisfiability.
    AdvisoryTension,
    /// A provable conflict with a DESCRIPTION side (no force): the system
    /// as described breaks (or is broken by) the other sentence.
    DescriptiveConflict,
    /// One contract provably refines the other. `concrete_is_a` reports
    /// the direction: `true` when `a` is the concrete (refining) side.
    ///
    /// FORCE-AWARE (round 12, change 1): [`assess`] reports `Refinement`
    /// only when the concrete side's force is at least as strong as the
    /// abstract side's ([`refinement_force_admissible`] — the legislated
    /// force preorder): Binding refines Binding, Recommended, or a
    /// description; Recommended refines only Recommended; descriptions
    /// (no force — capability included) refine only descriptions. A
    /// weaker-force "refinement" (`should respond within 5 seconds`
    /// against `shall respond within 10 seconds`) would promote advice
    /// into the discharge of a stronger binding promise, so those pairs
    /// are `Unknown` here. The low-level [`refines`] stays FORCE-BLIND by
    /// design (it compares contract formulas, whose propositions exclude
    /// force); `assess` is the graph-facing verdict where force re-enters.
    Refinement { concrete_is_a: bool },
    /// Mutual implication between SAME-FORCE sentences: the two state one
    /// claim. (Mutual implication across DIFFERENT forces — `should stop`
    /// vs `shall stop` — is LEGISLATED [`Outcome::Unknown`]: neither
    /// "equivalent" nor a directed refinement is structurally true of a
    /// force-divergent pair, and whether the weaker is subsumed is graph
    /// policy, not language fact.)
    Equivalent,
    /// Both implication directions are provably `No`: the sentences are
    /// provably unrelated. (Rarely provable by the structural rules —
    /// most non-entailments are `Unknown`.)
    Independent,
    /// A permission crossed by a prohibition (or a negative description)
    /// of the SAME behavior (round 7): the prohibition forbids exactly
    /// what the permission admits — the admissibility envelope and the
    /// bound cannot both stand. Not unsatisfiability (nothing obliges the
    /// admitted behavior to occur), but a specification-set conflict to
    /// resolve. Fires only when the admissibility atom and the forbidden
    /// behavior atom match on proposition (full identities included) and
    /// the guards witness a shared region ([`guards_witness_overlap`]).
    EnvelopeConflict,
    /// The structural rules cannot classify the pair. Definitions always
    /// land here (vocabulary has no contract to relate); permissions land
    /// here for everything EXCEPT an [`Outcome::EnvelopeConflict`] —
    /// including permission × obligation over one atom (an obligation
    /// implies admissibility, so nothing conflicts, but certifying the
    /// pair COMPATIBLE is graph work, legislated round 7: `Unknown`, not a
    /// positive outcome). Permissions otherwise participate via PAIRING
    /// ([`crate::formula::AssumptionSource`]), not head-to-head
    /// assessment.
    Unknown,
}

/// Assess two sentences end-to-end: build their contract formulas, run the
/// conservative structural judgments, then classify by act and force
/// (round 6). Every `Yes` consumed here is a proof by structural rule, so
/// every non-[`Outcome::Unknown`] outcome inherits that trust; `Unknown`
/// remains the honest default and must never be read as "unrelated".
///
/// Classification order (first match wins):
/// 0. a permission on either side: [`Outcome::EnvelopeConflict`] when the
///    other side forbids the admitted behavior (round 7, see
///    [`Outcome::EnvelopeConflict`]), `Unknown` otherwise — permission ×
///    obligation included (legislated: compatibility certification is
///    graph work);
/// 1. no contract on either side (definition or permission) → `Unknown`;
/// 2. guarantees contradict — structurally, OR by the round-7 guard-aware
///    rule (guards witness a shared region and the claims contradict, see
///    [`guards_witness_overlap`]) → [`Outcome::HardContradiction`] when
///    both sides bind, [`Outcome::AdvisoryTension`] when a side merely
///    recommends, [`Outcome::DescriptiveConflict`] otherwise (a
///    description side);
/// 3. mutual implication with equal force → [`Outcome::Equivalent`]
///    (unequal force → `Unknown`, legislated — see [`Outcome::Equivalent`]);
/// 4. refinement in exactly the surviving direction, AND the concrete
///    side's force at least as strong as the abstract side's (round 12 —
///    the force preorder, see [`Outcome::Refinement`] and
///    [`refinement_force_admissible`]) → [`Outcome::Refinement`] with its
///    direction; a force-inadmissible refinement direction is `Unknown`;
/// 5. both implication directions provably `No` →
///    [`Outcome::Independent`];
/// 6. otherwise `Unknown`.
pub fn assess(a: &Sentence, b: &Sentence) -> Outcome {
    // Round 7: envelope compatibility — the one head-to-head judgment a
    // permission takes part in.
    if speech_act(a) == SpeechAct::Permission || speech_act(b) == SpeechAct::Permission {
        let (permission, other) = if speech_act(a) == SpeechAct::Permission {
            (a, b)
        } else {
            (b, a)
        };
        if speech_act(other) != SpeechAct::Permission && envelope_conflict(permission, other) {
            return Outcome::EnvelopeConflict;
        }
        return Outcome::Unknown;
    }
    let (Some(ca), Some(cb)) = (contract_formula(a), contract_formula(b)) else {
        return Outcome::Unknown;
    };
    let fa = force(a);
    let fb = force(b);
    // Round 7: the guard-aware rule sees CONDITIONAL contradictions the
    // assembled-guarantee comparison cannot (the claims conflict wherever
    // the shared guard holds); the force classification is the same.
    if contradicts(&ca.guarantee, &cb.guarantee) == Ternary::Yes || conditional_contradiction(a, b)
    {
        return match (fa, fb) {
            (Some(Force::Binding), Some(Force::Binding)) => Outcome::HardContradiction,
            _ if fa == Some(Force::Recommended) || fb == Some(Force::Recommended) => {
                Outcome::AdvisoryTension
            }
            _ => Outcome::DescriptiveConflict,
        };
    }
    let fwd = implies(&ca.guarantee, &cb.guarantee);
    let bwd = implies(&cb.guarantee, &ca.guarantee);
    if fwd == Ternary::Yes && bwd == Ternary::Yes {
        return if fa == fb {
            Outcome::Equivalent
        } else {
            Outcome::Unknown
        };
    }
    // Round 12 (change 1): the force preorder gates the graph-facing
    // refinement verdict — the proof stays a proof at the [`refines`]
    // level (force-blind by design), but only a force-admissible
    // direction is REPORTED as Refinement.
    if refines(&ca, &cb) == Ternary::Yes && refinement_force_admissible(fa, fb) {
        return Outcome::Refinement {
            concrete_is_a: true,
        };
    }
    if refines(&cb, &ca) == Ternary::Yes && refinement_force_admissible(fb, fa) {
        return Outcome::Refinement {
            concrete_is_a: false,
        };
    }
    if fwd == Ternary::No && bwd == Ternary::No {
        return Outcome::Independent;
    }
    Outcome::Unknown
}

/// The FORCE PREORDER for directed refinement (round 12, change 1,
/// LEGISLATED): may a contract of force `concrete` be reported as refining
/// a contract of force `abstract_`? The concrete side must be at least as
/// strong: Binding refines Binding, Recommended, or a description (`None`
/// force — capability included); Recommended refines only Recommended;
/// descriptions refine only descriptions. Everything else — most
/// pointedly a Recommended concrete side against a Binding abstract side
/// (`should` "discharging" a `shall`) — is inadmissible, and [`assess`]
/// answers `Unknown` for it. The low-level [`refines`] does NOT consult
/// this table: it is force-blind by design (module docs), and this
/// preorder exists exactly where act and force re-enter — the graph-facing
/// verdict.
fn refinement_force_admissible(concrete: Option<Force>, abstract_: Option<Force>) -> bool {
    matches!(
        (concrete, abstract_),
        (Some(Force::Binding), _)
            | (Some(Force::Recommended), Some(Force::Recommended))
            | (None, None)
    )
}

// ---- simplification ---------------------------------------------------------------

/// Does this formula simplify to `Bottom` (round 8)? The vacuity gate for
/// [`crate::formula::AssumptionSource::for_guarantee_with_relied`]: a relied
/// formula that is (or simplifies to) `Bottom` would make the saturated
/// form `G ∨ ¬A` a tautology, erasing the guarantee.
pub(crate) fn simplifies_to_bottom(f: &Formula) -> bool {
    simplify(f) == Formula::Bottom
}

/// Simplify a formula syntactically: constant folding (`And` with `Bottom`
/// is `Bottom`, `Top` conjuncts drop, duals for `Or`), flattening of nested
/// same-connective groups, idempotence (duplicate items drop), double
/// negation, and syntactic absorption (`x ∧ (x ∨ y)` = `x`, `x ∨ (x ∧ y)` =
/// `x`). Structural, with ONE atom-aware exception: double negation does
/// not cancel over a count-subject atom, whose own `Not` is per-individual
/// rather than classical (round 7 attack fix, see [`count_subject_atom`]).
fn simplify(f: &Formula) -> Formula {
    match f {
        Formula::And { items } => {
            let mut out: Vec<Formula> = Vec::new();
            for item in items {
                match simplify(item) {
                    Formula::Top => {}
                    Formula::Bottom => return Formula::Bottom,
                    Formula::And { items } => {
                        for inner in items {
                            if !out.contains(&inner) {
                                out.push(inner);
                            }
                        }
                    }
                    other => {
                        if !out.contains(&other) {
                            out.push(other);
                        }
                    }
                }
            }
            // Absorption: drop an `Or` conjunct that contains another
            // conjunct as a disjunct.
            let absorbed: Vec<Formula> = out
                .iter()
                .filter(|item| match item {
                    Formula::Or { items: disjuncts } => !disjuncts
                        .iter()
                        .any(|d| out.iter().any(|c| c == d && c != *item)),
                    _ => true,
                })
                .cloned()
                .collect();
            group(absorbed, true)
        }
        Formula::Or { items } => {
            let mut out: Vec<Formula> = Vec::new();
            for item in items {
                match simplify(item) {
                    Formula::Bottom => {}
                    Formula::Top => return Formula::Top,
                    Formula::Or { items } => {
                        for inner in items {
                            if !out.contains(&inner) {
                                out.push(inner);
                            }
                        }
                    }
                    other => {
                        if !out.contains(&other) {
                            out.push(other);
                        }
                    }
                }
            }
            // Absorption: drop an `And` disjunct that contains another
            // disjunct as a conjunct.
            let absorbed: Vec<Formula> = out
                .iter()
                .filter(|item| match item {
                    Formula::And { items: conjuncts } => !conjuncts
                        .iter()
                        .any(|c| out.iter().any(|d| d == c && d != *item)),
                    _ => true,
                })
                .cloned()
                .collect();
            group(absorbed, false)
        }
        Formula::Not { inner } => match simplify(inner) {
            Formula::Top => Formula::Bottom,
            Formula::Bottom => Formula::Top,
            // Double negation — EXCEPT over a count-subject atom, whose own
            // `Not` is per-individual (the subject quantifier out-scopes it,
            // formula.rs § Quantifier scope convention): ¬(∃≥n ¬P) is not
            // (∃≥n P), so the two `Not`s do not cancel there (round 7
            // attack fix — collapsing them turned `at least 3 replicas
            // shall not run` into set-complement and manufactured false
            // contradictions).
            Formula::Not { inner } if !count_subject_atom(&inner) => *inner,
            other => Formula::Not {
                inner: Box::new(other),
            },
        },
        other => other.clone(),
    }
}

/// Rebuild a simplified group: the empty conjunction is `Top` (dual for
/// `Or`), a single item stands alone.
fn group(mut items: Vec<Formula>, conjunction: bool) -> Formula {
    match items.len() {
        0 => {
            if conjunction {
                Formula::Top
            } else {
                Formula::Bottom
            }
        }
        1 => items.remove(0),
        _ => {
            if conjunction {
                Formula::And { items }
            } else {
                Formula::Or { items }
            }
        }
    }
}

// ---- implication over simplified formulas -------------------------------------------

fn implies_s(a: &Formula, b: &Formula) -> Ternary {
    if a == b {
        return Ternary::Yes;
    }
    match (a, b) {
        (Formula::Bottom, _) => return Ternary::Yes,
        (_, Formula::Top) => return Ternary::Yes,
        (Formula::Top, Formula::Bottom) => return Ternary::No,
        // Contraposition — CLASSICAL `Not` only. A `Not` over a
        // count-subject atom is a PER-INDIVIDUAL denial (the subject
        // quantifier out-scopes it, formula.rs § Quantifier scope
        // convention), so contraposing it reverses a count entailment
        // (`≥3 refrain` does not imply `≥5 refrain` — round 7 attack fix).
        // Two counted denials over one identical atom compare by interval
        // containment in the SAME direction instead (`at least 5 replicas
        // refrain` ⇒ `at least 3 replicas refrain`); every other shape
        // touching a per-individual `Not` stays `Unknown`.
        (Formula::Not { inner: x }, Formula::Not { inner: y }) => {
            if count_subject_atom(x) || count_subject_atom(y) {
                if let (Formula::Atom { atom: ax }, Formula::Atom { atom: ay }) = (&**x, &**y) {
                    return negated_count_implies(ax, ay);
                }
                return Ternary::Unknown;
            }
            return implies_s(y, x);
        }
        (Formula::Atom { atom: x }, Formula::Atom { atom: y }) => return atom_implies(x, y),
        // Mixed polarity over one proposition: `P → ¬P` (and `¬P → P`) is
        // a proven non-entailment — the direct shape of a contradiction.
        // Round 6: disjoint comparison INTERVALS over one measured subject
        // prove the implication instead (`at most 3` → ¬`at least 5`).
        // COUNT SUBJECTS are exempt from both rules (round 7 attack fix):
        // the `Not` side is a per-individual denial, so neither the
        // exclusion (`≥5 run` does not bound how many refrain) nor the
        // non-entailment is what the classical rule proves — `Unknown`.
        (Formula::Atom { atom: x }, Formula::Not { inner }) => {
            if let Formula::Atom { atom: y } = &**inner {
                if count_subject_ref(x) || count_subject_ref(y) {
                    return Ternary::Unknown;
                }
                if atoms_exclude(x, y) {
                    return Ternary::Yes;
                }
                if same_proposition(x, y) {
                    return Ternary::No;
                }
            }
        }
        (Formula::Not { inner }, Formula::Atom { atom: y }) => {
            if let Formula::Atom { atom: x } = &**inner {
                if count_subject_ref(x) || count_subject_ref(y) {
                    return Ternary::Unknown;
                }
                if same_proposition(x, y) {
                    return Ternary::No;
                }
            }
        }
        _ => {}
    }
    // Connective decomposition — sufficient conditions only, so every rule
    // can only produce Yes; failing to fire falls through to Unknown.
    if let Formula::And { items } = a {
        if items.iter().any(|item| implies_s(item, b) == Ternary::Yes) {
            return Ternary::Yes;
        }
    }
    if let Formula::Or { items } = a {
        if items.iter().all(|item| implies_s(item, b) == Ternary::Yes) {
            return Ternary::Yes;
        }
    }
    if let Formula::And { items } = b {
        if items.iter().all(|item| implies_s(a, item) == Ternary::Yes) {
            return Ternary::Yes;
        }
    }
    if let Formula::Or { items } = b {
        if items.iter().any(|item| implies_s(a, item) == Ternary::Yes) {
            return Ternary::Yes;
        }
    }
    Ternary::Unknown
}

/// The propositions of two atom refs, when both are the same species.
/// Behavior and admissibility atoms never compare (requirement vs tolerance
/// are different modalities), and guard atoms compare only by their whole
/// `AtomRef` equality upstream.
fn propositions<'a>(a: &'a AtomRef, b: &'a AtomRef) -> Option<(Proposition, Proposition)> {
    match (a, b) {
        (AtomRef::Behavior { behavior: x }, AtomRef::Behavior { behavior: y })
        | (AtomRef::Admissibility { behavior: x }, AtomRef::Admissibility { behavior: y }) => {
            Some((x.proposition(), y.proposition()))
        }
        _ => None,
    }
}

fn same_proposition(a: &AtomRef, b: &AtomRef) -> bool {
    propositions(a, b).is_some_and(|(x, y)| x == y)
}

/// Does this behavior/admissibility atom carry a Count subject quantifier?
/// Such an atom's `Not` wrapper is a PER-INDIVIDUAL denial (formula.rs,
/// § Quantifier scope convention), so every rule that reads `Not` as
/// classical outer negation must skip it (round 7 attack fix).
fn count_subject_ref(a: &AtomRef) -> bool {
    match a {
        AtomRef::Behavior { behavior } | AtomRef::Admissibility { behavior } => {
            matches!(behavior.subject.quantifier, Quantifier::Count { .. })
        }
        AtomRef::Guard { .. } => false,
    }
}

/// Is this formula a single atom with a Count subject ([`count_subject_ref`])?
fn count_subject_atom(f: &Formula) -> bool {
    matches!(f, Formula::Atom { atom } if count_subject_ref(atom))
}

/// Implication between two PER-INDIVIDUAL denials (`Not` over count-subject
/// atoms): sound only when the atoms are identical except their subject
/// Count quantifiers — then the denied predicate is one and the same, and
/// interval containment decides in the SAME direction (`at least 5
/// replicas refrain` ⇒ `at least 3 replicas refrain`). Any other
/// difference (a differing measure, a mixed quantifier kind) is `Unknown`:
/// the predicate parts would need CONTRAPOSED comparison under the
/// same-direction count logic, which no current rule grounds.
fn negated_count_implies(a: &AtomRef, b: &AtomRef) -> Ternary {
    let Some((x, y)) = propositions(a, b) else {
        return Ternary::Unknown;
    };
    if x.atom == y.atom && subject_digests_match(&x.subject, &y.subject) {
        return count_implies(&x.subject.quantifier, &y.subject.quantifier);
    }
    Ternary::Unknown
}

fn atom_implies(a: &AtomRef, b: &AtomRef) -> Ternary {
    if a == b {
        return Ternary::Yes;
    }
    let Some((x, y)) = propositions(a, b) else {
        return Ternary::Unknown;
    };
    if x == y {
        return Ternary::Yes;
    }
    proposition_implies(&x, &y)
}

// ---- the numeric refinement hook -----------------------------------------------------

/// Atom-level refinement: propositions identical except ONE differing
/// measure — a Deadline/Duration role measure or a comparison predicate —
/// with the same unit and parseable numbers. Round 6: comparisons are
/// judged as INTERVALS over the six operators (implication = containment),
/// read from the structured [`ComparisonSkeleton`] digest; anything else is
/// `Unknown`.
fn proposition_implies(a: &Proposition, b: &Proposition) -> Ternary {
    if a.subject != b.subject {
        // Round 7: count-quantifier entailment — subjects identical except
        // their Det-derived Count quantifiers, everything else identical,
        // judged as intervals (`at least 5` ⇒ `at least 3`; `exactly 4` ⇒
        // `at most 7`). Universal/Existential/Definite/Negative mismatches
        // stay Unknown (count_interval grounds Count only).
        if a.atom == b.atom && subject_digests_match(&a.subject, &b.subject) {
            return count_implies(&a.subject.quantifier, &b.subject.quantifier);
        }
        return Ternary::Unknown;
    }
    let x = &a.atom;
    let y = &b.atom;
    // The object group's conjunction is identity too (round 6 follow-up):
    // an `or`-object and its `and`-object twin share every item digest, so
    // without this gate the measure hooks below would compare them as one
    // proposition — a false Yes.
    // The content complement is identity too (round 7): differing
    // `that`-clauses are different claims, and no measure hook below may
    // compare across them.
    if x.objects_conj != y.objects_conj || x.content != y.content {
        return Ternary::Unknown;
    }
    // Differing role measure: everything else identical.
    if x.words == y.words && x.manner == y.manner && x.objects == y.objects {
        return roles_imply(&x.roles, &y.roles);
    }
    // Differing comparison predicate: everything else identical (the words
    // ARE the comparison's render, so they differ exactly with it).
    if x.manner == y.manner && x.objects == y.objects && x.roles == y.roles {
        if let (Some(ca), Some(cb)) = (&x.comparison, &y.comparison) {
            return comparison_implies(ca, cb);
        }
    }
    // Round 7: object-position count quantifiers — everything identical
    // except the Count quantifier of object noun phrases (`keep at least 5
    // replicas` ⇒ `keep at least 3 replicas`), subjects fully matched
    // above.
    if x.words == y.words
        && x.manner == y.manner
        && x.objects_conj == y.objects_conj
        && x.roles == y.roles
        && x.comparison == y.comparison
    {
        return objects_count_implies(&x.objects, &y.objects);
    }
    Ternary::Unknown
}

/// Do two subject digests match on everything EXCEPT the quantifier
/// (round 7)? The `full` string excludes the top-level determiner, so two
/// counted subjects over one restrictor+head meet here.
fn subject_digests_match(
    a: &crate::semantics::SubjectSkeleton,
    b: &crate::semantics::SubjectSkeleton,
) -> bool {
    a.restrictor == b.restrictor && a.head == b.head && a.full == b.full
}

/// The interval a Det-derived Count quantifier denotes (round 7): `at
/// least n` is `[n, ∞)`, `at most n` is `(-∞, n]`, `exactly n` the point
/// interval. `None` for every non-Count quantifier — mixed-kind pairs
/// (Universal vs Count, Definite vs Count, …) never ground, so they stay
/// `Unknown` at the call sites.
fn count_interval(q: &Quantifier) -> Option<Interval> {
    let Quantifier::Count { op, n } = q else {
        return None;
    };
    let n = *n as f64;
    let closed = |value: f64| {
        Some(Bound {
            value,
            closed: true,
        })
    };
    Some(match op {
        CountOp::AtLeast => Interval {
            lo: closed(n),
            hi: None,
        },
        CountOp::AtMost => Interval {
            lo: None,
            hi: closed(n),
        },
        CountOp::Exactly => Interval {
            lo: closed(n),
            hi: closed(n),
        },
    })
}

/// Count-quantifier implication as interval containment (round 7): both
/// quantifiers must be Count; `at least 5` ⇒ `at least 3`, `exactly 4` ⇒
/// `at least 3` and ⇒ `at most 7`. Counts carry no unit, so no unit gate.
fn count_implies(a: &Quantifier, b: &Quantifier) -> Ternary {
    let (Some(ia), Some(ib)) = (count_interval(a), count_interval(b)) else {
        return Ternary::Unknown;
    };
    if ia.contained_in(&ib) {
        Ternary::Yes
    } else {
        Ternary::Unknown
    }
}

/// Object-list count implication (round 7): same length, all items equal
/// except EXACTLY ONE pair matching on head and `full` whose quantifiers
/// are both Count — interval containment decides. A second difference, a
/// head/full mismatch, or a non-Count quantifier is out of scope.
fn objects_count_implies(xs: &[ObjectSkeleton], ys: &[ObjectSkeleton]) -> Ternary {
    if xs.len() != ys.len() {
        return Ternary::Unknown;
    }
    let mut verdict: Option<Ternary> = None;
    for (x, y) in xs.iter().zip(ys) {
        if x == y {
            continue;
        }
        if verdict.is_some() || x.head != y.head || x.full != y.full {
            return Ternary::Unknown;
        }
        verdict = Some(count_implies(&x.quantifier, &y.quantifier));
    }
    verdict.unwrap_or(Ternary::Unknown)
}

/// Does `x` PROVABLY EXCLUDE `y` (round 6)? True exactly when the two
/// propositions are identical except their comparison predicates and the
/// comparison intervals have an EMPTY intersection over the same unit —
/// `at most 3` excludes `at least 5`, while `at most 3` and `at least 3`
/// stay compatible at 3. Powers the `x → ¬y` implication rule, hence
/// [`contradicts`].
fn atoms_exclude(a: &AtomRef, b: &AtomRef) -> bool {
    let Some((x, y)) = propositions(a, b) else {
        return false;
    };
    // Round 7: subject count exclusion — subjects identical except their
    // Count quantifiers with DISJOINT intervals, atoms fully equal:
    // `at least 5 replicas run` excludes `at most 3 replicas run`.
    if x.subject != y.subject {
        return x.atom == y.atom
            && subject_digests_match(&x.subject, &y.subject)
            && counts_disjoint(&x.subject.quantifier, &y.subject.quantifier);
    }
    if x.atom.manner != y.atom.manner
        || x.atom.objects_conj != y.atom.objects_conj
        || x.atom.content != y.atom.content
    {
        return false;
    }
    // Round 7: object count exclusion — everything else equal, exactly one
    // object pair (matching head and `full`) with disjoint Count intervals.
    if x.atom.objects != y.atom.objects {
        return x.atom.words == y.atom.words
            && x.atom.roles == y.atom.roles
            && x.atom.comparison == y.atom.comparison
            && objects_count_exclude(&x.atom.objects, &y.atom.objects);
    }
    if x.atom.roles != y.atom.roles {
        // Round 7 (change 7): same-kind Deadline/Duration role-measure
        // EXCLUSION — everything else equal, exactly one same-kind measure
        // pair whose intervals are provably disjoint over one unit
        // (`for at least 30 days` vs `for less than 10 days`). Supersedes
        // the round-6 "role intervals ground implication but not
        // contradiction" conservatism: the interval reading is the same
        // one containment already trusts, and an empty intersection is a
        // proof, not a guess. Mixed kinds (Deadline vs Duration) and unit
        // mismatches still never ground.
        return x.atom.words == y.atom.words
            && x.atom.comparison == y.atom.comparison
            && roles_exclude(&x.atom.roles, &y.atom.roles);
    }
    let (Some(ca), Some(cb)) = (&x.atom.comparison, &y.atom.comparison) else {
        return false;
    };
    let (Some((ia, ua)), Some((ib, ub))) = (interval_of(ca), interval_of(cb)) else {
        return false;
    };
    same_unit(ua.as_deref(), ub.as_deref()) && ia.disjoint(&ib)
}

/// Are two Count quantifiers provably DISJOINT (round 7)? `at least 5` vs
/// `at most 3` share no count. Non-Count quantifiers never ground.
fn counts_disjoint(a: &Quantifier, b: &Quantifier) -> bool {
    match (count_interval(a), count_interval(b)) {
        (Some(ia), Some(ib)) => ia.disjoint(&ib),
        _ => false,
    }
}

/// Object-list count exclusion (round 7): all items equal except EXACTLY
/// ONE pair matching on head and `full` whose Count intervals are disjoint.
fn objects_count_exclude(xs: &[ObjectSkeleton], ys: &[ObjectSkeleton]) -> bool {
    if xs.len() != ys.len() {
        return false;
    }
    let mut found = false;
    for (x, y) in xs.iter().zip(ys) {
        if x == y {
            continue;
        }
        if found || x.head != y.head || x.full != y.full {
            return false;
        }
        if !counts_disjoint(&x.quantifier, &y.quantifier) {
            return false;
        }
        found = true;
    }
    found
}

/// Role-list exclusion (round 7, change 7): same kinds in order, all
/// values equal except EXACTLY ONE same-kind Deadline/Duration measure
/// pair whose intervals share one unit and have an EMPTY intersection.
/// Mixed kinds and unit mismatches never ground.
fn roles_exclude(xs: &[RoleSkeleton], ys: &[RoleSkeleton]) -> bool {
    if xs.len() != ys.len() {
        return false;
    }
    let mut found = false;
    for (x, y) in xs.iter().zip(ys) {
        if x == y {
            continue;
        }
        if found || x.kind != y.kind {
            return false;
        }
        let (Some((ix, ux)), Some((iy, uy))) = (
            role_interval(x.kind, &x.value),
            role_interval(y.kind, &y.value),
        ) else {
            return false;
        };
        if !same_unit(ux.as_deref(), uy.as_deref()) || !ix.disjoint(&iy) {
            return false;
        }
        found = true;
    }
    found
}

/// Role-list refinement: same kinds in order, all values equal except
/// exactly one Deadline/Duration measure pair, judged as INTERVALS (round
/// 6 — bounded measures included): implication is containment.
fn roles_imply(xs: &[RoleSkeleton], ys: &[RoleSkeleton]) -> Ternary {
    if xs.len() != ys.len() {
        return Ternary::Unknown;
    }
    let mut verdict: Option<Ternary> = None;
    for (x, y) in xs.iter().zip(ys) {
        if x == y {
            continue;
        }
        if verdict.is_some() || x.kind != y.kind {
            // A second difference, or a kind mismatch: out of scope.
            return Ternary::Unknown;
        }
        let (Some((ix, ux)), Some((iy, uy))) = (
            role_interval(x.kind, &x.value),
            role_interval(y.kind, &y.value),
        ) else {
            return Ternary::Unknown;
        };
        if !same_unit(ux.as_deref(), uy.as_deref()) {
            return Ternary::Unknown;
        }
        verdict = Some(if ix.contained_in(&iy) {
            Ternary::Yes
        } else {
            Ternary::Unknown
        });
    }
    verdict.unwrap_or(Ternary::Unknown)
}

/// The interval a Deadline/Duration role denotes.
///
/// Plain measures keep their ROUND-5 LEGISLATED directions, which the
/// interval reading generalizes rather than replaces: `within n` is the
/// upper bound `(-∞, n]` (a tighter deadline meets every looser one), and
/// `for n` is the lower bound `[n, ∞)` (holding for n covers every shorter
/// requirement — retaining longer implies retaining shorter). Bounded
/// measures (round 6) denote their own operator's interval, so `for at
/// least 30 days` is `[30, ∞)` and composes with the plain reading: `for
/// 30 days` implies `for at least 10 days` and vice-versa rules follow
/// from containment alone.
fn role_interval(kind: RoleKind, value: &RoleValue) -> Option<(Interval, Option<String>)> {
    if !matches!(kind, RoleKind::Deadline | RoleKind::Duration) {
        return None;
    }
    match value {
        RoleValue::Measure { number, unit } => {
            let n = numeric(number)?;
            let interval = match kind {
                RoleKind::Deadline => Interval {
                    lo: None,
                    hi: Some(Bound {
                        value: n,
                        closed: true,
                    }),
                },
                RoleKind::Duration => Interval {
                    lo: Some(Bound {
                        value: n,
                        closed: true,
                    }),
                    hi: None,
                },
                _ => unreachable!("guarded above"),
            };
            Some((interval, unit.clone()))
        }
        RoleValue::BoundedMeasure {
            op,
            number,
            unit,
            upper,
        } => interval_of(&ComparisonSkeleton {
            op: *op,
            value: MeasureSkeleton::Quantity {
                number: number.clone(),
                unit: unit.clone(),
            },
            upper: upper.as_ref().map(|u| MeasureSkeleton::Quantity {
                number: u.clone(),
                unit: unit.clone(),
            }),
        }),
        _ => None,
    }
}

// ---- interval semantics over comparisons (round 6) -----------------------------------

/// One bound of a numeric interval. `None` is the unbounded side.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Bound {
    value: f64,
    /// Whether the bound's own value belongs to the interval. Open-vs-closed
    /// is DOCUMENTED AND FIXED: `greater than`/`less than` are open,
    /// `at least`/`at most` are closed, `equal to` is the point interval,
    /// `between` is closed at both ends.
    closed: bool,
}

/// A numeric interval over one unit: the denotation of a comparison.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Interval {
    lo: Option<Bound>,
    hi: Option<Bound>,
}

impl Interval {
    /// Is `self` contained in `other`? Interval containment IS comparison
    /// implication: every value satisfying `self` satisfies `other`.
    fn contained_in(&self, other: &Interval) -> bool {
        let lo_ok = match (&other.lo, &self.lo) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(o), Some(s)) => {
                s.value > o.value || (s.value == o.value && (o.closed || !s.closed))
            }
        };
        let hi_ok = match (&other.hi, &self.hi) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(o), Some(s)) => {
                s.value < o.value || (s.value == o.value && (o.closed || !s.closed))
            }
        };
        lo_ok && hi_ok
    }

    /// Is the intersection of `self` and `other` empty? Empty intersection
    /// IS comparison contradiction. Touching CLOSED endpoints intersect:
    /// `at most 3` and `at least 3` are compatible at 3 — not disjoint.
    fn disjoint(&self, other: &Interval) -> bool {
        let below = |hi: &Option<Bound>, lo: &Option<Bound>| match (hi, lo) {
            (Some(h), Some(l)) => {
                h.value < l.value || (h.value == l.value && !(h.closed && l.closed))
            }
            _ => false,
        };
        below(&self.hi, &other.lo) || below(&other.hi, &self.lo)
    }
}

/// The interval and unit of a structured comparison digest. `None` when the
/// comparison cannot be grounded: a noun-phrase measure, an unparseable
/// number, or a `between` whose two bounds carry DIFFERENT units (both
/// bounds must share one unit — legislated).
fn interval_of(c: &ComparisonSkeleton) -> Option<(Interval, Option<String>)> {
    let quantity = |m: &MeasureSkeleton| match m {
        MeasureSkeleton::Quantity { number, unit } => Some((numeric(number)?, unit.clone())),
        MeasureSkeleton::Np { .. } => None,
    };
    let (n, unit) = quantity(&c.value)?;
    let interval = match c.op {
        ComparisonOp::GreaterThan => Interval {
            lo: Some(Bound {
                value: n,
                closed: false,
            }),
            hi: None,
        },
        ComparisonOp::LessThan => Interval {
            lo: None,
            hi: Some(Bound {
                value: n,
                closed: false,
            }),
        },
        ComparisonOp::AtLeast => Interval {
            lo: Some(Bound {
                value: n,
                closed: true,
            }),
            hi: None,
        },
        ComparisonOp::AtMost => Interval {
            lo: None,
            hi: Some(Bound {
                value: n,
                closed: true,
            }),
        },
        ComparisonOp::EqualTo => Interval {
            lo: Some(Bound {
                value: n,
                closed: true,
            }),
            hi: Some(Bound {
                value: n,
                closed: true,
            }),
        },
        ComparisonOp::Between => {
            let (upper, upper_unit) = quantity(c.upper.as_ref()?)?;
            // Both bounds must share one unit: a written unit on either
            // side fixes it, and two written units must agree.
            let unit = match (unit, upper_unit) {
                (Some(a), Some(b)) => {
                    if !a.eq_ignore_ascii_case(&b) {
                        return None;
                    }
                    Some(a)
                }
                (Some(a), None) => Some(a),
                (None, other) => other,
            };
            return Some((
                Interval {
                    lo: Some(Bound {
                        value: n,
                        closed: true,
                    }),
                    hi: Some(Bound {
                        value: upper,
                        closed: true,
                    }),
                },
                unit,
            ));
        }
    };
    Some((interval, unit))
}

/// Comparison implication as interval containment (round 6): same unit
/// required, then `a ⊆ b` decides. Cross-operator implications now hold
/// where containment does (`equal to 3` implies `at most 3`; `between 4
/// and 6` implies `at least 4`); anything ungroundable is `Unknown`.
fn comparison_implies(a: &ComparisonSkeleton, b: &ComparisonSkeleton) -> Ternary {
    let (Some((ia, ua)), Some((ib, ub))) = (interval_of(a), interval_of(b)) else {
        return Ternary::Unknown;
    };
    if !same_unit(ua.as_deref(), ub.as_deref()) {
        return Ternary::Unknown;
    }
    if ia.contained_in(&ib) {
        Ternary::Yes
    } else {
        Ternary::Unknown
    }
}

/// Units must MATCH (case-insensitively); there is no normalization table.
/// `seconds` vs `ms` — and a present unit vs a missing one — is `Unknown`
/// territory, decided by the callers.
fn same_unit(a: Option<&str>, b: Option<&str>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => a.eq_ignore_ascii_case(b),
        _ => false,
    }
}

/// The numeric value of a measure token: a numeral (integers and decimals)
/// or one of the grammar's number words — the same table the recognizer
/// admits (round 12 extends both together: `zero`–`twenty`, tens to
/// `ninety`, `hundred`; single words only), so a measure written with a
/// word grounds the same interval its digit spelling does (`within eleven
/// seconds` refines `within twelve seconds`).
fn numeric(word: &str) -> Option<f64> {
    if let Ok(n) = word.parse::<f64>() {
        return n.is_finite().then_some(n);
    }
    const NUMBER_WORDS: &[(&str, f64)] = &[
        ("zero", 0.0),
        ("one", 1.0),
        ("two", 2.0),
        ("three", 3.0),
        ("four", 4.0),
        ("five", 5.0),
        ("six", 6.0),
        ("seven", 7.0),
        ("eight", 8.0),
        ("nine", 9.0),
        ("ten", 10.0),
        ("eleven", 11.0),
        ("twelve", 12.0),
        ("thirteen", 13.0),
        ("fourteen", 14.0),
        ("fifteen", 15.0),
        ("sixteen", 16.0),
        ("seventeen", 17.0),
        ("eighteen", 18.0),
        ("nineteen", 19.0),
        ("twenty", 20.0),
        ("thirty", 30.0),
        ("forty", 40.0),
        ("fifty", 50.0),
        ("sixty", 60.0),
        ("seventy", 70.0),
        ("eighty", 80.0),
        ("ninety", 90.0),
        ("hundred", 100.0),
    ];
    NUMBER_WORDS
        .iter()
        .find(|(w, _)| word.eq_ignore_ascii_case(w))
        .map(|(_, n)| *n)
}
