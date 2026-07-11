//! Origin enrichment (provenance sense ①: the source artifact's own provenance).
//!
//! Distinct from our snapshot (sense ②), origin is a claim *by the source* about
//! who authored it and when — a claim that could itself be wrong. The daemon
//! discovers it best-effort and lets the caller override it. The [`Origin`] value
//! type itself lives in the daemon domain; this module *produces* it.
//!
//! Enrichment is pluggable via [`OriginEnricher`]. Two built-ins ship:
//!   * [`GitEnricher`] — for files under version control (`git log`);
//!   * [`WebEnricher`] — for URLs, using hints extracted while snapshotting.
//!
//! **The plugin seam.** An external crate adds an enricher without editing this
//! crate: implement [`OriginEnricher`], then register it at link time. Submit
//! through this crate's re-exported [`inventory`] (`so_daemon::inventory`)
//! so no version-matched `inventory` dependency of your own is required:
//!
//! ```ignore
//! use so_daemon::origin::{EnricherRegistration, OriginEnricher};
//! struct IssueTrackerEnricher;
//! impl OriginEnricher for IssueTrackerEnricher { /* … */ }
//! fn make() -> Box<dyn OriginEnricher> { Box::new(IssueTrackerEnricher) }
//! so_daemon::inventory::submit! {
//!     EnricherRegistration::new("issue-tracker", 10, make)
//! }
//! ```
//!
//! [`registered_enrichers`] collects the built-ins and every submitted
//! registration, so the add operation calls them with no code change here.
//! (For the linker to keep a plugin crate's submissions, that crate must be
//! reachable from the final binary — reference it at least once, e.g. an
//! `extern crate` or a use.)
//!
//! Resolution precedence for each field: caller override (`--evidence` origin)
//! wins, then the enricher's discovery. A field nobody supplies stays `None`.
//! Among enrichers that handle the same locator, the highest-`priority` one wins
//! (first-match, not merge); ties break by `name`. As long as `name`s are
//! distinct — which they should be, since `name` identifies the enricher — the
//! order is fully determined and independent of link order.

use crate::domain::{Locator, Origin};

use crate::evidence::OriginInput;
use crate::snapshot::run_git;

/// Seed an [`Origin`] from a caller-supplied override.
fn origin_from_input(i: &OriginInput) -> Origin {
    Origin {
        author: i.author.clone(),
        created_at: i.created_at.clone(),
        updated_at: i.updated_at.clone(),
    }
}

/// Fill only the fields still empty in `origin` from `other`.
fn backfill(mut origin: Origin, other: &OriginInput) -> Origin {
    if origin.author.is_none() {
        origin.author = other.author.clone();
    }
    if origin.created_at.is_none() {
        origin.created_at = other.created_at.clone();
    }
    if origin.updated_at.is_none() {
        origin.updated_at = other.updated_at.clone();
    }
    origin
}

/// An extension point for discovering source provenance from a locator. Built-in
/// enrichers cover git and web; further parsers (package registries, issue
/// trackers, …) can be added without touching the add operation.
pub trait OriginEnricher {
    /// Whether this enricher handles the given locator.
    fn handles(&self, locator: &Locator) -> bool;
    /// Discover what it can. Best-effort: unknown fields are left `None`.
    fn discover(&self, locator: &Locator, hints: &OriginInput) -> OriginInput;
}

/// Discovers author and first/last change dates from `git log`.
pub struct GitEnricher;

impl OriginEnricher for GitEnricher {
    fn handles(&self, locator: &Locator) -> bool {
        matches!(locator, Locator::File { .. })
    }

    fn discover(&self, locator: &Locator, _hints: &OriginInput) -> OriginInput {
        let Locator::File { path, .. } = locator else {
            return OriginInput::default();
        };
        let p = std::path::Path::new(path);
        let dir = p.parent().filter(|d| !d.as_os_str().is_empty());
        // git runs in the file's parent directory, so the pathspec must be the
        // file name relative to it — not the full path, which would be resolved
        // against the parent again and match nothing.
        let Some(name) = p.file_name() else {
            return OriginInput::default();
        };
        let file = name.to_string_lossy();

        // Last commit that touched the path: author name + author date.
        let author =
            run_git(dir, &["log", "-1", "--format=%an", "--", &file]).filter(|s| !s.is_empty());
        let updated_at =
            run_git(dir, &["log", "-1", "--format=%aI", "--", &file]).filter(|s| !s.is_empty());
        // First commit that introduced the path (oldest author date).
        let created_at = run_git(dir, &["log", "--reverse", "--format=%aI", "--", &file])
            .and_then(|s| s.lines().next().map(str::to_string))
            .filter(|s| !s.is_empty());

        OriginInput {
            author,
            created_at,
            updated_at,
        }
    }
}

/// Uses web metadata hints gathered during snapshotting (HTML `<meta>` tags).
pub struct WebEnricher;

impl OriginEnricher for WebEnricher {
    fn handles(&self, locator: &Locator) -> bool {
        matches!(locator, Locator::Url { .. })
    }

    fn discover(&self, _locator: &Locator, hints: &OriginInput) -> OriginInput {
        hints.clone()
    }
}

/// Resolve the final [`Origin`]: caller override first, then the first enricher
/// that handles the locator, then any snapshot hints as a last backfill.
pub fn finalize(
    locator: &Locator,
    override_input: &OriginInput,
    hints: &OriginInput,
    enrichers: &[Box<dyn OriginEnricher>],
) -> Origin {
    let mut origin = origin_from_input(override_input);
    if let Some(enricher) = enrichers.iter().find(|e| e.handles(locator)) {
        let discovered = enricher.discover(locator, hints);
        origin = backfill(origin, &discovered);
    }
    backfill(origin, hints)
}

/// A link-time registration of an [`OriginEnricher`]. External crates submit one
/// via [`inventory::submit!`] to plug an enricher into ingest without editing
/// this crate. `factory` constructs the enricher; `priority` orders it (higher
/// is consulted first); `name` breaks ties and identifies it.
///
/// Construct via [`EnricherRegistration::new`] rather than a struct literal: the
/// constructor is the stable submission form, so future optional fields can be
/// added here without breaking existing plugins' call sites.
pub struct EnricherRegistration {
    pub name: &'static str,
    pub priority: i32,
    pub factory: fn() -> Box<dyn OriginEnricher>,
}

impl EnricherRegistration {
    /// The stable way to build a registration for [`inventory::submit!`]. `const`
    /// because `submit!` evaluates its argument into a `static`.
    pub const fn new(
        name: &'static str,
        priority: i32,
        factory: fn() -> Box<dyn OriginEnricher>,
    ) -> EnricherRegistration {
        EnricherRegistration {
            name,
            priority,
            factory,
        }
    }
}

inventory::collect!(EnricherRegistration);

fn make_git() -> Box<dyn OriginEnricher> {
    Box::new(GitEnricher)
}

fn make_web() -> Box<dyn OriginEnricher> {
    Box::new(WebEnricher)
}

/// The always-present built-ins. They are registered explicitly (not via
/// `inventory`) so they are guaranteed to be linked; submitted plugins are
/// merged on top in [`registered_enrichers`].
static BUILTIN_ENRICHERS: &[EnricherRegistration] = &[
    EnricherRegistration::new("git", 0, make_git),
    EnricherRegistration::new("web", 0, make_web),
];

/// The enrichers ingest will consult: the built-ins plus every
/// [`inventory::submit!`]-ed [`EnricherRegistration`], ordered deterministically
/// by descending `priority` then ascending `name` (independent of link order).
///
/// This is the wiring that makes the [`OriginEnricher`] seam reach `spec add`:
/// [`crate::add::run`] calls it, so a linked plugin's enricher is invoked with no
/// edit to the core crate.
pub fn registered_enrichers() -> Vec<Box<dyn OriginEnricher>> {
    let mut regs: Vec<&'static EnricherRegistration> = BUILTIN_ENRICHERS.iter().collect();
    for reg in inventory::iter::<EnricherRegistration> {
        regs.push(reg);
    }
    regs.sort_by(|a, b| b.priority.cmp(&a.priority).then_with(|| a.name.cmp(b.name)));
    regs.into_iter().map(|r| (r.factory)()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn override_wins_over_discovery() {
        struct Fake;
        impl OriginEnricher for Fake {
            fn handles(&self, _: &Locator) -> bool {
                true
            }
            fn discover(&self, _: &Locator, _: &OriginInput) -> OriginInput {
                OriginInput {
                    author: Some("discovered".into()),
                    created_at: Some("2000-01-01T00:00:00Z".into()),
                    updated_at: Some("2000-01-02T00:00:00Z".into()),
                }
            }
        }
        let loc = Locator::File {
            path: "x.rs".into(),
            line: None,
            col: None,
        };
        let override_input = OriginInput {
            author: Some("caller".into()),
            ..Default::default()
        };
        let enrichers: Vec<Box<dyn OriginEnricher>> = vec![Box::new(Fake)];
        let o = finalize(&loc, &override_input, &OriginInput::default(), &enrichers);
        // Author from override; dates backfilled from discovery.
        assert_eq!(o.author.as_deref(), Some("caller"));
        assert_eq!(o.created_at.as_deref(), Some("2000-01-01T00:00:00Z"));
        assert_eq!(o.updated_at.as_deref(), Some("2000-01-02T00:00:00Z"));
    }

    #[test]
    fn web_enricher_passes_hints_through() {
        let loc = Locator::Url {
            url: "https://example.com".into(),
        };
        let hints = OriginInput {
            author: Some("Jane".into()),
            created_at: Some("2024-01-02T00:00:00Z".into()),
            updated_at: None,
        };
        let o = finalize(
            &loc,
            &OriginInput::default(),
            &hints,
            &registered_enrichers(),
        );
        assert_eq!(o.author.as_deref(), Some("Jane"));
        assert_eq!(o.created_at.as_deref(), Some("2024-01-02T00:00:00Z"));
    }

    // A test-only plugin registered through the same public seam an external
    // crate would use. It handles only a sentinel path, so it never perturbs the
    // other tests' File/Url dispatch, and carries a high priority to prove that a
    // submitted enricher is collected and consulted ahead of the built-ins.
    const PROBE_PATH: &str = "__registry_probe__";

    struct ProbeEnricher;
    impl OriginEnricher for ProbeEnricher {
        fn handles(&self, locator: &Locator) -> bool {
            matches!(locator, Locator::File { path, .. } if path == PROBE_PATH)
        }
        fn discover(&self, _: &Locator, _: &OriginInput) -> OriginInput {
            OriginInput {
                author: Some("registered-plugin".into()),
                ..Default::default()
            }
        }
    }

    fn make_probe() -> Box<dyn OriginEnricher> {
        Box::new(ProbeEnricher)
    }

    inventory::submit! {
        EnricherRegistration::new("probe", 100, make_probe)
    }

    #[test]
    fn submitted_enricher_is_collected_and_invoked_at_ingest() {
        // The registry picks up the inventory submission alongside the built-ins.
        let enrichers = registered_enrichers();
        assert!(
            enrichers.len() >= 3,
            "expected built-ins plus the submitted probe"
        );

        // And finalize actually dispatches to it for the sentinel locator —
        // exactly the path add::run drives during ingest.
        let loc = Locator::File {
            path: PROBE_PATH.into(),
            line: None,
            col: None,
        };
        let o = finalize(
            &loc,
            &OriginInput::default(),
            &OriginInput::default(),
            &enrichers,
        );
        assert_eq!(o.author.as_deref(), Some("registered-plugin"));
    }

    #[test]
    fn registered_order_is_deterministic_by_priority_then_name() {
        // The probe (priority 100) sorts ahead of the built-ins (priority 0),
        // whose relative order is fixed by name: git before web.
        let names: Vec<&str> = {
            let mut regs: Vec<&EnricherRegistration> = BUILTIN_ENRICHERS.iter().collect();
            for reg in inventory::iter::<EnricherRegistration> {
                regs.push(reg);
            }
            regs.sort_by(|a, b| b.priority.cmp(&a.priority).then_with(|| a.name.cmp(b.name)));
            regs.into_iter().map(|r| r.name).collect()
        };
        let git = names.iter().position(|n| *n == "git").unwrap();
        let web = names.iter().position(|n| *n == "web").unwrap();
        let probe = names.iter().position(|n| *n == "probe").unwrap();
        assert!(probe < git, "higher priority is consulted first");
        assert!(git < web, "equal priority ties break by name");
    }
}
