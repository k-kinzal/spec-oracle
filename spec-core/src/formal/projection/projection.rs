/// Projection: The composition of observation and extraction
///
/// proj_i = obs_i >> extract_i
///
/// A projection takes a RootSpace, observes it through a specific layer lens
/// to produce an ArtifactSpace, then extracts typed intermediate representations.
///
/// This implements the core composition from paper §2.6:
///   Γ_root →[obs_i]→ Γ_i →[extract_i]→ β_i
///
/// Where:
///   - obs_i: RootSpace → ArtifactSpace (layer-specific observation)
///   - extract_i: ArtifactSpace → Vec<T> (typed extraction from artifacts)
///   - proj_i: the composition obs_i >> extract_i
use crate::formal::projection::{ArtifactSpace, Observer, RootSpace};
use crate::formal::universe::UniverseId;

/// Extractor trait: Γ_i → Option<β_i>
///
/// Extracts typed intermediate representations from an artifact space.
/// Each extractor is specialized for a particular output type T (the β_i).
///
/// Returns a Vec<T> because a single artifact space may yield multiple
/// extracted items (e.g., multiple spec fragments from a code file).
pub trait Extractor<T> {
    /// Extract typed representations from an artifact space.
    ///
    /// Given an observed artifact space Γ_i, produces a vector of
    /// extracted items of type T. Returns an empty Vec if no items
    /// can be extracted (rather than failing).
    fn extract(&self, artifact: &ArtifactSpace) -> Vec<T>;
}

/// Projection: composes an Observer and an Extractor into a single operation.
///
/// ```text
/// RootSpace →[observer]→ ArtifactSpace →[extractor]→ Vec<T>
/// ```
///
/// The target_layer determines which universe layer the observer focuses on.
pub struct Projection<O, E> {
    /// The observer that produces an ArtifactSpace from a RootSpace
    pub observer: O,

    /// The extractor that produces typed output from an ArtifactSpace
    pub extractor: E,

    /// The target universe layer for observation (e.g., U1, U2, U3)
    pub target_layer: UniverseId,
}

impl<O, E> Projection<O, E>
where
    O: Observer,
{
    /// Create a new projection for a specific target layer.
    pub fn new(observer: O, extractor: E, target_layer: UniverseId) -> Self {
        Self {
            observer,
            extractor,
            target_layer,
        }
    }

    /// Execute the projection: obs >> extract
    ///
    /// 1. Calls observer.observe(root, &target_layer) to get Option<ArtifactSpace>
    /// 2. If Some(artifact), calls extractor.extract(&artifact) to get Vec<T>
    /// 3. If None, returns empty Vec
    /// 4. Returns the extracted items
    pub fn project<T>(&self, root: &RootSpace) -> Vec<T>
    where
        E: Extractor<T>,
    {
        match self.observer.observe(root, &self.target_layer) {
            Some(artifact) => self.extractor.extract(&artifact),
            None => Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A trivial observer for testing that returns an empty ArtifactSpace
    struct StubObserver;

    impl Observer for StubObserver {
        fn observe(&self, _root: &RootSpace, _layer: &UniverseId) -> Option<ArtifactSpace> {
            use crate::formal::projection::ArtifactKind;
            Some(ArtifactSpace::from_text(
                ArtifactKind::SourceCode,
                String::new(),
                "stub".to_string(),
            ))
        }

        fn artifact_kind(&self) -> crate::formal::projection::ArtifactKind {
            crate::formal::projection::ArtifactKind::SourceCode
        }
    }

    /// A trivial extractor for testing that always returns an empty Vec
    struct StubExtractor;

    impl Extractor<String> for StubExtractor {
        fn extract(&self, _artifact: &ArtifactSpace) -> Vec<String> {
            Vec::new()
        }
    }

    #[test]
    fn projection_compose_returns_empty_for_stub() {
        let proj = Projection::new(
            StubObserver,
            StubExtractor,
            UniverseId::root(),
        );
        let root = RootSpace::new_artifact_bundle();
        let result: Vec<String> = proj.project(&root);
        assert!(result.is_empty());
    }
}
