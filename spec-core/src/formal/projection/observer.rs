/// Observer: obs_i (Omega -> Option Gamma_i)
///
/// An observer examines a root space (Omega) and, if the root space matches
/// the observer's expected kind, extracts an artifact space (Gamma_i) from it.
///
/// This is the first half of the projection composition:
///   proj_i = obs_i >> extract_i
///
/// Each observer is specialized for a particular root space kind:
/// - ArtifactBundleObserver: observes artifact bundle root spaces
/// - TraceObserver: observes behavioral trace root spaces
/// - FileSystemObserver: observes file system root spaces directly
use crate::formal::projection::{RootSpace, RootSpaceKind, ArtifactSpace, ArtifactKind};
use crate::formal::universe::UniverseId;

/// Observer trait: examines a root space and produces an artifact space.
///
/// Implements obs_i: Omega -> Option<Gamma_i>
/// Returns None when the root space kind does not match the observer's expectation.
pub trait Observer {
    /// Attempt to observe an artifact space from the given root space.
    ///
    /// The layer_id parameter specifies which universe layer is being observed,
    /// allowing observers to filter or select artifacts based on layer metadata.
    ///
    /// Returns `Some(ArtifactSpace)` if the root space kind matches and
    /// artifact information can be extracted from metadata.
    /// Returns `None` if the root space kind does not match.
    fn observe(&self, root: &RootSpace, layer_id: &UniverseId) -> Option<ArtifactSpace>;

    /// The kind of artifact this observer produces.
    fn artifact_kind(&self) -> ArtifactKind;
}

/// Observer for artifact bundle root spaces.
///
/// Expects `RootSpaceKind::ArtifactBundle` and extracts artifact information
/// from the root space metadata fields: "content_value" and "source".
pub struct ArtifactBundleObserver {
    expected_artifact_kind: ArtifactKind,
}

impl ArtifactBundleObserver {
    pub fn new(expected_artifact_kind: ArtifactKind) -> Self {
        Self { expected_artifact_kind }
    }
}

impl Observer for ArtifactBundleObserver {
    fn observe(&self, root: &RootSpace, _layer_id: &UniverseId) -> Option<ArtifactSpace> {
        if root.kind() != Some(RootSpaceKind::ArtifactBundle) {
            return None;
        }

        let inner = root.meta.inner();
        let content = inner.get("content_value").cloned().unwrap_or_default();
        let source = inner.get("source").cloned()
            .unwrap_or_else(|| format!("artifact_bundle:{}", root.id));

        Some(ArtifactSpace::from_text(self.expected_artifact_kind, content, source))
    }

    fn artifact_kind(&self) -> ArtifactKind {
        self.expected_artifact_kind
    }
}

/// Observer for behavioral trace root spaces.
///
/// Expects `RootSpaceKind::Trace` and extracts trace data as an artifact space.
/// Traces represent runtime behavior observations (logs, execution traces, etc.).
pub struct TraceObserver {
    expected_artifact_kind: ArtifactKind,
}

impl TraceObserver {
    pub fn new(expected_artifact_kind: ArtifactKind) -> Self {
        Self { expected_artifact_kind }
    }
}

impl Observer for TraceObserver {
    fn observe(&self, root: &RootSpace, _layer_id: &UniverseId) -> Option<ArtifactSpace> {
        if root.kind() != Some(RootSpaceKind::Trace) {
            return None;
        }

        let inner = root.meta.inner();
        let content = inner.get("trace_data").cloned()
            .or_else(|| inner.get("content_value").cloned())
            .unwrap_or_default();
        let source = inner.get("source").cloned()
            .unwrap_or_else(|| format!("trace:{}", root.id));

        Some(ArtifactSpace::from_text(self.expected_artifact_kind, content, source))
    }

    fn artifact_kind(&self) -> ArtifactKind {
        self.expected_artifact_kind
    }
}

/// Observer for direct file system observation.
///
/// Does not check root space kind -- it reads artifact information directly
/// from file system paths stored in the root space metadata.
/// This enables observation of raw files (source code, docs, proto files)
/// without requiring them to be pre-bundled.
pub struct FileSystemObserver {
    expected_artifact_kind: ArtifactKind,
}

impl FileSystemObserver {
    pub fn new(expected_artifact_kind: ArtifactKind) -> Self {
        Self { expected_artifact_kind }
    }
}

impl Observer for FileSystemObserver {
    fn observe(&self, root: &RootSpace, _layer_id: &UniverseId) -> Option<ArtifactSpace> {
        let inner = root.meta.inner();
        let file_path = inner.get("file_path")?;

        Some(ArtifactSpace::from_file(self.expected_artifact_kind, file_path.clone()))
    }

    fn artifact_kind(&self) -> ArtifactKind {
        self.expected_artifact_kind
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn artifact_bundle_observer_matches_correct_kind() {
        let root = RootSpace::new_artifact_bundle();
        let observer = ArtifactBundleObserver::new(ArtifactKind::SourceCode);
        let layer_id = UniverseId::projection(3).unwrap();

        let result = observer.observe(&root, &layer_id);
        assert!(result.is_some());
    }

    #[test]
    fn artifact_bundle_observer_rejects_wrong_kind() {
        let root = RootSpace::new_trace();
        let observer = ArtifactBundleObserver::new(ArtifactKind::SourceCode);
        let layer_id = UniverseId::projection(3).unwrap();

        let result = observer.observe(&root, &layer_id);
        assert!(result.is_none());
    }

    #[test]
    fn trace_observer_matches_correct_kind() {
        let root = RootSpace::new_trace();
        let observer = TraceObserver::new(ArtifactKind::TestCode);
        let layer_id = UniverseId::projection(3).unwrap();

        let result = observer.observe(&root, &layer_id);
        assert!(result.is_some());
    }

    #[test]
    fn trace_observer_rejects_wrong_kind() {
        let root = RootSpace::new_artifact_bundle();
        let observer = TraceObserver::new(ArtifactKind::TestCode);
        let layer_id = UniverseId::projection(3).unwrap();

        let result = observer.observe(&root, &layer_id);
        assert!(result.is_none());
    }

    #[test]
    fn file_system_observer_requires_file_path() {
        let root = RootSpace::new_artifact_bundle();
        let observer = FileSystemObserver::new(ArtifactKind::SourceCode);
        let layer_id = UniverseId::projection(3).unwrap();

        // No file_path in metadata, should return None
        let result = observer.observe(&root, &layer_id);
        assert!(result.is_none());
    }

    #[test]
    fn file_system_observer_extracts_from_file_path() {
        let mut root = RootSpace::new_artifact_bundle();
        root.meta.inner_mut().insert("file_path".to_string(), "src/main.rs".to_string());

        let observer = FileSystemObserver::new(ArtifactKind::SourceCode);
        let layer_id = UniverseId::projection(3).unwrap();

        let result = observer.observe(&root, &layer_id);
        assert!(result.is_some());
        let artifact = result.unwrap();
        assert_eq!(artifact.kind(), Some(ArtifactKind::SourceCode));
    }

    #[test]
    fn observer_returns_correct_artifact_kind() {
        let observer = ArtifactBundleObserver::new(ArtifactKind::APISpec);
        assert_eq!(observer.artifact_kind(), ArtifactKind::APISpec);

        let observer = TraceObserver::new(ArtifactKind::TestCode);
        assert_eq!(observer.artifact_kind(), ArtifactKind::TestCode);

        let observer = FileSystemObserver::new(ArtifactKind::FormalSpec);
        assert_eq!(observer.artifact_kind(), ArtifactKind::FormalSpec);
    }

    #[test]
    fn artifact_bundle_observer_extracts_content() {
        let mut root = RootSpace::new_artifact_bundle();
        root.meta.inner_mut().insert("content_value".to_string(), "fn main() {}".to_string());
        root.meta.inner_mut().insert("source".to_string(), "src/main.rs".to_string());

        let observer = ArtifactBundleObserver::new(ArtifactKind::SourceCode);
        let layer_id = UniverseId::projection(3).unwrap();
        let artifact = observer.observe(&root, &layer_id).unwrap();

        assert_eq!(artifact.as_text(), Some(&"fn main() {}".to_string()));
        assert_eq!(artifact.source(), Some(&"src/main.rs".to_string()));
    }

    #[test]
    fn trace_observer_extracts_trace_data() {
        let mut root = RootSpace::new_trace();
        root.meta.inner_mut().insert("trace_data".to_string(), "test passed: ok".to_string());

        let observer = TraceObserver::new(ArtifactKind::TestCode);
        let layer_id = UniverseId::projection(3).unwrap();
        let artifact = observer.observe(&root, &layer_id).unwrap();

        assert_eq!(artifact.as_text(), Some(&"test passed: ok".to_string()));
    }

    #[test]
    fn file_system_observer_produces_file_artifact() {
        let mut root = RootSpace::new_artifact_bundle();
        root.meta.inner_mut().insert("file_path".to_string(), "proto/api.proto".to_string());

        let observer = FileSystemObserver::new(ArtifactKind::APISpec);
        let layer_id = UniverseId::projection(2).unwrap();
        let artifact = observer.observe(&root, &layer_id).unwrap();

        assert_eq!(artifact.kind(), Some(ArtifactKind::APISpec));
        assert_eq!(artifact.source(), Some(&"proto/api.proto".to_string()));
    }
}
