/// Integration test for projection layer (following plan specification)
///
/// Tests the complete projection composition: proj_i = obs_i >> extract_i

use spec_core::formal::projection::{
    RootSpace, ArtifactSpace, ArtifactKind,
    Observer, ArtifactBundleObserver,
    Projection, Extractor,
};
use spec_core::formal::universe::UniverseId;
use spec_core::InferredSpecification;

/// Simple test extractor that extracts lines as specs
struct LineExtractor;

impl Extractor<String> for LineExtractor {
    fn extract(&self, artifact: &ArtifactSpace) -> Vec<String> {
        match artifact.as_text() {
            Some(text) => text.lines().map(|s| s.to_string()).collect(),
            None => Vec::new(),
        }
    }
}

#[test]
fn test_projection_composition() {
    // Create artifact bundle root using metadata-based design
    let mut root = RootSpace::new_artifact_bundle();

    // Add artifact content to metadata
    root.meta.inner_mut().insert(
        "content_value".to_string(),
        "line1\nline2\nline3".to_string(),
    );
    root.meta.inner_mut().insert(
        "source".to_string(),
        "test.txt".to_string(),
    );

    // Create observer
    let observer = ArtifactBundleObserver::new(ArtifactKind::SourceCode);

    // Create extractor
    let extractor = LineExtractor;

    // Create projection composition
    let layer_id = UniverseId::projection(3).unwrap();
    let projection = Projection::new(observer, extractor, layer_id);

    // Execute: obs >> extract
    let result: Vec<String> = projection.project(&root);

    // Verify composition worked
    assert_eq!(result.len(), 3);
    assert_eq!(result[0], "line1");
    assert_eq!(result[1], "line2");
    assert_eq!(result[2], "line3");
}

#[test]
fn test_projection_with_none_observer() {
    // Create trace root (wrong kind for ArtifactBundleObserver)
    let root = RootSpace::new_trace();

    // Create observer expecting artifact bundle
    let observer = ArtifactBundleObserver::new(ArtifactKind::SourceCode);
    let extractor = LineExtractor;

    let layer_id = UniverseId::projection(3).unwrap();
    let projection = Projection::new(observer, extractor, layer_id);

    // Execute - should return empty Vec because observer returns None
    let result: Vec<String> = projection.project(&root);
    assert!(result.is_empty());
}

#[test]
fn test_observer_returns_artifact_space() {
    let mut root = RootSpace::new_artifact_bundle();

    root.meta.inner_mut().insert(
        "content_value".to_string(),
        "test content".to_string(),
    );

    let observer = ArtifactBundleObserver::new(ArtifactKind::SourceCode);
    let layer_id = UniverseId::projection(3).unwrap();

    // Call observer directly
    let artifact = observer.observe(&root, &layer_id);

    assert!(artifact.is_some());
    let artifact = artifact.unwrap();
    assert_eq!(artifact.kind(), Some(ArtifactKind::SourceCode));
    assert_eq!(artifact.as_text(), Some(&"test content".to_string()));
}
