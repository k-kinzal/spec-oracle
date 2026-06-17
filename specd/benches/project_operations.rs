//! Performance benchmarks for specd project operations
//!
//! Run with: cargo bench --bench project_operations

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use specd::project::ProjectManager;
use specd::storage::{LocalFileBackend, StorageBackend};
use std::path::PathBuf;
use tempfile::TempDir;

fn benchmark_project_create(c: &mut Criterion) {
    c.bench_function("project_create", |b| {
        b.iter(|| {
            let temp_dir = TempDir::new().unwrap();
            let backend = Box::new(LocalFileBackend::new(temp_dir.path().to_path_buf()));
            let mut pm = ProjectManager::new(temp_dir.path().to_path_buf()).unwrap();

            pm.create_project(
                black_box("benchmark-project".to_string()),
                black_box("Benchmark project".to_string()),
                backend,
            )
            .unwrap();
        });
    });
}

fn benchmark_project_switch(c: &mut Criterion) {
    let temp_dir = TempDir::new().unwrap();
    let mut pm = ProjectManager::new(temp_dir.path().to_path_buf()).unwrap();

    // Create multiple projects
    for i in 0..10 {
        let backend = Box::new(LocalFileBackend::new(temp_dir.path().join(format!("project-{}", i))));
        pm.create_project(
            format!("project-{}", i),
            format!("Project {}", i),
            backend,
        )
        .unwrap();
    }

    c.bench_function("project_switch", |b| {
        b.iter(|| {
            for i in 0..10 {
                pm.switch_project(black_box(&format!("project-{}", i))).unwrap();
            }
        });
    });
}

fn benchmark_project_list(c: &mut Criterion) {
    let mut group = c.benchmark_group("project_list");

    for project_count in [10, 50, 100].iter() {
        let temp_dir = TempDir::new().unwrap();
        let mut pm = ProjectManager::new(temp_dir.path().to_path_buf()).unwrap();

        // Create N projects
        for i in 0..*project_count {
            let backend = Box::new(LocalFileBackend::new(temp_dir.path().join(format!("project-{}", i))));
            pm.create_project(
                format!("project-{}", i),
                format!("Project {}", i),
                backend,
            )
            .unwrap();
        }

        group.bench_with_input(
            BenchmarkId::from_parameter(project_count),
            project_count,
            |b, &_count| {
                b.iter(|| {
                    let projects = pm.list_projects();
                    black_box(projects);
                });
            },
        );
    }

    group.finish();
}

fn benchmark_load_project(c: &mut Criterion) {
    let temp_dir = TempDir::new().unwrap();
    let mut pm = ProjectManager::new(temp_dir.path().to_path_buf()).unwrap();

    // Create a project with some data
    let backend = Box::new(LocalFileBackend::new(temp_dir.path().join("load-test")));
    pm.create_project(
        "load-test".to_string(),
        "Load test project".to_string(),
        backend,
    )
    .unwrap();

    c.bench_function("project_load", |b| {
        b.iter(|| {
            let project = pm.load_project(black_box("load-test")).unwrap();
            black_box(project);
        });
    });
}

fn benchmark_save_project(c: &mut Criterion) {
    let temp_dir = TempDir::new().unwrap();
    let mut pm = ProjectManager::new(temp_dir.path().to_path_buf()).unwrap();

    let backend = Box::new(LocalFileBackend::new(temp_dir.path().join("save-test")));
    pm.create_project(
        "save-test".to_string(),
        "Save test project".to_string(),
        backend,
    )
    .unwrap();

    let project = pm.load_project("save-test").unwrap();

    c.bench_function("project_save", |b| {
        b.iter(|| {
            pm.save_project(black_box(&project)).unwrap();
        });
    });
}

criterion_group!(
    benches,
    benchmark_project_create,
    benchmark_project_switch,
    benchmark_project_list,
    benchmark_load_project,
    benchmark_save_project
);

criterion_main!(benches);
