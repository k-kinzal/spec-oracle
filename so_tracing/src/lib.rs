//! Shared OpenTelemetry setup for spec-oracle binaries.
//!
//! The binaries keep their own stable service names (`spec` and
//! `specd`), while the exporter and resource attributes remain
//! environment-driven so local development can point at the shared LGTM stack.

use std::env;

use anyhow::Context as _;
use opentelemetry::global;
use opentelemetry::propagation::{Extractor, Injector, TextMapCompositePropagator};
use opentelemetry::trace::TracerProvider as _;
use opentelemetry::KeyValue;
use opentelemetry_otlp::{Protocol, SpanExporter, WithExportConfig};
use opentelemetry_sdk::propagation::{BaggagePropagator, TraceContextPropagator};
use opentelemetry_sdk::trace::SdkTracerProvider;
use opentelemetry_sdk::Resource;
use sha2::{Digest, Sha256};
use tonic::metadata::{MetadataKey, MetadataMap, MetadataValue};
use tracing_opentelemetry::OpenTelemetrySpanExt;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

const DEFAULT_OTLP_HTTP_ENDPOINT: &str = "http://192.168.10.4:4318";
const DEFAULT_NAMESPACE: &str = "spec-oracle";
const DEFAULT_ENVIRONMENT: &str = "dev";
const SPEC_ORACLE_TELEMETRY_CAPTURE: &str = "SPEC_ORACLE_TELEMETRY_CAPTURE";

/// How much spec-oracle domain data may be attached to telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapturePolicy {
    /// Operational shape only: durations, counts, stages, broad error category.
    Ops,
    /// Improvement diagnostics: parser/error kinds, expected forms, stable hashes.
    Diagnostic,
    /// Full local-development content: raw statements and other content-bearing values.
    Content,
}

impl CapturePolicy {
    pub fn current() -> CapturePolicy {
        match env::var(SPEC_ORACLE_TELEMETRY_CAPTURE) {
            Ok(value) if value.eq_ignore_ascii_case("content") => CapturePolicy::Content,
            Ok(value)
                if value.eq_ignore_ascii_case("diagnostic")
                    || value.eq_ignore_ascii_case("diagnostics")
                    || value.eq_ignore_ascii_case("diag") =>
            {
                CapturePolicy::Diagnostic
            }
            _ => CapturePolicy::Ops,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            CapturePolicy::Ops => "ops",
            CapturePolicy::Diagnostic => "diagnostic",
            CapturePolicy::Content => "content",
        }
    }

    pub fn allows_diagnostic(self) -> bool {
        matches!(self, CapturePolicy::Diagnostic | CapturePolicy::Content)
    }

    pub fn allows_content(self) -> bool {
        matches!(self, CapturePolicy::Content)
    }
}

/// Holds the SDK provider long enough for shutdown to flush pending spans.
pub struct TelemetryGuard {
    tracer_provider: Option<SdkTracerProvider>,
}

impl Drop for TelemetryGuard {
    fn drop(&mut self) {
        if let Some(provider) = self.tracer_provider.take() {
            if let Err(err) = provider.shutdown() {
                eprintln!("warning: failed to shut down OpenTelemetry provider: {err}");
            }
        }
    }
}

/// Initialize tracing and OTLP trace export for one binary.
///
/// `service_name` is used only when `OTEL_SERVICE_NAME` and
/// `OTEL_RESOURCE_ATTRIBUTES=service.name=...` are both absent.
pub fn init(
    service_name: &'static str,
    service_version: &'static str,
) -> anyhow::Result<TelemetryGuard> {
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| {
        EnvFilter::new("info,h2=warn,hyper=warn,tonic=warn,opentelemetry=warn")
    });
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_writer(std::io::stderr)
        .compact();

    if otel_disabled() {
        Registry::default()
            .with(filter)
            .with(fmt_layer)
            .try_init()
            .context("failed to install tracing subscriber")?;
        return Ok(TelemetryGuard {
            tracer_provider: None,
        });
    }

    global::set_text_map_propagator(TextMapCompositePropagator::new(vec![
        Box::new(TraceContextPropagator::new()),
        Box::new(BaggagePropagator::new()),
    ]));

    let span_exporter = span_exporter().context("failed to build OTLP span exporter")?;
    let tracer_provider = SdkTracerProvider::builder()
        .with_resource(resource(service_name, service_version))
        .with_batch_exporter(span_exporter)
        .build();
    let tracer = tracer_provider.tracer(service_name);
    let otel_layer = tracing_opentelemetry::layer().with_tracer(tracer);

    Registry::default()
        .with(filter)
        .with(fmt_layer)
        .with(otel_layer)
        .try_init()
        .context("failed to install tracing subscriber")?;

    Ok(TelemetryGuard {
        tracer_provider: Some(tracer_provider),
    })
}

pub fn capture_policy() -> CapturePolicy {
    CapturePolicy::current()
}

pub fn statement_hash(statement: &str) -> String {
    let digest = Sha256::digest(statement.as_bytes());
    hex_lower(&digest)
}

pub fn record_statement_on_span(span: &tracing::Span, policy: CapturePolicy, statement: &str) {
    if policy.allows_diagnostic() {
        let hash = statement_hash(statement);
        span.record("spec.statement.hash", hash.as_str());
    }
    if policy.allows_content() {
        span.record("spec.statement.text", statement);
    }
}

/// Inject the current tracing span's OpenTelemetry context into tonic metadata.
pub fn inject_context(metadata: &mut MetadataMap) {
    let cx = tracing::Span::current().context();
    global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut MetadataInjector { metadata });
    });
}

/// Extract remote trace context from tonic metadata and make it the current span's parent.
pub fn set_current_span_parent_from_metadata(metadata: &MetadataMap) {
    set_span_parent_from_metadata(&tracing::Span::current(), metadata);
}

/// Extract remote trace context from tonic metadata and make `span` its child.
pub fn set_span_parent_from_metadata(span: &tracing::Span, metadata: &MetadataMap) {
    let parent = global::get_text_map_propagator(|propagator| {
        propagator.extract(&MetadataExtractor { metadata })
    });
    let _ = span.set_parent(parent);
}

fn otel_disabled() -> bool {
    env_bool("OTEL_SDK_DISABLED")
        || env::var("OTEL_TRACES_EXPORTER")
            .map(|value| value.eq_ignore_ascii_case("none"))
            .unwrap_or(false)
}

fn span_exporter() -> Result<SpanExporter, opentelemetry_otlp::ExporterBuildError> {
    let mut builder = SpanExporter::builder()
        .with_http()
        .with_protocol(Protocol::HttpBinary);
    if !env_is_set("OTEL_EXPORTER_OTLP_ENDPOINT")
        && !env_is_set("OTEL_EXPORTER_OTLP_TRACES_ENDPOINT")
    {
        builder = builder.with_endpoint(DEFAULT_OTLP_HTTP_ENDPOINT);
    }
    builder.build()
}

fn resource(service_name: &'static str, service_version: &'static str) -> Resource {
    let mut attributes = Vec::new();
    if !resource_attr_is_set("deployment.environment") {
        attributes.push(KeyValue::new("deployment.environment", DEFAULT_ENVIRONMENT));
    }
    if !resource_attr_is_set("service.namespace") {
        attributes.push(KeyValue::new("service.namespace", DEFAULT_NAMESPACE));
    }
    if !resource_attr_is_set("service.version") {
        attributes.push(KeyValue::new("service.version", service_version));
    }

    let mut builder = Resource::builder().with_attributes(attributes);
    if !service_name_is_set() {
        builder = builder.with_service_name(service_name);
    }
    builder.build()
}

fn service_name_is_set() -> bool {
    env_is_set("OTEL_SERVICE_NAME") || resource_attr_is_set("service.name")
}

fn resource_attr_is_set(key: &str) -> bool {
    env::var("OTEL_RESOURCE_ATTRIBUTES")
        .map(|value| {
            value.split(',').any(|entry| {
                entry
                    .split_once('=')
                    .map(|(entry_key, _)| entry_key.trim() == key)
                    .unwrap_or(false)
            })
        })
        .unwrap_or(false)
}

fn env_bool(key: &str) -> bool {
    env::var(key)
        .map(|value| {
            matches!(
                value.to_ascii_lowercase().as_str(),
                "true" | "1" | "yes" | "on"
            )
        })
        .unwrap_or(false)
}

fn env_is_set(key: &str) -> bool {
    env::var(key)
        .map(|value| !value.trim().is_empty())
        .unwrap_or(false)
}

fn hex_lower(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

struct MetadataInjector<'a> {
    metadata: &'a mut MetadataMap,
}

impl Injector for MetadataInjector<'_> {
    fn set(&mut self, key: &str, value: String) {
        let Ok(key) = MetadataKey::from_bytes(key.as_bytes()) else {
            return;
        };
        let Ok(value) = MetadataValue::try_from(value.as_str()) else {
            return;
        };
        self.metadata.insert(key, value);
    }
}

struct MetadataExtractor<'a> {
    metadata: &'a MetadataMap,
}

impl Extractor for MetadataExtractor<'_> {
    fn get(&self, key: &str) -> Option<&str> {
        self.metadata.get(key).and_then(|value| value.to_str().ok())
    }

    fn keys(&self) -> Vec<&str> {
        Vec::new()
    }
}
