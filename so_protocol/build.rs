//! Compile the `spec_oracle.v1` gRPC/protobuf contract into Rust at build time.
//!
//! Both the daemon (service trait) and the client (stub) are generated so the
//! two sides share one authoritative wire contract —
//! `proto/spec_oracle/v1/specification.proto`.
//! Requires `protoc` on PATH (prost-build invokes it).

fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::configure()
        .build_server(true)
        .build_client(true)
        .compile_protos(&["proto/spec_oracle/v1/specification.proto"], &["proto"])?;
    Ok(())
}
