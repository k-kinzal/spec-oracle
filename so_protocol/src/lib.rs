//! Generated protobuf/gRPC contract for spec-oracle.
//!
//! This crate intentionally contains only generated wire types and tonic stubs.
//! The daemon owns the domain model and any conversions between that model and
//! these protobuf messages; clients depend only on this protocol crate.

/// Generated protobuf messages and the tonic client/service stubs for the
/// `spec_oracle.v1` contract (see `proto/spec_oracle/v1/specification.proto`).
pub mod pb {
    #![allow(clippy::all)]
    tonic::include_proto!("spec_oracle.v1");
}
