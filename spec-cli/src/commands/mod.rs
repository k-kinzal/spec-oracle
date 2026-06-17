/// Command implementations for the spec CLI (gRPC only)
///
/// All commands communicate with specd via gRPC.
/// There is no standalone mode.

pub mod add;
pub mod check;
pub mod contradictions;
pub mod dispatcher;
pub mod export_dot;
pub mod find;
pub mod layer;
pub mod omissions;
pub mod project;
pub mod query;
pub mod specd_rpc;
pub mod summary;
pub mod trace;
pub mod watch;

pub use dispatcher::dispatch;
