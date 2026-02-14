/// Command implementations for the spec CLI
///
/// This module contains all command implementations, organized by functionality.
/// Each command is responsible for implementing a specific user-facing operation.

pub mod add;
pub mod api;
pub mod check;
pub mod contradictions;
pub mod extract;
pub mod find;
pub mod omissions;
pub mod prover;
pub mod query;
pub mod summary;
pub mod trace;
pub mod u0;

pub use add::{execute_add, execute_add_standalone, execute_add_server};
pub use check::{execute_check, execute_check_standalone, execute_check_server};
pub use contradictions::{execute_contradictions_standalone, execute_contradictions_server};
pub use extract::execute_extract_standalone;
pub use find::{execute_find_standalone, execute_find_server};
pub use omissions::{execute_omissions_standalone, execute_omissions_server};
pub use prover::{execute_prove_consistency_standalone, execute_prove_satisfiability_standalone, execute_inspect_model_standalone};
pub use query::{execute_query_standalone, execute_query_server};
pub use summary::execute_summary_standalone;
pub use trace::{execute_trace_standalone, execute_trace_server};
pub use u0::{execute_construct_u0_standalone, execute_cleanup_low_quality_standalone};
