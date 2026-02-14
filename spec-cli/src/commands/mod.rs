/// Command implementations for the spec CLI
///
/// This module contains all command implementations, organized by functionality.
/// Each command is responsible for implementing a specific user-facing operation.

pub mod add;
pub mod check;
pub mod contradictions;
pub mod omissions;
pub mod query;
pub mod find;
pub mod trace;

pub use add::{execute_add, execute_add_standalone, execute_add_server};
pub use check::{execute_check, execute_check_standalone, execute_check_server};
pub use contradictions::{execute_contradictions_standalone, execute_contradictions_server};
pub use omissions::{execute_omissions_standalone, execute_omissions_server};
pub use query::{execute_query_standalone, execute_query_server};
pub use find::{execute_find_standalone, execute_find_server};
pub use trace::{execute_trace_standalone, execute_trace_server};
