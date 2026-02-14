/// Command implementations for the spec CLI
///
/// This module contains all command implementations, organized by functionality.
/// Each command is responsible for implementing a specific user-facing operation.

pub mod add;
pub mod check;

pub use add::{execute_add, execute_add_standalone, execute_add_server};
pub use check::{execute_check, execute_check_standalone, execute_check_server};
