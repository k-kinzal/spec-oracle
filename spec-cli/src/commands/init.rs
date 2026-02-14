/// Initialize project-local specification management
///
/// Creates .spec/ directory structure with:
/// - specs.json (empty specification graph)
/// - README.md (documentation)
/// - scripts/start-specd.sh, stop-specd.sh (server management)
/// - .gitignore (ignore PID/log files)

use spec_core::{Store, FileStore, SpecGraph};
use std::fs;
use std::path::Path;

pub fn execute_init(path: String) -> Result<(), Box<dyn std::error::Error>> {
    let project_root = Path::new(&path);
    let spec_dir = project_root.join(".spec");

    if spec_dir.exists() {
        eprintln!("✗ Error: .spec/ directory already exists");
        eprintln!("  This project is already initialized for specification management");
        return Ok(());
    }

    println!("Initializing specification management in {}", project_root.display());

    // Create .spec directory structure
    fs::create_dir_all(&spec_dir)?;
    fs::create_dir_all(spec_dir.join("scripts"))?;

    // Create empty specs.json with proper SpecGraph structure
    let specs_file = spec_dir.join("specs.json");
    let empty_graph = SpecGraph::new();
    let store = FileStore::new(&specs_file);
    store.save(&empty_graph)?;
    println!("  ✓ Created .spec/specs.json");

    // Create README.md
    create_readme(&spec_dir)?;
    println!("  ✓ Created .spec/README.md");

    // Create server management scripts
    create_start_script(&spec_dir)?;
    println!("  ✓ Created .spec/scripts/start-specd.sh");

    create_stop_script(&spec_dir)?;
    println!("  ✓ Created .spec/scripts/stop-specd.sh");

    // Create .gitignore
    let gitignore = spec_dir.join(".gitignore");
    fs::write(&gitignore, "specd.pid\nspecd.log\n")?;
    println!("  ✓ Created .spec/.gitignore");

    println!("\n✓ Specification management initialized successfully!");
    println!("\nNext steps:");
    println!("  1. Start project-local server: .spec/scripts/start-specd.sh");
    println!("  2. Add specifications: spec add \"Your specification here\"");
    println!("  3. Add .spec/ to Git: git add .spec/");
    println!("\nFor team collaboration:");
    println!("  - Team members clone this repo (includes .spec/)");
    println!("  - Each developer runs: .spec/scripts/start-specd.sh");
    println!("  - Specifications are automatically version-controlled");
    println!("\nSee .spec/README.md for more details.");

    Ok(())
}

fn create_readme(spec_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let readme = spec_dir.join("README.md");
    fs::write(&readme, r#"# Specification Management

This directory contains specifications managed by specORACLE.

## Structure

- `specs.json` - Specification graph storage
- `scripts/` - Project-local specd server scripts

## Usage

### Option 1: Project-Local Server (Recommended for team projects)

Start project-local specification server:
```bash
.spec/scripts/start-specd.sh
```

Use spec commands (they will connect to project-local server):
```bash
spec add "Password must be at least 8 characters"
spec detect-contradictions
```

Stop the server:
```bash
.spec/scripts/stop-specd.sh
```

### Option 2: Direct File Access (Simple, no server needed)

Set environment variable to use this project's specs:
```bash
export SPECD_STORE_PATH="$(pwd)/.spec/specs.json"
specd &  # Start server with project-local storage
```

## Team Workflow

1. Add `.spec/` to Git: `git add .spec/`
2. Team members clone the repository (includes specs)
3. Each developer runs project-local specd
4. Specifications are version-controlled alongside code

## CI/CD Integration

Add to your CI pipeline:
```yaml
- name: Check specifications
  run: |
    export SPECD_STORE_PATH="${PWD}/.spec/specs.json"
    specd &
    sleep 2
    spec detect-contradictions
    spec detect-omissions
```
"#)?;
    Ok(())
}

fn create_start_script(spec_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let start_script = spec_dir.join("scripts/start-specd.sh");
    fs::write(&start_script, r#"#!/bin/bash
# Start project-local specification server

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SPEC_DIR="$PROJECT_ROOT/.spec"
PID_FILE="$SPEC_DIR/specd.pid"
LOG_FILE="$SPEC_DIR/specd.log"

if [ -f "$PID_FILE" ]; then
    PID=$(cat "$PID_FILE")
    if kill -0 "$PID" 2>/dev/null; then
        echo "✗ specd is already running (PID: $PID)"
        exit 1
    fi
    rm "$PID_FILE"
fi

export SPECD_STORE_PATH="$SPEC_DIR/specs.json"

echo "Starting project-local specd..."
echo "  Store: $SPECD_STORE_PATH"
echo "  Log: $LOG_FILE"

specd > "$LOG_FILE" 2>&1 &
echo $! > "$PID_FILE"

sleep 1

if kill -0 $(cat "$PID_FILE") 2>/dev/null; then
    echo "✓ specd started (PID: $(cat "$PID_FILE"))"
else
    echo "✗ Failed to start specd. Check $LOG_FILE"
    rm "$PID_FILE"
    exit 1
fi
"#)?;

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&start_script)?.permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&start_script, perms)?;
    }

    Ok(())
}

fn create_stop_script(spec_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let stop_script = spec_dir.join("scripts/stop-specd.sh");
    fs::write(&stop_script, r#"#!/bin/bash
# Stop project-local specification server

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SPEC_DIR="$PROJECT_ROOT/.spec"
PID_FILE="$SPEC_DIR/specd.pid"

if [ ! -f "$PID_FILE" ]; then
    echo "✗ specd is not running (no PID file)"
    exit 1
fi

PID=$(cat "$PID_FILE")
if ! kill -0 "$PID" 2>/dev/null; then
    echo "✗ specd is not running (stale PID file)"
    rm "$PID_FILE"
    exit 1
fi

echo "Stopping specd (PID: $PID)..."
kill "$PID"
rm "$PID_FILE"

echo "✓ specd stopped"
"#)?;

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&stop_script)?.permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&stop_script, perms)?;
    }

    Ok(())
}
