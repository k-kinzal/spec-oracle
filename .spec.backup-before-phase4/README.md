# Specification Management

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
