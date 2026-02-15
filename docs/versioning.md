# Specification Versioning and Update Workflow

## Philosophy: Git-Based Versioning

specORACLE adopts a **Git-based versioning model** rather than implementing explicit version management in the tool itself. This aligns with the "Beyond-DSL" paradigm - leveraging existing tools instead of inventing new mechanisms.

## Rationale

### Why Git-Based?

1. **Already Git-friendly**: Directory-based YAML storage designed for Git
2. **Natural version control**: Git provides proven version history, diffs, and rollback
3. **Team collaboration**: Git handles merges, conflicts, reviews naturally
4. **Audit trail**: Git commits provide "who, when, why" automatically
5. **No new concepts**: Users already understand Git workflows
6. **Minimal implementation**: Leverages existing lifecycle management

### Why NOT Explicit Versioning?

Adding explicit versioning (v1, v2, v3) would require:
- Defining specification identity (what makes specs "the same"?)
- Version numbering scheme
- Version storage model
- Complex update semantics
- UI for version navigation

This contradicts specORACLE's philosophy of simplicity and observation-based extraction.

## Update Workflow

### Scenario: Updating a Requirement

**Original**: "Password must be at least 8 characters"
**Updated**: "Password must be at least 12 characters"

**Steps**:

1. **Find the old specification**:
   ```bash
   spec find "password" --kind constraint --layer 0
   # Output: [U0] [a1b2c3d4] Password must be at least 8 characters
   ```

2. **Deprecate the old specification**:
   ```bash
   spec deprecate a1b2c3d4
   # ✓ Specification [a1b2c3d4] marked as deprecated
   ```

3. **Add the new specification**:
   ```bash
   spec add "Password must be at least 12 characters"
   # ✓ Specification [e5f6g7h8] added successfully
   ```

4. **Commit with meaningful message**:
   ```bash
   git add .spec/nodes/
   git commit -m "Update password length requirement from 8 to 12 chars

   Deprecates: a1b2c3d4
   Supersedes with: e5f6g7h8
   Reason: Security policy update per SEC-2026-01"
   ```

### Viewing Version History

**Use Git**:
```bash
# View change history
git log -- .spec/nodes/a1b2c3d4*.yaml

# Compare versions
git diff HEAD~1 .spec/nodes/

# See who changed what
git blame .spec/nodes/e5f6g7h8*.yaml
```

**Use specORACLE**:
```bash
# Find current active specs
spec api list-nodes --status active --kind constraint

# Find deprecated specs
spec api list-nodes --status deprecated

# Compare content
spec api get-node a1b2c3d4
spec api get-node e5f6g7h8
```

## Lifecycle Status

specORACLE provides three lifecycle states:

### `active` (default)
- Currently valid specification
- Included in all checks
- Default state for new specifications

### `deprecated`
- Being phased out
- Still checked (shows warnings)
- Indicates newer version exists

### `archived`
- Historical reference only
- Excluded from checks
- Kept for audit/history purposes

**Usage**:
```bash
# Mark as deprecated (planning to remove)
spec deprecate <id>

# Archive (keep for history, exclude from checks)
spec archive <id>

# Reactivate (if decision reversed)
spec activate <id>
```

## Best Practices

### 1. Meaningful Commit Messages

When updating specifications, commit messages should explain:
- **What** changed (content diff)
- **Why** it changed (requirement, bug, policy)
- **Which** specs are affected (old ID → new ID)

Example:
```
Update authentication timeout from 30min to 15min

Deprecates: [7a8b9c0d] "Session timeout: 30 minutes"
Supersedes with: [1d2e3f4a] "Session timeout: 15 minutes"

Reason: Compliance with updated security policy SEC-2026-02
Affects: U0 requirement, U2 API spec, U3 implementation
```

### 2. Gradual Deprecation

Don't delete immediately:
```bash
# Phase 1: Deprecate old spec
spec deprecate <old-id>
spec add "new content"
git commit -m "Deprecate old spec, add new version"

# Phase 2: Update implementation to match new spec
# (code changes)
git commit -m "Update implementation per new spec"

# Phase 3: Archive old spec after implementation updated
spec archive <old-id>
git commit -m "Archive old spec (implementation updated)"
```

### 3. Link Related Changes

Use Git commit references:
```bash
git commit -m "Update password policy spec

Related to:
- Implementation: commit abc123 (code update)
- Tests: commit def456 (test update)
- Docs: commit ghi789 (docs update)"
```

### 4. Semantic Search for Updates

Before adding what might be an update:
```bash
# Search for similar specs
spec find "password length"

# Check relationships
spec trace <found-id>

# If updating, deprecate first
spec deprecate <found-id>
spec add "new content"
```

## Advantages

### For Individual Developers
- ✅ Simple workflow (deprecate + add + commit)
- ✅ Full history via Git
- ✅ No complex version concepts
- ✅ Rollback with git revert

### For Teams
- ✅ Merge conflicts rare (separate YAML files)
- ✅ Code review via Git diffs
- ✅ Who/when/why via Git log
- ✅ Branch-based workflows supported

### For Compliance/Audit
- ✅ Complete audit trail (Git log)
- ✅ Immutable history (Git commits)
- ✅ Signed commits (Git GPG)
- ✅ Blame/attribution (Git blame)

## Limitations

### What Git-Based Versioning Does NOT Provide

1. **Automatic version numbering** - No v1, v2, v3 labels
   - Mitigation: Use lifecycle status + Git history

2. **In-tool version navigation** - No `spec history <id>` command
   - Mitigation: Use `git log -- .spec/nodes/<id>*.yaml`

3. **Automatic deprecation detection** - No "this is an update of that"
   - Mitigation: Explicit workflow (deprecate + add + commit message)

4. **Version comparison UI** - No `spec diff v1 v2`
   - Mitigation: Use `git diff <commit1> <commit2> -- .spec/nodes/`

These are **intentional trade-offs** to keep specORACLE simple and Git-centric.

## Future Enhancements (Optional)

If Git-based versioning proves insufficient, possible enhancements:

1. **Metadata-based version links**:
   ```yaml
   metadata:
     supersedes: "a1b2c3d4"
     superseded_by: "e5f6g7h8"
   ```

2. **Version chain visualization**:
   ```bash
   spec version-chain <id>
   # Shows: v1 [abc] → v2 [def] → v3 [ghi] (current)
   ```

3. **Automatic update detection**:
   ```bash
   spec add "Password >= 12 chars"
   # → Found similar spec: "Password >= 8 chars"
   # → Is this an update? (y/n)
   ```

However, these should only be added if the Git-based approach proves inadequate in practice.

## Conclusion

specORACLE's Git-based versioning approach:
- ✅ Leverages proven tools (Git)
- ✅ Minimal implementation complexity
- ✅ Team-friendly workflows
- ✅ Audit-compliant history
- ✅ Aligns with "Beyond-DSL" philosophy

**The absence of explicit versioning is a feature, not a limitation.**
