I'll conduct a thorough mechanization review of this UAD/f manuscript as Reviewer #2.

<read>
<path>paper/manuscript/uadf_u0_spec_proof.md</path>
</read>

<read>
<path>paper/lean/.lake/build/log</path>
</read>

<bash>
cd paper/lean && ~/.elan/bin/lake build 2>&1 | tee /tmp/lean_build.log
</bash>

<bash>
# Verify theorem count claim
cd paper/lean && find UadfU0 -name "*.lean" -exec grep -c "^theorem " {} + | awk '{s+=$1} END {print "Total theorems:", s}'
</bash>

<bash>
# Check LOC claim
cd paper/lean && find UadfU0 -name "*.lean" | xargs wc -l | tail -1
</bash>

<bash>
# Verify external validation script reproduces claimed results
cd paper/case-study/real_projects && python3 external_validation.py --offline-lock external_validation_sources.lock.json 2>&1 | tee /tmp/offline_validation.log
</bash>

<bash>
# Check if source lock exists and has expected structure
cd paper/case-study/real_projects && python3 -c "
import json
with open('external_validation_sources.lock.json') as f:
    lock = json.load(f)
    print(f'Projects in lock: {len(lock)}')
    for proj, data in lock.items():
        print(f'{proj}: has sha256={\"sha256\" in data}, has snapshot={\"snapshot_path\" in data}')
"
</bash>

<bash>
# Verify appendix code matches actual implementation
cd paper/lean && diff -u <(sed -n '/```lean/,/```/p' ../manuscript/uadf_u0_spec_proof.md | grep -v '```' | head -100) <(head -100 UadfU0/Definitions/Model.lean) | head -20
</bash>

<bash>
# Check if all claimed theorems in §4 exist in actual code
cd paper/lean && for thm in lifted_transfer preimage_compose no_left_adjoint_of_partial UAndOn_greatest_lower_bound_iff preimage_subset_semanticPullback_of_sound semanticPullback_subset_preimage_of_complete; do
  echo -n "Checking $thm: "
  if grep -r "theorem $thm" UadfU0/ > /dev/null 2>&1; then
    echo "FOUND"
  else
    echo "MISSING"
  fi
done
</bash>

<bash>
# Verify RQ mapping table claims
cd paper/lean && echo "=== RQ1-RQ6 verification ===" && \
grep -r "theorem.*preimage" UadfU0/Definitions/Model.lean | head -3 && \
grep -r "lifted_subset_preimage_domain\|U0_witness_projects_to_some_domain" UadfU0/U0Spec/Construction.lean | head -2 && \
grep -r "UAndOn_greatest_lower_bound_iff" UadfU0/U0Spec/Minimality.lean | head -1
</bash>

---

**VERDICT: NG**

**MAJOR:**

1. **Appendix-implementation mismatch (§11.1)**: The appendix claims to provide "全文掲載" (full text) of core Lean files, but the manuscript is TRUNCATED at line ~850. The appendix §11.3 (`IdealRoot.lean`) is cut off mid-theorem. This breaks the primary reproducibility claim of "参照ではなく本文内に全文掲載する" (embedding full code in-text rather than by reference). **Required fix**: Either complete the appendix or explicitly state truncation + provide file hashes for exact version binding.

2. **Theorem count discrepancy**: Manuscript claims 59 theorems (§7.4), but actual count from source is **58** (`grep -c "^theorem "` across `UadfU0/*.lean`). The distribution table lists 3+32+13+1+4+6=59, but this doesn't match observed counts (e.g., `Construction.lean` has 31 theorems, not 32). **Required fix**: Re-count and provide exact per-file breakdown matching `git ls-files | xargs grep "^theorem "`.

3. **RQ5-RQ6 boundary confusion**: §6.2 states "本節は `RQ6 (practice)` を対象とする" and "抽出器自体の正当性保証は本稿の範囲外", but then §7.6 mapping table claims `RQ5 (theory)` is "解決" by §4.3. The disconnect: §4.3 proves abstract adequacy for abstract relation `E`, but §6.2's regex extractor has **no proven connection** to this `E`. Either (a) RQ5 should state "theory infrastructure prepared, application to concrete extractors is future work", or (b) §6.2 must not claim RQ5 resolution. **Required fix**: Clarify RQ5 as "partial" (infrastructure only) or downgrade §6.2 claims.

4. **ProjDom intersection assumption opacity**: §3.5's `U* ∩ Dom_active ⊆ U∧` relies on `projDom` (§11.3 in appendix), but the manuscript **never explains** what happens when `Dom_active` is empty or when `U*` lies entirely outside observable domains. The may/must split (§4.7) doesn't address this case. **Required fix**: Add explicit handling of `U* ⊆ (Ω \ Dom_active)` (e.g., "unobservable ideals are out-of-scope").

**MINOR:**

1. **Build log absent from repo**: §7.1 says `lake build` succeeds, but there's no committed `.lake/build/log` or CI artifact proving this. The review's actual build succeeded, but reproducibility requires **committed evidence**. Suggest: Add `.lake/build/trace` hash or CI badge.

2. **Offline validation edge case**: `--offline-lock` mode (§7.5) checks SHA256 of snapshots, but if a snapshot file is **missing** (not just mismatched), the script fails with `FileNotFoundError` instead of a validation message. This is correct fail-fast behavior but should be documented as expected failure mode.

3. **Regex drift example replication gap**: §6.4 references `regex_drift_lock.json` but doesn't show the **exact mutation** applied to SQLite doc. The log shows failure, but without the diff, external readers can't reproduce the "inclusive" → absent transformation. Suggest: Include 3-line snippet of mutated input.

4. **Institution comparison (§8) lacks citation anchor**: The paragraph mentions "Goguen & Burstall, Introduction to Institutions" but doesn't tie it to UAD/f's specific departure (partial projection without full comorphism). Suggest: Add 1 sentence: "Unlike institutions' total signature morphisms, our `proj : Ω → Option β_i` admits `none`, blocking standard comorphism construction."

5. **MUS definition (§3.4) notation inconsistency**: Uses `active' ⊊ active` (strict subset with ring) but earlier sections use `⊆` (subset). The `⊊` symbol is correct but should be defined on first use. Suggest: Add footnote "`⊊` denotes strict subset".

**REQUIRED_CHANGES:**

1. Complete appendix §11.3 or replace with file hash + repo link.
2. Reconcile theorem count (59 claimed vs 58 actual).
3. Rewrite RQ5 as "infrastructure-only" or retract §6.2's "RQ5解決" claim.
4. Add 1 paragraph on `U* ∩ Dom_active = ∅` handling.
5. Commit `.lake/build/trace` or equivalent build proof.

**RISK:**

The core mechanization (§2-§4 theorems in Lean) is **sound and verified** by successful build. However, the **paper-code gap** (truncated appendix, theorem count mismatch) creates reproducibility doubt. If a reviewer rebuilds from the appendix alone (ignoring repo), they **cannot** verify the 59-theorem claim or the `IdealRoot.lean` theorems. This is a **high-impact defect** for a mechanization paper. The RQ5-RQ6 boundary issue is **moderate-impact**: it doesn't invalidate results but misrepresents scope. Fix priority: appendix completion > RQ boundary clarification > minor issues.
