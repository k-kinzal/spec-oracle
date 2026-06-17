VERDICT: NG

Q1: NO + "このとき `U0` は理想根の同値定義ではなく、理想根を外から包む root coverage baseline（被覆基準）として位置づける。" (§3.5)
Q2: NO + Although `U*` is separated from `U∧` and `U0`, the active-layer assumptions are stated but the relationship `U* ⊆ U∧` and `U* ⊆ U0On` is not mechanically connected to non-empty active conditions in the manuscript's core theorems.
Q3: YES + "`U0`（join: root 被覆仕様）`U∧`（meet: 同時満足診断）に分離し、同一の型付き部分射影モデルで Lean4 機械検証した。" (§10)
Q4: YES + "must解釈では ... may解釈では ... 運用時は、(i) 基準集合、(ii) 抽出仮定（sound/complete）、(iii) `none` 方針（must/may）をセットで宣言する必要がある。" (§4.7) + Lean: `preimageMay`, `UAndOn_subset_UAndMayOn`, etc.

Blocking issues:
1. Q1 fail: §3.5 states "`U0` は理想根の同値定義ではなく、理想根を外から包む root coverage baseline（被覆基準）として位置づける" but does NOT explicitly say "U0 is NOT the ideal root itself" at the beginning of the manuscript.
2. Q2 fail: While §3.5 gives `U* ⊆ U∧ ⊆ U0` under assumptions, the manuscript does NOT mechanically enforce the "active non-empty" guard for `UStar_subset_U0On_of_nonempty_active`. The theorem exists in Lean but the manuscript does not prominently state "U* relation requires active ≠ ∅" as a core constraint upfront.

Non-blocking suggestions:
- Add explicit early statement: "U0 is a root coverage baseline, NOT the ideal root U* itself."
- Clarify in §3.5 that `UStar_subset_U0On_of_nonempty_active` is the mechanized version tying U* to U0 under non-empty active, not just a textual claim.
