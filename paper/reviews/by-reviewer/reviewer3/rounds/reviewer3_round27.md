Looking at this UAD/f manuscript with the RE practitioner lens (Reviewer #3), I need to evaluate whether it demonstrates **technical re-executability** of the extraction pipeline, not whether it proves general industry applicability.

Let me trace through the scope boundaries carefully:

## VERDICT: OK

## MAJOR:
- none

## MINOR:

1. **§6.2 抽出器正当性の境界記述**: The text states "regex 抽出層は本稿で証明対象ではなく、機械検証済みモデルの前段入力生成層として扱う" but this boundary could be more prominent. Consider adding a callout box or subsection header explicitly titled "抽出器正当性はRQ6対象外" to prevent misreading.

2. **§6.4 負例の実用的含意**: The regex drift example is good but could benefit from one sentence on "実務でこのドリフトをどう検出するか" (e.g., CI stage での pattern 版管理、または抽出失敗率モニタリング). Currently it shows the failure mode but not the operational mitigation pattern.

3. **§7.5 長期保存の運用ガイダンス**: The lock file mechanism is solid, but "長期保存戦略（永続アーカイブ DOI, Wayback など）は運用上の推奨事項として残しており、現時点で制度化していない" in §9.9 could be moved to §7.5 with a concrete example (e.g., "推奨: リポジトリを Zenodo でアーカイブし、DOI を本文に記載"). This helps practitioners understand what "制度化していない" means in practice.

## REQUIRED_CHANGES:
- none

## RISK:

The PoC demonstrates **source-locked re-execution** with explicit scope (n=3, numeric bounds only, extractor correctness assumed). The manuscript correctly positions this as technical feasibility demo rather than industry validation. Mutation testing shows sensitivity rather than claiming bug discovery rates. The fail-fast/graceful/must/may policy separation is mechanized and documented. No fatal gaps for the stated scope.
