# 仕様の自動推論とAI活用

## 概要

現代のソフトウェアシステムの複雑性は、人間による仕様管理の限界を示唆している。この課題への一つの回答として、**仕様の自動推論**（Specification Inference）と**AI/機械学習の活用**が注目されている。本調査では、実行トレースからの不変条件発見、LLM（大規模言語モデル）による仕様生成・理解、AI支援による形式検証、プログラム合成、そして2020年代半ばの最新研究動向について包括的に調査する。

「人間が仕様を書く」という前提から、「システムから仕様を自動発見・推論し、AIが支援する」というパラダイムへの移行が進みつつある。

## 1. 仕様推論の基礎

### 1.1 仕様推論とは

**仕様推論**は、既存のプログラムコード、実行トレース、テストケース、あるいはドキュメントから、システムの振る舞いを記述する形式仕様を自動的に抽出・推論する技術である。

**動機**:
- 既存のレガシーシステムには形式仕様が存在しないことが多い
- 仕様とコードの乖離（specification drift）が生じやすい
- 人間が書いた仕様には漏れや曖昧性が存在する
- 大規模システムでは全体の振る舞いを人間が把握できない

**アプローチの分類**:
1. **動的推論**（Dynamic Inference）: 実行トレースから不変条件を発見
2. **静的推論**（Static Inference）: ソースコード解析による仕様抽出
3. **仕様マイニング**（Specification Mining）: 大量のコード実例からパターン抽出
4. **ハイブリッド推論**: 動的・静的手法の組み合わせ

### 1.2 不変条件とは

**不変条件**（Invariant）は、プログラムの特定の地点または実行全体を通じて常に成立する性質である。典型的な不変条件には以下がある：

- **ループ不変条件**（Loop Invariant）: ループの各イテレーション前後で成立する条件
- **クラス不変条件**: オブジェクトの公開メソッド実行前後で成立する条件
- **システム不変条件**: システム全体の状態について成立する大域的性質

不変条件は、プログラムの正当性証明、バグ検出、ドキュメント生成、テストケース生成の基盤となる。

## 2. Daikonと動的不変条件推論

### 2.1 Daikonの概要

**Daikon**は、MIT（現在はワシントン大学）のMichael Ernstらによって開発された、動的不変条件推論ツールの代表例である。Daikonは、プログラムの実行トレースを観察し、統計的に正当化される不変条件を報告する。

**動作原理**:
1. プログラムに計装（instrumentation）を施し、変数値を記録
2. 実行トレースを収集（テストケース実行、本番実行など）
3. 事前定義された不変条件テンプレートを適用
4. すべての観測で成立する条件を「可能性の高い不変条件」として報告

### 2.2 Daikonの不変条件テンプレート

Daikonは、以下のような豊富な不変条件テンプレートを持つ：

**単項テンプレート**:
- `x == c` (定数)
- `x > 0` (範囲制約)
- `x ∈ {v1, v2, ...}` (列挙)

**二項関係**:
- `x == y`, `x < y`
- `x == y + c`
- `x == y * c`

**配列・コレクション**:
- `array[i] > 0` (すべての要素が正)
- `array is sorted`
- `array contains no duplicates`

**オブジェクト関係**:
- `x.field == y.field`
- `x.size() == y.size()`

### 2.3 Daikonの応用

Daikonの出力は以下の目的に利用されている：

1. **ドキュメント生成**: 推論された不変条件をコメントやassertとしてコードに追加
2. **テスト生成**: 不変条件を満たすテストケースの生成
3. **バグ検出**: 不変条件違反を検出
4. **コンポーネント統合**: インターフェース互換性の予測
5. **定理証明支援**: 不変条件を定理証明器への入力として利用
6. **データストリーム検証**: ストリーミングデータの妥当性チェック

### 2.4 動的推論の限界

動的推論は観測ベースであるため、以下の限界がある：

- **偽陽性**（False Positive）: 偶然成立したが真の不変条件でない性質を報告
- **不完全性**: 実行されなかったパスの不変条件は発見できない
- **テストカバレッジ依存**: 良質なテストスイートが必要
- **計算コスト**: 大量の実行トレースの収集と解析に時間がかかる

これらの限界を補うため、静的解析との組み合わせや、AIを用いた不変条件の検証・修正が研究されている。

## 3. 仕様マイニング

### 3.1 仕様マイニングとは

**仕様マイニング**（Specification Mining）は、大量のコードリポジトリ、実行トレース、あるいはAPIログから、時相的性質や使用パターンを自動抽出する技術である。

### 3.2 時相仕様のマイニング

実行トレースから**線形時相論理（LTL）**や**有限状態オートマトン（FSA）**を学習する研究が多数存在する。

**NADA（Neural Acceptance-Driven Approach）**:
- 正例を受理し、合成された負例を拒否するようにFSAを探索
- 離散探索空間の連続緩和を利用
- ニューラルネットワークによる誘導探索

**DICE（Adversarial Specification Mining）**:
- テストスイートからLTL仕様をマイニング
- テスト生成により反例を探索し、偽の性質を無効化
- 敵対的学習のアプローチ

### 3.3 APIマイニング

APIの典型的な使用パターンを抽出することで、開発者支援や誤用検出を行う。

**API使用パターンの抽出**:
- 大量のコードリポジトリから関数呼び出しシーケンスを抽出
- メソッドの機能的役割に基づく分類
- 多段階順序マイニング技術の適用

**応用例**:
- コード補完の改善
- API誤用の自動検出
- REST API仕様に基づくプログラム修復（dcFix）

### 3.4 仕様マイニングの課題

- **スケーラビリティ**: 大規模コードベースへの適用
- **ノイズ**: 不正確なコードや特殊ケースの処理
- **汎化**: 特定プロジェクトに固有のパターンと汎用パターンの区別
- **時相論理の複雑性**: 複雑な時相性質の表現と学習

## 4. LLMによる仕様生成・理解

### 4.1 LLMと形式検証の融合

2020年代、**大規模言語モデル（LLM）**の登場により、仕様推論と形式検証の領域は大きな変革を迎えた。ChatGPT、GPT-4、Claude、Gemini等のLLMは、自然言語と形式言語の間のギャップを埋める能力を示している。

### 4.2 GitHub Copilotとコード生成

**GitHub Copilot**は、OpenAIのCodexモデル（GPTベース）を用いたAIペアプログラマーである。

**機能**:
- 自然言語による問題記述からコード生成
- コード説明の生成
- プログラミング言語間の翻訳
- ファイル検証とエージェントモード

**モデル対応**（2026年時点）:
- OpenAI: GPT-5, GPT-5 Mini
- Anthropic: Claude Sonnet
- Google: Gemini

**仕様との関係**:
- リポジトリカスタム命令により、プロジェクト固有のコーディング規約や仕様を指定可能
- コード生成時に有害・不適切なコンテンツや公開コード一致をフィルタリング

**課題**:
- 生成されたコードの正当性保証がない
- セキュリティ脆弱性やバグを含む可能性
- 形式検証との統合が不十分

### 4.3 ループ不変条件のLLM生成

ループ不変条件は形式検証において重要だが、手動で書くのは困難である。LLMを用いた自動生成が活発に研究されている。

**最近の研究成果（2023-2026）**:

**基本的なアプローチ**:
- GPT-3.5やGPT-4は、0-shot設定でループ不変条件を合成可能
- 正しい不変条件を生成するには複数サンプルが必要

**ハイブリッドフレームワーク**:

1. **LLM-SE Framework**:
   - 複数の検証ツールがLLMと協力して有効な不変条件を生成

2. **ACInv Tool**:
   - 静的解析でループの必要情報を抽出
   - LLMへのプロンプトに埋め込み
   - 適切な不変条件を生成

3. **LaM4Inv（LLM and Model checking for loop Invariant inference）**:
   - 生成的AIと形式検証の記号的アプローチを融合
   - ループ不変条件推論に特化

4. **Reasoning-Optimized LLMs with SMT**:
   - OpenAIのO1、O1-mini、O3-miniモデルを使用
   - Z3 SMTソルバーと密結合した生成-検証パイプライン
   - ソルバーの反例を用いた不変条件の反復的改良

**性能**:
- LLMは最大78%の成功率で不変条件を生成
- しかし、不変条件の修復（repair）は16%に留まる

**課題**:
- メモリ操作を含む複雑なプログラムへの対応
- 不変条件の修復能力の向上
- 生成された不変条件の検証と説明

### 4.4 FormalSpecCpp: LLMによる形式仕様データセット

2025年、**FormalSpecCpp**という、LLMによって作成されたC++形式仕様のデータセットが公開された。このデータセットは、LLMの形式仕様生成能力を評価し、今後の研究を促進することを目的としている。

### 4.5 DafnyProとLLM支援検証

**DafnyPro**は、LLMを活用したDafnyプログラムの自動検証システムである（POPL 2026）。

**特徴**:
- DafnyBenchベンチマークで86%の正解証明を達成
- LLMが仕様記述と証明の両方を支援
- 形式検証における実用的なLLM活用の成功例

## 5. ニューラル定理証明

### 5.1 定理証明の自動化

定理証明器（Proof Assistant）は、数学的定理やプログラムの正当性を厳密に証明するツールである。代表的な定理証明器には**Lean、Coq、Isabelle**がある。

従来、定理証明は高度な専門知識を要し、手動で行われていた。しかし、機械学習の進展により、**ニューラル定理証明**（Neural Theorem Proving）が可能になりつつある。

### 5.2 LLMベースの定理証明器

**LLMベースの定理証明器**は、LLMを用いて形式証明を生成・検証・改良し、証明構築を誘導するニューラル・ニューロシンボリックシステムである。

**最新の状況（2025-2026）**:
- miniF2F、ProofNet、LeanWorkbookなどのベンチマークで新たな最先端（SOTA）結果を達成
- Lean、Isabelle、Coq、ドメイン特化型の形式検証パイプライン全体に展開

**技術的革新**:
- 証明アシスタントとの統合
- きめ細かな証明解析
- 大規模な合成データ生成
- 強化学習トレーニングプロトコル
- 証明状態木探索
- ニューロシンボリック協調

### 5.3 最近の手法論的革新

**全証明生成**（Whole-Proof Generation）:
- MA-LoT（2025年3月）、HybridProver（2025年5月）

**補題抽出と再生**（Lemma Extraction and Replay）:
- Strat2Rocq（2025年10月）: LLMが発見した補題を抽出し、記号的証明器のライブラリに追加
- CoqHammerの定理成功率を+13.41%向上

**性能向上**:
- ProofAug: Isabelle上でSubgoal-XLの1/8未満のクエリで+10pp高いパス率を達成（2025年1月）

### 5.4 AlphaProofとIMO問題解決

**AlphaProof**は、Google DeepMindが開発した数学的推論のためのAIシステムである。

**成果（2024-2025）**:
- 2024年国際数学オリンピック（IMO）で銀メダルレベルの性能
- AlphaProofとAlphaGeometry 2で6問中4問を解決
- 2025年にはGemini 'Deep Think'で金メダルレベルに到達

**技術**:
- Lean形式言語で数学的主張を証明するよう自己訓練
- 事前訓練済み言語モデルとAlphaZero強化学習アルゴリズムの結合
- Geminiモデルを微調整して自然言語問題文を形式文に自動翻訳
- 約100万の非形式数学問題を形式数学言語に翻訳し、形式化ライブラリを構築
- AlphaZeroアルゴリズムによる証明探索ネットワークの段階的自己訓練

### 5.5 専門化された定理証明モデル

**2025-2026年の主要モデル**:

**プロプライエタリモデル**:
- GPT-4-mini

**オープンソースモデル**:
- K2-Think
- DeepSeek-V3.1
- Qwen3
- DeepSeek-Prover-V2（Lean特化）
- Goedel-Prover（Lean特化）
- Minilang

これらのモデルは、Lean、Isabelle、Coqの3大証明アシスタント全てで、ニューラルネットワークと形式検証を組み合わせた大きな進歩を示している。

## 6. プログラム合成と仕様

### 6.1 プログラム合成の基礎

**プログラム合成**（Program Synthesis）は、仕様からプログラムを自動的に生成する技術である。仕様が定理を誘導し、その定理の証明からプログラムを抽出する、という古典的なアプローチが存在する。

### 6.2 ニューラルプログラム合成

**ニューラルプログラム合成**は、ニューラルネットワークを用いて入出力例や自然言語記述からプログラムを生成する手法である。

**アプローチ**:
- **ニューラル誘導制約論理プログラミング**: 制約論理プログラミングにニューラルガイダンスを適用
- **ニューラル誘導演繹探索**: 例からのリアルタイムプログラム合成

### 6.3 ハイブリッドニューラル・シンボリックシステム

記号的AIとニューラルAIのいずれも、単独ではプログラム合成を解決できない可能性が高い。両パラダイムは知識の表現と学習において補完的な強みと弱みを持つため、**ハイブリッドシステム**が最も有望な道である。

**ProofNet++**:
- ハイブリッドニューラル・シンボリックアーキテクチャ
- 形式検証を証明生成の訓練と推論パイプラインに緊密に統合
- 自己回帰ニューラル言語モデルの汎化能力と記号的定理証明器の意味的精密性を明示的に組み合わせる

### 6.4 検証済みコード生成

**CLEVER（Curated Benchmark for Formally Verified Code Generation）**:
- 形式検証されたコード生成のためのベンチマーク
- 仕様付きコード生成の評価基準

**Towards Neural Synthesis for SMT-Assisted Proof-Oriented Programming**:
- SMTソルバー支援の証明指向プログラミングへのニューラル合成

**Specify What? Enhancing Neural Specification Synthesis by Symbolic Methods**:
- ニューラル仕様合成を記号的手法で強化

これらの研究は、形式仕様と証明を伴うプログラムを合成するシステムを開発している。機械学習、特にLLMは、形式定理を証明する能力を示しており、形式証明はその正当性を検証できるコンピュータプログラムであるため、定理証明はハルシネーションの余地がない厳密な評価を伴うコード生成の一形態である。

## 7. 自動プログラム修復と仕様修復

### 7.1 自動プログラム修復（APR）

**自動プログラム修復**（Automated Program Repair, APR）は、テストスイートや形式仕様を用いてソフトウェアの欠陥を自動的に修正する技術である。

**手法**:
- 探索ベース（Search-based）
- 制約ベース（Constraint-based）
- テンプレートベース（Template-based）
- 学習駆動（Learning-driven）

### 7.2 仕様誘導修復

形式仕様は強力な正当性基準を提供し、より効果的な自動修復を可能にする。

**Dafnyプログラムの算術エラー修復**:
- LLMを用いた仕様誘導修復
- 形式手法とLLMの組み合わせ（SpringerLink 2026）

**REST API仕様ベースの修復**:
- **dcFix**: REST API仕様に準拠しないコードを検出・自動修復
- 逸脱箇所と未満足仕様を含むプロンプトをLLMに提供し、誤用を自動修復

### 7.3 仕様修復

プログラムだけでなく、仕様自体の自動修復も研究されている。

**自動仕様修復**:
- 誤った仕様を検出し、修正を提案
- ソフトウェアエンジニアが正しい仕様を書く支援

**契約プログラミングにおける自動仕様修復**:
- 事前条件・事後条件の自動修正

**最新の進展（2025-2026）**:
- 検索拡張LLMとSMTソルバーの統合
- パッチ精度の向上とオーバーフィッティングの最小化
- 適応的・文脈認識型修復

## 8. TerraFormerとInfrastructure-as-Code生成

**TerraFormer**（2026年1月）は、Infrastructure-as-Code（IaC）の生成と変更を自動化するシステムである。

**技術**:
- 教師あり微調整（Supervised Fine-Tuning）
- 検証器誘導強化学習（Verifier-Guided Reinforcement Learning）
- 形式検証ツールによるフィードバック（構文、デプロイ可能性、ポリシー準拠）

**性能**:
- ベースLLMに比べて正確性を最大19.60%向上

**意義**:
- 形式検証をLLMの訓練ループに統合した実用例
- インフラ仕様の自動生成と検証の融合

## 9. CadenceのChipStack AIとハードウェア検証

**ChipStack AI Super Agent**（2026年2月発表）は、Cadenceが開発したチップ設計と検証のための生成的AIシステムである。

**アーキテクチャ**:
- **Mental Model**: 真理の根拠となる情報源として機能し、確率的モデルのハルシネーションを防止

**機能**:
- テスト計画生成
- テストコード記述
- シミュレーションまたは形式ツールの実行
- テスト失敗時のログ解析、根本原因の提案、修正の適用、再実行

**性能**:
- 検証時間を最大4倍削減

**意義**:
- ハードウェア検証における実用的なAI活用
- 形式手法とAIの産業レベルでの統合

## 10. 説明可能AI（XAI）と形式検証

### 10.1 XAIの必要性

AIシステム、特にニューラルネットワークはブラックボックスであり、その決定過程を理解するのは困難である。安全重要システムへの適用には、AIの振る舞いを説明し、形式的に検証する必要がある。

### 10.2 形式的決定トレース（FDT）

**Formal Decision Traces（FDT）**は、サイバーレジリエントな説明可能AIのための検証フレームワークである。

**特徴**:
- 制約充足を示す暗号的に証明された証明証明書を提供
- 分散検証、改ざん検出、監査証跡を可能にする
- 高保証環境に適合

### 10.3 検証済み説明可能性

従来の説明手法は**記述的**であり、何が起こったかを説明するが、出力が指定された制約を満たすことを保証しない。

**形式XAIの要件**:
- 明確に定義された問題を扱う
- 説明の正当性の客観的基準に対して評価
- 理論的に検証可能な説明正当性の概念
- 真理値データを用いて評価可能な説明性能の客観的メトリクス

### 10.4 ハイブリッド説明可能性

**3種類の説明可能性の統合**:
- **事前説明可能性**（A priori explainability）
- **アドホック説明可能性**（Ad hoc explainability）
- **事後説明可能性**（Ex post explainability）

これにより、検証を支援しながら、仕様空間をより良く構造化し、機械と人間の両方の説明可能性を提供する。

### 10.5 VerifAI: AI設計・解析ツールキット

**VerifAI**は、AIベースシステムの形式的設計と解析のためのツールキットである（UC Berkeley）。

**機能**:
- AIシステムのシミュレーションベース解析
- 反例生成
- パラメータ合成
- データ拡張

## 11. 強化学習と形式検証

### 11.1 RLの安全性保証

強化学習（RL）エージェントの振る舞いは、環境との相互作用を通じて学習されるため、その安全性を保証することは困難である。形式手法をRLに適用する研究が進展している。

### 11.2 形式仕様によるRL安全性保証

**アプローチ**:
1. **形式仕様言語**: 望ましくない振る舞いを明示的に定義
2. **制御バリア関数**: 安全性仕様の充足を強制

### 11.3 プログラマティックポリシー

ニューラルネットワークではなく、高水準プログラミング言語で表現可能なポリシーを探索する。

**利点**:
- ニューラルネットワークよりも解釈しやすい
- スケーラブルな記号的手法による検証が可能

### 11.4 検証誘導シールディング

**Multi State-Actor（MuStAc）フレームワーク**:
- 状態に応じてRLエージェントの行動数を変化させる
- エージェントを、その状態で形式検証された行動のみに露出

### 11.5 RL検証の課題

- **状態爆発問題**: 極めて大きなまたは連続的な状態空間
- **不透明なポリシー**: データから学習された、抽象化手法を必要とする不透明な関数
- **不十分なデータセット**: 有限データセットでの訓練により、状態空間の重要部分が過小表現

## 12. 最新の研究動向（2024-2026）

### 12.1 形式推論とLLMの融合

CACM（Communications of the ACM）の論文「Formal Reasoning Meets LLMs: Toward AI for Mathematics and Verification」では、LLMと形式手法の統合により以下が可能になると指摘されている：

- オープンな数学問題の解決
- 形式検証のスケール拡大
- 検証可能なソフトウェア・ハードウェアの生成

しかし、LLMは正当性構築（correctness by construction）ではなく確率的手法に基づいているため、より多くの計算とデータで効果が向上する。

### 12.2 VerifAIワークショップ@ICLR'26

2026年のICLR（International Conference on Learning Representations）では、VerifAIワークショップが開催され、AIの検証可能性が重要なテーマとなっている。

### 12.3 設計・検証のための生成AI/LLM（日本）

日本国内でも、半導体設計・検証における生成AI/LLM活用の議論が活発化している（Design and Verification LANDSCAPE 2024）。

**議論の焦点**:
- AI支援による形式検証の効率化
- LLMによる仕様生成と検証の自動化
- ハルシネーション問題への対策

### 12.4 LLMによるコード翻訳と形式合成推論

**LLM-Based Code Translation Needs Formal Compositional Reasoning**（UC Berkeley, 2025）:
- LLMベースのコード翻訳には形式的な合成推論が必要
- 単純な翻訳を超えた、意味保存の保証が課題

### 12.5 AIツールチェーンでのコード仕様・合成・検証

**A Toolchain for AI-Assisted Code Specification, Synthesis, and Verification**:
- AI支援によるコード仕様記述
- プログラム合成
- 形式検証
を統合したツールチェーンの構築

## 13. 課題と今後の展望

### 13.1 現在の課題

1. **ハルシネーション**: LLMが誤った仕様やコードを生成する
2. **検証可能性**: LLM生成物の正当性保証が困難
3. **スケーラビリティ**: 大規模システムへの適用
4. **データ品質**: 訓練データの偏りや不正確性
5. **説明可能性**: AIの決定過程の理解と検証
6. **ツール統合**: 既存の形式手法ツールとの統合
7. **人間とAIの協働**: AIが支援するが、最終判断は人間が行う体制

### 13.2 今後の展望

**短期（2026-2028）**:
- LLMと形式検証ツールの緊密な統合
- ループ不変条件、事前条件、事後条件の自動生成の実用化
- ハードウェア検証へのAI適用の拡大（Cadence等の産業主導）
- 定理証明の自動化レベルの向上

**中期（2028-2032）**:
- 仕様マイニング技術の成熟と産業採用
- AIによる仕様修復・進化の自動化
- 強化学習と形式検証の融合による安全なRLシステム
- 説明可能AIと形式検証の統合による高保証システム

**長期（2032年以降）**:
- 「人間が仕様を書く」から「AIが仕様を発見・管理する」へのパラダイムシフト
- 自律的な仕様推論・検証・修復システムの実現
- 形式手法の民主化（専門知識不要でAIが支援）

### 13.3 哲学的問題

**AIが推論した仕様は「真の仕様」か？**

AIによる仕様推論が高度化すると、以下の哲学的問題が浮上する：

- AIが発見した仕様は、システムの「本質」を捉えているのか、それとも観測された振る舞いの統計的要約に過ぎないのか？
- 人間の意図とAIが推論した仕様が乖離した場合、どちらが正しいのか？
- 完全に自動化された仕様管理は、本当に人間の管理より優れているのか？

これらの問いは、「仕様とは何か」という根本的な問題に帰着する。

## 14. まとめ

仕様の自動推論とAI活用は、形式手法の実用化を大きく前進させる可能性を持つ。Daikonに代表される動的不変条件推論、仕様マイニング、そしてLLMによる仕様生成・ループ不変条件推論、ニューラル定理証明など、多様なアプローチが研究されている。

**主要な成果**:
- Daikonによる動的不変条件推論の確立
- LLMによるループ不変条件生成（最大78%成功率）
- AlphaProofによるIMO銀メダルレベルの定理証明
- DafnyProによる86%正解証明達成
- Cadence ChipStack AIによる実用ハードウェア検証（4倍高速化）
- TerraFormerによるIaC生成の自動化

**今後の方向性**:
- LLMと形式手法のハイブリッド化
- プログラム合成と仕様検証の統合
- 説明可能AIと形式検証の融合
- 強化学習の安全性保証

しかし、AIはまだ完全に人間を置き換えることはできない。「AI支援による仕様推論」が現実的な着地点であり、人間の洞察とAIの計算能力を組み合わせることで、より信頼性の高いソフトウェア開発が可能になるだろう。

仕様の自動推論とAI活用は、「人間が仕様管理を行うのは不可能」という課題への一つの有力な回答であるが、同時に新たな課題（検証可能性、説明可能性、倫理）も提起している。

---

## 参考文献・情報源

### 動的不変条件推論・Daikon
- [The Daikon system for dynamic detection of likely invariants](https://web.eecs.umich.edu/~weimerw/2021-481F/readings/daikon-tool-scp2007.pdf)
- [Daikon: Dynamic Analysis for Inferring Likely Invariants - CMU](http://www.cs.cmu.edu/~aldrich/courses/654-sp05/handouts/daikon.pdf)
- [A Data Driven Approach for Algebraic Loop Invariants](https://saurabhg.web.illinois.edu/pdfs/sharma2013data.pdf)
- [Second-Order Constraints in Dynamic Invariant Inference](https://yanniss.github.io/meta-invariantsFSE13.pdf)
- [DySy: Dynamic Symbolic Execution for Invariant Inference](https://www.microsoft.com/en-us/research/wp-content/uploads/2007/11/tr-2007-151.pdf)
- [Specification Inference for Scala and Stainless](http://www.diva-portal.org/smash/record.jsf?pid=diva2:2016504&dswid=-2172)
- [FormalSpecCpp: A Dataset of C++ Formal Specifications created using LLMs](https://arxiv.org/pdf/2502.15217)

### 仕様マイニング
- [Software Specification Discovery: A New Data Mining Approach](https://userpages.cs.umbc.edu/hillol/NGDM07/abstracts/poster/DLo.pdf)
- [NADA: Neural Acceptance-Driven Approximate Specification Mining](https://dl.acm.org/doi/abs/10.1145/3728956?af=R)
- [Adversarial Specification Mining](https://arxiv.org/abs/2103.15350)
- [Mining API Usage Patterns by Applying Method Categorization to Improve Code Completion](https://www.jstage.jst.go.jp/article/transinf/E97.D/5/E97.D_1069/_article)

### LLMと形式検証
- [TerraFormer: Automated Infrastructure-as-Code with LLMs Fine-Tuned via Policy-Guided Verifier Feedback](https://arxiv.org/html/2601.08734v1)
- [Cadence Unleashes ChipStack AI Super Agent](https://www.cadence.com/en_US/home/company/newsroom/press-releases/pr/2026/cadence-unleashes-chipstack-ai-super-agent-pioneering-a-new.html)
- [設計と検証に関する生成AI / LLM活用の議論](https://www.paltek.co.jp/techblog/techinfo/250513_02)
- [Formal Verification First: How AI Supports But Cannot Replace It](https://semiengineering.com/formal-verification-first-how-ai-supports-but-cannot-replace-it/)
- [DafnyPro: LLM-Assisted Automated Verification for Dafny Programs](https://popl26.sigplan.org/details/dafny-2026-papers/12/DafnyPro-LLM-Assisted-Automated-Verification-for-Dafny-Programs)
- [Formal Reasoning Meets LLMs: Toward AI for Mathematics and Verification](https://cacm.acm.org/research/formal-reasoning-meets-llms-toward-ai-for-mathematics-and-verification/)

### プログラム合成
- [Toward automatic program synthesis - CACM](https://dl.acm.org/doi/10.1145/362566.362568)
- [LLM-Based Code Translation Needs Formal Compositional Reasoning](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2025/EECS-2025-174.pdf)
- [Recent Advances in Neural Program Synthesis](https://arxiv.org/pdf/1802.02353)
- [CLEVER: A Curated Benchmark for Formally Verified Code Generation](https://arxiv.org/pdf/2505.13938)
- [ProofNet++: A Neuro-Symbolic System for Formal Proof Verification with Self-Correction](https://arxiv.org/html/2505.24230v1)
- [Towards Neural Synthesis for SMT-Assisted Proof-Oriented Programming](https://arxiv.org/html/2405.01787)
- [Specify What? Enhancing Neural Specification Synthesis by Symbolic Methods](https://arxiv.org/html/2406.15540)
- [A Toolchain for AI-Assisted Code Specification, Synthesis](https://atlascomputing.org/ai-assisted-fv-toolchain.pdf)

### ループ不変条件生成（LLM）
- [Towards General Loop Invariant Generation: A Benchmark](https://arxiv.org/html/2311.10483v2)
- [LLM Meets Bounded Model Checking: Neuro-symbolic Loop Invariant Inference](https://chentaolue.github.io/pub-papers/ASE24.pdf)
- [Enhancing automated loop invariant generation for complex programs with large language models](https://www.sciencedirect.com/science/article/abs/pii/S0167642325001261)
- [Loop Invariant Generation: A Hybrid Framework of Reasoning optimised LLMs and SMT Solvers](https://arxiv.org/abs/2508.00419)
- [Enhancing Automated Loop Invariant Generation for Complex Programs with Large Language Models](https://arxiv.org/abs/2412.10483)
- [Finding Inductive Loop Invariants using Large Language Models](https://arxiv.org/pdf/2311.07948)
- [Ranking LLM-Generated Loop Invariants for Program Verification](https://arxiv.org/html/2310.09342v3)
- [LLM For Loop Invariant Generation and Fixing: How Far Are We?](https://arxiv.org/abs/2511.06552)

### ニューラル定理証明
- [LLM-Based Theorem Provers - Emergent Mind](https://www.emergentmind.com/topics/llm-based-theorem-provers)
- [Neural Theorem Proving for Verification Conditions](https://arxiv.org/pdf/2601.18944)
- [Neural Theorem Proving: Generating and Structuring Proofs for Formal Verification](https://arxiv.org/html/2504.17017v1)
- [A Survey on Deep Learning for Theorem Proving - GitHub](https://github.com/zhaoyu-li/DL4TP)
- [NeurIPS Tutorial on Machine Learning for Theorem Proving](https://machine-learning-for-theorem-proving.github.io/)
- [Theorem Proving and Machine Learning in the age of LLMs](https://europroofnet.github.io/wg5-edinburgh25/)
- [LEGO-PROVER: NEURAL THEOREM PROVING WITH ...](https://proceedings.iclr.cc/paper_files/paper/2024/file/85dca46374dc0f27b4bb5f265b3d17f0-Paper-Conference.pdf)

### AlphaProof
- [DeepMind hits milestone in solving maths problems](https://www.nature.com/articles/d41586-024-02441-2)
- [ADVANCING MATHEMATICS RESEARCH WITH GENERATIVE AI](https://arxiv.org/html/2511.07420)
- [AI achieves silver-medal standard solving International Mathematical Olympiad problems](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)
- [AI at the International Mathematical Olympiad: AlphaProof](https://www.unite.ai/ai-at-the-international-mathematical-olympiad-how-alphaproof-and-alphageometry-2-achieved-silver-medal-standard/)

### 自動プログラム修復と仕様修復
- [Specification-Guided Repair of Arithmetic Errors in Dafny Programs Using LLMs](https://link.springer.com/chapter/10.1007/978-3-032-10444-1_16)
- [Automated Program Repair - Emergent Mind](https://www.emergentmind.com/topics/automated-program-repair-apr)
- [Automated Code Repair Based on Inferred Specifications - SEI CMU](https://www.sei.cmu.edu/documents/1474/2016_021_001_483599.pdf)
- [Automated Program Repair – CACM](https://cacm.acm.org/research/automated-program-repair/)
- [Automatic Specification Repair in Contract Programming](https://haslab.github.io/SpecRep/pubs/AAbreu23.pdf)
- [Automated Program Repair Based on REST API Specifications Using LLMs](https://arxiv.org/html/2510.25148)
- [Automated Repair of Declarative Software Specifications in the Era of LLMs](https://arxiv.org/abs/2310.12425)

### 説明可能AIと形式検証
- [Formal Decision Traces for Data-Driven Verification](https://www.researchsquare.com/article/rs-8736256/v1)
- [Extracting Specifications Through Verified and Explainable AI](https://link.springer.com/chapter/10.1007/978-3-031-97007-8_2)
- [Verified AI - Berkeley](https://berkeleylearnverify.github.io/VerifiedAIWebsite/)
- [Towards Formal XAI: Formally Approximate Minimal Explanations](https://link.springer.com/chapter/10.1007/978-3-031-30823-9_10)
- [Explainable Verification: Survey, Situations, And New Ideas - SEI CMU](https://www.sei.cmu.edu/documents/5866/survey-explain_CGrLAVz.pdf)
- [Explainable AI needs formal notions of explanation correctness](https://arxiv.org/html/2409.14590v2)
- [VERIFAI: A Toolkit for the Formal Design and Analysis](https://people.eecs.berkeley.edu/~sseshia/pubdir/verifai-cav19.pdf)

### 強化学習と形式検証
- [A Deep Reinforcement Learning Framework with Formal Verification](https://dl.acm.org/doi/10.1145/3577204)
- [FORMAL VERIFICATION OF DEEP REINFORCEMENT LEARNING AGENTS](https://www.prismmodelchecker.org/papers/edoardo-bacci-phd-thesis.pdf)
- [Deep Reinforcement Learning Verification: A Survey](https://dl.acm.org/doi/10.1145/3596444)
- [Formal Specification and Testing for Reinforcement Learning](https://ebjohnsen.org/publication/23-icfp/23-icfp.pdf)
- [Verification-Guided Shielding for Deep RL](https://software.imdea.org/~cesar/papers/corsi24verification.pdf)
- [A formal methods approach to interpretable reinforcement learning](https://www.science.org/doi/10.1126/scirobotics.aay6276)
- [Verifiable and Interpretable RL through Program Synthesis](https://ojs.aaai.org/index.php/AAAI/article/view/5088)
- [Safe Reinforcement Learning via Formal Methods](https://www.researchgate.net/publication/321951041_Safe_Reinforcement_Learning_via_Formal_Methods_Toward_Safe_Control_Through_Proof_and_Learning)

### GitHub Copilot
- [GitHub Copilot · Your AI pair programmer](https://github.com/features/copilot)
- [Adding repository custom instructions for GitHub Copilot](https://docs.github.com/copilot/customizing-copilot/adding-custom-instructions-for-github-copilot)
- [Supported AI models in GitHub Copilot](https://docs.github.com/en/copilot/reference/ai-models/supported-models)
- [Review AI-generated code](https://docs.github.com/en/enterprise-cloud@latest/copilot/tutorials/review-ai-generated-code)

### その他
- [The VerifAI Workshop @ ICLR'26](https://verifai-workshop.github.io/)

---

**調査担当**: researcher-19
**調査日**: 2026年2月
**文字数**: 約5,200字
