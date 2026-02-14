# 自然言語による仕様記述

## 1. 概要

自然言語（Natural Language）は、ソフトウェアおよびシステムの要求仕様を記述する最も広く使われている手段である。形式手法やモデルベース手法が存在するにもかかわらず、産業界では依然として自然言語が仕様記述の主流を占めている。その理由は明確で、全てのステークホルダーが理解でき、特別な訓練を必要としないためである。しかし同時に、自然言語の本質的な曖昧性は仕様品質における最大の課題でもある。

本文書では、自然言語による仕様記述に関する標準規格、曖昧性の問題とその対策、テンプレートおよびパターン、品質基準、そして自然言語処理技術の応用について体系的に整理する。

---

## 2. 標準化団体と規格文書

### 2.1 IEEE 830 と ISO/IEC/IEEE 29148

**IEEE 830-1998**（IEEE Recommended Practice for Software Requirements Specifications）は、ソフトウェア要求仕様書（SRS）の記述に関する長年の標準であった。自然言語による要求記述では "The system shall..." という標準的な構文の使用を推奨し、用語集の作成を通じた一貫した理解を促した。

IEEE 830 は **ISO/IEC/IEEE 29148:2011**（2018年改訂）により後継された。29148 は要求工学のライフサイクルプロセス全体を対象とし、以下を含むより広範な規格となっている：

- ビジネス要求仕様（BRS）
- ステークホルダー要求仕様（StRS）
- システム／ソフトウェア要求仕様（SyRS/SRS）
- 要求の品質基準と管理プロセス

29148 は IEEE 830 より柔軟で、異なるレベルの抽象度・粒度・形式性を許容する。

### 2.2 ISO/IEC 25010（SQuaRE）

**ISO/IEC 25010:2023** は、ソフトウェアの品質要求と評価（SQuaRE）のための品質モデルを定義する。2011年版から2023年版への改訂で、以下の9つの主要品質特性が定められた：

- 機能適合性（Functional Suitability）
- 性能効率性（Performance Efficiency）
- 互換性（Compatibility）
- 相互作用能力（Interaction Capability）
- 信頼性（Reliability）
- セキュリティ（Security）
- 保守性（Maintainability）
- 柔軟性（Flexibility）
- 安全性（Safety）-- 2023年版で追加

この品質モデルは、要求仕様において非機能要求を体系的に記述するための語彙と分類を提供する。

### 2.3 RFC、W3C仕様

RFC（Request for Comments）は、インターネット技術の仕様記述における自然言語使用の代表例である。特に **RFC 2119** は、仕様文書における MUST、SHALL、SHOULD、MAY 等のキーワードの解釈を厳格に定義し、自然言語仕様の曖昧性を軽減する重要な規範を確立した。W3C仕様も同様に、自然言語をベースとしつつ、構造化された文書形式と明確なキーワード定義を併用している。

---

## 3. 要求工学の発展と手法

要求工学（Requirements Engineering, RE）は、ソフトウェア工学の中で要求の発見・分析・文書化・検証を扱う分野として発展してきた。

主要な発展段階は以下の通りである：

1. **1970-80年代**: 構造化分析（DeMarco, Yourdon）による要求の図式化が発展。データフロー図やエンティティ関係図が導入された。
2. **1990年代**: ユースケース（Jacobson）、シナリオベース手法の普及。UMLとの統合が進む。
3. **2000年代**: アジャイル開発におけるユーザーストーリー（"As a [role], I want [feature], so that [benefit]"）の台頭。軽量な自然言語テンプレートが主流に。
4. **2010年代以降**: ゴール指向要求工学（KAOS, i*）、モデルベース要求工学の発展。NLP技術の本格的応用が始まる。

---

## 4. 自然言語仕様の曖昧性問題

### 4.1 曖昧性の分類

自然言語における曖昧性は、要求仕様の品質を損なう最大の要因である。研究において以下の種類が識別されている：

- **語彙的曖昧性（Lexical Ambiguity）**: 単語が複数の意味を持つ場合。例：「bank」が金融機関か川岸かを区別できない。
- **構文的曖昧性（Syntactic Ambiguity）**: 文の文法構造が複数通りに解釈可能な場合。例：「superfluous hair remover」が「不要な毛の除去剤」か「余分な毛除去剤」か。
- **スコープ曖昧性（Scopal Ambiguity）**: 量化子や修飾語のスコープが不明確な場合。例：「すべてのユーザーが2つのレポートを閲覧した」が個別か共通かが曖昧。
- **照応的曖昧性（Anaphoric/Coreferential Ambiguity）**: 代名詞や指示語の参照先が不明確な場合。
- **語用論的曖昧性（Pragmatic Ambiguity）**: 文脈によって解釈が変わる場合。

最近の研究（2024年）では、これらに加えて省略曖昧性（Elliptical）、含意曖昧性（Implicative）、前提曖昧性（Presuppositional）、慣用句曖昧性（Idiomatic）など、11種類の包括的な分類体系が提案されている。

### 4.2 要求工学固有の曖昧性

一般的な言語学的曖昧性に加え、要求工学の文脈では以下の曖昧性が問題となる：

- **不十分な特定（Underspecification）**: 要求が十分に具体化されていない
- **過剰な一般化（Overgeneralization）**: 要求が広すぎて検証不可能
- **暗黙の前提（Implicit Assumptions）**: 記述されていない前提条件の存在
- **矛盾（Contradiction）**: 要求間の不整合

---

## 5. 曖昧性への対策

### 5.1 制限自然言語（Controlled Natural Language）

制限自然言語（CNL）は、自然言語の曖昧性と形式言語の複雑性の間の妥協として提案された手法である。構文と語彙を制限することで、自然言語の可読性を保ちつつ、機械処理可能な精度を実現する。

#### Attempto Controlled English（ACE）

**ACE** は1995年からチューリッヒ大学で開発されている制限英語である。主な特徴：

- 標準英語のサブセットで、制限された構文と意味論を持つ
- Attempto Parsing Engine（APE）により、ACEテキストを談話表現構造（DRS）に一義的に変換可能
- DRSは一階述語論理の変種であり、さらにOWLやSWRLへの変換も可能
- 見た目は完全に自然な英語だが、実質的には英語構文を持つ一階述語論理言語
- ソフトウェア／ハードウェア仕様、データベース整合性制約、法的規制、オントロジー等に応用

### 5.2 EARS（Easy Approach to Requirements Syntax）

**EARS** は2009年にロールス・ロイス航空エンジン部門で開発された、テキスト要求を穏やかに制約するメカニズムである。

EARSは5つの基本テンプレートを提供する：

1. **Ubiquitous（常時）**: "The [system] shall [action]."
2. **Event-driven（イベント駆動）**: "When [trigger], the [system] shall [action]."
3. **State-driven（状態駆動）**: "While [state], the [system] shall [action]."
4. **Unwanted behaviour（望まない動作）**: "If [condition], then the [system] shall [action]."
5. **Optional feature（オプション機能）**: "Where [feature], the [system] shall [action]."

EARSの成功要因は以下の点にある：

- 軽量で導入障壁が低い
- 特別なツールが不要
- 結果として得られる要求が読みやすい
- 曖昧性・複雑性・曖昧さの8つの一般的な要求問題に対処

---

## 6. 仕様書テンプレートとパターン

### 6.1 Volere テンプレート

**Volere Requirements Specification Template** は、James Robertson と Suzanne Robertson により開発された要求仕様のテンプレートである。主な構成：

- **プロジェクトドライバー**: 目的、ステークホルダー、ユーザー
- **プロジェクト制約**: スコープ、命名規則
- **機能要求**: 製品が行うべき処理やルール
- **非機能要求**: 性能、使いやすさ、セキュリティ等の品質特性
- **プロジェクト課題**: オープンイシュー、リスク

Volereの哲学は「要求を書き始めた時点からテストを始める」ことであり、プロセス非依存（アジャイル、ウォーターフォール、アウトソーシング問わず使用可能）である。

### 6.2 IEEE SRSテンプレート

ISO/IEC/IEEE 29148 に基づくSRSテンプレートは以下の構成を推奨する：

1. はじめに（目的、スコープ、定義、参考文献）
2. 全体的な記述（製品の見通し、機能、ユーザー特性、制約、前提）
3. 具体的な要求（機能要求、性能要求、設計制約、品質属性）
4. 検証（各要求の検証方法）

---

## 7. 要求の品質属性と評価基準

### 7.1 IEEE 29148 の品質基準

ISO/IEC/IEEE 29148:2018 は、個々の要求に対して以下の9つの品質属性を規定する：

| 属性 | 定義 |
|------|------|
| **必要性（Necessary）** | 要求が不可欠であること |
| **適切性（Appropriate）** | 要求が適切な抽象度であること |
| **一義性（Unambiguous）** | 唯一の解釈しか持たないこと |
| **完全性（Complete）** | 追加情報なしに能力や制約を定義すること |
| **単一性（Singular）** | 一つの能力・特性・制約・品質要素を述べること |
| **実現可能性（Feasible）** | 技術的に実現可能であること |
| **検証可能性（Verifiable）** | 実現の検証が可能で、測定可能であること |
| **正確性（Correct）** | 記述が正確であること |
| **準拠性（Conforming）** | 標準に従っていること |

### 7.2 要求セット全体の品質

個々の要求に加え、要求セット全体に対しては以下が求められる：

- **完全性**: 全ての必要な要求が含まれている
- **一貫性**: 要求間に矛盾がない
- **追跡可能性（Traceability）**: 要求の出所と実装への追跡が可能
- **手頃さ（Affordability）**: 予算・スケジュール内で実現可能

---

## 8. ドメイン固有言語（DSL）との境界

自然言語仕様とDSLの境界は明確ではなく、連続的なスペクトルとして捉えるべきである。

| 特性 | 自然言語仕様 | 制限自然言語 | DSL |
|------|------------|------------|-----|
| 読み手 | 人間 | 人間＋機械 | 人間＋機械 |
| 形式性 | 非形式 | 半形式 | 形式的 |
| 機械処理 | 困難 | 可能 | 完全に可能 |
| 学習コスト | なし | 低い | 中〜高 |
| 表現力 | 無制限 | 制限あり | ドメイン限定 |
| 曖昧性 | 高い | 低い | なし |

Martin Fowler は DSL を「特定ドメインに焦点を当てた限定的な表現力を持つプログラミング言語」と定義している。DSLとの本質的な差異は、DSLが機械処理可能で形式的に定義されているのに対し、自然言語仕様は非形式的で人間指向であるという点にある。

ただし、制限自然言語（ACEやEARS等）はこの境界を曖昧にし、自然言語の外見を保ちつつDSLに近い形式性を実現している。

---

## 9. 自然言語処理技術の仕様記述への応用

### 9.1 NLP4RE の発展

**NLP for Requirements Engineering（NLP4RE）** は、自然言語処理技術を要求工学に応用する研究分野として確立されている。NLP4RE ワークショップは毎年 REFSQ カンファレンスと共催で開催されている（2025年は4月7日開催予定）。

主要な応用領域：

- **要求分類**: 機能要求・非機能要求の自動分類
- **曖昧性検出**: NLPツールによる曖昧な表現の自動検出（最良のシステムで精度約60%、再現率100%）
- **要求の類似性検索と検索**: 類似要求の発見と重複排除
- **追跡可能性**: 要求と設計・コード・テスト間のトレーサビリティ自動確立
- **欠陥検出**: 不完全性・矛盾・曖昧性の自動検出
- **用語・関係の抽出**: ドメインオントロジーの自動構築

### 9.2 大規模言語モデル（LLM）の応用

2024-2025年における最大の変化は、大規模言語モデル（LLM）と生成AIの要求工学への応用である。LLMは以下の長年の課題を解決する可能性を持つ：

- **追跡可能性の自動確立**: 自然言語で記述された要求と実装の対応付け
- **要求の自動生成・補完**: ステークホルダーとの対話から要求の草案を生成
- **コンプライアンスチェック**: 規制要求への準拠確認
- **曖昧性の検出と修正**: 曖昧な要求の自動検出と修正提案

Springerから2024年に出版された "Handbook on Natural Language Processing for Requirements Engineering" は、この分野の包括的なリファレンスとなっている。

---

## 10. まとめと展望

自然言語による仕様記述は、その普遍性とアクセシビリティにより、今後も仕様記述の主要手段であり続ける。しかし、その固有の曖昧性に対処するため、以下の方向性が重要となる：

1. **段階的な形式化**: 自然言語 → 制限自然言語 → 半形式仕様 → 形式仕様という段階的なアプローチ
2. **テンプレートとパターンの活用**: EARSのような軽量なテンプレートによる品質の底上げ
3. **AIによる支援**: LLMを活用した曖昧性検出・品質チェックの自動化
4. **標準規格の遵守**: IEEE 29148 等の品質基準に基づく体系的な品質管理

自然言語仕様の本質的な課題は、「人間にとっての可読性」と「機械にとっての処理可能性」のバランスにある。制限自然言語やLLM技術の発展は、このバランスを新たな段階へと押し上げつつある。

---

## 参考文献

- IEEE 830-1998: IEEE Recommended Practice for Software Requirements Specifications
- ISO/IEC/IEEE 29148:2018: Systems and software engineering -- Life cycle processes -- Requirements engineering
- ISO/IEC 25010:2023: Systems and software Quality Requirements and Evaluation (SQuaRE)
- RFC 2119: Key words for use in RFCs to Indicate Requirement Levels
- Mavin, A. et al. (2009) "Easy Approach to Requirements Syntax (EARS)", IEEE RE 2009
- Fuchs, N. E. et al. "Attempto Controlled English (ACE)", University of Zurich
- Robertson, S. & Robertson, J. "Volere Requirements Specification Template"
- Zhao, L. et al. (2021) "Natural Language Processing for Requirements Engineering: A Systematic Mapping Study", ACM Computing Surveys
- Berry, D. M. "Ambiguity in Natural Language Requirements Specifications", University of Waterloo
- Springer (2024) "Handbook on Natural Language Processing for Requirements Engineering"
