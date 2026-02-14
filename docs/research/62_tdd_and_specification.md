# テスト駆動開発（TDD）と仕様

## 概要

テスト駆動開発（Test-Driven Development: TDD）は、1990年代後半にKent Beckがエクストリームプログラミング（XP）の一部として開発したソフトウェア構築手法である。TDDは「テストを先に書く」という逆説的なアプローチにより、ソフトウェア開発をガイドする。本調査では、TDDと仕様の関係、テストが仕様として機能する側面、その限界、そしてATDD（受入テスト駆動開発）、BDD（振る舞い駆動開発）、SDD（仕様駆動開発）などの派生手法について考察する。

TDDは「テストとしての仕様」（Test as Specification）という思想を体現しているが、同時に仕様記述の手段としての限界も持つ。本調査では、その両面を明らかにする。

## 1. テスト駆動開発（TDD）の基礎

### 1.1 TDDとは

**テスト駆動開発**は、テストを書くことでソフトウェア開発をガイドする手法であり、以下の特徴を持つ：

- テストを実装の前に書く（Test First）
- 小さなサイクルを高速に回す
- リファクタリングによる継続的な設計改善
- 自動テストによる即座のフィードバック

TDDは単なるテスト自動化ではなく、**ユニットテストとリファクタリングを両輪**とした小さいサイクルを回すことで不確実性を制御し、不断の設計進化を可能にする手法である。

### 1.2 Kent Beck

TDDの考案者は**Kent Beck**であり、彼の著書「**Test-Driven Development By Example**」（2003年）は、TDDの原典として広く知られている。日本語版は和田卓人氏の翻訳により2017年に出版された。

Kent Beckは以下の功績で知られる：
- エクストリームプログラミング（XP）の創始者
- TDDの体系化と普及
- JUnitフレームワークの共同開発（Erich Gammaと）
- Smalltalk Best Practice Patternsの著者

### 1.3 Kent BeckのMoney Example

Kent Beckの著書では、TDDの実践を2つの例で説明している：

1. **Money Example**: マルチカレンシー算術演算の実装
2. **xUnit Example**: テストフレームワーク自体の構築

**Money Example**は、Ward Cunninghamから得たアイデアで、通貨の種類（ドル、円等）と金額を扱うシステムを段階的に構築する。この例は、TDDの基本サイクルを学ぶための古典的な教材となっている。

Money Exampleは以下を示す：
- 最も単純なテストから始める（例: `$5 + $5 = $10`）
- テストを通すための最小限の実装
- 段階的な一般化とリファクタリング
- 通貨変換、異なる通貨同士の演算の追加

## 2. Red-Green-Refactorサイクル

### 2.1 TDDの基本サイクル

TDDは「**Red-Green-Refactor**」と呼ばれる3ステップのサイクルを繰り返す：

#### Red（赤）: テストを書き、失敗させる

- これから追加したい機能についてのテストを書く
- テストは必ず失敗する（まだ実装が存在しないため）
- 赤は「失敗」を意味する

**Red段階の意義**:
- モジュール、クラス、関数の契約について考える
- 新しいコードがどのように使われるかを考える
- 設計の初期段階でAPI/インターフェースを検討

#### Green（緑）: テストを通す

- テストをパスするための最小限のコードを可能な限り迅速に書く
- 「最も愚直な実装」でも構わない（例: `return 10;`）
- 緑は「成功」を意味する

**Green段階の意義**:
- まず動くようにする
- 美しさや効率性は後回し
- 素早いフィードバックループ

#### Refactor（リファクタリング）: 整理する

- 機能的に書いたコードを整理する
- テストコードも含めてリファクタリング
- 内部構造を改善するが、外部動作は変更しない

**Refactor段階の意義**:
- コードを美しく、保守しやすくする
- 重複を排除（DRY原則）
- 設計の洗練

### 2.2 TDDマントラ

TDDの実践を端的に表すマントラ：

> "Red/Green/Refactor"

Kent Beck自身による正規のTDD定義（和田卓人氏訳）：
1. 自動化されたテストが失敗したときのみ、新しいコードを書く
2. 重複を除去する

## 3. テストとしての仕様（Test as Specification）

### 3.1 実行可能な仕様

TDDにおけるテストは、以下の側面で**仕様**として機能する：

**実行可能な仕様**（Executable Specification）:
- テストは、システムがどう振る舞うべきかを具体的に記述する
- 自然言語の曖昧性がない
- 実行して確認できる

**生きたドキュメント**（Living Documentation）:
- テストは、コードの意図を明確に示すドキュメントとして機能する
- 伝統的なドキュメントとは異なり、コードベースと常に同期している
- 古くなったり不整合になったりしない

**契約の明示化**:
- メソッドやクラスが何をすべきかを明示
- 入力と期待される出力の関係を定義
- 振る舞いの境界条件を示す

### 3.2 仕様としてのテストの利点

1. **具体性**: 自然言語の仕様よりも具体的で曖昧性がない
2. **検証可能性**: 成功/失敗が明確な二択
3. **自動化**: 人手を介さず継続的に検証可能
4. **即時フィードバック**: 変更が仕様を満たすかすぐ確認できる
5. **リグレッション防止**: 過去の仕様が継続的に満たされることを保証

### 3.3 TDDによる設計フィードバック

**テストを先に書くことの効果**:

**テスト可能性による設計改善**:
- テストを書きやすいコードは、設計の質が高い
- 疎結合（Loose Coupling）
- 明確なインターフェースと契約
- 単一責任原則（SRP）の遵守
- 依存性注入によるコンポーネント分離

**設計レビューとしてのテスト記述**:
- コードが存在する前に設計レビューを行う効果
- APIの使いやすさを早期に確認
- 不要な複雑性の発見

### 3.4 品質第一の哲学

TDDは**品質第一の哲学**（Quality-First Philosophy）を体現している：

- 実装完了後に正当性を検証するのではなく、最初の一行から正当性を組み込む
- バグを後で発見するのではなく、最初から作り込まない
- 「後でテストを書く」ではなく「テストから始める」

## 4. TDDの実践と利点

### 4.1 TDDの利点

**開発効率**:
- 初期開発は15-30%遅くなる可能性があるが、バグが少なく保守が速いため、全体の納期は短縮される
- リファクタリングが安全に行える（テストがセーフティネット）

**コード品質**:
- テストカバレッジが自然に高くなる
- 疎結合・高凝集の設計になりやすい
- インターフェースが明確になる

**保守性**:
- テストがドキュメントとして機能
- 変更の影響範囲を即座に把握できる
- リグレッションを防止

**心理的効果**:
- 小さな成功体験を積み重ねることで開発のリズムが生まれる
- テストが通る瞬間の達成感
- 不安を軽減（「動いている」ことが常に確認できる）

### 4.2 より深い要求理解

テストを先に書くことで、以下の効果がある：

- プロダクト要件のより深く早い理解
- テストコードの有効性の確保
- ソフトウェア品質への継続的な焦点

## 5. ATDD（受入テスト駆動開発）

### 5.1 ATDDとは

**Acceptance Test-Driven Development（ATDD）**は、TDDを受入レベルに拡張した開発手法である。

**特徴**:
- ビジネス顧客、開発者、テスターのコミュニケーションに基づく
- エンドツーエンドの受入基準に焦点
- 自然言語を使用（プログラミング言語ではなく）
- ユーザーの視点（外部視点）からのテスト

### 5.2 ATDDとTDDの違い

| 観点 | TDD | ATDD |
|------|-----|------|
| レベル | ユニット（単体） | システム（受入） |
| 言語 | プログラミング言語 | 自然言語 |
| 視点 | 開発者の内部視点 | ユーザーの外部視点 |
| 対象 | クラス・メソッドの振る舞い | システム全体の振る舞い |

### 5.3 ATDDの利点

**ATDDの大きな転換**:
- コードを書く前に受入テストを事前に仕様化
- すべての関係者が関与することで誤解を回避
- 追加作業をほとんど必要としない

**具体的な効果**:
- 要求の明確化が早期に行われる
- ビジネス側と開発側の認識のずれを防ぐ
- 開発完了の定義（Definition of Done）が明確

## 6. BDD（振る舞い駆動開発）

### 6.1 BDDとATDDの関係

**Behavior-Driven Development（BDD）**とATDDは、実質的に同じ実践である。

**ATDDとBDDの違い**:
- **BDD**: 機能の振る舞いに焦点
- **ATDD**: 正確な要求の捕捉に焦点
- **最大の違い**: テスト仕様の記述フォーマット

両者の意図は同じで、受入基準を議論を通じて分析し、結果を受入テストの形式で書くという実践を指す。

### 6.2 TDD, ATDD, BDDの関係

**階層構造**:
- **BDD/ATDD**: システムレベルの仕様と検証
- **TDD**: ユニットレベルの仕様と検証

**相互補完**:
- TDDは各タスクで使用可能
- BDDはエンドツーエンドチェックで使用
- SDDはその上位に位置し、意図の源泉となる

## 7. SDD（仕様駆動開発）とAI時代の新展開

### 7.1 SDDとは

**Specification-Driven Development（SDD）**は、2026年のAI時代に注目される新しいパラダイムである。

**定義**:
- TDDがテスト先行であるのに対し、SDDは仕様先行
- テストやコードの前に仕様を書く
- より高いレベル（機能、システム、アーキテクチャ）に「仕様先行」の規律を適用

### 7.2 SDDとTDDの関係

**TDDはSDDのユニットレベル版**:
- テストを先に書くことは、期待される振る舞いを実装前に定義するマイクロ仕様を書くこと
- SDDはこの考え方をより広い範囲（機能、システム、アーキテクチャ）に拡張

**階層関係**:
```
SDD（仕様駆動）
  ↓
ATDD/BDD（受入テスト駆動）
  ↓
TDD（ユニットテスト駆動）
```

SDDは「何を」「なぜ」を捉える基盤的な仕様から始まり、TDDとBDDに先行する。

### 7.3 AI開発時代のSDDの優位性

**AIエージェントへの明確なガイド**:
- AIエージェントに確固たるガイドを与え、推測を止めさせる
- AI支援エンジニアリングでは、SDDは仕様をコーディングエージェント用の実行可能な青写真に変換する厳密なフレームワークとして機能
- アドホックな「雰囲気コーディング」（Vibe Coding）の不整合を防止

**意図駆動アプローチ**:
- 開発者の主な役割は、プロセスをステアリングし、出力を検証すること
- AIがコード生成と実装詳細の大部分を処理

### 7.4 2026年のSDDツール

**GitHub Spec-Kit**:
- 2026年、GitHubがSpec-Kitをリリース
- 一般的なコーディングエージェント（Copilot、Claude Code、Gemini CLI等）と連携
- 仕様を中心とした開発フローを実現

### 7.5 SDD vs. Vibe Coding

**Vibe Coding**:
- LLMに自然言語で「こんな感じで」と指示し、生成されたコードをそのまま使う開発スタイル
- 仕様が曖昧で、一貫性に欠ける

**SDDの優位性**:
- 明確で構造化された仕様が、AIの生成品質を向上させる
- 検証可能性と再現性を確保

## 8. テストが仕様として不十分な場面

### 8.1 TDDの限界

TDDは強力な手法だが、仕様記述の手段としては以下の限界がある：

### 8.2 網羅性の課題

**テスト網羅性の問題**:
- TDDで書かれたテストがすべてのケースを網羅できていることは稀
- 抜けは必ず発生する
- 必要な項目が盛り込まれていないと、不具合を見落とす

**人的リソースの限界**:
- 網羅性の高い抜けのないレベルのテストコードを自分でゼロから書ける開発者は少数
- ほとんどの開発現場では揃えられない

**後付けテストの問題**:
- テストを後から書くと、必要なことがテストされず、テストに抜けが生じやすい

### 8.3 カバレッジギャップ

**完全なテストカバレッジは困難**:
- すべての可能なシナリオに対してテストを書くことは困難
- テストスイートにギャップが残る可能性

**大規模・複雑システムへの限界**:
- 外部依存関係と相互作用するシステムのテストには効果が限定的
- エンドツーエンドの複雑な振る舞いは単体テストで捉えきれない

### 8.4 UI・UXのテスト

**UIテストの困難性**:
- TDDはユーザーインターフェースのテストに適していない
- UIは複雑で高度な相互作用を必要とする
- ユーザーの振る舞いと相互作用を正確に捉える自動テストの記述は困難

### 8.5 実装詳細への密結合

**モックの多用による問題**:
- ユニットテストを徹底するためにモックを多用しがちで、テストが実装の詳細に密結合
- リファクタリングが困難になる

**ブラックボックステストの原則違反**:
- TDDのテストはブラックボックス（内部構造に依存しない）であるべき
- しかし、テストがオブジェクトの内部を知りすぎると、外部に影響がない変更でもテストが失敗
- テストがリファクタリングを妨げる原因となる

### 8.6 要求変更への対応

**スコープ調整の影響**:
- 根本的な要求の修正が発生すると、スケジュールに大きな影響を与える
- テストコードも大幅に書き直しが必要

### 8.7 非機能要件

**非機能要件のテストの困難性**:
- パフォーマンス、セキュリティ、スケーラビリティ、可用性などは単体テストで表現しにくい
- システムレベルの性質であり、個別のユニットのテストでは捉えきれない

### 8.8 仕様の「なぜ」

**テストは「何を」しか示さない**:
- テストは、システムが何をすべきか（What）を示すが、なぜそうすべきか（Why）は示さない
- ドメイン知識、ビジネスルール、設計の意図は、テストだけでは伝わらない
- 自然言語や図表によるドキュメントが依然として必要

### 8.9 TDDが幻想となる場面

一部の批判では、TDDが「幻想」となる場面も指摘されている：

- テストを書くこと自体が目的化
- テストの保守コストが過大になる
- テストの粒度が適切でない（細かすぎる/粗すぎる）

## 9. TDDのアンチパターン

### 9.1 よくある失敗パターン

TDD初心者が陥りがちなアンチパターン：

1. **テスト後付け**: 実装後にテストを書く（TDDではない）
2. **過剰なモック**: すべての依存をモック化し、テストが実装に密結合
3. **巨大なテスト**: 1つのテストが多くのことを検証しすぎ
4. **テストの重複**: 同じことを複数のテストで検証
5. **テストの放置**: テストが失敗しても修正せず放置
6. **テストのためだけの設計**: テスト可能性のためだけに不自然な設計

### 9.2 対策

- テストは小さく、明確な1つのことを検証
- モックは必要最小限に
- 実装詳細ではなく、公開インターフェースの振る舞いをテスト
- テストコードも本番コードと同様にリファクタリング
- テストが失敗したら即座に修正

## 10. TDDと形式手法の比較

### 10.1 TDDと形式仕様

| 観点 | TDD | 形式仕様（モデル検査等） |
|------|-----|--------------------------|
| 表現力 | 具体的な例 | 性質の網羅的記述 |
| 検証範囲 | テストケースのみ | 全状態空間 |
| 自動化 | テスト実行は自動 | 検証は自動（反例生成含む） |
| 学習曲線 | 比較的緩やか | 急峻（専門知識必要） |
| 産業適用 | 広範に普及 | 限定的（安全重要システム中心） |

### 10.2 相補的関係

TDDと形式手法は対立するものではなく、相補的である：

- TDDは開発の日常的な実践として広く使える
- 形式手法は、安全性・信頼性が特に重要なコンポーネントに対して適用
- Property-Based Testing（PBT）は、TDDと形式手法の中間的アプローチ

## 11. TDDの哲学と本質

### 11.1 TDDの本質

TDDの本質は、以下の点にある：

1. **フィードバックループの短縮**: 問題をすぐに発見し、修正できる
2. **不確実性の管理**: 小さなステップで確実性を積み重ねる
3. **設計の進化**: リファクタリングによる継続的な改善
4. **品質の作り込み**: 後から品質を検証するのではなく、最初から組み込む

### 11.2 Kent Beckの思想

Kent Beckは、TDDを単なる技術ではなく、**ソフトウェア開発に対する考え方**として提示している：

- 恐怖を勇気に変える（Fear to Courage）
- 不確実性を確実性に変える
- 小さなステップで大きな成果を
- 「動くコード」を常に保つ

### 11.3 TDDとアジャイル

TDDは、アジャイル開発の技術的実践の柱である：

- エクストリームプログラミング（XP）の中核プラクティス
- 継続的インテグレーション（CI）との親和性
- 反復的・漸進的開発を支える

## 12. TDDの現状と未来

### 12.1 2026年の現状

**広範な普及**:
- 多くの開発現場でTDDが実践されている
- 特にアジャイル開発を採用する組織で標準的

**ツールの成熟**:
- JUnit（Java）、pytest（Python）、RSpec（Ruby）、Jest（JavaScript）等、充実したテストフレームワーク
- IDEの統合サポート

**課題**:
- 依然として「テストを後で書く」文化が残る組織も多い
- TDDの真の価値を理解せず、形だけ真似る失敗例

### 12.2 AI時代のTDD

**AIによるテスト生成**:
- GitHub CopilotやChatGPT等のLLMがテストコード生成を支援
- テストケースの候補を自動生成

**SDDとの統合**:
- 仕様駆動開発（SDD）が上位概念として浮上
- TDDはSDDのユニットレベル実践として位置づけられる

**自動化の進展**:
- テスト生成の自動化
- バグ修正の自動化（Automated Program Repair）
- テストからの仕様推論

### 12.3 今後の展望

**継続的な重要性**:
- TDDの基本原則（テスト先行、小さなサイクル、リファクタリング）は今後も有効
- AIが開発を支援する時代でも、品質保証の基盤として不可欠

**進化の方向**:
- AI支援によるテスト生成の高度化
- 形式手法との融合（Property-Based Testing等）
- より高レベルの仕様記述（SDD）との統合

## 13. まとめ

テスト駆動開発（TDD）は、Kent Beckによって体系化された「テストを先に書く」というパラダイムであり、Red-Green-Refactorサイクルを通じてソフトウェアの品質を継続的に保証する。TDDにおけるテストは、単なるバグ検出手段ではなく、**実行可能な仕様**（Executable Specification）として機能し、生きたドキュメント、明確な契約、そして設計フィードバックを提供する。

**TDDの強み**:
- テストが仕様として機能し、コードと常に同期
- 小さなサイクルによる迅速なフィードバック
- リファクタリングを安全に行えるセーフティネット
- 品質を最初から作り込む哲学
- 広範な産業適用と成熟したツール

**TDDの限界**:
- テスト網羅性の保証が困難
- UI/UX、非機能要件のテストには不向き
- 実装詳細への密結合のリスク
- 「なぜ」（Why）を伝えられない
- 学習曲線と初期コスト

**拡張と発展**:
- ATDD: システムレベルの受入テスト
- BDD: 振る舞いに焦点を当てた記述
- SDD: AI時代の仕様駆動開発（TDDの上位概念）

TDDは、仕様記述の完全な代替ではなく、形式仕様や自然言語ドキュメントと相補的な関係にある。2026年のAI時代においては、SDD（仕様駆動開発）がTDDの上位に位置づけられ、AIエージェントに明確な意図を伝える手段として注目されている。しかし、TDDの基本原則—テストファースト、小さなサイクル、リファクタリング—は、今後も開発の日常的実践として重要であり続けるだろう。

TDDは、「動くコードを常に保つ」という実用主義と、「品質を最初から作り込む」という理想主義を両立させた、ソフトウェアエンジニアリングの重要な一里塚である。

---

## 参考文献・情報源

### Kent Beckとテスト駆動開発
- [テスト駆動開発 - Ohmsha](https://shop.ohmsha.co.jp/shopdetail/000000004967/)
- [Amazon.co.jp: テスト駆動開発 : Kent Beck, 和田 卓人](https://www.amazon.co.jp/%E3%83%86%E3%82%B9%E3%83%88%E9%A7%86%E5%8B%95%E9%96%8B%E7%99%BA-Kent-Beck/dp/4274217884)
- [テスト駆動開発 - Martin Fowler's Bliki (ja)](https://bliki-ja.github.io/TestDrivenDevelopment)
- [【翻訳】テスト駆動開発の定義 - t-wadaのブログ](https://t-wada.hatenablog.jp/entry/canon-tdd-by-kent-beck)
- [What is Test-Driven Development (TDD)? | IBM](https://www.ibm.com/think/topics/test-driven-development)
- [私の TDD の理解と Kent Beck による TDD の解説の比較](https://blog.kuniwak.com/entry/2024/03/08/100026)

### Red-Green-Refactor
- [テスト駆動開発の基礎 | Remote TestKit](https://appkitbox.com/knowledge/test/20130115-367512)
- [Red, Green, Refactor | Codecademy](https://www.codecademy.com/article/tdd-red-green-refactor)
- [Test-driven development - Wikipedia](https://en.wikipedia.org/wiki/Test-driven_development)
- [bliki: Test Driven Development - Martin Fowler](https://martinfowler.com/bliki/TestDrivenDevelopment.html)
- [Test-Driven Development: Red, Green, Refactor! | Jamie Ingram](https://ingram.technology/blogs/28-03-2025-TDD-red-green-refactor.html)
- [Red, green, refactor: writing perfect Go, with TDD](https://bitfieldconsulting.com/posts/red-green-refactor)
- [Is the Red-Green-Refactor Cycle of Test-Driven Development Good? | Medium](https://medium.com/news-uk-technology/is-the-red-green-refactor-cycle-of-test-driven-development-good-9e2b1b52d721)

### ATDD・BDD
- [TDD vs BDD vs ATDD : Key Differences | BrowserStack](https://www.browserstack.com/guide/tdd-vs-bdd-vs-atdd)
- [Acceptance Test Driven Development (ATDD) | Agile Alliance](https://agilealliance.org/glossary/atdd/)
- [Key Differences Between TDD, BDD, and ATDD](https://www.testdevlab.com/blog/tdd-bdd-atdd-key-differences)
- [How to Start with ATDD using BDD - PMI](https://www.pmi.org/disciplined-agile/how-to-start-with-acceptance-test-driven-development)
- [Three Agile Testing Methods – TDD, ATDD and BDD](https://agiledataguides.com/wow/agile-data-information-value-stream/agile-data-build/three-agile-testing-methods-tdd-atdd-and-bdd/)
- [Acceptance test-driven development - Wikipedia](https://en.wikipedia.org/wiki/Acceptance_test-driven_development)
- [Acceptance Test Driven Development (ATDD) - Scaled Agile Framework](https://framework.scaledagile.com/blog/glossary_term/acceptance-test-driven-development)

### TDDの限界と課題
- [What is test-driven development (TDD)? The complete guide for 2026](https://monday.com/blog/rnd/test-driven-development-tdd/)
- [Testability-driven development: An improvement to the TDD efficiency](https://www.sciencedirect.com/science/article/abs/pii/S0920548924000461)
- [Introduction to Test Driven Development (TDD)](https://agiledata.org/essays/tdd.html)
- [What Is TDD? Process, Importance, and Limitations - LinkedIn](https://www.linkedin.com/pulse/what-tdd-test-driven-development-process-importance-limitations-9mwhc)
- [Test Driven Development Myths 2026 - ThinkSys](https://thinksys.com/development/test-driven-development-myths/)
- [The Limitations of Test Driven Development (TDD)](https://219design.com/limitations-of-test-driven-development/)
- [Test-Driven Development (TDD): Pros, Cons & Examples - Upwork](https://www.upwork.com/resources/test-driven-development)

### TDDの日本語資料（限界・アンチパターン）
- [テスト駆動開発（TDD）とは？目的やメリット・デメリット、やり方を解説 | SHIFT](https://service.shiftinc.jp/column/4654/)
- [テスト駆動開発（TDD）初心者が陥りがちなアンチパターン6選](https://tracpath.com/works/development/test_driven_development_6_anti_pattern/)
- [テスト駆動開発（TDD）とは？基本サイクルと運用時の注意点を解説！ | Qbook](https://www.qbook.jp/column/713.html)
- [テスト駆動開発（TDD）とは？基本サイクルとメリット・デメリット - VALTES](https://service.valtes.co.jp/s-test/blog/testdrivedevelopment_vol1/)
- [TDDという名の幻想... - Qiita](https://qiita.com/asip2k25/items/a580417c8aeedd248094)
- [失敗しない！TDD導入メリットと注意点 | 株式会社モンテカンポ](https://montecampo.co.jp/7754.html/)
- [テスト駆動開発（TDD）とは？やり方からメリット・デメリットまで解説 | HQW!](https://www.veriserve.co.jp/helloqualityworld/media/20250917001/)

### TDD哲学とドキュメント
- [Test Driven Development: Principles, Practices, & Benefits](https://www.virtuosoqa.com/post/test-driven-development)
- [The Philosophy Behind Test Driven Development(TDD) | Medium](https://medium.com/@saminYasir/the-philosophy-behind-test-driven-development-tdd-9473f683efb2)
- [Test-driven development (TDD) explained - CircleCI](https://circleci.com/blog/test-driven-development-tdd/)
- [Test-Driven Development Tutorial: Definition, Process, and Best Practices | ZetCode](https://zetcode.com/terms-testing/tdd/)
- [What is Test Driven Development (TDD)? Example - Guru99](https://www.guru99.com/test-driven-development.html)
- [Test-Driven Development: The Key to Building Reliable and Scalable Software | Medium](https://medium.com/@hilalfauzan9/test-driven-development-the-key-to-building-reliable-and-scalable-software-f6f355901330)

### Specification-Driven Development (SDD)
- [Spec Driven Development: The Future of Building with AI](https://beam.ai/agentic-insights/spec-driven-development-build-what-you-mean-not-what-you-guess)
- [Beyond TDD: Why Spec-Driven Development is the Next Step - Kinde](https://www.kinde.com/learn/ai-for-software-engineering/best-practice/beyond-tdd-why-spec-driven-development-is-the-next-step/)
- [Spec-Driven Development: From Code to Contract in the Age of AI](https://arxiv.org/html/2602.00180v1)
- [Specification-Driven Development (SDD) - AI First Coding Practice | Medium](https://medium.com/ai-pace/specification-driven-development-sdd-ai-first-coding-practice-e8f4cc3c2fc4)
- [Spec-Driven Development: Designing Before You Code (Again) | Medium](https://medium.com/@dave-patten/spec-driven-development-designing-before-you-code-again-21023ac91180)
- [Spec-driven development - Wikipedia](https://en.wikipedia.org/wiki/Spec-driven_development)
- [Understanding Spec-Driven-Development: Kiro, spec-kit, and Tessl - Martin Fowler](https://martinfowler.com/articles/exploring-gen-ai/sdd-3-tools.html)
- [Spec Driven Development: When Architecture Becomes Executable - InfoQ](https://www.infoq.com/articles/spec-driven-development/)
- [Specification-Driven Development // SDD | Medium](https://evoailabs.medium.com/specification-driven-development-sdd-66a14368f9d6)
- [Spec-Driven Development in 2025: The Complete Guide](https://www.softwareseni.com/spec-driven-development-in-2025-the-complete-guide-to-using-ai-to-write-production-code/)
- [Spec Driven Development vs. Vibe Coding: Which Will Win?](https://lasoft.org/blog/spec-driven-development-vs-ai-development-which-will-win/)

### Money Example（Kent Beck）
- [GitHub - No3x/money-tdd-by-example-kent-beck](https://github.com/No3x/money-tdd-by-example-kent-beck)
- [GitHub - TimHacker/tdd-money: The multi-currency Money TDD example](https://github.com/TimHacker/tdd-money)
- [GitHub - ioannakok/Kent-Beck-TDD](https://github.com/ioannakok/Kent-Beck-TDD)
- [Test-Driven Development By Example | George Aristy](https://georgearisty.dev/posts/test-driven-development-by-example/)
- [Money Example from Kent Beck's TDD by example](https://newbe.dev/money-example-from-kent-beck-s-tdd-by-example)

---

**調査担当**: researcher-19
**調査日**: 2026年2月
**文字数**: 約4,900字
