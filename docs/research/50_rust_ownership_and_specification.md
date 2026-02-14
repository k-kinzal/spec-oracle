# Rust所有権モデルと仕様の関係

## 調査目的

本調査では、Rustの所有権モデル（Ownership Model）と仕様の関係について調査する。所有権・借用・ライフタイムによる安全性保証、アフィン型としての所有権、borrow checkerによる仕様検証、unsafe Rustとの境界、RustBelt（形式的検証）、Prusti/Creusot等の検証ツール、Rustの型システムが暗黙的に表現する仕様、仕様言語としてのRust型システムについて詳述する。

## 1. Rustの所有権モデルの基礎

### 1.1 所有権システムの概要

**基本原則**：
Rustの所有権システムは、以下の3つのルールから構成される：

1. **所有権（Ownership）**：各値はただ1つの所有者を持つ
2. **借用（Borrowing）**：値への参照を作成できるが、所有権は移動しない
3. **ライフタイム（Lifetimes）**：借用の有効期間を管理する

**目的**：
- コンパイル時にメモリ安全性を保証
- ガベージコレクション不要
- データ競合の排除

### 1.2 所有権による安全性保証

**コンパイル時保証**：
Rustの堅牢な型システムと革新的な所有権モデルは、コンパイル時のメモリ安全性を保証し、null pointer、use-after-free脆弱性、データ競合などの一般的でコストのかかるエラーのクラス全体を排除する。

**形式化された保証**：
Rustの設計は、所有権、借用、ライフタイムのような概念を通じてコンパイル時に安全性を強制する。コンパイラは、プログラムが実行される前にこれらのルールを検査し、メモリリーク、ダングリングポインタ、データ競合を防止する。

### 1.3 所有権の意味論的基盤

**メモリ安全性の源泉**：
メモリ安全性は、厳密には借用検査から来るのではなく、型がアフィン型（affine types）であることから来る。

**所有権の本質**：
Rustのほとんどの型はアフィン型であり、値は最大で1回しか使用できない（ただし、使用せずにdropすることも可能）。使用するとは移動すること、使用しないとはdropすること。これが所有権の意味である。

## 2. アフィン型と線形型

### 2.1 アフィン型の定義

**アフィン型（Affine Types）**：
値が最大で1回使用される可能性がある（ただし、使用せずにdropされる場合もある）型。

**Rustにおける実装**：
Rustのほとんどの型はアフィン型である。これはアフィンリソース追跡の核心である。

### 2.2 線形型との比較

**線形型（Linear Types）**：
値が正確に1回使用されなければならない型。

**Rustの現状**：
Rustは現在、アフィン型を持つが、弱化（weakening）できない型、すなわち少なくとも1回は使用されなければならない型を持っていない。純粋な線形型への関心は高いが、まだ完全にはサポートされていない。

### 2.3 借用とアフィン性の関係

**借用の役割**：
借用の核心的アイデアは、ある区切られた時間の間、線形/アフィン型のルールを一時停止することである。これは領域ベースのメモリ管理と線形/アフィン型の組み合わせのようなものである。

**実用的効果**：
借用により、値を一時的に共有または変更可能にしつつ、所有権の不変性を保持できる。

## 3. 借用検査器（Borrow Checker）

### 3.1 借用検査器の役割

**目的**：
借用検査器は、借用された参照がそれらが指すデータより長生きしないことを保証するルールを強制する。これはアフィン保証にとって重要である。

**実装**：
Rustコンパイラが実行するフロー依存解析によって、所有権不変性を強制する。

### 3.2 型検査との関係

**2段階プロセス**：
より形式的には、Rustの型検査は2段階プロセスとして見ることができる：
1. 第1段階：伝統的な型検査器がフロー非依存的に動作
2. 第2段階：借用検査器がフロー依存解析を使用して所有権不変性を強制

**補完的役割**：
型システムとborrow checkerは互いに補完し合い、包括的な安全性保証を提供する。

### 3.3 借用パターンの制限

**一般的な制限**：
- ループ内での再借用（reborrowing）
- 可変借用のペアなど、借用を含むデータ構造
- ネストした借用

**ツールごとの対応**：
これらのパターンは、検証ツール（Prusti、Creusotなど）によって異なるレベルでサポートされる。

## 4. ライフタイムと仕様

### 4.1 ライフタイムの基本概念

**定義**：
ライフタイムは、参照が有効である期間を示す型システムの構成要素。

**暗黙的vs明示的**：
ほとんどの場合、ライフタイムは暗黙的で推論される（型が推論されるのと同様）。しかし、参照のライフタイムがいくつかの異なる方法で関連付けられる可能性がある場合、Rustはジェネリックライフタイムパラメータを使用して関係を注釈することを要求する。

### 4.2 ライフタイム注釈as契約

**契約としてのライフタイム**：
ライフタイム注釈は、関数のシグネチャの型と同様に、関数の契約の一部となる。関数シグネチャにライフタイム契約を含めることで、Rustコンパイラが行う解析がよりシンプルになる。

**制約の指定**：
関数シグネチャでライフタイムパラメータを指定する際、渡された値や返された値のライフタイムを変更しているのではなく、借用検査器がこれらの制約に従わない値を拒否すべきことを指定している。

### 4.3 ライフタイム省略（Lifetime Elision）

**省略規則**：
Rustは特定のパターンに対してライフタイム注釈を省略可能にする規則を持つ。

**利点**：
- コードの簡潔性向上
- 共通パターンでの煩雑さの軽減
- 型推論と同様の利便性

## 5. Rustの型システムが表現する暗黙的仕様

### 5.1 型as仕様

**型による制約**：
Rustの型システムは、以下の性質を暗黙的に仕様化する：
- メモリ安全性（null安全、use-after-free防止）
- スレッド安全性（データ競合防止）
- リソース管理（リソースリークの防止）

**型の意味論的内容**：
各型は、その値が満たすべき不変条件を暗黙的にエンコードする。

### 5.2 trait systemによる仕様

**trait as インターフェース仕様**：
traitは、型が実装すべき振る舞いの仕様を定義する。

**主要なtrait**：
- `Send`：スレッド間で転送可能
- `Sync`：スレッド間で共有可能
- `Copy`：ビット単位のコピーが安全
- `Drop`：値が破棄される際のカスタム処理

**マーカートrait**：
`Send`や`Sync`のようなマーカーtraitは、コンパイラが自動的に安全性チェックを行うための契約を表現する。

### 5.3 不変条件の静的強制

**コンパイル時検証**：
Rustの型システムは、以下の不変条件をコンパイル時に強制する：
- 参照の別名規則（aliasing rules）
- 可変性制約（mutability constraints）
- 所有権の一意性（uniqueness of ownership）

**実行時オーバーヘッドゼロ**：
これらの保証はコンパイル時に検証されるため、実行時のパフォーマンスペナルティがない。

## 6. unsafe Rustと仕様の境界

### 6.1 unsafe の役割

**必要性**：
ハードウェアの低レベル操作、FFI（Foreign Function Interface）、パフォーマンス最適化などでは、安全性保証を一時的に緩める必要がある。

**unsafe ブロック**：
`unsafe`キーワードにより、以下の操作が可能になる：
- 生ポインタのデリファレンス
- unsafe 関数の呼び出し
- 可変静的変数へのアクセス
- unsafe traitの実装

### 6.2 安全性のカプセル化

**カプセル化の原則**：
unsafeコードを内部で使用する任意のライブラリに対して、検証はその実装がインターフェースの意味論的解釈に関連付けられた述語を満たすことを確立しなければならない。これにより、unsafeコードがライブラリのAPIによって安全に「カプセル化」されていることが確立される。

**sound な境界**：
unsafeコードは、その外部インターフェースが安全である限り、内部で何を行っても良い。これが「sound な抽象化」の概念である。

### 6.3 unsafeコードの検証課題

**非局所性の問題**：
健全性について推論することは微妙で誤りやすい。なぜなら、遠く離れた場所にあるsafeコードとunsafeコードがしばしば相互依存しているからである。安全性は非局所的である：unsafe操作の健全性は、それ以外は「safe」な操作によって確立された状態に必然的に依存する。

**文書化の困難さ**：
unsafe APIの安全性プロパティの注釈は、安全性カプセル化の健全性を検証する上で重要な役割を果たすが、unsafe関数の安全性プロパティをどのように文書化するかについての実用的なガイダンスはほとんどない。

### 6.4 Rust Safety Standard

**提案**：
2023年にRust Safety Standardのpre-RFCが提案され、unsafeコードの正しさに関する条件についてのガイダンスを提供しようとしている。

**現在の方針**：
unsafeコードは、そのクレートの直接の依存関係が正しいと仮定して良いとされているが、これによりsafeプログラムが未定義動作を引き起こすことを許容している。

## 7. RustBelt: 形式的検証の基盤

### 7.1 RustBeltの概要

**目的**：
RustBeltは、Rustの現実的なサブセットを表す言語の最初の形式的（かつ機械検査された）安全性証明である。

**拡張可能性**：
証明は拡張可能であり、unsafeな機能を使用する各新しいRustライブラリについて、言語に対する安全な拡張とみなされるために満たすべき検証条件を指定できる。

### 7.2 Iris: 高階並行分離論理

**秘密兵器**：
RustBeltを可能にする「秘密兵器」は、Coqにおける高階並行分離論理のためのIrisフレームワークである。

**Irisの特徴**：
- 言語に依存しないフレームワーク
- ユーザー定義論理状態（user-defined logical state）
- ゴーストステート（ghost state）のサポート
- 所有権推論の組み込みサポート（分離論理として）

### 7.3 RustBeltの技術的貢献

**基本的アイデア**：
- 不変性（invariance）
- ユーザー定義論理状態/ゴーストステート

**意味論的型付け**：
Rustの型をIrisを使用して表現することの利点は、所有権のような概念が基礎となるフレームワークに既に組み込まれていることである。

### 7.4 RustBeltの適用範囲

**検証済みライブラリ**：
Rustエコシステム全体で使用される最も重要なライブラリのいくつかに対して検証が実施されている。

**プロジェクトの状態**：
ERC資金提供のRustBeltプロジェクトは2021年4月に正式に終了したが、プロジェクトは精神的に継続している。

## 8. 検証ツール: Prusti と Creusot

### 8.1 Prustiの概要

**目的**：
Prustiは、非常に控えめな注釈オーバーヘッドでRustプログラムの豊富な正しさプロパティを検証できる検証器である。

**アプローチ**：
- 分離論理を使用
- 基礎となる論理はViperのImplicit Dynamic Framesの方言

**許可システム**：
Prustiの許可システムはRustの一般的な借用パターンをサポートするが、以下のようなパターンに苦労する：
- ループ内での再借用
- 可変借用のペアのようなデータ構造
- ネストした借用

### 8.2 Creusotの概要

**目的**：
Creusotは、Rustコードの形式仕様と演繹的検証のためのツールである。

**アプローチ**：
- 予言（prophecy）モデルを使用
- 可変借用のための予言を使用したRust型の変換は一般的かつ合成的
- 可変借用の使用や型内での位置に制限を置かない

**実装**：
- Rustコンパイラの拡張として実装
- 標準的なRustワークフローに容易に統合
- 検証標準ライブラリを含めて合計14k行のコード
- LGPLライセンスで公開

### 8.3 PrustiとCreusotの比較

**アプローチの違い**：
- **Prusti**：分離論理とImplicit Dynamic Frames
- **Creusot**：予言モデル

**借用の扱い**：
- **Prusti**：一般的な借用パターンをサポートするが、複雑なパターンに制限
- **Creusot**：可変借用の使用に制限を置かない一般的な変換

**統合**：
両ツールとも、Rustの開発ワークフローへの統合を目指している。

### 8.4 その他の検証ツール

**Gillian-Rust**：
safeRustの自動検証とunsafeRustのターゲットを絞った半自動検証を組み合わせた、分離論理ベースのハイブリッド検証ツール。

**Aeneas**：
Rustの中間表現をCoq、Lean、F*、HOL4に変換し、Rustプログラムの対話的定理証明を可能にする。

**RUDRA**：
エコシステムスケールでRustのメモリ安全性バグを発見するツール。

## 9. 安全性重要システムでのRust（2025-2026）

### 9.1 認証への道

**現状（2025年）**：
FLS（Ferrocene Language Specification）チームがRustプロジェクトの下に2025年に創設され、現在仕様を積極的にメンテナンスし、変更をレビューし、FLSを言語進化と同期させている。

**認証の要件**：
Rustの所有権と型システムはコンパイル時に脆弱性のクラス全体を排除するが、認証は未定義動作の不在以上のものを要求する。

### 9.2 2026年の予測

**ツールチェーンの安定化**：
2026年までに、ベンダーはDO-178C、ISO 26262、IEC 61508、EN 50716の下で適格化に適した安定化されたRustツールチェーンを提供する見込みである。

**適格化キット**：
早期の適格化キットは以下をカバーする：
- コンパイラ構成
- ビルドシステムワークフロー
- パッケージマネージャの制限
- コーディング標準の強制
- カバレッジ解析ツール

### 9.3 産業での採用

**成長の勢い**：
安全性重要ドメインにおけるRustの勢いは2026年を通じて成長し続けると予想され、採用は生産レベルのサブシステムに拡大する。

**重要インフラストラクチャ**：
Rustは重要インフラストラクチャにおけるメモリ安全性とパフォーマンスのための言語として位置付けられている。

## 10. AWS Rust Standard Library検証プロジェクト

### 10.1 プロジェクトの目的

**動機**：
Rust標準ライブラリの安全性を検証し、unsafeコードの正しさを形式的に保証する。

**アプローチ**：
複数の検証手法とツールを組み合わせる包括的な戦略。

### 10.2 検証の範囲

**対象**：
- 標準ライブラリのunsafeコードセクション
- 基礎的なデータ構造（`Vec`、`HashMap`など）
- 並行プリミティブ（`Mutex`、`Arc`など）

**目標**：
標準ライブラリ全体の機械検証可能な安全性証明。

## 11. Rustの型システムを仕様言語として使用する

### 11.1 型レベルプログラミング

**高度な型機能**：
- 関連型（Associated Types）
- 高階型トレイト（Higher-Rank Trait Bounds）
- 定数ジェネリクス（Const Generics）

**仕様表現**：
これらの機能により、型システム自体で複雑な不変条件を表現できる。

### 11.2 ジェネリックプログラミングと仕様

**パラメトリック多相**：
ジェネリクスにより、型に依存しない仕様を記述できる。

**trait境界**：
trait境界は、ジェネリック型が満たすべき契約を指定する。

### 11.3 newtypeパターンによる型安全性

**newtypeパターン**：
既存の型をラップする新しい型を定義し、型レベルでの区別を強制する。

**例**：
```rust
struct UserId(u64);
struct ProductId(u64);
```

これにより、UserIdとProductIdを誤って混同することがコンパイル時に防止される。

### 11.4 型状態パターン

**状態マシンの型レベル表現**：
型システムを使用してオブジェクトの状態を追跡し、無効な状態遷移をコンパイル時に防止する。

**利点**：
- 実行時チェック不要
- APIの誤用をコンパイル時に検出
- ドキュメントとしての型

## 12. まとめと展望

### 12.1 所有権モデルの貢献

**仕様としての型**：
Rustの所有権モデルは、メモリ安全性、スレッド安全性、リソース管理に関する豊富な仕様を型システムとして表現している。

**コンパイル時保証**：
実行時オーバーヘッドなしに強力な安全性保証を提供することで、高性能かつ安全なシステムプログラミングを可能にする。

**アフィン型の重要性**：
メモリ安全性の源泉は、型がアフィン型であることであり、借用検査器はこれを強制するメカニズムである。

### 12.2 形式検証の進展

**RustBelt**：
Rustの意味論の機械検証可能な基盤を提供し、unsafeコードの健全性を証明するフレームワークを確立した。

**検証ツールの成熟**：
PrustiとCreusotのようなツールにより、Rustプログラムの演繹的検証が実用的になりつつある。

**unsafeの課題**：
unsafeコードの安全性カプセル化の検証は依然として課題であり、より良い注釈とガイダンスが必要である。

### 12.3 産業応用の展望

**安全性重要システムへの採用**：
2026年には、Rustが航空宇宙、自動車、医療機器などの安全性重要ドメインで広く採用されると予測される。

**認証ツールチェーン**：
DO-178C、ISO 26262、IEC 61508などの標準に適合するRustツールチェーンの整備が進行中である。

**重要インフラストラクチャ**：
Rustは、メモリ安全性とパフォーマンスが両立する言語として、重要インフラストラクチャの構築に選ばれつつある。

### 12.4 今後の課題

**線形型のサポート**：
純粋な線形型（正確に1回使用される型）への関心が高まっているが、言語への統合は未だ実現していない。

**unsafeガイドラインの標準化**：
unsafeコードの正しい使用に関する明確なガイドラインと検証手法の標準化が求められる。

**教育と普及**：
Rustの所有権モデルの学習曲線は依然として課題であり、より良い教育リソースとツールが必要である。

### 12.5 結論

Rustの所有権モデルは、型システムを仕様言語として使用する優れた例である。所有権、借用、ライフタイムという概念を通じて、メモリ安全性、スレッド安全性、リソース管理に関する豊富な仕様をコンパイル時に検証可能な形で表現している。

アフィン型としての所有権は、メモリ安全性の理論的基盤を提供し、借用検査器はこれを実用的に強制する。RustBeltによる形式的検証基盤の確立、PrustiやCreusotのような検証ツールの発展、そしてAWSなどによる標準ライブラリ検証プロジェクトにより、Rustの安全性保証の信頼性はさらに高まっている。

2025-2026年には、安全性重要システムへのRustの採用が加速し、認証ツールチェーンの整備が進むと予測される。Rustの所有権モデルは、仕様と実装を統合する新しいパラダイムとして、ソフトウェアエンジニアリングに大きな影響を与え続けるであろう。

## 参考文献

### Rust所有権と型システム

- [What does it take to ship Rust in safety-critical? - Rust Blog](https://blog.rust-lang.org/2026/01/14/what-does-it-take-to-ship-rust-in-safety-critical/)
- [Rust 2025: Memory Safety and Performance for Critical Infrastructure](https://blog.madrigan.com/en/blog/202602081440/)
- [Rust in Safety-Critical Systems: Predictions for 2026 - Electronic Design](https://www.electronicdesign.com/technologies/embedded/software/article/55356147/adacore-rust-in-safety-critical-systems-predictions-for-2026)
- [A Grounded Conceptual Model for Ownership Types in Rust - ACM POPL](https://dl.acm.org/doi/10.1145/3622841)
- [Why Rust Is the Language of Choice for Safe and Fast Systems (2025–2026) - Medium](https://medium.com/@amin-softtech/why-rust-is-the-language-of-choice-for-safe-and-fast-systems-2025-2026-060e3bb0a594)

### アフィン型と線形型

- [What are affine types in Rust? - Rust Forum](https://users.rust-lang.org/t/what-are-affine-types-in-rust/23755)
- [Rust Inference Rules for Linear Types - Medium](https://medium.com/@andrew_johnson_4/rust-inference-rules-for-linear-types-e55cb6a347ed)
- [The Pain Of Linear Types In Rust - Faultlore](https://faultlore.com/blah/linear-rust/)
- [What Vale Taught Me About Linear Types, Borrowing, and Memory Safety](https://verdagon.dev/blog/linear-types-borrowing)
- [Type Systems for Memory Safety](https://borretti.me/article/type-systems-memory-safety)
- [Ownership - Without Boats](https://without.boats/blog/ownership/)

### RustBelt

- [RustBelt - Programming Languages & Verification](https://plv.mpi-sws.org/rustbelt/)
- [RustBelt: Logical Foundations for the Future of Safe Systems Programming - Jane Street](https://www.janestreet.com/tech-talks/rustbelt/)
- [RustBelt: Securing the Foundations of the Rust Programming Language - ACM POPL](https://dl.acm.org/doi/10.1145/3158154)
- [RustHornBelt: A Semantic Foundation for Functional Verification - PDF](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf)

### 検証ツール

- [The Prusti Project: Formal Verification for Rust - Springer](https://link.springer.com/chapter/10.1007/978-3-031-06773-0_5)
- [The Prusti Project: Formal Verification for Rust - PDF](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf)
- [Creusot: a Foundry for the Deductive Verification of Rust - PDF](https://inria.hal.science/hal-03737878v1/document)
- [Creusot: A Foundry for the Deductive Verification of Rust Programs - Springer](https://link.springer.com/chapter/10.1007/978-3-031-17244-1_6)
- [Rust Formal Methods Interest Group](https://rust-formal-methods.github.io/)
- [Inventory: Tools of the Trade - High Assurance Rust](https://highassurance.rs/chp16_appendix/tools.html)

### unsafe Rust

- [Annotating and Auditing the Safety Properties of Unsafe Rust - arXiv](https://arxiv.org/pdf/2504.21312)
- [Pre-RFC: Rust Safety Standard - Rust Internals](https://internals.rust-lang.org/t/pre-rfc-rust-safety-standard/23963)
- [Verify the Safety of the Rust Standard Library - AWS Open Source Blog](https://aws.amazon.com/blogs/opensource/verify-the-safety-of-the-rust-standard-library/)
- [A Mixed-Methods Study on the Implications of Unsafe Rust - arXiv](https://arxiv.org/pdf/2404.02230)
- [Safety and Soundness in Rust](https://jacko.io/safety_and_soundness.html)
- [Working with Unsafe - The Rustonomicon](https://doc.rust-lang.org/nomicon/working-with-unsafe.html)
- [RUDRA: Finding Memory Safety Bugs in Rust at the Ecosystem Scale - PDF](https://gts3.org/assets/papers/2021/bae:rudra.pdf)

### ライフタイム

- [Validating References with Lifetimes - The Rust Programming Language](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)
- [Lifetimes - The Rustonomicon](https://doc.rust-lang.org/nomicon/lifetimes.html)
- [A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust - ACM](https://dl.acm.org/doi/fullHtml/10.1145/3443420)
- [Lifetime elision - The Rust Reference](https://doc.rust-lang.org/reference/lifetime-elision.html)

---

**調査実施日**: 2026-02-14  
**調査者**: researcher-06
