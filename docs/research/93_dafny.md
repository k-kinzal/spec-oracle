# Dafny（検証言語）

## 概要

Dafnyは、Microsoft Researchで開発された検証指向プログラミング言語（verification-aware programming language）である。K. Rustan M. Leinoによって設計され、プログラムの機能的正当性を自動的に検証することを目的としている。Dafnyは、仕様とプログラムを統合的に記述し、Hoare論理ベースの検証をSMTソルバー（Z3）を用いて自動的に実行する。

Dafnyの特徴は、プログラマが正しいコード（runtime errorsがなく、意図した通りに動作するコード）を書くことを容易にする点にある。事前条件、事後条件、ループ不変条件などの仕様をプログラムと共に記述し、Dafnyの検証器がこれらの性質を自動的に証明する。

## 1. 開発者と歴史

### 1.1 K. Rustan M. Leino

K. Rustan M. Leinoは、現在Amazon Web Services（AWS）のAutomated Reasoning GroupでSenior Principal Applied Scientistを務めている。プログラムが意図した通りに動作することを保証する方法、特にセキュアで機能的に正しいプログラムの検証に取り組んでいる。

**経歴:**
- Amazon Web Services（現職）
- Microsoft Research（Principal Researcher）
- Imperial College London（Visiting Professor）
- DEC/Compaq SRC（Researcher）

**主要な貢献:**
Leinoは、プログラミング手法とプログラム検証ツールの構築における世界的リーダーであり、以下のツールと言語を開発した:
- Dafny
- Chalice
- Jennisys
- Spec#
- Boogie
- Houdini
- ESC/Java
- ESC/Modula-3

### 1.2 Dafnyの位置づけ

Dafnyは、仕様と証明のネイティブサポートを持ち、自動アクティブ静的プログラム検証器を備えた、確立された検証指向プログラミング言語のグループに属する。POPL 2026でもDafny専用のワークショップが開催されるなど、学術界・産業界で広く認知されている。

## 2. Dafnyのアーキテクチャ

### 2.1 全体構造

Dafnyの検証アーキテクチャは、複数の層から構成される:

```
Dafnyプログラム（仕様+実装）
    ↓
Dafny検証器
    ↓
Boogie中間検証言語（IVR）
    ↓
Z3 SMTソルバー
    ↓
検証結果（成功/失敗）
```

### 2.2 Boogieとの関係

Dafnyの検証器は、Boogie中間検証言語の上に構築されている。Boogieは、検証条件を述語論理に変換する中間表現（IVR）を提供する。

**Boogieの役割:**
- プログラムロジックを検証条件に変換
- 型システムと制御フローの抽象化
- SMTソルバーへのインターフェース

### 2.3 Z3 SMTソルバー

Dafnyは、Satisfiability Modulo Theories（SMT）ソルバーとして、Microsoftが開発したZ3定理証明器を使用する。

**Z3の機能:**
- 検証条件の自動証明
- 理論の組み合わせ（算術、配列、ビットベクトル等）
- 反例の生成（証明失敗時）

**バージョン:**
- Dafny 4.0: Z3 4.8.5から4.12.1にアップグレード
- すべてのZ3バージョン4.8.5〜4.12.1と完全互換

### 2.4 コンパイル機能

Dafnyは検証だけでなく、複数のターゲット言語へのコンパイルもサポートする:

**サポートされるターゲット言語:**
- C#
- Java
- JavaScript
- Go
- Python

これにより、検証済みのDafnyコードを実際のプロダクション環境で実行できる。

## 3. Dafnyの仕様記述

### 3.1 事前条件（Precondition）

事前条件は、メソッドが呼び出される前に成立していなければならない条件を定義する。

**キーワード:** `requires`

**意味:**
- 呼び出し側の義務：事前条件を確立する責任
- メソッド側の権利：事前条件を仮定できる

**例:**
```dafny
method Divide(x: int, y: int) returns (q: int)
  requires y != 0  // yはゼロでない
{
  q := x / y;
}
```

Dafnyは、メソッド呼び出し時に事前条件が満たされていることを証明で強制する。

### 3.2 事後条件（Postcondition）

事後条件は、メソッド実行後に成立していることが保証される条件を定義する。

**キーワード:** `ensures`

**意味:**
- メソッド側の義務：事後条件を確立する責任
- 呼び出し側の権利：事後条件を仮定できる

**例:**
```dafny
method Max(a: int, b: int) returns (m: int)
  ensures m >= a && m >= b
  ensures m == a || m == b
{
  if a > b {
    m := a;
  } else {
    m := b;
  }
}
```

**`old`キーワード:**
事後条件内で`old(expr)`を使用すると、メソッド実行前の値を参照できる。

```dafny
method Increment(x: int) returns (y: int)
  ensures y == old(x) + 1
{
  y := x + 1;
}
```

### 3.3 ループ不変条件（Loop Invariant）

ループ不変条件は、ループ進入時とループ本体の各実行後に成立する式である。

**キーワード:** `invariant`

**役割:**
- ループに関する不変な性質を捕捉
- ループで変更される変数の情報を明示的に表現

**重要性:**
ループで変更される変数については、ループ前の情報が（ほとんど）破棄される。これらの変数の性質を証明するには、ループ不変条件で明示的に表現する必要がある。

**例:**
```dafny
method Sum(n: nat) returns (s: int)
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == i * (i + 1) / 2
  {
    i := i + 1;
    s := s + i;
  }
}
```

### 3.4 クラス不変条件

クラスのフィールドに対する不変条件も定義できる。これは、すべてのパブリックメソッドの実行前後で成立する必要がある。

## 4. ゴースト要素（Ghost Elements）

### 4.1 ゴースト変数（Ghost Variables）

ゴースト変数は、`ghost`修飾子で宣言され、検証時にのみ使用される変数である。

**特徴:**
- コンパイル時には削除される
- 実行時のパフォーマンスに影響しない
- プログラムの性質を推論するためのみに使用

**例:**
```dafny
class Counter {
  var value: int
  ghost var history: seq<int>

  constructor()
    ensures value == 0
    ensures history == [0]
  {
    value := 0;
    history := [0];
  }

  method Increment()
    ensures value == old(value) + 1
    ensures history == old(history) + [value]
  {
    value := value + 1;
    history := history + [value];
  }
}
```

### 4.2 ゴースト関数（Ghost Functions）

ゴースト関数も検証時のみに使用され、実行時には存在しない。

**用途:**
- 補助的な性質の定義
- 複雑な仕様の分解
- 抽象化レベルの提供

## 5. 帰納法と補題

### 5.1 補題（Lemmas）

補題は、定理を証明するために使用される中間結果である。Dafnyでは、補題はゴーストメソッドとして実装される。

**定義:**
補題のコントラクト（契約）が、その補題が保証する性質を表す。
- 事後条件：補題のステートメント（証明目標）
- 事前条件：補題の前提条件

**例:**
```dafny
lemma MultiplyCommutative(x: int, y: int)
  ensures x * y == y * x
{
  // 証明本体（多くの場合、自動的に証明される）
}
```

### 5.2 帰納法（Induction）

帰納法は、目標を一歩ずつ構築する方法、または小さなバージョンの観点から目標を証明する方法である。

**Dafnyでの帰納法:**
- 補題の再帰呼び出しが帰納的証明を設定する
- 再帰呼び出しにより帰納仮説を取得する

**例:**
```dafny
lemma SumFormula(n: nat)
  ensures 2 * Sum(n) == n * (n + 1)
{
  if n == 0 {
    // 基底ケース
  } else {
    // 帰納ステップ：帰納仮説を適用
    SumFormula(n - 1);
  }
}

function Sum(n: nat): nat
{
  if n == 0 then 0 else n + Sum(n - 1)
}
```

### 5.3 ヒントとアサーション

検証器がうまく証明できない場合、プログラマはヒントとしてアサーションを提供できる。

**ヒントの役割:**
- 検証器が証明すべきアサーション
- 証明されたら、正当性証明の完了に使用可能な性質になる

**`calc`文:**
段階的な証明の正当化に使用される特殊な構文。

```dafny
calc {
  f(x);
==  { Lemma1(x); }
  g(x);
==  { Lemma2(x); }
  h(x);
}
```

## 6. 自動検証と限界

### 6.1 自動検証の能力

多くの場合、`requires`と`ensures`句のような最終的な性質のみを記述し、残りは証明器に自動的に実行させることができる。

**成功例:**
- 単純な算術性質
- 基本的なデータ構造操作
- 標準的なアルゴリズム

### 6.2 自動検証の限界

Z3ソルバーが必要な証明に自動的に到達できない場合がある（証明が存在するにもかかわらず）。

**対処法:**
開発者の介入により、以下の形で追加のコンテキストを提供:
- アサーション（assertions）
- 関数（functions）
- 述語（predicates）
- 補題（lemmas）

### 6.3 エラーメッセージの課題

Dafnyは、事後条件を証明できない場合にエラーメッセージを出すが、**なぜ**証明できないかを説明しない。

**開発者の課題:**
- コードが事後条件に違反しているのか
- 検証器がDafnyまたはSMTソルバーの制限により失敗しているのか
- どのようなヒントが証明成功を可能にするか

を判断する必要がある。

## 7. Dafnyの実用事例

### 7.1 IronFleet

**概要:**
IronFleetは、分散システムの実装の安全性と活性を、Dafnyで機械チェック検証する手法である。

**特徴:**
- TLAスタイルの状態機械リファインメント
- Hoare論理検証の統合
- 実用的かつ証明可能に正しい分散システムの構築

**成果:**
- **IronRSL**: Paxosベースの複製状態機械ライブラリ
- **IronKV**: リースベースのシャード化キーバリューストア

**検証内容:**
- 簡潔な安全性仕様の遵守
- 望ましい活性要件の達成

**手法:**
分散システムの実装と証明を3つの層に整理:
1. 高レベル仕様層
2. 分散プロトコル層
3. 実装層

TLAスタイルの状態機械リファインメントでプロトコルレベルの並行性を推論し、Floyd-Hoareスタイルの命令型検証で実装の複雑さを推論する。

### 7.2 IronClad

Microsoftによる暗号学的に検証されたシステムの構築プロジェクト。Dafnyを使用してセキュリティプロパティを検証。

### 7.3 AWS関連プロジェクト

- **AWS Encryption SDK**: 一部でDafnyを使用
- **Amazon Verified Permissions**: モデルの検証にDafnyを利用

### 7.4 学術・産業での成功

Dafnyは、いくつかの産業および学術の場で利用され成功を収めており、形式検証の実用性を実証している。

## 8. AI/LLMとの統合

### 8.1 AI支援によるDafny合成

**最近の研究動向:**
大規模言語モデル（LLM）とDafnyの組み合わせが進んでいる。

**アプローチ:**
- LLMが直接ターゲット言語（例：Python）を生成するのではなく
- まず形式検証言語Dafnyの中間表現を生成
- その後、厳密な正確性検査を実行
- 最終的に目的のプログラミング言語に翻訳

**利点:**
- コード生成の正当性保証
- 検証可能なコードの自動生成

### 8.2 Dafny-Annotator

**概要:**
大規模言語モデルと検索アルゴリズムを組み合わせて、プログラムに論理的な注釈を自動的に追加するツール。

**機能:**
- アサーションの自動生成
- 補題の自動発見
- 検証可能なコードへの変換

### 8.3 ヘルパーアサーションの推論

**課題:**
実際には、ほとんどの証明が多数のヘルパーアサーション（検証器を導くが、プログラムの振る舞いに影響しないアサーションや補題呼び出し）を必要とする。

**AI支援:**
LLMを用いて、不足しているアサーションとその配置場所を特定する研究が進行中。

## 9. Dafnyの限界と課題

### 9.1 証明デバッグの困難さ

**問題:**
エラーメッセージが「なぜ」証明できないかを説明しないため、開発者は以下を判断する必要がある:
- コードの問題か検証器の限界か
- どのヒントが必要か

### 9.2 ヘルパーアサーションの必要性

**課題:**
- 不足しているアサーションの特定が困難
- アサーションの配置場所の決定が時間を要する
- 補題の発見と適用が複雑

### 9.3 スケーラビリティの問題

**証明コンテキストの増大:**
- 開発者が証明ツリーの上位に移動するにつれて、証明コンテキストが増加
- 下位レベルの補題を使用して高レベルの性質を証明する際、スケーリング問題が発生
- 大規模な証明の実現可能性への疑問

### 9.4 仕様の弱点

**根本的な限界:**
形式検証は、実装が仕様に適合することのみを保証し、意図した振る舞いを示すことは保証しない。

**問題:**
- 不正確な仕様
- 不完全な仕様
- 仕様自体の欠陥

これらは形式検証の重要な制限である。

### 9.5 複雑な証明機能

**証明の複雑性の源:**
- **量化子（Quantifiers）**: 複雑な論理表現
- **フレーム条件（Frame Conditions）**: オブジェクトが変更後も有効であることの証明

開発者がこれらを制御する能力は限定的。

### 9.6 トランスパイルのリスク

**問題:**
検証全体は、Dafnyからターゲット言語へのトランスパイラが正しく動作することに依存する。

**影響:**
- 8人の参加者がこのリスクを言及（研究調査より）
- 生成されたコードのレビューが必要

### 9.7 デバッグツールの欠如

**制限:**
- Dafnyにはデバッグやプロファイリングツールがない
- 開発者はトランスパイルされたターゲットコードを直接調査するしかない
- 検証済みソースコードのデバッグが困難

## 10. 他の検証言語との比較

### 10.1 Why3

**Why3の特徴:**
- 専用の演繹的検証言語
- Hoare論理を使用
- 複数のプログラミング言語の中間言語として機能
- 複数の定理証明器との統合

**Dafnyとの違い:**
- Dafny: スタンドアロンのプログラミング・検証言語
- Why3: 中間言語として設計、バックエンドを共有

**エイリアシング:**
- Why3: エイリアシングを静的に制御
- Dafnyでは任意のエイリアシングが可能（Cと同様）

### 10.2 Frama-C と ACSL

**Frama-C:**
- ISO C99ソースコードの産業分析のための包括的な静的解析プラットフォーム
- 協働するプラグインをホストする共通カーネル
- ACSLを共通仕様言語として使用

**ACSL（ANSI/ISO C Specification Language）:**
- Cプログラムのための振る舞い仕様言語
- JMLに触発された設計
- Frama-CプラグインのためのLingua Franca

**Dafnyとの違い:**
- Frama-C/ACSL: 既存のC言語プログラムに注釈を追加
- Dafny: 検証を組み込んだ独立した言語

**WPプラグイン:**
- Why3経由で外部定理証明器を使用して検証条件を解消
- Frama-CとWhy3の統合例

### 10.3 比較レポート

KeY、Why3、Dafny、Frama-Cを用いた同一の検証タスクの比較レポートが存在する。それぞれのツールの特徴と適用範囲が異なることが示されている。

**静的検証 vs 動的検証:**
Why3、Frama-C、SPARK 2014における静的検証と動的検証の比較研究も行われている。

## 11. Dafnyの統合開発環境

**Dafny IDE:**
Dafnyは統合開発環境を提供し、以下の機能をサポート:
- リアルタイムの検証フィードバック
- エラーの視覚化
- インタラクティブな証明開発

**ビジュアル検証フィードバック:**
最近の研究では、Dafnyのビジュアル検証フィードバックにより、検証をより魅力的にする取り組みが進められている。

## 12. まとめ

Dafnyは、K. Rustan M. Leinoによって開発された、検証指向プログラミング言語の代表例である。Hoare論理、Boogie中間言語、Z3 SMTソルバーを組み合わせ、プログラムの機能的正当性を自動的に検証する。

**主要な特徴:**
- 仕様とプログラムの統合記述
- 事前条件、事後条件、ループ不変条件
- ゴースト変数・関数による検証時のみの推論
- 帰納法と補題による高度な証明
- 複数言語へのコンパイル機能

**実用事例:**
- IronFleet（分散システムの検証）
- AWS Encryption SDK、Amazon Verified Permissions
- 学術・産業での多数の成功例

**利点:**
- 自動検証による高い生産性
- 正当性の数学的保証
- 実行可能な検証済みコード

**課題:**
- エラーメッセージの不明瞭さ
- ヘルパーアサーションの手動追加
- スケーラビリティの問題
- 仕様自体の正しさの保証は別問題
- トランスパイルの信頼性

**今後の展望:**
AI/LLMとの統合により、Dafnyのアサーション生成や補題発見の自動化が進んでいる。これにより、形式検証の実用性がさらに向上し、より広範な適用が期待される。

Dafnyは、仕様と実装の橋渡しとして、また形式手法の実用化の成功例として、プログラム検証の分野で重要な役割を果たし続けている。

## 参考文献・情報源

### 公式ドキュメント・概要
- [Dafny Official Website](https://dafny.org/)
- [Dafny - Wikipedia](https://en.wikipedia.org/wiki/Dafny)
- [Dafny: A Language and Program Verifier for Functional Correctness - Microsoft Research](https://www.microsoft.com/en-us/research/project/dafny-a-language-and-program-verifier-for-functional-correctness/)
- [Dafny 2026 - POPL 2026](https://popl26.sigplan.org/home/dafny-2026)

### K. Rustan M. Leino
- [Tutorial: Theorem Proving and Program Verification with Dafny - Imperial College London](https://www.imperial.ac.uk/events/106505/tutorial-theorem-proving-and-program-verification-with-dafny-rustan-leino-microsoft-research/)
- [K. Rustan M. Leino - POPL 2026 Profile](https://popl26.sigplan.org/profile/krustanmleino)

### アーキテクチャと検証
- [Dafny: An Automatic Program Verifier for Functional Correctness | Springer](https://link.springer.com/chapter/10.1007/978-3-642-17511-4_20)
- [Using Dafny, an Automatic Program Verifier - Microsoft Research](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml221.pdf)
- [The Dafny Integrated Development Environment](https://arxiv.org/pdf/1404.6602)
- [Verification Optimization | Dafny Documentation](https://dafny.org/latest/VerificationOptimization/VerificationOptimization)

### Z3とSMT
- [Dafny 4 is released | Dafny Blog](https://dafny.org/blog/2023/03/03/dafny-4-released/)
- [Z3 Theorem Prover - Wikipedia](https://en.wikipedia.org/wiki/Z3_Theorem_Prover)

### 仕様記述ガイド
- [Getting Started with Dafny: A Guide | Dafny Documentation](https://dafny.org/latest/OnlineTutorial/guide)
- [Getting Started with Dafny: A Guide - Jason Koenig & K. Rustan M. Leino](https://www.andrew.cmu.edu/course/18-330/2025s/reading/dafny_guide.pdf)
- [Dafny Quick Reference | Dafny Documentation](https://dafny.org/latest/QuickReference)
- [Verified programming in Dafny](https://www.doc.ic.ac.uk/~scd/Dafny_Material/Lectures.pdf)

### 帰納法と補題
- [Lemmas and Induction | Dafny Documentation](https://dafny.org/latest/OnlineTutorial/Lemmas)
- [A Tutorial on Using Dafny to Construct Verified Software](https://arxiv.org/pdf/1701.04481)
- [Dafny Power User: Automatic Induction](https://leino.science/papers/krml269.html)
- [Well-founded Functions and Extreme Predicates in Dafny: A Tutorial](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml250.pdf)

### 限界と課題
- [DafnyBench: A Benchmark for Formal Software Verification](https://www.aimodels.fyi/papers/arxiv/dafnybench-benchmark-formal-software-verification)
- [On the Impact of Formal Verification on Software Development](https://ranjitjhala.github.io/static/oopsla25-formal.pdf)
- [Inferring multiple helper Dafny assertions with LLMs](https://arxiv.org/html/2511.00125v1)
- [MutDafny: A Mutation-Based Approach to Assess Dafny Specifications](https://arxiv.org/html/2511.15403v1)

### IronFleet
- [IronFleet: Proving Practical Distributed Systems Correct](https://www.andrew.cmu.edu/user/bparno/papers/ironfleet.pdf)
- [Ironclad/ironfleet - GitHub](https://github.com/microsoft/Ironclad/blob/main/ironfleet/README.md)
- [IronFleet: Proving Practical Distributed Systems Correct | the morning paper](https://blog.acolyer.org/2015/10/15/ironfleet-proving-practical-distributed-systems-correc/)

### AI/LLM統合
- [Towards AI-Assisted Synthesis of Verified Dafny Methods](https://arxiv.org/html/2402.00247v1)
- [Dafny as Verification-Aware Intermediate Language for Code Generation](https://arxiv.org/abs/2501.06283)
- [DafnyメソッドのAI支援合成に向けて | AI Business Review](https://aibr.jp/2025/03/17/dafny%E3%83%A1%E3%82%BD%E3%83%83%E3%83%89%E3%81%AEai%E6%94%AF%E6%8F%B4%E5%90%88%E6%88%90%E3%81%AB%E5%90%91%E3%81%91%E3%81%A6%EF%BC%88towards-ai-assisted-synthesis-of-verified-dafny-methods%EF%BC%89/)
- [Dafny・アノテーター：AI支援によるDafnyプログラムの検証 | AI Business Review](https://aibr.jp/2025/01/27/dafny%E3%83%BB%E3%82%A2%E3%83%8E%E3%83%86%E3%83%BC%E3%82%BF%E3%83%BC%EF%BC%9Aai%E6%94%AF%E6%8F%B4%E3%81%AB%E3%82%88%E3%82%8Bdafny%E3%83%97%E3%83%AD%E3%82%B0%E3%83%A9%E3%83%A0%E3%81%AE%E6%A4%9C/)

### 比較研究
- [Proving Line Wrapping in KeY, Why3, Dafny and Frama-C – The KeY Project](https://www.key-project.org/2021/04/07/proving-line-wrapping/)
- [Static versus Dynamic Verification in Why3, Frama-C and SPARK 2014 | Springer](https://link.springer.com/chapter/10.1007/978-3-319-47166-2_32)
- [Frama-C: A software analysis perspective](https://cea.hal.science/cea-01808981/file/FRAMA.pdf)
- [ACSL - Frama-C](https://frama-c.com/html/acsl.html)
- [Frama-C - Wikipedia](https://en.wikipedia.org/wiki/Frama-C)
