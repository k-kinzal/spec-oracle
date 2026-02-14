# ミューテーションテスト

## 概要

ミューテーションテスト（Mutation Testing）は、テストスイートの品質を評価する技法である。プログラムに意図的に小さな変更（変異）を加え、テストがそれを検出できるかを確認する。

## 1. 基本概念

### 1.1 変異体（Mutant）

変異体は、1つの変異演算子をソースプログラムに適用した結果である。プログラムpから、わずかな構文的変更によって欠陥プログラムp'（変異体）の集合が生成される。

参考: [Mutation testing - Wikipedia](https://en.wikipedia.org/wiki/Mutation_testing)

### 1.2 変異演算子（Mutation Operators）

変異演算子はプログラムに構文的変更を加えるガイドラインである：
- コマンドや式の削除・複製
- 演算子の変更（+ → -）
- 演算子の挿入（cond → !cond）
- 定数の変更（True → False）

参考: [What is Mutation Testing? | BrowserStack](https://www.browserstack.com/guide/mutation-analysis-in-software-testing)

### 1.3 変異スコア（Mutation Score）

変異スコア = キルされた変異体数 / 非等価変異体の総数

目標は変異スコアを1に上げることで、テスト集合Tが変異体で示されるすべての欠陥を検出するのに十分であることを示す。

参考: [Mutation Testing in Software Testing](https://www.tutorialspoint.com/mutation-testing-in-software-testing-mutant-score-and-analysis-example)

## 2. 等価変異体問題

### 2.1 問題の定義

等価変異体は、すべての可能なテストケースに対して、元のプログラムと同じ振る舞いを示す変異体である。実世界では、等価変異体の割合は4%〜39%に及ぶ。

参考: [Large Language Models for Equivalent Mutant Detection](https://arxiv.org/html/2408.01760v1)

### 2.2 なぜ問題か

- 等価変異体の発見は決定不可能な問題
- 手作業でのレビューが必要で高コスト
- 変異スコア100%の達成を不可能にする

参考: [Mutation testing - Wikipedia](https://en.wikipedia.org/wiki/Mutation_testing)

### 2.3 対策

2014年の系統的文献レビューで17の関連技法（22論文）と3つのカテゴリが特定された：
- 検出（DEM）
- 提案（SEM）
- 等価変異体生成の回避（AEMG）

参考: [Mitigating the effects of equivalent mutants](https://www.sciencedirect.com/science/article/pii/S0167642314002603)

## 3. 主要ツール

### 3.1 PIT（Java用）

PITは、Javaプロジェクトで最も広く使用されているミューテーションテストツールである。Maven、Gradle、主要IDEと統合され、コンパイルされたJavaバイトコードに変更を注入する。

参考: [PIT Mutation Testing](https://pitest.org/)

### 3.2 Stryker（JavaScript/TypeScript等用）

Strykerは、JavaScript & TypeScript、C#、Scalaをサポートするオープンソースのミューテーションテストツールである。任意のテストランナーで動作し、Strykerダッシュボード経由でスマートレポートを提供する。

参考: [Stryker Mutator](https://stryker-mutator.io/)

## 4. U-D-Aモデルへの示唆

### テストスイートの品質評価

- D（望ましい振る舞い）: 仕様が記述する正しい振る舞い
- 変異体: Dに違反する振る舞い
- テスト: Dに違反する実装を検出する能力

ミューテーションテストは、テストスイートがDを適切に検証できているかを測定する。

## 参考文献

- [Mutation testing - Wikipedia](https://en.wikipedia.org/wiki/Mutation_testing)
- [What is Mutation Testing? | BrowserStack](https://www.browserstack.com/guide/mutation-analysis-in-software-testing)
- [PIT Mutation Testing](https://pitest.org/)
- [Stryker Mutator](https://stryker-mutator.io/)
- [Large Language Models for Equivalent Mutant Detection](https://arxiv.org/html/2408.01760v1)
