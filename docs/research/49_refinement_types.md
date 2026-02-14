# リファインメント型（Refinement Types）

## 概要

リファインメント型は、基底型に論理述語を付加することで、型が記述する値の集合を制約する型システムである。

## 1. 基本構造

リファインメント型の基本形式：`{v:b | p}`

- **b**: 基底型（Int、Bool など）
- **p**: 論理述語（値を制約するブール式）

参考: [Refinement Types - Liquid Haskell](https://nikivazou.github.io/lh-course/Lecture_01_RefinementTypes.html)

## 2. Liquid Types と LiquidHaskell

### 2.1 LiquidHaskell

LiquidHaskellは、リファインメント型を使用したHaskellの自動検証器である。リファインメント型は依存型の制限された形式で、値間の関係を論理述語で型を装飾することで符号化する。

参考: [LiquidHaskell: experience with refinement types](https://dl.acm.org/doi/10.1145/2775050.2633366)

### 2.2 動作原理

Liquid HaskellはリファインメントからZ3などのSMTソルバーに検証を外注する論理制約の集合に変換する。

参考: [Refinement Types For Haskell](https://goto.ucsd.edu/~nvazou/refinement_types_for_haskell.pdf)

## 3. F*（F-star）

F*は、依存リファインメント型を含む完全な依存型を持つ全域関数を特徴とするコア言語である。Z3 SMTソルバーを統合し、型検査器は証明すべきすべての事実を収集しSMTソルバーに符号化する。

参考: [Getting off the ground — F*](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html)

## 4. リファインメント型と依存型の違い

### 型システムの哲学

- **リファインメント型**: 既存の型システムを洗練する。言語や既存の型システムを変更できない
- **依存型**: より表現力のある型システムで、より多くのプログラムを受け入れる

### 証明の検証

- **リファインメント型**: 自動化が好まれる。外部ソルバー（SMTソルバー）を使用
- **依存型**: 手動証明記述が基本。証明は言語内に存在

参考: [Dependent And Refinement Types: Why?](https://xebia.com/blog/dependent-and-refinement-types-why/)

## 5. U-D-Aモデルへの示唆

リファインメント型は、U-D-Aモデルにおいて：

- **U（宇宙）**: 基底型が定義する値の空間
- **D（望ましい振る舞い）**: 述語pで表現される制約
- **A（許容集合）**: {v:b | p} を満たす値の集合

型検査によって、プログラムがAに属することを静的に保証できる。

## 参考文献

- [Refinement Types - Liquid Haskell](https://nikivazou.github.io/lh-course/Lecture_01_RefinementTypes.html)
- [LiquidHaskell: experience with refinement types](https://dl.acm.org/doi/10.1145/2775050.2633366)
- [Getting off the ground — F*](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html)
- [Dependent And Refinement Types: Why?](https://xebia.com/blog/dependent-and-refinement-types-why/)
