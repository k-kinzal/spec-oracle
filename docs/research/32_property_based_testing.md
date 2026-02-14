# Property-Based Testing（PBT）の理論と実践

## 概要

Property-Based Testing（PBT）は、プログラムが満たすべき**性質**（Property）を記述し、その性質をランダム生成された大量の入力で自動的に検証するテスト手法である。1999年にKoen Claessenと John Hughesによって開発されたHaskellのQuickCheckライブラリが起源であり、2000年のICFP（International Conference on Functional Programming）で発表された論文「QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs」により広く知られるようになった。

PBTは、個別のテストケースを列挙する従来の例ベースのテスト（Example-Based Testing）とは対照的に、「任意の入力に対して成立すべき抽象的な規則」を記述することで、より強力なテストを少ないコードで実現する。本調査では、PBTの理論的基盤、主要な概念（性質、ジェネレータ、シュリンキング）、各プログラミング言語のライブラリ、PBTと仕様の関係、そして限界と課題について包括的に考察する。

## 1. QuickCheckの誕生と歴史

### 1.1 起源（1999-2000年）

Property-Based Testingは、**Koen Claessen**と**John Hughes**によって1999年にHaskellのソフトウェアライブラリとして開発された。

**開発の経緯**:
- John Hughesがプロパティベーステストのアイデアに取り組んでいた際、Koen Claessenが興味を示した
- Koen Claessenが翌日、改良版を持ち帰った
- 1週間の反復を経て、最初のプロパティベーステストの実装が完成
- ICFP 2000で論文「QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs」を発表

**論文の内容**:
- 著者: Koen Claessen, John Hughes
- 会議: Fifth ACM SIGPLAN International Conference on Functional Programming (ICFP '00)
- 開催地: モントリオール、カナダ
- 日付: 2000年9月

### 1.2 QuickCheckの特徴

**軽量DSL**:
- オリジナルのQuickCheckは約300行のコード
- 論文の付録に完全なソースコードが掲載されている
- コンビネータライブラリとして設計

**設計思想**:
- プロパティをHaskell関数として記述
- ランダム入力による自動テスト
- カスタムテストデータジェネレータの定義が可能

**影響力**:
- 関数型プログラミングコミュニティで高い影響力
- 約40の異なる言語に移植された

### 1.3 Quviq ABの設立

**商用化**:
- 2006年、John HughesとThomas Artsにより**Quviq AB**が設立
- QuickCheckの商用版を提供
- 産業界での形式検証とテストの適用を推進

## 2. Property-Based Testingの基礎

### 2.1 PBTとは

**定義**:
Property-Based Testingは、「ある前提条件を満たすすべての入力に対して、ある述語が成立する」という形式のプロパティ（性質）を定義し、フレームワークが多様な入力を生成してテストを実行する手法である。

**基本的な流れ**:
1. プログラムの性質（Property）を記述
2. フレームワークが自動的にテスト入力を生成
3. 生成された入力で性質が成立するかチェック
4. 失敗した場合、最小の反例を探索（シュリンキング）

### 2.2 例ベーステストとの比較

| 観点 | 例ベーステスト | Property-Based Testing |
|------|----------------|-------------------------|
| テストケース | 手動で具体的なケースを列挙 | フレームワークが自動生成 |
| 記述内容 | 入力と期待出力の組 | 満たすべき性質（抽象的規則） |
| カバレッジ | 記述したケースのみ | 生成された多数のケース |
| エッジケース | 人間が思いつく範囲 | ランダム生成で発見 |
| コード量 | 多くなりがち | 少なくて済む |

### 2.3 PBTの利点

**多様な入力の自動生成**:
- 人間のバイアスによって見落とされるエッジケースを発見
- ライブラリによる自動生成で様々なデータパターンをテスト

**コア理論への集中**:
- プロパティ（性質）のテストに集中できる
- 仕様変更時、生成方法の修正のみで対応可能

**少ないコードで強力なテスト**:
- 抽象的な性質の記述により、多くのケースをカバー
- テストコードの再利用性が高い

**早期のバグ発見**:
- 開発中に継続的にテスト可能
- 単体テストのように素早く実行

## 3. 性質（Property）の記述

### 3.1 性質とは

**性質**（Property）は、プログラムが満たすべき抽象的な規則である。典型的には以下の形式で表現される：

> 「すべての入力 x に対して、P(x) が成立する」

### 3.2 典型的な性質のパターン

**1. ラウンドトリップ性（Roundtrip）**:
- エンコードとデコードを往復すると元に戻る
- 例: `decode(encode(x)) == x`
- シリアライゼーション、暗号化などに適用

**2. 不変量（Invariant）**:
- 操作の前後で特定の性質が保たれる
- 例: リストの長さ、要素の総和
- データ構造操作に適用

**3. 可逆性（Reversibility）**:
- ある操作を逆操作で元に戻せる
- 例: `reverse(reverse(list)) == list`

**4. 冪等性（Idempotence）**:
- 同じ操作を複数回適用しても結果が変わらない
- 例: `sort(sort(list)) == sort(list)`

**5. 交換法則（Commutativity）**:
- 操作の順序を入れ替えても結果が同じ
- 例: `add(x, y) == add(y, x)`

**6. 結合法則（Associativity）**:
- 操作のグループ化を変えても結果が同じ
- 例: `(a + b) + c == a + (b + c)`

**7. 参照実装との比較（Differential Testing）**:
- 既知の正しい実装と比較
- 例: 高速化したソート関数と標準ライブラリのソート関数の結果が一致

**8. 後条件（Postcondition）**:
- 関数実行後に成立すべき条件
- 例: `sorted(sort(list)) == true`

### 3.3 性質記述の例

**リストの逆転**:
```haskell
prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs
```

**ソートの性質**:
```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.lists(st.integers()))
def test_sort_length(xs):
    assert len(sorted(xs)) == len(xs)

@given(st.lists(st.integers()))
def test_sort_idempotent(xs):
    assert sorted(sorted(xs)) == sorted(xs)
```

**JSON エンコード/デコード**:
```javascript
fc.assert(fc.property(
  fc.record({name: fc.string(), age: fc.nat()}),
  (obj) => {
    const json = JSON.stringify(obj);
    const decoded = JSON.parse(json);
    return JSON.stringify(decoded) === json;
  }
));
```

## 4. ジェネレータ（Generator）

### 4.1 ジェネレータとは

**ジェネレータ**は、テスト用の入力データを自動生成する機構である。PBTフレームワークは、様々な型のデータに対するジェネレータを提供する。

### 4.2 基本的なジェネレータ

**プリミティブ型**:
- 整数: `st.integers()`, `fc.integer()`
- 浮動小数点数: `st.floats()`, `fc.float()`
- 文字列: `st.text()`, `fc.string()`
- ブール値: `st.booleans()`, `fc.boolean()`

**コレクション**:
- リスト: `st.lists(st.integers())`, `fc.array(fc.integer())`
- タプル: `st.tuples(st.integers(), st.text())`
- 辞書: `st.dictionaries(keys=st.text(), values=st.integers())`

### 4.3 カスタムジェネレータ

ドメイン特化型のデータ構造には、カスタムジェネレータを定義できる：

**複合オブジェクト**:
```python
from hypothesis import given
import hypothesis.strategies as st

# ユーザーオブジェクトのジェネレータ
users = st.builds(
    User,
    name=st.text(min_size=1, max_size=100),
    age=st.integers(min_value=0, max_value=150),
    email=st.emails()
)

@given(users)
def test_user_serialization(user):
    assert User.from_dict(user.to_dict()) == user
```

**制約付きデータ**:
```rust
use proptest::prelude::*;

// 正の偶数のジェネレータ
fn even_positive() -> impl Strategy<Value = i32> {
    (1..1000).prop_map(|x| x * 2)
}
```

### 4.4 ジェネレータの合成

小さなジェネレータを組み合わせて、複雑なデータ構造を生成：

```haskell
-- 二分木のジェネレータ
data Tree a = Leaf | Node a (Tree a) (Tree a)

instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = sized tree'
    where
      tree' 0 = return Leaf
      tree' n = oneof
        [ return Leaf
        , liftM3 Node arbitrary subtree subtree
        ]
        where subtree = tree' (n `div` 2)
```

## 5. シュリンキング（Shrinking）

### 5.1 シュリンキングとは

**シュリンキング**は、テストが失敗した際に、失敗を引き起こす最小の入力（最小反例）を自動的に探索する機構である。

**目的**:
- デバッグを容易にする
- 失敗の本質を明らかにする
- 偶然の要素を排除

### 5.2 シュリンキングの動作原理

**基本的な戦略**:
1. テストが失敗した入力から開始
2. その入力を「より小さく」変換
3. 変換後の入力でもテストが失敗するか確認
4. 失敗する限り、さらに小さくする
5. 最小の失敗入力が見つかるまで繰り返す

**「より小さく」の定義**:
- 数値: 0に近づける（整数化、絶対値の減少）
- リスト/配列: 要素を削除、空リストに近づける
- 文字列: 文字を削除、空文字列に近づける
- その他: 型やドメインに応じた「中立的な値」に近づける

### 5.3 シュリンキングの例

**元の失敗入力**:
```
リスト: [42, -17, 0, 99, -5, 3, 88, -2]
```

**シュリンキング過程**:
```
[42, -17, 0, 99, -5, 3, 88, -2]  # 失敗
[42, -17, 0, 99]                  # 失敗（後半削除）
[42, -17]                          # 失敗（さらに削除）
[42]                               # 失敗（さらに削除）
[]                                 # 成功（これ以上削れない）
-> 最小反例: [42]
```

### 5.4 Internal Shrinking

**Internal Shrinking**は、シュリンキングをランダム生成に統合した最新のアプローチである。

**利点**:
- ランダム生成とシュリンキングの統合が不要
- ランダムソースを縮小すると、生成されるテストケースが自動的に簡略化される
- より効率的で実装が簡潔

**仕組み**:
- ランダム性の根本的なソースを縮小
- ジェネレータが自動的に簡略化された出力を生成

## 6. 各言語のPBTライブラリ

### 6.1 Haskell: QuickCheck

**オリジナルのPBTライブラリ**:
- 最も歴史があり、他言語の手本
- 型クラスを活用した柔軟な設計
- `Arbitrary`型クラスでジェネレータを定義

**使用例**:
```haskell
import Test.QuickCheck

prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs

main = quickCheck prop_reverse
```

### 6.2 Python: Hypothesis

**特徴**:
- Pythonで最も人気のあるPBTライブラリ
- QuickCheckに触発されたが、独自の進化
- 豊富な組み込みストラテジー
- Numpyやpandas等のライブラリとの統合

**使用例**:
```python
from hypothesis import given
import hypothesis.strategies as st

@given(st.lists(st.integers()))
def test_sorted_is_sorted(xs):
    result = sorted(xs)
    for i in range(len(result) - 1):
        assert result[i] <= result[i + 1]
```

**公式サイト**: https://hypothesis.readthedocs.io/

### 6.3 JavaScript/TypeScript: fast-check

**特徴**:
- JavaScriptとTypeScript向けの主要PBTライブラリ
- 非同期コードのテストに対応
- Webアプリケーションのテストに最適

**使用例**:
```typescript
import fc from 'fast-check';

test('reverse twice is identity', () => {
  fc.assert(
    fc.property(fc.array(fc.integer()), (arr) => {
      const reversed = arr.slice().reverse();
      const reversedTwice = reversed.slice().reverse();
      return JSON.stringify(arr) === JSON.stringify(reversedTwice);
    })
  );
});
```

**公式リポジトリ**: https://github.com/dubzzz/fast-check

### 6.4 Rust: proptest

**特徴**:
- Rustの所有権システムと相性が良い
- Hypothesisに触発されて開発
- 型安全性を活かした設計

**使用例**:
```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_reverse_twice(ref v in prop::collection::vec(any::<i32>(), 0..100)) {
        let mut v2 = v.clone();
        v2.reverse();
        v2.reverse();
        assert_eq!(v, &v2);
    }
}
```

**公式リポジトリ**: https://github.com/proptest-rs/proptest

### 6.5 その他の言語

**Erlang/Elixir: PropEr**:
- Erlangの並行システムテストに特化
- 状態ベースPBTの強力なサポート

**Java: jqwik**:
- JUnit 5上で動作
- アノテーションベースの記述

**C/C++: RapidCheck**:
- C++向けのQuickCheck移植
- テンプレートメタプログラミングを活用

**Scala: ScalaCheck**:
- Scalaの標準的なPBTライブラリ
- 関数型プログラミングスタイル

**F#: FsCheck**:
- .NET環境でのPBT
- QuickCheckの設計を忠実に再現

## 7. PBTと仕様の関係

### 7.1 性質は仕様である

Property-Based Testingにおける「性質」（Property）は、**実行可能な仕様**として機能する。

**仕様としての性質**:
- プログラムが満たすべき抽象的な規則を明示
- 自然言語の仕様よりも厳密で曖昧性がない
- 実行して検証可能

### 7.2 形式仕様との関係

**PBTと形式手法の比較**:

| 観点 | PBT | 形式手法（モデル検査等） |
|------|-----|--------------------------|
| 検証範囲 | ランダム生成されたケース | 全状態空間（網羅的） |
| 学習曲線 | 比較的緩やか | 急峻 |
| 実行時間 | 秒〜分 | 分〜日 |
| 反例 | 具体的な入力値 | 実行パス |
| 完全性 | 不完全（確率的） | 完全（ただし有限状態のみ） |

**相補的関係**:
- PBTは日常的な開発で使いやすい
- 形式手法は安全重要システムの重要部分に適用
- PBTで大まかに検証し、重要部分を形式手法で厳密に検証

### 7.3 契約プログラミングとの関係

**Design by Contract**との類似性:
- 事前条件・事後条件・不変条件の概念
- PBTの性質は、実行可能な契約として機能
- Eiffelの契約とQuickCheckのプロパティは相補的

### 7.4 TDDとの関係

**TDDとPBTの統合**:
- TDDのRed-Green-Refactorサイクルにプロパティテストを組み込む
- 例ベーステストで具体的なケース、プロパティテストで一般的な性質を検証
- プロパティから具体例を発見するアプローチ

## 8. 状態ベースPBT（Stateful Property-Based Testing）

### 8.1 状態ベースPBTとは

**Stateful PBT**は、状態を持つシステムに対してPBTを適用する手法である。

**基本概念**:
- システムの状態を表すモデルを定義
- 状態を変更するコマンド（操作）の列を生成
- 各ステップで、実システムとモデルの結果を比較

### 8.2 状態ベースPBTの構成要素

**1. モデル**:
- システムの状態を表すデータ構造
- 実システムの簡略化された決定論的表現

**2. コマンド**:
- 状態を変更する操作
- 実システムとモデルの両方に適用

**3. 事前条件**（Precondition）:
- コマンドが実行可能な状態の条件

**4. 事後条件**（Postcondition）:
- コマンド実行後に成立すべき条件
- 実システムとモデルの結果を比較

### 8.3 状態ベースPBTの例

**スタックのテスト**:
```python
from hypothesis.stateful import RuleBasedStateMachine, rule, precondition
import hypothesis.strategies as st

class StackMachine(RuleBasedStateMachine):
    def __init__(self):
        super().__init__()
        self.model = []  # モデル（リスト）
        self.real = Stack()  # 実システム

    @rule(value=st.integers())
    def push(self, value):
        self.model.append(value)
        self.real.push(value)

    @rule()
    @precondition(lambda self: len(self.model) > 0)
    def pop(self):
        model_result = self.model.pop()
        real_result = self.real.pop()
        assert model_result == real_result

TestStack = StackMachine.TestCase
```

### 8.4 並行テスト

**並行状態ベースPBT**:
- 複数のコマンドを並行実行
- 競合状態（Race Condition）の検出
- 線形化可能性（Linearizability）の検証

**適用例**:
- 並行データ構造（ロックフリーキュー等）
- データベーストランザクション
- 分散システムのコンセンサス

## 9. PBTとFuzzingの違い

### 9.1 基本的な違い

| 観点 | Property-Based Testing | Fuzzing |
|------|------------------------|---------|
| アプローチ | ホワイトボックス | ブラックボックス |
| プロパティ | 明示的にコードで記述 | 通常「クラッシュしない」のみ |
| 入力生成 | 構造化されたジェネレータ | ランダムまたは変異 |
| 実行時間 | 短時間（秒〜分） | 長時間（時間〜日〜週） |
| 対象 | 個別の関数・モジュール | システム全体 |

### 9.2 アプローチの違い

**Fuzzing**:
- 一般的にブラックボックス手法
- システムへの入力生成方法をあまり指示しない
- クラッシュやハングを主に検出

**Property-Based Testing**:
- システムへの深い理解を要求
- プログラマーがテストするプロパティと「興味深い」入力の大まかな形状を記述
- 任意のプロパティをテスト可能（`assert(property())`で「クラッシュしない」以外も検証）

### 9.3 相補的な利用

**統合的アプローチ**:
- PBTツールでFuzzingも実行可能
- Fuzzingで発見したクラッシュをPBTでプロパティ化
- PBTは開発中の日常的テスト、Fuzzingは長期的なセキュリティテスト

**実用的な使い分け**:
- **PBT**: 開発者が日常的に使用、反復的テスト、コード記述中のバグ発見
- **Fuzzing**: セキュリティ監査、長期実行、外部入力の堅牢性検証

## 10. PBTの限界と課題

### 10.1 初期コストと学習曲線

**マインドセットの転換**:
- PBTの開始には、考え方の転換と初期作業が必要
- 「どんなプロパティを使えばいいの？思いつかない」という共通の悩み

**プロパティの発見**:
- 適切なプロパティを見つけるには経験が必要
- すべてのコードが明確なプロパティを持つわけではない

### 10.2 計算リソース

**リソース集約的**:
- 何百万ものテストケースを自動生成・実行
- 既にリソースを消費するテストには不向き
- 複雑なセットアップ・ティアダウンが必要なテストには非効率

### 10.3 参照実装の欠如

**差分プロパティの困難さ**:
- 良好な参照実装がない場合、PBTは困難
- 特に新規アルゴリズムや独自実装の場合

### 10.4 単純なコードへの過剰適用

**軽量な代替手段**:
- コードが十分に単純で、例が振る舞いを十分に伝える場合、例ベーステストが魅力的
- PBTは万能ではない

### 10.5 型システムで保証できる性質

**静的型付けとの重複**:
- 型システムが強力な言語（Haskell、Rust等）では、多くのプロパティが型で保証される
- PBTは型では表現できない実行時の性質に集中すべき

### 10.6 非決定性の扱い

**ランダム性のあるコード**:
- ランダム性や時間依存性を持つコードのプロパティ記述は困難
- モックやシード固定等の工夫が必要

### 10.7 UIやUXのテスト

**視覚的・対話的要素**:
- ユーザーインターフェースの視覚的側面はプロパティで記述しにくい
- PBTは主にロジックのテストに適している

## 11. PBTのベストプラクティス

### 11.1 プロパティの見つけ方

**1. 不変量を探す**:
- データ構造の不変量（ツリーのバランス、リストの順序等）
- システムの制約（残高は非負、ユニークIDの重複なし等）

**2. 逆操作を探す**:
- エンコード/デコード
- シリアライゼーション/デシリアライゼーション
- 圧縮/解凍

**3. 冪等操作を探す**:
- ソート、正規化、キャッシュクリア等

**4. 参照実装と比較**:
- ナイーブだが正しい実装と最適化版を比較

**5. 数学的性質を利用**:
- 交換法則、結合法則、分配法則等

### 11.2 効果的なジェネレータ設計

**ドメイン特化型ジェネレータ**:
- 汎用的なジェネレータより、ドメイン知識を反映したジェネレータが効果的
- 無効な入力を最初から生成しない

**制約の適用**:
- 事前条件をジェネレータに組み込む
- 無駄なテストケースの削減

### 11.3 PBTと例ベーステストの併用

**ハイブリッドアプローチ**:
- 典型的なケースは例ベーステストで明示
- エッジケースと一般的な性質はPBTで検証
- リグレッションテスト: PBTで発見したバグを例ベーステストに追加

### 11.4 CI/CDへの統合

**実行時間の管理**:
- 通常のCI: 少数のケース（100-1000）で高速実行
- 夜間ビルド: 大量のケース（10000-100000）で徹底検証

**シード固定**:
- 失敗したケースのシードを記録
- 再現可能性の確保

## 12. PBTの産業応用と成功事例

### 12.1 Erlang/Elixirエコシステム

**QuickCheck for Erlang**:
- Ericsson等の通信企業で使用
- 並行システムの堅牢性検証
- 状態機械テストによるプロトコル検証

### 12.2 金融システム

**取引システムの検証**:
- 不変量（残高の保存等）の検証
- トランザクションの可逆性テスト
- 数値計算の精度検証

### 12.3 暗号・セキュリティ

**暗号プリミティブ**:
- 数学的性質の検証（群の性質等）
- ラウンドトリップ性（暗号化/復号化）
- 衝突検出（ハッシュ関数）

### 12.4 データベース

**SQLite等のデータベースエンジン**:
- クエリの等価性検証
- インデックスの一貫性
- ACID性質の検証

## 13. 最新の研究動向（2020年代）

### 13.1 AI/LLMとの統合

**LLMによるプロパティ生成**:
- ChatGPT、GitHub Copilot等がプロパティ候補を提案
- プロパティ発見の自動化

**テストケース生成の高度化**:
- LLMによる意味的に妥当な入力生成
- ドメイン知識を反映したジェネレータの自動構築

### 13.2 内部シュリンキングの普及

**最新のPBTライブラリ**:
- Hypothesis（Python）が内部シュリンキングを採用
- より効率的で実装が簡潔
- ジェネレータとシュリンキングの統合

### 13.3 PBTとFuzzingの融合

**HypoFuzz**:
- HypothesisとFuzzingを統合
- カバレッジ誘導によるテスト生成
- 長時間実行による深いバグ発見

### 13.4 並行・分散システムへの適用拡大

**分散コンセンサス**:
- Raft、Paxos等のアルゴリズム検証
- Jepsenスタイルのテストとの統合

**マイクロサービス**:
- サービス間の契約検証
- API互換性のチェック

## 14. まとめ

Property-Based Testing（PBT）は、1999年にKoen ClassenとJohn HughesがHaskellのQuickCheckライブラリとして開発した、プログラムの性質をランダム生成された大量の入力で自動検証する強力なテスト手法である。個別のテストケースを列挙する従来の例ベーステストと異なり、PBTは抽象的な性質（Property）を記述することで、少ないコードで多様なケースをカバーし、人間のバイアスによって見落とされがちなエッジケースを発見する。

**PBTの核心**:
- **性質**（Property）: プログラムが満たすべき抽象的規則
- **ジェネレータ**（Generator）: テスト入力を自動生成する機構
- **シュリンキング**（Shrinking）: 失敗した入力から最小の反例を探索

**主要なライブラリ**:
- Haskell: QuickCheck（オリジナル）
- Python: Hypothesis
- JavaScript/TypeScript: fast-check
- Rust: proptest
- Erlang/Elixir: PropEr
- その他40以上の言語に移植

**仕様との関係**:
- プロパティは実行可能な仕様として機能
- 形式手法と相補的（PBTは日常的、形式手法は安全重要部分）
- 契約プログラミング、TDDとの統合が可能

**状態ベースPBT**:
- 状態を持つシステムのテスト
- モデルベーステスト
- 並行システムの競合状態検出

**PBTとFuzzingの違い**:
- PBT: 構造化された入力生成、明示的なプロパティ、短時間実行
- Fuzzing: ランダムな入力、主にクラッシュ検出、長時間実行

**限界と課題**:
- プロパティ発見の難しさ
- 学習曲線
- 計算リソースの消費
- 参照実装の必要性

**最新動向**（2020年代）:
- LLMによるプロパティ生成支援
- 内部シュリンキングの普及
- Fuzzingとの融合（HypoFuzz等）
- 分散システムへの適用拡大

Property-Based Testingは、仕様記述の一形態として、また実用的なテスト手法として、ソフトウェア開発における品質保証の重要なツールである。例ベーステストや形式手法と組み合わせることで、より堅牢で信頼性の高いソフトウェアの開発が可能になる。

---

## 参考文献・情報源

### QuickCheck・歴史
- [QuickCheck - Wikipedia](https://en.wikipedia.org/wiki/QuickCheck)
- [QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs - ACM ICFP 2000](https://dl.acm.org/doi/10.1145/351240.351266)
- [QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs (PDF)](https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf)
- [QuickCheck Paper - Alastair Reid](https://alastairreid.github.io/RelatedWork/papers/claessen:icfp:2000/)
- [(PDF) QuickCheck - ResearchGate](https://www.researchgate.net/publication/2449938_QuickCheck_A_Lightweight_Tool_for_Random_Testing_of_Haskell_Programs)
- [Experiences with QuickCheck: Testing the Hard Stuff and Staying Sane - John Hughes](https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quviq-testing.pdf)
- [QuickCheck: a lightweight tool for random testing - Semantic Scholar](https://www.semanticscholar.org/paper/QuickCheck:-a-lightweight-tool-for-random-testing-Claessen-Hughes/75d28729e96691eb85ae2b34e791473a24062ce5)
- [QuickCheck Testing for Fun and Profit - Springer](https://link.springer.com/chapter/10.1007/978-3-540-69611-7_1)

### 入門・概要
- [Introduction to Property Based Testing](https://alperenkeles.com/posts/introduction-to-property-based-testing/)
- [Property-based Testing With QuickCheck - Typeable](https://typeable.io/blog/2021-08-09-pbt.html)
- [The sad state of property-based testing libraries](https://stevana.github.io/the_sad_state_of_property-based_testing_libraries.html)
- [Property-based testing - UPenn](https://www.seas.upenn.edu/~cis1940/fall16/lectures/10-testing.html)
- [QuickCheck - property based testing in Haskell and JavaScript](https://www.endpointdev.com/blog/2016/03/quickcheck-property-based-testing-in/)
- [Introduction to QuickCheck1 - HaskellWiki](https://wiki.haskell.org/Introduction_to_QuickCheck1)

### シュリンキング
- [Shrinking - Property Testing](https://propertesting.com/book_shrinking.html)
- [Shrinking | Kotest](https://kotest.io/docs/proptest/property-test-shrinking.html)
- [Your own property based testing framework — Part 3: Shrinkers | Medium](https://medium.com/@nicolasdubien/your-own-property-based-testing-framework-part-3-shrinkers-564fa7a180eb)
- [Property-Based Testing in Practice - Harrison Goldstein](https://andrewhead.info/assets/pdf/pbt-in-practice.pdf)
- [Property based testing: Shrinking (part 1)](https://blog.agilogy.com/2022-08-26-pbt-shrinking-part1.html)
- [Property-based Testing #5: Shrinking Choices, Shrinking Values](https://getcode.substack.com/p/property-based-testing-5-shrinking)
- [Shrinking | ZIO](https://zio.dev/reference/test/property-testing/shrinking/)
- [Property-based testing #3: Shrinking Take One](https://getcode.substack.com/p/property-based-testing-3-shrinking)
- [The Magic of Internal Shrinking for Property Based Testing](https://www.elixirconf.eu/talks/the-magic-of-internal-shrinking-for-property-based-testing/)

### 各言語のライブラリ
- [GitHub - proptest-rs/proptest: Hypothesis-like property testing for Rust](https://github.com/proptest-rs/proptest)
- [GitHub - HypothesisWorks/hypothesis: The property-based testing library for Python](https://github.com/HypothesisWorks/hypothesis)
- [proptest - Rust](https://altsysrq.github.io/rustdoc/proptest/0.8.7/proptest/)
- [Proptest: property testing in Rust - Ivan Yurchenko](https://ivanyu.me/blog/2024/09/22/proptest-property-testing-in-rust/)
- [100% Test Coverage Is Not Enough](https://robertroskam.com/blog/100-test-coverage-is-not-enough/)
- [hypothesis - Keywords - crates.io](https://crates.io/keywords/hypothesis)

### PBTとFuzzing
- [definition of property based testing - Hypothesis](https://hypothesis.works/articles/what-is-property-based-testing/)
- [Property-Based Testing Is Fuzzing | Lobsters](https://lobste.rs/s/p1flip/property_based_testing_is_fuzzing)
- [Fuzzing vs property testing](https://www.tedinski.com/2018/12/11/fuzzing-and-property-testing.html)
- [Property-Based Testing Is Fuzzing - Made of Bugs](https://blog.nelhage.com/post/property-testing-is-fuzzing/)
- [Fuzzing vs. Property Testing | Hacker News](https://news.ycombinator.com/item?id=20279500)
- [How to Use Property-Based Testing as Fuzzy Unit Testing - InfoQ](https://www.infoq.com/news/2024/12/fuzzy-unit-testing/)
- [What Is Fuzz Testing and How Does It Work? | Black Duck](https://www.blackduck.com/glossary/what-is-fuzz-testing.html)

### 状態ベースPBT
- [GitHub - jmid/pbt-frameworks: An overview of property-based testing functionality](https://github.com/jmid/pbt-frameworks)
- [Model-based Testing | Stateful and Model-based Properties](https://johanneslink.net/model-based-testing/)
- [Property-based Testing in Java: Stateful Testing](https://blog.johanneslink.net/2018/09/06/stateful-testing/)
- [property-based-testing-stateful-systems - GitHub](https://github.com/symbiont-io/property-based-testing-stateful-systems/blob/main/README.md)
- [property-based-testing-stateful-systems-tutorial - GitHub](https://github.com/stevana/property-based-testing-stateful-systems-tutorial)
- [Introduction to Stateful Property Based Testing - Lambda Days 2019 - InfoQ](https://www.infoq.com/news/2019/08/lamda-days-2019-stateful-pbt/)
- [Stateful Property-Based Testing in Action](https://blog.aqd.is/2021/07/liar-pbt)
- [Property Testing Stateful Code in Rust | Lobsters](https://lobste.rs/s/1aamnj/property_testing_stateful_code_rust)
- [Stateful Testing — Brownie documentation](https://eth-brownie.readthedocs.io/en/stable/tests-hypothesis-stateful.html)
- [Stateful Properties - Property Testing](https://propertesting.com/book_stateful_properties.html)

### 日本語資料
- [プロパティベーステストをやってみよう #TypeScript - Qiita](https://qiita.com/kiwa-y/items/354744ef7393d07a8928)
- [コードは仕様と一致していますか？ 〜プロパティベーステストで「正しさ」を測定する〜 | AWS ブログ](https://aws.amazon.com/jp/blogs/news/property-based-testing/)
- [「実践プロパティベーステスト」を読んで - Zenn](https://zenn.dev/rescuenow/articles/75b40ced2bc254)
- [Property based testing を試してみよう - Qiita](https://qiita.com/freddiefujiwara/items/e345f4a0610bf08deea7)
- [Goにproperty based testingを布教したい - k.dev](https://kdotdev.com/kdotdev/go-pbt-testing)
- [Kotlin と jqwik で Property Based Testing - Zenn](https://zenn.dev/msksgm/articles/20221006-kotlin-property-based-testing-with-jqwik)
- [fast-check を通して Property Based Testing について理解する - Zenn](https://zenn.dev/cloud_ace/articles/b020c9969effa3)

### 限界・ベストプラクティス
- [Property testing - Wikipedia](https://en.wikipedia.org/wiki/Property_testing)
- [Property-based Testing | Kotest](https://kotest.io/docs/proptest/property-based-testing.html)
- [In praise of property-based testing – Increment: Testing](https://increment.com/testing/in-praise-of-property-based-testing/)
- [Property-based testing - how it works and when to use it - Antithesis](https://antithesis.com/resources/property_based_testing/)
- [How Property Based Testing helps - Richard Seidl](https://www.richard-seidl.com/en/blog/propertybased-testing)
- [The Beginner's Guide to Property-based Testing](https://www.thesoftwarelounge.com/the-beginners-guide-to-property-based-testing/)
- [What is Property-based Testing? | Mayhem](https://www.mayhem.security/blog/what-is-property-based-testing)
- [Choosing properties for property-based testing | F# for fun and profit](https://fsharpforfunandprofit.com/posts/property-based-testing-2/)
- [Testing across a Large Number of Inputs with Property-Based Testing - InfoQ](https://www.infoq.com/news/2023/07/property-based-testing/)

---

**調査担当**: researcher-19
**調査日**: 2026年2月
**文字数**: 約5,100字
