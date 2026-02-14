# 契約プログラミングとDesign by Contract

## 概要

契約プログラミング（Contract Programming）またはDesign by Contract（DbC）は、ソフトウェアの正確性と頑健性を高めるための体系的なソフトウェア設計手法である。バートランド・メイヤー（Bertrand Meyer）によって提案され、Eiffelプログラミング言語の中核機能として実装された。DbCは、クラスやメソッドの振る舞いを形式的に定義し、ソフトウェアコンポーネント間の契約を明示的にすることで、プログラムの信頼性を向上させることを目的とする。

契約プログラミングの基本思想は、ソフトウェアモジュール間の関係をビジネス契約のメタファーで表現することである。契約は供給者（サプライヤ）と顧客（クライアント）の間の相互義務を定義し、それぞれが果たすべき責任と享受すべき利益を明確化する。

## 1. 契約プログラミングの三本柱

契約プログラミングは三つの主要な契約要素から構成される。

### 1.1 事前条件（Precondition）

事前条件は、メソッドが実行される前に成立していなければならない条件を定義する。

**特徴:**
- クライアントの義務であり、供給者の利益である
- 事前条件を満たさない状態でメソッドが呼び出された場合、供給者は正しい動作を保証する必要がない
- 事前条件のチェックにより、供給者は条件外のケースを処理する負担から解放される

**例（Eiffel）:**
```eiffel
deposit(amount: INTEGER)
    require
        amount > 0  -- 預金額は正の値でなければならない
    do
        balance := balance + amount
    ensure
        balance = old balance + amount
    end
```

### 1.2 事後条件（Postcondition）

事後条件は、メソッドが実行された後に成立していることが保証される条件を定義する。

**特徴:**
- 供給者の義務であり、クライアントの利益である
- メソッドの実行結果に対する特定の性質を保証する
- `old`キーワードを使用して、メソッド実行前の状態を参照できる

**メリット:**
- メソッドの効果が明確になる
- 実装の正確性を検証できる
- クライアントが安心してメソッドを利用できる

### 1.3 クラス不変条件（Class Invariant）

クラス不変条件は、クラスのオブジェクトが常に満たすべき条件を定義する。

**特徴:**
- オブジェクトの生成後に成立する
- すべての公開メソッドの実行前と実行後に成立する
- オブジェクトの内部状態の一貫性を保証する

**検証タイミング:**
- コンストラクタの実行後
- 公開メソッドの実行前（メソッド呼び出し時）
- 公開メソッドの実行後（メソッド終了時）

**例（Eiffel）:**
```eiffel
class BANK_ACCOUNT
invariant
    balance >= 0  -- 残高は常に非負である
end
```

クラス不変条件は最も強力な契約形式だが、頻繁にチェックされるため最もコストが高い。

## 2. 契約の基本原則

### 2.1 契約の原則

クラス不変条件**かつ**事前条件が真である状態でクライアントが供給者を呼び出した場合、サービスの完了後には不変条件**かつ**事後条件が真になる。

この原則は以下の論理式で表現できる:

```
{Invariant ∧ Precondition} Operation {Invariant ∧ Postcondition}
```

### 2.2 責任の分離

契約プログラミングは、エラーチェックの責任を明確に分離する:

- **事前条件の確保**: クライアントの責任
- **事後条件の確保**: 供給者の責任
- **不変条件の維持**: クラス自身の責任

この責任分離により、防御的プログラミングで見られる冗長なチェックを排除できる。

## 3. 契約と継承：リスコフの置換原則

### 3.1 リスコフの置換原則（Liskov Substitution Principle）

リスコフの置換原則は、「派生型（サブクラス）はその基底型（スーパークラス）と置換可能でなければならない」という原則である。契約プログラミングとの関連において、この原則は契約継承の具体的なルールを定義する。

### 3.2 契約継承のルール

サブクラスでメソッドをオーバーライドする際、以下のルールに従わなければならない:

#### 事前条件の弱化（Weakening of Preconditions）

**ルール**: サブクラスの事前条件は、スーパークラスの事前条件と同じか、それより**弱く**なければならない。

**理由**: クライアントはスーパークラスの契約に基づいてコードを書いている。サブクラスが事前条件を強化すると、スーパークラスで有効だった呼び出しがサブクラスでは無効になり、置換可能性が破綻する。

**例:**
```
スーパークラス: require amount > 0
サブクラス: require amount >= 0  -- より弱い条件（許容）
サブクラス: require amount > 100 -- より強い条件（禁止）
```

#### 事後条件の強化（Strengthening of Postconditions）

**ルール**: サブクラスの事後条件は、スーパークラスの事後条件と同じか、それより**強く**なければならない。

**理由**: クライアントはスーパークラスの事後条件が提供する保証に依存している。サブクラスはより多くの保証を提供できるが、保証を弱めることはできない。

**例:**
```
スーパークラス: ensure result > 0
サブクラス: ensure result > 0 and result is_prime  -- より強い条件（許容）
サブクラス: ensure result >= 0  -- より弱い条件（禁止）
```

#### クラス不変条件の維持

**ルール**: サブクラスはスーパークラスのすべての不変条件を満たさなければならない。加えて、独自の不変条件を追加できる。

サブクラスの不変条件 = スーパクラスの不変条件 **∧** サブクラス固有の不変条件

### 3.3 共変性と反変性

契約継承のルールは、型理論における共変性（covariance）と反変性（contravariance）の概念と対応している:

- **事前条件**: 反変的（contravariant）- より広い入力を受け入れる
- **事後条件**: 共変的（covariant）- より限定された出力を生成する

## 4. 各言語における契約機能

### 4.1 Eiffel

**歴史**: Design by Contractの発祥地であり、最も完全な実装を持つ。

**機能:**
- `require`（事前条件）、`ensure`（事後条件）、`invariant`（クラス不変条件）のネイティブサポート
- `old`キーワードによるメソッド実行前の状態参照
- 契約の継承に関する完全なサポート

**例:**
```eiffel
class STACK[G]
invariant
    count >= 0
    count <= capacity

feature
    push(item: G)
        require
            not is_full
        do
            -- 実装
        ensure
            count = old count + 1
            top = item
        end
end
```

### 4.2 Ada/SPARK

**Ada 2012**: 契約ベースプログラミングのネイティブサポートを導入。

**機能:**
- `Pre`（事前条件）と`Post`（事後条件）をアスペクト構文で記述
- サブプログラムの契約を形式的に定義

**SPARK**: Adaのサブセットで、契約を静的検証に利用。

**特徴:**
- コンパイル時に契約が証明できる
- 形式検証ツール（SPARK Pro）により契約違反を事前に検出
- 安全性が重視される航空宇宙・防衛分野で使用

**例:**
```ada
procedure Deposit(Account : in out Bank_Account; Amount : in Money)
    with Pre  => Amount > 0,
         Post => Account.Balance = Account.Balance'Old + Amount;
```

### 4.3 D言語

**機能:**
- `in`ブロック（事前条件）、`out`ブロック（事後条件）、`body`ブロック（実装）の明確な分離
- `invariant()`による構造体とクラスの不変条件定義
- `out(result)`による戻り値の検証

**特徴:**
- すべての契約はリリースビルドで削除される
- クラス不変条件は継承される（基底クラスと派生クラスの不変条件の論理積）

**例:**
```d
class BankAccount {
    private double balance;

    invariant {
        assert(balance >= 0);
    }

    void deposit(double amount)
    in {
        assert(amount > 0);
    }
    out {
        assert(balance >= 0);
    }
    body {
        balance += amount;
    }
}
```

### 4.4 Java Modeling Language (JML)

**概要**: Javaのための仕様記述言語で、Eiffelの契約プログラミングとLarch系列の仕様言語を組み合わせたもの。

**機能:**
- `//@ requires`（事前条件）、`//@ ensures`（事後条件）、`//@ invariant`（不変条件）
- Java注釈コメント内に記述するため、通常のJavaコンパイラで処理可能

**ツール:**
- `jmlc`: JML注釈を実行時アサーションに変換するコンパイラ
- `jmldoc`: JML情報を含むドキュメント生成
- `jmlunit`: JML注釈からJUnitテストコードを生成
- ESC/Java: 拡張静的チェッカー

**例:**
```java
public class BankAccount {
    private /*@ spec_public @*/ double balance;

    //@ invariant balance >= 0;

    //@ requires amount > 0;
    //@ ensures balance == \old(balance) + amount;
    public void deposit(double amount) {
        balance += amount;
    }
}
```

**現状**: 2026年1月時点でもJMLリファレンスマニュアルは作業中であり、言語仕様は継続的に議論・改善されている。

### 4.5 C# Code Contracts

**概要**: Microsoftが開発した.NET Framework向けの契約プログラミングライブラリ。

**機能:**
- `System.Diagnostics.Contracts`名前空間のクラス群
- `Contract.Requires`（事前条件）、`Contract.Ensures`（事後条件）、`Contract.Invariant`（不変条件）

**ツール:**
- **ccrewrite.exe**: 実行時チェック
- **cccheck.exe**: 静的プログラム検証
- **ccdoc.exe**: ドキュメント生成
- **Pex**: 契約を利用した自動テスト生成
- **Clousot**: 静的検証エンジン

**現状**: オープンソースプロジェクトとしてGitHubで管理されているが、.NET Coreへの完全な移行については議論が続いている。

### 4.6 Kotlin

**機能**: Kotlin 1.3で契約機能を導入（標準ライブラリでは安定、ユーザー定義では実験的）。

**特徴:**
- `require`型メソッドによる事前条件の実装（満たされない場合は`IllegalArgumentException`を投げる）
- Eiffelの契約設計パラダイムに触発された設計
- シンプルなメソッド呼び出しベースのアプローチ

**例:**
```kotlin
fun deposit(amount: Double) {
    require(amount > 0) { "Amount must be positive" }
    balance += amount
}
```

### 4.7 Racket

**特徴**: 高階契約（higher-order contracts）と依存契約（dependent contracts）をサポート。

**高階契約:**
- 関数が引数として渡される関数に対する契約も記述可能
- `(-> natural-number/c prime?)`のような契約で、自然数を素数に写像する関数を指定

**依存契約:**
- `->i`記法により、引数と結果の間の依存関係を表現
- 引数に名前を付け、その名前を事後条件で参照可能

**例:**
```racket
(define/contract (get-char s n)
  (->i ([s string?]
        [n (s) (and/c natural-number/c (</c (string-length s)))])
       [result char?])
  (string-ref s n))
```

この例では、インデックス`n`が文字列`s`の長さ未満であることを依存契約として記述している。

### 4.8 C++の契約プログラミング

**歴史**: C++20に契約機能が提案されたが、設計上の懸念から標準への導入が延期された。

**現状**: C++23以降での導入に向けて議論が続いている。

**課題:**
- 契約違反時の動作（継続、終了、未定義動作など）
- リリースビルドでの契約の扱い
- パフォーマンスへの影響

**代替手段:**
- `assert`マクロ（デバッグビルドのみ）
- サードパーティライブラリ（Boost.Contract等）

## 5. 契約の実行時検証と静的検証

### 5.1 実行時検証（Runtime Verification）

**概要**: プログラム実行時に契約条件をチェックする方法。

**メリット:**
- 実装が比較的容易
- より精密な仕様を記述可能（計算可能であれば任意の述語が使用可能）
- デバッグ時に即座にエラーを発見できる

**デメリット:**
- パフォーマンスオーバーヘッドが発生する
- すべての契約違反を検出できるわけではない（実行されたパスのみ検証）
- エラー発見が遅延する（実際に違反が発生するまで検出されない）

**標準的な実践:**
- 開発・テスト時に契約チェックを有効化
- リリースビルドでは契約チェックを無効化（`NDEBUG`マクロ等）
- これにより、開発時の安全性とリリース時のパフォーマンスを両立

**注意点**: 契約はユーザー入力の検証に使用すべきではない。契約はプログラマのバグを検出するためのものであり、外部からの不正入力に対する防御は別途実装する必要がある。

### 5.2 静的検証（Static Verification）

**概要**: コンパイル時または専用ツールにより、契約違反の可能性を解析する方法。

**メリット:**
- 実行前にバグを発見できる
- すべてのパスを網羅的に検証可能（理論上）
- 実行時のパフォーマンスオーバーヘッドがゼロ

**デメリット:**
- 状態爆発問題（state explosion problem）により、大規模システムでの完全な検証は困難
- すべての可能性を仮定するため、誤検知（false positive）が発生しやすい
- 複雑な契約の検証には高度な定理証明技術が必要

**主要ツール:**
- **SPARK Pro**: Ada/SPARKプログラムの形式検証
- **Clousot**: C# Code Contractsの静的検証エンジン
- **ESC/Java**: JMLの拡張静的チェッカー

### 5.3 ハイブリッドアプローチ

**概念**: 静的検証と動的検証を組み合わせる手法。

**戦略:**
- 静的解析で検証可能な契約は静的にチェック
- 複雑で静的解析が困難な契約は実行時にチェック

**利点:**
- 両方のアプローチの長所を活用
- 検証の精度と実用性のバランスを取る

## 6. 契約プログラミングの利点

### 6.1 エラー特定の明確化

契約により、エラーの責任所在が明確になる:
- 事前条件違反: クライアントのバグ
- 事後条件違反: 供給者のバグ
- 不変条件違反: クラス実装のバグ

この明確化により、デバッグが効率化される。

### 6.2 文書化の自動化

契約は実行可能な仕様として機能し、以下の利点をもたらす:
- コードと仕様の同期が自動的に保たれる
- 新しいチームメンバーのオンボーディングが容易になる
- APIの使用方法が明確になる

### 6.3 冗長チェックの削減

呼び出し階層において、上位で事前条件がチェックされていれば、下位の階層での重複チェックが不要になる。これにより:
- コードの重複が減少
- パフォーマンスが向上
- コードの保守性が向上

### 6.4 設計の改善

契約を考えることで、以下の設計改善が促進される:
- 責任の明確化
- インターフェースの洗練
- モジュール間の依存関係の明確化

## 7. 契約プログラミングの限界と課題

### 7.1 表現力の限界

すべての仕様を契約として表現できるわけではない:
- 複雑な時相的性質（temporal properties）
- リソース使用に関する性質
- セキュリティ特性

これらの性質には、より高度な形式手法（モデル検査、時相論理等）が必要となる。

### 7.2 パフォーマンスオーバーヘッド

実行時契約チェックは、特に性能要求が厳しいシステムでは問題となる:
- リアルタイムシステム
- 組み込みシステム
- 高性能計算

標準的な対処法は、リリースビルドで契約を無効化することだが、これによりリリース版でのバグ検出能力が失われる。

### 7.3 フレーム問題（Frame Problem）

**問題**: メソッドが「変更しない」ものを明示する必要がある。

オブジェクト指向プログラミングにおいて、メソッドがどのメモリ位置を変更しないかを知ることは、どの位置を変更するかを知ることとほぼ同じくらい重要である。これをフレーム問題と呼ぶ。

**課題:**
- すべての不変なフィールドを列挙するのは冗長
- 参照の共有により、間接的な状態変化が発生しうる
- コールバックによる再入が不変条件を無効化する可能性

**対処法:**
- Dynamic Frames技術
- クラスフレームによる分割
- Ownership型システム

### 7.4 契約と例外の相互作用

契約違反と例外処理の関係は複雑である:
- 契約違反は修復不可能なバグを示す
- 例外は回復可能なエラー状態を表す
- 両者を混同すると設計が混乱する

### 7.5 継承における複雑性

#### コールバック問題

基底クラスのコンストラクタが派生クラスのメソッドを（仮想関数経由で）呼び出した場合、派生クラスの不変条件がまだ確立されていない可能性がある。

#### 密行アクセス（Furtive Access）

オブジェクトへの参照が意図しない経路で共有されている場合、不変条件が密かに破られる可能性がある。

#### 参照リーク（Reference Leak）

オブジェクトの参照が外部に漏れると、そのオブジェクトの状態が予期しない方法で変更される可能性がある。

**実例**: 2016年のEthereum DAO攻撃では、5000万ドルが盗まれたが、これはコールバックによる不変条件の無効化が原因であった。

### 7.6 レガシーコードへの適用

既存のコードベースに契約を追加することは困難である:
- 完全な書き換えが必要になる場合がある
- 労力集約的で時間がかかる
- 安全性が絶対的に重要な分野以外では費用対効果が合わない

### 7.7 形式検証の限界

契約プログラミングのみでは形式検証は完結しない:
- ユニットテストとの組み合わせが必要
- 契約外の性質（性能、セキュリティ等）も検証する必要がある

## 8. 契約プログラミング vs 防御的プログラミング

### 8.1 防御的プログラミング

**概念**: すべての入力を疑い、あらゆる箇所で検証を行う手法。

**特徴:**
- 局所最適化アプローチ
- 「誰もルールを守っていないかもしれない」という前提
- 各モジュールが自身を防御する

**結果:**
- コードの重複率が増加
- コード総量が増加
- 複雑性が上昇
- 保守性が低下

### 8.2 契約プログラミング

**概念**: ルールを定め、内部モジュール間では相互信頼を前提とする手法。

**特徴:**
- 全体最適化アプローチ
- 信頼境界線の明確化
- 外部との境界では防御、内部では信頼

**信頼境界線:**
- **外部境界**: 何が来るか分からないため防御が必要
- **内部領域**: 同僚が開発しているため、ルール遵守を信頼

**結果:**
- コードの重複が減少
- システム全体の保守性が向上
- レイヤー間の重複が減少
- 内部品質が向上

### 8.3 実践における使い分け

**外部インターフェース**: 防御的プログラミング
- ユーザー入力の検証
- 外部APIからのデータ検証
- セキュリティチェック

**内部実装**: 契約プログラミング
- モジュール間の契約定義
- クラス階層内の契約
- チーム内のコード規約

## 9. 契約プログラミングの実践事例

### 9.1 成功事例

**Eiffelコミュニティ**: 多数の信頼性の高いソフトウェアシステムを構築。特に以下の分野で成功:
- 金融システム
- 医療機器ソフトウェア
- 産業制御システム

**SPARK/Ada**: 航空宇宙・防衛分野での広範な採用:
- 航空機制御システム
- 衛星ソフトウェア
- 軍事システム

### 9.2 失敗事例からの教訓

**PHP6の失敗**: 契約プログラミングの概念が欠如していたため、Unicode対応を目指したPHP6の開発が失敗。言語が自動的に処理を保証しようとした結果:
- 内部処理が複雑化
- パフォーマンスが大幅に低下
- プロジェクトが頓挫

**教訓**: 責任の所在を明確にせず、システムがすべてを自動処理しようとすると、複雑性とコストが管理不能になる。

**Ethereum DAO攻撃（2016年）**: コールバックによって不変条件が無効化され、5000万ドルが盗まれた。

**教訓**: 契約プログラミングの理論を理解するだけでなく、実装レベルでの落とし穴（コールバック、再入等）にも注意が必要。

## 10. 契約プログラミングの理論的背景

### 10.1 ホーア論理（Hoare Logic）

契約プログラミングはホーア論理に基づいている。ホーアトリプルは以下の形式で表現される:

```
{P} C {Q}
```

- **P**: 事前条件（precondition）
- **C**: プログラム（command）
- **Q**: 事後条件（postcondition）

これは「Pが真の状態でCを実行すると、終了後にQが真になる」ことを意味する。

### 10.2 最弱事前条件（Weakest Precondition）

ダイクストラの最弱事前条件計算（wp計算）は、契約プログラミングの理論的基盤を提供する:

```
wp(C, Q)
```

これは「コマンドCを実行した後に事後条件Qが成立する最弱の事前条件」を計算する。

### 10.3 リファインメント計算（Refinement Calculus）

契約プログラミングは、リファインメント計算の要素を取り入れている。これは、抽象的な仕様から具体的な実装へと段階的に洗練していく手法である。

## 11. 契約プログラミングの将来展望

### 11.1 AI/機械学習との統合

契約を学習データとして利用し、以下の可能性が研究されている:
- 契約違反の自動検出
- 契約の自動生成
- テストケースの自動生成

### 11.2 型システムとの融合

依存型（Dependent Types）や洗練型（Refinement Types）により、契約を型システムに統合する研究が進んでいる:
- Idris、Agda、Coqなどの依存型言語
- Liquid Haskellなどの洗練型システム

これにより、より多くの契約をコンパイル時に検証できるようになる。

### 11.3 契約の標準化

主流プログラミング言語（C++、Java、Python等）への契約機能の標準化が進められている。これにより:
- 契約プログラミングの普及
- ツールのエコシステムの成熟
- 教育への組み込み

## 12. まとめ

契約プログラミング（Design by Contract）は、ソフトウェアの信頼性を向上させるための強力な手法である。事前条件、事後条件、クラス不変条件の三本柱により、モジュール間の責任を明確化し、エラーの早期発見と効率的なデバッグを可能にする。

**主要な利点:**
- エラーの責任所在の明確化
- 実行可能な仕様としての文書化
- 冗長チェックの削減
- 設計品質の向上

**主要な課題:**
- 表現力の限界
- パフォーマンスオーバーヘッド
- フレーム問題
- レガシーコードへの適用の困難さ

**実践的な指針:**
- 外部境界では防御的プログラミング、内部では契約プログラミングを使い分ける
- 開発時には契約チェックを有効化、リリース時には最適化する
- 契約を単独で使うのではなく、テストや他の検証手法と組み合わせる

契約プログラミングは、形式手法と実用的なプログラミングの橋渡しとして、仕様と実装の一貫性を保つための重要な技術である。特に安全性・信頼性が重視される分野では、必須の技術となっている。今後、型システムとの統合やAIとの組み合わせにより、さらに強力で実用的な技術へと発展していくことが期待される。

## 参考文献・情報源

### 主要文献
- [契約プログラミング - Wikipedia](https://ja.wikipedia.org/wiki/%E5%A5%91%E7%B4%84%E3%83%97%E3%83%AD%E3%82%B0%E3%83%A9%E3%83%9F%E3%83%B3%E3%82%B0)
- [Design by contract - Wikipedia](https://en.wikipedia.org/wiki/Design_by_contract)
- [Design By Contract - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/design-by-contract)
- [Chapter 1 Design by Contract - Bertrand Meyer](https://se.inf.ethz.ch/~meyer/publications/old/dbc_chapter.pdf)

### Eiffel
- [Eiffel (programming language) - Wikipedia](https://en.wikipedia.org/wiki/Eiffel_(programming_language))
- [Bertrand Meyer: Basic Eiffel language mechanisms](https://se.inf.ethz.ch/~meyer/publications/online/eiffel/basic.html)
- [Design by Contract and Assertions - Eiffel](https://www.eiffel.org/doc/solutions/Design_by_Contract_and_Assertions)

### リスコフの置換原則
- [Liskov substitution principle - Wikipedia](https://en.wikipedia.org/wiki/Liskov_substitution_principle)
- [リスコフの置換原則 - Wikipedia](https://ja.wikipedia.org/wiki/%E3%83%AA%E3%82%B9%E3%82%B3%E3%83%95%E3%81%AE%E7%BD%AE%E6%8F%9B%E5%8E%9F%E5%89%87)
- [The Liskov Substitution Principle | Microsoft Press Store](https://www.microsoftpressstore.com/articles/article.aspx?p=2255313&seqNum=2)
- [リスコフの置換原則（LSP）と契約による設計（DbC）の関連について - Qiita](https://qiita.com/hiko1129/items/9b3066feffabccf83c16)

### Ada/SPARK
- [Design by contracts - learn.adacore.com](https://learn.adacore.com/courses/intro-to-ada/chapters/contracts.html)
- [Studies of Contracts in Practice - The AdaCore Blog](https://blog.adacore.com/studies-of-contracts-in-practice)
- [SPARK (programming language) - Wikipedia](https://en.wikipedia.org/wiki/SPARK_(programming_language))
- [Ada Programming/Contract Based Programming - Wikibooks](https://en.wikibooks.org/wiki/Ada_Programming/Contract_Based_Programming)

### D言語
- [契約プログラミング - D言語ツアー](https://tour.dlang.org/tour/ja/gems/contract-programming)
- [Contract Programming - Dlang Tour](https://tour.dlang.org/tour/en/gems/contract-programming)
- [Contract Programming - D Programming Language](https://dlang.org/spec/contracts.html)
- [Programming in D - Contract Programming for Structs and Classes](https://ddili.org/ders/d.en/invariant.html)

### JML
- [Java Modeling Language - Wikipedia](https://en.wikipedia.org/wiki/Java_Modeling_Language)
- [The Java Modeling Language (JML) Home Page](https://cs.ucf.edu/~leavens/JML/index.shtml)
- [Formal Specification with the Java Modeling Language](https://www.cse.chalmers.se/~ahrendt/papers/JML16chapter.pdf)

### C# Code Contracts
- [Code Contracts - .NET Framework | Microsoft Learn](https://learn.microsoft.com/en-us/dotnet/framework/debug-trace-profile/code-contracts)
- [GitHub - microsoft/CodeContracts](https://github.com/microsoft/CodeContracts)
- [Code Contracts - Microsoft Research](https://www.microsoft.com/en-us/research/project/code-contracts/)

### Racket
- [7 Contracts - Racket Guide](https://docs.racket-lang.org/guide/contracts.html)
- [7.4 Contracts: A Thorough Example](https://docs.racket-lang.org/guide/contracts-first.html)

### C++
- [契約に基づくプログラミング - cpprefjp](https://cpprefjp.github.io/lang/future/contract-based_programming.html)
- [C++における契約プログラミング機能のこれまでとこれから](https://onihusube.hatenablog.com/entry/2023/12/25/220134)

### 実装と検証
- [契約プログラミング 実行時検証 静的検証](https://ja.wikipedia.org/wiki/%E5%A5%91%E7%B4%84%E3%83%97%E3%83%AD%E3%82%B0%E3%83%A9%E3%83%9F%E3%83%B3%E3%82%B0)
- [Design by contract - Wikipedia (Runtime verification)](https://en.wikipedia.org/wiki/Design_by_contract)
- [Design by Contract for Embedded Software](https://www.state-machine.com/dbc)

### 防御的プログラミングとの比較
- [防御的プログラミングと契約プログラミング - よしたろうブログ](https://yoshitaro-yoyo.hatenablog.com/entry/2022/08/07/On_Defensive_and_Contract_Programming)
- [防御的プログラミングと契約プログラミング - Qiita](https://qiita.com/yoshitaro-yoyo/items/bb8cc631276380b68c13)
- [エンジニア必須の概念 – 契約による設計と信頼境界線](https://blog.ohgaki.net/design-by-contract-and-trust-boundary)

### フレーム問題とクラス不変条件
- [The Concept of Class Invariant in Object-oriented Programming](https://arxiv.org/abs/2109.06557)
- [The Concept of Class Invariant - ACM](https://dl.acm.org/doi/10.1145/3626201)
- [Verification of object-oriented programs with invariants](https://courses.cs.washington.edu/courses/cse503/10wi/readings/boogie-methodology.pdf)

### 実践と応用
- [【契約による設計】あなたのプログラムが守るべき３つの約束](https://plainprogram.com/design-by-contract/)
- [契約プログラミングとは？意味をわかりやすく解説](https://trends.codecamp.jp/blogs/media/terminology275)
- [契約による設計・契約プログラミングが少しワカッタ - Neo's World](https://neos21.net/blog/2019/10/05-01.html)
