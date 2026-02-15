# UAD/fにおける根仕様統制の二演算意味論: `U0`(join) と `U∧`(meet) の形式化

## 0. 問題設定と研究目的
### 0.1 問題設定
本稿が対象とする問題は、**多層防御における仕様統制の困難性**である。  
ここで「層」とは、要求仕様・API仕様・型・契約・テスト・実装など、異なる抽象度で記述された仕様アーティファクトを指す。  
各層 `i` は root 空間 `Ω` から層空間 `β_i` への部分射影 `proj_i : Ω → Option β_i` により接続される（詳細は §2）。
要求仕様、API仕様、型、契約、テスト、実装はそれぞれ局所的には正しさを主張できるが、層が独立に進化すると全体として次が起きる。

1. 層間矛盾: 例として同一制約（パスワード長など）が層ごとに食い違う
2. 保証の隙間: 個別手法は通っても、層横断の整合が未検証のまま残る
3. 変更波及の断絶: 上位仕様変更が下位層へ一貫して反映されない

すなわち問題は、多様な保証手法を横断して統制するための共通基準が欠けることである。

本稿の立場は、**根仕様（root の完全仕様）を人間が網羅的・無矛盾に直接記述することは現実的でない**、という点にある。  
したがって根 `U` は「先に与える対象」ではなく、層と root を結ぶ部分射影 `f_{0i}`（`proj_i`）から逆像で**構成する対象**として扱う。

導入例（同一意図の層別表現）:
- アプリ層: 「データAを取得する」
- API層: 「システムAのAPIを呼び出して取得する」
- HTTP層: 「`GET /A`」
- 通信層: 「接続・再送・順序制御」

同じ意図が層ごとに異なる記述として現れるため、層間比較の共通基準を root 側で構成する必要がある。

### 0.2 研究目的
本稿の到達目標は次の3点である。

1. 多層仕様統制の最小核として `U,D,A,f` を型付きで定義し、root を「記述」ではなく「射影逆像で構成」する形式を与える。
2. 運用上の2用途を分離する。  
   - 変更影響や被覆合成（over-approximation）のための join 演算（`U0`）  
   - 同時満足・矛盾判定のための meet 演算（`U∧`）
3. Lean4で中核定理を機械検証し、実アーティファクト抽出パイプラインの再実行可能性を示す。

### 0.3 貢献範囲
- 研究者: 暗黙仮定（随伴の成立、層間伝播仮定、抽出同値仮定）を明示し、議論可能にする。
- 実務者: `U0`（被覆合成 / over-approximation）と `U∧`（同時満足）の使い分け定義、および抽出パイプライン技術的実行可能性のPoCを得る（一般適用性は未評価）。
- 再現性: Lean証明・抽出スクリプト・ソースロックを同梱し、第三者検証可能にする。
- 評価範囲: 実OSS評価は convenience sample（`n=3`）による PoC であり、母集団推定を目的としない。

## 1. 研究課題（RQ）
本稿のRQは、上記の統制課題を「定義可能性」「証明可能性」「再現可能性」に分解したものである。

- `RQ1`: 層ごと異型 (`carrier : I → Type`) でも一貫した逆像定義を与えられるか。
- `RQ2`: `A(i) ⊆ D(i)` を root 側の証人妥当性に持ち上げられるか。
- `RQ3`: join側 (`U0`) と meet側 (`U∧`) を同一モデル上で整合的に定義できるか。
- `RQ4`: 層間伝播・層間合成の仮定を型付きで明示し、機械検証できるか。
- `RQ5 (theory)`: 抽象抽出関係 `E : Ω → β_i → Prop` に対し、抽出適合を `↔` だけでなく one-sided（sound / complete）にも分解できるか。
- `RQ6 (practice)`: 実OSSアーティファクト抽出パイプラインの**技術的再実行可能性**を確保できるか。

### 1.1 評価軸
| 軸 | 内容 | 指標 |
|---|---|---|
| 定義妥当性 | 型整合・記法整合 | §2, §3 と `paper/lean/UadfU0/Definitions/Model.lean` |
| 理論妥当性 | RQ対応定理 | §4 の中核定理群 |
| 非自明性 | Lean化で顕在化した欠落仮定 | §5（設計判断1〜4） |
| 再現可能性 | build/抽出再実行性 | §7.3, §7.4 |
| 抽出パイプライン実行可能性デモ | source-lock 付き再実行（PoC限定: n=3, 数値境界制約のみ, 抽出正当性は対象外） | §6.2（3 OSS, source-lock 再実行） |

## 2. 型付き UAD/f モデル（自己完結定義）
### 2.1 記法表
| 数学記法 | Lean実装 | 意味 |
|---|---|---|
| `Ω` | `α` | ルート空間 |
| `I` | `ι` | 層インデックス |
| `β_i` | `M.carrier i : Type w` | 層 `i` の搬送型（`carrier : ι → Type w` の `i` への適用結果） |
| `D_i` | `D i : SpecSet (carrier i)` | 層 `i` の対象領域 |
| `A_i` | `Ui i : SpecSet (carrier i)` | 層 `i` の許容集合 |
| `f_{0i}` | `proj i : Ω → Option β_i` | 部分射影 |

本文では数学記法 `A(i)` を用い、Lean実装名 `Ui i` に対応づける。

`D(i)` を分離する理由:
- `carrier i` は型レベルの対象空間全体を表し、`D(i)` はその上の対象領域述語（値レベル制約）を表す。
- `A(i)` だけでは「仕様が語る対象範囲（`D(i)`）」と「その範囲内で許容される条件（`A(i)`）」が混在する。
- `A(i) ⊆ D(i)` を明示することで、root 側証人が `carrier i` のうち domain 述語 `D(i)` を満たすこと（RQ2）を定理として追跡できる。
- 実アーティファクト抽出でも、境界値・単位・包含性の前提を `D(i)` 側に置き、`A(i)` は許容条件に限定できる。
- ただし §6.2 の現行抽出デモは `A(i)` 候補生成に主眼があり、`D(i)` 分離の実運用実証までは到達していない（限界 §9）。

### 2.2 逆像の誘導定義
\[
f^{-1}_{0i}(S)
:= \{x\in Ω \mid \exists y\in β_i,\ proj_i(x)=some(y) \land y\in S\}
\]

Lean（`paper/lean/UadfU0/Definitions/Model.lean`）:

```lean
def preimage (M : Model ι α) (i : ι) (S : SpecSet (M.carrier i)) : SpecSet α :=
  fun x => ∃ y : M.carrier i, M.proj i x = some y ∧ y ∈ S
```

### 2.3 順序の固定（定理語彙の一意化）
本稿で join / meet / LUB / GLB と呼ぶときの順序は、**包含順序 `⊆` のみ**とする。

1. join（最小上界） = `∪`
2. meet（最大下界） = `∩`

仕様の強弱は補助的な直観として扱う。  
許容集合が大きい仕様ほど弱く、小さい仕様ほど強い。  
この意味で `U0`（`∪`）は各層を被覆する over-approximation であり、`U∧`（`∩`）は同時満足を与える。

### 2.4 Lean 記述抜粋（定義と定理）
```lean
def lifted (M : Model ι α) (i : ι) : SpecSet α :=
  M.preimage i (M.Ui i)

def U0 (M : Model ι α) : SpecSet α :=
  fun x : α => ∃ i : ι, x ∈ M.lifted i

def UAndOn (active : ι → Prop) : SpecSet α :=
  fun x : α => ∀ i : ι, active i → x ∈ M.lifted i

theorem UAndOn_antitone {J K : ι → Prop}
    (hJK : ∀ i : ι, J i → K i) :
    M.UAndOn K ⊆ M.UAndOn J
```

### 2.5 `Ω`（root空間）の実務的解釈
`Ω` は「誰かが完全列挙した実体集合」ではなく、層横断比較のための意味領域（挙動宇宙）として置く。  
実務上は次の近似で扱える。

1. テストやシミュレーションで生成可能な挙動集合
2. ログ/トレースとして観測される挙動集合
3. IR制約から構成される候補挙動集合

本稿が必要とするのは `Ω` の全列挙ではなく、`x ∈ lifted(i)` の membership 判定を定義できることである。

### 2.6 NL入口と中間表現（IR）
実務では自由記述自然言語（NL）を入口から排除できない。  
本稿は NL を禁止せず、次の分離で扱う。

1. 生テキスト（NL）は証拠・説明として保持する。
2. 形式判定に使うのは `β_req` 上の中間表現（IR）とする。
3. 抽出器（規則ベース/LLM含む）は NL→IR の候補生成器（`A(i)` 候補生成器）として扱う。
4. IR項目には原文スパン（引用位置）を保持し、抽出結果の追跡性を確保する。
5. 抽出器の正当性は `RQ5 (theory)` の one-sided adequacy（sound / complete）で管理する。

したがって、本稿モデルは「NLを直接形式意味に同一視する」のでなく、「NL入口を許容しつつ、IR層で機械検証に接続する」立場である。

## 3. `U0` と `U∧` の役割分離
### 3.1 join側（被覆合成）
\[
lifted(i) := f^{-1}_{0i}(A(i)),\quad
U0 := \bigcup_{i\in I} lifted(i)
\]

`U0` は「どれかの層で許容される root 状態」の集合であり、包含順序 `⊆` での join（最小上界）である。  
ゆえに `U0` は各層を被覆する over-approximation であり、仕様強弱の直観では各層より弱い（許容集合が大きい）統合として解釈する。

運用ミニシナリオ（変更波及の説明）:
1. 新規層 `k` を追加したとき、`U0` は被覆集合として追跡対象を保ちやすい。
2. 同時に `U∧` が空になれば、「新規層の制約追加で既存層との同時満足が崩れた」と診断できる。
3. このとき `U0` と `U∧` の差分は「被覆は維持されるが同時満足が壊れた」ことを示し、調停対象層の局所化に使える。

### 3.2 meet側（同時満足統合）
有効層集合 `active : I → Prop` に対し
\[
U^\wedge_{active}(x) := \forall i,\ active(i) \to x\in lifted(i)
\]

Lean:
- `UAndOn` / `UAnd`: `paper/lean/UadfU0/U0Spec/Construction.lean`
- GLB定理群: `paper/lean/UadfU0/U0Spec/Minimality.lean`

### 3.3 join と meet の接続
整合/矛盾は以下で定義する。
\[
Consistent(i,j) :\Leftrightarrow \exists x,\ x\in lifted(i)\land x\in lifted(j)
\]
\[
Contradictory(i,j) :\Leftrightarrow \forall x,\ x\in lifted(i)\to x\in lifted(j)\to False
\]

- `UAndOn_subset_U0On`: 非空な `active` では `U∧ ⊆ U0`。
- `consistent_iff_exists_UAndOn_pair`: 2層整合は「その2層に対する `U∧` の非空性」と同値。
- `UAndOn_antitone`: `active` を増やすと `U∧` は反単調に小さくなる（要件が厳しくなる）。
- `UAndOn_empty_eq_univ`: `active=∅` では vacuous truth により `U∧=Ω` となるため、運用上は `∃i, active i` を要求する。

これにより、`U0`（OR）と整合性判定（AND）を別演算として明示し、意味論的混線を解消する。

## 4. 中核定理（主結果）
本稿の主結果は「定義展開で終わる補題」より、以下の仮定明示型定理を中心に置く。

### 4.1 層間伝播の十分条件（同一点 `x` の連結仮定）
`R : β_i → β_j → Prop` とし、次を仮定する。

1. (`hproj` in Lean) `∀ x yj, proj_j x = some yj → ∃ yi, proj_i x = some yi ∧ R yi yj`
2. (`hA` in Lean) `∀ yi yj, R yi yj → yj∈A(j) → yi∈A(i)`

このとき `lifted(j) ⊆ lifted(i)`。

Lean: `lifted_transfer` in `paper/lean/UadfU0/InterLayer/Transfer.lean`。

### 4.2 層間合成則（`pullbackVia` を明示）
`g : β_i → Option β_j`（`β_i` から `β_j` への部分写像）に対して
\[
pullbackVia_g(S) := \{yi \mid \exists yj,\ g(yi)=some(yj)\land yj\in S\}
\]

`∀ x, proj_j x = Option.bind (proj_i x) g` なら
\[
f^{-1}_{0j}(S)=f^{-1}_{0i}(pullbackVia_g(S)).
\]

Lean: `preimage_compose` in `paper/lean/UadfU0/InterLayer/Composition.lean`。

### 4.3 抽出適合の one-sided 分解
`E : Ω → β_i → Prop` に対し、次を機械検証した。

- Soundnessのみ: `preimage ⊆ semanticPullback`
  - Lean: `preimage_subset_semanticPullback_of_sound`
- Completenessのみ: `semanticPullback ⊆ preimage`
  - Lean: `semanticPullback_subset_preimage_of_complete`
- 両方向成立時: `preimage = semanticPullback`
  - Lean: `preimage_eq_semanticPullback`

これにより、`proj_i(x)=some(y) ↔ E(x,y)` の強仮定を分解し、現実抽出器への接続を段階化した。
ここでの `E` は抽象関係であり、regex 抽出器の意味保存性をこの節で証明したことを意味しない。

運用上の帰結:
- 偽陽性（存在しない整合を報告）を避ける側に効くのは soundness 側 (`preimage ⊆ semanticPullback`) である。
- 偽陰性（見逃し）を避ける側に効くのは completeness 側 (`semanticPullback ⊆ preimage`) である。
- `U∧` の空判定でどちらの側を安全性基準に置くかは運用要件に依存するため、判定ポリシー（偽陽性抑制 / 偽陰性抑制）を先に固定する必要がある。

### 4.4 部分射影下での非随伴性
`∃x0, proj_i(x0)=none` なら、`preimage_i` は冪集合上の左随伴を持たない。

Lean: `no_left_adjoint_of_partial` in `paper/lean/UadfU0/RelatedWork/Galois.lean`。

これは「逆像なら常に随伴がある」という暗黙仮定を否定し、部分性を含むモデルで追加仮定が必要であることを示す。

### 4.5 meet側のGLB特性
- `UAndOn_lower_bound`
- `below_UAndOn_of_lower_bounds`
- `UAndOn_greatest_lower_bound_iff`

により、`U∧` が active 層の greatest lower bound であることを示した。

### 4.6 基礎補題（背景）
以下は背景補題として扱う。

- `preimage_monotone`（逆像単調性）
- `preimage_union`（逆像の和保存）
- `U0_least_upper_bound_iff`（`U0` の LUB）
- `contradictory_iff_not_consistent`（双対）

### 4.7 `proj_i(x)=none` の解釈（must / may）
本稿の `preimage` は
\[
x\in f^{-1}_{0i}(S) \iff \exists y,\ proj_i(x)=some(y)\land y\in S
\]
であり、`none` は membership 不成立として扱う（must 寄り）。

運用上は別解釈もあり得る。
- must解釈: `none` は観測不能/適用外として除外する（本稿の既定）。
- may解釈: `none` は判断保留として、矛盾断定の根拠に使わない。

どちらを採るかで `U∧` の空判定挙動が変わるため、適用時には偽陽性/偽陰性の優先方針と合わせて宣言する必要がある。

## 5. 形式化エンジニアリング上の設計判断
本稿の主たる貢献は、UAD/f 最小コアの参照 mechanization を通じて、必要仮定を明示化した点にある。
以下は本稿が初出の数学的主張であることを意図せず、UAD/f 文脈での実装可能な設計判断として提示する。

### 判断1: 「統合」の二義性を演算分離で扱う
初稿では `U0` を統合仕様と呼んでいたが、形式化により `U0` は join（OR）であり、同時満足（AND）は `U∧` として別演算であるべきことが明確化した。

### 判断2: 伝播定理には同一点連結仮定が必要
`R` だけでは不十分で、`proj_j x` と `proj_i x` を同じ root 点 `x` で結ぶ仮定（`hproj`）が必要であることが分かった。
この仮定が破れる場合、`lifted(j) ⊆ lifted(i)` の全域主張は一般に得られない。

### 判断3: 抽出適合は `↔` 一発でなく段階化する
現実抽出器では sound/complete が非対称になり得るため、one-sided inclusion を先に定理化すべきであることが明確化した。

### 判断4: 部分性は随伴構造を壊し得る
`none` が存在するだけで left adjoint が失われる。したがって、抽象解釈系の直観をそのまま移植できない。

## 6. ケーススタディ（抽出パイプライン実行可能性デモ）
### 6.1 Lean内ケース（パスワード長制約）
`paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean` で

\[
check = true \iff \exists n,\ n\in lifted(req)\cap lifted(api)\cap lifted(code)
\]

を証明した（`checkConsistent_iff_allThree`）。

このケースで主張するのは「閉形式判定式と存在証人判定の同値」であり、一般産業有効性ではない。

### 6.2 実OSS抽出パイプラインデモ（PostgreSQL / zlib / SQLite）
`paper/case-study/real_projects/external_validation.py` は以下を自動実行する。

**重要（RQ5/RQ6境界）**: 本節は `RQ6 (practice)`（技術的再実行可能性）を対象とする。  
`RQ5 (theory)` の adequacy（§4.3）で使う抽象関係 `E` について、regex抽出器が意味保存性を満たすことは本節で証明していない。

1. 公式ドキュメント/公式ソースを取得
2. 正規表現で境界値を抽出
3. `requirement / api / code` の3層制約を構成
4. 交差判定で整合性評価
5. 変異試験（`requirement.lower = upper + 1`）で矛盾検出感度を確認

**重要**: 本節の `n=3` は技術的実行可能性デモであり、矛盾発生率の推定や母集団代表性の主張を意図しない。  
選定は「3層公開・数値境界制約・URL固定取得可能」という実行要件に基づく convenience sample である。

デモ実行結果（2026-02-14）:
- `n_real_projects = 3`
- `n_real_consistent = 3`
- `n_real_contradictory = 0`
- `mutation_detected = 3 / 3`

交差区間:
| Project | lower | upper | 判定 |
|---|---:|---:|---|
| PostgreSQL identifier length | 1 | 63 | consistent |
| zlib compression level | -1 | 9 | consistent |
| SQLite page size | 512 | 65536 | consistent |

選定理由とバイアス管理:
- 3件はいずれも「要求文書・API文書・実装ソース」の3層が公開され、URL固定取得が可能な代表例として選定した convenience sample である。
- 制約種別はいずれも数値境界制約である。識別子長（言語仕様）、圧縮レベル（アルゴリズムパラメータ）、ページサイズ（ストレージ設定）という文脈の異なる3件で、同一の数値抽出処理が技術的に再実行できるかを確認する目的で選んだ。
- したがって本結果は contradiction 発生率を推定する統計研究ではなく、抽出から判定までの**パイプライン実行可能性デモ**として解釈する。
- 版固定情報（URL/SHA256/UTC時刻）は `external_validation_sources.lock.json` に記録し、結果追試で同一入力を再構成できるようにした。

入力マッピング上の仮定:
- 各プロジェクトで抽出した `lower/upper` は、運用上の入力候補として区間制約に整形する。
- 交差判定 `max(lower_i) ≤ min(upper_i)` は、3層区間制約の整合判定実装である。
- ただし本稿は regex 抽出そのものの soundness/completeness を証明していない。  
  したがって「抽出結果が `A(i)` を正しく表す」ことは未検証であり、定理4.3を本デモへ直接適用したとは主張しない。
- 明示的に言えば、regex 抽出層は本稿で証明対象ではなく、機械検証済みモデルの前段入力生成層として扱う。

### 6.3 何が分かったか（結果と解釈の分離）
- 結果: 3件とも整合、変異3件は全検出。
- 解釈: 本節が示すのは「既存仕様の不具合発見率」ではなく、**実アーティファクト抽出からJSON出力・交差判定までを source-lock 付きで再実行できること**。
- ただし抽出器自体（regex層）の正当性保証は本稿の範囲外であり、抽出 soundness/completeness は仮定として扱う。
- したがって本節は `RQ6 (practice)` の実行可能性確認を対象とし、`RQ5 (theory)` の実抽出器適用（意味保存証明）は対象外である。
- 変異試験の意味: `lower > upper` 変異は、実装した区間判定が破綻入力を検出することを確認する sanity check であり、理論の外的妥当性や現実バグ有病率を示すものではない。
- 限界: 対象は数値境界制約に限定。構造制約・時間制約は未評価。
- 運用ポリシーの目安: 偽陽性抑制を優先する場合は soundness 側、偽陰性抑制を優先する場合は completeness 側を重視して抽出器要件を定める。

### 6.4 負例（抽出揺れ）: 単位解釈ミス
本稿の数値境界系でも、抽出揺れの負例は作れる。  
例として SQLite page size で、`65536 bytes` を誤って `64 bytes` と解釈すると、要求層区間が `[512, 64]` となり空区間になる。  
このとき `U∧` 判定は空となり contradiction が発生する。

注記: 本負例は「抽出器リスクの構成的デモ」であり、実運用ログからの統計的実測値ではない。

この負例が示す点:
1. 抽出器の単位解釈ミスは、層間矛盾を人工的に発生させ得る。
2. したがって `RQ5 (theory)` の one-sided adequacy（sound / complete）管理は、実抽出器に対しても運用上不可欠である。
3. 本稿の実デモは技術的再実行可能性（RQ6）に焦点を置くため、この種の抽出意味保存評価は今後課題として分離する。

## 7. 再現可能性
### 7.1 Lean 再現
```bash
cd paper/lean
~/.elan/bin/lake build
```

### 7.2 環境と依存
- Lean4: `leanprover/lean4:v4.27.0`
- Lake: `5.0.0-src+db93fe1`
- `lean-toolchain`: `paper/lean/lean-toolchain`
- `lakefile`: `paper/lean/lakefile.lean`
- `manifest`: `paper/lean/lake-manifest.json`
- 外部パッケージ: `packages = []`（mathlib 非依存、Lean標準ライブラリのみ）
- 抽出デモスクリプト: Python標準ライブラリのみ（追加pip依存なし）
- 抽出デモのオンライン実行はネットワーク接続を要する（公式URL取得のため）

### 7.3 論理基盤の明示
- `SpecSet α := α → Prop` を採用。
- 集合外延は `set_ext`（`funext` + `propext`）で実装。
- 明示的に使用している原理は `funext` と `propext`。`open Classical` は導入していない。

### 7.4 規模と成果物
- Lean LOC: 1103
- `theorem` 宣言数: 43
- 定理内訳: 中核定理（本文§4対応）12、背景補題（定義展開・証明支援）26、具体例定理（`Examples`）5
- 構成内訳（LOC）:
  - 定義基盤 (`Definitions`): 100（9.1%）
  - 証明本体 (`U0Spec` + `InterLayer` + `RelatedWork` + `CaseStudy`): 693（62.8%）
  - 具体例 (`Examples`): 310（28.1%）
- 中核ファイル:
  - `paper/lean/UadfU0/U0Spec/Construction.lean`
  - `paper/lean/UadfU0/U0Spec/Minimality.lean`
  - `paper/lean/UadfU0/InterLayer/Transfer.lean`
  - `paper/lean/UadfU0/InterLayer/Composition.lean`
  - `paper/lean/UadfU0/InterLayer/Adequacy.lean`
  - `paper/lean/UadfU0/RelatedWork/Galois.lean`
  - `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`

上記43定理の役割は「定理数そのもの」ではなく、§5の設計判断（二演算分離、同一点連結仮定、one-sided adequacy、部分性と随伴破綻）を機械検証可能な依存構造として固定した点にある。

### 7.5 抽出デモのロック情報
実OSS抽出デモは次を出力する。
- `paper/case-study/real_projects/external_validation_results.json`
- `paper/case-study/real_projects/external_validation_sources.lock.json`
- `paper/case-study/real_projects/snapshots/*`

`source_lock` には URL, SHA256, 取得UTC時刻, snapshot path を記録し、抽出再現の証跡とする。
抽出スクリプトは Python標準ライブラリのみを使用し、追加pip依存を必要としない。
`snapshots/*` は本リポジトリに同梱し、オフライン追試時の入力として利用する。

追試手順（オンライン/オフライン）:
1. オンライン再取得: `python external_validation.py` を引数なしで実行し、`results` / `source_lock` / `snapshots` を再生成する（既存 lock/snapshot があってもオンライン取得を行う。ネットワーク必要）。
2. オフライン追試: `python external_validation.py --offline-lock external_validation_sources.lock.json` を実行し、各 snapshot 読み込み時に lock 記録との SHA256 整合を検証しながら同じ抽出処理を再実行する（ネットワーク不要）。
3. SHA256 検証は `paper/case-study/real_projects/external_validation.py` の `fetch_text` オフライン分岐で実装している（不一致時は例外停止）。
4. オフライン追試で SHA256 不一致が発生した場合は、論文実行時と異なる入力であり再現性が保証されないことを意味するため、同梱 snapshot と lock の一致状態を復元して再実行する。
5. 長期保存に関しては、ソース固定アーカイブ（例: DOI付きリポジトリアーカイブ）とURL失効時フォールバック（例: Wayback参照）を推奨する。

## 8. 関連研究と位置づけ
本稿は既存理論の代替ではなく、UAD/f 最小コアの mechanization を目的とする。

- 抽象解釈（Cousot & Cousot）:
  逆像単調性は整合するが、標準的議論は総写像・随伴成立を前提に置く場合が多い。  
  本稿では部分射影（`Option`）下でその前提が崩れることを `no_left_adjoint_of_partial`（`paper/lean/UadfU0/RelatedWork/Galois.lean`）で示す。
- Institution（Goguen & Burstall）:
  言語横断満足移送を扱う一般理論に対し、本稿は root 演算 `U0`/`U∧` の具体的機械化に焦点を限定。  
  相違は、(i) `Option` による部分射影の一次表現、(ii) root 空間での join/meet 演算の明示、(iii) Lean 上での実行可能証明資産にある。
- システム仕様形式手法（TLA+ など）:
  全体系挙動ではなく、層横断統合カーネルの定義整備と証明再利用に焦点を当てる。
- インターフェース理論（Interface Automata）:
  入出力仮定/保証による合成互換性の形式化を与える。  
  本稿はそれを置換せず、`Option` 部分射影と root 演算 `U0`/`U∧` の明示化に焦点を絞る。
- 精緻化計算（Refinement Calculus）:
  段階的詳細化の一般枠組みに対し、本稿は包含順序を定理語彙として固定しつつ、仕様強弱解釈を補助的に併記して root 統制演算を具体的に機械化した位置づけである。
- ViewPoints / inconsistency management:
  分散視点の整合管理は要求工学の古典課題であり、本稿の「層が独立進化する」問題設定と整合する。  
  本稿は調停手続き自体よりも、比較基準となる root 演算核を Lean で固定する点に焦点を置く。
- 多ビュー整合（pullback 系）:
  ビュー整合を pullback 構成で説明する系譜に対し、本稿は `Option` 部分射影と join/meet を一次表現した最小核 mechanization を与える。
- BX / モデル同期（TGG 等）:
  層間伝播・合成は双方向同期の問題意識と重なる。  
  本稿は完全同期器の構成ではなく、同一点連結仮定の明示と one-sided adequacy の分離を主眼とする。  
  不整合許容型の部分的BX議論とも接続可能である。
- 異種仕様統合（Hets/Institution 実装系）:
  多言語仕様を横断する一般基盤に対し、本稿は UAD/f 文脈での root 統制演算を小さく mechanize した位置づけである。
- 要求形式化（EARS/FRET/ACE/Property Patterns）:
  NL入口を完全排除しない実務系譜に対し、本稿は NL→IR→判定の接続点を one-sided adequacy で管理する立場を採る。
- 仕様マイニング（Daikon 系）:
  `A(i)` 候補の生成源は NL抽出だけでなく、トレース由来不変条件推定も取り得る。  
  本稿は生成源に中立で、`proj` と逆像の整合性条件を核として扱う。
- LLM × Requirements Engineering:
  LLM を直接証明器とみなさず、抽出器候補として位置づけ、誤り特性を sound/complete 分解で管理する方針を採る。
- NL要求→形式論理翻訳（LLM）:
  LLMによる NL→LTL 翻訳は有望だが、失敗解析と改善ループが必要であることが報告されている。  
  本稿は一撃翻訳を前提にせず、候補生成と adequacy 管理を分離する。
- INCOSE系の対話的形式化:
  対話的に NL から形式仕様へ導く系譜と整合し、本稿はその入力管理側（抽出器管理と root 比較基準）を担う位置づけである。

使い分け指針:
- root 空間上で join/meet を明示分離し、部分射影の未定義点まで追跡したい場合: 本稿の UAD/f コア。
- 言語間満足移送を公理的に比較したい場合: Institution。
- 時相的ふるまいやシステム遷移を主対象にする場合: TLA+ などの時相仕様手法。

### 8.1 自説の洗練1: `U0` の Colimit 一般化
本稿コアは同一論理空間（同一 `Ω`）での
\[
U0 = \bigcup_i f^{-1}_{0i}(A_i)
\]
を扱った。  
異種ロジック/異種メタモデルへ拡張する場合、単純な和集合ではなく、仕様図式 `𝒟` の **余極限（colimit）**
\[
U_{\mathrm{colim}} := \mathrm{colim}(\mathcal{D})
\]
として「統合近似」を定義するのが自然である。  
このとき本稿の `U0` は「同一論理空間における colimit の特殊形（coproduct/quotient を伴う join 特例）」として位置づけられる。

### 8.2 自説の洗練2: `proj` を Institution Morphism/Comorphism として再定義
`proj_i` は単なる文字列翻訳ではなく、次の3層を運ぶ構造として解釈できる。

1. 構文（signature/語彙）
2. 文（sentence/論理式）
3. モデル（意味論）

さらに、満足条件（satisfaction condition）を満たす射として制約することで、「翻訳後に真なら翻訳前でも真」が保証される。  
これにより `RQ5 (theory)` の adequacy 分解は、抽出器評価だけでなく「論理空間間の意味保存制約」の監査枠組みとしても読める。

### 8.3 自説の洗練3: `U` の実装を仮想フェデレーションへ
`U` を巨大な物理一元モデルとして保持するのでなく、**仮想統合モデル**として実装する。

1. 各層仕様 `A_i` は元ツール/元表現に残す
2. 統合側はリンク・変換規則・取得手続きを保持する
3. 必要時に動的に射影/逆像評価して `U0`/`U∧` を計算する

この方式は Vitruvius の V-SUM や OpenFlexo の FML が採る「実体集中ではなく関係編成」の思想と整合する。

### 8.4 自説の洗練4: 許容集合の Δ駆動解釈
実務では全状態再計算より、差分 `Δ` を伝播する一貫性維持が有効である。  
そのため `f` を「状態全体写像」だけでなく、Consistency Preservation Rules (CPR) として扱う。

1. 変更 `ΔA_i` が入る
2. CPR が関連層へ `Δ` を伝播
3. `U∧` 空判定/`U0` 被覆差分を更新

さらに実行時には、操作入力を許容集合境界へ射影するシールド（runtime projection guard）として実装できる。

### 8.5 AIエージェント時代での位置づけ
手作業での `proj` 保守は高コストであるため、現在の実装戦略は次の分担が現実的である。

1. LLM/エージェント: NL→IR 抽出、曖昧箇所質問、層間リンク候補生成
2. 形式基盤（本稿コア）: adequacy 条件と整合性判定の監査
3. モデル検査器/証明器: 反例提示と修復ループの収束判定

この分担では、LLM を「完全翻訳器」とみなさず、`A(i)` 候補生成器として扱い、誤りを one-sided adequacy で管理する。

### 8.6 洗練後の全体像（本稿の再定式化）
1. 真の根仕様は直接記述対象でなく、射影ネットワークから構成される（構成主義）。
2. 局所仕様はコンテキスト依存で記述され、`proj` は意味保存制約付き射として管理される。
3. 実装は仮想フェデレーションで行い、物理集中型SUMを避ける。
4. 運用は `Δ` 伝播と runtime projection で継続的一貫性を維持する。

注記: §8.1〜§8.6 は本稿コア（Lean機械検証済み部分）を拡張する理論整理であり、colimit 構成や institution 射の完全機械化は今後課題である。

## 9. 限界と脅威
1. 抽出器の意味保存証明は一般形では未完（§4.3 は抽象関係 `E` に対する接続定理）。
2. 外部評価は convenience sample の3プロジェクト・数値境界制約に限定（母集団代表性は未保証）。
3. 変異試験は感度確認であり、現実バグ分布の推定ではない。
4. regex 抽出の soundness/completeness（抽出漏れ・誤抽出率）は本稿で定量評価していない。
5. 現在のケースは層間合成連鎖や one-sided adequacy の実プロジェクト実証まで到達していない。
6. mathlib非依存のため、既存ライブラリ比較の網羅性は今後の課題。
7. 層間伝播定理（§4.1）は十分条件を与えるが、必要条件は未証明である。
8. `none` の must 解釈（§4.7）は矛盾判定の偽陽性リスクを持ち得るが、本稿では数値境界制約のみを対象としたため定量評価していない。
9. 抽出デモの長期保存戦略（永続アーカイブ DOI, Wayback など）は運用上の推奨事項として残しており、現時点で制度化していない。
10. colimit 構成・institution 射・`Δ` 駆動 CPR の完全機械化は本稿の範囲外であり、拡張設計（§8.1〜§8.6）として提示した。

## 10. 結論
本稿は、UAD/f の root 統合問題を

- `U0`（join: 被覆合成）
- `U∧`（meet: 同時満足統合）

に分離し、両者を同一の型付き部分射影モデルで Lean4 機械検証した。

本稿の主たる増分は、集合論の再掲ではなく、UAD/f 最小コア mechanization に必要な仮定を形式的に明示した点にある。

1. 統合演算の二義性（OR/AND）の分離必要性
2. 伝播定理の同一点連結仮定（関係 `R` だけでは不足）
3. 抽出適合の one-sided 分解（`↔` 一発主張の分解）
4. 部分性による随伴不成立条件（総写像前提の破綻）

さらに、実OSSアーティファクト抽出をソースロック付きで再実行可能にし、前段入力生成パイプラインとしての PoC 基盤を示した。

加えて、本稿コアを異種ロジック統合へ拡張する洗練方向として、`U0` の colimit 一般化、`proj` の institution 射解釈、仮想フェデレーション実装、`Δ` 駆動一貫性維持、LLM候補生成器との分担を提示した（§8.1〜§8.6）。

RQ対応の要約:
- `RQ1`: §2.2 の型付き `preimage` 定義と `Definitions/Model.lean` で解決。
- `RQ2`: §2.1 と `paper/lean/UadfU0/U0Spec/Construction.lean` の `lifted_subset_preimage_domain`, `U0_witness_projects_to_some_domain` で解決。
- `RQ3`: §3 と §4.5（`U0`/`U∧` の join/meet 分離と GLB/LUB 性質）で解決。
- `RQ4`: §4.1, §4.2（`lifted_transfer`, `preimage_compose`）で仮定明示の上で解決。
- `RQ5 (theory)`: §4.3（sound-only / complete-only / equality）で抽象関係 `E` に対する分解を定式化して解決。実抽出器への適用には抽出層の意味保存証明が別途必要（限界 §9）。
- `RQ6 (practice)`: §6.2, §7.5 で source-lock 付き抽出パイプラインの技術的再実行可能性を確認して解決。抽出正当性（soundness/completeness）は RQ6 の対象外であり、限界 §9 に記載。

---
### 参考文献
- Patrick Cousot and Radhia Cousot, “Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints,” *Proceedings of the 4th ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages (POPL 1977)*, pp. 238-252, 1977.
- Joseph A. Goguen and Rod M. Burstall, “Introducing Institutions,” in *Logics of Programs*, Lecture Notes in Computer Science 164, Springer, pp. 221-256, 1984.
- Leslie Lamport, *Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers*, Addison-Wesley, 2002.
- Luca de Alfaro and Thomas A. Henzinger, “Interface Automata,” *Proceedings of the 9th ACM SIGSOFT International Symposium on Foundations of Software Engineering (FSE 2001)*, pp. 109-120, 2001.
- Ralph-Johan Back and Joakim von Wright, *Refinement Calculus: A Systematic Introduction*, Springer, 1998.
- Bashar Nuseibeh, Jeff Kramer, Anthony Finkelstein, “A Framework for Expressing the Relationships Between Multiple Views in Requirements Specification,” IEEE TSE, 1994. URL: https://www.cs.toronto.edu/~sme/papers/1994/csrp333.pdf
- Martin Wirsing and Alexander Knapp, “View Consistency in Software Development,” in *RADICAL 2004* (Springer LNCS), 2004. URL: https://link.springer.com/chapter/10.1007/978-3-540-24626-8_24
- Yingfei Xiong et al., “Model Synchronization Based on Triple Graph Grammars,” *Software and Systems Modeling*, 2012. URL: https://xiongyingfei.github.io/papers/Sosym12.pdf
- Till Mossakowski et al., “The Heterogeneous Tool Set (Hets),” CEUR-WS. URL: https://ceur-ws.org/Vol-259/paper11.pdf
- Alistair Mavin, Philip Wilkinson, Adrian Harwood, Mark Novak, “Easy Approach to Requirements Syntax (EARS),” RE'09 workshop. URL: https://www.researchgate.net/publication/224079416_Easy_approach_to_requirements_syntax_EARS
- NASA Formal Requirements Elicitation Tool (FRET/FRETish) Tutorial, NASA Technical Reports Server, 2022. URL: https://ntrs.nasa.gov/citations/20220009659
- Norbert E. Fuchs et al., *Attempto Controlled English (ACE) Manual*, University of Zurich / Attempto project. URL: https://attempto.ifi.uzh.ch/site/pubs/papers/ace3manual.pdf
- Matthew B. Dwyer, George S. Avrunin, James C. Corbett, “Patterns in Property Specifications for Finite-State Verification,” ICSE 1999. URL: https://ext.math.umass.edu/~avrunin/papers/dwyer99-icse-patterns.pdf
- Michael D. Ernst et al., “The Daikon system for dynamic detection of likely invariants,” *Science of Computer Programming*, 2007. URL: https://web.eecs.umich.edu/~weimerw/2024-481F/readings/daikon-tool-scp2007.pdf
- “Large Language Models (LLMs) for Requirements Engineering (RE): A Systematic Literature Review,” arXiv preprint, 2025. URL: https://arxiv.org/abs/2509.11446
- “Learning from Failures: Translation of Natural Language Requirements into Linear Temporal Logic by LLMs,” East China Normal University repository page. URL: https://pure.ecnu.edu.cn/en/publications/learning-from-failures-translation-of-natural-language-requiremen/
- “Transforming Natural Language Requirements to Formalism (interactive workflow),” INCOSE Systems Engineering. URL: https://incose.onlinelibrary.wiley.com/doi/10.1002/sys.70023
- “Bidirectionally tolerating inconsistency: partial bidirectional transformations,” FoSSaCS/FASE era reference. URL: https://groups.inf.ed.ac.uk/bx/fase14.pdf
- “Automated formalization of structured natural language requirements,” *Information and Software Technology*. URL: https://www.sciencedirect.com/science/article/abs/pii/S0950584921000707
