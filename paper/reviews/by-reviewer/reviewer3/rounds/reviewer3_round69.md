## 総合判定

**条件付き採択可能（Major Revision）**

FM/FASE/CPP 基準での形式論文寄与としては方向性は妥当だが、以下の問題を修正しなければ採択阻害となる。

---

## 主要懸念

### 1. 新規性の主張が不明確かつ弱い（採択阻害）

§6「What Mechanization Added Beyond Textbook Identities」でクラシカル重複を自ら列挙しているが、**差分がどこにあるかの論証が定性的すぎる**。

- "one auditable package" は工学的価値として認めうるが、CPP/FASEレベルでは「なぜこのパッケージが既存Mathlibや既存ITP論文で間に合わないか」の反駁が必要。
- §6.1「Concrete delta against baseline theorem libraries」が存在するが、Mathlibの`Set.preimage`との差を「heterogeneous carriers + Option」と述べるのみで、**その組み合わせが引き起こす定理インターフェースの非自明性**を証明ステップレベルで示していない。
- 査読者は「Lean4でSet.preimageをOptionに替えてラップしただけでは？」と読む恐れがある。反例（TransferCounterexample）はこの懸念の一部を払拭するが、**論文本文での位置づけが弱い**（§5に埋没）。

**修正方針**: §6.1に、既存ライブラリを直接使おうとした場合に何が壊れるかの具体的技術的障壁を1–2段落追加する。

---

### 2. `preimage_compose`の公理使用（`Classical.choice`）の説明不足（採択阻害リスク）

§4.3で`Classical.choice`がappearすることを開示しているが、**なぜ構成的に処理できないかの説明がない**。

CPP査読者（Coq/Agda文化からの転向者を含む）は、`Classical.choice`の使用を問題視する可能性がある。"this paper does not claim constructivity-preserving normalization" と書いているだけでは不十分。

**修正方針**: 「extensional equality over existential branches in Lean4の証明項の構造上、`Quot.sound`+`Classical.choice`が誘発される理由」を1文の技術的説明として追加する。または、Decidable instanceによる代替を検討し、できない理由を明示する。

---

### 3. RQ設計と答えの非対称性（誤読リスク大）

§1.3でRQ1–RQ5を列挙し、§1.4で "Primary RQs for this formal paper are RQ3, RQ4, RQ5" と限定している。

- RQ1・RQ2を「primary」から除外しておきながら、§3.2で "RQ1 is answered by typed inverse-image definitions" と記述するのは**構造的に矛盾**している。
- 査読者は「RQ1・RQ2はこの論文の貢献なのかそうでないのか」を判断できない。

**修正方針**: RQ1・RQ2を「supporting questions answered as prerequisites」として明示的に分類し直すか、§1.4の primary RQ 限定の文を削除する。

---

### 4. Related workの定位置付けが表面的（FM/FASE基準での採択阻害）

§7は7項目列挙するが、各項目が2–3文の断言で終わっており、**差分の根拠が技術的に示されていない**。

特にFASE・FM査読では「institutions（Goguen & Burstall）との差分」が重要視される。§7.7に差分記述があるが、「this paper does not mechanize general signature/sentence/model morphisms」という否定的説明のみで、なぜその設計選択をしたかの正当化がない。

**修正方針**: §7.7に対して、「satisfaction condition preservation を機械化しないことで得られる定理インターフェースの簡潔さ」等、設計上のトレードオフを1段落追加する。

---

## 軽微懸念

### 5. `lake-manifest.json`の内容が異常に薄い

```json
{"packages": [], ...}
```

Lean4でMathlib等を使わずに済んでいる理由（自前定義で完結）については§4.3に開示があるが、**manifest hashの意義が希薄**になっている。§9でmanifest hashを再現性メタデータとして挙げているが、依存パッケージゼロのmanifestのhashを検証することに実質的意味がないため、査読者が「再現性メタデータとして不誠実」と読む恐れがある。

**修正方針**: manifest hashの役割を「toolchain固定のlock」ではなく「lean-toolchain fileとの整合確認」として再記述する。

---

### 6. `UStar`の扱いが§3.8と§2.8で二重説明されている

§2.8「Root-space instantiation templates」と§3.8「Ideal-root linkage under observability domains」の内容が重複しており、論文構成上の冗長性がある。§2.8は定義セクションなので`UStar`の性質を先出しすることの正当化が必要か、あるいは§3.8の冒頭で§2.8への前方参照を簡潔にまとめる形にした方が読みやすい。

---

### 7. PasswordPolicy case studyの位置づけが曖昧

§5.2で「mechanized sanity theorem for constrained interval domain」と述べているが、これが formal contribution に含まれるのか、例示のみなのかが不明確。§0.2の non-claims と照合すると "no proof that a concrete extractor satisfies adequacy" と述べているのに、§5.2の`req_projection_adequacy`は具体的モデルでの adequacy の等式証明になっており、**non-claimsと矛盾するように読める**。

**修正方針**: `req_projection_adequacy`が「concrete extractor correctness」ではなく「abstract E の具体化例示」であることを明示的に注記する。

---

## 必須修正

1. **新規性の防衛強化**（§6.1）: 既存Mathlibアプローチが失敗する具体的技術障壁を追記。
2. **RQ1・RQ2の分類整理**（§1.3–1.4, §3.2）: primary/supportingの区分を論文全体で統一。
3. **`Classical.choice`使用の技術的正当化**（§4.3）: 構成的回避不能の理由を1文追加。
4. **Related work §7.7の設計選択正当化**: institution不採用のトレードオフを1段落追加。
5. **§5.2の non-claims との整合性注記**: `req_projection_adequacy`の位置づけを明確化。
