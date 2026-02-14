# 査読レポート（査読者1: 理論・意味論担当）

**Verdict: OK**

## 承認根拠

### 1. 問題設定と研究目的の整合性（§0）
- 問題設定（§0.1）は「多層仕様統制の困難性」を明確に定義し、層間矛盾・保証の隙間・変更波及断絶の3点で具体化している
- 研究目的（§0.2）は問題に対応して「root構成」「join/meet分離」「機械検証」の3到達目標を提示
- RQ1〜RQ6は目的を操作的に分解しており、かつ§1.1評価軸が各RQの検証可能性を担保
- 特にRQ5(theory)/RQ6(practice)の分離は「抽象adequacy定理」と「実抽出パイプライン」を明示的に区別し、主張範囲を限定

### 2. U0(join)/U∧(meet)分離と順序語彙の一貫性（§2.3, §3, §4）
- §2.3で包含順序`⊆`を**唯一の順序**として固定し、定理語彙の一意性を確保
- join=`∪`（最小上界）、meet=`∩`（最大下界）の定義が§3.1, §3.2で整合
- `U0`=join（被覆合成/over-approximation）、`U∧`=meet（同時満足）の意味分離が明確
- 「仕様強弱」は補助的直観として扱い、順序反転による混乱を回避
- §3.3の接続定理群（`UAndOn_subset_U0On`, `UAndOn_antitone`, `consistent_iff_exists_UAndOn_pair`）がLean実装と対応

### 3. 理論構造の論理整合（§4中核定理群）
- RQ1→§2.2 `preimage`（型付き逆像）
- RQ2→§4.1 `lifted_subset_preimage_domain`, `U0_witness_projects_to_some_domain`（`A⊆D`の持ち上げ）
- RQ3→§4.5 GLB定理群（`UAndOn_lower_bound`, `UAndOn_greatest_lower_bound_iff`）
- RQ4→§4.1, §4.2（`lifted_transfer`の同一点連結仮定`hproj`, `preimage_compose`の合成則）
- RQ5→§4.3（sound-only/complete-only adequacy分解）
- RQ6→§6.2, §7.5（source-lock付き抽出再実行）

中核定理§4.1〜§4.3は「定義展開補題」でなく、**同一点連結仮定（hproj）の必要性**、**pullbackVia明示の合成則**、**adequacy一方向分解**という非自明な構造を機械検証で顕在化させた点が貢献。

§4.4の非随伴性定理（`no_left_adjoint_of_partial`）は部分射影の本質的制約を証明し、総写像前提の暗黙仮定を否定。

---

## 補足観察（瑕疵ではない）

1. **NL入口管理（§2.6）**: 自然言語を入口から排除せず、NL→IR→判定の接続点をadequacy管理で扱う方針は実務的。ただし§6.2の regex抽出層はadequacy未検証であり、§9限界で明示済み。理論/実践分離は整合。

2. **抽出デモの位置づけ（§6.2）**: `n=3` convenience sample を技術的実行可能性PoC（RQ6）として扱い、母集団推定を目的外と明記。変異試験も感度確認（sanity check）として解釈。選定理由・バイアス管理・source-lock再現性の記述が十分。

3. **順序固定の徹底性**: §2.3で`⊆`を唯一の順序と宣言し、以降の join/meet/LUB/GLB がすべて包含順序で統一。仕様強弱は補助的直観に留め、定理語彙混線を回避。

---

**結論**: 問題設定・研究目的・RQ・定理構造・用語秩序がすべて整合し、機械検証により仮定明示化という主張が成立している。理論（RQ5）と実践（RQ6）の分離も明確で、限界§9で対象外範囲を適切に宣言。
