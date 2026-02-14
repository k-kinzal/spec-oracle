# 状態機械と仕様記述

## 1. 状態機械の概要

### 1.1 基本概念

**状態機械（State Machine）** は、システムが「状態（state）」と「遷移（transition）」によって振る舞いを記述するモデルです。システムはある時点で必ず何らかの状態にあり、イベントや入力が発生すると条件に応じて別の状態へ遷移します。

状態機械の数学的基盤：
```
M = (S, Σ, δ, s₀, F)
```
- S: 有限状態集合
- Σ: 入力記号のアルファベット
- δ: 遷移関数 δ: S × Σ → S
- s₀: 初期状態 (s₀ ∈ S)
- F: 受理状態集合 (F ⊆ S)

### 1.2 状態遷移図（State Transition Diagram）

状態遷移図は、有限オートマトンなどの状態機械について、その各状態を頂点とし、状態から状態への各遷移を辺としたグラフ構造に注目してグラフィカルに表現した図です。

**基本要素**：
- **状態（State）**: 円または角丸四角形で表現
- **遷移（Transition）**: 矢印で表現
- **イベント/条件**: 遷移を引き起こすトリガー
- **アクション**: 遷移時に実行される処理
- **初期状態**: 黒丸または矢印で示す
- **最終状態**: 二重円で表現

```
[状態A] --イベント[条件]/アクション--> [状態B]
```

## 2. 有限状態機械（FSM）の分類

### 2.1 Mealy機械

**Mealy機械** は、出力が現在の状態と入力の両方に依存する有限状態機械です。

定義：
```
M_Mealy = (S, Σ, Ω, δ, λ, s₀)
```
- Ω: 出力記号のアルファベット
- λ: 出力関数 λ: S × Σ → Ω

**特徴**：
- 出力は遷移に付随
- 入力に即座に反応
- 状態数が少なくて済む
- 非同期回路に適している

**例**（簡易自動販売機）：
```
待機状態 --100円投入/釣銭なし--> 100円状態
100円状態 --100円投入/飲料提供--> 待機状態
100円状態 --150円投入/飲料提供+50円釣銭--> 待機状態
```

### 2.2 Moore機械

**Moore機械** は、出力が現在の状態のみに依存する有限状態機械です。

定義：
```
M_Moore = (S, Σ, Ω, δ, λ, s₀)
```
- λ: 出力関数 λ: S → Ω

**特徴**：
- 出力は状態に付随
- 同期回路に適している
- 遷移が明確で理解しやすい
- 状態数が多くなる傾向

**例**（信号機）：
```
赤状態 → 出力: 赤点灯
  ↓ タイマー満了
青状態 → 出力: 青点灯
  ↓ タイマー満了
黄状態 → 出力: 黄点灯
  ↓ タイマー満了
赤状態...
```

### 2.3 Mealy vs Moore比較表

| 観点 | Mealy | Moore |
|------|-------|-------|
| 出力依存 | 状態+入力 | 状態のみ |
| 出力タイミング | 遷移時（即座） | 状態到達時 |
| 状態数 | 少ない | 多い |
| 設計の明確さ | やや複雑 | 明確 |
| 同期/非同期 | 非同期向き | 同期向き |
| UML対応 | 遷移アクション | 入場/退出アクション |

## 3. 拡張有限状態機械（EFSM）

### 3.1 EFSMの概要

**拡張有限状態機械（Extended Finite State Machine, EFSM）** は、伝統的なFSMに以下の要素を追加した拡張モデルです：

1. **コンテキスト変数**: データ値を保持
2. **ガード条件**: 遷移の可否を判定する述語
3. **パラメータ**: 入力/出力パラメータ
4. **アクション**: データ操作と副作用

定義：
```
EFSM = (S, Σ, Γ, δ, λ, Ω, s₀, V)
```
- V: コンテキスト変数集合
- Γ: ガード述語集合
- δ: S × Σ × Γ → S (ガード付き遷移)
- λ: アクション関数

### 3.2 EFSMの構造

EFSMモデルは3つの主要な組み合わせブロックで構成されます：

1. **FSMブロック**: 状態遷移グラフを実現
2. **Aブロック**: 各遷移に関連するデータ操作を実行
3. **Eブロック**: 各遷移に関連するトリガー条件を評価

**遷移の表現**：
```
状態A --イベント[ガード条件]/アクション(変数更新)--> 状態B
```

**例**（ATMの暗証番号検証）：
```
変数: attempts = 0, max_attempts = 3

待機 --カード挿入/attempts := 0--> PIN入力
PIN入力 --PIN入力[PIN正しい]/口座表示--> ログイン済
PIN入力 --PIN入力[PIN誤り AND attempts < max_attempts]/attempts++--> PIN入力
PIN入力 --PIN入力[attempts >= max_attempts]/カード没収--> ロック
```

### 3.3 EFSMの利点

1. **表現力の向上**: 複雑なデータ依存の振る舞いを表現可能
2. **状態爆発の回避**: 変数を使用することで状態数を削減
3. **現実的なシステムモデル**: 実際のソフトウェアシステムにより近い
4. **テスト生成**: データ駆動テストケースの自動生成に適用可能

### 3.4 ECFSM（拡張通信有限状態機械）

**ECFSM（Extended Communicating Finite State Machine）** は、EFSMに通信機構を追加したモデルで、並行プロセス間の相互作用を記述できます。

PROMELA と SDL は、ECFSM の強力な形式的基盤を採用しています。

## 4. 階層的状態機械（Harel Statecharts）

### 4.1 Harel Statechartsの歴史

**Statecharts** は、David Harel が1980年代に発明した形式主義で、リアクティブシステムの複雑さを忠実に表現する非常に効率的な方法を提供します。

Harel Statecharts は、従来の状態図に以下の追加要素を導入しました：
1. **階層性（Hierarchy）**: 複合状態と入れ子状態
2. **並行性（Concurrency/Orthogonality）**: 直交領域
3. **通信（Communication）**: イベント放送とブロードキャスト

### 4.2 階層性（複合状態）

**複合状態（Composite State）** は、内部に複数のサブ状態を持つ状態です。

**利点**：
- 設計のさらなる細分化が可能
- 状態間に必要な遷移線の数を減らす
- 共通の振る舞いをグループ化
- 複雑さの管理が容易

**例**（電話システム）：
```
通話中（複合状態）
  ├─ 呼び出し中
  ├─ 接続中
  └─ 保留中
```

複合状態への遷移は、デフォルトでその初期サブ状態への遷移になります。

**History状態**：
- **浅い履歴（Shallow History）**: 複合状態の直接のサブ状態を記憶
- **深い履歴（Deep History）**: 入れ子の全階層を記憶

### 4.3 並行性（直交領域）

**直交領域（Orthogonal Regions）** は、同時に複数の状態に存在できる並行実行を表現します。

**例**（マルチメディアプレーヤー）：
```
プレーヤー
├─ 再生制御 ──┐
│   ├─ 停止   │
│   ├─ 再生   │  並行実行
│   └─ 一時停止│
│             │
└─ 音量調整 ──┘
    ├─ ミュート
    └─ 通常音量
```

システムは「再生」かつ「ミュート」のように、両方の領域で同時に状態を持ちます。

### 4.4 UML State Machines

**UML State Machines** は、Harel Statecharts を基にしたオブジェクト指向拡張版で、OMG（Object Management Group）の最新UML仕様で採用されています。

UML Statecharts の特徴：
- 階層的にネストされた状態
- 直交領域
- 拡張されたアクション概念
- MealyとMooreの両方の特性

**アクションの種類**：
- **Entry Action**: 状態への入場時に実行（Moore的）
- **Exit Action**: 状態からの退出時に実行（Moore的）
- **Do Activity**: 状態滞在中に実行される長時間動作
- **Transition Action**: 遷移時に実行（Mealy的）

**例**：
```
State 起動中
  entry / システム初期化()
  do / 起動画面表示()
  exit / リソース解放()
```

## 5. 状態機械の仕様記述言語

### 5.1 SDL（Specification and Description Language）

**SDL** は、通信、医療、自動車、軍事、航空宇宙などの産業で使用される、国際標準で正式に定義された主要なドメイン固有言語の1つです。

**特徴**：
- ITU-T標準（Z.100シリーズ）
- EFSMとECFSMに基づく
- グラフィカルとテキスト記法の両方
- タイムアウトとタイマーのサポート
- 通信プロトコル仕様に特化

**主要な構成要素**：
- **System**: 最上位の構造
- **Block**: システムの構造的単位
- **Process**: 動的な振る舞いを定義（EFSM）
- **Signal**: プロセス間通信
- **Channel**: 通信路

**応用分野**：
- 電気通信プロトコル（GSM、UMTS、LTE）
- 交換機とネットワーク制御
- 組み込みシステム制御

### 5.2 SCXML（State Chart XML）

**SCXML** は、W3Cで標準化された、Harel Statecharts に基づくXMLベースのマークアップ言語です。

**特徴**：
- W3C勧告（2015年）
- 汎用の状態機械実行環境
- イベント駆動アーキテクチャ
- データモデルのサポート（ECMAScript、XPathなど）
- Webアプリケーションとの統合

**主要要素**：
```xml
<scxml initial="待機" version="1.0">
  <datamodel>
    <data id="counter" expr="0"/>
  </datamodel>

  <state id="待機">
    <transition event="開始" target="実行">
      <assign location="counter" expr="0"/>
    </transition>
  </state>

  <state id="実行">
    <onentry>
      <log expr="'実行開始'"/>
    </onentry>
    <transition event="完了" target="待機" cond="counter >= 10"/>
  </state>
</scxml>
```

**応用分野**：
- 音声ダイアログシステム（VoiceXML連携）
- Webアプリケーションのワークフロー
- 産業用制御システムのシミュレーション
- UIインタラクションの仕様

### 5.3 PROMELA（Process Meta Language）

**PROMELA** は、SPINモデル検査器で使用される高レベルのモデル記述言語です。

**特徴**：
- C言語風の構文
- ECFSMの形式的基盤
- 非決定性と並行性の表現
- LTL（線形時相論理）による仕様記述
- 通信チャネルとメッセージパッシング

**例**（相互排除）：
```promela
byte turn = 0;
bool want[2];

active [2] proctype P() {
  pid me = _pid;
  pid other = 1 - _pid;

  do
  :: true ->
     want[me] = true;
     turn = other;
     (want[other] == false || turn == me);
     /* クリティカルセクション */
     want[me] = false;
  od
}
```

**応用分野**：
- 並行プロトコルの検証
- 分散アルゴリズムの解析
- デッドロックとライブロックの検出

### 5.4 SDL ⇄ PROMELA変換

**sdl2pml** という自律ツールが開発され、SDL仕様からPromelaモデルへの直接的な自動生成が可能になりました。

**変換の利点**：
- SDLの表現力と SPIN の検証能力を組み合わせ
- 産業用通信プロトコルの形式検証
- モデル駆動開発プロセスへの統合

## 6. 状態機械の形式検証

### 6.1 モデル検査

**モデル検査（Model Checking）** は、状態機械の形式検証に最も広く使用される手法です。

**主要ツール**：

#### SPIN
- **型**: 明示的状態モデル検査器
- **手法**: 構築して各訪問状態の表現を保存
- **最適化**: 部分順序削減（Partial-Order Reduction）
- **用途**: 並行システム、プロトコル検証

**産業応用例**：
- Deep Space One 飛行ソフトウェアの二重冗長化コントローラ検証
- Mars Science Laboratory ソフトウェアの重要部分
- 打ち上げロケットのオンボードコンピュータソフトウェア

#### NuSMV
- **型**: シンボリックモデル検査器
- **手法**: BDD（二分決定図）とSATベースモデル検査の組み合わせ
- **サポート論理**: CTL（計算木論理）とLTL（線形時相論理）
- **利点**: 大規模な状態空間を扱える

**比較**：

| 特性 | SPIN（明示的） | NuSMV（シンボリック） |
|------|---------------|---------------------|
| 状態表現 | 個別に保存 | BDD/SAT |
| 状態空間サイズ | 中規模 | 大規模 |
| 反例生成 | 詳細なトレース | 抽象的 |
| メモリ使用 | 高い | 効率的 |

### 6.2 検証対象の性質

状態機械で検証される典型的な性質：

1. **安全性（Safety）**: 「悪いことは起こらない」
   - デッドロック不在
   - 相互排除
   - 不変条件の維持

2. **活性（Liveness）**: 「良いことはいずれ起こる」
   - 進行保証
   - 公平性
   - 最終的到達性

3. **時間制約**: タイミング要求の満足

**例（LTL仕様）**：
```
□(request → ◇grant)  // 要求は必ず許可される
□¬(critical₁ ∧ critical₂)  // 相互排除
```

### 6.3 状態空間爆発問題

**課題**: 状態数がシステムの規模に対して指数的に増大

**対策技術**：
1. **抽象化（Abstraction）**: 不要な詳細を削除
2. **部分順序削減（POR）**: 等価なインターリーブを削減
3. **シンボリック表現（BDD/SAT）**: 状態集合を論理式で表現
4. **有界モデル検査（BMC）**: 検証深度を制限
5. **分割統治（Compositional Verification）**: システムを部分ごとに検証

## 7. 状態機械に基づくテスト生成

### 7.1 カバレッジ基準

状態機械からテストケースを生成する際の主要なカバレッジ基準：

#### 基本カバレッジ
1. **状態カバレッジ（State Coverage）**:
   - すべての状態を少なくとも1回訪問
   - 基準: |訪問状態| / |全状態| = 100%

2. **遷移カバレッジ（Transition Coverage）**:
   - すべての遷移を少なくとも1回実行
   - 基準: |実行遷移| / |全遷移| = 100%

#### 高度なカバレッジ
3. **遷移ペアカバレッジ（Transition Pair Coverage）**:
   - 連続する2つの遷移のすべての組み合わせ
   - 各状態の入出力遷移の全組み合わせをカバー

4. **0-スイッチカバレッジ**:
   - 個々の遷移を連続性を考慮せずにテスト

5. **1-スイッチカバレッジ**:
   - 2つの連続遷移の全組み合わせをテスト

6. **フルパスカバレッジ**:
   - 初期状態から最終状態への全パス
   - 一般的には実行不可能（指数的増大）

#### その他の基準
7. **完全述語カバレッジ（Full Predicate, FP）**
8. **往復パスカバレッジ（Round Trip Path, RTP）**
9. **全遷移（All Transitions, AT）**
10. **全遷移ペア（All Transition Pairs, ATP）**
11. **長さNのATPパス（LN2, LN3, LN4）**

### 7.2 テスト生成手法

#### モデルベーステスト（Model-Based Testing, MBT）

状態遷移ベースの制御フローとデータ要素を含むシステムに対するモデルベーステストアプローチで、モデルのすべての遷移に到達することを目指したテストケースを生成します。

**プロセス**：
1. 状態機械モデルの構築
2. カバレッジ基準の選択
3. テストケースの自動生成
4. 具体的なテストデータの生成
5. テスト実行とカバレッジ計測

#### アルゴリズム

**状態遷移図からのテストケース生成アルゴリズム**：
```
Input: StateChart SC, Coverage Criterion C
Output: Test Suite TS

1. Parse SC and build graph G = (V, E)
   V = states, E = transitions

2. For each coverage target t ∈ C:
   a. Find path p from initial state to t
   b. Extract test sequence from p
   c. Generate test data satisfying guards
   d. Add test case to TS

3. Calculate degree of coverage

4. If coverage < threshold:
   Generate additional test cases

5. Return TS
```

#### ツールサポート

現代のテスト生成ツール：
- **SpecExplorer**: モデル探索に基づく
- **Conformiq**: 商用MBTツール
- **GraphWalker**: オープンソースMBTフレームワーク
- **UPPAAL TRON**: 時間オートマトンからのオンラインテスト

### 7.3 実装例：UML State Machineからのテスト生成

**ステップ**：

1. **モデルのパース**:
```
StateChart:
  States = {Idle, Active, Error}
  Transitions = {
    (Idle, start, Active),
    (Active, error, Error),
    (Active, stop, Idle),
    (Error, reset, Idle)
  }
```

2. **遷移カバレッジのテストケース生成**:
```
Test Case 1: Idle → start → Active
Test Case 2: Active → error → Error
Test Case 3: Active → stop → Idle
Test Case 4: Error → reset → Idle
```

3. **遷移ペアカバレッジの追加**:
```
Test Case 5: Idle → start → Active → stop → Idle
Test Case 6: Idle → start → Active → error → Error
Test Case 7: Error → reset → Idle → start → Active
```

### 7.4 計測とフィードバック

**カバレッジ計測**：
```
Transition Coverage = (実行された遷移数) / (全遷移数) × 100%
```

各テストケース作成中に、生成されたテストケースがすべての可能なテストシナリオをカバーすることを保証するために、テストカバレッジの度合いが計算されます。

## 8. 状態機械の実用ツールと言語

### 8.1 XState（JavaScript/TypeScript）

**XState** は、JavaScript および TypeScript アプリケーションの状態管理およびオーケストレーションソリューションです。

**特徴**：
- W3C SCXML 準拠のデータ構造
- 階層的状態機械とStatecharts
- Actorモデルのサポート
- TypeScript型安全性
- ビジュアライゼーションツール

**例**：
```typescript
import { createMachine, interpret } from 'xstate';

const trafficLightMachine = createMachine({
  id: 'trafficLight',
  initial: 'red',
  states: {
    red: {
      on: { TIMER: 'green' }
    },
    yellow: {
      on: { TIMER: 'red' }
    },
    green: {
      on: { TIMER: 'yellow' }
    }
  }
});

const service = interpret(trafficLightMachine)
  .onTransition(state => console.log(state.value))
  .start();

service.send('TIMER'); // 'green'
```

**応用分野**：
- Webアプリケーションの状態管理（React、Vue、Svelteなど）
- フロントエンドワークフロー
- UIインタラクションの仕様と実装

### 8.2 Stateflow（MATLAB/Simulink）

**Stateflow** は、MATLAB/Simulink環境の組み込み系状態機械設計ツールです。

**特徴**：
- グラフィカルな状態遷移図エディタ
- Simulinkモデルとの統合
- Mealy/Mooreの両方をサポート
- コード生成（C/C++）
- 組み込みターゲットへの展開

**応用分野**：
- 自動車制御システム（ECU）
- 航空宇宙システム
- ロボット制御
- 産業オートメーション

### 8.3 Yakindu Statechart Tools

**Yakindu** は、Statecharts のモデリング、シミュレーション、コード生成のためのオープンソース/商用ツールです。

**特徴**：
- Eclipse ベース IDE
- SCXMLサポート
- 多言語コード生成（C、C++、Java、Python）
- シミュレーションとデバッグ
- 形式検証連携

### 8.4 SCADE（Safety-Critical Application Development Environment）

**SCADE** は、安全クリティカルシステム向けのモデルベース開発環境です。

**特徴**：
- IEC 61508、DO-178C 認証済み
- 形式的に検証されたコード生成
- 状態機械とデータフロー統合
- 要求トレーサビリティ

**応用分野**：
- 航空電子機器（DO-178C）
- 鉄道制御システム（CENELEC EN 50128）
- 原子力制御システム（IEC 61513）

### 8.5 組み込みシステムでの実装

**実装パターン**：

#### 1. Switch-Case パターン
```c
typedef enum {
  STATE_IDLE,
  STATE_ACTIVE,
  STATE_ERROR
} State;

State current_state = STATE_IDLE;

void state_machine_run(Event event) {
  switch(current_state) {
    case STATE_IDLE:
      if (event == EVENT_START) {
        on_start();
        current_state = STATE_ACTIVE;
      }
      break;
    case STATE_ACTIVE:
      if (event == EVENT_ERROR) {
        on_error();
        current_state = STATE_ERROR;
      } else if (event == EVENT_STOP) {
        on_stop();
        current_state = STATE_IDLE;
      }
      break;
    case STATE_ERROR:
      if (event == EVENT_RESET) {
        on_reset();
        current_state = STATE_IDLE;
      }
      break;
  }
}
```

#### 2. テーブル駆動パターン
```c
typedef struct {
  State current_state;
  Event event;
  State next_state;
  void (*action)(void);
} Transition;

Transition transition_table[] = {
  {STATE_IDLE, EVENT_START, STATE_ACTIVE, on_start},
  {STATE_ACTIVE, EVENT_ERROR, STATE_ERROR, on_error},
  {STATE_ACTIVE, EVENT_STOP, STATE_IDLE, on_stop},
  {STATE_ERROR, EVENT_RESET, STATE_IDLE, on_reset}
};

void state_machine_run(Event event) {
  for (int i = 0; i < sizeof(transition_table)/sizeof(Transition); i++) {
    if (transition_table[i].current_state == current_state &&
        transition_table[i].event == event) {
      if (transition_table[i].action != NULL) {
        transition_table[i].action();
      }
      current_state = transition_table[i].next_state;
      break;
    }
  }
}
```

#### 3. 関数ポインタパターン
```c
typedef void (*StateFunc)(Event);

void state_idle(Event event);
void state_active(Event event);
void state_error(Event event);

StateFunc current_state_func = state_idle;

void state_idle(Event event) {
  if (event == EVENT_START) {
    on_start();
    current_state_func = state_active;
  }
}

void state_active(Event event) {
  if (event == EVENT_ERROR) {
    on_error();
    current_state_func = state_error;
  } else if (event == EVENT_STOP) {
    on_stop();
    current_state_func = state_idle;
  }
}

void state_machine_run(Event event) {
  current_state_func(event);
}
```

## 9. 産業応用例

### 9.1 プロトコル仕様

#### TCP状態遷移

TCPプロトコルの接続管理は、状態機械で定義されています：

```
CLOSED → LISTEN
CLOSED → SYN_SENT → ESTABLISHED
LISTEN → SYN_RCVD → ESTABLISHED
ESTABLISHED → FIN_WAIT_1 → FIN_WAIT_2 → TIME_WAIT → CLOSED
ESTABLISHED → CLOSE_WAIT → LAST_ACK → CLOSED
```

#### 通信プロトコルの形式仕様

SDL を使用した GSM プロトコルスタック、UMTS、LTE の仕様記述が標準的です。

### 9.2 組み込み制御システム

**応用例**：
1. **家電製品**:
   - 洗濯機（給水→洗浄→すすぎ→脱水→完了）
   - エアコン（停止→冷房→除湿→暖房）
   - 電子レンジ（待機→加熱→一時停止→完了）

2. **自動車**:
   - エンジン制御（始動→アイドル→走行→停止）
   - ドアロック制御
   - ワイパー制御（オフ→間欠→低速→高速）

3. **ロボット**:
   - 移動制御（待機→前進→旋回→停止）
   - マニピュレータ制御
   - センサフュージョン状態管理

### 9.3 ユーザーインターフェース

**Webアプリケーション状態管理**：
```
未認証 → ログイン中 → 認証済
認証済 → データ読み込み中 → データ表示
データ表示 → 編集中 → 保存中 → データ表示
```

XState を使用した React アプリケーションでの典型的な使用例です。

### 9.4 ワークフロー管理

**ビジネスプロセス**：
```
注文受付 → 在庫確認 → 決済処理 → 配送準備 → 発送完了
                ↓
            在庫不足 → 入荷待ち → 在庫確認
```

SCXML は、ワークフローエンジンのバックエンドとして使用されます。

## 10. 状態機械と仕様の関係

### 10.1 仕様としての状態機械

状態機械は、システムの振る舞いを記述する**実行可能仕様**として機能します：

**メリット**：
1. **明確性**: グラフィカル表現により理解が容易
2. **形式性**: 数学的基盤に基づく厳密な定義
3. **実行可能性**: シミュレーションと検証が可能
4. **実装との対応**: コード生成により仕様と実装のギャップを削減
5. **テスト可能性**: 自動テスト生成の基盤

### 10.2 状態機械による仕様の階層化

大規模システムの仕様は、状態機械の階層化により管理できます：

```
システム全体（高レベル状態機械）
  ├─ サブシステムA（中レベル状態機械）
  │   ├─ コンポーネントA1（低レベル状態機械）
  │   └─ コンポーネントA2（低レベル状態機械）
  └─ サブシステムB（中レベル状態機械）
      └─ コンポーネントB1（低レベル状態機械）
```

各階層で適切な抽象化レベルの仕様を提供します。

### 10.3 状態機械と他の仕様技法の統合

1. **時相論理との統合**:
   - 状態機械: 構造的な振る舞い
   - LTL/CTL: 性質の仕様
   - モデル検査により検証

2. **契約プログラミングとの統合**:
   - 状態不変条件: 各状態で成立すべき条件
   - 遷移事前条件: 遷移が発火する条件
   - 遷移事後条件: 遷移後に成立する条件

3. **データフローとの統合**:
   - Simulink/Stateflow: 制御フロー（Stateflow）とデータフロー（Simulink）
   - SCADE: 同期データフローと状態機械の統合

### 10.4 状態機械仕様の課題

**限界**：
1. **状態爆発**: 複雑なシステムで状態数が急増
2. **データ抽象化**: データ操作の詳細な仕様が困難
3. **並行性の表現**: 多数の並行プロセスの管理が複雑
4. **非機能要件**: 性能、セキュリティなどの表現が難しい

**対策**：
1. EFSM とガード条件により状態数を削減
2. 階層的状態機械により複雑さを管理
3. 直交領域により並行性を表現
4. 他の仕様技法（時相論理、制約言語）との組み合わせ

## 11. 状態機械の理論的発展

### 11.1 時間オートマトン（Timed Automata）

**時間オートマトン** は、リアルタイムシステムの仕様と検証のために、FSMに時間制約を追加した拡張です。

**定義**：
- クロック変数
- クロック制約（ガード）
- クロックリセット

**ツール**: UPPAAL

**応用**: リアルタイム組み込みシステム、通信プロトコルのタイミング検証

### 11.2 確率オートマトン（Probabilistic Automata）

**確率オートマトン** は、遷移に確率を付与したモデルで、確率的システムの振る舞いを表現します。

**応用**:
- フォールトトレラントシステムの信頼性解析
- ランダム化アルゴリズムの解析
- 性能評価

**ツール**: PRISM

### 11.3 ハイブリッドオートマトン

**ハイブリッドオートマトン** は、離散状態と連続ダイナミクスを組み合わせたモデルです。

**応用**:
- サイバーフィジカルシステム（CPS）
- 自動運転車の制御
- 航空機の飛行制御

## 12. まとめ

### 12.1 状態機械の強み

1. **視覚的明確性**: グラフィカル表現により、振る舞いが直感的に理解できる
2. **形式的基盤**: 数学的に厳密な定義により、形式検証が可能
3. **実行可能性**: シミュレーションとコード生成により、仕様と実装のギャップを削減
4. **スケーラビリティ**: 階層化と並行性により、大規模システムにも適用可能
5. **産業標準**: UML、SDL、SCXMLなどの標準化により、広範な支持

### 12.2 状態機械と形式仕様

状態機械は、形式仕様の中核的な技法の一つとして：
- **モデル駆動開発**: 仕様から実装への自動変換
- **テスト駆動**: 仕様からテストケースの自動生成
- **検証駆動**: モデル検査による性質の保証

これらにより、高品質なソフトウェアとシステムの開発を支援します。

### 12.3 今後の展望

1. **AIとの統合**: 機械学習モデルと状態機械の組み合わせ
2. **クラウドネイティブ**: マイクロサービスの状態管理
3. **量子コンピューティング**: 量子状態機械の研究
4. **形式手法の普及**: より使いやすいツールとワークフローの開発

状態機械は、ソフトウェア工学における最も成功した形式手法の一つであり、今後もシステム設計と検証の中心的役割を果たし続けるでしょう。

---

## 参考文献

### 基礎理論
- Hopcroft, J. E., & Ullman, J. D. (1979). *Introduction to Automata Theory, Languages, and Computation*. Addison-Wesley.
- Harel, D. (1987). "Statecharts: A visual formalism for complex systems". *Science of Computer Programming*, 8(3), 231-274.

### UML State Machines
- OMG. (2017). *Unified Modeling Language Specification Version 2.5.1*. Object Management Group.
- Samek, M. (2009). *Practical UML Statecharts in C/C++, Second Edition*. Newnes.

### 形式検証
- Baier, C., & Katoen, J.-P. (2008). *Principles of Model Checking*. MIT Press.
- Holzmann, G. J. (2003). *The SPIN Model Checker: Primer and Reference Manual*. Addison-Wesley.

### テスト生成
- Utting, M., & Legeard, B. (2007). *Practical Model-Based Testing: A Tools Approach*. Morgan Kaufmann.
- Binder, R. V. (1999). *Testing Object-Oriented Systems: Models, Patterns, and Tools*. Addison-Wesley.

### 産業応用
- ITU-T Recommendation Z.100 (2011). *Specification and Description Language (SDL)*. International Telecommunication Union.
- W3C. (2015). *State Chart XML (SCXML): State Machine Notation for Control Abstraction*. W3C Recommendation.

### Web参考資料
- [UML state machine - Wikipedia](https://en.wikipedia.org/wiki/UML_state_machine)
- [Finite-state machine - Wikipedia](https://en.wikipedia.org/wiki/Finite-state_machine)
- [Extended finite-state machine - Wikipedia](https://en.wikipedia.org/wiki/Extended_finite-state_machine)
- [SCXML - Wikipedia](https://en.wikipedia.org/wiki/SCXML)
- [NuSMV - Wikipedia](https://en.wikipedia.org/wiki/NuSMV)
- [状態遷移図 - Wikipedia](https://ja.wikipedia.org/wiki/%E7%8A%B6%E6%85%8B%E9%81%B7%E7%A7%BB%E5%9B%B3)
- [📖 ステートマシンと状態遷移図について｜JS/TSで堅牢な状態管理を可能にするXStateの解説](https://zenn.dev/susiyaki/books/379ad159248627/viewer/what-is-state-machines-and-statecharts)
- [XState のステートマシンのコンセプト](https://zenn.dev/hayato94087/articles/bdd9156d2a92cb)
