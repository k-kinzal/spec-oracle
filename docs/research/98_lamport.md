# Leslie Lamportの仕様思想

## 概要

Leslie B. Lamport（レスリー・ランポート、1941年生まれ）は、分散システムと並行システムの理論に革命的な貢献をしたアメリカの計算機科学者である。2013年にACMチューリング賞を受賞し、「分散・並行システムの理論と実践への基本的貢献、特に因果性と論理時計、安全性と活性、複製状態機械、逐次一貫性といった概念の発明」が評価された。

Lamportの仕様に関する思想は、ソフトウェア工学における根本的なパラダイムシフトを提唱するものである。彼は一貫して、**仕様はプログラムではなく、数学である**という立場を取り、エンジニアが「コードの上で考える（Thinking Above the Code）」ことの重要性を説いてきた。

2025年1月にMicrosoft Researchを引退したが、彼が創造したTLA+とその背後にある思想は、TLA+ Foundationによって継続的に発展している。

## 核心的主張：「プログラムを書いていないなら、プログラミング言語を使うな」

### 「If You're Not Writing a Program, Don't Use a Programming Language」

Lamportの最も挑発的で重要な主張の一つが、このタイトルの論文（Bulletin of EATCS掲載）に集約されている。彼はプログラムとアルゴリズムを明確に区別する：

- **プログラム（Program）**: プログラミング言語で書かれた実世界のコード
- **アルゴリズム（Algorithm）**: その根底にある抽象的概念

Lamportによれば、アルゴリズムはプログラムではなく、**より単純で表現力豊かな言語——数学の言語——で表現できる**。我々はアルゴリズムをコードではなく、数学で記述すべきである。

### 問題の所在

Lamportが指摘する問題は、人々があまりにも頻繁にアルゴリズムをプログラムレベルで検証しようとすることである。プログラムレベルでは、アルゴリズムはコードの煩雑な詳細によって隠されてしまう。**アルゴリズムを数学として扱うことで、その全体構造をより容易に理解し、うまくデバッグできる**。

### TLA+による実現

Lamportは、このアイデアを実装するシステムとしてTLA（Temporal Logic of Actions）を開発した。TLA+の哲学は、Lamport自身の言葉で「もしあなたがプログラムを書いていないなら、プログラミング言語を使うべきではない。なぜなら、プログラミング言語はコンパイラの要件によって複雑化されているからだ。アルゴリズムを記述する際——実際のコードを書くのではなく——これらの複雑さで自分を苦しめるべきではない」と要約される。

## 「コードの上で考える（Thinking Above the Code）」

### 青写真の比喩

Lamportは、Microsoft Researchでの講演「Thinking Above the Code」で、建築家の比喩を用いる：

> 建築家は、レンガを一つ積む前に、釘を一本打つ前に、詳細な青写真を描く。しかし、プログラマーやソフトウェアエンジニアはめったにそうしない。**ソフトウェアの青写真は仕様（specification）と呼ばれる**。

複雑または重要なシステムをコーディングする前に、極めて厳密な仕様が必要であることは明白であるはずだ——特に並行・分散システムでは。仕様はどのソフトウェアのためにも書かれるべきである。

### 抽象化の階梯

TLA+において、正しさ性質とシステム設計は抽象化の階梯（ladder of abstraction）における段階である：

- **高レベル**: 正しさ性質（correctness properties）
- **中レベル**: システム設計とアルゴリズム
- **低レベル**: 実行可能コードとハードウェア

具体的なプログラムは、異なる詳細レベルで表現できる概念である。ソフトウェアコードは多くの詳細を扱わなければならないが、それらは抽象化することができ、抽象プログラム（abstract program）に到達する。これを数学で表現することは、正しさのために実用的で有益である。

### 思考と数学

Lamportは、思考と数学の関係について明確な立場を取る：

> **思考こそが重要で難しい部分である**。何かを理解したとき、その理解を表現する数学を見つけることができる。数学が理解を提供するのではない。

しかし、単純かつ正確であるための最良の言語は数学である——集合、関数、単純な論理。言語が単純な数学から離れるほど、複雑なプログラムやシステムを理解するのに必要な抽象化を妨げる。

## 仕様の数学的純粋さ

### 数学としての仕様

Lamportの『Specifying Systems』（2002年）は、25年以上にわたる彼の研究の精髄である。この本で彼は、仕様の本質を明確に定義する：

> **仕様とは、システムが何をすべきかの書かれた記述であり、それが機能することを確認する方法でもある**。システムを仕様化することは、それを理解するのに役立つ。

### 数学の役割

仕様を書くための基本ツールは数学である。Lamportはその理由を率直に述べる：

> **数学は、あなたの書き物がどれほど杜撰かを知らせる自然の方法である**。英語や中国語のような不正確な言語で正確であることは難しい。工学において、不正確さはエラーにつながる。エラーを避けるため、科学と工学は数学を言語として採用してきた。

### TLA+の表現力

TLA+は、抽象機械やプログラミング言語に基づく手法の仕様とは異なり、状態述語とアクションは、集合論と述語論理の完全な力を持つ高レベル言語で書かれた任意の式である。これにより、**TLA+は非常に表現力が豊か**になる。

TLA仕様の大部分は、通常の非時相的数学（ordinary, nontemporal mathematics）で構成される。時相論理は、それが得意とする性質——主に安全性と活性——を記述する際にのみ重要な役割を果たす。

### 振る舞いによる仕様

システムは、その許容される振る舞い（allowed behaviors）を記述することで仕様化される——実行の過程でシステムが何を行えるか。これらが、システムが何をすべきかを仕様化する性質である。

**アクション（action）**は数学的式であり、プライムなし変数はステップの最初の状態を参照し、プライムあり変数はその次の状態を参照する。

## 時相論理による仕様

### TLAの誕生

時相論理（Temporal Logic of Actions, TLA）は、仕様を記述するための最も効果的なツールとして同定されている。なぜなら、それがシステムを記述するための数学的で正確な基盤を提供するからである。

Lamportは1983年の論文「Specifying Concurrent Programming Modules」で、状態遷移をプライムありとプライムなしの変数のブール値関数として記述するアイデアを導入した。TLAは、時相式の中でアクションを使用できるようにし、「並行システム検証で使われるすべての推論を形式化し体系化する洗練された方法を提供する」。

### TLAの利点

TLAは、プログラミング言語を排除し、アルゴリズムを直接数学で書くことを可能にした。これにより、次状態関係（next-state relation）を記述するより強力で柔軟な方法が提供された。仕様を数学的式として書くことは、概念的に検証を単純化し、機械検証に必要な証明の厳密な形式化をより容易にする。

### アルゴリズムと仕様の正しさ

Lamportが強調する基本的洞察は：

> **アルゴリズムは単に正しいのではない。アルゴリズムは仕様に対して正しい**。

この見解は、正しさが常に仕様との関係において定義されることを明確にする。仕様のない正しさは意味をなさない。

## 分散システムの仕様への貢献

### 基礎的概念の確立

Lamportは、分散システムの理論の基礎を築いた。彼の貢献は以下の概念を含む：

#### 1. 論理時計と因果性（1978年）

論文「Time, Clocks, and the Ordering of Events in a Distributed System」（2000年にPODC Influential Paper Award受賞）で、Lamportは分散システムにおける事象の順序付けの問題を解決した。

彼の洞察は、複製データベースに関する論文を読んでいるときに訪れた。そのコマンドの論理的順序付けが因果性を違反する可能性があることに気づいたのだ。

Lamportは「論理時計（logical clocks）」の代替概念を初めて正確に定義した。これは、システムのある部分から別の部分へメッセージを送ることによって引き起こされる因果関係に基づいて、事象に部分順序を課すものである。

**Lamportタイムスタンプ**は、分散システムにおける事象の因果順序を決定する基本的アルゴリズムとなった。

#### 2. 逐次一貫性（Sequential Consistency, 1979年）

論文「How to Make a Multiprocessor Computer That Correctly Executes Multiprocess Programs」で、Lamportは**逐次一貫性（sequential consistency）**の概念を定義した：

> 任意の実行の結果が、すべてのプロセッサの操作がある逐次順序で実行されたかのようであり、各個別プロセッサの操作がそのプログラムで指定された順序でこのシーケンスに現れる場合、システムは逐次一貫である。

この定義は、マルチプロセッサシステムとメモリ一貫性モデルの理論の基礎となった。

#### 3. 状態機械複製（State Machine Replication, 1984年）

Lamportは1984年の論文「Using Time Instead of Timeout In Distributed Systems」で状態機械アプローチを提案した。**状態機械複製（SMR）**は、サーバを複製し、クライアントとサーバレプリカの相互作用を調整することで、耐障害性サービスを実装する一般的方法である。

Lamportの貢献は、論理時計を使って状態機械を複製する方法を示したことである。因果順序（Causal Order）に基づく部分的グローバル順序は、通信パターンから推論でき、各サーバが独立して導出できる。状態機械への入力は因果順序で実行され、すべての非障害レプリカについて一貫した状態と出力が保証される。

#### 4. Paxosアルゴリズム（1989年提出、1998年出版）

**Paxosプロトコル**は1989年に最初に提出され、後に1998年にジャーナル論文として出版された。Paxosは洗練された形式主義を提供し、耐障害性分散合意プロトコルの安全性に関する最も初期の証明の一つを含んでいた。

Lamportの状態機械複製（SMR）とPaxosは、合意と複製方法を設計し推論するための**事実上の標準フレームワーク**となった。Google、Yahoo、Microsoft、Amazonを含む多くの企業が、Paxosの基礎を採用した重要な情報システムを構築している。

後にLamportは「Paxos Made Simple」を執筆し、アルゴリズムをより理解しやすく説明した。

#### 5. ビザンチン将軍問題（1982年）

1982年、LamportはMarshall PeaseとRobert Shostakと共に「ビザンチン将軍問題（Byzantine Generals Problem）」の解決策を考案した。

**ビザンチン障害（Byzantine failures）**は、Lamportが普及させた解決策にちなんで命名されている。1970年代のスタンフォード研究所で、LamportはNASAの堅牢な航空電子制御システムの設計を支援するチームの一員だった。ミッションクリティカルなタスクの性質上、形式的保証が絶対的必要性であった。

### Bakeryアルゴリズム（1974年）

**Lamportのベーカリーアルゴリズム（Lamport's Bakery Algorithm）**は、複数の並行スレッドがコードのクリティカルセクションに同時に入ることを防ぐ相互排除アルゴリズムである。1974年に導入されたこのアルゴリズムは、各プロセスにチケット番号を割り当てることで相互排除を保証する——まるでパン屋で順番を待つ顧客のように。

アルゴリズム発見の動機は、Lamportが頻繁に利用していた地元のパン屋の待ち行列システムだった。番号を取得する機械（ミューテックスデバイスとして機能する）を使う代わりに、顧客は昔ながらの方法で列に並ぶ：全員に番号を尋ね、全員より高い番号を選ぶ。最小の番号を持っていれば、次はあなたの番だ。

このアルゴリズムは、同期プリミティブを欠くメモリ（例：2台のコンピュータ間で共有される単純なSCSIディスク）上で相互排除を実装するために使用できる。

また、**Lamportの分散相互排除アルゴリズム**も存在する。これは分散システムにおける相互排除のための競合ベースのアルゴリズムである。すべてのプロセスは、クリティカルセクションに入るための保留中のリクエストのキューを順序付けて保持する。キューはLamportタイムスタンプから導出された仮想タイムスタンプによって順序付けられる。

### 並行プログラムの検証理論

Lamportは、並行プログラムの仕様と検証の理論に中心的な貢献をした。彼は、非同期分散アルゴリズムのための**安全性性質（safety properties）と活性性質（liveness properties）**の概念を最初に明確に述べた。

1977年の論文「Proving the Correctness of Multiprocess Programs」と、1980年の「The Weak and Strong Condition Problem」など、並行アルゴリズムの複雑さとその正しさ証明の必要性を追跡してきた。

## 仕様教育への取り組み

### TLA+ビデオコース

Lamportは、プログラマーやソフトウェアエンジニアが自分自身のTLA+仕様を書く方法を教えるために、一連のビデオ講義を作成している。このコースは「進行中の作品」として位置づけられ、プログラミング概念の基本的理解と初等数学の知識を前提とする。

**特徴：**
- ビデオは注意深い視聴と実際の思考を要求する（軽い娯楽ではない）
- 各ビデオには完全なスクリプトが提供される
- ネットワーク接続が遅い人は低解像度版をダウンロードしてオフラインで視聴可能
- URL: [https://lamport.azurewebsites.net/video/videos.html](https://lamport.azurewebsites.net/video/videos.html)

**カバーされるトピック：**
- TLA+における状態機械
- 「Die Hard」例題（パーサーとTLCでの仕様チェックを学ぶ）
- Paxos Commit（データベーストランザクションをコミットする実際の耐障害性アルゴリズムの仕様化）
- 交互ビットプロトコル（活性と公平性の説明）

### 『Specifying Systems』教科書（2002年）

Lamportは2002年に、TLA+の完全な教科書『Specifying Systems: The TLA+ Language and Tools for Software Engineers』を出版した。

この本は古いリソースだが、実践的というよりも理論に深く踏み込んでおり、より深い内容を提供する。無料でダウンロード可能である。

### The TLA+ Hyperbook

Lamportは、更新されたTLA+リファレンス「The TLA+ Hyperbook」も作成しており、公式ウェブサイトから入手可能である。

### 教育哲学

Lamportの教育アプローチは、「エンジニアの数学への反感を克服するための途方もない試み（quixotic attempt）」と自ら形容している。彼は、数学が本質的に難しいのではなく、それを適切に提示し、その価値を示すことが重要だと考えている。

TLA+の設計自体が教育的意図を持つ：プログラマーが慣れ親しんだ概念（状態、遷移、変数）を使いながら、数学的厳密性を導入する。

## LaTeX：数学的組版への貢献

### LaTeXの開発

Lamportは、分散システムの理論家としての業績に加えて、**LaTeX文書準備システムの最初の開発者**としても広く知られている。LaTeXは1980年代初頭にLamportによってSRI Internationalで書かれた。

LaTeXは、Donald E. Knuthの **TeX** 組版言語に基づいている。LaTeXは、TeXをより容易に利用するための高レベルで記述的なマークアップ言語を提供する：TeXが文書レイアウトを処理し、LaTeXが文書処理のためのコンテンツ側を処理する。

### 数学表現の標準

LaTeXは、複雑な数学記法のサポートにより、多くの分野で科学文書の通信と出版、技術ノート作成に広く使用されている。**LaTeXは、科学文書で数学的表現を組版するための事実上の標準となった**。

Lamportは1984年と1985年にLaTeXマクロのバージョンをリリースした。1989年8月21日、スタンフォードでのTeX Users Group（TUG）会議で、LamportはLaTeXの保守と開発をFrank Mittelbachに引き継ぐことに合意した。

### 権威的ガイド

Lamportは、LaTeXコンピュータ組版システムの権威的ユーザーズガイドとリファレンスを執筆した。これはLaTeX2eリリースで利用可能な機能を文書化するために改訂された。

### 数学と文書作成の統合

LaTeXの成功は、Lamportの「数学は正確な思考のための言語である」という哲学の実践的証明でもある。LaTeXは、数学者、科学者、エンジニアが数学的表現を美しく、正確に文書化することを可能にした。

## 主要業績と受賞

### チューリング賞（2013年）

Lamportは、**2013年ACM A.M.チューリング賞**を受賞した。受賞理由は：

> 「分散・並行システムの理論と実践への基本的貢献、特に因果性と論理時計、安全性と活性、複製状態機械、逐次一貫性といった概念の発明」

チューリング賞の公式声明は、Lamportについて次のように述べている：

> 「Lamportは、一見カオス的に見える分散コンピューティングシステムの振る舞いに、明確で良く定義された一貫性を課した」

### その他の栄誉

- **ACM Fellow**（2014年）：「分散・並行システムの理論と実践への基本的貢献」により選出
- **PODC Influential Paper Award**（2000年）：「Time, Clocks, and the Ordering of Events in a Distributed System」に対して
- 多数の他の賞と名誉

### 産業への影響

Lamportの形式検証ツール（TLA+とTLC）は、2005年のリリース前にMicrosoftのXbox 360のハードウェアで使用される一貫性プロトコルの重大なエラーを発見するために使用された。

TLA+は、以下で産業利用のために採用されている：
- 半導体メーカー
- 分散システムとデータベースシステムを構築する企業
- その他のテクノロジー企業
- 小売店の決済システムなどの主流アプリケーション

## Lamportの遺産と影響

### 引退と継続（2025年）

Lamportは**2025年1月にMicrosoft Researchを引退**した。彼は2001年から同社で働いていた。

しかし、彼の遺産は継続している。**TLA+は現在TLA+ Foundationに所属**しており、彼の引退後も彼の仕事が保守・発展されることが保証されている。

### 永続的影響

Lamportの貢献は計算機科学の基礎を形成している：

1. **分散システム理論**：彼の論理時計、Paxos、ビザンチン合意に関する研究は、現代のクラウドコンピューティングとブロックチェーン技術の基盤である

2. **形式手法の実用化**：TLA+は、形式手法が「象牙の塔」から実世界の産業問題へ移行できることを実証した

3. **数学的思考の普及**：「コードの上で考える」という彼のメッセージは、ソフトウェア工学における抽象化と数学的推論の重要性を強調している

4. **科学的出版の変革**：LaTeXは、数学的・科学的コミュニケーションの方法を変えた

### 「A Science of Concurrent Programs」（2024年）

引退直前の2024年6月版の論文「A Science of Concurrent Programs」で、Lamportは並行プログラムの科学的記述に関する彼の最新の思考を展開している。この論文では、抽象プログラムをTLA式として書く方法が議論されており、TLA+が単なる仕様言語ではなく、並行プログラムの科学的理論の基盤であることを示している。

## Lamportの仕様哲学の本質

### 10の核心原則

Lamportの仕様思想は、以下の原則に要約できる：

1. **仕様はプログラムではない**：仕様は数学であり、プログラミング言語の制約から自由である

2. **数学は精確さの保証**：不正確な自然言語と異なり、数学は曖昧さを排除する

3. **抽象化が理解を生む**：コードの詳細から離れ、より高いレベルで考えることで、システムの本質を理解できる

4. **思考が先、形式化が後**：数学は理解を表現する手段であり、理解を生み出す手段ではない

5. **振る舞いによる仕様**：システムは、許容される状態の列（振る舞い）の集合として定義される

6. **正しさは相対的**：アルゴリズムは仕様に対して正しい。仕様のない正しさは無意味である

7. **安全性と活性の分離**：システムの性質は「悪いことが起こらない」（安全性）と「良いことがいずれ起こる」（活性）に分類される

8. **青写真としての仕様**：建築家が青写真を描くように、ソフトウェアエンジニアは仕様を書くべきである

9. **時相論理の適切な使用**：ほとんどの仕様は通常の数学で書かれ、時相論理は時間依存性質に使用される

10. **教育と普及の責任**：形式手法の価値を広めることは、研究者の責任である

### 仕様とは何か：Lamportの答え

Lamportの視点から、**仕様とは以下のものである**：

- システムの許容される振る舞いの数学的記述
- 実装の正しさを判断する基準
- システムを理解し、推論し、検証するためのツール
- 実装に先立つ思考の産物
- 抽象から具体への橋渡し

彼にとって、仕様の本質は**抽象化のレベルを選択する自由**にある。TLA+では、同じシステムを異なる抽象度で記述でき、精緻化マッピングによって階層を接続できる。

## まとめ：Lamportからの教訓

Leslie Lamportの仕様思想は、ソフトウェア工学における知的誠実さの呼びかけである。彼は、複雑なシステムを構築する前に、まずそれを理解しなければならないと主張する。そして理解は、曖昧さのない言語——数学——によって最もよく表現される。

**「プログラムを書いていないなら、プログラミング言語を使うな」**というスローガンは挑発的だが、その背後にある洞察は深遠である：適切な抽象化レベルで作業することで、問題の本質を見ることができ、偶発的複雑性に惑わされない。

Lamportの遺産は、彼が発明したアルゴリズムやツールだけでなく、**ソフトウェア工学を科学にする**という彼のビジョンにある。TLA+、Paxos、論理時計、LaTeX——これらはすべて、同じ哲学の表現である：**明確な思考は明確な記述を生み、明確な記述は信頼できるシステムを生む**。

2025年の引退後も、Lamportの思想は新しい世代のエンジニアに影響を与え続けている。彼が示したのは、形式手法は実用的であり、数学は美しく、そして良いソフトウェアは**コードを書く前に、コードの上で考えること**から始まるということである。

---

## 主要参考文献とソース

### Lamportの仕様哲学
- [If You're Not Writing a Program, Don't Use a Programming Language - Bulletin of EATCS](https://bulletin.eatcs.org/index.php/beatcs/article/view/539)
- [HLF Blogs: Leslie Lamport Thinks Your Code Is Bad - The Aperiodical](https://aperiodical.com/2018/09/hlf-blogs-leslie-lamport-thinks-your-code-is-bad/)
- [Thinking Above the Code - Microsoft Research (PDF)](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/leslie_lamport.pdf)
- [Thinking Above the Code - Microsoft Research (Video)](https://www.microsoft.com/en-us/research/video/thinking-above-the-code/)

### Specifying Systems
- [Specifying Systems - Leslie Lamport (PDF)](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)
- [Specifying and Verifying Systems With TLA+](https://lamport.org/pubs/spec-and-verifying.pdf)
- [Specifying Systems - Amazon](https://www.amazon.com/Specifying-Systems-Language-Hardware-Engineers/dp/032114306X)

### 分散システムへの貢献
- [Leslie Barry Lamport - A.M. Turing Award Laureate](https://amturing.acm.org/award_winners/lamport_1205376.cfm)
- [Paxos (computer science) - Wikipedia](https://en.wikipedia.org/wiki/Paxos_(computer_science))
- [Byzantizing Paxos by Refinement (PDF)](https://lamport.azurewebsites.net/tla/byzsimple.pdf)
- [SE Radio 203: Leslie Lamport on Distributed Systems](https://se-radio.net/2014/04/episode-203-leslie-lamport-on-distributed-systems/)

### 基礎的概念
- [Sequential Consistency - Jepsen](https://jepsen.io/consistency/models/sequential)
- [Lamport timestamp - Wikipedia](https://en.wikipedia.org/wiki/Lamport_timestamp)
- [State machine replication - Wikipedia](https://en.wikipedia.org/wiki/State_machine_replication)
- [Lamport's bakery algorithm - Wikipedia](https://en.wikipedia.org/wiki/Lamport's_bakery_algorithm)
- [Lamport's distributed mutual exclusion algorithm - Wikipedia](https://en.wikipedia.org/wiki/Lamport's_distributed_mutual_exclusion_algorithm)

### 教育リソース
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [Learning TLA+ - Leslie Lamport](https://lamport.azurewebsites.net/tla/learning.html)
- [Learn TLA+](https://learntla.com/)
- [TLA in Practice and Theory Part 1: The Principles of TLA+](https://pron.github.io/posts/tlaplus_part1)

### LaTeX
- [LaTeX - Wikipedia](https://en.wikipedia.org/wiki/LaTeX)
- [LaTeX: A Document Preparation System - Amazon](https://www.amazon.com/LaTeX-Document-Preparation-System-2nd/dp/0201529831)

### キャリアと受賞
- [Leslie Lamport - Wikipedia](https://en.wikipedia.org/wiki/Leslie_Lamport)
- [Leslie Lamport at Microsoft Research](https://www.microsoft.com/en-us/research/people/lamport/)
- [The Writings of Leslie Lamport](https://lamport.azurewebsites.net/pubs/pubs.html)
- [TLA+ Foundation - Microsoft Research Blog](https://www.microsoft.com/en-us/research/blog/tla-foundation-aims-to-bring-math-based-software-modeling-to-the-mainstream/)

### 最新研究
- [A Science of Concurrent Programs (2024年6月版)](https://lamport.org/tla/science.pdf)
- [Issue #1 - A Science of Concurrent Programs](https://dtornow225.substack.com/p/issue-1-a-science-of-concurrent-programs)

### 日本語リソース
- [レスリー・ランポート - Wikipedia](https://ja.wikipedia.org/wiki/%E3%83%AC%E3%82%B9%E3%83%AA%E3%83%BC%E3%83%BB%E3%83%A9%E3%83%B3%E3%83%9D%E3%83%BC%E3%83%88)
- [Time, Clocks, and the Ordering of Events in a Distributed System 要約](https://gist.github.com/sile/5f4c04d15b8ff25e70c9d3c18670397b)
