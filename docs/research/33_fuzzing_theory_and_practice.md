# Fuzzingの理論と実践

## 1. はじめに

Fuzzing（ファジング、ファズテスト）は、ソフトウェアのバグや脆弱性を発見するための自動テスト技術であり、ランダムまたは半ランダムなデータをプログラムに入力して、クラッシュ、メモリリーク、異常動作などを検出する。1988年にBarton Millerによって偶然発見されて以来、Fuzzingは現代のソフトウェアセキュリティとテストにおいて不可欠なツールとなっている。

本調査では、Fuzzingの歴史、各種アプローチ、最新技術、そして仕様検証との関係について詳細に論じる。

## 2. Fuzzingの歴史

### 2.1 起源：1988年の嵐の夜

1988年、Barton Miller教授は自宅のコンピューターからキャンパスのUnixシステムにログインしていた。中西部の激しい雷雨がダイヤルアップモデム接続にノイズを引き起こし、Miller教授は多くのプログラムが乱れたデータに対処できないことに気づいた—それらはクラッシュし、ハングアップし、制御不能な方法で動作を停止した ([Trail of Bits - Fuzzing Like 1989](https://blog.trailofbits.com/2018/12/31/fuzzing-like-its-1989/))。

### 2.2 最初のFuzzingプロジェクト

Miller教授は、ウィスコンシン大学の授業で「Operating System Utility Program Reliability – The Fuzz Generator」というタイトルのプロジェクトを学生に割り当てた。学生たちは、Unixプログラムの信頼性をテストするために、ランダムなデータで攻撃し、クラッシュを監視する基本的なコマンドラインファザーを開発することになった ([Wisconsin CS - Trials and Tribulations](https://www.cs.wisc.edu/2021/01/14/the-trials-and-tribulations-of-academic-publishing-and-fuzz-testing/))。

### 2.3 命名の由来

Miller教授によると、「プロジェクトの説明を書く過程で、この種のテストに名前を付ける必要がありました。ランダムで非構造化されたデータの感覚を呼び起こす名前が欲しかった。いくつかのアイデアを試した後、『fuzz』という用語に落ち着きました」([Wikipedia - Fuzzing](https://en.wikipedia.org/wiki/Fuzzing))。

### 2.4 最初の論文と発見

オリジナルのFuzzingの論文は「An Empirical Study of the Reliability of UNIX Utilities」というタイトルで、ソースコードのコメントの著作権日付は1989年であったが、論文の公表日は1990年であった。

研究では、一般的なユーティリティの25-33%がこのような条件下でクラッシュ、ハング、またはその他の失敗をすることが判明した ([CISPA - Random Testing with Fuzz](https://cispa.de/dls-miller))。

### 2.5 Fuzz Revisited

1995年と2006年には、Miller教授と共同研究者により「Fuzz Revisited」として再検証が行われ、Unixユーティリティとサービスの信頼性を再調査した ([ResearchGate - Fuzz Revisited](https://www.researchgate.net/publication/239668581_Fuzz_Revisited_A_Re-Examination_of_the_Reliability_of_UNIX_Utilities_and_Services))。

## 3. Fuzzingの分類

### 3.1 ブラックボックスFuzzing

ブラックボックスFuzzingは、プログラムの知識なしに入力を生成する。ブラックボックスファザーは、内部動作や実装の知識なしにターゲットプログラムの入力を生成する ([Fuzzing Book - Greybox Fuzzer](https://www.fuzzingbook.org/html/GreyboxFuzzer.html))。

**特徴**:
- ゼロから入力を生成するか、有効な入力ファイルの静的コーパスに基づいて変異を行う
- 毎秒数十万のランダムに生成された入力を簡単に作成できる
- 実装が単純で高速
- プログラム内部の情報を使用しない

**制限**:
- 深いコードパスに到達することが困難
- 複雑な入力制約を通過できない可能性がある

### 3.2 ホワイトボックスFuzzing

ホワイトボックスFuzzingでは、コードが解析され、静的手法と同様に形式的モデルに変換され、最後の詳細まで体系的に検証される ([MPG - Greybox Fuzzing](https://www.mpg.de/20666079/software-security-gap-fuzzing))。

**特徴**:
- 毎秒1つまたは2つの入力しか作成しない
- バグの不在を形式的に検証できる
- 記号実行などの技術を使用

**利点**:
- 形式的保証を提供可能
- 列挙できるすべてのパスでバグの不在を証明できる

**制限**:
- 非常に遅い（1秒あたり1-2入力）
- パス爆発問題に直面
- 合理的な時間内にすべてのパスを列挙できない場合、部分的保証のみ提供

### 3.3 グレーボックスFuzzing

グレーボックスFuzzingは、カバレッジフィードバックを活用してプログラムのより深い部分に到達する方法を学習する ([Fuzzing Book - Greybox Fuzzer](https://www.fuzzingbook.org/html/GreyboxFuzzer.html))。

**特徴**:
- ブラックボックスファザーと同じ速さで入力を生成
- ホワイトボックスファザーのように、既に実行されたプログラムの部分に関する追加のフィードバックを使用
- 同じソフトウェア要素の反復的なテストを回避し、プロセス全体の速度低下を防ぐ

**実用性**:
- ブラックボックスFuzzingの速度とホワイトボックスFuzzingのプログラムフィードバックを組み合わせる
- ニッチ機能を持つソフトウェアの部分が見過ごされないようにする
- Googleだけでも、10万台のコンピューターがグレーボックスファザーの実行に専念し、24時間体制で500以上のソフトウェアプロジェクトのテストに使用されている

### 3.4 比較表

| 特性 | ブラックボックス | ホワイトボックス | グレーボックス |
|------|------------------|------------------|----------------|
| 速度 | 非常に高速（数十万/秒） | 非常に遅い（1-2/秒） | 高速（数万/秒） |
| プログラム情報 | なし | 完全 | カバレッジ情報 |
| 保証 | なし | 形式的保証可能 | 経験的保証 |
| 実装複雑度 | 低 | 高 | 中 |
| 深いパス到達 | 困難 | 可能 | 可能 |

## 4. カバレッジガイドFuzzing

### 4.1 基本概念

カバレッジガイドFuzzingは、ブロックカバレッジ（新しい基本ブロックにヒットすることを報酬とする）やエッジカバレッジ（制御フローグラフで新しく発見されたエッジを測定する）などのアプローチを使用してカバレッジを測定する ([ClusterFuzz - Coverage Guided](https://google.github.io/clusterfuzz/reference/coverage-guided-vs-blackbox/))。

これらのメカニズムにより、ファザーは新しいカバレッジをもたらすテストケースのみを保持でき、ファジングキャンペーンをアプリケーションコードのより深い部分に導き、バグを見つける可能性を高める。

### 4.2 American Fuzzy Lop (AFL)

American Fuzzy Lop（AFL）は、インストルメンテーションガイド遺伝的アルゴリズムと結合されたブルートフォースファザーである ([Wikipedia - AFL](https://en.wikipedia.org/wiki/American_fuzzy_lop_(fuzzer)))。

**主要な特徴**:
- プログラム制御フローへの微妙でローカルスケールの変更を簡単に検出するために、修正されたエッジカバレッジの形式を使用
- 産業界と学術研究者の両方に採用された、最も使用され拡張されているファザーの1つ
- AFLに基づく現代のツール（AFL++、LibAFL、libfuzzer）はすべてカバレッジガイドFuzzingの単純なアイデアに基づいている

### 4.3 AFL++

AFL++は、コミュニティパッチ、QEMU 5.1アップグレード、衝突のないカバレッジ、拡張されたlaf-intel & redqueen、AFLfast++パワースケジュール、MOpt変異器、unicorn_mode、その他多くの機能を備えたAFLである ([GitHub - AFL++](https://github.com/AFLplusplus/AFLplusplus))。

### 4.4 FuzzBench評価

「Dissecting American Fuzzy Lop」研究では、FuzzBenchを使用したAFLの評価が行われ、AFLの個々のコンポーネントとその貢献度を分析した ([ACM TOSEM - Dissecting AFL](https://dl.acm.org/doi/full/10.1145/3580596), [ResearchGate - Dissecting AFL](https://www.researchgate.net/publication/367297404_Dissecting_American_Fuzzy_Lop_-_A_FuzzBench_Evaluation))。

### 4.5 最近の進展（2024-2025）

2024-2025年の最近の論文には以下が含まれる:
- 「AFLNet Five Years Later: On Coverage-Guided Protocol Fuzzing」（2025年）
- 「SGMFuzz: State Guided Mutation Protocol Fuzzing」（2025年）
- 機械学習技術を使用した脆弱性検出のためのFuzzing強化に関する2024年のレビュー

## 5. 文法ベースおよび構造認識Fuzzing

### 5.1 文法ベースFuzzing

スマート（モデルベース、文法ベース、またはプロトコルベース）ファザーは、入力モデルを活用してより高い割合の有効な入力を生成する ([Fuzzing Book - Grammars](https://www.fuzzingbook.org/html/Grammars.html))。

**利点**:
- 入力が形式文法でモデル化できる場合、スマート生成ベースファザーは文法に関して有効な入力を生成するために生成規則をインスタンス化する
- 文法を介して入力を指定することで、特に複雑な入力形式に対して非常に体系的で効率的なテスト生成が可能になる

### 5.2 構造認識Fuzzing

AFLSmartは、シードファイルの高レベル構造表現を受け取ることで、AFLを入力構造認識にする ([GitHub - Google Fuzzing](https://github.com/google/fuzzing/blob/master/docs/structure-aware-fuzzing.md))。これにより、AFLのようなランダムなビットフリップ変異を回避し、PDF、PNG、WAVなどの構造化ファイル形式を処理するアプリケーションのテストにおいてカバレッジベースのグレーボックスFuzzingを非常に効果的にする。

### 5.3 主要ツール

#### Superion

Superionは、構造化入力を処理するプログラム向けの新しい文法認識カバレッジベースグレーボックスFuzzingアプローチを提案し、AFLの拡張として実装されている ([arXiv - Superion](https://arxiv.org/pdf/1812.01197))。

#### Gramatron

Gramatronは、効果的な文法認識Fuzzingを実現する ([ISSTA - Gramatron](https://hexhive.epfl.ch/publications/files/21ISSTA.pdf), [ResearchGate - Gramatron](https://www.researchgate.net/publication/353168541_Gramatron_effective_grammar-aware_fuzzing))。

#### NAUTILUS

NAUTILUSも注目すべき構造認識Fuzzingツールである。

### 5.4 プロトコルFuzzing

Protobufsは構造化データをシリアライズする便利な方法を提供し、LPMは構造認識Fuzzingのためにprotobufsを変異させる簡単な方法を提供する。たとえば、Config_fuzz_testはEnvoy設定APIをファズする ([Fuzzing Book - Efficient Grammar Fuzzing](https://www.fuzzingbook.org/html/GrammarFuzzer.html))。

## 6. 変異戦略とシード選択

### 6.1 シードスケジューリング

シードスケジューリング、つまり次のFuzzing反復のシードとしてシードプールから入力を選択するプロセスは、カバレッジベースのグレーボックスFuzzingにおいて中心的な役割を果たす ([ISSTA - Seed Selection](https://hexhive.epfl.ch/publications/files/21ISSTA2.pdf))。

### 6.2 進化的アプローチ

研究者は、シード間の変異関係を調査することで「シード変異ツリー」を設計し、シードスケジューリング問題をモンテカルロ木探索（MCTS）問題としてモデル化した ([arXiv - AlphaFuzz](https://arxiv.org/abs/2101.00612), [ResearchGate - AlphaFuzz](https://www.researchgate.net/publication/348212826_AlphaFuzz_Evolutionary_Mutation-based_Fuzzing_as_Monte_Carlo_Tree_Search))。

### 6.3 適応的変異戦略

最近の研究では、プログラム適応的なアプローチだけでなく、シード適応的なアプローチが強調されている。一部の技術は、シード入力の個別の特性を捕捉し、異なるシード入力に対して異なる変異戦略を適用することを目指している ([IEEE - Learning Seed-Adaptive](https://ieeexplore.ieee.org/document/10172576/), [Korea U - SeamFuzz](https://prl.korea.ac.kr/papers/icse23-seamfuzz.pdf))。

あるアプローチでは、シード入力をその構文的および意味的特性に基づいてグループにクラスタリングし、Thompson サンプリングの変形を活用してシードクラスターごとに変異メソッドを選択する異なる確率分布をオンラインで学習する。

### 6.4 位置センシティブ変異

一部のアプローチでは、進化的アルゴリズムを使用して演算子と変異位置の最適な選択確率分布を学習し、学習した分布でシード変異をガイドする位置センシティブ戦略を設計する ([ScienceDirect - Adaptive Mutation](https://www.sciencedirect.com/science/article/abs/pii/S002002552500091X))。

## 7. ハイブリッドFuzzing：記号実行との統合

### 7.1 ハイブリッドFuzzingの概念

ハイブリッドFuzzingは、従来のFuzzingの基礎に記号実行技術を追加したものであり、現在Fuzzingの新しいブランチに発展している ([ACM - Survey on Hybrid Fuzzing](https://dl.acm.org/doi/10.1145/3444370.3444570))。

### 7.2 Driller

Drillerは、相補的な方法でFuzzingと選択的具体的実行を活用するハイブリッド脆弱性発掘ツールであり、具体的解析に固有のパス爆発とFuzzingの不完全性を軽減するために、それらの弱点を緩和する ([NDSS - Driller](https://www.ndss-symposium.org/wp-content/uploads/2017/09/driller-augmenting-fuzzing-through-selective-symbolic-execution.pdf), [Semantic Scholar - Driller](https://www.semanticscholar.org/paper/Driller:-Augmenting-Fuzzing-Through-Selective-Stephens-Grosen/f049751103f13d1ce6080418813e2a26820713e1))。

ハイブリッドファズテストでは、限定的な記号探索を利用して「フロンティアノード」を見つけ、その後Fuzzingを使用して、フロンティアノードに至るパスに従うように事前制約されたランダム入力でプログラムを実行する。

### 7.3 QSYM

QSYMは、動的バイナリ変換を使用して記号エミュレーションとネイティブ実行を緊密に統合し、命令レベルの記号エミュレーションを可能にする ([USENIX - QSYM](https://www.usenix.org/conference/usenixsecurity18/presentation/yun), [ACM - QSYM](https://dl.acm.org/doi/10.5555/3277203.3277260), [Semantic Scholar - QSYM](https://www.semanticscholar.org/paper/QSYM-:-A-Practical-Concolic-Execution-Engine-for-Yun-Lee/79b4d4fb6800d89f1f649dfd49b7b28727e10dde), [GitHub - QSYM](https://github.com/sslab-gatech/qsym))。

**主要な特徴**:
- より良いパフォーマンスのために従来の具体的実行器の厳密な健全性要件を緩和
- 検証のためにより高速なファザーを利用
- LAVA-Mデータセットで、VUzzerの14倍のバグを発見
- 126個のバイナリのうち104個でDrillerを上回る性能

### 7.4 最近の進展（2024年）

2024年の研究には、緊密に結合されたハイブリッドFuzzingと動的指向グレーボックスFuzzingアプローチに関する研究が含まれており、この分野の継続的な進歩を示している ([IEEE - Tightly-Coupled Hybrid](https://www.computer.org/csdl/journal/tq/2024/05/10418578/1Ublds1CRt6))。

## 8. サニタイザ（Sanitizers）

### 8.1 サニタイザの役割

サニタイザは、ソフトウェアの様々な種類のバグや脆弱性を検出および防止するのに役立つツールであり、コンパイラで利用可能で、追加のランタイムチェックを追加するためにコードをインストルメンテーションすることで動作する ([Wikipedia - Code Sanitizer](https://en.wikipedia.org/wiki/Code_sanitizer))。

サニタイザを使用する一般的な方法の1つは、Fuzzingと組み合わせることであり、Fuzzingはバグをトリガーする可能性の高い入力を生成する。

### 8.2 主要なサニタイザ

Googleは以下のサニタイザを開発した ([GitHub - Google Sanitizers](https://github.com/google/sanitizers)):

- **LeakSanitizer (LSan)**: メモリリーク検出
- **ThreadSanitizer (TSan)**: データ競合とデッドロック検出
- **MemorySanitizer (MSan)**: 初期化されていないメモリの使用検出
- **UndefinedBehaviorSanitizer (UBSan)**: 未定義動作の検出（細かい制御が可能）

### 8.3 AddressSanitizer (ASan)

Fuzzingは、バッファオーバーフローやuse-after-freeエラーなどの、そうでなければ気づかれないかもしれないメモリエラーを検出するのに役立つため、ASanの使用から大きな恩恵を受ける ([Fuzzing Project - Tutorial 2](https://fuzzing-project.org/tutorial2.html), [Testing Handbook - ASan](https://appsec.guide/docs/fuzzing/techniques/asan/))。

ただし、Fuzzingプロセスを約2-4倍遅くする可能性があり、これはテストの信頼性と深さの向上とのトレードオフである。

### 8.4 MemorySanitizer (MSan)

MemorySanitizerは、初期化されていない読み取りの検出器である。MemorySanitizerは、すべてのプログラムコードをインストルメンテーションする必要があり、C/C++の依存関係は-fsanitize=memoryオプションを使用してClangで再コンパイルする必要がある ([Rust Unstable Book - Sanitizer](https://doc.rust-lang.org/beta/unstable-book/compiler-flags/sanitizer.html))。

### 8.5 パフォーマンスオーバーヘッド

ASan、UBSan、MSanは、Fuzzing速度を平均でそれぞれ3.6倍、2.0倍、46倍遅くする。このパフォーマンスオーバーヘッドは、Fuzzingキャンペーンでサニタイザを使用する際の重要な考慮事項である ([arXiv - Sand](https://arxiv.org/html/2402.16497v1))。

### 8.6 Fuzzingでのサニタイザの重要性

サニタイザは、多くのセキュリティ上の欠陥が必ずしもクラッシュを引き起こすわけではないという問題に対処するために設計されている。コンパイル時にサニタイザが有効になっていると、コンパイラはターゲットプログラムに様々なチェックを挿入するために大量にインストルメンテーションを行う。実行時には、これらのチェックに対する違反はプログラムのクラッシュを引き起こす。したがって、サニタイザが有効なプログラムでのFuzzingは、ソフトウェアのバグを発見する上でより効果的である ([Medium - Beyond Sanitizers](https://medium.com/mit-security-seminar/beyond-sanitizers-guided-fuzzing-and-security-hardening-9cc8155e19fb))。

## 9. 継続的Fuzzing インフラストラクチャ

### 9.1 OSS-Fuzz

OSS-Fuzzは、Core Infrastructure InitiativeおよびOpenSSFと協力して、最新のFuzzing技術とスケーラブルで分散された実行を組み合わせることで、一般的なオープンソースソフトウェアをより安全で安定したものにすることを目指している ([GitHub - OSS-Fuzz](https://github.com/google/oss-fuzz), [Google OSS-Fuzz Docs](https://google.github.io/oss-fuzz/))。

Googleは、オープンソースプロジェクトのファザーを実行し、検出されたバグを開発者に非公開で警告する無料サービスとしてOSS-Fuzzを作成した ([Google Open Source Blog - OSS-Fuzz](https://opensource.googleblog.com/2016/12/announcing-oss-fuzz-continuous-fuzzing.html))。

**成果**:
- 2023年8月時点で、OSS-Fuzzは1,000プロジェクトにわたって10,000以上の脆弱性と36,000のバグの特定と修正に貢献
- C/C++を超えて成長し、Go、Rust、Pythonなどのメモリ安全言語での問題も検出

### 9.2 ClusterFuzz

ClusterFuzzは、OSS-Fuzzの背後にある分散Fuzzingインフラストラクチャであり、当初はChromeを大規模にファズするために構築された ([GitHub - ClusterFuzz](https://github.com/google/clusterfuzz), [OSS-Fuzz ClusterFuzz](https://google.github.io/oss-fuzz/further-reading/clusterfuzz/))。

GoogleはClusterFuzzをすべてのGoogle製品のFuzzingに使用し、OSS-FuzzのFuzzingバックエンドとして使用している。

**主要機能**:
- 最適な結果のために複数のカバレッジガイドFuzzingエンジン（libFuzzer、AFL、AFL++、Honggfuzz）をサポート
- アンサンブルFuzzingとFuzzing戦略を使用
- OSS-Fuzzに統合された850プロジェクトにわたって8,900以上の脆弱性と28,000のバグの特定と修正に貢献

### 9.3 FuzzBench

2020年初頭、OSSチームは、Fuzzing研究を大規模に評価できるサービスとしてFuzzBenchを開始した ([Code Intelligence - OSS-Fuzz](https://www.code-intelligence.com/blog/intro-to-oss-fuzz))。

## 10. カーネルとシステムFuzzing

### 10.1 syzkaller

syzkallerは、教師なしカバレッジガイドカーネルファザーである。FreeBSD、Fuchsia、gVisor、Linux、NetBSD、OpenBSD、Windowsをサポートしている ([GitHub - syzkaller](https://github.com/google/syzkaller))。

syzkallerは、Linuxカーネル用の最高のファザーの1つである。カバレッジ（KCOVを通じて）をサポートし、ファズしたいシステムコールを宣言的に記述する方法を提供する ([Cloudflare - Linux Kernel Fuzzing](https://blog.cloudflare.com/a-gentle-introduction-to-linux-kernel-fuzzing/))。

**主要機能**:
- 各システムコールの引数ドメインを示すテンプレートに依存
- コードカバレッジ情報からのフィードバックを使用してFuzzingをガイド
- 小さなプログラムを大量に生成し、常にコードカバレッジを増やすことを目指す

### 10.2 ネットワークプロトコルFuzzing

syzkallerは、ネットワークスタックの外部Fuzzingをサポートしている。これは、TUN/TAPインターフェースを使用して実現される ([GitHub - syzkaller Network](https://github.com/google/syzkaller/blob/master/docs/linux/external_fuzzing_network.md), [Xairy - RCE Bugs](https://xairy.io/articles/syzkaller-external-network))。

仮想ネットワークインターフェースを設定し、外部ネットワークから受信されているかのようにカーネルにパケットを送信できる。

**擬似システムコール**:
- `syz_emit_ethernet`: 仮想インターフェースを通じて外部的にパケットを送信
- `syz_extract_tcp_res`: パケットを外部的に受信し、後続のパケットで使用するためにTCPシーケンス番号を解析

### 10.3 ファイルシステムFuzzing

ネットワークは、ファイルシステムよりもはるかにファズしやすい。データはソケットを通じてきれいに出入りし、すべていくつかのioctlとsetsockopt呼び出しで設定できる。これをファイルシステムと比較すると、バイナリBLOBを処理し、それらをマウントおよびアンマウントする必要があり、または特定のハードウェアに依存する可能性のある他のサブシステムと比較する必要がある ([LWN - Coverage-Guided Kernel Fuzzing](https://lwn.net/Articles/677764/))。

### 10.4 影響

Dmitry Vyukovによるsyzkaller（別名syzbot）は、非常に強力なCIスタイルで継続的に実行されるカーネルファザーであり、すでに数百の問題を発見している ([Collabora - Using syzkaller](https://www.collabora.com/news-and-blog/blog/2020/03/26/syzkaller-fuzzing-the-kernel/))。

## 11. 機械学習とニューラルFuzzing

### 11.1 2024-2025年の最新動向

**ディープニューラルモデルとFuzzingの調査**:

ディープニューラルネットワーク（DNN）はFuzzingの効率を大幅に改善したが、意味的に無効なシード、高い計算オーバーヘッド、限定的なクロスドメイン適応性などの課題が未解決のままである ([ScienceDirect - Survey on DNN Fuzzing](https://www.sciencedirect.com/science/article/pii/S0950584925001363))。

2つの変革的な方向性:
1. **LLMパワードFuzzing**: 生成AIとドメイン固有のファインチューニングを組み合わせてコンテキスト認識入力を生成
2. **ニューロシンボリック統合**: 記号実行の精度とニューラルネットワークのスケーラビリティを融合してパス爆発に対処

### 11.2 LLMベースの深層学習ライブラリFuzzing

**FD-FACTORY**は、DL APIテストのためのファズドライバーを生成するためにLLMを活用する完全自動化フレームワークである ([Springer - FD-FACTORY](https://link.springer.com/article/10.1186/s42400-025-00532-9))。

**成果**:
- PyTorchで308,351行、TensorFlowで528,427行の合計カバレッジを達成
- 以前のアプローチによって報告された結果を大幅に上回る
- テストプロセス全体を通じてLLMサーバーとの繰り返しの対話に依存する以前のアプローチとは異なり、このフレームワークはLLMの使用を展開前のファズドライバー生成段階に厳密に限定
- 生成されたファズドライバーは、さらにLLMを関与させることなく再利用可能

### 11.3 基礎的アプローチ

研究では、サンプル入力とニューラルネットワークベースの統計的機械学習技術を使用して、入力Fuzzingに適した入力文法の生成を自動化する方法が示されている ([IEEE - Learn&Fuzz](https://ieeexplore.ieee.org/document/8115618/), [ResearchGate - Learn&Fuzz](https://www.researchgate.net/publication/312908535_LearnFuzz_Machine_Learning_for_Input_Fuzzing))。

### 11.4 将来の方向性

この分野は、複雑なソフトウェアシステムにおけるより効果的な脆弱性検出のために、AIと形式手法を組み合わせたハイブリッドアプローチに向けて積極的に進化している ([Microsoft Research - Neural Fuzzing](https://www.microsoft.com/en-us/research/blog/neural-fuzzing/))。

## 12. Fuzzingと仕様の関係

### 12.1 オラクル問題

自動化されたソフトウェアテストにおいて、テストオラクル問題は、バグと機能を区別することの困難さを指す ([YLD - Oracle Problem](https://www.yld.com/blog/the-oracle-problem), [Medium - Oracle Problem](https://medium.com/yld-engineering-blog/the-oracle-problem-cc02b42a1f44))。

「オラクル問題」に対処するテスト技術には、広く定義されたファズテストが含まれ、変異Fuzzing、生成テスト、プロパティベーステスト、モデルベーステスト、変異テストが含まれる。

### 12.2 Fuzzingとプロパティベーステストの関係

FuzzingとプロパティテストはMany commonalities があるが、テストの駆動方法が異なる傾向がある ([Ted's Blog - Fuzzing vs Property Testing](https://www.tedinski.com/2018/12/11/fuzzing-and-property-testing.html))。

**プロパティベーステスト**:
- テスト対象のシステムに関する深い理解が必要
- プログラマーはテストするプロパティを指定し、「興味深い」入力の大まかな「形状」を記述
- ユニットテストのように素早く実行できる

**Fuzzing**:
- どの入力がコード内のどのブランチがヒットされるかを追跡し、できるだけ多くのブランチをカバーするように入力を調整
- 時間がかかる可能性があるプロセスだが、長期間ファザーを実行すると報われることが多い

### 12.3 仕様ベースのオラクル

仕様ベースのオラクルは、命令の意味論と安全性プロパティを仕様としてエンコードし、対応する安全性制約の充足可能性を自動的にチェックすることでバグを検出するためにファザーと統合されている ([ACM - eBPF Misbehavior](https://dl.acm.org/doi/10.1145/3731569.3764797), [EPFL - eBPF Fuzzing](https://infoscience.epfl.ch/entities/publication/84348103-d63a-43fd-ad8c-0803e299aa18))。

プログラムの仕様が利用可能な場合、ホワイトボックスファザーは、モデルベーステストからの技術を活用して入力を生成し、プログラム仕様に対してプログラム出力をチェックする可能性がある。

### 12.4 適合性テスト

文法ベースFuzzingを使用した形式的意味論の適合性テストも研究されている ([Springer - Conformance Testing](https://link.springer.com/chapter/10.1007/978-3-031-09827-7_7))。

### 12.5 プロパティベースFuzzingの統合

プロパティベースFuzzingは、Fuzzingとプロパティベーステストの橋渡しを試みる ([Yosh's Blog - Bridging](https://blog.yoshuawuyts.com/bridging-fuzzing-and-property-testing/), [PLUM UMD - Randomized Testing](https://plum-umd.github.io/projects/random-testing.html))。

**PBFDroid**:

Androidアプリのデータ操作エラーを見つけるためのプロパティベースFuzzing手法 ([FSE - PBFDroid](https://tingsu.github.io/files/fse23-PBFDroid.pdf))。

## 13. Fuzzingの限界と保証

### 13.1 オラクル問題の再考

従来のソフトウェアテストでは、明確に定義されたオラクルが与えられた入力に対して出力が正しいかどうかを示す。サイバーセキュリティのFuzzingは、バグオラクルの使用に依存しており、これは与えられた実行が特定のセキュリティポリシーに違反するかどうかを判断するプログラムである ([Fuzzing Book - Coverage](https://www.fuzzingbook.org/html/Coverage.html))。

### 13.2 Fuzzingの基本的限界

ファザーは、その入力から生じるすべてのバグを検出することを意図していないし、コードに潜んでいる可能性のあるすべてのバグを検出するように設計されていない ([IEEE Software - Fuzzing Challenges](https://abhikrc.com/pdf/IEEE-SW-Fuzzing.pdf))。

**重要な区別**:
- Fuzzingはプログラムが正しくないことを証明するのに役立つが、プログラムが正しいことを証明することはできない

### 13.3 カバレッジの限界

コードカバレッジを達成しても、プログラムがエラーフリーであることを意味しない。結果がチェックされないため、関数はチェックや気づきなしに任意の値を返すことができる。このようなエラーをキャッチするには、結果チェッカー（一般にオラクルと呼ばれる）がテスト結果を検証する必要がある。

### 13.4 形式的保証の可能性

ホワイトボックスファザーは、検出可能な脆弱性の不在について形式的保証を提供する可能性がある。記号実行エンジンがコード内のすべてのパスを列挙でき、オラクルがアサーションとしてエンコードされている場合、ホワイトボックスFuzzingはバグの不在を形式的に検証できる。合理的な時間内に一部のパスのみを列挙できる場合でも、部分的保証を提供できる ([Trust-in-Soft - Beyond Fuzzing](https://trust-in-soft.com/optimizing-fuzzing-to-eliminate-more-vulnerabilities))。

### 13.5 健全性テストの課題

健全性テストの場合、無効だが受け入れられたウィットネスを生成することは大幅に困難である：有効な入力をランダムに変異させると、検証器によって完全に拒否される証明が生成されることが多く、変異されたウィットネスが正しくないが依然として受け入れられるかどうかを判断するには高度なオラクルが必要であり、小さなローカル変異が回路の他の部分を無効にする可能性がある ([arXiv - Fuzzing ZK Circuits](https://arxiv.org/html/2504.14881))。

### 13.6 保証の程度

Fuzzingが提供する保証の程度は、使用されるアプローチに依存する：

| アプローチ | 保証のレベル | 制限 |
|-----------|--------------|------|
| ブラックボックス | 経験的のみ | パス列挙なし |
| グレーボックス | カバレッジベースの経験的 | 完全性の保証なし |
| ホワイトボックス | 潜在的に形式的 | パス爆発、スケーラビリティ |

## 14. 結論

Fuzzingは、1988年の偶然の発見以来、ソフトウェアセキュリティとテストの基礎技術に成長した。ランダムテストから洗練されたカバレッジガイドおよびハイブリッドアプローチへの進化は、自動バグ検出における継続的な革新を反映している。

### 主要な洞察

1. **多様なアプローチ**: ブラックボックス、ホワイトボックス、グレーボックスFuzzingは、速度、精度、保証の異なるトレードオフを提供
2. **実用的有効性**: OSS-Fuzzを通じて、数万のバグと脆弱性が現実世界のソフトウェアで発見された
3. **継続的革新**: 機械学習、LLM、ニューロシンボリック手法が次世代Fuzzingを推進
4. **保証の限界**: Fuzzingはプログラムの正しさの経験的証拠を提供するが、形式的証明を置き換えるものではない

### 仕様検証との関係

Fuzzingと仕様は相補的な関係にある：

- **仕様はオラクルを定義**: 明確な仕様により、Fuzzingツールは単なるクラッシュ以上のものを検出できる
- **Fuzzingは仕様の穴を発見**: 実行ベースのテストは、形式仕様では見逃される可能性のあるエッジケースを明らかにする
- **ハイブリッドアプローチ**: 仕様ベースのオラクルとカバレッジガイドFuzzingの組み合わせが最も強力

### Fuzzingの位置付け

仕様記述と検証のエコシステムにおいて、Fuzzingは以下の役割を果たす：

- **補完的検証**: 形式手法が網羅的保証を提供する一方、Fuzzingは実用的な経験的検証を提供
- **早期バグ検出**: 開発サイクルの早い段階で低コストで問題を発見
- **継続的保証**: CI/CDパイプラインに統合され、継続的なセキュリティ検証を提供

Fuzzingは、完璧な保証を提供しないが、現実世界のソフトウェアの品質とセキュリティを向上させるための実用的で効果的かつスケーラブルなアプローチである。仕様記述、形式検証、その他のテスト技術と組み合わせることで、より堅牢で安全なソフトウェアシステムの構築に貢献する。

## 参考文献

### 歴史と基礎
- [Trail of Bits - Fuzzing Like It's 1989](https://blog.trailofbits.com/2018/12/31/fuzzing-like-its-1989/)
- [ResearchGate - Fuzz Revisited](https://www.researchgate.net/publication/239668581_Fuzz_Revisited_A_Re-Examination_of_the_Reliability_of_UNIX_Utilities_and_Services)
- [Wikipedia - Fuzzing](https://en.wikipedia.org/wiki/Fuzzing)
- [Wisconsin CS - Trials and Tribulations](https://www.cs.wisc.edu/2021/01/14/the-trials-and-tribulations-of-academic-publishing-and-fuzz-testing/)
- [CISPA - Random Testing with Fuzz](https://cispa.de/dls-miller)

### カバレッジガイドFuzzing
- [GitHub - AFL](https://github.com/google/AFL)
- [ACM TOSEM - Dissecting AFL](https://dl.acm.org/doi/full/10.1145/3580596)
- [ResearchGate - Dissecting AFL](https://www.researchgate.net/publication/367297404_Dissecting_American_Fuzzy_Lop_-_A_FuzzBench_Evaluation)
- [GitHub - AFL++](https://github.com/AFLplusplus/AFLplusplus)
- [Wikipedia - AFL](https://en.wikipedia.org/wiki/American_fuzzy_lop_(fuzzer))
- [ClusterFuzz - Coverage Guided](https://google.github.io/clusterfuzz/reference/coverage-guided-vs-blackbox/)

### Fuzzingアプローチの比較
- [Fuzzing Book - Greybox Fuzzer](https://www.fuzzingbook.org/html/GreyboxFuzzer.html)
- [ResearchGate - Common Fuzzers Table](https://www.researchgate.net/figure/Common-white-box-gray-box-and-black-box-fuzzers_tbl3_325577316)
- [Smart Greybox Fuzzing - PDF](https://mboehme.github.io/paper/TSE19.pdf)
- [MPG - Greybox Fuzzing](https://www.mpg.de/20666079/software-security-gap-fuzzing)
- [IEEE Software - Fuzzing Challenges](https://mboehme.github.io/paper/IEEESoftware20.pdf)

### 文法ベースと構造認識Fuzzing
- [GitHub - Google Fuzzing](https://github.com/google/fuzzing/blob/master/docs/structure-aware-fuzzing.md)
- [Fuzzing Book - Efficient Grammar Fuzzing](https://www.fuzzingbook.org/html/GrammarFuzzer.html)
- [ISSTA - Gramatron](https://hexhive.epfl.ch/publications/files/21ISSTA.pdf)
- [arXiv - Superion](https://arxiv.org/pdf/1812.01197)
- [GitHub - Awesome Grammar Fuzzing](https://github.com/Microsvuln/Awesome-Grammar-Fuzzing)
- [Fuzzing Book - Grammars](https://www.fuzzingbook.org/html/Grammars.html)
- [ResearchGate - Gramatron](https://www.researchgate.net/publication/353168541_Gramatron_effective_grammar-aware_fuzzing)

### 変異戦略とシード選択
- [arXiv - AlphaFuzz](https://arxiv.org/abs/2101.00612)
- [ResearchGate - AlphaFuzz](https://www.researchgate.net/publication/348212826_AlphaFuzz_Evolutionary_Mutation-based_Fuzzing_as_Monte_Carlo_Tree_Search)
- [ScienceDirect - Adaptive Mutation](https://www.sciencedirect.com/science/article/abs/pii/S002002552500091X)
- [ISSTA - Seed Selection](https://hexhive.epfl.ch/publications/files/21ISSTA2.pdf)
- [Korea U - SeamFuzz](https://prl.korea.ac.kr/papers/icse23-seamfuzz.pdf)
- [IEEE - Learning Seed-Adaptive](https://ieeexplore.ieee.org/document/10172576/)
- [Fuzzing Book - Mutation Fuzzer](https://www.fuzzingbook.org/html/MutationFuzzer.html)

### ハイブリッドFuzzing
- [NDSS - Driller](https://www.ndss-symposium.org/wp-content/uploads/2017/09/driller-augmenting-fuzzing-through-selective-symbolic-execution.pdf)
- [USENIX - QSYM](https://www.usenix.org/conference/usenixsecurity18/presentation/yun)
- [ACM - QSYM](https://dl.acm.org/doi/10.5555/3277203.3277260)
- [Semantic Scholar - QSYM](https://www.semanticscholar.org/paper/QSYM-:-A-Practical-Concolic-Execution-Engine-for-Yun-Lee/79b4d4fb6800d89f1f649dfd49b7b28727e10dde)
- [GitHub - QSYM](https://github.com/sslab-gatech/qsym)
- [ACM - Survey on Hybrid Fuzzing](https://dl.acm.org/doi/10.1145/3444370.3444570)
- [IEEE - Tightly-Coupled Hybrid](https://www.computer.org/csdl/journal/tq/2024/05/10418578/1Ublds1CRt6)
- [Semantic Scholar - Driller](https://www.semanticscholar.org/paper/Driller:-Augmenting-Fuzzing-Through-Selective-Stephens-Grosen/f049751103f13d1ce6080418813e2a26820713e1)

### サニタイザ
- [GitHub - Google Sanitizers](https://github.com/google/sanitizers)
- [Wikipedia - Code Sanitizer](https://en.wikipedia.org/wiki/Code_sanitizer)
- [Rust Unstable Book - Sanitizer](https://doc.rust-lang.org/beta/unstable-book/compiler-flags/sanitizer.html)
- [Medium - Beyond Sanitizers](https://medium.com/mit-security-seminar/beyond-sanitizers-guided-fuzzing-and-security-hardening-9cc8155e19fb)
- [Fuzzing Project - Tutorial 2](https://fuzzing-project.org/tutorial2.html)
- [arXiv - Sand](https://arxiv.org/html/2402.16497v1)
- [Testing Handbook - ASan](https://appsec.guide/docs/fuzzing/techniques/asan/)

### 継続的Fuzzingインフラ
- [GitHub - OSS-Fuzz](https://github.com/google/oss-fuzz)
- [Google OSS-Fuzz Docs](https://google.github.io/oss-fuzz/)
- [Google Open Source Blog - OSS-Fuzz](https://opensource.googleblog.com/2016/12/announcing-oss-fuzz-continuous-fuzzing.html)
- [GitHub - ClusterFuzz](https://github.com/google/clusterfuzz)
- [OSS-Fuzz ClusterFuzz](https://google.github.io/oss-fuzz/further-reading/clusterfuzz/)
- [Code Intelligence - OSS-Fuzz](https://www.code-intelligence.com/blog/intro-to-oss-fuzz)

### カーネルFuzzing
- [GitHub - syzkaller](https://github.com/google/syzkaller)
- [Cloudflare - Linux Kernel Fuzzing](https://blog.cloudflare.com/a-gentle-introduction-to-linux-kernel-fuzzing/)
- [GitHub - syzkaller Network](https://github.com/google/syzkaller/blob/master/docs/linux/external_fuzzing_network.md)
- [LWN - Coverage-Guided Kernel Fuzzing](https://lwn.net/Articles/677764/)
- [Collabora - Using syzkaller](https://www.collabora.com/news-and-blog/blog/2020/03/26/syzkaller-fuzzing-the-kernel/)
- [Xairy - RCE Bugs](https://xairy.io/articles/syzkaller-external-network)

### 機械学習とニューラルFuzzing
- [ScienceDirect - Survey on DNN Fuzzing](https://www.sciencedirect.com/science/article/pii/S0950584925001363)
- [ACM FSE - Neural Program Smoothing](https://dl.acm.org/doi/10.1145/3611643.3616308)
- [PLOS One - ML Fuzzing Review](https://journals.plos.org/plosone/article?id=10.1371/journal.pone.0237749)
- [Springer - FD-FACTORY](https://link.springer.com/article/10.1186/s42400-025-00532-9)
- [IEEE - Learn&Fuzz](https://ieeexplore.ieee.org/document/8115618/)
- [Microsoft Research - Neural Fuzzing](https://www.microsoft.com/en-us/research/blog/neural-fuzzing/)
- [ResearchGate - Learn&Fuzz](https://www.researchgate.net/publication/312908535_LearnFuzz_Machine_Learning_for_Input_Fuzzing)

### Fuzzingと仕様
- [YLD - Oracle Problem](https://www.yld.com/blog/the-oracle-problem)
- [Ted's Blog - Fuzzing vs Property Testing](https://www.tedinski.com/2018/12/11/fuzzing-and-property-testing.html)
- [Medium - Oracle Problem](https://medium.com/yld-engineering-blog/the-oracle-problem-cc02b42a1f44)
- [FSE - PBFDroid](https://tingsu.github.io/files/fse23-PBFDroid.pdf)
- [ACM - eBPF Misbehavior](https://dl.acm.org/doi/10.1145/3731569.3764797)
- [EPFL - eBPF Fuzzing](https://infoscience.epfl.ch/entities/publication/84348103-d63a-43fd-ad8c-0803e299aa18)
- [Springer - Conformance Testing](https://link.springer.com/chapter/10.1007/978-3-031-09827-7_7)
- [Yosh's Blog - Bridging](https://blog.yoshuawuyts.com/bridging-fuzzing-and-property-testing/)
- [PLUM UMD - Randomized Testing](https://plum-umd.github.io/projects/random-testing.html)

### Fuzzingの限界
- [Fuzzing Book - Coverage](https://www.fuzzingbook.org/html/Coverage.html)
- [IEEE Software - Fuzzing Challenges](https://abhikrc.com/pdf/IEEE-SW-Fuzzing.pdf)
- [Trust-in-Soft - Beyond Fuzzing](https://trust-in-soft.com/optimizing-fuzzing-to-eliminate-more-vulnerabilities)
- [arXiv - Fuzzing ZK Circuits](https://arxiv.org/html/2504.14881)
