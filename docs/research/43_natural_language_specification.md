# 自然言語仕様と構造化仕様

## 概要

ソフトウェア要求仕様の圧倒的多数は自然言語で記述されている。自然言語は普遍的で柔軟性があり広く普及しているが、不幸にも本質的に曖昧である。本調査では、自然言語による仕様記述の利点と問題点、曖昧性を軽減するための構造化アプローチ、制限自然言語（CNL）、要求仕様テンプレート、標準規格、そしてNLPによる自動解析について検討する。

## 自然言語仕様の利点と問題点

### なぜ自然言語が使われるのか

[要求仕様の圧倒的多数は自然言語で記述されている](https://cs.uwaterloo.ca/~dberry/natural.language.html)。これは、数式や図表などの他の表記法で補完されることがあるとしても変わらない事実である。

**利点**:
- **普遍性**: すべてのステークホルダーが理解できる
- **柔軟性**: 複雑な概念を表現できる
- **アクセシビリティ**: 特別なトレーニングを必要としない
- **コミュニケーション**: ドメイン専門家、開発者、ユーザー間の共通言語

### 自然言語の根本的な問題：曖昧性

[自然言語は本質的に曖昧](https://link.springer.com/chapter/10.1007/978-3-642-14192-8_21)である。自然言語は「意味を曖昧なまま表現するツール」であり、「一つの文に対して複数の解釈ができる」という特性を持っている。

**曖昧性の影響**:
[曖昧な要求はしばしばプロジェクト失敗の原因](https://dl.acm.org/doi/10.1145/2815021.2815032)と見なされる。曖昧性が問題なのは、要求仕様の異なる読者が異なることを理解する可能性があるためである。実装者の理解が顧客やユーザーの理解と異なる場合、顧客とユーザーは実装に満足しない可能性が高い。

### 曖昧性の種類

[研究では2つのカテゴリの曖昧性](https://link.springer.com/chapter/10.1007/978-3-642-14192-8_21)を区別している：

**言語学的曖昧性**:
自然言語の一般的に知られた曖昧性。例えば：
- 代名詞参照の曖昧性
- 語彙的曖昧性（同じ単語の複数の意味）
- 構文的曖昧性（文の構造の複数の解釈）
- 意味的曖昧性

**RE固有の曖昧性**:
要求工学（RE）のコンテキストから生じる曖昧性。アプリケーション、システム、開発ドメインを含む。

### 日本における実態

[JUAS（情報システムユーザー協会）の調査](https://www.veriserve.co.jp/asset/approach/column/test-technique/software-test03.html)によると、プロジェクトの工期遅延の理由のうち55%が要件定義の問題であると言われている。

**具体的な問題**:
[ソフトウェア工学的曖昧さ](https://www.veriserve.co.jp/asset/approach/column/test-technique/software-test03.html)は、読み手の適用分野知識の有無により複数の解釈が生まれるものである。例えば、「水位が100メーターを上回る」という記述でも、平均水位なのか中央値なのか、または二乗平方根水位なのかで解釈が異なる場合がある。

組織間に要求の認識齟齬が発生し、受入試験までその齟齬に気づかず問題発覚が遅延するなどの問題が生まれる。

### 曖昧性への対処

[自然言語には曖昧さに気づくための言語学的な技術に限界](https://playgram.jp/oshiete-pfn/robot-3-nlp/)があり、曖昧さを完全に排除することは困難である。しかし、自然言語の特徴を理解し、適切な対応をすることにより、曖昧さを減らす・曖昧さによる影響を下げることは十分可能である。

## 制限自然言語（Controlled Natural Language）

### CNLの概念

[制限自然言語（CNL）](https://link.springer.com/article/10.1007/s10664-021-09956-6)は、要求文書の品質問題を防ぐ方法として提案されている。CNLは、要求を直感的かつ普遍的に理解される方法で記述・伝達する柔軟性を維持しながら、問題を防ぐ。

CNLは標準的な自然言語のサブセットであり、ドメイン固有の語彙と制限された文法を持つ。

### Attempto Controlled English (ACE)

[ACE（Attempto Controlled English）](https://en.wikipedia.org/wiki/Attempto_Controlled_English)は、最もよく研究されたCNLの一つである。

**主要な特徴**:
- ドメイン専門家が対話的に要求仕様をドメイン概念で定式化できる
- コンピュータによって正確かつ効率的に処理できる
- 自然な使用を許可するのに十分な表現力がある

**言語機能**:
ACEは以下をサポートする：
- 複雑な名詞句
- 複数形
- 照応参照
- 従属節
- モダリティ
- 質問

ACEテキストは、照応的に相互関連できる宣言文のシーケンスである。さらに、ACEは質問とコマンドをサポートする。

**形式化への変換**:
[Attempto Parsing Engine（APE）](https://www.researchgate.net/publication/220483487_Attempto_Controlled_English_ACE)は、ACEテキストを曖昧さなく、一階述語論理の言語の変種を使用する談話表現構造（DRS）に変換する。DRSは、AceRules（様々な意味論を持つ）、OWL、SWRLなどの他の形式言語にさらに変換できる。

ACEテキストを（一階述語論理の断片に）変換することで、ユーザーはテキストについて推論できる。例えば、検証、妥当性確認、問い合わせが可能になる。

**曖昧性の解決**:
いくつかの曖昧な構文は言語の一部ではなく、その代わりに曖昧でない代替案が利用可能である。残りのすべての曖昧な構文は、少数の解釈規則に基づいて決定論的に解釈される。

## 構造化自然言語仕様

### 基本的なアプローチ

構造化自然言語仕様は、完全な形式言語への移行なしに自然言語の利点を保持しながら、曖昧性を減らすことを目指す。

### USDM（統合仕様記述方法論）

[USDM](https://www.eureka-box.com/media/column/a19)は日本で開発された要求仕様記述技法である。

**主要な特徴**:
- 統一された記述マナーのテンプレートを持つ
- Excelで作成でき、個々の要求仕様がセルで区切られている
- IDも付与できるため、レビューでの指摘やメンテナンスがしやすい
- 自然言語で記載するため自由度が高い

**構造化の原則**:
[USDMでは複合的な要求を単純な要求に分割](https://sqripts.com/2024/02/06/90314/)し、曖昧な要求を具体化し、要求を階層化することで、認識のブレを防止している。

### 要求の階層化

要求仕様書の基本構成には以下が含まれる：
- プロジェクト概要（目的、背景、期待される成果）
- 機能要件（具体的な機能の詳細）
- 非機能要件（パフォーマンス、セキュリティ、ユーザビリティ）
- 制約条件（技術的・法的・予算制約）

## 要求仕様テンプレート

### Volere要求仕様テンプレート

[Volere要求仕様テンプレート](https://www.volere.org/templates/volere-requirements-specification-template/)は、Suzanne RobertsonとJames Robertsonによる書籍「Mastering the Requirements Process」で説明されている技法である。

**背景**:
Volereは、要求工学における長年の実践、コンサルティング、研究の結果であり、一般的な要求プロセス、要求トレーニング、要求コンサルタンシー、要求監査、様々なダウンロード可能なガイド、要求テンプレートの形式でパッケージ化されている。

**要求シェル**:
[要求シェル](https://www.reqview.com/doc/volere-template/)は、各原子的な機能的および非機能的要求を記述するためのガイドである。シェルの構成要素（「スノーカード」とも呼ばれる）が識別される。シェルは自動化可能であり、自動化すべきである。

**テンプレートの目的**:
テンプレートは以下を提供する：
- 要求仕様の基礎として使用することを意図
- 今日のビジネス、科学、ソフトウェアシステムに適切な各要求タイプを提供
- 要求のチェックリスト、構造、トレーサビリティを提供

テンプレートはツール独立であり、Yonix、Requisite、DOORS、Caliber RM、IRqAなどの人気のあるツールで成功裏に使用されている。

Volereテンプレートは[Atlantic Systems Guildによって維持](https://www.volere.org/)されており、ソフトウェア工学業界で最も広く使用されている要求仕様テンプレートの1つである。

## IEEE 830とISO/IEC/IEEE 29148

### IEEE 830の遺産

[IEEE 830-1998](https://en.wikipedia.org/wiki/Software_requirements_specification)は、ソフトウェア要求仕様のためのよく知られた標準であった。後にISO/IEC/IEEE 29148に置き換えられた。

### ISO/IEC/IEEE 29148

[ISO/IEC/IEEE 29148標準](https://standards.ieee.org/ieee/29148/5289/)は2011年にIEEE 830に取って代わり、現在の改訂版は2018年からのものである。

**範囲と目的**:
ISO/IEC/IEEE 29148は、システムおよびソフトウェア工学の文脈において、特性と属性を含む、適切に形成されたテキスト要求の構成の詳細を提供する。

ISO/IEC/IEEE 29148:2011は、ライフサイクル全体を通じてシステムおよびソフトウェア製品とサービスの要求の工学に関連するプロセスと成果物の規定を含む。

**IEEE 830からの拡張**:
[ISO/IEC/IEEE 29148はIEEE 830よりも広範](https://www.researchgate.net/figure/Feature-comparison-between-IEEE-830-y-ISO-IEC-IEEE-29148_tbl2_330681432)であり、要求品質基準、要求管理プロセス、ビジネス要求仕様（BRS）、およびステークホルダー要求仕様（StRS）をカバーしている。

### 自然言語の品質問題

[要求の品質に関連する多くの問題](https://www.cin.ufpe.br/~if716/arquivos20192/03-%20IEEE-830&IEEE-29184)は、自然言語で記述されるため、引き出しと仕様化活動中に発生する。言語の柔軟性と本質的な性質により、要求は不整合、冗長性、曖昧性を起こしやすい。

**バッドスメル**:
ISO/IEC/IEEE 29148は以下を含むバッドスメルのセットを定義している：
- 主観的言語
- 曖昧な副詞と形容詞
- 抜け穴
- オープンエンド
- 検証不可能な用語
- 最上級
- 比較句
- 否定文
- 曖昧な代名詞
- 不完全な参照

## EARS（Easy Approach to Requirements Syntax）

### 概要

[EARS（Easy Approach to Requirements Syntax）](https://medium.com/paramtech/ears-the-easy-approach-to-requirements-syntax-b09597aae31d)は、テキスト要求を緩やかに制約するメカニズムであり、EARSパターンは、著者が高品質のテキスト要求を書くことを可能にする構造化ガイダンスを提供する。

### 歴史的背景

EARSは[2009年にRolls-Royce Aero Engines](https://alistairmavin.com/ears/)で最初に開発された。分野横断的なエンジニアのグループが、航空機エンジン制御システムの要求を決定するために耐空性規則を分析した。

### 5つの要求タイプ

[ルールセットにより、すべての自然言語要求を5つの簡単なテンプレートの1つで表現](https://ieeexplore.ieee.org/document/5328509/)できる：

**1. Ubiquitous（ユビキタス）**:
常にアクティブな要求で、EARSキーワードなし。

例：「携帯電話の質量はXXグラム未満でなければならない」

**2. State-Driven（状態駆動）**:
指定された状態が真である限りアクティブで、キーワード「While」で示される。

例：「ATMにカードが挿入されていない間、ATMは『開始するにはカードを挿入してください』と表示しなければならない」

**3. Event-Driven（イベント駆動）**:
トリガーイベントが発生したときにシステムがどのように応答しなければならないかを指定し、キーワード「When」で示される。

例：「『ミュート』が選択されたとき、ラップトップはすべてのオーディオ出力を抑制しなければならない」

**4. Optional Feature（オプション機能）**:
指定された機能を含む製品またはシステムに適用され、キーワード「Where」で示される。

例：「車がサンルーフを持つ場合、車は運転席ドアにサンルーフ制御パネルを持たなければならない」

**5. Unwanted Behavior（望ましくない動作）**:
望ましくない状況に対する必要なシステム応答を指定するために使用され、キーワード「If」と「Then」で示される。

例：「無効なクレジットカード番号が入力された場合、Webサイトは『クレジットカードの詳細を再入力してください』と表示しなければならない」

### 利点

[EARSはいくつかのキーワードと単純な基礎ルールセット](https://qracorp.com/guides_checklists/the-easy-approach-to-requirements-syntax-ears/)を使用して自然言語要求を緩やかに制約し、時相論理に従って常に同じ順序である句により、要求は明確さと精度を最適化しながら英語の一般的な使用法を反映する。

### 制限事項

[EARSはすべての要求タイプに適しているわけではない](https://qracorp.com/when-not-to-use-ears/)。以下の場合は使用を避けるべき：
- データ定義
- 物理的制約
- インターフェース仕様
- 複雑な計算式

## NLPによる要求仕様解析

### NLP4REの概要

[NLP4RE（Natural Language Processing for Requirements Engineering）](https://arxiv.org/pdf/2004.01099)は、NLP技法、ツール、リソースを要求工学プロセスに適用し、テキスト要求文書の分析タスクをサポートする。言語問題の検出、主要ドメイン概念の特定、要求トレーサビリティリンクの確立などを行う。

### 目的と利点

[NLP要求分析ツール](https://qracorp.com/leveraging-natural-language-processing-in-requirements-analysis/)は、個々の要求の仕様に使用される言語を分析し、分析された各要求の品質評価をユーザーに提供する。これらのツールは、退屈で、時間がかかり、疲労しやすく、エラーが発生しやすいタスクをほぼ瞬時に自動化し、ドメイン知識を必要としないタスクからドメイン専門家を解放する。

### 主要な自動化ツール

**QuARS（Quality Analyzer for Requirements Specifications）**:
[QuARS](https://ceur-ws.org/Vol-2376/NLP4RE19_paper07.pdf)は、自然言語処理技法を用いて自然言語要求の自動分析を実行できるツールである。曖昧性検出に焦点を当て、要求エンジニアが潜在的な言語的欠陥を自動的に検出するための早期分析を実行できるようにする。

**NLP技法**:
NLP技法には、POSタグ付け、解析、トークン化などの実用的な方法が含まれる。一方、NLPツールは、Stanford CoreNLPやNLTKなど、1つ以上のNLP技法をサポートするソフトウェアシステムまたはライブラリである。

### 主要な応用

言語分析タスクには、言語問題の検出、主要ドメイン概念の特定、要求間のトレーサビリティリンクの確立が含まれる。

[NLPベースの要求検証ワークフロー](https://www.ijcaonline.org/archives/volume187/number53/baranetska-2025-ijca-925909.pdf)は、要求の文書化から始まり、NLP処理を経て、自動テストケース生成で最高潮に達する継続的サイクルに従い、手作業の削減、曖昧性の最小化、品質保証プロセスの精度と効率の向上を実現する。

### 現在の課題

[NLP4RE研究における技術の最先端と実践の最先端の間には大きな乖離](https://dl.acm.org/doi/10.1145/3444689)がある。これは以下によって示される：
- 不十分な産業検証
- 提案されたツールの産業採用の証拠が少ない
- 共有RE固有の言語リソースの欠如
- NLP4RE研究におけるNLP専門知識の欠如

## 実践的な課題と解決策

### 曖昧性の完全排除は不可能

自然言語には曖昧さに気づくための言語学的な技術に限界があり、曖昧さを完全に排除することは困難である。しかし、自然言語の特徴を理解し、適切な対応をすることにより、曖昧さを減らす・曖昧さによる影響を下げることは十分可能である。

### 複数アプローチの組み合わせ

実践的には、以下の組み合わせが効果的：

1. **制限自然言語（CNL）**: 語彙と文法を制限
2. **構造化テンプレート**: EARSやVolereのようなパターンを使用
3. **自動解析ツール**: NLPツールによる曖昧性検出
4. **手動レビュー**: ドメイン専門家による検証
5. **形式的補完**: 重要な部分に形式手法を適用

### 段階的な厳密化

すべての要求を最初から厳密に形式化する必要はない：

- **初期段階**: 自然言語での記述
- **構造化**: テンプレートを使用した整理
- **検証**: NLPツールによる分析
- **重要部分の形式化**: クリティカルな要求のみ形式手法を適用

## 考察

### 自然言語の必然性

自然言語による仕様記述が圧倒的多数を占めるのは、以下の理由から必然である：

**コミュニケーションの必要性**:
要求仕様は、ドメイン専門家、開発者、テスター、ユーザー、経営層など、多様なバックグラウンドを持つステークホルダー間のコミュニケーションツールである。すべてが理解できる共通言語として自然言語は不可欠である。

**形式手法の限界**:
完全な形式手法は以下の問題を抱える：
- 習得に時間がかかる
- ツールサポートが限定的
- ドメイン専門家が理解できない
- すべての要求を表現できるわけではない

### 曖昧性との共存

曖昧性を完全に排除することは不可能であり、必要でもない：

**必要な曖昧性**:
初期段階の要求では、ある程度の曖昧性が許容され、むしろ有用である。詳細を早期に固定しすぎると、柔軟性が失われる。

**段階的な明確化**:
要求工学プロセス全体を通じて、段階的に曖昧性を減らしていくアプローチが現実的である。

### 構造化アプローチの有効性

EARSのような構造化アプローチは、以下の利点を持つ：

**学習容易性**:
5つの単純なパターンは、エンジニアが容易に習得できる。形式手法と比較して、トレーニングコストが低い。

**自然さの保持**:
EARSは自然言語の範囲内で動作するため、ステークホルダーが理解しやすい。

**ツールサポート**:
単純なパターンは、自動化ツールでのサポートが容易である。

### CNLの実用性

Attempto ACEのようなCNLは理論的には魅力的だが、実用上の課題がある：

**採用の障壁**:
- 新しい言語を学ぶ必要がある
- 既存の文書との統合が困難
- ツールサポートが限定的

**適用範囲**:
CNLは、形式化が必要な重要な要求に対して有用だが、すべての要求に適用するのは非現実的である。

### NLPの可能性と限界

NLPツールは曖昧性検出を自動化できるが、以下の限界がある：

**技術的限界**:
自然言語理解は依然として困難な問題である。文脈依存の曖昧性、ドメイン固有の知識、暗黙の前提の理解は、現在のNLP技術では不完全である。

**産業採用のギャップ**:
研究と実践の間に大きなギャップがある。多くのNLP4REツールは学術的な成果であり、産業での検証と採用が不十分である。

### 標準規格の役割

IEEE 830/ISO 29148のような標準規格は、以下を提供する：

**共通の枠組み**:
組織間での要求仕様の構造と内容についての共通理解。

**品質基準**:
バッドスメルのカタログなど、品質評価のための具体的な基準。

**しかし、銀の弾丸ではない**:
標準規格に従うだけでは、高品質の要求は保証されない。適切な理解、トレーニング、実践が必要である。

### 実践的な推奨事項

以下のバランスの取れたアプローチが推奨される：

1. **基本は自然言語**: すべてのステークホルダーが理解できる
2. **構造化を追加**: EARSやVolereのようなテンプレートを使用
3. **自動検証**: NLPツールで曖昧性を検出
4. **重要部分の形式化**: クリティカルな要求にはCNLや形式手法を適用
5. **継続的改善**: レビュー、テスト、フィードバックを通じて要求を洗練

## 結論

自然言語による仕様記述は、その曖昧性にもかかわらず、要求工学において支配的であり続ける。これは欠陥ではなく、多様なステークホルダー間のコミュニケーションツールとしての要求仕様の本質的な性質を反映している。

重要なのは、曖昧性を完全に排除しようとするのではなく、適切に管理することである：

**段階的アプローチ**:
- 初期：自然言語での自由な記述
- 中期：構造化テンプレート（EARS、Volere）の適用
- 後期：重要部分の形式化（CNL、形式手法）

**ツールの活用**:
- NLPツールによる自動曖昧性検出
- 標準規格（ISO 29148）に基づく品質チェック
- レビューとテストによる検証

**現実的な期待**:
完璧な要求仕様は存在しない。曖昧性との共存、段階的な改善、複数の検証手法の組み合わせが、実用的なアプローチである。

自然言語仕様は、形式手法の対極ではなく、仕様の厳密さのスペクトラムにおける一つの位置である。適切な構造化、ツールサポート、プロセスと組み合わせることで、自然言語は効果的な要求仕様の基礎となり得る。

## 参考文献

### 自然言語仕様の問題点
- [Ambiguity in Natural Language Software Requirements: A Case Study | Springer](https://link.springer.com/chapter/10.1007/978-3-642-14192-8_21)
- [Resolving Ambiguities in Natural Language Software Requirements: A Comprehensive Survey | ACM](https://dl.acm.org/doi/10.1145/2815021.2815032)
- [Ambiguity in Natural Language Requirements Specifications](https://cs.uwaterloo.ca/~dberry/ambiguity.res.html)
- [Natural Language in Requirements Engineering](https://cs.uwaterloo.ca/~dberry/natural.language.html)

### 制限自然言語（CNL）
- [Attempto Controlled English - Wikipedia](https://en.wikipedia.org/wiki/Attempto_Controlled_English)
- [Attempto Controlled English (ACE) | ResearchGate](https://www.researchgate.net/publication/220483487_Attempto_Controlled_English_ACE)
- [On systematically building a controlled natural language for functional requirements | Springer](https://link.springer.com/article/10.1007/s10664-021-09956-6)

### IEEE 830とISO 29148
- [ISO/IEC/IEEE 29148:2018](https://standards.ieee.org/ieee/29148/5289/)
- [Software requirements specification - Wikipedia](https://en.wikipedia.org/wiki/Software_requirements_specification)
- [ISO/IEC/IEEE 29148 Requirements Specification Templates | ReqView](https://www.reqview.com/doc/iso-iec-ieee-29148-templates/)

### EARS
- [EARS: The Easy Approach to Requirements Syntax | Medium](https://medium.com/paramtech/ears-the-easy-approach-to-requirements-syntax-b09597aae31d)
- [Alistair Mavin EARS](https://alistairmavin.com/ears/)
- [Easy Approach to Requirements Syntax (EARS) | IEEE](https://ieeexplore.ieee.org/document/5328509/)
- [EARS – The Easy Approach to Requirements Syntax: The Definitive Guide - QRA](https://qracorp.com/guides_checklists/the-easy-approach-to-requirements-syntax-ears/)

### Volereテンプレート
- [Volere Requirements Specification Template](https://www.volere.org/templates/volere-requirements-specification-template/)
- [Volere Requirements](https://www.volere.org/)
- [Volere Requirements Specification Template | ReqView](https://www.reqview.com/doc/volere-template/)

### NLPによる要求解析
- [QuARS A NLP Tool for Requirements Analysis](https://ceur-ws.org/Vol-2376/NLP4RE19_paper07.pdf)
- [Leveraging Natural Language Processing in Requirements Analysis - QRA](https://qracorp.com/leveraging-natural-language-processing-in-requirements-analysis/)
- [Natural Language Processing (NLP) for Requirements Engineering | arXiv](https://arxiv.org/pdf/2004.01099)
- [Natural Language Processing for Requirements Engineering: A Systematic Mapping Study | ACM](https://dl.acm.org/doi/10.1145/3444689)

### 日本語資料
- [要求仕様の曖昧さを理解し、ソフトウェアテストを組み立てる - ベリサーブ](https://www.veriserve.co.jp/asset/approach/column/test-technique/software-test03.html)
- [自然言語の曖昧性 – コンピュータは「このはしわたるべからず」がわかるか？ | Playgram](https://playgram.jp/oshiete-pfn/robot-3-nlp/)
- [正確な要求記述、要求仕様を定義する技法USDMとは](https://www.eureka-box.com/media/column/a19)
- [USDMで仕様を上手にアウトプットしよう！ | Sqripts](https://sqripts.com/2024/02/06/90314/)
- [要求仕様書の書き方完全ガイド](https://ones.com/ja/blog/how-to-write-requirements-document-sample-and-format/)
- [要求仕様 - Wikipedia](https://ja.wikipedia.org/wiki/%E8%A6%81%E6%B1%82%E4%BB%95%E6%A7%98)
