# Amazon/AWSにおけるTLA+活用事例

## 概要

Amazon Web Services（AWS）は、2011年以降、形式手法（特にTLA+）を活用して重要なシステムの設計問題を解決してきた。これは商用クラウドサービスにおける形式手法の最も成功した事例の一つとして広く知られている。本文書では、Newcombe et al.による2015年の画期的な論文「How Amazon Web Services Uses Formal Methods」を中心に、AWSのTLA+導入の経緯、効果、発見されたバグ、組織的展開、および最新の発展について詳述する。

---

## 1. TLA+導入の契機と歴史

### 1.1 導入前の状況

AWSのような大規模分散システムでは、並行性、非決定性、障害処理などの複雑性により、従来の開発手法だけでは見逃される微妙なバグが存在する。これらのバグは、広範な設計レビュー、コードレビュー、テストを経ても発見されないことが多い。

### 1.2 TLA+との出会い（2011年）

2011年、AWS内の一部のエンジニアがTLA+（Temporal Logic of Actions plus）を知り、試験的に使用を開始した。TLA+はレスリー・ランポート（Leslie Lamport）が開発した形式仕様記述言語であり、分散システムやコンカレントシステムの設計を数学的に記述し、モデル検査器TLCを用いて網羅的に検証できる。

### 1.3 DynamoDBでの初期成功（2012年）

2012年1月、AWSはDynamoDB（強い一貫性を保証するNoSQLデータストア）をローンチした。DynamoDBの開発過程において、T.R.（実名匿名化）は分散アルゴリズムの正当性を従来の非形式的証明で検証しようとしたが、限界を感じていた。

その後TLA+を使用してアルゴリズムを形式化したところ、モデル検査器は他のアルゴリズムにおいて**2つの深刻で微妙なバグ**を発見した。これらのバグは広範な設計レビュー、コードレビュー、テストを通過していたものであり、T.R.は「従来の手法をどれだけ追加しても発見できなかっただろう」と確信している。

T.R.は後に「もしDynamoDBの開発開始前にTLA+を知っていたら、最初から使用していただろう」と述べ、「形式的なTLA+仕様の作成と検証に費やした投資は、非形式的証明よりも信頼性が高く、かつ時間も少なくて済んだ」と評価している。

---

## 2. AWSにおけるTLA+の適用範囲

### 2.1 対象システム（2015年時点）

Newcombeらの2015年論文の時点で、AWSでは**7つのチームがTLA+を使用**し、すべてが高い価値を見出している。具体的には以下のような重要システムが含まれる：

- **DynamoDB**: NoSQLデータベースサービス
- **Amazon S3**: オブジェクトストレージサービス
- **Amazon EBS**: ブロックストレージサービス
- **内部分散ロックマネージャ**
- その他の重要な分散アルゴリズム

2015年論文では「10の大規模で複雑な実世界システム」にTLA+を適用したと記述されており、いずれのケースでも以下のいずれかの重要な価値が得られた：

1. 他の手段では発見できなかったであろう微妙なバグの発見
2. 正しさを犠牲にせずに積極的な性能最適化を行うための理解と確信の獲得

### 2.2 最新の展開（2024年）

2024年のTLA+ Confでは、AWS Distinguished EngineerのMarc Brookerが「Fifteen years of TLA+ at AWS」（AWSにおけるTLA+の15年間）という講演を行い、TLA+の継続的な活用と進化を報告している。

---

## 3. 発見されたバグの種類と事例

### 3.1 分散アルゴリズムにおける重大バグ

**M.D.によるロックフリー並行アルゴリズムの検証**

M.D.はPlusCal（TLA+の上位言語）を使用してロックフリー並行アルゴリズムを検証し、その後TLA+を用いてAWSの最も重要な新分散アルゴリズムの一つにおいて**重大なバグ**を発見した。M.D.はそのバグの修正も開発し、修正の正しさも検証した。

興味深いことに、C.N.（別のエンジニア）も同じアルゴリズムについて全く異なるスタイルで仕様を記述したが、**同じバグを発見**した。これは形式手法の再現性と信頼性を示す好例である。

**DynamoDBにおける2つの深刻なバグ**

前述の通り、T.R.が開発したDynamoDBのアルゴリズムにおいて、モデル検査器は2つの深刻で微妙なバグを発見した。これらは：

- 広範な設計レビューを通過
- 徹底的なコードレビューを通過
- 大規模なテストを通過

していたにもかかわらず、TLA+によって初めて発見された。

### 3.2 分散システム特有のバグタイプ

形式検証で発見されるバグの典型的なカテゴリは以下の通り：

- **レースコンディション（競合状態）**: 複数のプロセスやスレッドが共有リソースにアクセスする順序・タイミングに依存して、システムの動作が予期しない方向に変化する不具合
- **デッドロック**: 複数のノードが互いにリソースの解放を待ち続け、無限に停止してしまう状況
- **協調バグ**: 分散システムにおける複数ノードの同期・調整の問題により、一貫性のない動作やデッドロックが発生する不具合
- **コンセンサスアルゴリズムの微妙な失敗モード**: 特定のメッセージ遅延やノード障害の組み合わせで発生する、一貫性違反や活性違反

### 3.3 M.B.の個人プロジェクト

AWS Distinguished EngineerのMarc Brooker（M.B.）は個人の時間を使ってPlusCalで分散アルゴリズムを検証し、**3つのバグ**を発見した。この経験について公開ブログで詳述している。彼は後に「形式手法は私の問題の半分しか解決しない」という率直な評価も行い、形式手法の適用範囲と限界について考察している。

---

## 4. TLA+導入のROI（投資対効果）

### 4.1 学習コスト

**驚くべき短期間での習得**

形式手法は「膨大なトレーニングと労力を要し、ごくわずかなコードを検証するのにも大きなコストがかかるため、安全性が極めて重要な領域（医療システムや航空電子機器）でのみROIが正当化される」という評判があった。

しかし、AWSの経験はこの認識が**誤りであることを証明**した：

- **エントリーレベルからプリンシパルエンジニアまで**のエンジニアが、TLA+をゼロから学び、**2〜3週間で有用な結果**を得られた
- 中には**週末や夜の個人時間のみ**で習得した者もいる
- さらなるヘルプやトレーニングなしで成果を上げられた

**PlusCalの役割**

PlusCalは疑似コードの直接的な置き換えとして設計されており、多くのエンジニアはTLA+よりもPlusCalの方が学びやすいと感じている。PlusCalは単一のキー操作でTLA+に自動変換されるため、設計の記述にPlusCalを使い、詳細な検証にTLA+を使うというハイブリッドアプローチが可能である。

### 4.2 作業プロセスへの統合

**漸進的アプローチ**

AWSは、従来の散文形式の設計文書をまず作成し、その後部分的にPlusCalまたはTLA+へと段階的に精緻化するという実践を採用した。多くの場合、完全な仕様やモデル検査まで至らなくても、この過程で重要な洞察が得られる。

**設計レビュープロセスの変化**

現在では、経営陣が積極的に新機能や重要な設計変更についてTLA+仕様の作成を奨励している。形式手法は「特殊なケース」ではなく、設計プロセスの標準的な一部となりつつある。

### 4.3 時間節約と品質向上

T.R.の証言によれば、形式仕様の作成と検証に費やした時間は、非形式的証明の作成と検証に費やした時間よりも：

- **より信頼性が高い**
- **より時間がかからない**

つまり、形式手法の適用は品質を高めるだけでなく、開発時間の短縮にも寄与する可能性がある。

---

## 5. 組織的導入プロセス

### 5.1 初期段階（2011〜2012年）

TLA+の導入は一部の先駆的エンジニアの個人的な試みから始まった。DynamoDBでの成功が明確な証拠となり、AWS内のより広いエンジニアリングコミュニティへの紹介が行われた。

### 5.2 社内での拡散（2012年以降）

DynamoDBの事例が発表された直後、S3（Simple Storage Service）チームがTLA+使用の支援を要請した。これは成功事例の可視化が組織内での採用拡大に重要であることを示している。

### 5.3 経営層の支援（2014年以降）

2014〜2015年頃には、エグゼクティブマネジメントがTLA+仕様作成を積極的に奨励するようになった。トップダウンとボトムアップの両方からの推進が、組織全体への浸透を加速させた。

### 5.4 スケーリングの課題と対応（2010年代後半）

2010年代初頭のAWSでの初期チームを超えて形式手法を拡大する過程で、多くのエンジニアがTLA+の学習と生産的活用に苦労した。TLA+は数学により近い高レベル・抽象言語であり、命令型プログラミング言語とは大きく異なるためである。

この課題に対応するため、AWSは複数の戦略を採用した：

- 内部トレーニングプログラムの整備
- メンターシップ制度の確立
- ベストプラクティスとパターンの文書化
- より習得しやすい代替ツールの探索

---

## 6. AWSエンジニアの証言

### 6.1 Chris Newcombe（論文筆頭著者）

> 「TLA+は私の職業人生で学んだ最も価値あるものである。TLA+は、システム設計における微妙な欠陥を発見する極めて強力なツールを与えることで、私の働き方を変えた。新しい種類のメンタルモデルを構築するフレームワーク、正しさ特性とシステム設計の間の正確な関係を明らかにすること、ソフトウェア開発プロセスのはるかに早い段階で『もっともらしい散文』から正確な記述へと移行できることで、私の考え方を変えた。」

### 6.2 T.R.（DynamoDBエンジニア）

- 「もしDynamoDB開発開始前にTLA+を知っていたら、最初から使用していただろう」
- 「形式的TLA+仕様の作成と検証への投資は、非形式的証明よりも信頼性が高く、かつ時間も少なくて済んだ」
- 「バグは広範な設計レビュー、コードレビュー、テストを通過していたが、従来の手法をさらに追加しても発見できなかっただろうと確信している」

### 6.3 Marc Brooker（Distinguished Engineer）

Marc Brookerは複数のブログ記事と論文でTLA+の経験を共有している：

- **Physalia（トランザクショナルKVS）**: 設計全体でTLA+を広範に使用し、実装中のドキュメントとして活用
- **DynamoDBのレプリケーションプロトコル**: TLA+で仕様を記述
- **Aurora（リレーショナルDB）のコミットプロトコル**: PとTLA+でモデル化し、分散コミットのコストを2ラウンドトリップから1.5ラウンドトリップに削減する機会を発見（安全性を犠牲にせず）

彼はまた「形式手法は私の問題の半分しか解決しない」という率直な評価も行い、形式手法が万能ではないことを認めつつ、その価値を強調している。

---

## 7. TLA+以外の形式手法の併用

### 7.1 P言語（2020年代）

AWSはMicrosoftと共同で、分散システムの形式仕様のためのプログラミング言語**P**を広範に使用している。Pは分散システムのための形式仕様言語であり、より命令型プログラミングに近いスタイルを提供する。

2024年の論文「Systems Correctness Practices at AWS」では、TLA+とPの両方の活用が報告されている。Pは、TLA+の高度な抽象性に苦しむエンジニアのための代替選択肢として機能している。

### 7.2 Zelkova（ポリシー検証）

**Zelkova**はAWSが開発したポリシー分析エンジンであり、リソースの設定ミスを自動的に検出する。Zelkovaはポリシーの意味論をSMT（Satisfiability Modulo Theories）にエンコードし、振る舞いを比較し、性質を検証する。これにより、ユーザーのポリシーの設定ミスを検出する健全なメカニズムを提供する。

IAM（Identity and Access Management）、S3バケットポリシー、VPCセキュリティグループなどの設定の正しさを検証するために使用されている。

### 7.3 Cedar（認可ポリシー言語）

**Cedar**は、2024年に公式論文が発表された新しい認可言語である。表現力豊か、高性能、安全、かつ分析可能であり、AWSの製品・サービスで大規模に使用されている。Cedarはオープンソースであり、形式的に証明可能な正しさを持つ。

Amazon Verified Permissionsは、Cedarポリシー言語を使用するフルマネージドな認可サービスであり、「1日に数兆回の形式検証された認可処理」を実行していると報告されている（2024年キーノート）。

### 7.4 その他の形式手法

- **SMTソルバー**: IAMポリシーの等価性検証、アクセス制御の意味論的推論
- **ランタイム検証**: 本番環境での振る舞いの監視と仕様適合性の検証
- **シミュレーション**: 創発的システム動作の探索
- **重要性質の証明**: Coq、Isabelle/HOLなどの定理証明支援系の使用（報告は限定的）

---

## 8. 具体的適用事例の詳細

### 8.1 DynamoDB

**背景**

DynamoDBは、複数のデータセンター間で顧客データを複製しながら強い一貫性を保証するNoSQLデータストアである。2012年1月にローンチされた。

**TLA+の適用**

- コアレプリケーションプロトコルをTLA+で仕様化
- 分散コンセンサスアルゴリズムの正当性を検証
- 2つの深刻なバグを発見し、修正を検証

**効果**

T.R.は、TLA+なしではこれらのバグを発見できなかったと確信しており、「もっと早く知りたかった」という後悔を表明している。

### 8.2 Amazon S3

**背景**

S3は世界最大規模のオブジェクトストレージサービスであり、何兆ものオブジェクトを保存している。

**TLA+の適用**

DynamoDBの成功事例を聞いた直後、S3チームがTLA+の使用支援を要請した。具体的な適用内容は公開論文では詳述されていないが、分散メタデータ管理や一貫性プロトコルへの適用が推測される。

### 8.3 Amazon EBS

**背景**

EBSはEC2インスタンス向けの永続ブロックストレージサービスである。

**TLA+の適用**

レプリケーション、スナップショット、整合性保証などの重要な分散アルゴリズムにTLA+が適用されたと報告されている。

### 8.4 内部分散ロックマネージャ

AWSは複数の内部サービスで使用される分散ロックマネージャをTLA+で検証した。分散ロックは、デッドロックや活性違反などの微妙なバグが発生しやすい領域であり、形式検証の恩恵が特に大きい。

### 8.5 その他のシステム

2015年論文では「10の大規模で複雑な実世界システム」と記述されており、DynamoDB、S3、EBS、分散ロックマネージャ以外にも少なくとも6つのシステムが存在する。これらの詳細は機密情報のため公開されていない可能性が高い。

---

## 9. 形式手法の価値と限界

### 9.1 形式手法が提供する価値

AWSの15年間の経験から、形式手法は以下の価値を提供することが明らかになった：

**バグ発見の観点から**

1. **従来手法では発見不可能な微妙なバグの検出**: 設計レビュー、コードレビュー、テストをすべて通過したバグを発見
2. **早期発見**: 設計段階でのバグ発見により、修正コストを大幅に削減
3. **網羅性**: モデル検査による状態空間の網羅的探索

**設計と最適化の観点から**

1. **深い理解の獲得**: システムの振る舞いについての正確で深い理解
2. **積極的な最適化の実現**: 正しさへの確信により、従来なら躊躇したであろう性能最適化を実施可能に
3. **設計の明確化**: 形式化プロセス自体が曖昧さや矛盾を浮き彫りにする

**コミュニケーションの観点から**

1. **正確なドキュメント**: 仕様が実装の正確なドキュメントとして機能
2. **共通理解**: チーム間での設計の共通理解を促進

### 9.2 形式手法の限界

Marc Brookerの「形式手法は私の問題の半分しか解決しない」という指摘が象徴するように、形式手法には明確な限界がある：

**技術的限界**

1. **状態爆発**: 複雑なシステムでは状態空間が爆発的に増大し、モデル検査が現実的でなくなる場合がある
2. **抽象化の必要性**: 実際のシステムを検証可能なモデルに抽象化する際、重要な詳細を見落とすリスク
3. **仕様と実装のギャップ**: 形式仕様が正しくても、実装が仕様と一致しているかは別問題

**組織的・人間的限界**

1. **学習曲線**: 数学的背景が弱いエンジニアには習得が困難
2. **時間投資**: 初期の仕様作成には相応の時間が必要
3. **メンテナンス**: 設計変更に伴う仕様の更新の負担
4. **文化的障壁**: 形式手法を重視する文化の欠如

**適用範囲の限界**

1. **システムの一部のみ**: 多くの場合、システム全体ではなく、最も重要で複雑な部分（コアアルゴリズム、並行制御など）のみを形式化
2. **非機能要件**: 性能、可用性、ユーザビリティなどの非機能要件は形式検証が困難
3. **外部依存**: ハードウェア、ネットワーク、外部サービスなどの想定のモデル化の困難さ

---

## 10. 産業界への影響と標準化

### 10.1 他社への波及効果

AWSの成功事例は、他のクラウドプロバイダーやテクノロジー企業に大きな影響を与えた：

- **Microsoft Azure**: Cosmos DBなどで形式手法を使用
- **MongoDB**: レプリケーションプロトコルの形式検証
- **Elasticsearch**: 分散コンセンサスアルゴリズムの検証
- その他多数のオープンソースプロジェクト

### 10.2 TLA+ Foundationの設立

2023年4月、Linux FoundationはTLA+ Foundationの設立を発表した。創立メンバーには以下が含まれる：

- Amazon Web Services
- Microsoft
- Oracle
- その他の企業・組織

TLA+の採用と開発を促進し、TLA+プログラミング言語をメインストリームに導入することを目的としている。これは、TLA+がニッチなアカデミックツールから産業標準へと進化しつつあることを示している。

### 10.3 教育とトレーニング

TLA+のコミュニティは、学習リソースの拡充に力を入れている：

- **learntla.com**: 包括的なTLA+学習サイト
- レスリー・ランポートのビデオコース
- オンラインコミュニティとフォーラム
- 企業内トレーニングプログラム

---

## 11. 最新の動向（2024〜2026年）

### 11.1 LLMと形式手法の融合

2025〜2026年にかけて、大規模言語モデル（LLM）と形式検証の統合が進展している：

- **TLA+仕様の自動生成**: 自然言語記述からTLA+仕様を生成する研究
- **LLM支援によるモデル検査**: 反例の解釈、バグの説明、修正案の提案
- **仕様の自然言語説明**: TLA+仕様を人間が読みやすい説明に変換

AWSもこの分野での実験を進めていると推測されるが、公開情報は限定的である。

### 11.2 新しいツールと手法の採用

2024年の論文「Systems Correctness Practices at AWS」では、AWSが以下のような幅広い正しさ実践を採用していることが報告されている：

- 設計時のモデル検査
- ランタイム監視による本番環境での検証
- シミュレーションによる創発的動作の探索
- 重要性質の証明

これは、TLA+を中心としつつも、多様な形式手法・半形式手法を統合的に活用する方向へと進化していることを示している。

### 11.3 規模の拡大

「1日に数兆回の形式検証された認可処理」という数字が示すように、形式手法はAWSにおいて研究プロジェクトではなく、本番システムの中核的な品質保証手段となっている。

---

## 12. 教訓と推奨事項

### 12.1 組織への導入を成功させるために

AWSの経験から得られる教訓：

**段階的導入**

1. 小規模なパイロットプロジェクトから開始
2. 成功事例を可視化し、組織内で共有
3. トップダウンとボトムアップの両方からの推進

**実践的アプローチ**

1. 完璧な形式化を目指さず、価値が得られる範囲で使用
2. PlusCalのような習得しやすいツールの活用
3. 既存の設計プロセスへの統合（全面的な置き換えではなく）

**文化の醸成**

1. 経営層の理解と支援の獲得
2. エンジニアの学習時間の確保
3. 失敗を許容する文化（形式手法は万能ではない）

### 12.2 適用すべき領域

形式手法のROIが最も高い領域：

1. **並行性・分散性が高いシステム**: レースコンディション、デッドロック、分散コンセンサスなど
2. **重要性が極めて高いシステム**: 障害が大規模な損失を招く領域
3. **複雑な状態管理**: 多数の状態と遷移が存在するシステム
4. **セキュリティ・認証**: アクセス制御、暗号プロトコルなど
5. **長期運用されるシステム**: 初期投資を長期間にわたって回収できる

### 12.3 成功の測定

形式手法の価値を測定する指標：

- **発見されたバグの深刻度**: 他の手法では発見できなかったバグの数と深刻さ
- **設計の変更コスト削減**: 実装前の設計段階でのバグ発見による節約
- **性能最適化の実現**: 正しさへの確信によって可能になった最適化
- **エンジニアの満足度**: ツールの学習と使用に対するエンジニアの評価

---

## 13. まとめ

Amazon Web Servicesは、2011年から15年以上にわたり、TLA+を中心とした形式手法を実践し、以下を実証した：

1. **形式手法は実用的である**: 「高コストで限定的な価値」という従来の評判は誤りである
2. **学習は現実的である**: 2〜3週間で実用レベルに到達可能
3. **ROIは明確である**: 重大バグの発見と性能最適化の両面で価値を提供
4. **段階的導入が有効である**: 完全な形式化は不要、部分的な適用でも効果あり
5. **組織文化が重要である**: 経営層の支援と成功事例の共有が普及の鍵

DynamoDB、S3、EBSなどの世界規模のクラウドサービスにおいて、形式手法は研究室の実験ではなく、日常的な設計ツールとして定着している。「何兆回の形式検証された処理」という規模は、形式手法が産業界において成熟した技術であることを示している。

同時に、Marc Brookerが指摘するように「形式手法は問題の半分しか解決しない」という限界も認識されている。TLA+、P、Zelkova、Cedarなど、複数の形式手法・半形式手法を組み合わせた多層的アプローチが、AWSの現在の戦略である。

今後、LLMと形式手法の融合、より習得しやすいツールの開発、ランタイム検証との統合などにより、形式手法の適用範囲とアクセシビリティはさらに拡大すると予想される。AWSの15年間の実践は、形式手法が特殊な領域の技術ではなく、高品質なソフトウェアエンジニアリングの標準的な一部になりつつあることを示している。

---

## 参考文献

### 主要論文

1. Newcombe, C., Rath, T., Zhang, F., Munteanu, B., Brooker, M., & Deardeuff, M. (2015). "How Amazon Web Services Uses Formal Methods." *Communications of the ACM*, 58(4), 66–73. [https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/](https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/)

2. Newcombe, C., Rath, T., Zhang, F., Munteanu, B., Brooker, M., & Deardeuff, M. (2014). "Use of Formal Methods at Amazon Web Services." [https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf](https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf)

3. Cook, B., Khazem, K., Kroening, D., Tasiran, S., Tautschnig, M., & Tuttle, M. R. (2024). "Systems Correctness Practices at Amazon Web Services." *Communications of the ACM*. [https://cacm.acm.org/practice/systems-correctness-practices-at-amazon-web-services/](https://cacm.acm.org/practice/systems-correctness-practices-at-amazon-web-services/)

### ブログ記事・解説

4. Brooker, M. (2022). "Getting into formal specification, and getting my team into it too." *Marc's Blog*. [https://brooker.co.za/blog/2022/07/29/getting-into-tla.html](https://brooker.co.za/blog/2022/07/29/getting-into-tla.html)

5. Brooker, M. (2022). "Formal Methods Only Solve Half My Problems." *Marc's Blog*. [https://brooker.co.za/blog/2022/06/02/formal.html](https://brooker.co.za/blog/2022/06/02/formal.html)

6. Brooker, M. (2020). "Physalia: Millions of Tiny Databases." *Marc's Blog*. [https://brooker.co.za/blog/2020/02/17/physalia/](https://brooker.co.za/blog/2020/02/17/physalia/)

7. Acolyer, A. (2014). "Use of Formal Methods at Amazon Web Services." *The Morning Paper*. [https://blog.acolyer.org/2014/11/24/use-of-formal-methods-at-amazon-web-services/](https://blog.acolyer.org/2014/11/24/use-of-formal-methods-at-amazon-web-services/)

8. AWS Maniac. "How formal methods helped AWS to design amazing services." [https://awsmaniac.com/how-formal-methods-helped-aws-to-design-amazing-services/](https://awsmaniac.com/how-formal-methods-helped-aws-to-design-amazing-services/)

### ポリシー検証とCedar

9. Backes, J., Bolignano, P., et al. (2018). "Semantic-based Automated Reasoning for AWS Access Policies using SMT." *FMCAD 2018*. [http://www0.cs.ucl.ac.uk/staff/b.cook/FMCAD18.pdf](http://www0.cs.ucl.ac.uk/staff/b.cook/FMCAD18.pdf)

10. Amazon Science. (2024). "Cedar: A New Language for Expressive, Fast, Safe, and Analyzable Authorization." [https://assets.amazon.science/96/a8/1b427993481cbdf0ef2c8ca6db85/cedar-a-new-language-for-expressive-fast-safe-and-analyzable-authorization.pdf](https://assets.amazon.science/96/a8/1b427993481cbdf0ef2c8ca6db85/cedar-a-new-language-for-expressive-fast-safe-and-analyzable-authorization.pdf)

11. AWS Security. "Provable Security - Automated Reasoning." [https://aws.amazon.com/security/provable-security/](https://aws.amazon.com/security/provable-security/)

### TLA+ Foundation

12. Linux Foundation. (2023). "Linux Foundation Launches New Organization To Maintain TLA+." [https://www.linuxfoundation.org/press/linux-foundation-launches-tlaplus-foundation](https://www.linuxfoundation.org/press/linux-foundation-launches-tlaplus-foundation)

13. Microsoft Research. (2023). "TLA+ Foundation aims to bring math-based software modeling to the mainstream." [https://www.microsoft.com/en-us/research/blog/tla-foundation-aims-to-bring-math-based-software-modeling-to-the-mainstream/](https://www.microsoft.com/en-us/research/blog/tla-foundation-aims-to-bring-math-based-software-modeling-to-the-mainstream/)

### その他

14. Vanlightly, J. "Detecting Bugs in Data Infrastructure using Formal Methods (TLA+ Series Part 1)." *Splunk-MaaS*. [https://medium.com/splunk-maas/detecting-bugs-in-data-infrastructure-using-formal-methods-704fde527c58](https://medium.com/splunk-maas/detecting-bugs-in-data-infrastructure-using-formal-methods-704fde527c58)

15. Bharathi, V. "Paper notes: Use of Formal Methods at Amazon Web Services." [https://vishnubharathi.codes/blog/paper-notes-use-of-formal-methods-at-amazon-web-services/](https://vishnubharathi.codes/blog/paper-notes-use-of-formal-methods-at-amazon-web-services/)

16. Brooker, M. "Publications." *Marc's Blog*. [https://brooker.co.za/blog/publications.html](https://brooker.co.za/blog/publications.html)
