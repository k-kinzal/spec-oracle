# API仕様とインターフェース記述言語（IDL）

## 1. IDLの歴史と発展

### 1.1 起源と初期の発展

インターフェース記述言語（IDL: Interface Description Language）の概念は1980年代半ばに登場した。Cronus Type Definition LanguageやMach Interface Generatorが初期の実装として知られる。その根底には、1970年代に発展したリモートプロシージャコール（RPC）メカニズムがあり、1980年代にはSun RPCなどがIDLの形式化を推進した。

### 1.2 DCE/RPC

分散コンピューティング環境（DCE）のRPCは、Open Software Foundation（OSF）が委託したRPCシステムである。DCE RPCでは、IDLコンパイラによるインターフェース記述のコンパイルによってクライアント・サーバスタブが生成され、NDR（Network Data Representation）仕様がIDLデータ型からオクテットストリームへのマッピングを担当した。DCE IDLは後続の多くのIDLの基盤となった。

### 1.3 CORBA IDL

OMG（Object Management Group）は1989年に設立され、1991年にCORBA 1.0仕様の基盤要素としてIDLを導入した。CORBA IDLはDCE/RPCのIDLを基盤としつつ、オブジェクト指向の概念を取り入れ、言語中立・プラットフォーム中立なインターフェース定義を実現した。CORBAは異なるプログラミング言語やOS間での分散オブジェクト通信を可能にし、企業システムで広く採用された。

### 1.4 Microsoft COM/DCOM IDL

Microsoftは独自のComponent Object Model（COM）およびDistributed COM（DCOM）においてIDLを使用し、ネットワーク環境におけるコンポーネント間インターフェースを定義した。DCOMはDCE/RPCを拡張したMSRPCを基盤としており、IDLの系譜を直接受け継いでいる。

## 2. SOAP/WSDL時代のWebサービス仕様

### 2.1 SOAPの発展

SOAP（Simple Object Access Protocol）は、1998年にXML-RPCとして登場し、Dave Winer、Don Box、Bob Atkinson、Mohsen Al-GhoseinによってMicrosoft向けに開発された。2000年5月にW3C Noteとしてバージョン1.1が公開され、2007年にはSOAP 1.2 Second EditionがW3C勧告となった。SOAPはXMLベースのメッセージングプロトコルとして、エンタープライズ統合の標準となった。

### 2.2 WSDL（Web Services Description Language）

WSDLはWebサービスのインターフェースを記述するためのXMLベースの言語である。

- **WSDL 1.0**（2000年9月）：IBM、Microsoft、Aribaが共同開発。IBMのNASSLとMicrosoftのSDLを統合したもの
- **WSDL 1.1**（2001年3月）：1.0の形式化。実質的な変更はなし
- **WSDL 2.0**（2007年6月）：W3C勧告。複数インターフェース定義、インターフェース継承、明示的なメッセージ交換パターン（MEP）のサポートなど大幅に改良

WSDLはSOAPと組み合わせてWebサービスの記述・発見・呼び出しの標準を形成し、WS-*仕様群（WS-Security、WS-ReliableMessaging等）とともにエンタープライズSOAの基盤となった。

## 3. RESTful API仕様

### 3.1 OpenAPI（Swagger）

OpenAPIは現在、RESTful API仕様のデファクトスタンダードである。もともとSwagger仕様として開発され、2015年にLinux Foundation傘下のOpenAPI Initiativeに移管された。最新の安定版はOpenAPI 3.1.xであり、JSON Schemaとの完全互換性が実現されている。

採用率の調査では、OpenAPI 2.0/3.xが39〜55%の回答者に使用されており、他の仕様を大きく引き離している。「OpenAPI」は仕様そのもの、「Swagger」はその仕様に対応するツールセットを指す。

### 3.2 RAML（RESTful API Modeling Language）

RAMLはAPIの「モデリングと設計」に焦点を当てたトップダウン仕様であり、YAML形式のみをサポートする。REST以外にもHTTPを使用するRPCやSOAPアーキテクチャも記述可能という特徴を持つ。しかし近年は採用率が低下傾向にあり（7%程度）、MuleSoft Anypoint Platform自体もOpenAPI 3.0サポートを開始している。

### 3.3 API Blueprint

API BlueprintはMarkdown形式に依拠した仕様記述フォーマットで、ドキュメントの読みやすさを重視していた。しかし2019年以降はメンテナンスが事実上停止しており、Apiary自体がOpenAPI 3.0の実験的サポートを開始したことが背景にある。

### 3.4 現状の評価

OpenAPIが事実上の標準として確立している。オープンソース性、Linux Foundationの支援、広範なツールエコシステムがその地位を支えている。RAMLやAPI Blueprintは特定のユースケースでは残存するが、全体的な市場シェアは縮小している。

## 4. GraphQL Schema Definition Language

GraphQL SDL（Schema Definition Language）は、GraphQL仕様の一部として定義された人間可読なスキーマ定義言語である。その構文は簡潔でありながら強力な表現力を持つ。

主要な特徴は以下の通りである。

- **型システム**：Object、Scalar、Enum、Interface、Union、Input Objectの6種類の名前付き型定義
- **組み込みスカラ型**：Int、Float、String、Boolean、ID。カスタムスカラ型も定義可能
- **ルート操作型**：Query、Mutation、Subscriptionの3つの特別なルート操作型
- **型修飾子**：List（[]）とNon-Null（!）による出力型・入力型の制約
- **ドキュメント**：Markdown対応のdescriptionフィールドによるスキーマ内ドキュメント

GraphQL SDLは言語非依存であり、すべてのプログラミング言語・フレームワーク間で一貫したスキーマ定義を可能にする。REST APIとは異なり、クライアントが必要なデータの形状を指定できるクエリ言語と一体化している点が特徴的である。

## 5. gRPCとProtocol Buffers

gRPCはGoogleが開発した高性能RPCフレームワークであり、HTTP/2を使用し双方向ストリーミングをサポートする。データシリアライゼーションにはProtocol Buffers（Protobuf）を使用し、テキストベースのフォーマット（JSON等）と比較して3〜10倍高速な処理を実現する。

Protocol Buffersはバイナリシリアライゼーションフォーマットであると同時にIDLとしても機能し、`.proto`ファイルでサービスとメッセージ型を定義する。`protoc`コンパイラにより、多数の言語（C++、Java、Python、Go、C#等）のクライアント・サーバコードが自動生成される。

## 6. Apache Thrift・Apache Avro

### 6.1 Apache Thrift

Apache ThriftはFacebookが開発し、Apache Software Foundationに寄贈されたフレームワークである。gRPCと同様にデータシリアライゼーションとRPC通信の両方を提供する。独自のIDLでサービスとデータ構造を定義し、特徴的な点としてバイナリ・コンパクト・JSON等、複数のシリアライゼーションプロトコルを選択できる柔軟性がある。

### 6.2 Apache Avro

Apache AvroはProtobufやThriftと同等のスコープを持つが、動的言語を念頭に設計された。最大の特徴は、スキーマがメッセージヘッダに直接埋め込まれるため、事前のコンパイルステージが不要である点である。Apache Hadoopエコシステムとの親和性が高く、大規模データ処理パイプラインでの採用が多い。

### 6.3 スキーマ進化

Thrift、Protobuf、Avroの三者すべてがスキーマ進化（Schema Evolution）をサポートしている。異なるバージョンのスキーマを持つプロデューサとコンシューマが共存でき、後方互換性・前方互換性を維持しながらスキーマを変更可能である。

## 7. JSON SchemaとJSON-LD

### 7.1 JSON Schema

JSON SchemaはJSONデータの構造を記述・検証するための仕様である。OpenAPI仕様においてリクエスト・レスポンスの構造記述に広く組み込まれており、OpenAPI 3.1ではJSON Schema Draft 2020-12との完全互換が実現された。API仕様におけるデータモデル定義の標準的な手段として機能している。

### 7.2 JSON-LD

JSON-LD（JSON for Linked Data）は、JSONドキュメントにコンテキスト化された意味（セマンティクス）を付与するための仕様である。「context」の概念により、JSONオブジェクトのプロパティをRDFモデルに基づくオントロジーの概念にマッピングする。JSON Schemaがデータ構造を定義するのに対し、JSON-LDはデータの意味的な相互運用性を提供する。W3C勧告としてJSON-LD 1.1が策定されている。

## 8. AsyncAPI（非同期API仕様）

AsyncAPIは非同期APIを定義するための業界標準仕様であり、OpenAPIがHTTP APIに対して果たす役割を、イベント駆動アーキテクチャ（EDA）に対して果たすことを目指している。

主な構成要素として、メッセージブローカー（メッセージの受信・配信を担うインフラ）、パブリッシャー（メッセージ送信アプリケーション）、サブスクライバー（メッセージ受信アプリケーション）を定義する。

AsyncAPIは以下の特徴を持つ。

- プロトコル非依存（Kafka、AMQP、MQTT、WebSocket等に対応）
- 人間可読かつ機械可読
- データモデル、クライアントライブラリ、サーバコード、ドキュメントの自動生成をサポート
- NodeJS、Java、Python、Go、.NET、PHP等の多数言語に対応するツールエコシステム

## 9. API仕様ファーストvs実装ファーストアプローチ

### 9.1 仕様ファースト（Design-First）

APIの設計をコーディング前に仕様として詳細に定義するアプローチ。利点として、ベストプラクティスへの準拠、一貫性のあるAPI設計、仕様からのドキュメント・クライアントライブラリの自動生成が挙げられる。課題として、仕様の過剰定義リスクや、要件が流動的なプロジェクトでの時間コストがある。大規模プロジェクトやチーム間協調が重要な場合に推奨される。

### 9.2 実装ファースト（Code-First）

コード実装を起点とし、アノテーションやコメントからAPI定義を生成するアプローチ。Swashbuckle（.NET）やspringdoc-openapi（Java）などのツールが代表的。即座にコーディングを開始できる迅速さが利点だが、ドキュメントや標準化の欠如、フレームワークへの過度な依存がリスクとなる。

### 9.3 ハイブリッドアプローチ

初期段階で仕様ファーストによりAPI契約を定義し、開発の進行に伴い実装ファーストで仕様を進化させるハイブリッド手法も広く採用されている。

## 10. コード生成と仕様の同期

API仕様からのコード生成は現代的なAPI開発の中核的な要素である。

- **OpenAPI Generator**：OpenAPI仕様（v2/v3）からクライアントライブラリ（SDK）、サーバスタブ、ドキュメント、設定ファイルを自動生成する。40以上の言語・フレームワークに対応
- **gRPC Gateway**：gRPCサービス定義からRESTful JSON APIへのリバースプロキシを生成するprotocプラグイン
- **openapi2proto**：OpenAPI定義からProtobuf v3スキーマおよびgRPCサービス定義を生成する双方向変換ツール
- **Envoyプロキシ**によるgRPC-RESTトランスコーディング

仕様と実装の同期は永続的な課題であり、CI/CDパイプラインへの仕様検証の組み込み、破壊的変更の自動検出、仕様からのコード生成の自動化が実践的な解決策として確立されている。

## 11. APIガバナンスと仕様管理

APIガバナンスとは、組織がAPIの設計・開発・公開・保守・廃止を一貫して安全に行うためのポリシー・標準・プロセスの枠組みである。

主要な実践として以下が挙げられる。

- **仕様中心のガバナンス**：OpenAPI仕様をAPI契約の信頼できる唯一の情報源（Single Source of Truth）とする
- **所有権とカタログ**：各APIに明確なオーナーを設定し、オーナー、連絡先、データ分類、環境、バージョン、ライフサイクルステータスを含むカタログエントリを維持
- **自動化による強制**：OpenAPIの自動検証、破壊的変更の検出、セキュリティルールの適用を手動ではなく自動化
- **ドキュメントの最低要件**：description、examples、errorsなどの必須情報をポリシーとして強制

## 12. API仕様のバージョニング戦略

### 12.1 バージョニング方式

API仕様のバージョニングには主に4つの方式がある。

- **URIバージョニング**（`/v1/resources`）：最も直感的で広く採用されている
- **クエリパラメータ**（`?version=1`）：URIを変更せずにバージョンを指定
- **HTTPヘッダ**（`Accept: application/vnd.api.v1+json`）：コンテントネゴシエーションを活用
- **ハイブリッド**：上記を組み合わせた方式

### 12.2 セマンティックバージョニング

API仕様自体のバージョニングにはセマンティックバージョニング（SemVer）が推奨される。MAJOR.MINOR.PATCHの3部構成で、MAJORは破壊的変更、MINORは後方互換の新機能、PATCHはバグ修正を表す。

### 12.3 非推奨化（Deprecation）ポリシー

明確な非推奨化ポリシーの策定が重要であり、業界の一般的な実践として、6か月の告知期間、12か月のアクティブ移行サポート、18〜24か月での完全廃止というタイムラインが採用されている。Microsoft Graphは廃止前に少なくとも24か月の猶予を設けており、Google Mapsは約12か月の非推奨期間を設定している。

## まとめ

API仕様とIDLの歴史は、1980年代のDCE RPCから始まり、CORBA、SOAP/WSDL、REST（OpenAPI）、GraphQL、gRPC、そしてAsyncAPIへと進化してきた。この発展は、分散システム間の通信の複雑さを管理し、開発者体験を向上させるという一貫した動機に駆動されている。

現在のAPI仕様エコシステムでは、同期REST APIにはOpenAPI、クエリ志向APIにはGraphQL SDL、高性能RPCにはProtocol Buffers/gRPC、非同期イベント駆動APIにはAsyncAPIという棲み分けが形成されている。仕様ファーストアプローチの採用拡大、自動化されたガバナンス、CI/CDパイプラインへの仕様検証の統合が、現代のAPI開発のベストプラクティスとして定着しつつある。
