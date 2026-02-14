# 90. VRT（Visual Regression Testing）と仕様

## 概要

Visual Regression Testing（VRT、視覚的回帰テスト）は、アプリケーションの画面を画像として保存し、その画像差分を比較することで、意図しない視覚的変化を検出するテスト手法である。従来のユニットテストや統合テストが機能的な正しさを検証するのに対し、VRTはユーザーインターフェース（UI）の見た目の一貫性を保証する。本稿では、VRTの技術的原理、主要ツール、仕様との関係性、そして限界について包括的に考察する。

## VRTの基本原理

### ピクセル比較とその仕組み

VRTの最も基本的なアプローチは**ピクセルレベルの比較**である。アプリケーションの特定の画面状態をレンダリングし、スクリーンショットを撮影して基準画像（ベースライン）として保存する。その後、コードに変更が加えられるたびに新しいスクリーンショットを撮影し、ベースラインと**1ピクセル単位で比較**することで差分を検出する。

BrowserStackのガイドによれば、Percyなどの先進的なツールは単純なピクセル比較を超え、**DOM スナップショット**を取得する。これにより、複数のブラウザや画面幅で同じスナップショットを比較し、視覚的な差分を検出・グループ化できる。この手法は、レンダリング環境の違いによる誤検知を減らすのに役立つ。

### 構造比較とAI駆動型アプローチ

従来のピクセル比較は精度が高い反面、アンチエイリアシングやマイナーなレンダリングの揺らぎによって**偽陽性（false positive）**が発生しやすい。この問題に対処するため、最新のVRTツールは**AIと機械学習**を活用している。

Percyは2026年時点で、**Visual AIエージェント**を導入し、「人間のように」インターフェースを見る能力を持つ。強化学習を用いて、本物のバグと無害なレンダリングの変動を区別し、レビュー時間を3倍短縮する自然言語サマリーを提供する。このAI駆動型アプローチは、単なるピクセルマッチングから、**意味的な差分検出**へのパラダイムシフトを示している。

また、Applitoolsのような一部のツールは、**視覚的知覚**をモデル化したアルゴリズムを用いて、人間が気づく変化と気づかない変化を判別する。これは、ピクセル比較と構造比較の中間的なアプローチと言える。

## 主要VRTツールの比較

### Percy（BrowserStack）

Percyは**SaaS型**のビジュアルテストプラットフォームで、CI/CDパイプラインに統合しやすい設計になっている。主な特徴：

- **AIエージェント統合**: 6倍速いセットアップ、自動要件検出・インストール
- **DOM スナップショット方式**: ピクセル画像ではなくDOMを保存することで、複数ブラウザ・画面サイズでの比較が可能
- **自然言語サマリー**: 変更の影響を言語で説明し、レビューコストを削減
- 有料サービスだが、「札束で解決できるなら体験は非常に良い」と評価される

### Chromatic

ChromaticはStorybookの公式メンテナーが開発した**マネージドSaaS**である。主な特徴：

- **Storybook特化**: コンポーネントライブラリと密接に連携
- **シンプルなセットアップ**: スクリーンショット取得、デプロイ、差分比較を自動処理
- **無料プラン**: 月5,000スナップショットまで無料
- Storybookのストーリーがそのままテストケースになる思想

Storybookの公式ドキュメントでは、「各ストーリーは本質的にテスト仕様である。ストーリーを書いたり更新したりするたびに、無料で仕様を手に入れる」と述べられており、VRTと**仕様の自動生成**の関係を示唆している。

### BackstopJS

BackstopJSは**オープンソース**のVRTフレームワークで、Node.js上で動作する。主な特徴：

- **無料・自己ホスト**: インフラコストを抑えられる
- **Puppeteer/Playwright統合**: ヘッドレスブラウザでスクリーンショット取得
- **単純なピクセルマッチング**: アンチエイリアシングやレンダリング揺らぎに敏感で、偽陽性が発生しやすい
- 複数のビューポートサイズをサポート

Zennの記事によれば、BackstopJSは設定が対話的で導入しやすいものの、差分管理がリポジトリ内で完結するため、CI実行時の差分確認体験に課題がある。

### reg-suit + Storycap

日本で**最も普及している組み合わせ**とされる。主な特徴：

- **reg-suit**: 画像差分検出CLI、S3/GCSなどのストレージサービス連携
- **Storycap**: Storybook専用のスクリーンショットキャプチャツール
- **豊富なプラグイン**: GitHub Actions、Slackなどとの統合
- オープンソースで柔軟なカスタマイズが可能

設定も対話的に入力していくだけでほぼ完了でき、既存インフラ（AWS/GCP）を活用できる点が強みである。

### Playwright

Microsoftが開発したブラウザ自動化ライブラリで、`toHaveScreenshot()`メソッドによるVRT機能を提供。主な特徴：

- **Storybook非依存**: URL単位でのテストが可能
- **リポジトリ内差分管理**: 画像をGitで管理
- **Component Testing（実験的）**: v1.22以降、コンポーネント単位のVRTをサポート
- CI実行時の差分確認手段がやや弱い

### 選定基準

VRTツールを選ぶ際は、以下の要素を考慮すべきである：

1. **既存インフラ**: AWS/GCP活用状況、Storybook導入の有無
2. **セットアップ工数と維持管理負荷**: SaaSか自己ホストか
3. **差分確認体験**: UIの使いやすさ、CI統合
4. **予算制約**: 無料ツールか有料SaaSか
5. **偽陽性への対策**: AI機能の有無

2023〜2026年の現時点では、セットアップ利便性と情報量を総合すると、**reg-suit + Storycap**が実装的優位性を保持している一方、予算があれば**Chromatic**や**Percy**の体験が優れている。

## VRTと仕様の関係

### 見た目の仕様化

従来のソフトウェア仕様は、機能要件（「何をするか」）と非機能要件（「どれだけ速く、安全に」）に焦点を当ててきた。しかし、UIの**視覚的側面**を形式的に記述することは困難である。例えば：

- 「ボタンの色は青である」
- 「テキストのフォントサイズは16pxである」
- 「要素間の余白は8pxである」

このような視覚的制約を自然言語や従来の仕様記述言語で網羅的に記述するのは現実的ではない。VRTは、**スクリーンショットそのものを仕様とする**アプローチを提供する。つまり、ベースライン画像が「承認された視覚的仕様」となり、それからの逸脱を自動的に検出する。

Storybookのドキュメントでは、「各ストーリーは本質的にテスト仕様である」と述べられている。これは、コンポーネントの視覚的状態を記述したストーリーが、そのまま**実行可能な仕様**として機能することを意味する。

### UIの仕様記述の困難さ

Qiitaの記事や業務Webシステムのガイドラインによれば、UI仕様には以下のような記述困難な要素が含まれる：

- **空値フォーマット**: 値がない場合の表示
- **日付フォーマット**: タイムゾーン、ロケールの扱い
- **レスポンシブレイアウト**: 画面サイズごとの挙動
- **アニメーション**: 遷移の速度、イージング関数
- **インタラクション**: ホバー時、フォーカス時の状態

これらを網羅的に文書化するコストは膨大であり、しばしば実装時に「暗黙の了解」として扱われる。VRTは、こうした**暗黙の仕様**を画像として明示化し、回帰を防ぐ役割を果たす。

### Design Tokensとの連携

**Design Tokens**は、デザインシステムの値（色、タイポグラフィ、スペーシングなど）を**単一の真実の源**として管理する手法である。CSS Tricksの記事によれば、Design Tokensは以下の特徴を持つ：

- **プラットフォーム非依存**: JSON、YAMLなどで定義し、iOS、Android、Webに自動変換
- **階層構造**: プリミティブトークン（基本値）とセマンティックトークン（用途別）
- **ツール連携**: Amazon Style Dictionary、Salesforce Theoなど

Design Tokensは、**視覚的仕様の一部を形式化**する試みと言える。例えば：

```json
{
  "color": {
    "brand": {
      "primary": { "value": "#0066CC" }
    }
  },
  "spacing": {
    "small": { "value": "8px" }
  }
}
```

このトークンをもとにCSSやコンポーネントを生成すれば、デザインの一貫性が保証される。VRTは、こうしたトークンが正しく適用されているかを**視覚的に検証**する役割を担う。

Figmaなどのデザインツールを「真実の源」として、APIで設計値を自動抽出し、コードベースに反映させる統合も進んでいる。これにより、デザイナーの意図がトークンとして形式化され、VRTでその適用が自動検証される、というエコシステムが構築されつつある。

### Storybookと仕様駆動開発

Storybookは、UIコンポーネントを**孤立した環境**で開発・テストするツールである。各ストーリーは、コンポーネントの特定の状態（propsやAPIモック）を記述したものであり、**視覚的なテストケース**として機能する。

Storybookの公式チュートリアルでは、視覚的テストについて以下のように説明されている：

> 「視覚的テストはレンダリングされたピクセルを既知のベースラインと比較する。スナップショットテストはHTMLマークアップを比較するため、コードの変更が視覚的変化につながらない場合に偽陽性が増加する。一方、視覚的テストはユーザーが実際に見る内容をテストするため、より実用的で保守性に優れる。」

つまり、Storybookのストーリーは**仕様記述**であると同時に、**テスト対象**でもある。この二重性は、BDD（Behavior-Driven Development）における「実行可能な仕様」の概念と共通する。

Chromatic統合により、ストーリーの視覚的変化を自動検出し、承認されたベースラインはクラウドに同期される。これにより、チーム全体で**視覚的仕様の真実の源**が共有される。

## VRTの限界と偽陽性

### 動的コンテンツによる偽陽性

VRTの最大の課題は**偽陽性（false positive）**である。以下のような要素は、コードに変更がなくてもスクリーンショットに差分を生じさせる：

- **動画・アニメーション**: 再生タイミングによりフレームが異なる
- **広告・外部コンテンツ**: 第三者サービスのコンテンツ
- **タイムスタンプ**: 現在時刻の表示
- **ランダム要素**: ランダムなプレースホルダー画像など

Uzabaseの技術ブログでは、ReactPlayerで自動再生される動画コンポーネントの偽陽性問題を取り上げている。スナップショットAで撮影された映像とスナップショットBで撮影された映像が異なるため、必ず差分が検出される。

### 偽陽性への対策

同記事では、以下の2つの解決策を提示している：

**1. 動画再生の凍結**

Storybookのグローバル設定で、ReactPlayerをオーバーライドし、VRT実行時のみ`playing={false}`に設定：

```javascript
Object.defineProperty(ReactPlayer, 'default', {
  value: (props) => (
    <OriginalReactPlayer {...props} playing={isVrt ? false : props.playing} />
  ),
})
```

この手法は、プロダクションコードを変更せずに、テスト時のみ動作を制御できる。

**2. スクリーンショット遅延の追加**

アニメーションがある場合、storycapの`delay`パラメータで撮影タイミングを遅延させる。1000msのアニメーションには1300msの遅延を設定し、完了を待つ。

これらの対策により、「非侵襲的」に偽陽性を排除し、本物の視覚的回帰に集中できる。

### 差分閾値の調整

リクルートの技術ブログでは、差分閾値が偽陽性と偽陰性のバランスを左右すると指摘している：

- **閾値を大きく**: 偽陽性を減らすが、小さな変更を見逃すリスク（偽陰性）
- **閾値を小さく**: 偽陰性を減らすが、ノイズが増える（偽陽性）

適切な閾値はプロジェクトごとに異なり、チームの**コンセンサス**が必要である。

### VRTの運用上の課題

スタディサプリのブログでは、VRT運用の組織的課題を指摘している：

- **責務の曖昧さ**: 偽陽性とわかっても、コード修正で是正できない場合、誰が確認するか
- **チーム合意**: VRT自体が発展途上のため、運用ルールをチーム内で決定する必要がある

VRTは単なる技術的ツールではなく、**組織的プラクティス**として定着させる必要がある。

## VRTの仕様的位置づけ

### 半形式的仕様としてのVRT

形式手法の観点から見ると、VRTは**半形式的仕様**に分類される。完全に形式化されたZ記法やAlloyのような仕様言語とは異なり、画像という**非形式的な表現**をベースラインとして用いる。

しかし、VRTには以下の利点がある：

1. **直感的**: 画像は人間にとって理解しやすい
2. **実行可能**: 自動化されたテストとして機能
3. **網羅的**: 視覚的側面を包括的にカバー

これは、UMLなどの半形式的モデリング言語が、完全な形式性を犠牲にして実用性を得るのと類似している。

### BDDとの関係

BDD（Behavior-Driven Development）は、Gherkinなどの**自然言語ベースの仕様**をテストとして実行する手法である。Zennの記事によれば、BDDフレームワーク（Cucumber、Gaugeなど）は、技術者と非技術者の両方が理解できる「ユビキタス言語」で期待される振る舞いを記述する。

VRTは、**視覚的振る舞い**をBDD的にテストする手法と見なせる。Storybookのストーリーは、コンポーネントの期待される視覚的状態を記述しており、ChromaticやPercyはそれを検証する。

LINEのお年玉プロジェクトでは、「制作現場」でのVRT導入事例が紹介されている。デザイナーとエンジニアが視覚的仕様を共有し、変更をレビューするワークフローが確立されている。これは、仕様が**共有された理解**として機能する好例である。

### 仕様の階層性

仕様は多層的である。例えば：

- **要求レベル**: ユーザーストーリー、ユースケース
- **設計レベル**: アーキテクチャ、API仕様
- **実装レベル**: コード、型システム
- **視覚レベル**: UI、デザインシステム

VRTは**視覚レベルの仕様**を扱い、他の層とは独立して検証される。しかし、Design Tokensやコンポーネントライブラリを通じて、実装レベルと緊密に連携する。

## まとめ

Visual Regression Testing（VRT）は、UIの視覚的一貫性を保証するための強力な手法である。ピクセル比較からAI駆動型の意味的差分検出まで、技術は進化し続けている。Percy、Chromatic、BackstopJS、reg-suit、Playwrightなど、多様なツールが存在し、それぞれプロジェクトの要件に応じて選択される。

VRTは、従来の仕様記述では困難だった「見た目の仕様化」を可能にする。スクリーンショットをベースラインとし、Design TokensやStorybookと連携することで、**視覚的仕様の実行可能な検証**を実現する。

しかし、VRTには偽陽性の問題、動的コンテンツへの対応、運用上の組織的課題など、限界も存在する。これらは技術的対策（動画凍結、遅延設定、AI差分検出）と組織的合意（責務の明確化、閾値の決定）によって軽減される。

仕様理論の観点から、VRTは**半形式的仕様**の一種であり、BDDの視覚版とも言える。完全な形式性を持たないが、直感性と実用性により、現代のUIドリブンなソフトウェア開発において不可欠なツールとなっている。

今後、AIのさらなる進化により、VRTは単なる差分検出を超え、**デザイン意図の理解**や**アクセシビリティの自動検証**など、より高度な仕様検証へと発展する可能性を秘めている。

## 参考文献

### VRTツールと比較
- [Visual Regression Testing: Percy vs Chromatic vs BackstopJS | Medium](https://medium.com/@sohail_saifi/visual-regression-testing-percy-vs-chromatic-vs-backstopjs-0291477a23ef)
- [2023年にVisual Regression Testingを始めるならどんな選択肢があるか | Zenn](https://zenn.dev/loglass/articles/visual-regression-testing-comparison)
- [What is Automated Visual Regression Testing? | BrowserStack](https://www.browserstack.com/guide/automated-visual-regression-testing)
- [Visual Regression Testing Tools Compared | BrowserStack](https://www.browserstack.com/guide/visual-regression-testing-tool)
- [Visual Regression Testing: Comparing SaaS tools and DIY tools | Sparkbox](https://sparkbox.com/foundry/visual_regression_testing_with_backstopjs_applitools_webdriverio_wraith_percy_chromatic)
- [awesome-regression-testing | GitHub](https://github.com/mojoaxel/awesome-regression-testing)

### Storybook統合
- [Visual Tests | Storybook Tutorials](https://storybook.js.org/tutorials/intro-to-storybook/react/en/test/)
- [Visual tests | Storybook docs](https://storybook.js.org/docs/writing-tests/visual-testing)
- [How Netlify Uses Storybook for Visual Regression Testing](https://www.netlify.com/blog/storybook-visual-regression-testing/)
- [Visual Regression Testing for UI Components in Storybook | BrowserStack](https://www.browserstack.com/guide/visual-regression-testing-using-storybook)
- [Visual testing for Storybook • Chromatic](https://www.chromatic.com/storybook)

### 偽陽性と限界
- [Visual Regression Testが誤検知した動画やアニメーションの問題解決 | Uzabase](https://tech.uzabase.com/entry/2023/02/28/100554)
- [間違って覚えがちなテストの false positive（偽陽性）と false negative（偽陰性） | Zenn](https://zenn.dev/tnyo43/articles/2139de46a448f7)
- [Android における Visual Regression Test tips 集 #1 | スタディサプリ](https://blog.studysapuri.jp/entry/2021-08-23/android-vrt-tips-1)
- [Visual Regression Testing はじめました - 具体的な運用 Tips | リクルート](https://blog.recruit.co.jp/rmp/front-end/visual-regression-testing/)

### Design Tokens
- [What Are Design Tokens? | CSS-Tricks](https://css-tricks.com/what-are-design-tokens/)
- [Design Tokens Format Module 2025.10](https://www.designtokens.org/tr/drafts/format/)
- [Design tokens | U.S. Web Design System](https://designsystem.digital.gov/design-tokens/)
- [The developer's guide to design tokens and CSS variables | Penpot](https://penpot.app/blog/the-developers-guide-to-design-tokens-and-css-variables/)
- [Design Token-Based UI Architecture | Martin Fowler](https://martinfowler.com/articles/design-token-based-ui-architecture.html)

### UI仕様と実践
- [ユーザー体験を軸とした開発仕様書「UI Spec」とは | Goodpatch Blog](https://goodpatch.com/blog/mvp-ui-spec)
- [業務Webシステムでより良いUI実装のために決めておきたかった画面仕様 | Qiita](https://qiita.com/y_hokkey/items/cb6f1aa8817d0dd34e26)
- [制作現場におけるビジュアルリグレッションテストの導入 - 「LINEのお年玉」4年目の挑戦](https://engineering.linecorp.com/ja/blog/visual-regression-otoshidama/)

### Percy（AI駆動型VRT）
- [How to Implement Visual Regression Testing with Percy (2026)](https://oneuptime.com/blog/post/2026-01-25-visual-regression-testing-with-percy/view)
- [All-in-one visual testing and review platform | Percy](https://percy.io/)
- [Automated visual testing with Percy | BrowserStack](https://www.browserstack.com/percy/visual-testing)
- [Revolutionizing Visual Testing using Automation & AI: Percy | Halodoc](https://blogs.halodoc.io/percy-web/)

### BDDと仕様
- [ビヘイビア駆動開発BDDテスト | Squish](https://www.qt.io/ja-jp/quality-assurance/squish/feature-bdd-behavior-driven-development-testing)
- [BDD のすすめ | Zenn](https://zenn.dev/uakihir0/articles/241221-recm-bdd)
