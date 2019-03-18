# samurai-coding-2016-ysai
Samuraicoding 2016-2017に提出したAIです。

AIのアルゴリズムには手を加えていませんが、検証用のコードがいくつか追加されています。

Visual Studio でコンパイルしたい場合は、x64を設定し、プロジェクトのプロパティの
C/C++のコード生成の「拡張命令セットを有効にする」に「Advanced Vector Extensions 2」を
設定してコンパイルして下さい。また、CPUがAVX、SSE、BMI命令をサポートしていない場合は、
samuraicoding2016.hpp の　USE_AVX、USE_SSE、USE_BMI の#defineをコメントアウトして下さい。

本AIに関する論文を書きました。興味がある方は<a href="https://www.jstage.jst.go.jp/article/jssst/36/1/36_119/_article/-char/ja">こちら</a>のリンクからどうぞ。

2019/3/17: 2017年度、2018年度の samuraicoding の AI も公開しました。

質問やコメントがあればissueのほうに書いてください。
