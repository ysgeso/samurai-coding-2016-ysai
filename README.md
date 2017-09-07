# samurai-coding-2016-ysai
Samuraicoding 2016-2017に提出したAIです。

AIのアルゴリズムには手を加えていませんが、検証用のコードがいくつか追加されています。

Visual Studio でコンパイルしたい場合は、x64を設定し、プロジェクトのプロパティの
C/C++のコード生成の「拡張命令セットを有効にする」に「Advanced Vector Extensions 2」を
設定してコンパイルして下さい。また、CPUがAVX、SSE、BMI命令をサポートしていない場合は、
samuraicoding2016.hpp の　USE_AVX、USE_SSE、USE_BMI の#defineをコメントアウトして下さい。
