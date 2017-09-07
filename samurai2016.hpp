// デバッグ時は下記を有効にすること
//#define DEBUG
//#define DEBUGRTIME	// responseTime を使ったデバッグを行うかどうか（予選の時は、cerr の出力がわからなかったので苦肉の策。本選では使用しない）
#define DEBUGMSG		// デバッグ用のメッセージを表示するかどうか
#define USERANDOM		// 乱数を使用するかどうか
//#define LOADPARAM		// 評価パラメータを読み込むかどうか
// responseTime を使ったデバッグ出力を有効にするかどうか
#ifdef DEBUGRTIME
int rtime[96];
#endif
//#define DONOTUSEAI
// デバッグ関連の機能が有効な場合の定義
#ifdef DEBUG
// デバッグ関連の機能が有効でない場合は NDEBUG を undef しておく
#undef NDEBUG
// デバッグ表示を行うターン
int debugturn = 34;
// 分析の経過のデバッグ表示を行うかどうか
bool debuganalyze;
// 分析の結果を表示するかどうか
bool debuganalyzeresult;
// 分析による、過去の結果を表示するかどうか
bool debuganalyzepast;
// 評価に関するデバッグ表示を行うかどうか
bool debughyouka;
// 1手目を評価する際に枝かりをするかどうか
bool debugusealpha;
// 決勝提出バージョンかどうか
bool submitversion = true;
// 以下検証用に使用するフラグ
// analyze で1回分の行動しか計算しないようにするかどうか
bool analyzeonlyoneaction = false;
// recalculaterecords で analyze の結果を使用しない
bool donotuseanalyzeresultinrecalculaterecords = false;
// 侍が移動可能な場所を厳密に計算しない（マンハッタン距離が3以内の場所を移動可能な距離とする）
bool donotcalcarriveplacestrictly = false;
// 分析した検証用データをファイルに出力するかどうか
bool saveverifydata = false;

// 各ターンの味方の侍の移動可能な区画を計算するベンチマークを行うかどうか
bool benchmarkflag = false;
// ベンチマーク時に、calccanarriveplaceをテーブルを使わずに計算するかどうか
bool calccanarriveplacewithoutusingtableflag = false;

#define DEBUGANALYZERESULT
#define DEBUGANALYZEPAST
#define DONOTUSEAI
#define RECORDACTION
#define DEBUGANALYZECONDITION (debuganalyze && turn == debugturn)
#define DEBUGRECCONDITION (debughyouka && rec_start == debugturn)
#else
#if !defined(NDEBUG)
#define NDEBUG
#endif
#endif

#include <iostream>
#include <sstream>
#include <iomanip>
#include <cstring>
#include <immintrin.h>
#include <cassert>
#include <vector>
#include <unordered_map>
#include <chrono>
#include <math.h>
#include <cstdlib>
#include <fstream>
#include <random>
#include <map>
#if !defined(_MSC_VER)
#include <unistd.h>
#endif

using namespace std;

// avx が使える場合に有効にすること
// 最初のサーバだと使えてたのに、2月に入ってから新しくなったサーバでは使えなくなってる・・・ひどい
#define USE_AVX
//#define USE_SSE

// bmi2 が使える場合に有効にすること
#define USE_BMI2

// visual studio で開発する場合
#if defined(_MSC_VER)
typedef signed char        int8_t;
typedef short              int16_t;
typedef int                int32_t;
typedef long long          int64_t;
typedef unsigned char      uint8_t;
typedef unsigned short     uint16_t;
typedef unsigned int       uint32_t;
typedef unsigned long long uint64_t;
// 64ビットのデータのうち、最も下位のビットが 1 の桁数を返す
inline int LSB64(uint64_t v) { assert(v != 0); unsigned long index; _BitScanForward64(&index, v); return index; }
// それ以外の場合
#else
#undef USE_BMI2
inline int LSB64(const uint64_t v) { assert(v != 0); return __builtin_ctzll(v); }
#endif

// 最も下位のビットの桁数を計算して返す。その際にその桁を 0 にする。b が 0 の場合はうまくいかないので注意！
inline int pop_lsb(uint64_t & b) { int index = LSB64(b);  b &= b - 1; return index; }

#ifdef USE_AVX
const int alignsize = 32;
#define M256	__m256
//#define SETZERO256()	_mm256_setzero_ps()
#define AND256(x, y)	_mm256_and_ps(x, y)
#define OR256(x, y)		_mm256_or_ps(x, y)
#define XOR256(x, y)	_mm256_xor_ps(x, y)
#define ANDNOT256(x, y)	_mm256_andnot_ps(x, y)
#define TESTC256(x, y)	_mm256_testc_si256(*((__m256i *)&x), *((__m256i *)&y))
// 等しいかどうかのチェック _CMP_EQ_UQ は、の U の unordered は 同時に比較する float32 がNANの場合でも気にせず等しいかどうかをチェックするという意味
// なお、これはすべてが 1 のビットのM256を作成するために使う。等しいかどうかの比較はTEST256を使っている
#define CMPEQ256(x, y)  _mm256_cmp_ps(x, y, _CMP_EQ_UQ)
#else
#ifdef USE_SSE
const int alignsize = 16;
struct M256 {
	union {
		struct { __m128 m1; __m128 m2; };
		struct { __m128i m1i; __m128i m2i; };
	};
};
inline M256 AND256(M256 x, M256 y) { M256 m; m.m1 = _mm_and_ps(x.m1, y.m1); m.m2 = _mm_and_ps(x.m2, y.m2); return m; }
inline M256 OR256(M256 x, M256 y) { M256 m; m.m1 = _mm_or_ps(x.m1, y.m1); m.m2 = _mm_or_ps(x.m2, y.m2); return m; }
inline M256 XOR256(M256 x, M256 y)	{ M256 m; m.m1 = _mm_xor_ps(x.m1, y.m1); m.m2 = _mm_xor_ps(x.m2, y.m2); return m; }
// expression template でいずれ置き換える予定・・・
inline M256 ANDNOT256(M256 x, M256 y) { M256 m; m.m1 = _mm_andnot_ps(x.m1, y.m1); m.m2 = _mm_andnot_ps(x.m2, y.m2); return m; }
inline bool TESTC256(M256 x, M256 y) { return _mm_testc_si128(*((__m128i *)&x.m1), *((__m128i *)&y.m1)) & _mm_testc_si128(*((__m128i *)&x.m2), *((__m128i *)&y.m2)) ? true : false; }
//inline M256 CMPEQ256(M256 x, M256 y) { M256 m; m.m1 = _mm_cmp_ps(x.m1, y.m1, _CMP_EQ_UQ); m.m2 = _mm_cmp_ps(x.m2, y.m2, _CMP_EQ_UQ); return m; }
// _m_cmpeq_ps は使っちゃダメ。浮動小数点数として不正なビット列があるとうまくいかない
inline M256 CMPEQ256(M256 x, M256 y) { M256 m; m.m1i = _mm_cmpeq_epi64(x.m1i, y.m1i); m.m2i = _mm_cmpeq_epi64(x.m2i, y.m2i); return m; }
//inline M256 FULL256(M256 m1) { M256 m;  m.m1 = _mm_cmpeq_ps(m1.m1, m1.m1); m.m2 = m.m1; return m; }
#else
const int alignsize = 16;
struct M256 {
	union {
		struct { uint64_t m[4]; };
	};
};
inline M256 AND256(M256 x, M256 y) { M256 m; m.m[0] = x.m[0] & y.m[0]; m.m[1] = x.m[1] & y.m[1]; m.m[2] = x.m[2] & y.m[2]; m.m[3] = x.m[3] & y.m[3]; return m; }
inline M256 OR256(M256 x, M256 y) { M256 m; m.m[0] = x.m[0] | y.m[0]; m.m[1] = x.m[1] | y.m[1]; m.m[2] = x.m[2] | y.m[2]; m.m[3] = x.m[3] | y.m[3]; return m; }
inline M256 XOR256(M256 x, M256 y) { M256 m; m.m[0] = x.m[0] ^ y.m[0]; m.m[1] = x.m[1] ^ y.m[1]; m.m[2] = x.m[2] ^ y.m[2]; m.m[3] = x.m[3] ^ y.m[3]; return m; }
// expression template でいずれ置き換える予定・・・
inline M256 ANDNOT256(M256 x, M256 y) { M256 m; m.m[0] = (~m.m[0]) & y.m[0]; m.m[1] = (~x.m[1]) & y.m[1]; m.m[2] = (~x.m[2]) & y.m[2]; m.m[3] = (~x.m[3]) & y.m[3]; return m; }
inline bool TESTC256(M256 x, M256 y) { return ((x.m[0] == y.m[0]) && (x.m[1] == y.m[1]) && (x.m[2] == y.m[2]) && (x.m[3] == y.m[3])) ? true : false; }
inline M256 NOT256(M256 x) { M256 m; m.m[0] = ~m.m[0]; m.m[1] = ~x.m[1]; m.m[2] = ~x.m[2]; m.m[3] = ~x.m[3]; return m; }
//inline M256 CMPEQ256(M256 x, M256 y) { M256 m; m.m1 = _mm_cmp_ps(x.m1, y.m1, _CMP_EQ_UQ); m.m2 = _mm_cmp_ps(x.m2, y.m2, _CMP_EQ_UQ); return m; }
// _m_cmpeq_ps は使っちゃダメ。浮動小数点数として不正なビット列があるとうまくいかない
//inline M256 CMPEQ256(M256 x, M256 y) { M256 m; m.m1i = _mm_cmpeq_epi64(x.m1i, y.m1i); m.m2i = _mm_cmpeq_epi64(x.m2i, y.m2i); return m; }
//inline M256 FULL256(M256 m1) { M256 m;  m.m1 = _mm_cmpeq_ps(m1.m1, m1.m1); m.m2 = m.m1; return m; }
#endif
#endif

// bmi2 が使える場合
#ifdef USE_BMI2
// for AVX2 : hardwareによるpext実装
#define PEXT64(a,b) _pext_u64(a,b)
#define PDEP64(a,b) _pdep_u64(a,b)
// 使えない場合は pext, pdep に相当する関数を定義する。当然だが使える場合よりは遅い
#else
inline uint64_t pext(uint64_t val, uint64_t mask)
{
	uint64_t res = 0;
	for (uint64_t bb = 1; mask; bb += bb) {
		if ((int64_t)val & (int64_t)mask & -(int64_t)mask)
			res |= bb;
		mask &= mask - 1;
	}
	return res;
}

inline uint64_t PEXT64(uint64_t a, uint64_t b) { return pext(a, b); }

inline uint64_t pdep(uint64_t val, uint64_t mask)
{
	uint64_t res = 0;
	for (uint64_t bb = 1; mask; bb += bb) {
		if (val & bb)
			res |= (int64_t)mask & -(int64_t)mask;
		mask &= mask - 1;
	}
	return res;
}

inline uint64_t PDEP64(uint64_t a, uint64_t b) { return pdep(a, b); }
#endif

#define POPCNTU32(a) _mm_popcnt_u32(a)

// 自作のアロケータ。確保したメモリのアライメントが 32 に収まるようにしたもの。
template <class T>
struct MyAllocator {
	typedef T* pointer;
	typedef const T* const_pointer;
	typedef T& reference;
	typedef const T& const_reference;
	// 要素の型
	using value_type = T;
	static const int alignment = alignsize;

	// 特殊関数
	// (デフォルトコンストラクタ、コピーコンストラクタ
	//  、ムーブコンストラクタ)
	MyAllocator() {}

	// 別な要素型のアロケータを受け取るコンストラクタ
	template <class U>
	MyAllocator(const MyAllocator<U>&) {}

	template <class U>
	struct rebind
	{
		typedef MyAllocator<U> other;
	};

	// 初期化済みの領域を削除する
	void destroy(pointer p)
	{
		p->~T();
	}

	// 割当て済みの領域を初期化する
	void construct(pointer p, const T& value)
	{
		new((void*)p) T(value);
	}

	// メモリ確保
	T* allocate(std::size_t n)
	{
#if defined(_MSC_VER)
		return reinterpret_cast<T*>(_aligned_malloc(sizeof(T) * n, alignment));
#else
		void* p;
		return reinterpret_cast<T *>(posix_memalign(&p, alignment, sizeof(T) * n) == 0 ? p : nullptr);
#endif
	}

	// メモリ解放
	void deallocate(T* p, std::size_t n)
	{
		static_cast<void>(n);
#if defined(_MSC_VER)
		_aligned_free(p);
#else
		std::free(p);
#endif
	}
};

// 評価値に関係するパラメータ定義
// 評価の最小、最大値
double HYOUKA_MIN = -100000000;
double HYOUKA_MAX = 100000000;

int EARLY_TURN = 24;						// このターンより前は、あらかじめ定義した行動の評価値にボーナスを加える
double HYOUKA_EARLY_BESTACTION = 1250;		// 加えるボーナス

double HYOUKA_OCCUPY = 90;					// 味方の視界内の占領地1マスに対する評価値。
double HYOUKA_ENEOCCUPY = -90;				// 敵の視界内の占領地1マスに対する評価値
double HYOUKA_OCCBYNEXTPERIOD = 90;			// 次のピリオドも含めた行動するキャラクターの占領マスに対する評価
double HYOUKA_SIGHT = 10;					// 視界1マスに対する評価値
double HYOUKA_NOTALLYOCCUPY_INSIGHT = 10;	// 視界内の味方が占領していない場所1マスに対する評価値
double HYOUKA_ENEMYOCCUPY_INSIGHT = 0;		// 視界内の敵が占領している可能性のある場所1マスに対する評価値
//double HYOUKA_DISTFROMBASE = 30;			// 本拠地からの距離1マスに対する評価値
//double HYOUKA_DISTFROMCORNER = 20;			// 本拠地の角からの距離1マスに対する評価値
double HYOUKA_DISTFROMTARGET = -50;			// それぞれのキャラクターの目標地点からの距離

double HYOUKA_NOMOVETURN = 36;				// 下記の評価を行うターン数
double HYOUKA_NOMOVE[3] = { 300, 150, 0 };	// 味方の行動可能な場合の評価。槍＞鉾＞鉞の順で行動を残しておきたい。
double HYOUKA_PASS = 150;					// パスすることによる評価値
double HYOUKA_APPEARED = 10;					// 顕現状態による評価値（必要なければ顕現状態の方が次の行動の幅がでる）
double HYOUKA_RANDOM = 10;					// 評価値に加算する乱数の幅（USERANDOMが定義されている場合のみ使われる）
// 各キャラクターの治療ターン数1あたりの評価値
// 味方が死んだ場合は、視界に関する評価が大幅に悪化する。一方で相手を殺した場合は、相手の視界に関する状況が悪化するはずなので、
// それを考慮して相手の治療ターン数に関する点数を大きめにとっておく
// 前半と後半で価値を変える
double HYOUKA_LATTER_TURN = 66;
double HYOUKA_RECOVERY[2][2][3] = { { { -20, -16, -12 }, { 30, 24, 18 } },{ { -18, -18, -18 },{ 24, 24, 24 } } };

// 治療ターン数の評価値に乗算する値
double HYOUKA_CUREMUL_NORMAL = 10;				// 通常の場合に乗算する値
double HYOUKA_CUREMUL_ENECANMOVE = 0.25;		// こちらがその敵を殺す前に、その敵が行動可能だった場合に乗算する値
double HYOUKA_CUREMUL_ALLYCANMOVE = 0.35;		// 敵がこちらを殺す前に、その味方が行動可能だった場合に乗算する値
double HYOUKA_CUREMUL_ALLYMOVED = 0.5;
double HYOUKA_CUREMUL_MAYKILLBEFOREKILLED = 0; // 敵がこちらを殺す前に、返り討ちできる場合に乗算する値

// 状況に応じて、以下の計算式で乗算する値を計算する 
double HYOUKA_CUREMUL_NORMAL_MAX = 10;
// 以下は count.tsv を読み込んだ場合は、使用しない
// 味方が顕現状態の場合
double HYOUKA_CUREMUL_NORMAL_DIV = 150;
// 味方が隠蔽状態で、攻撃をしていない場合などで存在場所が相手にわかっていない場合
double HYOUKA_CUREMUL_HIDDEN_MAX = 7.5;
double HYOUKA_CUREMUL_HIDDEN_DIV = 20;
// 味方が隠蔽状態だが、移動後に攻撃するなどして、存在場所が相手にわかっている可能性が高い場合
double HYOUKA_CUREMUL_MATTACKHIDDEN_MAX = 9.25;
double HYOUKA_CUREMUL_MATTACKHIDDEN_DIV = 100;
// 味方が隠蔽状態だが、攻撃後に移動するなどして、存在場所が多くても5か所に絞られる場合
double HYOUKA_CUREMUL_AMOVEHIDDEN_MAX = 7;
double HYOUKA_CUREMUL_AMOVEHIDDEN_DIV = 50;
//double HYOUKA_CUREMUL_RARECASE[3] = { 0.25, 0.5, 0.75 };		// 試合の記録からそこに敵が存在することがレアケースだと判断できる場合に乗算する値

// count.tsv を読み込んだ場合に使用するパラメータ
double HYOUKA_CUREMUL_MOVE = 1;
double HYOUKA_CUREMUL_ASSUMED = 20;
double HYOUKA_CUREMUL_ATTACK = 5;

double HYOUKA_NOTDETECTED = 50;		// 最初の行動を行ったキャラクターが敵に察知されない場合の評価値
double HYOUKA_MAYKILL = 100;		// 最初の行動で敵を殺した可能性がある場合、殺した可能性に比例して加算される評価値

double HYOUKA_ENEATTACKINNOTOCCUPIEDPLACE = 0.8;	// 敵が、敵の占領している場所でない場所で攻撃した場合に乗算される評価値。味方の行動が PREVACTION_MOVE の場合のみ使用する

double HYOUKA_NEARALLY_DISTMAX = 2;
double HYOUKA_NEARALLY_PERDIST = 50;
double HYOUKA_NEARALLY = -150;

double HYOUKA_NOOCCUPY = -3000;

// 30 ターンまでの、あらかじめ定義された行動
const int autoactions[30][4] = { { 15, 2, 0, 1 },{ 37, 2, 0, -1 },{ 61, 1, 1, 0 },{ 83, 1, -1, 0 },{ 15, 0, 0, 1 },{ 37, 0, 0, -1 },
{ 25, 2, 0, 1 },{ 47, 2, 0, -1 },{ 52, 1, 0, 1 },{ 74, 1, 0, -1 },{ 26, 0, 1, 0 },{ 48, 0, -1, 0 },
{ 61, 1, 1, 0 },{ 47, 0, 0, -1 },{ 25, 0, 0, 1 },{ 83, 1, -1, 0 },{ 555, 2, 0, 3 },{ 777, 2, 0, -3 },
{ 25, 0, 0, 1 },{ 47, 0, 0, -1 },{ 16, 1, 1, 0 },{ 38, 1, -1, 0 },{ 953, 2, 0, 1 },{ 951, 2, 0, -1 },
{ 16, 2, 1, 0 },{ 38, 2, -1, 0 },{ 27, 1, 0, -1 },{ 45, 1, 0, 1 },{ 25, 0, 0, 1 },{ 47, 0, 0,-1 } };

// 直前の行動が相手にどう見えているかを表す定数。現在隠蔽状態かどうかは関係ない
const int PREVACTION_MOVE = 0;		// 直前の行動が移動のみ（または相手に見えていない）で、現在位置が相手にわからない場合
const int PREVACTION_ASSUMED = 1;	// 相手に場所が推測されている可能性が高い場合
const int PREVACTION_ATTACK = 2;	// 相手に攻撃したことが察知されている場合

// 盤の幅、高さ、治療ターン
const int width = 15;
const int height = 15;
const int recoveryTurns = 18;

// 分析に費やしても良い最大時間
int analyzetimelimit = 50;
// 分析を含む、そのターンに費やしても良い最大時間
int timelimit = 190;

// 手番情報
extern int playOrder;
// 最大ターン
extern int totalTurns;

// すべてのビットが 0 な 256ビットのデータ
extern M256 zero256;

// 回転させる関数（サンプルのコードをそのまま流用）
void rotate(int direction, int x0, int y0, int& x, int& y);

// 時間を計測するクラス
class Timer {
public:
	Timer() {
		reset();
	}
	// 時間をリセットする
	void reset() {
		totaltime = 0;
		starttime = chrono::high_resolution_clock::now();
		stopflag = false;
	}
	void stop() {
		if (stopflag == false) {
			totaltime += chrono::duration_cast<chrono::microseconds>(chrono::high_resolution_clock::now() - starttime).count();
			stopflag = true;
		}
	}
	void start() {
		if (stopflag == true) {
			starttime = chrono::high_resolution_clock::now();
			stopflag = false;
		}
	}
	// 経過時間を取得する
	int64_t gettime() const {
		return totaltime + (stopflag ? 0 : chrono::duration_cast<chrono::microseconds>(chrono::high_resolution_clock::now() - starttime).count()) / 1000;
	}
	int64_t getmicrotime() const {
		return totaltime + (stopflag ? 0 : chrono::duration_cast<chrono::microseconds>(chrono::high_resolution_clock::now() - starttime).count());
	}
private:
	chrono::high_resolution_clock::time_point starttime, stoptime;
	bool stopflag;
	int64_t totaltime = 0;
};

ostream& operator<<(ostream& os, const Timer& timer)
{
	os << timer.gettime() << " ms" << endl;
	return os;
}

// 2次元の場所を表す構造体
// 座標(x, y) は 0 <= x < 16, 0 <= y < 16 までの範囲を取る
// 実体としては x + y * 16 の 1 バイトの値で座標を記録する
// 座標ではなくベクトルとして使うこともできる。
// この場合は、-8 <= x < 7, -8 <= y < 7 として考える
struct Pos {
	Pos() {}
	Pos(const uint8_t x_, const uint8_t y_) : pos((y_ << 4) + x_) {}
	Pos(const uint8_t p) : pos(p) {}

	// ranged based for を使えるようにするための関数定義。
	// ranged based for を使って (0, 0), (1, 0)・・・(15, 0), (0, 1), …の順で座標を取る
	// このゲームでは、(0, 0) - (14, 14) までの範囲の座標を使うので、 end は (15, 14) とする
	// このやり方だと、ゲームに使われない(y, 15) の座標も ranged base for で取ってくることになるが、
	// それらの座標を取ってこないようにすると、operator++ で条件分岐が発生してかえって遅く
	// なりそうなので気にしないことにする
	Pos begin() {
		return Pos(0, 0);
	}
	Pos end() {
		return Pos(15, 14);
	}
	Pos operator*() { return *this; }
	void operator++() { (this->pos)++; }

		// (x, y) を使って座標を設定する
	void set(const int8_t x_, const int8_t y_) {
		pos = (y_ << 4) + x_;
	}
	// x 座標を取得する
	int getx() const {
		return pos & 0x0f;
	}
	// y 座標を取得する
	int gety() const {
		return pos >> 4;
	}
	// 1バイトで表現された座標の値を取得する
	int getpos() const {
		return pos;
	}
	// ベクトルとして使った場合の、x 方向の値を取得する
	int getdirx() const {
		return (pos & 0x0f) < 8 ? pos & 0x0f : (pos & 0x0f) - 16;
	}
	// ベクトルとして使った場合の、y 方向の値を取得する
	int getdiry() const {
		return ((pos >> 4) < 8 ? pos >> 4 : (pos >> 4) - 16) + (getdirx() >= 0 ? 0 : 1);
	}
	bool operator==(const Pos p) const {
		return pos == p.pos;
	}
	bool operator!=(const Pos p) const {
		return pos != p.pos;
	}
	void operator=(const Pos p) {
		pos = p.pos;
	}
	void operator=(const uint8_t pos_) {
		pos = pos_;
	}
	void operator+=(const Pos p) {
		pos += p.pos;
	}
	// p とのマンハッタン距離を計算する
	int dist(const Pos& p) const {
		return abs(getx() - p.getx()) + abs(gety() - p.gety());
	}
	// ベクトルとして考えた場合、direction 方向（反時計回りに 0: 0度, 1: 90度, 2: 180度, 3: 270度 回転させた座標)を計算する
	Pos rotate(const int direction) const {
		int x = getdirx();
		int y = getdiry();
		switch (direction) {
		case 0:
			return Pos(x, y);
		case 1:
			return Pos(y, -x);
		case 2:
			return Pos(-x, -y);
		case 3:
			return Pos(-y, x);
		default:
			assert(0);
			return Pos(0, 0);
		}
	}
	// Pos どうしの + の処理
	Pos operator+(const Pos pos2) const {
		Pos pos1 = *this;
		pos1 += pos2;
		return pos1;
	}
	// 座標種類の個数
	static const int possize = 16 * 16;
	// 座標を表すデータ
	uint8_t pos;
};

ostream& operator<<(ostream& os, const Pos& p);

// 先手の場合の本拠地の場所。後手の場合は init 関数の中で入れ替える
static Pos homepos[2][3] = { { Pos(0, 0), Pos(0, 7), Pos(7, 0) },{ Pos(14, 14), Pos(14, 7), Pos(7, 14) } };
// それぞれのキャラクターが目指す場所
static Pos targetpos[2][3] = { { Pos(9, 9), Pos(3, 11), Pos(11, 3) }, { Pos(5, 5), Pos(11, 3), Pos(3, 11) } };

// ゲーム盤を表す構造体。それぞれのマスを 256 ビットのデータで表現する
// ゲーム盤の座標を (x, y) とした場合、その座標のデータは 下位 Pos(x, y).getpos() ビット目に対応する
struct alignas(alignsize) BitBoard {
	// コンストラクタ。通常時はデータは初期化しない
	BitBoard() {}
	// 中身を 0 クリアする場合のコンストラクタ
	// flag が 1 の場合は 中身をすべて 1 にする
	BitBoard(int flag) {
		if (flag == 0) {
			clear();
		}
		else if (flag == 1) {
			memset(&data, 255, 32);
		}
	}
	// 中身を 0 クリアする
	void clear() {
		memset(&data, 0, 32);
//		this->data = SETZERO256();
	}
	// 様々なビット演算に関する関数
	const BitBoard operator | (const BitBoard& bb) const {
		BitBoard retval;
		retval.data = OR256(data, bb.data);
		return retval;
	}
	const BitBoard& operator |= (const BitBoard& bb) {
		data = OR256(data, bb.data);
		return *this;
	}
	const BitBoard operator & (const BitBoard& bb) const {
		BitBoard retval;
		retval.data = AND256(data, bb.data);
		return retval;
	}
	const BitBoard& operator &= (const BitBoard& bb) {
		data = AND256(data, bb.data);
		return *this;
	}
	const BitBoard operator ^ (const BitBoard& bb) const {
		BitBoard retval;
		retval.data = XOR256(data, bb.data);
		return retval;
	}
	const BitBoard& operator ^= (const BitBoard& bb) {
		data = XOR256(data, bb.data);
		return *this;
	}

	const BitBoard operator ~() const {
		BitBoard retval;
#if defined(USE_AVX) | defined(USE_SSE)
		retval.data = ANDNOT256(data, CMPEQ256(data, data));
#else
		retval.data = NOT256(data);
#endif
		return retval;
	}
	bool operator==(const BitBoard& bb) const {
		return (TESTC256(data, bb.data) & TESTC256(bb.data, data)) ? true : false;
	}
	bool operator!=(const BitBoard& bb) const {
		return (TESTC256(data, bb.data) & TESTC256(bb.data, data)) ? false : true;
	}
	// (~b1) & b2 を計算する 
	static BitBoard andnot(const BitBoard& b1, const BitBoard& b2) {
		BitBoard bb;
		bb.data = ANDNOT256(b1.data, b2.data);
		return bb;
	}
	// 自身が bb に完全に含まれているかどうかを調べる
	bool isincluded(const BitBoard& bb) const {
		return (*this & bb) == *this;
	}
	// すべてのビットが 0 かどうかを計算する
	bool iszero() const {
		return TESTC256(zero256, data) ? true : false;
	}
	void operator=(const BitBoard& bb) {
		memcpy(&data, &(bb.data), 32);
	}
	// (x, y) のビットを 1 にする
	void set(const int x, const int y) {
		assert(0 <= x && x < 16 && y >= 0 && y < 16);
		d16[y] |= 1 << x;
	}
	// p の位置のビットを 1 にする
	void set(const Pos p) {
		set(p.getx(), p.gety());
	}
	// (x, y) のビットを 0 にする
	void reset(const int x, const int y) {
		assert(0 <= x && x < 16 && y >= 0 && y < 16);
		d16[y] &= 0xffff - (1 << x);
	}
	// p のビットを 0 にする
	void reset(const Pos p) {
		reset(p.getx(), p.gety());
	}
	// (x, y) のビットが 1 の場合に true を返す
	bool isset(const int x, const int y) const {
		assert(0 <= x && x < 16 && y >= 0 && y < 16);
		return (d16[y] & (1 << x)) ? true : false;
	}
	// p のビットが 1 の場合に true を返す
	bool isset(Pos p) const {
		return isset(p.getx(), p.gety());
	}
	// ビットが 1 の数を数える
	int popcnt() const {
		return static_cast<int>(_mm_popcnt_u64(d64[0]) + _mm_popcnt_u64(d64[1]) + _mm_popcnt_u64(d64[2]) + _mm_popcnt_u64(d64[3]));
	}
	// 最も下位にある 1 のビットに相当する座標を Pos 型のデータで返し、そのビットを 0 にする
	// すべてのビットが 0 の場合に呼び出してはいけない！
	Pos pop() { return Pos((d64[0] != 0) ? pop_lsb(d64[0]) : (d64[1] != 0) ? pop_lsb(d64[1]) + 64 : (d64[2] != 0) ? pop_lsb(d64[2]) + 128 : (d64[3] != 0) ? pop_lsb(d64[3]) + 192 : 255); }

	// ranged based for を使えるようにするための関数定義。
	// ranged based for を使って (0, 0), (1, 0)・・・(15, 0), (0, 1), …の順でビットが 1 に相当する座標を Pos のデータ構造で取得する
	BitBoard begin() const;
	BitBoard end() const;
	Pos operator*() { return pop(); }
	void operator++() {}

	union {
		uint16_t	d16[16];
		uint32_t	d32[8];
		uint64_t	d64[4];
		__m128i		d128[2];
		M256		data;
	};
};

ostream& operator<<(ostream& os, const BitBoard& bb);

struct IntBoard {
	void clear(const int num);
	void set(const Pos p, const int data);
	void setifmax(Pos p, const int data);
	int get(const Pos p) const;
	int data[Pos::possize];
};

ostream& operator<<(ostream& os, const IntBoard& bb);

struct Action {
	Action() : pid(0), actionnum(0) {};
	Action(int action) : pid(0) {
		setaction(action, Pos(0, 0), false);
	}
	Action(int action, const Pos pos, const bool c) : pid(0) {
		setaction(action, pos, c);
	}
	// 行動をdirection * 90 度反時計回りに 回転する
	void rotate(const int direction) {
		assert(direction >= 0 && direction < 4);
		for (int i = 0; i < actionnum; i++) {
			if (actions[i] >= 1 && actions[i] <= 4) {
				actions[i] = (actions[i] + direction - 1) % 4 + 1;
			}
			else if (actions[i] >= 5 && actions[i] <= 8) {
				actions[i] = (actions[i] + direction - 5) % 4 + 5;
			}
		}
		dest = dest.rotate(direction);
	}
	// 行動を登録する。行動は10進数で表現し、1の位から順に10進数の一桁で行動を表す
	void setaction(int action, const Pos pos, const bool c) {
		assert(action >= 0 && action < 100000);
		actionnum = 0;
		while (action > 0 && actionnum < 4) {
			assert(actionnum < 4);
			actions[actionnum++] = action % 10;
			action = static_cast<int>(floor(action / 10));
		}
		dest = pos;
		changed = c;
	}
	void setaction(int action, const int _pid, const int x, const int y) {
		setaction(action, Pos(x, y), false);
		pid = _pid;
	}
	// 行動を表す数値を計算する
	int getactionvalue() const {
		int retval = 0;
		for (int i = actionnum - 1; i >= 0; i--) {
			retval *= 10;
			retval += actions[i];
		}
		return retval;
	}
	void push_back(const int action) {
		assert(action >= 1 && action <= 9 && actionnum < 4);
		actions[actionnum++] = action;
	} 
	void push_front(const int action) {
		assert(action >= 1 && action <= 9 && actionnum < 4);
		for (int i = actionnum - 1; i >= 0; i--) {
			actions[i + 1] = actions[i];
		}
		actions[0] = action;
		actionnum++;
	}
	void push_second(const int action) {
		assert(action >= 1 && action <= 9 && actionnum < 4);
		for (int i = actionnum - 1; i >= 1; i--) {
			actions[i + 1] = actions[i];
		}
		actions[1] = action;
		actionnum++;
	}
	bool operator==(const Action& a) const {
		return pid == a.pid && getactionvalue() == a.getactionvalue();
	}
	bool operator!=(const Action& a) const {
		return !(pid == a.pid && getactionvalue() == a.getactionvalue());
	}
	uint8_t	pid;			// 行動するプレーヤーのID
	uint8_t actionnum;		// 行動命令数
	uint8_t actions[4];		// 1 ～ 4: 占領、5: 移動（移動の内容は moveindex)、9:隠蔽、顕現
	Pos		dest;			// 移動先
	bool	changed;		// 移動先の状態が、最初の状態から（隠蔽または顕現によって）変化したかどうか
};

ostream & operator<<(ostream& os, const Action &ac);

inline bool isinfield(int x, int y) {
	return (x >= 0 && x < width && y >= 0 && y < height) ? true : false;
}

// 侍の状態
struct SamuraiState {
	Pos pos;			// 場所
	bool done;			// 行動済かどうか
	bool hidden;		// 隠蔽状態かどうか
	uint8_t recovery;	// 治療ターン数
	bool firstdone;		// 評価開始ターンで行動済かどうか
	bool firstalive;	// 評価開始ターンで生存しているかどうか

	void initSamuraiState(int a, int w);
};

struct EneRecord {
	int turn;
	BitBoard eneplacebb[3];				// 存在可能な場所
	BitBoard eneplacebbbak[3];			// 存在可能な場所のバックアップ
	BitBoard eneplacelimitbb[2];		// 存在可能な場所の制限
	BitBoard mustoccupybb;				// 占領しなければならない場所
	BitBoard mustoccupybythisturnbb;	// このターンまでに占領していなければならない場所
	BitBoard mustoccupyinthisturnbb;	// このターンに占領していなければならない場所
	BitBoard mayoccupybb;				// 敵が占領した可能性がある場所
	BitBoard mayoccupybbbak;
	BitBoard occupiedbb;				// 敵が必ず占領した場所
	BitBoard occupiedbbbak;
	bool	 recovery;					// 治療中かどうか
	Pos	     mustplacepos;				// 必ずそこに存在していなければならない場所（なければPos(-1, -1))
};

// cygwinだと vector<EneRecord> を使うと中の BitBoard の align がうまくいかないようで、SIMD命令を使うと segmentation falut になるみたいなので、こちらを使う
struct EneRecordArray {
	struct reverseiterator {
		reverseiterator(EneRecord *erecord) : e(erecord) {}
		reverseiterator *operator++ () {
			this->e--;
			return this;
		}
		reverseiterator *operator-- () {
			this->e++;
			return this;
		}
		EneRecord* operator->() {
			return e;
		}
		bool operator==(const reverseiterator& r) const {
			return this->e == r.e;
		}
		bool operator!=(const reverseiterator& r) const {
			return this->e != r.e;
		}
		EneRecord *e;
	};
	EneRecordArray() : sz(0) {}

	void push_back(const EneRecord& e) {
		if (sz < maxsize) {
			erecord[sz + 1] = e;
			sz++;
		}
		else {
			cerr << "error!!! push_back size over." << endl;
		}
	}
	EneRecord& front() {
		if (sz == 0) {
			cerr << "error!!! no front data." << endl;
		}
		return erecord[1];
	}
	EneRecord& back() {
		if (sz == 0) {
			cerr << "error !!! no back data." << endl;
		}
		return erecord[sz];
	}
	EneRecord *begin() {
		return &erecord[1];
	}
	EneRecord *end() {
		return &erecord[sz + 1];
	}
	reverseiterator rbegin() {
		return reverseiterator(&erecord[sz]);
	}
	reverseiterator rend() {
		return reverseiterator(&erecord[0]);
	}
	void clear() {
		sz = 0;
	}
	int size() const {
		return sz;
	}
	static const int maxsize = 48;
	EneRecord erecord[maxsize + 2];
	int sz;
};

const int APPEAR = 0;
const int HIDDEN = 1;
const int ALL = 2;
const int ALLY = 0;
const int ENEMY = 1;

struct GameInfo {
	void readTurnInfo();
	int attack(const int weapon, const int direction, const bool updaterecords);
	double calcbestaction();
	double	calchyouka();
	void move(const int weapon, const Pos& from, const bool fromhidden, const Pos& to, const bool tohidden);
	void calcprevactiontype(const int type, const int weapon, const int changednuminenemysight, const Pos prevpos, const bool prevhidden);
	void startsimulate(const int type, const int weapon, const int attackdir, Action& act, const int maxturn, double& maxhyouka);
	void simulateandcheckhyouka(Action& act, const int maxturn, double& maxhyouka, Action& bestaction);
	double simulate(const int maxturn, double alpha, double beta);
	void kill(const int pl, const int weapon);
	bool checkcandestroy(const int t, const int attacker, const int attackweapon, const int defenceweapon, BitBoard& attackplacebb, BitBoard& attackmoveplacebb, BitBoard& attackbeforeplaceupbb, BitBoard& attackbeforeplaceunderbb, IntBoard &occnumib, const int period);
	//bool checkcandestroy2(const int t, const int attacker, const int attackweapon, const int defenceweaponbit, BitBoard& attackplacebb);
	void calccanmoveandattackbb(BitBoard upbb, BitBoard downbb, const int t, const int pl, const int weapon);
	void nextturn();
	void calcenesikaibb();
	void calccanmoveandattackall();
	void calccanmoveandattack2(const int pl, const int weapon);
	void analyze(GameInfo& previnfo);
//	bool calceneplace(const int weapon, BitBoard& eneplaceup, BitBoard& eneplaceunder, BitBoard mayoccupybb, BitBoard occupiedbb, const vector<EneRecord>::iterator itstart, const vector<EneRecord>::iterator itend);
	bool calceneplace(const int weapon, BitBoard& eneplaceup, BitBoard& eneplaceunder, BitBoard mayoccupybb, BitBoard occupiedbb, EneRecord *itstart, EneRecord *itend);
	void recalculaterecords(const bool updatelimit);

	uint8_t	turn;						// 現在ターン	
	SamuraiState	sstates[2][3];		// 各侍の状態
	BitBoard appearplbb;				// 隠れていないプレーヤーの位置を表す BitBoard
	BitBoard appearallybb;				// 隠れていない味方のプレーヤーの位置を表す BitBoard
	BitBoard appearenemybb;				// 隠れていない敵のプレーヤーの位置を表す BitBoard
	BitBoard mayoccupybb[2];			// それぞれの陣営が占領しているかもしれない場所
	BitBoard enesikaibb;				// 敵の視界内の可能性がある場所
	BitBoard placebb[3][2][3];			// プレーヤーの存在可能な場所を表す BitBoard。一つ目のインデックスは 0:顕現状態、1:隠蔽状態、2:0と1のor、二つ目のインデックスは陣営、三つ目のインデックスは武器の番号を表す
	BitBoard canattackplacebb[2][2][3];	// それぞれのプレーヤーが最初のインデックスが表す行動回数後に、攻撃を行うことができる場所
	BitBoard canattackbb[2][2][3];		// それぞれのプレーヤーが最初のインデックスが表す行動回数後に、占領可能な場所 // todo: 名前がかぶっているので変える！
	BitBoard canmovebb[2][3][2][3];		// それぞれのプレーヤーが移動を行うことができる場所。一つ目のインデックスは1回
	BitBoard visibilitybb;				// 味方の視界の Bitboard
	BitBoard occbb;						// 占領した場所
	BitBoard eneoccbb;					// 敵が占領したかもしれない場所
	int		occupynuminsight[2];		// 視界内の占領数（0:味方の占領数、1:敵の占領数で、最初の行動を行った直後のもの）
	int		maxoccnumbynextperiod;		// 次のピリオドも含めた味方の最大占領数
	int		prevactiontype[3];			// それぞれのプレーヤーが直近に行った行動の種類。種類は定数 PREVACTION_xxx で定義済
	int		preveneplacepopcnt[3];		// 敵が移動する前の存在可能な場所の数
	int8_t	actionnum[2][3];			// それぞれのプレーヤーが、シミュレーション中に行動した回数（攻撃して殺すと0にリセットされる）
	bool	actionflag[2][3];			// それぞれのプレーヤーがシミュレーション中に行動したかどうか（上記と違い、リセットされない）
	bool	mayactionflag[3];			// 味方がシミュレーション中にそれまでに自由に行動可能であったかどうか（攻撃した場合は自由に行動できない）
	double	curehyoukamul[2][3];		// 治療ターンに対する評価値の倍率。シミュレーションで敵に殺されたと判断した場合、殺される可能性が低い場合はこの値を小さくする
	Action	bestaction;					// 最善手
	bool	earlybestaction;			// 初期ターンの最善手候補かどうか
	int		startturn;					// 最善手の計算を開始した最初のターン
	bool	ispass;						// 最初の行動がパス（治療中のプレーヤーの行動）かどうか
	bool	ishidden;					// 最初の行動後に隠蔽状態かどうか
	bool	isdetected;					// 最初の行動後に敵に場所が察知されているかどうか
	double  killpercent;				// 最初の行動で、敵を殺した確率の合計（確実に殺した場合は、加算しない）
#ifdef RECORDACTION
	// デバッグ時に、行動を記録する場合に使う変数
	int rec_start, rec_end;			// 記録の開始、終了ターン
	int rec_pl[96];					// そのターンに行動したキャラクター。-1はパス。0～2:味方、3～5:敵
	int rec_ac[96];					// そのターンに行動したキャラクターの行動(0:移動、1～3:殺した敵の武器ID+1
#endif
};

struct Canmovebits {
	uint64_t data[5];
};

void calccanarriveplace(BitBoard canmoveup, BitBoard canmoveunder, Pos pos, BitBoard& canarriveup, BitBoard& canarriveunder, int num = 5);
void calccanarriveplaceapproximate(BitBoard canmoveup, BitBoard canmoveunder, Pos pos, BitBoard& canarriveup, BitBoard& canarriveunder, int num = 5);
void calccanarriveplacewithoutusingtable(BitBoard canmoveup, BitBoard canmoveunder, Pos pos, BitBoard& canarriveup, BitBoard& canarriveunder, int num = 5);
void calccanmoveaction(BitBoard canmoveup, BitBoard canmoveunder, Pos pos, Canmovebits& movebits, int num = 5);
void dumpbitboardhorizontal(vector<string>& caption, vector<BitBoard>& bb, int type = 0);

// occupybb のインデックス
const int allyindex = 6;
const int enemyindex = 7;
const int neutralindex = 8;
const int unknownindex = 9;

// 様々な記録
struct Records {
	void init(const uint8_t porder);
	void addnewenerecord(const int turn, const int weapon);

	uint8_t		turn;								// 現在のターン
	//vector<EneRecord>	enerecord[3];				// 敵の行動履歴
	EneRecordArray enerecord[3];					// 敵の行動履歴
	BitBoard	occupybb[96][10];					// 各ターンの占領状況（0～5（プレーヤー）、6：味方、7：敵、8：未占領、9：視界外　それぞれの占領状況）
	BitBoard	appearplbb[96];						// 各ターンの隠れていないプレーヤーの位置を表すBitBoard
	BitBoard	appearallybb[96];					// 各ターンの隠れていない味方の位置を表すBitBoard
	BitBoard	appearenemybb[96];					// 各ターンの隠れていない敵の位置を表すBitBoard
	BitBoard	enemayoccupybb[96][7];				// 0 ～ 2: 敵のID、3～5: それぞれ 1 と 2, 0 と 2, 1 と 2 の or 6: すべての or :各ターンのそれぞれの敵が占領しているかもしれない場所を表す BitBoard
	BitBoard	eneplacebb[96][3][3];				// 敵の存在可能な場所
	BitBoard	visibilitybb[96];					// 各ターンの視界
	int8_t		allyattackplnum[96];				// そのターンに攻撃した味方のID（してなければ-1）
	BitBoard	allyattackbb[96];					// 味方がそのターンに占領した場所
	IntBoard	lastoccupyturn[96];					// 各マスについて、そのマスをどこが占領していたかについてわかっている最も最近のターン数
	IntBoard	lastoccupyplnum[96];				// 上記で、その時に誰が占領していたかのプレーヤー番号（未占領は6)
	IntBoard	board[96];
} records;

static const uint64_t FNV_OFFSET_BASIS_64 = 14695981039346656037U;
static const uint64_t FNV_PRIME_64 = 1099511628211LLU;
inline uint64_t fnv_1_hash_64(const uint8_t *bytes, size_t length)
{
	uint64_t hash;
	size_t i;

	hash = FNV_OFFSET_BASIS_64;
	for (i = 0; i < length; ++i) {
		hash = (FNV_PRIME_64 * hash) ^ (bytes[i]);
	}

	return hash;
}

struct HashData1 {
	HashData1(const BitBoard& _b1, const BitBoard& _b2, const BitBoard& _b3, const BitBoard& _b4, const int _turn) : b1(_b1), b2(_b2), b3(_b3), b4(_b4), turn(_turn) {}
	BitBoard b1, b2, b3, b4;
	int turn;
	const static int size = sizeof(BitBoard) * 4 + sizeof(int);
	size_t calchash() const {
		return fnv_1_hash_64(reinterpret_cast<const uint8_t *>(this), size);
	}
};

struct HashData2 {
	HashData2(const BitBoard& _b1, const BitBoard& _b2, const BitBoard& _b3, const BitBoard& _b4, const BitBoard& _b5, const BitBoard& _b6, const BitBoard& _b7, const int _w) : b1(_b1), b2(_b2), b3(_b3), b4(_b4), b5(_b5), b6(_b6), b7(_b7), w(_w) {}
	BitBoard b1, b2, b3, b4, b5, b6, b7;
	int w;
	const static int size = sizeof(BitBoard) * 7 + sizeof(int);
	size_t calchash() const {
		return fnv_1_hash_64(reinterpret_cast<const uint8_t *>(this), size);
	}
};

struct HashData3 {
	HashData3(const BitBoard& _b1, const BitBoard& _b2, const BitBoard& _b3, const BitBoard& _b4, const int& _p, const int& _w) : b1(_b1), b2(_b2), b3(_b3), b4(_b4), p(_p), w(_w) {}
	BitBoard b1, b2, b3, b4;
	int p, w;
	const static int size = sizeof(BitBoard) * 4 + sizeof(int) * 2;
	size_t calchash() const {
		return fnv_1_hash_64(reinterpret_cast<const uint8_t *>(this), size);
	}
};

struct HashData4 {
	HashData4(const BitBoard& _b1, const int period, const int weapon) : b1(_b1), p(period), w(weapon) {}
	BitBoard b1;
	int p, w;
	const static int size = sizeof(BitBoard) * 1 + sizeof(int) * 2;
	size_t calchash() const {
		return fnv_1_hash_64(reinterpret_cast<const uint8_t *>(this), size);
	}
};

#ifdef DEBUG
void benchmark(GameInfo& info);
#endif
Timer benchmarktimer;