
// samurai2016.cpp : コンソール アプリケーションのエントリ ポイントを定義します。
//

// todo
//      味方が確実に占領している場所の数を考慮に入れる
//ver1: 全件探索（depth3あたりでタイムオーバーする）
//ver2: 探索は未完成。敵の行動分析未完成バージョン
//ver3: 周囲の状況によって移動できる場所および、移動行動を計算できるようにした
//ver4: 7手先まで読んで行動するようにした
//ver5: 最初の24ターンの行動を固定。隠れている場合などに死亡した場合の評価値を変えた
//ver6: 占領状態が変化したことを元に相手の位置を推測するようにした
//ver7: 敵の位置の推定に時間がかかる場合があるので、反復深化で時間切れまでの深さで推定するようにした
//ver8.1: αβ法を使うようにした
#include "samurai2016.hpp"

// 乱数発生用
#ifdef USERANDOM
random_device rnd;     // 非決定的な乱数生成器を生成
#ifdef DEBUG
mt19937 mt(20170304);     //  メルセンヌ・ツイスタの32ビット版、引数は初期シード値
#else
mt19937 mt(rnd());     //  メルセンヌ・ツイスタの32ビット版、引数は初期シード値
#endif
//uniform_int_distribution<> rndhyouka(0, HYOUKA_RANDOM - 1); // 0 から HYOUKA_RANDOM 未満の整数を生成する乱数
uniform_real_distribution<> rndhyouka(0, HYOUKA_RANDOM); // 0 から HYOUKA_RANDOM 未満の実数を生成する乱数
#endif

// デバッグ時に、ファイルの中に保存された行動を読み込んで保存するための変数
#ifdef DONOTUSEAI
Action recaction[96];
#endif

// 評価値順に Action を記録するための map
#ifdef RECORDACTION
map<double, Action> actionmap;
#endif

Timer timer;

int playOrder;
int totalTurns = 96;
int64_t c1,c2,c3,c4,hc;
// analyzeの分析で時間切れになった回数
int atimeovercount = 0;
// 思考で時間切れになった回数
int ttimeovercount = 0;

// 序盤の最善手の候補
Action earlyturnbestaction[3];

unordered_map <size_t, bool> analyzemap;
unordered_map<size_t, BitBoard> enesikaimap;
unordered_map<size_t, BitBoard[4]> attackplacemap;
unordered_map<size_t, BitBoard[4]> moveandattackbbmap;
unordered_map<size_t, IntBoard> occnumibmap;
unordered_map<size_t, int> checkplacenummap;

// あらかじめ様々なデータを計算しておくことで様々な計算の高速化を図る。下記はそれらのテーブル
// ここで定義されている変数は、init で計算して初期化して使う
BitBoard basebb[2][3];				// 自分の本拠地を表すBitBoard
BitBoard allbasebb;					// 全員の本拠地を表すBitBoard
BitBoard cannotenterbb[2][3];		// 自分が移動不可能な場所を表すBitBoard（=他人の本拠地）d
BitBoard attackbb[3][5][256];		// 1つ目のインデックス：武器の種類、2つ目：方向（4は全方向に攻撃した場合）、3つ目：座標。占領した場所を表す BitBoard
BitBoard canseebb[256];				// 各マスの視界を表すの BitBoard
BitBoard canattackmovebb[256];		// 各マスから、攻撃した場合に移動可能な場所を表す BitBoard
BitBoard cannoattackmovebb[256];	// 各マスから、移動撃した場合に移動可能な場所を表す BitBoard

// 検証用：移動可能な場所を現在存在する場所からマンハッタン距離が1及び3以下の場所とした場合のテーブル。本選では使用していない
BitBoard withindist1bb[256], withindist3bb[256];

const int PERIOD_MAX = 16;
BitBoard periodplacebb[PERIOD_MAX][2][3];		// 各ピリオドの、記録から推測される敵の存在可能範囲
IntBoard periodplaceintb[PERIOD_MAX][2][3];	// 各ピリオドの、記録からの敵の存在回数
int periodplacemaxnum = 0;

// すべてのビットが 0 の BitBoard
const BitBoard ZERO_BB = BitBoard(0);
// 不明な場所
const Pos UNKNOWN_POS(-1, -1);
// 原点
const Pos ZERO_POS(0, 0);

// ここから下のテーブルに関する詳しい説明は init() の中にコメントがあるのでそちらを参照すること。
BitBoard obstaclemaskbb[2][5][256];			// 二つ目のインデックスが示す範囲の中で到達可能な場所を計算するために必要な障害物の場所を表す BitBoard
											// 一つ目のインデックスは 0:移動開始地点を含まない、1:含む
											// 二つ目のインデックスは、0:距離が0,1の場所、1:距離が2,3で右上の場所、2:左上の場所、3:左下の場所、4:右下の場所
											// 三つ目のインデックスは、移動開始地点。場所を表す Pos の getpos で得られる値
uint64_t obstaclepdepmask[5][256];			// 到達可能な場所を計算するために必要な場所が盤外の場合、obstaclemaskbb を使って得られたビット列に対して、盤外場所に相当するビットを補完するためのテーブル
											// 一つ目のインデックスは、obstaclemaskbbの二つ目のインデックスと同じ。二つ目のインデックスは場所
uint64_t canarrivetable[2][5][1 << 17];		// 三つ目のインデックスが表す周囲の障害物のビット列に対して、二つ目のインデックスが表す範囲内の5つの地点に関して到達可能かどうかを表すビット列
											// 一つ目のインデックスは 0:顕現状態で到達可能、1:隠蔽状態で到達可能
uint64_t canarrivepextmask[5][256];			// 到達可能な場所が盤外の場合、_pext_u64 を使って盤外の場所のビットを削除するために使うテーブル
											// 一つ目のインデックスは到達可能な場所の範囲、二つ目は場所
BitBoard canarrivebb[5][256];				// canarrivetable と canarrivepextmask を使って得られた到達可能な場所を表すビット列に対応する、移動可能な場所を表す BitBoard
											// 一つ目のインデックスは到達可能な場所の範囲、二つ目は場所
vector<Action> actiontable[5];				// 一つ目のインデックスが表す範囲への、すべての移動行動を列挙したテーブル
uint64_t actionsindextable[5][1 << 17];		// 一つ目のインデックスが表す範囲に対して、二つ目のインデックスが表す周囲の障害物があった場合、到達可能な場所への移動行動を表すビット列。ビット列のうち、2^n のビット1になっていた場合場合に、actiontable の二つ目のインデックスが n の移動行動で到達可能な場所に移動できることを表す
unordered_map<int, size_t> actionvaluetoindextable[5];	// 行動を表す数値(Action の getactionvalue()で得られる値）から、その値の行動に対応する actiontable の二つ目のインデックス値を逆引きするテーブル

M256 zero256;			// すべてのビットが 0 の __m256i のデータ
Pos dist1pos[5];			// 距離が１の方向（0:南、1:東、2:北、3:西

int epopcnt[3][3][96];


// サンプルのコードをそのまま流用
char getChar() {
	return cin.get();
}

// サンプルのコードをそのまま流用
int getInt() {
	char c;
	do {
		c = getChar();
	} while (isspace(c));
	int v = 0;
	bool negate = (c == '-');
	if (negate) c = getChar();
	do {
		v = 10 * v + c - '0';
		c = getChar();
	} while (!isspace(c));
	if (negate) v = -v;
	return v;
}

void SamuraiState::initSamuraiState(int a, int w) {
	int x = getInt();
	int y = getInt();
	pos.set(x, y);
	done = getInt() ? true : false;
	hidden = (getInt() == 0) ? false : true;
	recovery = getInt();
}

void GameInfo::readTurnInfo() {
	turn = getInt();
	if (turn < 0) exit(0);
	appearplbb.clear();
	appearallybb.clear();
	appearenemybb.clear();
	for (int a = 0; a != 2; a++) {
		for (int w = 0; w != 3; w++) {
			SamuraiState &ss = sstates[a][w];
			ss.initSamuraiState(a, w);
			if (!ss.hidden) {
				appearplbb.set(ss.pos);
				if (a == ALLY) {
					appearallybb.set(ss.pos);
				}
				else {
					appearenemybb.set(ss.pos);
				}
			}
		}
	}
	for (int y = 0; y != height; y++) {
		for (int x = 0; x != width; x++) {
			int f = getInt();
			records.board[turn].set(Pos(x, y), f);
			records.occupybb[turn][f].set(x, y);
			if (f < 3) {
				records.occupybb[turn][allyindex].set(x, y);
			}
			else if (f < 6) {
				records.occupybb[turn][enemyindex].set(x, y);
			}
		}
		// 盤外の部分には視界外をセットしておく（そうしないと後の for (auto pos : Pos()) の処理で盤外の場所を取ってきた時にエラーになる） 
		records.board[turn].set(Pos(15, y), 9);
	}
}

void rotate(int direction, int x0, int y0, int& x, int& y) {
	switch (direction) {
	case 0: x = x0; y = y0; break;
	case 1: x = y0; y = -x0; break;
	case 2: x = -x0; y = -y0; break;
	case 3: x = -y0; y = x0; break;
	}
}

static const int osize[3] = { 4, 5, 7 };

static const int ox[3][7] = {
	{ 0, 0, 0, 0 },
	{ 0, 0, 1, 1, 2 },
	{ -1,-1,-1, 0, 1, 1, 1 } };

static const int oy[3][7] = {
	{ 1, 2, 3, 4 },
	{ 1, 2, 0, 1, 0 },
	{ -1, 0, 1, 1, 1, 0,-1 } };

ostream& operator<<(ostream& os, const BitBoard& bb)
{	os << " 0123456789ABCDE" << endl;
	for (int y = 0; y < height; y++) {
		if (y < 10) {
			cerr << y;
		}
		else {
			cerr << static_cast<char>('A' + y - 10);
		}
		for (int x = 0; x < width; x++) {
			if (bb.isset(x, y)) {
				os << "o";
			}
			else {
				os << ".";
			}
		}
		os << endl;
	}
	return os;
}

ostream& operator<<(ostream& os, const Pos& p) {
	os << "(" << p.getx() << "," << p.gety() << ")";
	return os;
}

inline BitBoard BitBoard::begin() const {
	return *this;
}
inline BitBoard BitBoard::end() const {
	return ZERO_BB;
}

// p 番目のプレーヤーが、direction の方向に攻撃を行う
// 敵の視界内の可能性のある場所で、占領状態が変化した場所の数（敵に見られた可能性のあるマスの数）を返す
inline int GameInfo::attack(const int weapon, const int direction, const bool updaterecords = false) {
	BitBoard& attbb = attackbb[weapon][direction][sstates[ALLY][weapon].pos.getpos()];
	mayoccupybb[ALLY] |= attbb;
	mayoccupybb[ENEMY] = BitBoard::andnot(attbb, mayoccupybb[ENEMY]);
	// 占領状態が変化した場所のうち、敵の視界内のマスの数
	int changednuminenemysight = (BitBoard::andnot(records.occupybb[turn][weapon], attbb) & enesikaibb).popcnt();
	// 視界内の占領数を計算しなおす
	occupynuminsight[ALLY] = (records.occupybb[turn][allyindex] | attbb).popcnt();
	occupynuminsight[ENEMY] = BitBoard::andnot(attbb, records.occupybb[turn][enemyindex]).popcnt();
	// 記録を更新する
	if (updaterecords) {
		records.allyattackplnum[turn + 1] = weapon;
		records.allyattackbb[turn + 1] = attbb;
		for (int i = 0; i < 10; i++) {
			if (i == weapon || i == allyindex) {
				records.occupybb[turn + 1][i] |= attbb;
				}
			else {
				records.occupybb[turn + 1][i] = BitBoard::andnot(attbb, records.occupybb[turn + 1][i]);
			}
		}
	}
	// 敵の死亡チェック
	for (int w = 0; w < 3; w++) {
		// 敵を確実に殺した場合
		if (placebb[ALL][ENEMY][w].isincluded(attbb)) {
			kill(ENEMY, w);
		}
		// 敵を殺した可能性がある場合
		else {
			killpercent += static_cast<double>((attbb & placebb[ALL][ENEMY][w]).popcnt()) / static_cast<double>(placebb[ALL][ENEMY][w].popcnt());
		}
	}
	return changednuminenemysight;
}

double GameInfo::calchyouka() {
	hc++;
#ifdef RECORDACTION
	if (DEBUGRECCONDITION) {
		for (int i = rec_start + 1; i <= rec_end; i++) {
			if (rec_pl[i] == -1) {
				cerr << "Ps";
			}
			else if (rec_pl[i] < 3) {
				cerr << "P" << rec_pl[i];
			}
			else {
				cerr << "E" << rec_pl[i] - 3;
			}
			cerr << " ";
			if (rec_ac[i] == 0) {
				cerr << "Mo   ";
			}
			else if (rec_ac[i] < 0) {
				cerr << "--   ";
			}
			else {
				if (rec_pl[i] >= 3) {
					cerr << "K" << rec_ac[i] - 1 << " " << setw(2) << floor(curehyoukamul[ALLY][rec_ac[i] - 1] * 10) / 10.0;
				}
				else {
					cerr << "K" << rec_ac[i] - 1 << " " << setw(2) << floor(curehyoukamul[ENEMY][rec_ac[i] - 1] * 10) / 10.0;
				}
			}
			cerr << " ";
		}
		cerr << endl;
	}

#endif
	double hyouka = 0;
	// 占領した場所の評価
	double occupyhyouka = occupynuminsight[ALLY] * HYOUKA_OCCUPY + occupynuminsight[ENEMY] * HYOUKA_ENEOCCUPY;// (occupybb[allyindex].popcnt() - occupybb[enemyindex].popcnt()) * HYOUKA_OCCUPY;
	// 計算開始ターンが最後のピリオドより前の場合
	// todo もっといろいろできるはず！
	if (startturn < 90) {
		// 味方の視界（分析の最初に行動した味方以外は現在の視界で計算する）
		BitBoard sightbb = canseebb[sstates[ALLY][0].pos.getpos()] | canseebb[sstates[ALLY][1].pos.getpos()] | canseebb[sstates[ALLY][2].pos.getpos()];
		// 付近の味方が占領していない場所による評価
		double nearnotallyoccupyhyouka = BitBoard::andnot(mayoccupybb[ALLY], sightbb).popcnt() * HYOUKA_NOTALLYOCCUPY_INSIGHT;
		// 付近の敵が占領している場所による評価
		nearnotallyoccupyhyouka += (mayoccupybb[ENEMY] & sightbb).popcnt() * HYOUKA_ENEMYOCCUPY_INSIGHT;
//		nearnotallyoccupyhyouka += (records.occupybb[startturn][enemyindex] & sightbb).popcnt() * HYOUKA_ENEMYOCCUPY_INSIGHT;
		// 敵が占領している可能性のある場所と敵が存在している可能性のある場所に限定する
		sightbb &= placebb[ALL][ENEMY][0] | placebb[ALL][ENEMY][1] | placebb[ALL][ENEMY][2] | mayoccupybb[ENEMY];
		// 視界の評価
		double sighthyouka = sightbb.popcnt() * HYOUKA_SIGHT;
//		// 本拠地からの距離による評価（離れてるほうが良い）
//		double distfrombasehyouka = (homepos[ALLY][0].dist(sstates[ALLY][0].pos) + homepos[ALLY][1].dist(sstates[ALLY][1].pos) + homepos[ALLY][2].dist(sstates[ALLY][2].pos)) * HYOUKA_DISTFROMBASE;
//		// 角の本拠地のからの距離による評価（離れてるほうが良い）
//		distfrombasehyouka += (homepos[ALLY][0].dist(sstates[ALLY][0].pos) + homepos[ALLY][1].dist(sstates[ALLY][0].pos) + homepos[ALLY][2].dist(sstates[ALLY][0].pos)) * HYOUKA_DISTFROMCORNER;
		// 目標地点からの距離による評価（近いほうが良い）
		double distfromdestinationhyouka = (targetpos[playOrder][0].dist(sstates[ALLY][0].pos) + targetpos[playOrder][1].dist(sstates[ALLY][1].pos) + targetpos[playOrder][2].dist(sstates[ALLY][2].pos)) * HYOUKA_DISTFROMTARGET;
		// 死亡していることによる評価
		double deadhyouka = 0;
		// 行動していないことによる評価
		double nomovehyouka = 0;
		for (int weapon = 0; weapon < 3; weapon++) {
//			deadhyouka += sstates[0][weapon].recovery * HYOUKA_RECOVERY[0][weapon] * HYOUKA_CUREMUL_NORMAL;
//			deadhyouka += sstates[1][weapon].recovery * HYOUKA_RECOVERY[1][weapon] * HYOUKA_CUREMUL_NORMAL;
			// ゲーム終了までに復帰できない場合は、治療ターンを最大治療ターン数として計算する
			int latter = (startturn < HYOUKA_LATTER_TURN) ? 0 : 1;
			if (sstates[ALLY][weapon].recovery > 0) {
				deadhyouka += ((sstates[ALLY][weapon].recovery + turn < totalTurns) ? sstates[ALLY][weapon].recovery : recoveryTurns) * HYOUKA_RECOVERY[latter][ALLY][weapon] * HYOUKA_CUREMUL_NORMAL;
			}
			if (sstates[ENEMY][weapon].recovery > 0) {
				deadhyouka += ((sstates[1][weapon].recovery + turn < totalTurns) ? sstates[ENEMY][weapon].recovery : recoveryTurns) * HYOUKA_RECOVERY[latter][ENEMY][weapon] * HYOUKA_CUREMUL_NORMAL;
			}
			// 評価開始ターンに生存しており、行動していなければ侍の種類に応じて評価値を加算する
			if (startturn >= HYOUKA_NOMOVETURN) {
				nomovehyouka += (sstates[ALLY][weapon].firstdone == 0 && sstates[ALLY][weapon].firstalive == true) ? HYOUKA_NOMOVE[weapon] : 0;
			}
		}
		// パスの行動による評価
		double passhyouka = (ispass) ? HYOUKA_PASS : 0;
		// 見つかっていないことによる評価
		double notdetecthyouka = (isdetected) ? 0 : HYOUKA_NOTDETECTED;
		// 顕現状態による評価
		double appearhyouka = ishidden ? 0 : HYOUKA_APPEARED;
		// 敵を殺した可能性がある場合の評価
		double maykillhyouka = killpercent * HYOUKA_MAYKILL;
		// 味方が近くにいることの評価
		double nearallyhyouka = 0;
		for (int w1 = 0; w1 < 3; w1++) {
			for (int w2 = w1 + 1; w2 < 3; w2++) {
				int dist = sstates[ALLY][w1].pos.dist(sstates[ALLY][w2].pos);
				if (dist <= HYOUKA_NEARALLY_DISTMAX) {
					nearallyhyouka += HYOUKA_NEARALLY + dist * HYOUKA_NEARALLY_PERDIST;
				}
			}
		}
		
		// 乱数による評価
#ifdef USERANDOM
		double randomhyouka = rndhyouka(mt);
#else
		double randomhyouka = 0;
#endif
		// 序盤の優先される行動の場合の評価。先手はさらに加算する
		double earlybestactionhyouka = earlybestaction ? HYOUKA_EARLY_BESTACTION + ((playOrder == 0) ? 200 : 0) : 0;
		// 次のピリオドも含めた最大占領数による評価（最後のひとつ前のピリオドのみ計算してある）
		double maxoccnumbynextperiodhyouka = maxoccnumbynextperiod * HYOUKA_OCCBYNEXTPERIOD;
		hyouka = occupyhyouka + sighthyouka + nearnotallyoccupyhyouka + distfromdestinationhyouka + deadhyouka + nomovehyouka + earlybestactionhyouka + passhyouka + appearhyouka + randomhyouka + notdetecthyouka + maykillhyouka + nearallyhyouka + maxoccnumbynextperiodhyouka;
#ifdef RECORDACTION
		if (DEBUGRECCONDITION) {
			cerr << "hyouka = " << hyouka << " occupy = " << occupyhyouka << " sight = " << sighthyouka << " notallyocc " << nearnotallyoccupyhyouka << " distfromdestination " << distfromdestinationhyouka << " dead = " << deadhyouka << " nomove " << nomovehyouka << " earlybestaction " << earlybestactionhyouka << " pass " << passhyouka << " appear " << appearhyouka << " random " << randomhyouka << " notdetected " << notdetecthyouka << " maykill " << maykillhyouka << " nearally " << nearallyhyouka << " maxocc " << maxoccnumbynextperiodhyouka;
			cerr << " " << (int)sstates[ALLY][0].recovery << "," << (int)sstates[ALLY][1].recovery << "," << (int)sstates[ALLY][2].recovery << "," << (int)sstates[ENEMY][0].recovery << "," << (int)sstates[ENEMY][1].recovery << "," << (int)sstates[ENEMY][2].recovery << endl;
		}
#endif
		return hyouka;
	}
	// 分析開始ターンが最後のピリオドの場合は占領の評価と死亡の評価と行動していないことによる評価のみ行う
	else {
		double deadhyouka = 0;
//		double nomovehyouka = 0;
		double mustoccupyhyouka = BitBoard::andnot(eneoccbb, occbb).popcnt() * HYOUKA_OCCUPY;
		for (int weapon = 0; weapon < 3; weapon++) {
			// 分析開始時に行動済のキャラクターはもう手番は回ってこないので死亡していても評価に入れない
			deadhyouka += recoveryTurns * HYOUKA_RECOVERY[1][ALLY][weapon] * HYOUKA_CUREMUL_NORMAL * (sstates[ALLY][weapon].recovery == 0 || sstates[ALLY][weapon].firstdone ? 0 : 1);
			deadhyouka += recoveryTurns * HYOUKA_RECOVERY[1][ENEMY][weapon] * HYOUKA_CUREMUL_NORMAL * (sstates[ENEMY][weapon].recovery == 0 || sstates[ENEMY][weapon].firstdone ? 0 : 1);
			// 評価開始ターンに生存しており、行動していなければ侍の種類に応じて評価値を加算する
			//nomovehyouka += (sstates[ALLY][weapon].done == 0 && sstates[ALLY][weapon].firstalive == true) ? HYOUKA_NOMOVE[weapon] : 0;
		}
		// パスの行動による評価
		double passhyouka = (ispass) ? HYOUKA_PASS : 0;
		double noocchyouka = occbb.iszero() ? HYOUKA_NOOCCUPY : 0;
		hyouka = occupyhyouka + deadhyouka + passhyouka + mustoccupyhyouka + noocchyouka;
#ifdef RECORDACTION
		if (DEBUGRECCONDITION) {
			cerr << "hyouka = " << hyouka << " occupy = " << occupyhyouka << " dead = " << deadhyouka << " pass " << passhyouka << " mustoccupy " << mustoccupyhyouka << " noocc " << noocchyouka << endl;
		}
#endif
		return hyouka;
	}
}

// 計算した行動の数を数えるための変数
int checkactioncount = 0;
// 最善手を計算する
double GameInfo::calcbestaction() {
	checkactioncount = 0;
	// 現在のターンから最大 7 ターン後まで計算する
	int maxturn = turn + 7;
	// ただし、最終ターンは超えない
	if (maxturn >= totalTurns) {
		maxturn = totalTurns - 1;
	}
	// デバッグ表示
#ifdef DEBUGMSG
	cerr << "Turn " << static_cast<int>(turn) << " start calc bestaction " << (int)turn << "," << maxturn << endl;
	cerr << "place " << sstates[ALLY][0].pos << sstates[ALLY][1].pos << sstates[ALLY][2].pos << endl;
#endif
	// 計算の開始ターンを記録しておく
	startturn = turn;

	// 視界内の占領数を計算する
	occupynuminsight[ALLY] = records.occupybb[turn][allyindex].popcnt();
	occupynuminsight[ENEMY] = records.occupybb[turn][enemyindex].popcnt();
	// 最初の行動をパスではないものとする
	ispass = false;
#ifdef RECORDACTION
	// 評価値の順に行動を記録するための map
	actionmap.clear();
	// デバッグ時に分析中の行動を記録する場合の処理。
	// 開始ターンと終了ターンを記録しておく
	rec_start = turn;
	rec_end = maxturn;
#endif

	// 分析が始まる前の各敵味方が行動済かどうかを記録しておく
	for (int w = 0; w < 3; w++) {
		sstates[ALLY][w].firstdone = sstates[ALLY][w].done;
		sstates[ALLY][w].firstalive = (sstates[ALLY][w].recovery == 0) ? true : false;
		sstates[ENEMY][w].firstdone = sstates[ENEMY][w].done;
		sstates[ENEMY][w].firstalive = (sstates[ENEMY][w].recovery == 0) ? true : false;
	}

	// みつかった評価値の最大値の初期化
	double maxhyouka = HYOUKA_MIN;
	// 最善手の初期化（ID 0 が何もしない行動をセットしておく）
	bestaction.setaction(0, ZERO_POS, false);
	// 最善手を計算中に、それぞれのプレーヤーが行動した回数をリセット
	for (int pl = 0; pl < 2; pl++) {
		for (int weapon = 0; weapon < 3; weapon++) {
			actionnum[pl][weapon] = 0;
			actionflag[pl][weapon] = false;
		}
	}
	// 治療中ターンに対する評価の倍率を初期化
	// 味方が行動可能であったかどうかを初期化
	for (int w = 0; w < 3; w++) {
		curehyoukamul[ALLY][w] = HYOUKA_CUREMUL_NORMAL;
		curehyoukamul[ENEMY][w] = HYOUKA_CUREMUL_NORMAL;
		mayactionflag[w] = false;
	}

		// 行動可能な味方の各キャラクターのとりうる行動を列挙する
	for (int w = 0; w < 3; w++) {
		// 時間切れの場合は処理を中断する
		if (timer.gettime() > timelimit) {
			cerr << "time out weapon = " << w << endl;
			return maxhyouka;
		}
		// キャラクターの状態
		SamuraiState& ss = sstates[ALLY][w];
		// キャラクターの位置
		Pos spos = ss.pos;
		// 行動済または、治療中の場合は飛ばす
		if (ss.done || ss.recovery > 0) {
			continue;
		}
		// 行動を記録する変数
		Action action;

#ifdef RECORDACTION
		if (DEBUGRECCONDITION) {
			cerr << "プレーヤー" << w << "の行動" << endl;
		}
#endif

		//　可能な行動を計算する
		BitBoard canmoveup, canmoveunder;
		canmoveup = ~(records.appearplbb[turn] | cannotenterbb[ALLY][w]);
		canmoveunder = BitBoard::andnot(cannotenterbb[ALLY][w], records.occupybb[turn][allyindex]);
		Canmovebits mbits;
		if (!ss.hidden) {
			calccanmoveaction(canmoveup, canmoveunder, ss.pos, mbits);
		}
		else {
			calccanmoveaction(canmoveunder, canmoveup, ss.pos, mbits);
		}

		// 今回の行動で占領した場所をクリア
		occbb.clear();
		// 敵が占領したかもしれない場所をクリア
		eneoccbb.clear();

		// 移動のみの行動の計算
		for (int i = 0; i < 5; i++) {
			for (size_t j = 0; j < actiontable[i].size(); j++) {
				if (timer.gettime() > timelimit) {
					cerr << "time out no attack. weapon = " << w << " i = " << i << " j = " << j << endl;
					return maxhyouka;
				}
				if (mbits.data[i] & (static_cast<uint64_t>(1) << j)) {
					// 行動の設定
					action = actiontable[i][j];
					action.pid = w;
					startsimulate(0, w, 0, action, maxturn, maxhyouka);
				}
			}
		}
		// 移動して攻撃する行動の計算
		// 移動距離が 0,1 の行動は mbits.data[0] に計算済
		for (size_t j = 0; j < actiontable[0].size(); j++) {
			// 右、隠蔽、上、左 のような移動距離が1の移動は除く。これらはactionnum が必ず 3 以上になる
			if (actiontable[0][j].actionnum > 2) {
				continue;
			}
			if (mbits.data[0] & (static_cast<uint64_t>(1) << j)) {
				// 移動しない行動は除く。隠蔽状態は除く
				bool hidden = ss.hidden ^ actiontable[0][j].changed;
				if (actiontable[0][j].dest != ZERO_POS && !hidden) {
					// そこから全方位に攻撃する
					for (int dir = 0; dir < 4; dir++) {
						if (timer.gettime() > timelimit) {
							cerr << "time out move attack. weapon = " << w << " j = " << j << " dir = " << dir << endl;
							return maxhyouka;
						}
						// 行動の設定
						action = actiontable[0][j];
						action.pid = w;
						// 行動の最後に攻撃を加える
						action.push_back(dir + 1);
						// 攻撃後の場所
						Pos attackpos = spos + action.dest;
						// 攻撃の占領範囲
						BitBoard& abb = attackbb[w][dir][attackpos.getpos()];
						// 今回占領した場所を記録する
						occbb = BitBoard::andnot(mayoccupybb[ALLY], abb);
						// 占領する場所が存在しない場合は攻撃しても無駄なので攻撃しない
						if (abb.iszero()) {
							continue;
						}
						// 占領する場所がすべて味方の占領地であれば無駄なので攻撃しない
						// ただし、敵を撃破している可能性があれば攻撃を行う
						if (abb.isincluded(records.occupybb[turn][allyindex]) && !records.eneplacebb[turn][ALL][0].isincluded(abb) && !records.eneplacebb[turn][ALL][1].isincluded(abb) && !records.eneplacebb[turn][ALL][2].isincluded(abb)) {
								continue;
						}
						startsimulate(1, w, dir, action, maxturn, maxhyouka);
					}
				}
			}
		}
		// 移動せずに攻撃する場合。この場合は、攻撃した際に、敵がいればその敵は排除される。また、攻撃して占領した場所に移動して隠れることも可能
		// 隠蔽状態で、出現できない場合は飛ばす
		if (!(ss.hidden && appearplbb.isset(ss.pos))) {
			// 攻撃してみる
			for (int dir = 0; dir < 4; dir++) {
				if (timer.gettime() > timelimit) {
					cerr << "time out attack move. weapon = " << w << " dir = " << dir << endl;
					return maxhyouka;
				}
				BitBoard& abb = attackbb[w][dir][spos.getpos()];
				// 今回占領した場所を記録する
				occbb = BitBoard::andnot(mayoccupybb[ALLY], abb);
				// 占領する場所が存在しない場合は攻撃しても無駄なので攻撃しない
				if (abb.iszero()) {
					continue;
				}
				// 占領する場所がすべて味方の占領地であれば無駄なので攻撃しない
				// 敵を撃破している可能性がないことも条件
				if (abb.isincluded(records.occupybb[turn][allyindex]) && !records.eneplacebb[turn][ALL][0].isincluded(abb) && !records.eneplacebb[turn][ALL][1].isincluded(abb) && !records.eneplacebb[turn][ALL][2].isincluded(abb)) {
					continue;
				}

				// 攻撃を考慮に入れた移動可能な場所を計算する
				// 攻撃した場所にいる敵は排除して考える
				canmoveup = ~(BitBoard::andnot(abb, records.appearenemybb[turn]) | records.appearallybb[turn] | cannotenterbb[ALLY][w]);
				// 攻撃して占領した場所も含める
				canmoveunder = BitBoard::andnot(cannotenterbb[ALLY][w], (records.occupybb[turn][allyindex] | abb));
				// 距離が0,1の場所のみ、移動可能な場所を計算する
				if (!ss.hidden) {
					calccanmoveaction(canmoveup, canmoveunder, ss.pos, mbits, 1);
				}
				else {
					calccanmoveaction(canmoveunder, canmoveup, ss.pos, mbits, 1);
				}

				for (size_t j = 0; j < actiontable[0].size(); j++) {
					if (timer.gettime() > timelimit) {
						cerr << "time out attack move. weapon = " << w << " j =" << j << " dir = " << dir << endl;
						return maxhyouka;
					}
					// 右、隠蔽、上、左 のような移動距離が1の移動は除く。これらはactionnum が必ず 3 以上になる
					if (actiontable[0][j].actionnum > 2) {
						continue;
					}
					if (mbits.data[0] & (static_cast<uint64_t>(1) << j)) {
						action = actiontable[0][j];
						action.pid = w;
						// 最初に隠蔽状態で、最初の行動が移動で、その次の行動が顕現の場合は、入れ替えてもOKなので、入れ替える
						// （0 6 9 0 と 0 9 6 0 が同時に実行できる場合は、 0 9 6 0 は省略されるので入れ替えないといけない）
						if (ss.hidden && action.actionnum >= 2 && action.actions[0] != 9 && action.actions[1] == 9) {
							action.actions[1] = action.actions[0];
							action.actions[0] = 9;
						}
						// 最初に隠蔽状態で、最初の行動が顕現でなければ最初の場所で攻撃できないので飛ばす
						if (ss.hidden && (action.actionnum == 0 || action.actions[0] != 9)) {
							continue;
						}
						// 最初に顕現状態だった場合は、最初に攻撃を行う
						if (!ss.hidden) {
							action.push_front(dir + 1);
						}
						// そうでなかった場合は、顕現の後に攻撃を行う
						else {
							action.push_second(dir + 1);
						}
						// 最初に顕現状態だった場合は、すべての移動を行える。
						// 最初に隠蔽状態だった場合は、最初の行動が顕現であり、目的地が最初の位置または、最後に顕現状態の場合のみ移動を行える
						if (!ss.hidden || (ss.hidden && action.actionnum > 0 && action.actions[0] == 9 && (action.dest == ZERO_POS || action.changed))) {
							startsimulate(2, w, dir, action, maxturn, maxhyouka);
						}
					}
				}
			}
		}
	}
	// 治療中の味方がいた場合、治療中の味方の行動を出力することで、パスすることができる。
	// 治療中の味方がこのピリオド中に復帰しない場合は、パスすることで、行動を遅らせることができるので、パスの行動もチェックする
	// このフェーズの残り行動回数
	int actionleftnum = 3 - ((turn - playOrder) % 6) / 2;
	int canactionnum = 0;
	int passplnum = -1;
	for (int w = 0; w < 3; w++) {
		// 行動済の場合はこのフェーズに行動不能
		if (sstates[ALLY][w].done) {
			continue;
		}
		// 治療中でなければこのフェーズに行動可能
		if (sstates[ALLY][w].recovery == 0) {
			canactionnum++;
		}
		// 治療中の場合、このフェーズ中に治療期間が終われば行動可能
		else if (sstates[ALLY][w].recovery <= 4 + playOrder - (turn % 6)) {
			canactionnum++;
		}
		// 治療中で行動不能なキャラをパスの候補として挙げておく
		else {
			passplnum = w;
		}
	}
	if (actionleftnum > canactionnum) {
		// 最初の行動をパスの行動とする
		ispass = true;
		assert(passplnum >= 0);
		Action action;
		// 治療中のプレーヤーの行動をセットする
		action.setaction(0, passplnum, 0, 0);
		// 今回占領した場所をクリア
		occbb.clear();
#ifdef RECORDACTION
		if (DEBUGRECCONDITION) {
			cerr << "pass :" << action << endl;
		}
#endif
		GameInfo ginfo = *this;
		ginfo.sstates[ALLY][passplnum].done = true;
		ginfo.nextturn();
		ginfo.ishidden = false;
		if (ginfo.sstates[ALLY][passplnum].hidden == false && enesikaibb.isset(ginfo.sstates[ALLY][passplnum].pos)) {
			ginfo.isdetected = true;
		}
		else {
			ginfo.isdetected = false;
		}
		ginfo.simulateandcheckhyouka(action, maxturn, maxhyouka, bestaction);
		checkactioncount++;
	}

#ifdef RECORDACTION
	if (DEBUGRECCONDITION || debughyouka) {
		int count = 1;
		cerr << "hyouka ranking." << endl;
		for (auto itr = actionmap.rbegin(); itr != actionmap.rend() && count <= 20 ; ++itr) {
			cerr << setw(2) << count << ": hyouka = " << setw(5) << (itr->first / 100000) << " " << itr->second;
			count++;
		}
	}
#endif
	return maxhyouka;
}

int attackplacecount1 = 0;
int attackplacecount2 = 0;

// attacker の陣営の attackweapon のプレーヤーが、相手の陣営の defenceweapon のプレーヤーを確実に殺せるかどうか
// 殺せる場合は、殺した際の攻撃した場所 を attackplacebb に、攻撃した後に存在可能な場所を attackmoveplacebb に格納する
// 攻撃する前の存在可能な場所を attackbeforeplacexxbb に格納する
bool GameInfo::checkcandestroy(const int t, const int attacker, const int attackweapon, const int defenceweapon, BitBoard& attackplacebb, BitBoard& attackmoveplacebb, BitBoard& attackbeforeplaceupbb, BitBoard& attackbeforeplaceunderbb, IntBoard& occnumib, const int period) {
	int defender = 1 - attacker;

	// 治療中であれば、本拠地にいるはずなので絶対に死なない
	if (sstates[defender][defenceweapon].recovery > 0) {
		return false;
	}
	// 防御側の存在可能な場所
	BitBoard& defbb = placebb[ALL][defender][defenceweapon];

	// 防御側の存在可能な場所の数が、攻撃側の一度に攻撃可能な場所の数以下でなければ、確実に殺すことはできない
	if (defbb.popcnt() > osize[attackweapon]) {
		return false;
	}
	// 防御側の存在可能な場所が、攻撃側の攻撃可能な範囲にすべて収まっていなければ、確実に殺すことはできない
	if (!defbb.isincluded(canattackbb[t][attacker][attackweapon])) {
		return false;
	}
	attackplacebb.clear();
	attackmoveplacebb.clear();
	attackbeforeplaceupbb.clear();
	attackbeforeplaceunderbb.clear();
	occnumib.clear(0);
	bool candestroy = false;
	// 攻撃可能な場所から攻撃をし、防御側の存在可能な場所をすべて占領していれば殺せる
//	HashData2 h2(canattackplacebb[t][attacker][attackweapon], defbb, attackweapon);
	HashData2 h2(canattackplacebb[t][attacker][attackweapon], appearplbb, appearenemybb, mayoccupybb[attacker], placebb[APPEAR][attacker][attackweapon], placebb[HIDDEN][attacker][attackweapon], defbb, attackweapon);
	size_t hashvalue = h2.calchash();
	if (attackplacemap.count(hashvalue) == 1) {
		attackplacebb = attackplacemap[hashvalue][0];
		attackmoveplacebb = attackplacemap[hashvalue][1];
		attackbeforeplaceupbb = attackplacemap[hashvalue][2];
		attackbeforeplaceunderbb = attackplacemap[hashvalue][3];
		occnumib = occnumibmap[hashvalue];
		if (attackplacebb.popcnt() > 0) {
			candestroy = true;
		}
		attackplacecount2++;
	}
	else {
		for (auto pos: canattackplacebb[t][attacker][attackweapon]) {
			for (int dir = 0; dir < 4; dir++) {
				BitBoard& attbb = attackbb[attackweapon][dir][pos.getpos()];
				if (defbb.isincluded(attbb)) {
					int occnum = BitBoard::andnot(mayoccupybb[attacker], attbb).popcnt() + (mayoccupybb[defender] & attbb).popcnt();
					candestroy = true;
					// 攻撃した場所を存在可能な場所に追加
					attackplacebb.set(pos);
					attackmoveplacebb.set(pos);
					// 攻撃前に存在可能な場所を追加
					if (placebb[APPEAR][attacker][attackweapon].isset(pos)) {
						attackbeforeplaceupbb.set(pos);
						if (attacker == ENEMY) {
							occnumib.setifmax(pos, occnum);
						}
					}
					if (mayoccupybb[attacker].isset(pos) && placebb[HIDDEN][attacker][attackweapon].isset(pos)) {
						attackbeforeplaceunderbb.set(pos);
						if (attacker == ENEMY) {
							occnumib.setifmax(pos, occnum);
						}
					}
					BitBoard canmoveup, canmoveunder, canarriveup, canarriveunder;
					// 占領した場所に防御側のプレーヤーが顕現状態で存在していた場合は排除して計算する
					if (attacker == 0) {
						canmoveup = ~(BitBoard::andnot(attbb, appearenemybb) | appearplbb | cannotenterbb[attacker][attackweapon]);
					}
					else {
						canmoveup = ~(BitBoard::andnot(attbb, appearplbb) | appearenemybb | cannotenterbb[attacker][attackweapon]);
					}
					// 占領した場所は隠蔽状態で移動可能になる
					canmoveunder = BitBoard::andnot(cannotenterbb[attacker][attackweapon], (mayoccupybb[attacker] | attbb));
					// 攻撃後に移動する場合も計算する
					if (placebb[APPEAR][attacker][attackweapon].isset(pos)) {
						calccanarriveplace(canmoveup, canmoveunder, pos, canarriveup, canarriveunder, 1);
						attackmoveplacebb |= canarriveup | canarriveunder;
					}
					if (placebb[HIDDEN][attacker][attackweapon].isset(pos)) {
						calccanarriveplace(canmoveunder, canmoveup, pos, canarriveunder, canarriveup, 1);
						attackmoveplacebb |= canarriveup | canarriveunder;
					}
					// 周囲4マスに攻撃前に存在可能だったかどうかのチェック
					for (int i = 0 ; i < 4 ; i++) {
						Pos pos2 = pos + dist1pos[i];
						// 盤内かどうかのチェック
						if (isinfield(pos.getx() + dist1pos[i].getdirx(), pos.gety() + dist1pos[i].getdiry())) {
							// 顕現状態で存在していた可能性がある場合は、攻撃前にそこに存在可能
							if (placebb[APPEAR][attacker][attackweapon].isset(pos2)) {
								attackbeforeplaceupbb.set(pos2);
								if (attacker == ENEMY) {
									occnumib.setifmax(pos2, occnum);
								}
							}
							// 隠蔽状態で存在していた可能性がある場合は、そこに誰もいないか、攻撃地点を攻撃側が占領していた場合は、そこに存在可能
							if (placebb[HIDDEN][attacker][attackweapon].isset(pos2) && (!appearplbb.isset(pos2) || mayoccupybb[attacker].isset(pos))) {
								attackbeforeplaceunderbb.set(pos2);
								if (attacker == ENEMY) {
									occnumib.setifmax(pos2, occnum);
								}
							}
						}
					}
					// 攻撃方向によっては、移動可能な場所が変わる可能性があるので break はしない
				}
			}
		}
		attackplacemap[hashvalue][0] = attackplacebb;
		attackplacemap[hashvalue][1] = attackmoveplacebb;
		attackplacemap[hashvalue][2] = attackbeforeplaceupbb;
		attackplacemap[hashvalue][3] = attackbeforeplaceunderbb;
		occnumibmap[hashvalue] = occnumib;
		attackplacecount1++;
	}
	return candestroy;
}

// attacker の陣営の attackweapon のプレーヤーが、相手の陣営の defenceweaponbit のプレーヤーをすべて確実に殺せるかどうか
// defenceweaponbit は下位ビットから順に相手陣営のプレーヤーを表す
// 殺せる場合は、殺した際の場所を attackplacebb に格納する
//bool GameInfo::checkcandestroy2(const int t, const int attacker, const int attackweapon, const int defenceweaponbit, BitBoard& attackplacebb) {
//	int defender = 1 - attacker;
//	// ビットが立っている各相手陣営のプレーヤーについてのチェック
//	for (int defenceweapon = 0; defenceweapon < 3; defenceweapon++) {
//		if ((1 << defenceweapon) & defenceweaponbit) {
//			// 治療中であれば、本拠地にいるはずなので絶対に死なない
//			if (sstates[defender][defenceweapon].recovery > 0) {
//				return false;
//			}
//			// 防御側の存在可能な場所
//			BitBoard& defbb = placebb[ALL][defender][defenceweapon];
//			// 防御側の存在可能な場所の数が、攻撃側の一度に攻撃可能な場所の数以下でなければ、確実に殺すことはできない
//			if (defbb.popcnt() > osize[attackweapon]) {
//				return false;
//			}
//			// 防御側の存在可能な場所が、攻撃側の攻撃可能な範囲にすべて収まっていなければ、確実に殺すことはできない
//			if (!defbb.isincluded(canattackbb[t][attacker][attackweapon])) {
//				return false;
//			}
//		}
//	}
//	attackplacebb.clear();
//	bool candestroy = false;
//	// 攻撃可能な場所から攻撃をし、防御側の存在可能な場所をすべて占領していれば殺せる
//	HashData2 h2(canattackplacebb[t][attacker][attackweapon], defbb, attackweapon);
//	size_t hashvalue = h2.calchash();
//	if (attackplacemap.count(hashvalue) == 1) {
//		attackplacebb = attackplacemap[hashvalue];
//		if (attackplacebb.popcnt() > 0) {
//			candestroy = true;
//		}
//		attackplacecount2++;
//	}
//	else {
//		for (auto pos : canattackplacebb[t][attacker][attackweapon]) {
//			for (int dir = 0; dir < 4; dir++) {
//				if (defbb.isincluded(attackbb[attackweapon][dir][pos.getpos()])) {
//					candestroy = true;
//					attackplacebb.set(pos);
//					break;
//				}
//			}
//		}
//		attackplacemap[hashvalue] = attackplacebb;
//		attackplacecount1++;
//	}
//	return candestroy;
//}

// 指定したプレーヤーを殺す
void GameInfo::kill(const int pl, const int weapon) {
	// 殺した敵を本拠地に移動する
	//for (int i = 0; i < 3; i++) {
	//	placebb[i][pl][weapon].clear();
	//}
	if (!sstates[pl][weapon].hidden) {
		appearplbb.reset(sstates[pl][weapon].pos);
		if (pl == 0) {
			appearallybb.reset(sstates[pl][weapon].pos);
		}
		else {
			appearenemybb.reset(sstates[pl][weapon].pos);
		}
	}
	placebb[APPEAR][pl][weapon].set(homepos[pl][weapon]);
	placebb[HIDDEN][pl][weapon].clear();
	placebb[ALL][pl][weapon].set(homepos[pl][weapon]);
	sstates[pl][weapon].pos = homepos[pl][weapon];
	sstates[pl][weapon].hidden = false;
	sstates[pl][weapon].recovery = recoveryTurns;
}

void GameInfo::move(const int weapon, const Pos& from, const bool fromhidden, const Pos& to, const bool tohidden) {
	// 移動する
	if (!fromhidden) {
		placebb[APPEAR][ALLY][weapon].reset(from);
		appearplbb.reset(from);
	}
	else {
		placebb[HIDDEN][ALLY][weapon].reset(from);
	}
	placebb[ALL][ALLY][weapon].reset(from);
	if (!tohidden) {
		placebb[APPEAR][ALLY][weapon].set(to);
		appearplbb.set(to);
	}
	else {
		placebb[HIDDEN][ALLY][weapon].set(to);
	}
	placebb[ALL][ALLY][weapon].set(to);
	sstates[ALLY][weapon].pos = to;
	sstates[ALLY][weapon].hidden = tohidden;
}

// 直前の行動を計算する。
// type: 行動の種類 0: 移動のみ、1: 移動後に攻撃した、2: 移動前に攻撃した（移動しない場合も含む）
// weapon: 計算するキャラクターの武器ID
// changednuminenemysight: 攻撃した場合、敵の視界内の可能性のある場所で占領状態が変化したマスの数
// prevpos: 行動前の場所
// prevhidden: 行動前に隠蔽状態だったか
void GameInfo::calcprevactiontype(const int type, const int weapon, const int changednuminenemysight, const Pos prevpos, const bool prevhidden) {
	// 行動する前の直前の行動タイプ
	int ptype = prevactiontype[weapon];
	Pos currentpos = sstates[ALLY][weapon].pos;
	
	// 攻撃によって変化したマスが相手に見えていない場合は、相手に何の情報も与えていないので移動のみ扱いとする
	if (changednuminenemysight == 0) {
		prevactiontype[weapon] = PREVACTION_MOVE;
	}
	else {
		// 移動しかしていない場合
		if (type == 0) {
			prevactiontype[weapon] = PREVACTION_MOVE;
		}
		// 移動後に攻撃した場合
		else if (type == 1) {
			// 移動前の場所がばれているか（ばれている可能性が高い）場合、場所を推測されたものとする
			// 直前の場所が隠蔽状態で、場所を完全に特定されていない PREVACTION_ATTACK でも、状況によっては場所を1か所に推定される可能性がある
			if ((enesikaibb.isset(prevpos) && prevhidden == false) || ptype == PREVACTION_ASSUMED) {
				prevactiontype[weapon] = PREVACTION_ASSUMED;
			}
			else {
				// 1マスのみ攻撃を見られた場合は、場所の特定は困難だと思われるので、移動扱いとしておく
				// todo: これは本当か？
				if (changednuminenemysight == 1) {
					prevactiontype[weapon] = PREVACTION_MOVE;
				}
				// 攻撃した場所は推測されたとして計算をすすめる
				else {
					// 行動後に隠蔽状態だとした場合、相手の立場から立ってみると味方の行動は以下のように推測されるはず。
					// １．攻撃した場所が相手の視界内の場合（移動後に攻撃したわけなので、そこには絶対行動前には存在していない）
					// １．１．攻撃した場所に隠蔽状態で存在、顕現、攻撃、その場で隠蔽
					// １．２．攻撃した場所に隠蔽状態で存在、顕現、攻撃、視界外へ移動
					// １．３．攻撃した場所の隣に存在、攻撃した場所に移動、攻撃、隠蔽
					// 従って、攻撃した場所と、その周囲4マスのうち視界外の場所のいずれかに味方が存在すると推測される。
					// その範囲が2マス以下の場合は、危険なので場所を推定されたものとして扱う。そうでなければ、攻撃した場所が推測されたものとして扱う
					if (enesikaibb.isset(currentpos)) {
						// enesikaibb に currentpos は必ず入っているので、これで（currentposを除く）周囲4マスのうち条件を満たす場所の数を数えることができる
						if ((BitBoard::andnot(enesikaibb, canattackmovebb[currentpos.getpos()])).popcnt() <= 1) {
							prevactiontype[weapon] = PREVACTION_ASSUMED;
						}
						else {
							prevactiontype[weapon] = PREVACTION_ATTACK;
						}
					}
					// ２．攻撃した場所が相手の視界外の場合
					// ２．１．攻撃した場所に存在、攻撃、その場に存在
					// ２．２．攻撃した場所に存在、攻撃、視界外へ移動
					// ２．３．攻撃した場所に存在、攻撃、視界内の味方の占領地へ移動、隠蔽
					// ２．４．攻撃した場所の隣に存在、攻撃した場所に移動、攻撃
					// 従って、攻撃した場所と、その周囲4マスのうち視界外または、味方の占領地のいずれかに味方が存在すると推測される。
					// その範囲が2マス以下の場合は、危険なので場所を推定されたものとして扱う。そうでなければ、攻撃した場所が推測されたものとして扱う
					else {
						// ~enesikaibb に必ず currentpos は入っているので、これで currentpos を含む周囲4マスのうち条件を満たす場所の数を数えることができる
						if (((~enesikaibb | mayoccupybb[ALLY]) & canattackmovebb[currentpos.getpos()]).popcnt() <= 2) {
							prevactiontype[weapon] = PREVACTION_ASSUMED;
						}
						else {
							prevactiontype[weapon] = PREVACTION_ATTACK;
						}
					}
				}
			}
		}
		// 移動前に攻撃した場合
		else {
			// 行動前の場所がばれているか（ばれている可能性が高い）場合、場所を推測されたものとする
			// 直前の場所が隠蔽状態で、場所を完全に特定されていない PREVACTION_ATTACK でも、状況によっては場所を1か所に推定される可能性がある
			if ((enesikaibb.isset(prevpos) && prevhidden == false) || ptype != PREVACTION_MOVE) {
				// 相手の立場から見ると味方の行動は以下のように推測されるはず
				// １．味方が行動前に顕現状態の場合
				// １．１．攻撃、その場で隠蔽
				// １．２．攻撃、視界外へ移動
				// １．３．攻撃、味方の占領地へ移動、隠蔽
				// ２．味方が行動前に隠蔽状態の場合
				// ２．１．顕現、攻撃、その場で隠蔽
				// ２．２．顕現、攻撃、視界外へ移動
				// これらの条件を満たすマスが 2 以下の場合は危険とみなす
				if ((prevhidden == false ? 
					((~enesikaibb | mayoccupybb[ALLY]) & canattackmovebb[prevpos.getpos()]).popcnt() :
					BitBoard::andnot(enesikaibb, canattackmovebb[prevpos.getpos()]).popcnt())
					<= 2) {
					prevactiontype[weapon] = PREVACTION_ASSUMED;
				}
				else {
					prevactiontype[weapon] = PREVACTION_ATTACK;
				}
			}
			else {
				// 1マスのみ攻撃を見られた場合は、場所の特定は困難だと思われるので、移動扱いとしておく
				// ただし、周囲8マスを攻撃するキャラの場合は、特定される可能性が高いので除く
				// todo: これは本当か？
				if (changednuminenemysight == 1 && weapon != 2) {
					prevactiontype[weapon] = PREVACTION_MOVE;
				}
				// 攻撃した場所は推測されたとして計算をすすめる
				else {
					// 行動後に隠蔽状態だとした場合、相手の立場から立ってみると味方の行動は以下のように推測されるはず。
					// １．攻撃した場所が相手の視界内の場合（ここに来たということは相手に行動前の存在場所がわかっていないということなので、そこには顕現状態で存在していない）
					// １．１．攻撃した場所に隠蔽状態で存在、顕現、攻撃、その場で隠蔽
					// １．２．攻撃した場所に隠蔽状態で存在、顕現、攻撃、視界外へ移動
					// １．３．攻撃した場所の隣に存在、攻撃した場所に移動、攻撃、隠蔽
					// 従って、攻撃した場所と、その周囲4マスのうち視界外の場所のいずれかに味方が存在すると推測される。
					// その範囲が2マス以下の場合は、危険なので場所を推定されたものとして扱う。そうでなければ、攻撃した場所が推測されたものとして扱う
					if (enesikaibb.isset(prevpos)) {
						// enesikaibb に currentpos は必ず入っているので、これで（currentposを除く）周囲4マスのうち条件を満たす場所の数を数えることができる
						if ((BitBoard::andnot(enesikaibb, canattackmovebb[prevpos.getpos()])).popcnt() <= 1) {
							prevactiontype[weapon] = PREVACTION_ASSUMED;
						}
						else {
							prevactiontype[weapon] = PREVACTION_ATTACK;
						}
					}
					// ２．攻撃した場所が相手の視界外の場合
					// ２．１．攻撃した場所に存在、攻撃、その場に存在
					// ２．２．攻撃した場所に存在、攻撃、視界外へ移動
					// ２．３．攻撃した場所に存在、攻撃、視界内の味方の占領地へ移動、隠蔽
					// ２．４．攻撃した場所の隣に存在、攻撃した場所に移動、攻撃
					// 従って、攻撃した場所と、その周囲4マスのうち視界外または、味方の占領地のいずれかに味方が存在すると推測される。
					// その範囲が2マス以下の場合は、危険なので場所を推定されたものとして扱う。そうでなければ、攻撃した場所が推測されたものとして扱う
					else {
						// ~enesikaibb に必ず currentpos は入っているので、これで currentpos を含む周囲4マスのうち条件を満たす場所の数を数えることができる
						if (((~enesikaibb | mayoccupybb[ALLY]) & canattackmovebb[prevpos.getpos()]).popcnt() <= 2) {
							prevactiontype[weapon] = PREVACTION_ASSUMED;
						}
						else {
							prevactiontype[weapon] = PREVACTION_ATTACK;
						}
					}
				}
			}
		}
	}
#ifdef RECORDACTION
	if (DEBUGRECCONDITION) {
		cerr << "  patype " << prevactiontype[weapon] << endl;
	}
#endif
}

// 行動のシミュレーションを開始する
// type: 行動のタイプ 0: 移動のみ 1: 移動後に dir の方向に攻撃する 2: 移動前に攻撃する場合
void GameInfo::startsimulate(const int type, const int weapon, const int attackdir, Action& act, const int maxturn, double& maxhyouka) {
	// 現在のゲーム情報を壊さないように、ゲーム情報をコピーし、コピーしたものでシミュレーションを行う
	GameInfo ginfo = *this;
	// キャラクターの状態
	SamuraiState& ss = ginfo.sstates[ALLY][weapon];
	// 行動済にする
	ss.done = ss.firstdone = true;
	// 移動前の場所
	Pos oldpos = ss.pos;
	// 移動前が隠蔽状態かどうか
	bool oldhidden = ss.hidden;
	// 移動後の場所
	Pos newpos = oldpos + act.dest;
	// 移動後が隠蔽状態かどうか
	bool newhidden = ss.hidden ^ act.changed;

	// 敵を殺した確率を初期化
	ginfo.killpercent = 0;

	// 相手の視界内の可能性のある場所で、攻撃によって変化した場所の数
	int changednuminenemysight = 0;
	// typeに合わせた行動を行う
	// 移動前に攻撃する
	if (type == 2) {
		// 移動後に攻撃する
		changednuminenemysight = ginfo.attack(weapon, attackdir);
	}
	// 移動する
	ginfo.move(weapon, oldpos, oldhidden, newpos, newhidden);
	if (type == 1) {
		// 移動後に攻撃する
		changednuminenemysight = ginfo.attack(weapon, attackdir);
	}
	ginfo.calccanmoveandattack2(ALLY, weapon);

	// そのキャラクターの直前の行動タイプを設定する
	// 移動のみ
	ginfo.calcprevactiontype(type, weapon, changednuminenemysight, oldpos, oldhidden);

	// 敵に察知されているかどうか
	// 敵の視界内にいる可能性があり、そこに顕現状態であれば察知されている
	if (newhidden == false && enesikaibb.isset(newpos)) {
		ginfo.isdetected = true;
	}
	// そうでなければ、行動のタイプが推測されていない場合は察知されていないことにする
	else {
		ginfo.isdetected = (ginfo.prevactiontype[weapon] != PREVACTION_ASSUMED) ? false : true;
	}
	// 次のターンにする
	ginfo.nextturn();

#ifdef RECORDACTION
	if (DEBUGRECCONDITION) {
		cerr << "type: " << type << "," << ginfo.prevactiontype[weapon] << " " << checkactioncount << ":" << act << "  " << newpos << (newhidden ? " 隠" : "") << endl;
	}
#endif
	ginfo.ishidden = newhidden;
	ginfo.simulateandcheckhyouka(act, maxturn, maxhyouka, bestaction);

	checkactioncount++;

	// 移動後に攻撃する場合
	if (type == 1) {
		// 最初に顕現状態だった場合で、移動先に隠蔽できる場合は、さらに隠蔽できる
		if (!oldhidden && ginfo.mayoccupybb[ALLY].isset(newpos)) {
			if (timer.gettime() > timelimit) {
				cerr << "time out move attack hidden. weapon = " << weapon << " dir = " << attackdir << endl;
				return;
			}
			act.push_back(9);
			act.changed = !act.changed;
#ifdef RECORDACTION
			if (DEBUGRECCONDITION) {
				cerr << "type: " << type << "," << ginfo.prevactiontype[weapon] << " " << checkactioncount << ":" << act << "  " << newpos << " 隠" << endl;
			}
#endif	
			// 隠蔽に関連するところだけ更新する。nextturn はもうすでに行っているのでしてはいけない
			ginfo.placebb[APPEAR][ALLY][weapon].reset(newpos);
			ginfo.placebb[HIDDEN][ALLY][weapon].set(newpos);
			ginfo.sstates[ALLY][weapon].hidden = true;
			ginfo.ishidden = true;
			ginfo.isdetected = (ginfo.prevactiontype[weapon] == PREVACTION_MOVE) ? false : true;
			ginfo.calccanmoveandattack2(ALLY, weapon);
			ginfo.simulateandcheckhyouka(act, maxturn, maxhyouka, bestaction);
			checkactioncount++;
		}
	}
	// 攻撃後に移動する場合
	else if (type == 2) {
		// 最初に隠蔽状態で、移動していない場合は、出現、攻撃、隠蔽という行動を行える
		if (oldhidden && act.dest == ZERO_POS) {
			if (timer.gettime() > timelimit) {
				cerr << "time out appear attack hidden. weapon = " << weapon << " dir = " << attackdir << endl;
				return;
			}	
			act.push_back(9);
			act.changed = !act.changed;
#ifdef RECORDACTION
			if (DEBUGRECCONDITION) {
				cerr << "type: " << type << "," << ginfo.prevactiontype[weapon] << " " << checkactioncount << ":" << act << "  " << newpos << " 隠" << endl;
			}
#endif	
			// 隠蔽に関連するところだけ更新する。nextturn はもうすでに行っているのでしてはいけない
			ginfo.placebb[APPEAR][ALLY][weapon].reset(newpos);
			ginfo.placebb[HIDDEN][ALLY][weapon].set(newpos);
			ginfo.sstates[ALLY][weapon].hidden = true;
			ginfo.ishidden = true;
			ginfo.calccanmoveandattack2(ALLY, weapon);
			ginfo.calcprevactiontype(type, weapon, changednuminenemysight, oldpos, oldhidden);
			//ginfo.prevactiontype[weapon] = PREVACTION_ATTACK;
			ginfo.isdetected = (ginfo.prevactiontype[weapon] == PREVACTION_MOVE) ? false : true;
			ginfo.simulateandcheckhyouka(act, maxturn, maxhyouka, bestaction);
			checkactioncount++;
		}
	}
}

// シミュレーションを行い、評価値を計算し、評価値がそれまでの最大評価値を超えていた場合は、最善手を更新する
void GameInfo::simulateandcheckhyouka(Action& act, const int maxturn, double& maxhyouka, Action& bestact) {
	// シミュレーションを行い、評価値を計算する
	earlybestaction = (turn <= EARLY_TURN && (act == earlyturnbestaction[0] || act == earlyturnbestaction[1] || act == earlyturnbestaction[2])) ? true : false;
	// 次のターンも含めた最大占領数（最後から一つ前のピリオドのみ計算する）
	maxoccnumbynextperiod = 0;
	// 最後から一つ前のピリオドの場合、次の行動も含めて最も占領数の多い占領数を計算する
	if (startturn >= 84 && startturn < 90) {
		maxoccnumbynextperiod = -10000;
		// 次に距離１以内で、顕現状態で移動可能な場所を計算する
		SamuraiState& ss = sstates[ALLY][act.pid];
		BitBoard canmoveup, canmoveunder, canarriveup, canarriveunder;
		canmoveup = ~(appearplbb | cannotenterbb[ALLY][act.pid]);
		canmoveunder = BitBoard::andnot(cannotenterbb[ALLY][act.pid], mayoccupybb[ALLY]);
		if (ss.hidden == false) {
			calccanarriveplace(canmoveup, canmoveunder, ss.pos, canarriveup, canarriveunder, 1);
		}
		else {
			calccanarriveplace(canmoveunder, canmoveup, ss.pos, canarriveunder, canarriveup, 1);
		}
		// そこから攻撃した場合、もっとも占領数の多い占領数を記録する
		for (auto pos : canarriveup) {
			for (int dir = 0; dir < 4; dir++) {
				BitBoard& attbb = attackbb[act.pid][dir][pos.getpos()];
				int occnum = (attbb | mayoccupybb[ALLY]).popcnt() - BitBoard::andnot(attbb, mayoccupybb[ENEMY]).popcnt();
				if (occnum > maxoccnumbynextperiod) {
					maxoccnumbynextperiod = occnum;
				}
			}
		}
	}

	double hyouka;
#ifdef DEBUG
	if (debugusealpha) {
		hyouka = simulate(maxturn, maxhyouka, HYOUKA_MAX);
	}
	else {
		hyouka = simulate(maxturn, HYOUKA_MIN, HYOUKA_MAX);
	}
#else
	hyouka = simulate(maxturn, maxhyouka, HYOUKA_MAX);
#endif

#ifdef RECORDACTION
	actionmap[hyouka * 100000 + act.getactionvalue()] = act;
	if (DEBUGRECCONDITION) {
		cerr << "hyouka: = " << hyouka << endl;
	}
#endif


	// 評価値がそれまでに見つかった最大の評価値を超えていた場合は、更新する
	if (hyouka > maxhyouka) {
		maxhyouka = hyouka;
		bestact = act;
#ifdef RECORDACTION
		if (DEBUGRECCONDITION) {
			cerr << "best action " << bestact << " maxhyouka " << maxhyouka << endl;
		}
#endif
	}
}

// maxturn までシミュレーションを行い、評価値を計算する
double GameInfo::simulate(const int maxturn, double alpha, double beta) {
	double hyouka;
	// シミュレートする最大ターン数を超えていれば、現在の局面の評価値を計算して返す
	if (turn > maxturn) {
		return calchyouka();
	}
	// 味方の手番の場合
	else if (turn % 2 == playOrder) {
		GameInfo ginfo;
		// 行動可能なすべての味方のうち、まず、移動のみの行動の評価値を計算する。
		// 次に、敵を殺せる場合は殺す行動をとって評価値を計算し、殺せる確率に応じて殺した場合の評価値を計算する
		// 一人でも行動したかどうかを表すフラグ
		// 同時に複数の敵を殺せる場合もあるが、その計算は大変なので考慮しない
		bool actionflag = false;

		// そのターンに自由に行動可能なキャラクターのチェック
		for (int w = 0; w < 3; w++) {
			// 行動可能かどうかのチェック
			if (!sstates[ALLY][w].done && sstates[ALLY][w].recovery == 0) {
				mayactionflag[w] = true;
			}
		}

		// 各キャラクターについて順番に調べる
		for (int w = 0; w < 3; w++) {
			// 行動可能かどうかのチェック
			if (!sstates[ALLY][w].done && sstates[ALLY][w].recovery == 0) {
				actionflag = true;
				// 現在のゲーム情報をコピーし、それを使って計算する
				ginfo = *this;


				// 各敵について、殺せるかどうかを調べる
				// αβを使って殺さない場合の評価をしてもよいか
				bool canusealphabeta = true;
				// 敵を殺せる場合、存在可能な場所
				BitBoard killplacebb[3], killbb[3], killbeforeplaceup[3], killbeforeplaceunder[3];
				IntBoard occnumib[3];
				// それぞれの敵を殺せるかどうか
				bool cankill[3] = { false, false, false };
				for (int ew = 0; ew < 3; ew++) {
					// 最後のピリオド（90 ターン以上の場合）で、行動済の敵は殺しても意味がないので飛ばす
					if (turn >= 90 && ginfo.sstates[ENEMY][ew].done == true) {
						continue;
					}
					// ew の敵を殺せるかどうか
					// その敵の治療ターンの評価倍率が 0 の場合は殺す価値がない
					if (ginfo.curehyoukamul[ENEMY][ew] != 0) {
						if (ginfo.checkcandestroy(actionnum[ALLY][w], ALLY, w, ew, killplacebb[ew], killbb[ew], killbeforeplaceup[ew], killbeforeplaceunder[ew], occnumib[ew], 0)) {
							// 殺した場合の治療ターンの評価値が通常の場合は、殺さない場合の評価値は影響しないのでαβの枝狩をしても良い
							if (ginfo.curehyoukamul[ENEMY][ew] != HYOUKA_CUREMUL_NORMAL) {
								canusealphabeta = false;
							}
							cankill[ew] = true;
						}
					}
				}
				
				// 殺さない場合の評価をまず行う
				double notkillhyouka;
#ifdef RECORDACTION
				ginfo.rec_pl[turn] = w;
				ginfo.rec_ac[turn] = 0;
#endif
				assert(ginfo.actionnum[0][w] <= 1);
				// 行動したことにする
				ginfo.sstates[ALLY][w].done = true;
				// 自身の存在可能な場所設定する（あらかじめ calccanmoveandattack で計算したものを使う）
				ginfo.placebb[APPEAR][ALLY][w] = ginfo.canmovebb[ginfo.actionnum[ALLY][w]][APPEAR][ALLY][w];
				ginfo.placebb[HIDDEN][ALLY][w] = ginfo.canmovebb[ginfo.actionnum[ALLY][w]][HIDDEN][ALLY][w];
				ginfo.placebb[ALL][ALLY][w] = ginfo.canmovebb[ginfo.actionnum[ALLY][w]][ALL][ALLY][w];
				// 隠蔽状態で存在可能な場所があれば隠蔽状態としておく
				ginfo.sstates[ALLY][w].hidden = (ginfo.placebb[HIDDEN][ALLY][w].popcnt() == 0) ? false : true;
				ginfo.actionnum[ALLY][w]++;
				ginfo.actionflag[ALLY][w] = true;
				// 直前の行動の種類を移動にする
				ginfo.prevactiontype[w] = PREVACTION_MOVE;
				// 次のターンの計算
				ginfo.nextturn();
				// 敵を殺せない場合は、枝狩りありの評価値を計算する。
				if (canusealphabeta) {
					notkillhyouka = ginfo.simulate(maxturn, alpha, beta);
				}
				// 敵を殺せる場合は、枝狩りしない評価値なので、alpha, beta は使わない
				else {
					notkillhyouka = ginfo.simulate(maxturn, HYOUKA_MIN, HYOUKA_MAX);
				}

#ifdef RECORDACTION
				if (DEBUGRECCONDITION) {
					cerr << "  ta " << (int)turn << " h " << notkillhyouka << " a " << alpha << " b " << beta;
					if (notkillhyouka > alpha) {
						cerr << " max";
					}
					cerr << endl;
				}
#endif
				// alpha 値を越えていた場合の処理
				if (notkillhyouka > alpha) {
					alpha = notkillhyouka;
					// alpha 値が beta 値を越えていた場合は、beta カットする
					if (alpha >= beta) {
						return beta;
					}
				}

				// それぞれの敵を攻撃で殺せる場合の評価
				// todo: 同時に複数の敵を殺すことができる場合も対応する
				for (int ew = 0; ew < 3; ew++) {
					// 殺せる場合
					if (cankill[ew] == true) {
						ginfo = *this;
						// 殺した場合は、殺すことができる場所に顕現状態で存在できる。todo：隠蔽状態ではとりあえず存在しないことにするが、実際には存在できるはず！
						// todo: 殺すということは占領しているはず
						ginfo.placebb[APPEAR][ALLY][w] = killbb[ew];
						ginfo.placebb[HIDDEN][ALLY][w].clear();
						ginfo.placebb[ALL][ALLY][w] = killbb[ew];
						ginfo.sstates[ALLY][w].hidden = false;
						// 存在場所は推測されたものとする
						ginfo.prevactiontype[w] = PREVACTION_ASSUMED;
						ginfo.kill(ENEMY, ew);
						// 攻撃した場合は、自由に行動できない
						ginfo.mayactionflag[w] = false;
						// 2回目の行動の場合は不確実なので評価を下げる
						// todo:これで良いか？
						if (ginfo.actionflag[ALLY][w]) {
							ginfo.curehyoukamul[ENEMY][ew] *= HYOUKA_CUREMUL_ALLYCANMOVE;
						}
#ifdef RECORDACTION
						ginfo.rec_pl[turn] = w;
						ginfo.rec_ac[turn] = ew + 1;
#endif
						// 行動済にする
						ginfo.sstates[ALLY][w].done = true;
						ginfo.nextturn();
						ginfo.actionflag[ALLY][w] = true;
						// 行動回数をリセットする
						ginfo.actionnum[ALLY][w] = 0;
						// 次の行動で攻撃可能な場所と、移動可能な場所を計算しなおす。殺した敵はもう行動できないので計算しなおす必要はない
						ginfo.calccanmoveandattackbb(ginfo.placebb[APPEAR][ALLY][w], ginfo.placebb[HIDDEN][ALLY][w], ginfo.actionnum[ALLY][w], ALLY, w);

						// 枝狩りはしない状態で評価値を計算する
						hyouka = ginfo.simulate(maxturn, HYOUKA_MIN, HYOUKA_MAX);
						// 殺した相手の治療ターンの評価の倍率が、殺せる確率を表す。その確率を使って殺さないで移動した場合の評価値を考慮に入れた評価値に計算しなおす
						hyouka = (hyouka * ginfo.curehyoukamul[ENEMY][ew] + notkillhyouka * (HYOUKA_CUREMUL_NORMAL - ginfo.curehyoukamul[ENEMY][ew])) / HYOUKA_CUREMUL_NORMAL;
#ifdef RECORDACTION
						if (DEBUGRECCONDITION) {
							cerr << "  turn " << (int)turn << " h " << hyouka << " a " << alpha << " b " << beta;
							if (hyouka > alpha) {
								cerr << " max";
							}
							cerr << endl;
						}
#endif
						if (hyouka > alpha) {
							alpha = hyouka;
							if (alpha >= beta) {
								return beta;
							}
						}
					}
				}
			}
		}
		// 誰も行動していなければ、なにもせず次のターンへ
		if (!actionflag) {
			ginfo = *this;
#ifdef RECORDACTION
			ginfo.rec_pl[turn] = -1;
			ginfo.rec_ac[turn] = -1;
#endif
			ginfo.nextturn();
			hyouka = ginfo.simulate(maxturn, alpha, beta);
#ifdef RECORDACTION
			if (DEBUGRECCONDITION) {
				cerr << "  pa " << (int)turn << " h " << hyouka << " a " << alpha << " b " << beta;
				if (hyouka > alpha) {
					cerr << " max";
				}
				cerr << endl;
			}
#endif
			if (hyouka > alpha) {
				alpha = hyouka;
				if (alpha >= beta) {
					return beta;
				}
			}
		}
		// 評価値を返す
		return alpha;
	}
	// 敵の手番の場合
	else {
		// 行動可能なすべての敵のうち、まず、移動のみの行動の評価値を計算する。
		// 次に、味方を殺せる場合は殺す行動をとって評価値を計算し、殺せる確立に応じて殺した場合の評価値を計算する
		// 最も評価の低いものを採用する
		GameInfo ginfo;
		// 一人でも行動したかを表すフラグ
		bool actionflag = false;
		// 各キャラクターについて順番に調べる
		int checkplacenum[3] = { 0, 0, 0 };

		for (int w = 0; w < 3; w++) {
			// 行動可能かどうかのチェック
			if (!sstates[ENEMY][w].done && sstates[ENEMY][w].recovery == 0) {
				int period = turn / 6;
				actionflag = true;
				ginfo = *this;
				// 各味方について、殺されるかどうかを調べる
				// αβを使って殺さない場合の評価をしてもよいか
				bool canusealphabeta = true;
				// 味方が殺される場合、殺した敵の存在可能な場所
				BitBoard killplacebb[3], killbb[3], killbeforeplaceupbb[3], killbeforeplaceunderbb[3];
				IntBoard occnumib[3];
				double hyoukamul[3];
				HashData4 h4(placebb[APPEAR][ENEMY][w] | placebb[HIDDEN][ENEMY][w], period, w);
				size_t hashvalue = h4.calchash();
				if (checkplacenummap.count(hashvalue) == 1) {
					checkplacenum[w] = checkplacenummap[hashvalue];
				}
				else {
					for (auto pos : (placebb[APPEAR][ENEMY][w] | placebb[HIDDEN][ENEMY][w])) {
						checkplacenum[w] += periodplaceintb[period][1 - playOrder][w].get(pos);
					}
					if (checkplacenum[w] == 0) {
						checkplacenum[w] = 1;
					}
					checkplacenummap[hashvalue] = checkplacenum[w];
				}
//#ifdef RECORDACTION
//				if (DEBUGRECCONDITION) {
//					cerr << "qwerty" << w << endl << (placebb[APPEAR][ENEMY][w] | placebb[HIDDEN][ENEMY][w]) << periodplaceintb[period][1 - playOrder][w] << endl<< checkplacenum[w] << endl;;
//				}
//#endif
				// それぞれの味方を殺せるかどうか
				bool cankill[3] = { false, false, false };
				int killnum = 0;
				// todo 同時に複数の味方が死ぬ場合もある。それを考慮すべきだが、計算に時間がかかりそうなので現状では考慮しない。
				for (int aw = 0; aw < 3; aw++) {
					// aw の味方を殺せるかどうか
					BitBoard bbbak = mayoccupybb[ENEMY];
					ginfo.mayoccupybb[ENEMY] |= ginfo.eneoccbb;
					if (ginfo.checkcandestroy(actionnum[ENEMY][w], ENEMY, w, aw, killplacebb[aw], killbb[aw], killbeforeplaceupbb[aw], killbeforeplaceunderbb[aw], occnumib[aw], period) == true) {
						assert(ginfo.placebb[ALL][ENEMY][w].popcnt() > 0);

						// 最後のピリオド（90 ターン以上の場合）で、行動済の味方は殺されても意味がないので飛ばす
						if (turn >= 90 && ginfo.sstates[ALLY][aw].done == true) {
							continue;
						}
						if (periodplacemaxnum == 0) {

							// 殺された場合の治療ターンの評価値の倍率を計算する
							// 自分が隠蔽状態の場合。相手の視界なども考慮に入れたほうが良い！
							// 敵が移動していた場合は、移動前の存在可能数で計算する
							int popcnt = (ginfo.actionflag[ENEMY][w] == false) ? ginfo.placebb[ALL][ENEMY][w].popcnt() : ginfo.preveneplacepopcnt[w];
							if (ginfo.sstates[ALLY][aw].hidden) {
								// 前の行動が移動のみの場合。
								if (ginfo.prevactiontype[aw] == PREVACTION_MOVE) {
									// 場所が複数ある場合または、危険な場所にいない場合
									ginfo.curehyoukamul[ALLY][aw] = HYOUKA_CUREMUL_HIDDEN_MAX * HYOUKA_CUREMUL_HIDDEN_DIV / (HYOUKA_CUREMUL_HIDDEN_DIV - 1 + popcnt);
									// こちらの行動が移動のみの場合で、敵の2回目の行動の場合は不確実なので評価を下げる
									if (ginfo.actionflag[ENEMY][w]) {
										ginfo.curehyoukamul[ALLY][aw] = ginfo.curehyoukamul[ALLY][aw] * ginfo.curehyoukamul[ALLY][aw] / HYOUKA_CUREMUL_NORMAL;
#ifdef RECORDACTION
										if (DEBUGRECCONDITION) {
											cerr << "action ";
										}
#endif
									}
									//#ifdef RECORDACTION
									//								if (DEBUGRECCONDITION) {
									//									cerr << mayoccupybb[ENEMY] << killplacebb[aw];
									//								}
									//#endif
																	// 敵が攻撃した場所が、敵の占領した場所でない場合は、危険度を下げる
									if (BitBoard::andnot(mayoccupybb[ENEMY], killplacebb[aw]) == killplacebb[aw]) {
										ginfo.curehyoukamul[ALLY][aw] *= HYOUKA_ENEATTACKINNOTOCCUPIEDPLACE;
#ifdef RECORDACTION
										if (DEBUGRECCONDITION) {
											cerr << "notocc ";
										}
#endif
									}
								}
								// 前の行動で、どこにいるか敵に推定されている可能性が高い場合
								else if (ginfo.prevactiontype[aw] == PREVACTION_ASSUMED) {
									ginfo.curehyoukamul[ALLY][aw] = HYOUKA_CUREMUL_MATTACKHIDDEN_MAX * HYOUKA_CUREMUL_MATTACKHIDDEN_DIV / (HYOUKA_CUREMUL_MATTACKHIDDEN_DIV - 1 + popcnt);
								}
								// 前の行動で攻撃したことが察知された場合
								else if (ginfo.prevactiontype[aw] == PREVACTION_ATTACK) {
									ginfo.curehyoukamul[ALLY][aw] = HYOUKA_CUREMUL_AMOVEHIDDEN_MAX * HYOUKA_CUREMUL_AMOVEHIDDEN_DIV / (HYOUKA_CUREMUL_AMOVEHIDDEN_DIV - 1 + popcnt);
									// こちらの行動が移動のみの場合は2回目の行動の場合は不確実なので評価を下げる
									if (ginfo.actionflag[ENEMY][w]) {
										ginfo.curehyoukamul[ALLY][aw] = ginfo.curehyoukamul[ALLY][aw] * ginfo.curehyoukamul[ALLY][aw] / HYOUKA_CUREMUL_NORMAL;
									}
#ifdef RECORDACTION
									if (DEBUGRECCONDITION) {
										cerr << "action ";
									}
#endif
								}
#ifdef RECORDACTION
								if (DEBUGRECCONDITION) {
									cerr << "wid " << w << " > " << aw << " turn " << static_cast<int>(turn) << " pat " << ginfo.prevactiontype[aw] << " mulfirst " << ginfo.curehyoukamul[ALLY][aw] << " ";
								}
#endif
							}
							// 自分が顕現状態の場合
							else {
								ginfo.curehyoukamul[ALLY][aw] = (HYOUKA_CUREMUL_NORMAL_MAX * HYOUKA_CUREMUL_NORMAL_DIV) / (HYOUKA_CUREMUL_NORMAL_DIV - 1 + popcnt);
							}
							// それまでに行動していた場合は評価を半減させる
							if (ginfo.actionflag[ALLY][aw]) {
								ginfo.curehyoukamul[ALLY][aw] *= HYOUKA_CUREMUL_ALLYMOVED;
#ifdef RECORDACTION
								if (DEBUGRECCONDITION) {
									cerr << "action ";
								}
#endif
							}
							// この敵が攻撃するまでの間に、自由に行動可能な味方がいた場合で、攻撃する前の敵の存在可能な場所をその味方が攻撃できていた場合は、殺される前に味方が殺せていた可能性が高い
							// 隠蔽状態で攻撃前に存在可能であった場合は、居場所を察知できない可能性があるので飛ばす
							if ((killbeforeplaceunderbb[aw] & mayoccupybb[ENEMY]).iszero()) {
								// 顕現状態で存在可能な場所をすべて攻撃可能な味方がいるかどうかを調べる
								for (int aw2 = 0; aw2 < 3; aw2++) {
									if (mayactionflag[aw2] == true && killbeforeplaceupbb[aw].isincluded(canattackbb[0][ALLY][aw2])) {
										//#ifdef RECORDACTION
										//									if (DEBUGRECCONDITION) {
										//										cerr << "qwerty! " << endl << killbeforeplaceupbb[aw] << killbeforeplaceunderbb[aw] << mayoccupybb[ENEMY] << canattackbb[0][ALLY][aw2] << endl << w << "," << aw << "," << aw2 <<  endl;
										//									}
										//#endif
										ginfo.curehyoukamul[ALLY][aw] *= HYOUKA_CUREMUL_MAYKILLBEFOREKILLED;
#ifdef RECORDACTION
										if (DEBUGRECCONDITION) {
											cerr << "beforekill ";
										}
#endif
										break;
									}
								}
							}
						}
						else {
							// 殺された場合の治療ターンの評価値の倍率を計算する
							// 自分が隠蔽状態の場合。相手の視界なども考慮に入れたほうが良い！
							// 敵が移動していた場合は、移動前の存在可能数で計算する
#ifdef DEBUG
							int popcnt = (ginfo.actionflag[ENEMY][w] == false) ? ginfo.placebb[ALL][ENEMY][w].popcnt() : ginfo.preveneplacepopcnt[w];
#endif
							if (ginfo.sstates[ALLY][aw].hidden) {
								// 前の行動が移動のみの場合。
								if (ginfo.prevactiontype[aw] == PREVACTION_MOVE) {
									double cnumtotal = 0;
									for (auto pos : (killbeforeplaceupbb[aw] | killbeforeplaceunderbb[aw])) {
										int onum = occnumib[aw].get(pos);
										int cnum = periodplaceintb[period][1 - playOrder][w].get(pos);
										if (onum < 4) {
											cnumtotal += cnum / 4 * onum;
										}
										else {
											cnumtotal += cnum;
										}
									}
									ginfo.curehyoukamul[ALLY][aw] = cnumtotal / checkplacenum[w] * HYOUKA_CUREMUL_NORMAL_MAX * HYOUKA_CUREMUL_MOVE;
#ifdef RECORDACTION
									if (DEBUGRECCONDITION) {
										cerr << "move " << endl;
//										cerr << occnumib[aw] << periodplaceintb[period][1 - playOrder][w] << endl << (killbeforeplaceupbb[aw] | killbeforeplaceunderbb[aw]) << endl;
										cerr << cnumtotal << "," << checkplacenum[w] << "," << cnumtotal / checkplacenum[w] * 10 << "(" << HYOUKA_CUREMUL_HIDDEN_MAX * HYOUKA_CUREMUL_HIDDEN_DIV / (HYOUKA_CUREMUL_HIDDEN_DIV - 1 + popcnt) << ") ";
									}
#endif
									// 場所が複数ある場合または、危険な場所にいない場合
//									ginfo.curehyoukamul[ALLY][aw] = HYOUKA_CUREMUL_HIDDEN_MAX * HYOUKA_CUREMUL_HIDDEN_DIV / (HYOUKA_CUREMUL_HIDDEN_DIV - 1 + popcnt);
//									// こちらの行動が移動のみの場合で、敵の2回目の行動の場合は不確実なので評価を下げる
//									if (ginfo.actionflag[ENEMY][w]) {
//										ginfo.curehyoukamul[ALLY][aw] = ginfo.curehyoukamul[ALLY][aw] * ginfo.curehyoukamul[ALLY][aw] / HYOUKA_CUREMUL_NORMAL;
//#ifdef RECORDACTION
//										if (DEBUGRECCONDITION) {
//											cerr << "action ";
//										}
//#endif
//									}
									//#ifdef RECORDACTION
									//								if (DEBUGRECCONDITION) {
									//									cerr << mayoccupybb[ENEMY] << killplacebb[aw];
									//								}
									//#endif
									// 敵が攻撃した場所が、敵の占領した場所でない場合は、危険度を下げる
									if (BitBoard::andnot(mayoccupybb[ENEMY], killplacebb[aw]) == killplacebb[aw]) {
										ginfo.curehyoukamul[ALLY][aw] *= HYOUKA_ENEATTACKINNOTOCCUPIEDPLACE;
#ifdef RECORDACTION
										if (DEBUGRECCONDITION) {
											cerr << "notocc ";
										}
#endif
									}
								}
								// 前の行動で、どこにいるか敵に推定されている可能性が高い場合
								else if (ginfo.prevactiontype[aw] == PREVACTION_ASSUMED) {
									double cnumtotal = 0;
									for (auto pos : (killbeforeplaceupbb[aw] | killbeforeplaceunderbb[aw])) {
										cnumtotal += periodplaceintb[period][1 - playOrder][w].get(pos);
									}
									ginfo.curehyoukamul[ALLY][aw] = cnumtotal / checkplacenum[w] * HYOUKA_CUREMUL_NORMAL_MAX * HYOUKA_CUREMUL_ASSUMED;
									if (ginfo.curehyoukamul[ALLY][aw] > 10) {
										ginfo.curehyoukamul[ALLY][aw] = 10;
									}

//									ginfo.curehyoukamul[ALLY][aw] = HYOUKA_CUREMUL_MATTACKHIDDEN_MAX * HYOUKA_CUREMUL_MATTACKHIDDEN_DIV / (HYOUKA_CUREMUL_MATTACKHIDDEN_DIV - 1 + popcnt);
#ifdef RECORDACTION
									if (DEBUGRECCONDITION) {
										cerr << "assumed " << endl;
//										cerr << occnumib[aw] << endl << periodplaceintb[period][1 - playOrder][w] << endl << (killbeforeplaceupbb[aw] | killbeforeplaceunderbb[aw]) << endl;
										cerr << cnumtotal << "," << checkplacenum[w] << "," << cnumtotal / checkplacenum[w] * 10 << "(" << HYOUKA_CUREMUL_MATTACKHIDDEN_MAX * HYOUKA_CUREMUL_MATTACKHIDDEN_DIV / (HYOUKA_CUREMUL_MATTACKHIDDEN_DIV - 1 + popcnt) << ") ";
									}
#endif
								}
								// 前の行動で攻撃したことが察知された場合
								else if (ginfo.prevactiontype[aw] == PREVACTION_ATTACK) {
									double cnumtotal = 0;
									for (auto pos : (killbeforeplaceupbb[aw] | killbeforeplaceunderbb[aw])) {
										int onum = occnumib[aw].get(pos);
										int cnum = periodplaceintb[period][1 - playOrder][w].get(pos);
										if (onum < 2) {
											cnumtotal += cnum / 2 * onum;
										}
										else {
											cnumtotal += cnum;
										}
									}
									ginfo.curehyoukamul[ALLY][aw] = cnumtotal / checkplacenum[w] * HYOUKA_CUREMUL_NORMAL_MAX * HYOUKA_CUREMUL_ATTACK;
									if (ginfo.curehyoukamul[ALLY][aw] > 10) {
										ginfo.curehyoukamul[ALLY][aw] = 10;
									}
#ifdef RECORDACTION
									if (DEBUGRECCONDITION) {
										cerr << "attack " << endl;
										cerr << occnumib[aw] << endl << periodplaceintb[period][1 - playOrder][w] << endl << (killbeforeplaceupbb[aw] | killbeforeplaceunderbb[aw]) << endl;
										cerr << cnumtotal << "," << checkplacenum[w] << "," << cnumtotal / checkplacenum[w] * 10 << "(" << HYOUKA_CUREMUL_AMOVEHIDDEN_MAX * HYOUKA_CUREMUL_AMOVEHIDDEN_DIV / (HYOUKA_CUREMUL_AMOVEHIDDEN_DIV - 1 + popcnt) << ") ";
									}
#endif//									ginfo.curehyoukamul[ALLY][aw] = HYOUKA_CUREMUL_AMOVEHIDDEN_MAX * HYOUKA_CUREMUL_AMOVEHIDDEN_DIV / (HYOUKA_CUREMUL_AMOVEHIDDEN_DIV - 1 + popcnt);
									//// こちらの行動が移動のみの場合は2回目の行動の場合は不確実なので評価を下げる
									//if (ginfo.actionflag[ENEMY][w]) {
									//	ginfo.curehyoukamul[ALLY][aw] = ginfo.curehyoukamul[ALLY][aw] * ginfo.curehyoukamul[ALLY][aw] / HYOUKA_CUREMUL_NORMAL;
									//}
#ifdef RECORDACTION
									if (DEBUGRECCONDITION) {
										cerr << "action ";
									}
#endif
								}
#ifdef RECORDACTION
								if (DEBUGRECCONDITION) {
									cerr << "wid " << w << " > " << aw << " turn " << static_cast<int>(turn) << " period " << period << " pat " << ginfo.prevactiontype[aw] << " mulfirst " << ginfo.curehyoukamul[ALLY][aw] << " ";
								}
#endif
							}
							// 自分が顕現状態の場合
							else {
								double cnumtotal = 0;
								for (auto pos : (killbeforeplaceupbb[aw] | killbeforeplaceunderbb[aw])) {
									cnumtotal += periodplaceintb[period][1 - playOrder][w].get(pos);
								}
								ginfo.curehyoukamul[ALLY][aw] = cnumtotal / checkplacenum[w] * HYOUKA_CUREMUL_NORMAL_MAX * HYOUKA_CUREMUL_ASSUMED;
								if (ginfo.curehyoukamul[ALLY][aw] > 10) {
									ginfo.curehyoukamul[ALLY][aw] = 10;
								}
#ifdef RECORDACTION
								if (DEBUGRECCONDITION) {
									cerr << "appear " << endl;
//									cerr << occnumib[aw] << endl << periodplaceintb[period][1 - playOrder][w] << endl << (killbeforeplaceupbb[aw] | killbeforeplaceunderbb[aw]) << endl;
									cerr << cnumtotal << "," << checkplacenum[w] << "," << cnumtotal / checkplacenum[w] * 10 << "(" << HYOUKA_CUREMUL_MATTACKHIDDEN_MAX * HYOUKA_CUREMUL_MATTACKHIDDEN_DIV / (HYOUKA_CUREMUL_MATTACKHIDDEN_DIV - 1 + popcnt) << ") ";
								}
#endif
								//								ginfo.curehyoukamul[ALLY][aw] = (HYOUKA_CUREMUL_NORMAL_MAX * HYOUKA_CUREMUL_NORMAL_DIV) / (HYOUKA_CUREMUL_NORMAL_DIV - 1 + popcnt);
#ifdef RECORDACTION
								if (DEBUGRECCONDITION) {
									cerr << "wid " << w << " > " << aw << " turn " << static_cast<int>(turn) << " period " << period << " pat " << ginfo.prevactiontype[aw] << " mulfirst " << ginfo.curehyoukamul[ALLY][aw] << " ";
								}
#endif
							}
							// それまでに行動していた場合は評価を半減させる
							if (ginfo.actionflag[ALLY][aw]) {
								ginfo.curehyoukamul[ALLY][aw] *= HYOUKA_CUREMUL_ALLYMOVED;
#ifdef RECORDACTION
								if (DEBUGRECCONDITION) {
									cerr << "action ";
								}
#endif
							}
							// この敵が攻撃するまでの間に、自由に行動可能な味方がいた場合で、攻撃する前の敵の存在可能な場所をその味方が攻撃できていた場合は、殺される前に味方が殺せていた可能性が高い
							// 隠蔽状態で攻撃前に存在可能であった場合は、居場所を察知できない可能性があるので飛ばす
							if ((killbeforeplaceunderbb[aw] & ginfo.mayoccupybb[ENEMY]).iszero()) {
								// 顕現状態で存在可能な場所をすべて攻撃可能な味方がいるかどうかを調べる
								for (int aw2 = 0; aw2 < 3; aw2++) {
									if (mayactionflag[aw2] == true && killbeforeplaceupbb[aw].isincluded(canattackbb[0][ALLY][aw2])) {
										//#ifdef RECORDACTION
										//									if (DEBUGRECCONDITION) {
										//										cerr << "qwerty! " << endl << killbeforeplaceupbb[aw] << killbeforeplaceunderbb[aw] << mayoccupybb[ENEMY] << canattackbb[0][ALLY][aw2] << endl << w << "," << aw << "," << aw2 <<  endl;
										//									}
										//#endif
										ginfo.curehyoukamul[ALLY][aw] *= HYOUKA_CUREMUL_MAYKILLBEFOREKILLED;
#ifdef RECORDACTION
										if (DEBUGRECCONDITION) {
											cerr << "beforekill " << placebb[APPEAR][ENEMY][w] << placebb[HIDDEN][ENEMY][w] << killbeforeplaceupbb[aw] << killbeforeplaceunderbb[aw] << mayoccupybb[ENEMY] << ginfo.eneoccbb;
										}
#endif
										break;
									}
								}
							}
						}
#ifdef RECORDACTION
						if (DEBUGRECCONDITION) {
							cerr << " mul " << ginfo.curehyoukamul[ALLY][aw] << endl;
						}
#endif

						// 殺した場合の治療ターンの評価値の倍率が0の場合は、殺さない場合と同じ評価になるの採用しない
						if (ginfo.curehyoukamul[ALLY][aw] != 0) {
							// 殺した場合の治療ターンの評価値が通常の場合は、殺さない場合の評価値は影響しないのでαβの枝狩をしても良い
							if (ginfo.curehyoukamul[ALLY][aw] != HYOUKA_CUREMUL_NORMAL) {
								canusealphabeta = false;
							}
							cankill[aw] = true;
							killnum++;
						}
						hyoukamul[aw] = ginfo.curehyoukamul[ALLY][aw];
					}
					ginfo.mayoccupybb[ENEMY] = bbbak;
				}

#ifdef RECORDACTION
				if (killnum > 1) {
					if (DEBUGRECCONDITION) {
						cerr << "killnum " << killnum << " ";
					}
				}
#endif			
				// 殺さない場合の評価をまず行う。
				double notkillhyouka;
				ginfo = *this;
				//#ifdef DEBUG
				//				cerr << " turn " << static_cast<int>(ginfo.turn) << " ene " << i << endl;
				//#endif
#ifdef RECORDACTION
				ginfo.rec_pl[turn] = w + 3;
				ginfo.rec_ac[turn] = 0;
#endif
				// この時に、他の敵が移動できていた場合、この敵は逃げれる可能性があるので、移動できていた敵を撃破したときの評価を変更する
				// todoこれで良い？
				for (int ew = 0; ew < 3; ew++) {
					if (w != ew && ginfo.sstates[ENEMY][ew].done == false && ginfo.sstates[ENEMY][ew].recovery == 0) {
						ginfo.curehyoukamul[ENEMY][ew] *= HYOUKA_CUREMUL_ENECANMOVE;
					}
				}
				// 行動したことにする
				ginfo.sstates[ENEMY][w].done = true;
				ginfo.preveneplacepopcnt[w] = ginfo.placebb[ALL][ENEMY][w].popcnt();
				// 敵の存在可能な場所を設定する
				ginfo.placebb[APPEAR][ENEMY][w] = ginfo.canmovebb[ginfo.actionnum[ENEMY][w]][APPEAR][ENEMY][w];
				ginfo.placebb[HIDDEN][ENEMY][w] = ginfo.canmovebb[ginfo.actionnum[ENEMY][w]][HIDDEN][ENEMY][w];
				ginfo.placebb[ALL][ENEMY][w] = ginfo.canmovebb[ginfo.actionnum[ENEMY][w]][ALL][ENEMY][w];
				// 占領したかもしれない場所を記録
				ginfo.eneoccbb |= ginfo.canattackbb[ginfo.actionnum[ENEMY][w]][ENEMY][w];
				ginfo.actionnum[ENEMY][w]++;
				ginfo.actionflag[ENEMY][w] = true;
				ginfo.nextturn();
				if (canusealphabeta) {
					notkillhyouka = ginfo.simulate(maxturn, alpha, beta);
				}
				else {
					notkillhyouka = ginfo.simulate(maxturn, HYOUKA_MIN, HYOUKA_MAX);
				}
#ifdef RECORDACTION
				if (DEBUGRECCONDITION) {
					cerr << "  te " << (int)turn << " h " << notkillhyouka << " a " << alpha << " b " << beta;
					if (notkillhyouka < beta) {
						cerr << " min";
					}
					cerr << " cankill ";
					for (int aw = 0; aw < 3; aw++) {
						if (cankill[aw]) {
							cerr << aw << " ";
						}
					}
					cerr << endl;
				}
#endif
				if (notkillhyouka < beta) {
					beta = notkillhyouka;
					if (alpha >= beta) {
						return alpha;
					}
				}

				double killhyouka[3];
				// 殺せる場合の評価値を計算する
				for (int aw = 0; aw < 3; aw++) {
					ginfo = *this;
					if (cankill[aw] == true) {
						assert(ginfo.placebb[ALL][ENEMY][w].popcnt() > 0);
						ginfo.curehyoukamul[ALLY][aw] = hyoukamul[aw];
#ifdef RECORDACTION
						ginfo.rec_pl[turn] = w + 3;
						ginfo.rec_ac[turn] = aw + 1;
#endif
						// 殺した場合は、殺すことができる場所に顕現状態で存在できる。todo：隠蔽状態ではとりあえず存在しないことにするが、実際には存在できるはず！
						// todo: 殺すということは占領しているはず
						ginfo.placebb[APPEAR][ENEMY][w] = killbb[aw];
						ginfo.placebb[HIDDEN][ENEMY][w].clear();
						ginfo.placebb[ALL][ENEMY][w] = killbb[aw];
						ginfo.kill(ALLY, aw);
						ginfo.sstates[ENEMY][w].done = true;
						ginfo.actionflag[ENEMY][w] = true;
						ginfo.actionnum[ENEMY][w] = 0;
						// この時に、他の敵が移動できていた場合、他の敵は逃げれる可能性があるので、移動できていた敵を撃破したときの評価を変更する
						for (int ew = 0; ew < 3; ew++) {
							if (w != ew && ginfo.sstates[ENEMY][ew].done == false && ginfo.sstates[ENEMY][ew].recovery == 0) {
								ginfo.curehyoukamul[ENEMY][ew] *= HYOUKA_CUREMUL_ENECANMOVE;
							}
						}
						// 場所が新たに確定したのでこの敵を撃破したときの評価を初期値に戻す
						ginfo.curehyoukamul[ENEMY][w] = HYOUKA_CUREMUL_NORMAL;
						ginfo.nextturn();
						// 次の行動で攻撃可能な場所と、移動可能な場所を計算しなおす
						ginfo.calccanmoveandattackbb(ginfo.placebb[APPEAR][ENEMY][w], ginfo.placebb[HIDDEN][ENEMY][w], ginfo.actionnum[ENEMY][w], ENEMY, w);
						// 枝かりはしない状態で評価を計算する
						killhyouka[aw] = ginfo.simulate(maxturn, HYOUKA_MIN, HYOUKA_MAX);					
					}
				}
				// 評価値を計算する
				for (int aw = 0; aw < 3; aw++) {
					if (cankill[aw] == true) {
						hyouka = 0;
						if (killnum == 1) {
							hyouka = (killhyouka[aw] * hyoukamul[aw] + notkillhyouka * (HYOUKA_CUREMUL_NORMAL - hyoukamul[aw])) / HYOUKA_CUREMUL_NORMAL;
						}
						else if (killnum == 2) {
							int aw2;
							for (aw2 = 0; aw2 < 3; aw2++) {
								if (aw != aw2 && cankill[aw2] == true) {
									double hyouka2 = (killhyouka[aw2] * hyoukamul[aw2] + notkillhyouka * (HYOUKA_CUREMUL_NORMAL - hyoukamul[aw2])) / HYOUKA_CUREMUL_NORMAL;
									hyouka = (killhyouka[aw] * hyoukamul[aw] + hyouka2 * (HYOUKA_CUREMUL_NORMAL - hyoukamul[aw])) / HYOUKA_CUREMUL_NORMAL;
									//#ifdef RECORDACTION
									//									if (DEBUGRECCONDITION) {
									//										cerr << "  kill 2 " << killnum << "," << aw << "," << aw2 << "," << hyouka2 << "," << hyouka << endl;
									//										cerr << notkillhyouka << "," << killhyouka[aw] << "," << killhyouka[aw2] << "," << hyoukamul[aw] << "," << hyoukamul[aw2] << endl;
									//									}
									//#endif
									break;
								}
							}
						}
						else {
							int aw2[2];
							aw2[0] = (aw == 0) ? 1 : 0;
							aw2[1] = (aw == 2) ? 1 : 2;
							double hyouka2[2];
							hyouka2[0] = (killhyouka[aw2[1]] * hyoukamul[aw2[1]] + notkillhyouka * (HYOUKA_CUREMUL_NORMAL - hyoukamul[aw2[1]])) / HYOUKA_CUREMUL_NORMAL;
							hyouka2[1] = (killhyouka[aw2[0]] * hyoukamul[aw2[0]] + hyouka2[0] * (HYOUKA_CUREMUL_NORMAL - hyoukamul[aw2[0]])) / HYOUKA_CUREMUL_NORMAL;
							hyouka = (killhyouka[aw] * hyoukamul[aw] + hyouka2[1] * (HYOUKA_CUREMUL_NORMAL - hyoukamul[aw])) / HYOUKA_CUREMUL_NORMAL;
							//#ifdef RECORDACTION
							//							if (DEBUGRECCONDITION) {
							//								cerr << "  kill 3 " << killnum << "," << aw << "," << aw2[0] << "," << aw2[1] << "," << hyouka2[0] << "," << hyouka2[1] << "," << hyouka << endl;
							//								cerr << notkillhyouka << "," << killhyouka[aw] << "," << killhyouka[aw2[0]] << "," << killhyouka[aw2[1]] << "," << hyoukamul[aw] << "," << hyoukamul[aw2[0]] << "," << hyoukamul[aw2[1]] << endl;
							//							}
							//#endif

						}
#ifdef RECORDACTION
						if (DEBUGRECCONDITION) {
							cerr << "  te " << (int)turn << " k " << killnum << " h " << hyouka << " a " << alpha << " b " << beta;
							if (hyouka < beta) {
								cerr << " min";
							}
							cerr << endl;
						}
#endif
						if (hyouka < beta) {
							beta = hyouka;
							if (alpha >= beta) {
								return alpha;
							}
						}
					}
				}
			}
		}
		if (!actionflag) {
			ginfo = *this;
#ifdef RECORDACTION
			ginfo.rec_pl[turn] = -1;
			ginfo.rec_ac[turn] = -1;
#endif
			ginfo.nextturn();
			hyouka = ginfo.simulate(maxturn, alpha, beta);
#ifdef RECORDACTION
			if (DEBUGRECCONDITION) {
				cerr << "  pe " << (int)turn << " h " << hyouka << " a " << alpha << " b " << beta;
				if (hyouka < beta) {
					cerr << " min";
				}
				cerr << endl;
			}
#endif
			if (hyouka < beta) {
				beta = hyouka;
				if (alpha >= beta) {
					return alpha;
				}
			}
		}
		return beta;
	}
}

int canattackandmovecount1 = 0;
int canattackandmovecount2 = 0;

// 指定したプレーヤーがt回行動後に攻撃可能な場所を表す BitBoard を計算する
void GameInfo::calccanmoveandattackbb(BitBoard upbb, BitBoard downbb, const int t, const int pl, const int weapon) {
	assert(t >= 0 && t < 2 && pl >= 0 && pl < 2 && weapon >= 0 && weapon < 3);
	BitBoard& abb = canattackbb[t][pl][weapon];
	abb.clear();
	BitBoard& apbb = canattackplacebb[t][pl][weapon];
	apbb.clear();
	BitBoard& bbup = canmovebb[t][APPEAR][pl][weapon];
	BitBoard& bbunder = canmovebb[t][HIDDEN][pl][weapon];
	bbup.clear();
	bbunder.clear();

	BitBoard canmoveup, canmoveunder, canarriveup, canarriveunder;
	canmoveup = ~(appearplbb | cannotenterbb[pl][weapon]);
	canmoveunder = BitBoard::andnot(cannotenterbb[pl][weapon], mayoccupybb[pl]);

	HashData3 h3(upbb, downbb, canmoveup, canmoveunder, pl, weapon);
	size_t hashvalue = h3.calchash();
	if (moveandattackbbmap.count(hashvalue) == 1) {
		apbb = moveandattackbbmap[hashvalue][0];
		abb = moveandattackbbmap[hashvalue][1];
		bbup = moveandattackbbmap[hashvalue][2];
		bbunder = moveandattackbbmap[hashvalue][3];
		canmovebb[t][ALL][pl][weapon] = bbup | bbunder;
		canattackandmovecount2++;
	}
	else {
		for (auto pos : upbb) {
			calccanarriveplace(canmoveup, canmoveunder | attackbb[weapon][4][pos.getpos()], pos, canarriveup, canarriveunder, 1);
			apbb |= canarriveup;
			bbunder |= canarriveunder;
			calccanarriveplace(canmoveup, canmoveunder, pos, canarriveup, canarriveunder);
			bbup |= canarriveup;
			bbunder |= canarriveunder;
		}
		for (auto pos : downbb) {
			calccanarriveplace(canmoveunder, canmoveup, pos, canarriveunder, canarriveup, 1);
			apbb |= canarriveup;
			calccanarriveplace(canmoveunder, canmoveup, pos, canarriveunder, canarriveup);
			bbup |= canarriveup;
			bbunder |= canarriveunder;
		}
		for (auto pos : apbb) {
			abb |= attackbb[weapon][4][pos.getpos()];
		}
		moveandattackbbmap[hashvalue][0] = apbb;
		moveandattackbbmap[hashvalue][1] = abb;
		moveandattackbbmap[hashvalue][2] = bbup;
		moveandattackbbmap[hashvalue][3] = bbunder;
		canmovebb[t][ALL][pl][weapon] = bbup | bbunder;
		canattackandmovecount1++;
	}
}

int ec1 = 0;
int ec2 = 0;

// 次のターンへ進める処理
void GameInfo::nextturn() {
	turn++;
	bool newperiod = (turn % 6) == 0 ? true : false;
	for (int pl = 0; pl < 2; pl++) {
		for (int w = 0; w < 3; w++) {
			// 治療状態の場合、治療ターンを一つ減らす
			// ただし、最終ターンを越えた場合は、hyouka の中でゲーム終了直前の治療状態を知りたいので治療ターンを減らさない
			if (turn < 96 && sstates[pl][w].recovery > 0) {
				sstates[pl][w].recovery--;
			}
			// 新しいピリオドの場合、行動済フラグを落とす
			if (newperiod) {
				sstates[pl][w].done = false;
			}
		}
	}
	// 敵の視界内の可能性がある場所を計算しなおす
	calcenesikaibb();
}

// 敵の視界内の可能性がある場所を計算する
void GameInfo::calcenesikaibb() {
	enesikaibb.clear();
	// 敵の存在可能な場所の合計
	BitBoard ebb = placebb[ALL][ENEMY][0] | placebb[ALL][ENEMY][1] | placebb[ALL][ENEMY][2];
	// ハッシュ値を計算する
	size_t ehash = fnv_1_hash_64((uint8_t *)&ebb, sizeof(BitBoard));
	// 置換表に登録されていればそのデータを使う
	if (enesikaimap.count(ehash) == 1) {
		enesikaibb = enesikaimap[ehash];
		ec2++;
	}
	else {
		// 登録されていなければ計算する
		for (auto pos : ebb) {
			enesikaibb |= canseebb[pos.getpos()];
		}
		enesikaimap[ehash] = enesikaibb;
		ec1++;
	}
}

void GameInfo::calccanmoveandattackall() {
	for (int pl = 0; pl < 2; pl++) {
		for (int weapon = 0; weapon < 3; weapon++) {
			calccanmoveandattack2(pl, weapon);
		}
	}
}

inline void GameInfo::calccanmoveandattack2(const int pl, const int weapon) {
	calccanmoveandattackbb(placebb[APPEAR][pl][weapon], placebb[HIDDEN][pl][weapon], 0, pl, weapon);
	calccanmoveandattackbb(canmovebb[0][APPEAR][pl][weapon], canmovebb[0][HIDDEN][pl][weapon], 1, pl, weapon);
}

// 敵の位置を分析する
void GameInfo::analyze(GameInfo& previnfo) {
#ifdef DEBUGMSG
	cerr << "Turn: " << static_cast<int>(turn) << " analyze start." << endl;
#endif
	// 味方の位置の設定
	for (int w = 0; w < 3; w++) {
		placebb[APPEAR][ALLY][w].clear();
		placebb[HIDDEN][ALLY][w].clear();
		if (!sstates[ALLY][w].hidden) {
			placebb[APPEAR][ALLY][w].set(sstates[ALLY][w].pos);
		}
		else {
			placebb[HIDDEN][ALLY][w].set(sstates[ALLY][w].pos);
		}
		placebb[ALL][ALLY][w] = placebb[APPEAR][ALLY][w] | placebb[HIDDEN][ALLY][w];
	}

	// 現在未占領状態のマスは、過去も未占領状態のはずなので、さかのぼって更新する
	for (int t = 0; t < turn; t++) {
		for (int i = 0; i < 10; i++) {
			if (i == neutralindex) {
				records.occupybb[t][i] |= records.occupybb[turn][neutralindex];
			}
			else {
				records.occupybb[t][i] = BitBoard::andnot(records.occupybb[turn][neutralindex], records.occupybb[t][i]);
			}
		}
	}

	// 前のターンに行動した可能性のある敵を計算する
	// 前のターンに行動した可能性のある敵を表すビット列（最下位ビットから順に武器IDが 0,1,2の敵キャラクターを表す）
	uint32_t eneactionbit = 0;

	// 0 ターン目は前のターンが存在しないので、誰も行動していないのでなにもしない
	if (turn == 0) {
	}
	// ピリオドの先頭のターンの場合
	else if (turn % 6 == 0) {
		// 前のターンで行動可能な敵が行動した可能性がある。治療中の敵がいた場合、複数の敵が行動可能だった場合がある点に注意
		for (int w = 0; w < 3; w++) {
			if (!previnfo.sstates[ENEMY][w].done && previnfo.sstates[ENEMY][w].recovery == 0) {
				eneactionbit |= (1 << w);
			}
		}
	}
	// ピリオドの先頭の次のターンの場合、ピリオドが変わったのでこのターンに行動済の敵が行動した
	else if (turn % 6 == 1) {
		for (int w = 0; w < 3; w++) {
			// ただし、前のターンに治療中であったり、このターンに治療中であった場合は行動できないので除く
			// 治療中であっても 2 0 のような行動を相手が出力すると、行動済になるという仕様のようなので、recovery もチェックしないど駄目！
			if (sstates[ENEMY][w].done && sstates[ENEMY][w].recovery == 0 && previnfo.sstates[ENEMY][w].recovery == 0) {
				eneactionbit |= (1 << w);
				break;
			}
		}
	}
	// それ以外の場合、前のターンの敵の行動と今のターンの敵の行動を比較すれば、どの敵が行動したかがわかる
	else {
		for (int w = 0; w < 3; w++) {
			// 前のターンに行動しておらず、このターンに行動済であればその敵が行動したはず。
			// 治療中であっても 2 0 のような行動を相手が出力すると、行動済になるという仕様のようなので、recovery もチェックしないど駄目！
			if (!previnfo.sstates[ENEMY][w].done && sstates[ENEMY][w].done && sstates[ENEMY][w].recovery == 0 && previnfo.sstates[ENEMY][w].recovery == 0) {
				eneactionbit |= (1 << w);
			}
		}
		// 先頭ターン以外の場合は、必ず行動した敵が特定できるはずなので、popcnt は 0 か 1 になるはず
		assert(POPCNTU32(eneactionbit) <= 1);
	}

	// 現在の視界を計算し、記録する
	visibilitybb.clear();
	for (int w = 0; w < 3; w++) {
		visibilitybb |= canseebb[sstates[ALLY][w].pos.getpos()];
	}
	records.visibilitybb[turn] = visibilitybb;

	// 前のターン
	int prevturn = (turn > 0) ? turn - 1 : 0;

	// 敵の攻撃によって味方が死んだかどうかのチェック
	bool allykilled = false;
	// 味方が死んだときにいた場所(複数の味方が同時に死亡する場合があるので、BitBoardで表現する
	BitBoard deadallybb;
	deadallybb.clear();
	// 複数の敵が行動した可能性がある場合は、どちらの敵の攻撃で死んだかを限定するのは困難なのでチェックしない（todo:なんとかする？）
	if (POPCNTU32(eneactionbit) == 1) {
		for (int w = 0; w < 3; w++) {
			// 治療時間が、治療期間 の場合は、前のターンの敵の攻撃で殺されたことを意味する
			// 同時に複数の味方が殺される可能性もあるので、breakはしない
			if (sstates[ALLY][w].recovery == recoveryTurns - 1) {
				allykilled = true;
				//enemyattacked = true;
				deadallybb.set(previnfo.sstates[ALLY][w].pos);
				// そのマスの色を敵の色に変える
				records.board[turn].set(previnfo.sstates[ALLY][w].pos, (eneactionbit == 1) ? 3 : (eneactionbit == 2) ? 4 : 5);
			}
		}
	}

	for (int w = 0; w < 3; w++) {
		// 各敵キャラクターの最後の記録
		EneRecord& erecord = records.enerecord[w].back();
		// このターンに行動していない敵に関しては、敵が見えていなくても、存在可能な場所が1か所で顕現状態であるのであれば、それを appearplbb に追加する
		if (!(eneactionbit & (1 << w)) && sstates[ENEMY][w].hidden == true && erecord.eneplacebb[APPEAR].popcnt() == 1 && erecord.eneplacebb[HIDDEN].popcnt() == 0) {
			appearplbb |= erecord.eneplacebb[APPEAR];
			appearenemybb |= erecord.eneplacebb[APPEAR];
		}
		// 敵が行動していれば、新しい記録を追加する。
		if (eneactionbit & (1 << w)) {
			records.addnewenerecord(turn, w);
		}
	}

	// 各敵の最後の記録の情報が更新されたかどうかを表すフラグ
	bool enerecordchanged[3] = { false, false, false };

	// 敵の居場所が新たに判明した場合は、最後の記録の一部を修正し、記録が変化したことにして場所の推測を行うことにする。
	// 敵が治療期間中であった場合は、殺されて場所が移動した可能性があるので除く
	for (int w = 0; w < 3; w++) {
		EneRecord& erecord = records.enerecord[w].back();
		if (sstates[ENEMY][w].recovery == 0 && sstates[ENEMY][w].pos != UNKNOWN_POS && erecord.mustplacepos != sstates[ENEMY][w].pos) {
			erecord.mustplacepos = sstates[ENEMY][w].pos;
			erecord.eneplacebb[APPEAR].clear();
			erecord.eneplacebb[APPEAR].set(sstates[ENEMY][w].pos);
			erecord.eneplacebb[HIDDEN].clear();
			erecord.eneplacebb[ALL] = erecord.eneplacebb[APPEAR];
			// 記録が更新されたのでフラグを立てる
			enerecordchanged[w] = true;
		}
	}

	// 記録を計算しなおす（前のターンの味方の行動を考慮に入れるため）
	recalculaterecords(false);

	// このターンの出現しているプレーヤーの位置を記録する
	records.appearplbb[turn] = appearplbb;
	records.appearallybb[turn] = appearallybb;
	records.appearenemybb[turn] = appearenemybb;

	// 視界内の各マスの確認できる最後の占領状態が、更新されたかどうかを調べる
	for (auto p : Pos()) {
		// 現在のマスの占領状況
		uint8_t occ = records.board[turn].get(p);

		// 視界外以外の場合で、そのマスの占領の状況が変化していた場合
		if (occ != 9 && occ != records.lastoccupyplnum[prevturn].get(p)) {
#ifdef DEBUG
			if (DEBUGANALYZECONDITION) {
				cerr << "occ " << static_cast<int>(occ) << "," << static_cast<int>(records.lastoccupyplnum[prevturn].get(p)) << "," << static_cast<int>(records.lastoccupyturn[prevturn].get(p)) << " " << p << endl;
			}
#endif
			// 味方、未占領の場合は、味方の占領行動は完全に把握できるので本来はありえないが、AIのバージョンが変わるなどの状況で
			// AIが導き出した行動と異なる行動を取っていた場合などではありうる。その場合は警告を出力しておき、飛ばす
			if (occ < 3 || occ == 8) {
				cerr << "warning!! 予期しない味方の占領状態の変化." << endl;
				cerr << "occ " << prevturn << " " << static_cast<int>(occ) << "," << static_cast<int>(records.lastoccupyplnum[prevturn].get(p)) << "," << static_cast<int>(records.lastoccupyturn[prevturn].get(p)) << " " << p << endl;
#ifdef DEBUGRTIME
				rtime[turn] = 160;
#endif
				continue;
			}
			// その敵が必ず行動したはずなので、敵の記録が更新されたことにする
			enerecordchanged[occ - 3] = true;
		}
	}

	// 敵の記録が更新された敵に対して、過去の記録から現在のその敵の状況を分析する
	// 敵の記録の深さが深いと分析に時間がかかり、制限時間を超える可能性があるので、反復深化で実行する
	// 1 ターンずつ推測すると組み合わせが爆発して処理時間がかかりすぎるので、各敵プレーヤーをそれぞれ独立して推測する

	// それぞれの敵の位置の推測が終了したかどうか。
	bool analyzecompleted[3] = { false, false, false };

	//vector<EneRecord>::iterator lastit[3], itend[3];
	EneRecord *itbegin[3], *itend[3], *itstart[3];	// 一番最初の記録、イテレータの終了条件、分析の起点となる記録をそれぞれ表すイテレータ
	for (int w = 0; w < 3; w++) {
		itbegin[w] = records.enerecord[w].begin();
		itend[w] = records.enerecord[w].end();
		// 最後の記録のイテレータ（記録は必ず一つは入っているはず)
		assert(itbegin[w] != itend[w]);
		// 分析の起点となる記録を、最後の記録に設定する
		itstart[w] = itend[w] - 1;
		// 実際の分析は、起点となる記録の次の記録から行う。そのため、最後の記録の前があれば、それを起点とする
		if (itstart[w] != itbegin[w]) {
			itstart[w]--;
		}
	}
	// すべての敵の位置の分析が終了するまで繰り返す
	while (!(analyzecompleted[0] & analyzecompleted[1] & analyzecompleted[2])) {
		for (int w = 0; w < 3; w++) {
			// 敵の記録が更新された場合か、敵が行動していた場合に計算する
			if (!analyzecompleted[w] && (enerecordchanged[w] || (eneactionbit & (1 << w)))) {
#ifdef DEBUG
				if (DEBUGANALYZECONDITION) {
					if (enerecordchanged[w]) {
						cerr << "enerecord changed " << w << " turn " << static_cast<int>(turn) << endl;
					}
					if (eneactionbit & (1 << w)) {
						cerr << "enemy action " << w << " turn " << static_cast<int>(turn) << endl;
					}
				}
#endif
				// 最新の敵の記録
				auto& lastrecord = records.enerecord[w].back();
				// 分析の起点となる記録の次の記録から先を初期化する
				for (auto it = itstart[w] + 1; it != itend[w]; ++it) {
					// 時間切れになった場合に備えて、存在可能な場所に関してはバックアップを取っておく
					for (int i = 0; i < 3; i++) {
						it->eneplacebbbak[i] = it->eneplacebb[i];
						it->eneplacebb[i].clear();
					}
					it->mayoccupybbbak = it->mayoccupybb;
					it->occupiedbbbak = it->occupiedbb;
					it->mayoccupybb.clear();
					it->occupiedbb.clear();
					it->occupiedbb = ~it->occupiedbb;
					it->mustoccupybb.clear();
					it->mustoccupybythisturnbb.clear();
				}
				// 敵が行動していた場合の処理
				if (eneactionbit & (1 << w)) {
					// 味方がこのターンに死んでいれば、このターンに敵はその場所を攻撃していなければならないので、敵の最後の記録の、このターンに占領していなければならない場所に設定する
					if (allykilled) {
						lastrecord.mustoccupyinthisturnbb |= deadallybb;
					}
				}
				// 占領しなければならない場所と、このターンまでに占領しなければならない場所を計算する
				// mustoccupybb と mustoccupybythisturnbb を計算する
				// （分析の結果、これらの値は変化する可能性があるので、毎回計算しなおす）
				// 推測を開始する次のターンから今のターンまで、確認できる占領状態が更新されていれば、mustoccupybb と mustoccupybythisturnbb を更新する

				// 確認する必要がある最初のターン（推測の起点となるターン）。これ以前の情報は考慮しない
				int firstturn = (itstart[w])->turn;
				// 起点となる次の記録から最後まで繰り返す
				for (auto it = itstart[w] + 1; it != itend[w]; ++it) {
					// it の記録のターンから、次の記録の一つ前の敵のターン（次の記録がなければ最後のターン）までくり返す
					for (int t = it->turn; t < ((it + 1 != itend[w]) ? (it + 1)->turn : turn + 1); t += 2) {
						for (auto p : Pos()) {
							// 視界内の各マスの確認できる最後の占領状態が、更新されたかどうかを調べる
							// ターン t のマスの占領状況
							uint8_t occ = records.board[t].get(p);

							// これはデバッグ用。
							if (occ != 9 && occ != records.lastoccupyplnum[t - 1].get(p)) {
								// 味方、未占領の場合は、味方の占領行動は完全に把握できるので本来はありえないが、AIのバージョンが変わるなどの状況で
								// AIが導き出した行動と異なる行動を取っていた場合などではありうる。その場合は警告を出力しておき、飛ばす
								if (occ < 3 || occ == 8) {
									cerr << "warning!! 予期しない味方の占領状態の変化." << endl;
									cerr << "occ " << t - 1 << " " << static_cast<int>(occ) << "," << static_cast<int>(records.lastoccupyplnum[t - 1].get(p)) << "," << static_cast<int>(records.lastoccupyturn[t - 1].get(p)) << " " << p << endl;
									cerr << records.lastoccupyplnum[t - 1];
#ifdef DEBUGRTIME
									rtime[turn] = 160;
#endif
								}
							}

							// 視界外以外の場合で、そのマスの確認できる最後の占領状況が調べている敵の占領とは異なり、このターンに調べている敵が占領していた場合
							if (occ == w + 3 && occ != records.lastoccupyplnum[t - 1].get(p)) {
								// そのマスの前の占領状態を確認できる最後のターンを計算する
								int lastturn = records.lastoccupyturn[t - 1].get(p);
#ifdef DEBUG
								if (DEBUGANALYZECONDITION) {
									cerr << "occ2 " << t << "," << firstturn << "," << lastturn << "," << static_cast<int>(occ) << "," << static_cast<int>(records.lastoccupyplnum[t - 1].get(p)) << " " << p << endl;
								}
#endif
								// 推測を開始する記録のターンより前の場合は、推測より前に変化している可能性があるので捨てる
								if (lastturn >= firstturn) {
									// この記録までに、その場所を占領している必要がある
									it->mustoccupybythisturnbb.set(p);
									// 記録をさかのぼって、占領しなければならない場所を記録する
									auto it2 = it;
									while (1) {
										// 確認できる最後のターンより後のターンの記録を更新する
										if (lastturn < it2->turn) {
											it2->mustoccupybb.set(p);
										}
										else {
											break;
										}
										if (it2 == itstart[w] + 1) {
											break;
										}
										it2--;
									}
								}
							}
						}
					}
				}

				// 敵の存在可能な場所の上と下
				BitBoard eneplaceup    = records.eneplacebb[itstart[w]->turn][APPEAR][w];
				BitBoard eneplaceunder = records.eneplacebb[itstart[w]->turn][HIDDEN][w];
				// 敵の場所の計算を行う関数を呼び出す。場所が確定している記録から推測する。次の記録がなければ何もする必要はないので終了
				c1 = c2 = c3 = 0;// c4 = 0;
				// 分析の中で、同じ状況の分析が行われた際に何度も同じ処理を行わなくて済むために置換表として使う analyzemap をクリアする
				analyzemap.clear();
#ifdef DEBUG
				if (debuganalyze) {
					cerr << "start estimate enemy " << w << " place. turn " << static_cast<int>(turn) << " start turn " << itstart[w]->turn << " size " << (itend[w] - itstart[w] - 1) << endl;
				}
#endif

				// 最後の記録であれば、分析は終了。そうでなければ分析を行う関数を呼び出す
				if (itstart[w] + 1 == itend[w] || calceneplace(w, eneplaceup, eneplaceunder, itstart[w]->mayoccupybb, ZERO_BB, itstart[w] + 1, itend[w])) {
					// 時間切れだった場合は分析をここで打ち切る。ここに来ることはまずないはず？
					if (timer.gettime() >= analyzetimelimit) {
#ifdef DEBUGMSG
						cerr << "c1 " << w << "," << c1 << "," << c2 << "," << c3 << "," << c4 << " size " << (itend[w] - itstart[w] - 1) << endl;
						cerr << "analyze time over " << timer.gettime() << endl;
#endif
						//for (auto it = itstart[w] + 1; it != itend[w]; ++it) {
						//	// 時間切れになった場合はバックアップからデータを復帰する
						//	it->eneplacebb[0] = it->eneplacebbbak[0];
						//	it->eneplacebb[1] = it->eneplacebbbak[1];
						//	it->eneplacebb[2] = it->eneplacebbbak[2];
						//	it->mayoccupybb = it->mayoccupybbbak;
						//	it->occupiedbb = it->occupiedbbbak;
						//}
						analyzecompleted[w] = true;
					}
					else {
#ifdef DEBUG
						if (debuganalyze) {
							cerr << "c1 " << w << "," << c1 << "," << c2 << "," << c3 << "," << c4 << " size " << (itend[w] - itstart[w] - 1) << endl;
							cerr << "estimate completed." << endl;
						}
#endif
						for (auto& e : records.enerecord[w]) {
							// 確実に占領した場所が初期状態のままならば確実に占領されている場所は存在しない
							if ((~e.occupiedbb).iszero()) {
								e.occupiedbb.clear();
							}
#ifdef DEBUG
							if (DEBUGANALYZECONDITION) {
								cerr << "turn " << e.turn << endl;
								vector<string> captions = { "eneup", "eneunder" , "mayoccupy", "mustoccupy", };
								vector<BitBoard> bbs = { e.eneplacebb[APPEAR], e.eneplacebb[HIDDEN], e.mayoccupybb, e.occupiedbb };
								dumpbitboardhorizontal(captions, bbs);
							}
#endif
						}
						// 一番最初、または、場所が確定している記録からの推測が行われた場合は、推測を完了する（それより前まで遡って推測しても精度は上がらないので）
						if (itstart[w] == itbegin[w] || itstart[w]->mustplacepos != UNKNOWN_POS) {
#ifdef DEBUG
							cerr << "analyze " << w << " completed. " << c1 << "," << c2 << "," << c3 << "," << c4 << " from " << (itstart[w] - 1)->turn << " to " << (itend[w] - 1)->turn << " size " << (itend[w] - itstart[w] - 1) << endl;
#endif
							analyzecompleted[w] = true;
						}
						itstart[w]--;
					}
				}
				else {
					// 分析が失敗した場合
					// 時間切れの場合
					if (timer.gettime() >= analyzetimelimit) {
						atimeovercount++;
						cerr << "analyze time over " << timer.gettime() << endl;
					}
					else {
						// 分析が失敗すること自体がおかしいので、ここにはこないはず！（来たら何かがバグっている）
						cerr << "error!! estimate failed!! " << endl;
#ifdef DEBUGRTIME
							rtime[turn] = 190;
#endif
					}
					// いずれにせよ、失敗したのでバックアップからデータを復帰する
					for (auto it = itstart[w] + 1; it != itend[w]; ++it) {
						it->eneplacebb[APPEAR] = it->eneplacebbbak[APPEAR];
						it->eneplacebb[HIDDEN] = it->eneplacebbbak[HIDDEN];
						it->eneplacebb[ALL] = it->eneplacebbbak[ALL];
						it->mayoccupybb = it->mayoccupybbbak;
						it->occupiedbb = it->occupiedbbbak;
					}
					// 分析を終了したことにする
					analyzecompleted[w] = true;
				}
			}
			else {
				// 分析をする必要がない場合は、分析を終了したことにする
				analyzecompleted[w] = true;
			}
#ifdef DEBUG
			// 分析用：一回分の分析しかしないフラグが立っている場合は、分析を終了したことにする
			if (analyzeonlyoneaction) {
				analyzecompleted[w] = true;
			}
#endif
		}
	}

	// ここから先は敵の行動を推測し終わった後に行う必要がある
	for (int w = 0; w < 3; w++) {
		// 敵が前の味方のターン(2ターン前)に殺された場合は記録を追加する
		if (sstates[ENEMY][w].recovery == recoveryTurns - 2) {
			//cerr << "killed ! " << i << "," << turn << endl;
			records.addnewenerecord(turn, w);
			EneRecord& erecord = records.enerecord[w].back();
			// 本拠地にいるはず
			erecord.mustplacepos = homepos[ENEMY][w];
			erecord.eneplacebb[APPEAR].clear();
			erecord.eneplacebb[APPEAR].set(homepos[ENEMY][w]);
			erecord.eneplacebb[HIDDEN].clear();
			erecord.eneplacebb[ALL] = erecord.eneplacebb[APPEAR];
			// 治療状態とする
			erecord.recovery = true;
		}
	}

	// 記録内のすべての enemayoccupybb を計算しなおす
	recalculaterecords(true);

	// 分析が終わったので、味方、敵の占領しているかもしれない場所に分析結果を反映させる
	mayoccupybb[ALLY] = records.occupybb[turn][allyindex];
	mayoccupybb[ENEMY] = records.enemayoccupybb[turn][6];
	// 敵の存在可能な場所を更新する
	for (int w = 0; w < 3; w++) {
		placebb[APPEAR][ENEMY][w] = records.eneplacebb[turn][APPEAR][w];
		placebb[HIDDEN][ENEMY][w] = records.eneplacebb[turn][HIDDEN][w];
	}

	// それぞれのプレーヤーが存在可能な場所の BitBoard を計算する
	for (int pl = 0; pl < 2; pl++) {
		for (int w = 0; w < 3; w++) {
			placebb[ALL][pl][w] = placebb[APPEAR][pl][w] | placebb[HIDDEN][pl][w];
		}
	}
	// 敵の視界内の可能性がある場所を計算しなおす
	calcenesikaibb();
	// それぞれのキャラクターに対して、2回分、移動、攻撃可能な場所をあらかじめ計算しておく
	calccanmoveandattackall();

#ifdef DEBUG
	// 分析結果をデバッグ表示する
	if (debuganalyzeresult) {		// 占領状態が不明な場所を計算する
		BitBoard unknownbb;
		unknownbb.clear();
		for (int y = 0; y < height; y++) {
			for (int x = 0; x < width; x++) {
				Pos p(x, y);
				if (turn != records.lastoccupyturn[turn].get(p)) {
					unknownbb.set(p);
				}
			}
		}
		cerr << "Turn " << static_cast<int>(turn) << " analyze." << endl;
		cerr << "enemy action: ";
		for (int w = 0; w < 3; w++) {
			if (eneactionbit & (1 << w)) {
				cerr << w << " ";
			}
		}
		cerr << endl;
		{
			vector<string> captions;
			vector<BitBoard> bbs;
			for (int w = 0; w < 3; w++) {
				ostringstream oss;
				if (eneactionbit & (1 << w)) {
					oss << "敵[" << w << "]の範囲 ";
				}
				else {
					oss << "敵 " << w << " の範囲 ";
				}
				oss << records.eneplacebb[turn][ALL][w].popcnt();
				epopcnt[w][APPEAR][turn] = records.eneplacebb[turn][APPEAR][w].popcnt();
				epopcnt[w][HIDDEN][turn] = records.eneplacebb[turn][HIDDEN][w].popcnt();
				epopcnt[w][ALL][turn] = records.eneplacebb[turn][ALL][w].popcnt();
				captions.push_back(oss.str());
				bbs.push_back(records.eneplacebb[turn][APPEAR][w]);
				bbs.push_back(records.eneplacebb[turn][HIDDEN][w]);
			}
			dumpbitboardhorizontal(captions, bbs, 1);
		}
		{
			cerr << "レアケースを除いた存在範囲" << endl;
			vector<string> captions;
			vector<BitBoard> bbs;
			for (int w = 0; w < 3; w++) {
				ostringstream oss;
				if (eneactionbit & (1 << w)) {
					oss << "敵[" << w << "]の範囲 ";
				}
				else {
					oss << "敵 " << w << " の範囲 ";
				}
				BitBoard bbup = records.eneplacebb[turn][APPEAR][w];
				BitBoard bbunder = records.eneplacebb[turn][HIDDEN][w];
				int period = turn / 6 + ((sstates[ENEMY][w].done) ? 1 : 0);
				if (period > 15) {
					period = 15;
				}
				for (int y = 0; y < height; y++) {
					for (int x = 0; x < width; x++) {
						Pos pos(x, y);
						if (periodplaceintb[period][1 - playOrder][w].get(pos) < periodplacemaxnum / 256) {
							bbup.reset(pos);
							bbunder.reset(pos);
						}
					}
				}
				oss << (bbup | bbunder).popcnt();
				captions.push_back(oss.str());
				bbs.push_back(bbup);
				bbs.push_back(bbunder);
			}
			dumpbitboardhorizontal(captions, bbs, 1);
		}
		{
			vector<string> captions = { "敵の占領可能性", "敵の視界可能性" , "占領状態不明" };
			vector<BitBoard> bbs = { mayoccupybb[ENEMY], enesikaibb, enesikaibb };
			dumpbitboardhorizontal(captions, bbs);
		}
	}
	if (debuganalyzepast) {
		// 過去の敵の存在範囲
		for (int w = 0; w < 3; w++) {
			{
				vector<string> captions;
				vector<BitBoard> bbs;
				cerr << "敵 " << w << " の過去の存在可能範囲" << endl;
				for (const auto& e : records.enerecord[w]) {
					ostringstream oss;
					oss << "Turn " << e.turn;
					captions.push_back(oss.str());
					bbs.push_back(e.eneplacebb[APPEAR]);
					bbs.push_back(e.eneplacebb[HIDDEN]);
				}
				dumpbitboardhorizontal(captions, bbs, 1);
			}
			{
				cerr << "敵 " << w << " の過去の占領したかもしれない範囲" << endl;
				vector<string> captions;
				vector<BitBoard> bbs;
				for (const auto& e : records.enerecord[w]) {
					ostringstream oss;
					oss << "Turn " << e.turn;
					captions.push_back(oss.str());
					bbs.push_back(e.mayoccupybb);
				}
				dumpbitboardhorizontal(captions, bbs);
			}
			{
				cerr << "敵 " << w << " の過去の占領した範囲" << endl;
				vector<string> captions;
				vector<BitBoard> bbs;
				for (const auto& e : records.enerecord[w]) {
					ostringstream oss;
					oss << "Turn " << e.turn;
					captions.push_back(oss.str());
					bbs.push_back(e.occupiedbb);
				}
				dumpbitboardhorizontal(captions, bbs);
			}

		}
		cerr << "確認できる最後の占領状態から変化した場所" << endl;
		cerr << "lastoccupyturn " << endl;
		cerr << records.lastoccupyturn[turn];
		cerr << "lastoccupyplnum " << endl;
		cerr << records.lastoccupyplnum[turn];
	}
#endif
}

// eneplacebb はコピーして使うので、 & はつけない
// 敵の位置を推測する。うまくいった場合は true、いかなかった場合は false を返す
// weapon: 位置を推測する敵の武器
// eneplaceup, eneplaceunder: 敵の存在可能な場所。うまくいった場合は、その中で実際に存在可能な場所を記録して返す
// mayoccupybb: これまでの行動で占領したかもしれない場所
// occupybb: これまでの行動で占領した場所
// itstart: 現在分析している敵の記録のイテレータ
// itend:   分析している敵の記録のイテレータの end
//bool GameInfo::calceneplace(const int weapon, BitBoard& eneplaceup, BitBoard& eneplaceunder, BitBoard mayoccupybb, BitBoard occupybb, const vector<EneRecord>::iterator itstart, const vector<EneRecord>::iterator itend) {
bool GameInfo::calceneplace(const int weapon, BitBoard& eneplaceup, BitBoard& eneplaceunder, BitBoard mayoccupybb, BitBoard occupybb, EneRecord* itstart, EneRecord *itend) {
	// 分析してする記録
	auto& e = *itstart;
	// 前のターン
	int prevturn = e.turn - 1;

	// 時間切れの場合は false を返す
	if (timer.gettime() >= analyzetimelimit) {
		return false;
	}

	// この記録が治療中だった場合は、位置が本拠地にワープするので、この記録で推測することはできない。このまま true を返す。
	if (itstart->recovery == true) {
		// 本拠地に移動させる
		e.eneplacebb[APPEAR].clear();
		e.eneplacebb[APPEAR].set(homepos[ENEMY][weapon]);
		e.eneplacebb[HIDDEN].clear();
		e.eneplacebb[ALL] = e.eneplacebb[APPEAR];
		// 占領した場所に関してはバックアップのデータを戻す
		e.mayoccupybb = e.mayoccupybbbak;
		e.occupiedbb = e.occupiedbbbak;
		return true;
	}


#ifdef DEBUG
	if (DEBUGANALYZECONDITION) {
		cerr << "eneplace" << endl;
		cerr << eneplaceup << eneplaceunder;
	}
#endif

	// 占領しなければならない場所などに、このターンに占領しなければならない場所（敵が味方を攻撃した際の、味方の位置）を加える
	e.mustoccupybb |= e.mustoccupyinthisturnbb;
	e.mustoccupybythisturnbb |= e.mustoccupyinthisturnbb;

	// ひとつ前の記録の後のターンから今のターンまでに mayoccupybb と occupybb を自分以外が占領していた場合は更新する
	// eneplaceunder も敵が占領していない場所にはいられないので更新する
	int prevrecordturn = (itstart - 1)->turn;
	// 前の記録が最初の記録だった場合、前のターンを後手の場合は 1 ターンとする
	if (prevrecordturn == 0) {
		prevrecordturn = playOrder;
	}
	for (int t = prevrecordturn + 1; t <= e.turn; t++) {
		// mustoccupybb を除く、他の敵が占領した可能性のある場所を除いておく
		// enemayoccupybb[t][weapon + 3] にはあらかじめ weapon 以外の敵が占領したかもしれない場所が計算済
		occupybb &= BitBoard::andnot(BitBoard::andnot(e.mustoccupybb, records.enemayoccupybb[t][weapon + 3]), (records.occupybb[t][weapon + 3] | records.occupybb[t][unknownindex]));
		// 占領したかもしれない場所は、そのターンにその敵が占領しているか、視界外の場所のいずれかのはず
		mayoccupybb &= (records.occupybb[t][weapon + 3] | records.occupybb[t][unknownindex]);
		// 隠蔽状態でいられるのは、占領したかもしれない場所のみ
		eneplaceunder &= (records.occupybb[t][enemyindex] | records.occupybb[t][unknownindex]);
	}
#ifdef DEBUG
	if (DEBUGANALYZECONDITION) {
		cerr << "eneplace2" << endl;
		cerr << eneplaceup << eneplaceunder;
	}
#endif
	// このターンに占領しなければならない場所を、occupybb から取り除く
	occupybb = BitBoard::andnot(e.mustoccupyinthisturnbb, occupybb);
	// 制限をはみ出る部分は削除する（この制限は分析後の eneplace から算出されたもの）
	eneplaceup &= (itstart - 1)->eneplacelimitbb[APPEAR];
	eneplaceunder &= (itstart - 1)->eneplacelimitbb[HIDDEN];

	// 存在できる場所がなくなった場合は失敗として終了
	if ((eneplaceup | eneplaceunder).iszero()) {
#ifdef DEBUG
		if (DEBUGANALYZECONDITION) {
			cerr << "eneplace is zero" << endl;
			cerr << (itstart - 1)->turn << endl << (itstart - 1)->eneplacelimitbb[APPEAR] << (itstart - 1)->eneplacelimitbb[HIDDEN];
		}
#endif
		return false;
	}

	// 返り値を false に設定しておく。一つでも成功すれば true にする
	bool retval = false;
	// 顕現、隠蔽状態で移動可能な場所の計算。
	BitBoard canmoveup, canmoveunder, canarriveup, canarriveunder;
	// 顕現状態で移動可能な場所は、そのターン（そのターンの記録の appearplbb は、その敵がそのターンに移動した後の情報）ではなく、直前のターンの情報で計算する必要がある
	canmoveup = ~(records.appearplbb[prevturn] | cannotenterbb[ENEMY][weapon]);
	// weapon 以外の占領状態は、記録されているものを使う。weapon の占領状態は mayoccupybb を使う
	canmoveunder = BitBoard::andnot(cannotenterbb[ENEMY][weapon], records.enemayoccupybb[e.turn][weapon + 3] | mayoccupybb);

	// このターンに占領してはいけない場所(自分の占領地または視界外のマス以外の場所)
	BitBoard maynotoccupybb = ~(records.occupybb[e.turn][unknownindex] | records.occupybb[e.turn][weapon + 3]);

	// このターンから、次にこの敵が行動するまでの間、味方が得た視界。その記録での所在地がわかっていない場合は、この視界の中に存在することはできない。
	BitBoard totalvisibilitybb;
	totalvisibilitybb.clear();
	// 最後の記録の場合は、現在のターンが最後のターン。そうでなければ次の記録のターン - 2
	int lastturn = (itstart + 1 == itend) ? turn : (itstart + 1)->turn - 2;
	for (int t = e.turn; t <= lastturn; t += 2) {
		totalvisibilitybb |= records.visibilitybb[t];
	}

#ifdef DEBUG
	if (DEBUGANALYZECONDITION) {
		vector<string> captions = { "must occupy", "must occupybytt", "must occupyintt", "placeup", "placeunder", "canmoveup", "canmoveunder", "mayoccupybb", "maynotoccupy", "occupybb", "totalvisibility", "elimitup", "elimitunder" };
		vector<BitBoard> bbs = { e.mustoccupybb, e.mustoccupybythisturnbb, e.mustoccupyinthisturnbb, eneplaceup, eneplaceunder, canmoveup, canmoveunder, mayoccupybb, maynotoccupybb, occupybb, totalvisibilitybb, e.eneplacelimitbb[APPEAR], e.eneplacelimitbb[HIDDEN] };
		cerr << "erecord turn " << e.turn << " current turn " << static_cast<int>(turn) << endl;
		cerr << "mustplacepos" << e.mustplacepos << endl;
		dumpbitboardhorizontal(captions, bbs);
	}
#endif
	// この5つの条件を使ってこの後計算するので、このハッシュ値が等しければすでに計算済なので置換表のデータを返して終了
	HashData1 h1(eneplaceup, eneplaceunder, mayoccupybb, occupybb, e.turn);
	size_t hashvalue = h1.calchash();
	if (analyzemap.count(hashvalue) == 1) {
		c2++;
		return analyzemap[hashvalue];
	}

	// eneplacebbup, under の中で実際に存在できた場所
	BitBoard totalcanexistupbb, totalcanexistunderbb;
	totalcanexistupbb.clear();
	totalcanexistunderbb.clear();
	// このターンまでに占領しなければならない場所が既に占領済で、このターンに占領しなければならない場所が存在しない場合、移動のみの行動をこのターン行うことが可能
	if (e.mustoccupybythisturnbb.isincluded(occupybb) && e.mustoccupyinthisturnbb.iszero()) {
		// このチェックの中で実際に存在可能だった場所。あとで eneplacexxcanexistbb との or を取る
		BitBoard canexistupbb, canexistunderbb;
		canexistupbb.clear();
		canexistunderbb.clear();
		// 現在存在可能な場所から移動可能な場所を計算し、次の存在可能な場所とする
		// 次の存在可能な場所
		BitBoard nextplaceupbb, nextplaceunderbb;
		nextplaceupbb.clear();
		nextplaceunderbb.clear();
		// 攻撃可能な場所を計算する
		BitBoard canattackbb;
		canattackbb.clear();
		// 以下を配列で表現すると、サイズが大きいのでこの関数を再起呼び出ししすぎると stack overflow になるので、vector で表現する
		// その際、BitBoardは32ビットアライメントに配置しなければならないので、自作のアロケータを使う必要がある
		vector<vector <BitBoard, MyAllocator<BitBoard>>> canmoveplaceupbb(2, vector<BitBoard, MyAllocator<BitBoard>>(Pos::possize));	// (x, y) から行動した後に、顕現状態で存在可能な場所
		vector<vector <BitBoard, MyAllocator<BitBoard>>> canmoveplaceunderbb(2, vector<BitBoard, MyAllocator<BitBoard>>(Pos::possize)); // (x, y) から行動した後に、隠蔽状態で存在可能な場所
		vector<vector <BitBoard, MyAllocator<BitBoard>>> canattackplacebb(2, vector<BitBoard, MyAllocator<BitBoard>>(Pos::possize));	// 各マスに存在した場合に、攻撃を行うことができる場所
		vector<BitBoard, MyAllocator<BitBoard>> canoccupybb(Pos::possize);			// そのマスから占領可能な場所の合計
		// 初期化
		for (auto p: Pos()) {
			int index = p.getpos();
			canmoveplaceupbb[APPEAR][index].clear();
			canmoveplaceupbb[HIDDEN][index].clear();
			canmoveplaceunderbb[APPEAR][index].clear();
			canmoveplaceunderbb[HIDDEN][index].clear();
			canattackplacebb[APPEAR][index].clear();
			canattackplacebb[HIDDEN][index].clear();
			canoccupybb[index].clear();
		}
		// 各マスについて調べる
		// eneplaceup, canmoveup, canmoveunder から nextplaceup, nextplaceunder を計算する
		// e.mustplacepos が UNKNOWN_POS でない場合は canexistupbb も計算する
		// 顕現状態で存在可能なマスすべてを調べる
		for (auto pos : eneplaceup) {
			int index = pos.getpos();
#ifdef DEBUG
			if (donotcalcarriveplacestrictly) {
				calccanarriveplaceapproximate(canmoveup, canmoveunder, pos, canarriveup, canarriveunder);
			}
			else {
#endif
				calccanarriveplace(canmoveup, canmoveunder, pos, canarriveup, canarriveunder);
#ifdef DEBUG
			}
#endif
			nextplaceupbb |= canarriveup;
			nextplaceunderbb |= canarriveunder;
			canmoveplaceupbb[APPEAR][index] |= canarriveup;
			canmoveplaceunderbb[APPEAR][index] |= canarriveunder;
			// 場所が特定されている場合、そこに移動できればこの場所に顕現状態でこのターンが始まった時点で存在可能
			if (e.mustplacepos != UNKNOWN_POS && canarriveup.isset(e.mustplacepos)) {
				canexistupbb.set(pos);
			}

			// 攻撃可能な場所を調べる
			calccanarriveplace(canmoveup, canmoveunder, pos, canarriveup, canarriveunder, 1);
			// このターンでの場所が特定されている場合
			if (e.mustplacepos != UNKNOWN_POS) {
				if (canarriveup.isset(e.mustplacepos)) {
					// この場合は、今いる位置か、特定されている場所で攻撃可能
					canattackplacebb[APPEAR][index].set(pos);
					canattackplacebb[APPEAR][index].set(e.mustplacepos);
					canattackbb.set(pos);
					canattackbb.set(e.mustplacepos);
				}
			}
			else {
				// 特定されていない場合は、視界外の移動可能な場所、または、顕現、隠蔽状態共に移動可能な場所で攻撃可能
				canattackplacebb[APPEAR][index] = BitBoard::andnot(totalvisibilitybb, canarriveup) | (canarriveup & canarriveunder);
				// この場所が上記の条件を満たさない場合（視界内で、隠蔽不可能な場合）でも、上記の条件を満たす場所が存在していれば、攻撃後に確認できない場所に移動できるので、この場所で攻撃可能
				if (!canattackplacebb[APPEAR][index].iszero()) {
					canattackplacebb[APPEAR][index].set(pos);
				}
				canattackbb |= canattackplacebb[APPEAR][index];
			}
		}

		// 隠蔽状態で存在可能なマスすべてを調べる
		for (auto pos : eneplaceunder) {
			int index = pos.getpos();
#ifdef DEBUG
			if (donotcalcarriveplacestrictly) {
				calccanarriveplaceapproximate(canmoveup, canmoveunder, pos, canarriveup, canarriveunder);
			}
			else {
#endif
				calccanarriveplace(canmoveunder, canmoveup, pos, canarriveunder, canarriveup);
#ifdef DEBUG
			}
#endif
			nextplaceupbb |= canarriveup;
			nextplaceunderbb |= canarriveunder;
			canmoveplaceupbb[HIDDEN][index] |= canarriveup;
			canmoveplaceunderbb[HIDDEN][index] |= canarriveunder;
			// 場所が特定されている場合、そこに移動できればこの場所に隠蔽状態でこのターンが始まった時点で存在可能
			if (e.mustplacepos != UNKNOWN_POS && canarriveup.isset(e.mustplacepos)) {
				// この場所に隠蔽状態でこのターンが始まった時点で存在可能
				canexistunderbb.set(pos);
			}

			// 攻撃可能な場所を調べる
			calccanarriveplace(canmoveunder, canmoveup, pos, canarriveunder, canarriveup, 1);
			// このターンでの場所が特定されている場合
			if (e.mustplacepos != UNKNOWN_POS) {
				// まず、その場所に顕現状態で移動可能でなければならない
				if (canarriveup.isset(e.mustplacepos)) {
					// 今いる位置に顕現状態で移動可能であれば、今いる位置で攻撃可能
					if (canarriveup.isset(pos)) {
						canattackplacebb[HIDDEN][index].set(pos);
						canattackbb.set(pos);
					}
					// 特定されている場所では必ず攻撃可能
					canattackplacebb[HIDDEN][index].set(e.mustplacepos);
					canattackbb.set(e.mustplacepos);
				}
			}
			// 特定されていない場合は、視界外の移動可能な場所、または、今いる場所に顕現状態で移動可能であればそこで隠蔽できるので今いる場所で攻撃可能
			else {
				if (canarriveup.isset(pos)) {
					canattackplacebb[HIDDEN][index].set(pos);
				}
				canattackplacebb[HIDDEN][index] |= BitBoard::andnot(totalvisibilitybb, canarriveup);
				canattackbb |= canattackplacebb[HIDDEN][index];
			}
		}

		// 攻撃可能な全範囲
		BitBoard totalattackbb;
		totalattackbb.clear();

		// 攻撃可能な全マスから攻撃可能な場所を調べる
		for (auto pos : canattackbb) {
			int index = pos.getpos();
			// このマスからの可能な攻撃範囲
			BitBoard attackrangebb;
			attackrangebb.clear();
			// 各方向について攻撃を調べる
			for (int dir = 0; dir < 4; dir++) {
				BitBoard& abb = attackbb[weapon][dir][index];
				// そのターンに占領してはいけない場所を占領していなければ、その攻撃を採用する
				if ((abb & maynotoccupybb).iszero()) {
					attackrangebb |= abb;
				}
			}
			// この場所に顕現状態で存在する場合、攻撃したことによって、隣のマスが占領状態になったり、味方が攻撃で排除されることで移動できるようになる場合があるので、それを考慮する
			if (eneplaceup.isset(pos)) {
				for (int i = 0; i < 4; i++) {
					Pos p2 = pos + dist1pos[i];
					// 敵が顕現状態で存在していた場合は移動できない
					if (attackrangebb.isset(p2) && !cannotenterbb[ENEMY][weapon].isset(p2) && !records.appearenemybb[e.turn].isset(p2)) {
						nextplaceupbb.set(p2);
						nextplaceunderbb.set(p2);
						canmoveplaceupbb[APPEAR][index].set(p2);
						canmoveplaceunderbb[APPEAR][index].set(p2);
						// 場所が特定されている場合で、隣がその位置の場合は、この場所に顕現状態でこのターンが始まった時点で存在可能
						if (e.mustplacepos != UNKNOWN_POS && e.mustplacepos == p2) {
							canexistupbb.set(pos);
						}
					}
				}
			}
			// この場所に隠蔽状態で存在する場合で、この場所に顕現状態で移動できる場合、攻撃したことによって隣のマスの味方が攻撃で排除されることで移動できるようになる場合があるので、それを考慮する
			if (eneplaceunder.isset(pos) && canmoveup.isset(pos)) {
				for (int i = 0; i < 4; i++) {
					Pos p2 = pos + dist1pos[i];
					if (attackrangebb.isset(p2) && !cannotenterbb[ENEMY][weapon].isset(p2) && !records.appearenemybb[e.turn].isset(p2)) {
						nextplaceupbb.set(p2);
						canmoveplaceupbb[APPEAR][index].set(p2);
						// 場所が特定されている場合で、隣がその位置の場合は、この場所に顕現状態でこのターンが始まった時点で存在可能
						if (e.mustplacepos != UNKNOWN_POS && e.mustplacepos == p2) {
							canexistunderbb.set(pos);
						}
					}
				}
			}
			totalattackbb |= attackrangebb;
			canoccupybb[index] = attackrangebb;
		}

		// 次の記録がなければこれで終了
		if (itstart + 1 == itend) {
#ifdef DEBUG
			if (DEBUGANALYZECONDITION) {
				cerr << "last attempt move." << endl;
			}
#endif
			// 最後の記録された行動の場合は必ず mustoccupybb == mustoccupybythisturnbb となっているはず
			if (e.mustoccupybb != e.mustoccupybythisturnbb) {
				cerr << "error!!! mustoccupybb != mustoccupybythisturnbb" << endl;
#ifdef DEBUGRTIME
				rtime[turn] = 190;
#endif
			}

			// 最後の場所がわかっていないか、移動可能な場所にその場所が入っている場合はOK
			if (e.mustplacepos == UNKNOWN_POS || nextplaceupbb.isset(e.mustplacepos)) {
				if (e.mustplacepos != UNKNOWN_POS) {
					nextplaceupbb.clear();
					nextplaceupbb.set(e.mustplacepos);
					nextplaceunderbb.clear();
					// この場合、canexistup, under については計算済
				}
				else {
					// 最後の場所がわかっていないということは顕現状態で視界内にはいられない
					nextplaceupbb = BitBoard::andnot(totalvisibilitybb, nextplaceupbb);
					// eneplaceup, eneplaceunder のすべての場所に存在可能
					canexistupbb = eneplaceup;
					canexistunderbb = eneplaceunder;
				}
				// 存在可能な場所がなければ失敗
				if ((nextplaceupbb | nextplaceunderbb).iszero()) {
#ifdef DEBUG
					if (DEBUGANALYZECONDITION) {
						cerr << "no move place." << endl;
					}
#endif
				}
				else {
#ifdef DEBUG
					if (DEBUGANALYZECONDITION) {
						cerr << "occupy completed." << endl;
						cerr << "estimate success!" << endl;
					}
#endif
					// 存在可能な場所を更新する
					e.eneplacebb[APPEAR] |= nextplaceupbb;
					e.eneplacebb[HIDDEN] |= nextplaceunderbb;
					e.eneplacebb[ALL] = e.eneplacebb[APPEAR] | e.eneplacebb[HIDDEN];


					e.mayoccupybb |= mayoccupybb | totalattackbb;
					e.occupiedbb &= occupybb;
					retval = true;
#ifdef DEBUG
					if (DEBUGANALYZECONDITION) {
						vector<string> captions = { "nextup", "nextunder" , "placeup", "placeunder", "eneplaceup", "eneplaceunder", "mayoccupy", "mustoccupy" };
						vector<BitBoard> bbs = { nextplaceupbb, nextplaceunderbb, canexistupbb, canexistunderbb, e.eneplacebb[0], e.eneplacebb[1], e.mayoccupybb, e.occupiedbb };
						dumpbitboardhorizontal(captions, bbs);
					}
#endif
					totalcanexistupbb |= canexistupbb;
					totalcanexistunderbb |= canexistunderbb;
					// 存在可能な場所がなければおかしい。
					if ((canexistupbb | canexistunderbb).iszero()) {
						cerr << "error!!! canexistbb is zero." << endl;
#ifdef DEBUGRTIME
						rtime[turn] = 190;
#endif
					}
					retval = true;
				}
			}
		}
		else {
#ifdef DEBUG
			if (DEBUGANALYZECONDITION) {
				cerr << "try next after move. turn " << e.turn << endl;
			}
#endif
			// 最後の記録以外は、場所がわかっていないはずなので、顕現状態で視界内にはいられないはず
			if (e.mustplacepos != UNKNOWN_POS) {
				cerr << "error!!! mustplacepos is unknown" << endl;
#ifdef DEBUGRTIME
				rtime[turn] = 190;
#endif
			}
			nextplaceupbb = BitBoard::andnot(totalvisibilitybb, nextplaceupbb);
			// 存在可能な場所がなければ失敗
			if ((nextplaceupbb | nextplaceunderbb).iszero()) {
#ifdef DEBUG
				if (DEBUGANALYZECONDITION) {
					cerr << "no move place." << endl;
				}
#endif
			}
			else {
				// 次の行動の記録で処理を続ける
				if (calceneplace(weapon, nextplaceupbb, nextplaceunderbb, mayoccupybb | totalattackbb, occupybb, itstart + 1, itend)) {
					e.mayoccupybb |= mayoccupybb;
					e.eneplacebb[APPEAR] |= nextplaceupbb;
					e.eneplacebb[HIDDEN] |= nextplaceunderbb;
					e.eneplacebb[ALL] = e.eneplacebb[APPEAR] | e.eneplacebb[HIDDEN];
					// todo: これ nextplaceupbb が変化してなかったらこの後計算しなおさなくてもいいんじゃ？
					// nextplaceupbb, underbb に実際に移動可能だった場所が記録されている。このターンに実際に存在可能な場所は、そこへ移動できる場所なのでそれを計算する。
					// 各マスからどこへ移動可能かは計算済なので、それを使って調べる
					// また、このターンに占領可能な状態も計算する
					for (auto pos : eneplaceup) {
						int index = pos.getpos();
						// ここから移動可能な場所に、次の存在可能場所が含まれている場合、この場所に存在可能
						if (!(canmoveplaceupbb[APPEAR][index] & nextplaceupbb).iszero() || !(canmoveplaceunderbb[APPEAR][index] & nextplaceunderbb).iszero()) {
							canexistupbb.set(pos);
							// 存在可能な場所だった場合、pos を含む周囲1マスを調べ、そこで攻撃可能だったかどうかを調べる
							for (int i = 0; i < 5; i++) {
								Pos p2 = pos + dist1pos[i];
								// p2 で攻撃可能な条件は以下の通り
								// p に存在していた時に、p2 で攻撃可能な場合
								// p と p2 が同じか、p2 に顕現状態で移動可能で、p2 が次に存在可能な場所である場合
								// その場合にこのターンに占領可能な場所を追加する
								if (canattackplacebb[APPEAR][index].isset(p2) &&
									(pos == p2 || (canmoveplaceupbb[APPEAR][index].isset(p2) && (nextplaceupbb | nextplaceunderbb).isset(p2)))) {
									e.mayoccupybb |= canoccupybb[p2.getpos()];
								}
							}
						}
					}

					for (auto pos : eneplaceunder) {
						int index = pos.getpos();
						// ここから移動可能な場所に、次の存在可能場所が含まれている場合、この場所に存在可能
						if (!(canmoveplaceupbb[HIDDEN][index] & nextplaceupbb).iszero() || !(canmoveplaceunderbb[HIDDEN][index] & nextplaceunderbb).iszero()) {
							canexistunderbb.set(pos);
							// 存在可能な場所だった場合、pを含む周囲1マスを調べ、そこで攻撃可能だったかどうかを調べる
							for (int i = 0; i < 5; i++) {
								Pos p2 = pos + dist1pos[i];
								// p2 で攻撃可能な条件は以下の通り
								// p に存在していた時に、p2 で攻撃可能な場合
								// p と p2 が同じか、p2 に顕現状態で移動可能かつ存在可能である場合
								// その場合にこのターンに占領可能な場所を追加する
								if (canattackplacebb[HIDDEN][index].isset(p2) && (pos == p2 || (canmoveplaceupbb[HIDDEN][index].isset(p2) && nextplaceupbb.isset(p2)))) {
									e.mayoccupybb |= canoccupybb[p2.getpos()];
								}
							}
						}
					}
					e.occupiedbb &= occupybb;
#ifdef DEBUG
					if (DEBUGANALYZECONDITION) {
						cerr << "try succeed 1. turn " << e.turn << endl;
						vector<string> captions = { "nextup", "nextunder" , "placeup", "placeunder", "eneplaceup", "eneplaceunder", "mayoccupy", "mustoccupy" };
						vector<BitBoard> bbs = { nextplaceupbb, nextplaceunderbb, canexistupbb, canexistunderbb, e.eneplacebb[0], e.eneplacebb[1], e.mayoccupybb, e.occupiedbb };
						dumpbitboardhorizontal(captions, bbs);
					}
#endif
					totalcanexistupbb |= canexistupbb;
					totalcanexistunderbb |= canexistunderbb;
					if ((canexistupbb | canexistunderbb).iszero()) {
						cerr << "error!!! canexist is zero" << endl;
#ifdef DEBUGRTIME
						rtime[turn] = 190;
#endif
					}
					retval = true;
				}
				else {
#ifdef DEBUG
					if (DEBUGANALYZECONDITION) {
						cerr << "try failed after move. turn " << e.turn << endl;
					}
#endif
					// 時間切れで帰ってきた場合は、false を返す
					if (timer.gettime() >= analyzetimelimit) {
						return false;
					}
				}
			}
		}
	}
#ifdef DEBUG
	if (DEBUGANALYZECONDITION) {
		if (retval == false) {
			cerr << "try after move failed. turn " << e.turn << endl;
		}
	}
#endif
	// 占領しなければならない場所がまだ占領済でない場合は、占領しなければならない場所を占領するような攻撃を試みる
	// （mustoccupybb >= mustoccupybythisturnbb なので、この上の条件(e.mustoccupybythisturnbb.isincluded(occupybb))を満たす場合でも、この条件は実行される可能性がある）
	if (!e.mustoccupybb.isincluded(occupybb) || !e.mustoccupyinthisturnbb.iszero()) {
		// このチェックの中で実際に存在可能だった場所。あとで eneplacexxcanexistbb との or を取る
		BitBoard canexistupbb, canexistunderbb;
		canexistupbb.clear();
		canexistunderbb.clear();
		// 攻撃可能な場所を計算する
		BitBoard canattackbb;								// 攻撃可能な場所
		vector<BitBoard, MyAllocator<BitBoard>> canmoveafterattackupbb(Pos::possize);		// (x, y)で攻撃した後に顕現状態で移動可能な場所。先に計算しておく。(x, y) に移動後に攻撃した場合も含む
		vector<BitBoard, MyAllocator<BitBoard>> canmoveafterattackunderbb(Pos::possize);		// (x, y)で攻撃した後に隠蔽状態で移動可能な場所。先に計算しておく。(x, y) に移動後に攻撃した場合も含む
		vector<vector <BitBoard, MyAllocator<BitBoard>>> canattackplacebb(2, vector<BitBoard, MyAllocator<BitBoard>>(Pos::possize));				// (x, y)に最初にいた時に攻撃を行うことができる場所
		vector<vector <BitBoard, MyAllocator<BitBoard>>> canmoveplaceupbb(2, vector<BitBoard, MyAllocator<BitBoard>>(Pos::possize));				// (x, y)から攻撃を含む行動を行った後に、顕現状態で存在可能な場所
		vector<vector <BitBoard, MyAllocator<BitBoard>>> canmoveplaceunderbb(2, vector<BitBoard, MyAllocator<BitBoard>>(Pos::possize));			// (x, y)から攻撃を含む行動を行った後に、隠蔽状態で存在可能な場所
		canattackbb.clear();

		for (auto p : Pos()) {
			int index = p.getpos();
			canmoveafterattackupbb[index].clear();
			canmoveafterattackunderbb[index].clear();
			canattackplacebb[APPEAR][index].clear();
			canattackplacebb[HIDDEN][index].clear();
			canmoveplaceupbb[APPEAR][index].clear();
			canmoveplaceupbb[HIDDEN][index].clear();
			canmoveplaceunderbb[APPEAR][index].clear();
			canmoveplaceunderbb[HIDDEN][index].clear();
		}

		for (auto pos : eneplaceup) {
			int index = pos.getpos();
			// 距離１で移動可能な場所を計算する
			calccanarriveplace(canmoveup, canmoveunder, pos, canarriveup, canarriveunder, 1);
			// 移動可能な顕現状態の場所で攻撃可能。
			canattackbb |= canarriveup;
			// この場所で攻撃後に移動可能な場所は、移動可能な場所に等しい
			canmoveafterattackupbb[index] |= canarriveup;
			canmoveafterattackunderbb[index] |= canarriveunder;
			// 攻撃を含む行動を行った後に移動可能な場所
			canmoveplaceupbb[APPEAR][index] |= canarriveup;
			canmoveplaceunderbb[APPEAR][index] |= canarriveunder;
			// 移動せずにここで攻撃可能
			canattackplacebb[APPEAR][index].set(pos);

			// 隣の場所に顕現状態で移動できる場合は、そこで攻撃後にその場所に顕現状態で移動可能。隠蔽可能なら、隠蔽状態でも移動可能
			// 同時に、ここから移動して、顕現状態で移動できる場所で攻撃可能
			for (int i = 0; i < 4; i++) {
				Pos p2 = pos + dist1pos[i];
				if (canarriveup.isset(p2)) {
					canmoveafterattackupbb[p2.getpos()].set(p2);
					canattackplacebb[APPEAR][index].set(p2);
					if (canarriveunder.isset(p2)) {
						canmoveafterattackunderbb[p2.getpos()].set(p2);
					}
				}
			}
		}
		for (auto pos : eneplaceunder) {
			int index = pos.getpos();
			// 距離１で移動可能な場所を計算する
			calccanarriveplace(canmoveunder, canmoveup, pos, canarriveunder, canarriveup, 1);
			// 移動可能な顕現状態の場所で攻撃可能。
			canattackbb |= canarriveup;
			// この場所で攻撃することができるのは、この場所に顕現状態で移動可能な場合
			if (canarriveup.isset(pos)) {
				// 移動可能な顕現状態の場所に、この場所で攻撃後に移動可能。
				canmoveafterattackupbb[index] |= canarriveup;
				// 今いる場所にはこの場所で攻撃後に隠蔽状態で移動可能
				canmoveafterattackunderbb[index].set(pos);
				// 今いる場所に顕現状態で移動できる場合は、ここから移動して、ここで攻撃可能
				canattackplacebb[HIDDEN][index].set(pos);
			}
			// 攻撃を含む行動を行った後に移動可能な場所
			// 移動可能な顕現状態の場所にそこで攻撃した後に移動可能
			canmoveplaceupbb[HIDDEN][index] |= canarriveup;
			// 今いる場所に顕現状態で移動できる場合は、ここで攻撃後に隠蔽状態で移動可能
			if (canarriveup.isset(pos)) {
				canmoveplaceunderbb[HIDDEN][index].set(pos);
			}

			// 隣の場所に顕現状態で移動できる場合は、そこで攻撃後に、その場所に顕現状態で移動可能
			// 同時に、ここから移動して、顕現状態で移動できる場所で攻撃可能
			for (int i = 0; i < 4; i++) {
				Pos p2 = pos + dist1pos[i];
				if (canarriveup.isset(p2)) {
					canmoveafterattackupbb[p2.getpos()].set(p2);
					canattackplacebb[HIDDEN][index].set(p2);
				}
			}
		}

		for (auto p : canattackbb) {
			int index = p.getpos();
			// 同じ場所を新しく占領する攻撃を複数回チェックしても仕方がないので、記録しておく
			BitBoard changedbb[4], changedbball;
			// すべての方向に攻撃してみる
			for (int dir = 0; dir < 4; dir++) {
				BitBoard& abb = attackbb[weapon][dir][index];
				// 確実に占領した場所を追加する
				BitBoard newoccupiedbb = occupybb | abb;
				// 攻撃によって新しく占領した場所
				changedbb[dir] = BitBoard::andnot(occupybb, abb);
				bool newattack = true;
				// 新しく占領した場所がなければこの攻撃は採用しない
				if (changedbb[dir].iszero()) {
					newattack = false;
				}
				else {
					// 他の方向から攻撃した場合の新しく占領した場所と同じであれば、採用しない
					for (int j = 0; j < dir; j++) {
						if (changedbb[dir] == changedbb[j]) {
							newattack = false;
							break;
						}
					}
				}
				// 以下の条件をすべて満たす場合に、この攻撃を採用する
				// 攻撃した場所がこれまで占領した場所に完全に含まれていない（newattackでチェック）
				// これまに行った攻撃がこのターンまでに占領しなければならない場所をすべて含んでいる。
				// このターンに行った攻撃がこのターンに占領しなければならない場所をすべて含んでいる。
				// これまでに行った攻撃が占領しなければならない場所を含んでいる。
				// このターンに行った攻撃がそのターンに占領してはいけない場所を占領していない。
				if (newattack && e.mustoccupybythisturnbb.isincluded(newoccupiedbb) && e.mustoccupyinthisturnbb.isincluded(abb) && !(e.mustoccupybb & changedbb[dir]).iszero() && (abb & maynotoccupybb).iszero()) {
#ifdef DEBUG
					if (DEBUGANALYZECONDITION) {
						cerr << "attack dir " << dir << " turn " << e.turn << " " << p << endl;
					}
#endif
					BitBoard nextplaceupbb, nextplaceunderbb;
					// ここで攻撃後に移動可能な場所を次の移動可能な場所とする
					nextplaceupbb = canmoveafterattackupbb[index];
					nextplaceunderbb = canmoveafterattackunderbb[index];
					// このマスに、顕現状態で存在可能であり、攻撃範囲のうち、隣の移動可能なマスに敵がいなかった場合（味方は殺されるのでいなくなる）、
					// その隣のマスに顕現、隠蔽状態で移動可能
					if (eneplaceup.isset(p)) {
						for (int i = 0; i < 4; i++) {
							Pos p2 = p + dist1pos[i];
							if (abb.isset(p2) && !cannotenterbb[HIDDEN][weapon].isset(p2) && !records.appearenemybb[e.turn].isset(p)) {
								nextplaceupbb.set(p2);
								nextplaceunderbb.set(p2);
							}
						}
					}
					// このマスに、隠蔽状態で存在可能であり、このマスに顕現することができる場合、攻撃範囲のうち、隣の移動可能なマスに敵がいなかった場合（味方は殺されるのでいなくなる）、
					// その隣のマスに顕現状態で移動可能
					if (eneplaceunder.isset(p) && canmoveup.isset(p)) {
						for (int i = 0; i < 4; i++) {
							Pos p2 = p + dist1pos[i];
							if (abb.isset(p2) && !cannotenterbb[HIDDEN][weapon].isset(p2) && !records.appearenemybb[e.turn].isset(p)) {
								nextplaceupbb.set(p2);
							}
						}
					}
					// 最後の記録の場合はこれで終了
					if (itstart + 1 == itend) {
#ifdef DEBUG
						if (DEBUGANALYZECONDITION) {
							cerr << "last attempt attack." << endl;
						}
#endif
						// 最後の場所がわかっていないか、移動可能な場所にその場所が入っている場合はOK
						if (e.mustplacepos == UNKNOWN_POS || nextplaceupbb.isset(e.mustplacepos)) {
							// 場所がわかっていれば、次の移動可能な場所をそこにセットする
							if (e.mustplacepos != UNKNOWN_POS) {
								nextplaceupbb.clear();
								nextplaceupbb.set(e.mustplacepos);
								nextplaceunderbb.clear();
							}
							else {
								// 最後の場所がわかっていないということは顕現状態で視界内にはいられない
								nextplaceupbb = BitBoard::andnot(totalvisibilitybb, nextplaceupbb);
								// その結果次の移動可能な場所が存在しなくなればこの攻撃は採用しない
								if ((nextplaceupbb | nextplaceunderbb).iszero()) {
#ifdef DEBUG
									if (DEBUGANALYZECONDITION) {
										cerr << "no move place." << endl;
									}
#endif
									continue;
								}
							}
#ifdef DEBUG
							if (DEBUGANALYZECONDITION) {
								cerr << "occupy completed." << endl;
								cerr << "estimate success." << endl;
							}
#endif
							// 存在可能な場所を更新する
							e.eneplacebb[APPEAR] |= nextplaceupbb;
							e.eneplacebb[HIDDEN] |= nextplaceunderbb;
							e.eneplacebb[ALL] = e.eneplacebb[APPEAR] | e.eneplacebb[HIDDEN];
							e.mayoccupybb |= mayoccupybb | abb;
							e.occupiedbb &= newoccupiedbb;

							// このターンの最初に存在可能な場所を探す
							for (auto p2 : eneplaceup) {
								int index2 = p2.getpos();
								if (canattackplacebb[APPEAR][index2].isset(p)) {
									// 攻撃箇所と(x2, y2)が同じ場所だった場合
									if (p == p2) {
										// ここが次の存在箇所と同じ場所であれば、移動可能な場所と、次の存在場所が一致すればここに最初に存在可能
										if (!(canmoveplaceupbb[APPEAR][index2] & nextplaceupbb).iszero() || !(canmoveplaceunderbb[APPEAR][index2] & nextplaceunderbb).iszero()) {
											canexistupbb.set(p2);
										}
										else {
											// 隣を調べる
											for (int i = 0; i < 4; i++) {
												Pos p3 = p2 + dist1pos[i];
												// 隣に味方がいなくて、隣を攻撃していた場合は、隣に顕現、隠蔽状態で移動できる
												if (abb.isset(p3) && !cannotenterbb[ENEMY][weapon].isset(p3) && !records.appearenemybb[e.turn].isset(p3) && (nextplaceupbb | nextplaceunderbb).isset(p3)) {
													canexistupbb.set(p2);
													break;
												}
											}
										}
									}
									// 同じ場所でない場合は、攻撃した場所に顕現状態で移動可能。そこに隠蔽可能なら隠蔽状態で移動可能。
									else {
										if (nextplaceupbb.isset(p) || (canmoveunder.isset(p) && nextplaceunderbb.isset(p))) {
											canexistupbb.set(p2);
										}
									}
								}
							}

							for (auto p2 : eneplaceunder) {
								int index2 = p2.getpos();
								if (canattackplacebb[HIDDEN][index2].isset(p)) {
									// 同じ場所ならその場所に出現して攻撃してから隠蔽状態で移動可能。そこから顕現状態で移動可能な場所に移動可能
									if (p == p2) {
										if (nextplaceunderbb.isset(p2) || !(canmoveplaceupbb[HIDDEN][index2] & nextplaceupbb).iszero()) {
											canexistunderbb.set(p2);
										}
										else {
											// 隣を調べる
											for (int i = 0; i < 4; i++) {
												Pos p3 = p2 + dist1pos[i];
												// 隣に味方がいなくて、隣を攻撃していた場合は、隣に顕現状態で移動できる
												if (abb.isset(p3) && !cannotenterbb[ENEMY][weapon].isset(p3) && !records.appearenemybb[e.turn].isset(p3) && nextplaceupbb.isset(p3)) {
													canexistupbb.set(p2);
													break;
												}
											}
										}
									}
									// 同じ場所でない場合は、攻撃した場所に顕現状態で移動可能
									else {
										if (nextplaceupbb.isset(p)) {
											canexistunderbb.set(p2);
										}
									}
								}
							}
#ifdef DEBUG
							if (DEBUGANALYZECONDITION) {
								vector<string> captions = { "nextup", "nextunder" , "placeup", "placeunder", "eneplaceup", "eneplaceunder", "mayoccupy", "mustoccupy" };
								vector<BitBoard> bbs = { nextplaceupbb, nextplaceunderbb, canexistupbb, canexistunderbb, e.eneplacebb[0], e.eneplacebb[1], e.mayoccupybb, e.occupiedbb };
								dumpbitboardhorizontal(captions, bbs);
							}
#endif
							totalcanexistupbb |= canexistupbb;
							totalcanexistunderbb |= canexistunderbb;
							if ((canexistupbb | canexistunderbb).iszero()) {
								cerr << "error!!! canexist is zero" << endl;
#ifdef DEBUGRTIME
								rtime[turn] = 190;
#endif
							}
							retval = true;
						}
					}
					else {
#ifdef DEBUG
						if (DEBUGANALYZECONDITION) {
							cerr << "try next after attack. turn " << e.turn << endl;
						}
#endif
						// 最後の記録以外は、場所がわかっていないはずなので、顕現状態で視界内にはいられないはず
						if (e.mustplacepos != UNKNOWN_POS) {
							cerr << "error!!! mustplacepos is unknown." << endl;
#ifdef DEBUGRTIME
							rtime[turn] = 190;
#endif
						}
						nextplaceupbb = BitBoard::andnot(totalvisibilitybb, nextplaceupbb);
						// 存在可能な場所がなければ失敗なので次へ
						if ((nextplaceupbb | nextplaceunderbb).iszero()) {
#ifdef DEBUG
							if (DEBUGANALYZECONDITION) {
								cerr << "no move place." << endl;
							}
#endif
							continue;
						}
						// 次の行動の記録で処理を続ける
						if (calceneplace(weapon, nextplaceupbb, nextplaceunderbb, mayoccupybb | abb, newoccupiedbb, itstart + 1, itend)) {
							e.eneplacebb[APPEAR] |= nextplaceupbb;
							e.eneplacebb[HIDDEN] |= nextplaceunderbb;
							e.eneplacebb[ALL] = e.eneplacebb[APPEAR] | e.eneplacebb[HIDDEN];
							// nextplaceupbb, underbb に実際に移動可能だった場所が記録されている。このターンに実際に存在可能な場所は、(x, y)で攻撃した後にそこへ移動できる場所なのでそれを計算する。
#ifdef DEBUG
							if (DEBUGANALYZECONDITION) {
								cerr << "eneplace " << eneplaceup << eneplaceunder << endl;
							}
#endif

							for (auto p2 : eneplaceup) {
								int index2 = p2.getpos();
								if (canattackplacebb[APPEAR][index2].isset(p)) {
									// 同じ場所ならそこから移動可能な場所に移動できる
									if (p == p2) {
										if (!(canmoveplaceupbb[APPEAR][index2] & nextplaceupbb).iszero() || !(canmoveplaceunderbb[APPEAR][index2] & nextplaceunderbb).iszero()) {
											canexistupbb.set(p2);
										}
										else {
											// 隣を調べる
											for (int i = 0; i < 4; i++) {
												Pos p3 = p2 + dist1pos[i];
												// 隣に味方がいなくて、隣を攻撃していた場合は、隣に顕現、隠蔽状態で移動できる
												if (abb.isset(p3) && !cannotenterbb[ENEMY][weapon].isset(p3) && !records.appearenemybb[e.turn].isset(p3) && (nextplaceupbb | nextplaceunderbb).isset(p3)) {
													canexistupbb.set(p2);
													break;
												}
											}
										}
									}
									// 同じ場所でない場合は、攻撃した場所に顕現状態で移動可能。そこに隠蔽可能なら隠蔽状態で移動可能。
									else {
										if (nextplaceupbb.isset(p) || (canmoveunder.isset(p) && nextplaceunderbb.isset(p))) {
											canexistupbb.set(p2);
										}
									}
								}
							}

							for (auto p2 : eneplaceunder) {
								int index2 = p2.getpos();
								// 隠蔽状態の場合
								if (canattackplacebb[HIDDEN][index2].isset(p)) {
									// 同じ場所ならその場所に出現して攻撃してから隠蔽状態で移動可能。そこから顕現状態で移動可能な場所に移動可能
									if (p == p2) {
										if (nextplaceunderbb.isset(p2) || !(canmoveplaceupbb[HIDDEN][index2] & nextplaceupbb).iszero()) {
											canexistunderbb.set(p2);
										}
										else {
											// 隣を調べる
											for (int i = 0; i < 4; i++) {
												Pos p3 = p2 + dist1pos[i];
												// 隣に味方がいなくて、隣を攻撃していた場合は、隣に顕現状態で移動できる
												if (abb.isset(p3) && !cannotenterbb[ENEMY][weapon].isset(p3) && !records.appearenemybb[e.turn].isset(p3) && nextplaceupbb.isset(p3)) {
													canexistupbb.set(p2);
													break;
												}
											}
										}
									}
									// 同じ場所でない場合は、攻撃した場所に顕現状態で移動可能
									else {
										if (nextplaceupbb.isset(p)) {
											canexistunderbb.set(p2);
										}
									}
								}
							}
							e.mayoccupybb |= mayoccupybb | abb;
							e.occupiedbb &= newoccupiedbb;
#ifdef DEBUG
							if (DEBUGANALYZECONDITION) {
								cerr << "try end after attack. turn " << e.turn << endl;
								vector<string> captions = { "nextup", "nextunder" , "placeup", "placeunder", "eneplaceup", "eneplaceunder", "mayoccupy", "mustoccupy" };
								vector<BitBoard> bbs = { nextplaceupbb, nextplaceunderbb, canexistupbb, canexistunderbb, e.eneplacebb[0], e.eneplacebb[1], e.mayoccupybb, e.occupiedbb };
								dumpbitboardhorizontal(captions, bbs);
							}
#endif
							totalcanexistupbb |= canexistupbb;
							totalcanexistunderbb |= canexistunderbb;
							if ((canexistupbb | canexistunderbb).iszero()) {
								cerr << "error!!! canexist is zero" << endl;
#ifdef DEBUGRTIME
								rtime[turn] = 190;
#endif
							}
							retval = true;
						}
						else {
#ifdef DEBUG
							if (DEBUGANALYZECONDITION) {
								cerr << "try failed after attack. turn " << e.turn << endl;
							}
#endif
							// 時間切れで帰ってきた場合は、false を返す
							if (timer.gettime() >= analyzetimelimit) {
								return false;
							}
						}
					}
				}
			}
		}
	}
#ifdef DEBUG
	if (DEBUGANALYZECONDITION) {
		if (retval == false) {
			cerr << "failed." << endl;
		}
	}
#endif
	// 実際に存在可能だった場所を更新する
	eneplaceup = totalcanexistupbb;
	eneplaceunder = totalcanexistunderbb;

	// 置換表に結果を登録する
	analyzemap[hashvalue] = retval;

	c1++;

	return retval;
}

// 記録の情報を計算しなおす
void GameInfo::recalculaterecords(const bool updatelimit) {
	// 各敵の記録のイテレータ、itend は end を表す
	//vector<EneRecord>::iterator it[3], itend[3];;
	EneRecord *it[3], *itend[3];;
	for (int w = 0; w < 3; w++) {
		it[w] = records.enerecord[w].begin();
		itend[w] = records.enerecord[w].end();
	}
	// 最初の味方のターンから、現在のターンまで、順番に記録を更新する
	for (int t = playOrder; t <= turn; t++) {
		// まず、敵のターンの記録による更新
		// enemayoccupybb の初期化
		for (int i = 0; i < 7; i++) {
			records.enemayoccupybb[t][i].clear();
		}
		// 0 ターン目以外の場合
		if (t != 0) {
			// ターン t の記録の一部に t - 1 のものをコピーする
			for (int w = 0; w < 3; w++) {
				records.enemayoccupybb[t][w] = records.enemayoccupybb[t - 1][w];
				records.eneplacebb[t][APPEAR][w] = records.eneplacebb[t - 1][APPEAR][w];
				records.eneplacebb[t][HIDDEN][w] = records.eneplacebb[t - 1][HIDDEN][w];
				records.eneplacebb[t][ALL][w]    = records.eneplacebb[t - 1][ALL][w];
			}
			records.lastoccupyplnum[t] = records.lastoccupyplnum[t - 1];
			records.lastoccupyturn[t] = records.lastoccupyturn[t - 1];
		}

		// 各マスについて、視界が 9（視界外）以外の場合、そのマスの確認できる最後の状況を更新する
		for (auto p : Pos()) {
			uint8_t occ = records.board[t].get(p);
			// 視界外（９）以外の場合
			if (occ != 9) {
				records.lastoccupyturn[t].set(p, t);
				records.lastoccupyplnum[t].set(p, occ);
			}
		}

		// ターン t に敵キャラクターの記録があれば更新する
		for (int w = 0; w < 3; w++) {
			// 次の記録のターンが t と同じであれば進める。it[w]をターン t 以下の最初の記録に設定する
			while ((it[w] + 1) != itend[w] && (it[w] + 1)->turn == t) {
				it[w]++;
			}
			// 記録がターン t と同じであれば、その記録を反映する
			if (it[w]->turn == t) {
				// 現在味方が占領している場所または中立な場所は占領不可なので更新する
				// 本選提出AIは下の行のようになっており、味方が占領している場所は考慮していなかった
#ifdef DEBUG
				if (submitversion) {
#endif
					it[w]->mayoccupybb = BitBoard::andnot(records.occupybb[turn][neutralindex], it[w]->mayoccupybb);
#ifdef DEBUG
				}
				else {
					it[w]->mayoccupybb = BitBoard::andnot(records.occupybb[turn][allyindex] | records.occupybb[turn][neutralindex], it[w]->mayoccupybb);
				}
#endif
				// 隠蔽状態で存在可能なのは、敵が占領しているかもしれない場所に限定される
#ifdef DEBUG
				if (!donotuseanalyzeresultinrecalculaterecords) {
#endif
					it[w]->eneplacebb[HIDDEN] &= (it[0]->mayoccupybb | it[1]->mayoccupybb | it[2]->mayoccupybb);
#ifdef DEBUG
				}
#endif
				// 場所の制限を更新する。この作業は分析が終わってから行う
				if (updatelimit) {
					it[w]->eneplacelimitbb[APPEAR] &= it[w]->eneplacebb[APPEAR];
					it[w]->eneplacelimitbb[HIDDEN] &= it[w]->eneplacebb[HIDDEN];
				}
				// 存在可能な場所と、占領した可能性のある場所を記録にコピーする
				records.eneplacebb[t][APPEAR][w] = it[w]->eneplacebb[APPEAR];
				records.eneplacebb[t][HIDDEN][w] = it[w]->eneplacebb[HIDDEN];
				records.eneplacebb[t][ALL][w] = it[w]->eneplacebb[APPEAR] | it[w]->eneplacebb[HIDDEN];
				records.enemayoccupybb[t][w] = it[w]->mayoccupybb;

				EneRecord& e = *it[w];
				// 確実に占領された場所の情報を更新する
				// なお、分析中に一度も攻撃をしなかった場合は、occupiedbb のビットはすべて立っているので、それも除く必要がある
#ifdef DEBUG
				if (!(~e.occupiedbb).iszero() && !e.occupiedbb.iszero() && !donotuseanalyzeresultinrecalculaterecords) {
#else
				if (!(~e.occupiedbb).iszero() && !e.occupiedbb.iszero()) {
#endif
					for (int i = 0; i < 10; i++) {
						if (i == w + 3 || i == enemyindex) {
							records.occupybb[t][i] |= e.occupiedbb;
						}
						else {
							records.occupybb[t][i] = BitBoard::andnot(e.occupiedbb, records.occupybb[t][i]);
						}
					}
					// 他の敵キャラクターの占領していた可能性のある場所から、このキャラクターが必ず攻撃した場所を削除する
					for (int ow = 0; ow < 3; ow++) {
						if (w != ow) {
							records.enemayoccupybb[t][ow] = BitBoard::andnot(e.occupiedbb, records.enemayoccupybb[t][ow]);
						}
					}
					for (auto pos : e.occupiedbb) {
						// そのマスの確認できる最後の占領状態を変える
						records.board[t].set(pos, w + 3);
						records.lastoccupyplnum[t].set(pos, w + 3);
						records.lastoccupyturn[t].set(pos, t);
					}
				}
			}

			// 現在味方が占領している場所を、そのキャラクターが占領しているかもしれない場所から排除する
			records.enemayoccupybb[t][w] = BitBoard::andnot(records.occupybb[t][allyindex], records.enemayoccupybb[t][w]);
			// 場所がわかっていない場合は、ターン t の視界内の顕現状態の存在可能な場所を削除する
			if (it[w]->mustplacepos == UNKNOWN_POS) {
				records.eneplacebb[t][APPEAR][w] =  BitBoard::andnot(records.visibilitybb[t], records.eneplacebb[t][APPEAR][w]);
				records.eneplacebb[t][ALL][w] = records.eneplacebb[t][APPEAR][w] | records.eneplacebb[t][HIDDEN][w];
			}
		}
		// すべての敵の処理が終了したら、敵の占領したかもしれない場所について、後の処理を軽減するための計算を行っておく
		records.enemayoccupybb[t][3] = records.enemayoccupybb[t][1] | records.enemayoccupybb[t][2];
		records.enemayoccupybb[t][4] = records.enemayoccupybb[t][0] | records.enemayoccupybb[t][2];
		records.enemayoccupybb[t][5] = records.enemayoccupybb[t][0] | records.enemayoccupybb[t][1];
		records.enemayoccupybb[t][6] = records.enemayoccupybb[t][0] | records.enemayoccupybb[t][1] | records.enemayoccupybb[t][2];

		// 分析前で、現在のターンでない場合の処理（分析前は、現在のターンの情報をまだ計算していないので、この処理を行うことはできない）
		if (!(updatelimit == false && turn == t)) {
			// すべての場所について調べる
			for (auto pos : Pos()) {
				// 確認できる最後のターンが前のターンで、その場所を敵が占領した可能性がなければ、その場所は前のターンのままであるはず
				if (!records.enemayoccupybb[t][6].isset(pos) && records.lastoccupyturn[t].get(pos) == t - 1) {
					records.lastoccupyturn[t].set(pos, t);
					int occ = records.lastoccupyplnum[t].get(pos);
					records.board[t].set(pos, occ);
					// そのターンの占領状況を更新する
					for (int i = 0; i < 10; i++) {
						if (occ == i || (occ < 3 && i == allyindex) || (occ >= 3 && occ < 6 && i == enemyindex)) {
							records.occupybb[t][i].set(pos);
						}
						else {
							records.occupybb[t][i].reset(pos);
						}
					}
				}
			}
		}
		// 味方のターンの行動の反映
		// ターンを増やす
		t++;
		// 現在のターンを越えていた場合は終了する
		if (t > turn) {
			break;
		}
		// ターン t の記録の一部に t - 1 のものをコピーする
		for (int w = 0; w < 3; w++) {
			records.enemayoccupybb[t][w] = records.enemayoccupybb[t - 1][w];
			records.eneplacebb[t][APPEAR][w] = records.eneplacebb[t - 1][APPEAR][w];
			records.eneplacebb[t][HIDDEN][w] = records.eneplacebb[t - 1][HIDDEN][w];
			records.eneplacebb[t][ALL][w]    = records.eneplacebb[t - 1][ALL][w];
		}
		records.lastoccupyplnum[t] = records.lastoccupyplnum[t - 1];
		records.lastoccupyturn[t] = records.lastoccupyturn[t - 1];

		// そのターンに攻撃した味方がいれば、その行動を記録に反映させる
		int w = records.allyattackplnum[t];
		if (w >= 0) {
			// 占領状況を更新する
			for (int i = 0; i < 10; i++) {
				if (i == w || i == allyindex) {
					records.occupybb[t][i] |= records.allyattackbb[t];
				}
				else {
					records.occupybb[t][i] = BitBoard::andnot(records.allyattackbb[t], records.occupybb[t][i]);
				}
			}
			// 他のプレーヤーの占領していた可能性の場る場所と、存在可能な場所を更新する
			for (int ew = 0; ew < 3; ew++) {
				records.enemayoccupybb[t][ew] = BitBoard::andnot(records.allyattackbb[t], records.enemayoccupybb[t][ew]);
				records.eneplacebb[t][APPEAR][ew] = BitBoard::andnot(records.allyattackbb[t], records.eneplacebb[t][APPEAR][ew]);
				records.eneplacebb[t][HIDDEN][ew] = BitBoard::andnot(records.allyattackbb[t], records.eneplacebb[t][HIDDEN][ew]);
				records.eneplacebb[t][ALL][ew] = records.eneplacebb[t][APPEAR][ew] | records.eneplacebb[t][HIDDEN][ew];
			}
		}
		// すべてのマスについて調べる
		for (auto pos : Pos()) {
			// そのマスを攻撃していれば、マスの占領状況と、確認できる最後の情報を更新する
			if (w >= 0 && records.allyattackbb[t].isset(pos)) {
				records.board[t].set(pos, w);
				records.lastoccupyplnum[t].set(pos, w);
				records.lastoccupyturn[t].set(pos, t);
			}
			// そのマスを攻撃していない場合は、そのマスが視界内の場合は確認できる最後のターンを更新する
			// 視界外の場合は、確認できる最後のターンが前のターンの場合は、変化していないはずだから更新する
			else if (!records.occupybb[t][unknownindex].isset(pos) || records.lastoccupyturn[t].get(pos) == t - 1) {
				records.lastoccupyturn[t].set(pos, t);
				int occ = records.lastoccupyplnum[t].get(pos);
				records.board[t].set(pos, occ);
				for (int i = 0; i < 10; i++) {
					if (occ == i || (occ < 3 && i == allyindex) || (occ >= 3 && occ < 6 && i == enemyindex)) {
						records.occupybb[t][i].set(pos);
					}
					else {
						records.occupybb[t][i].reset(pos);
					}
				}
			}
		}
		// 敵の占領したかもしれない場所について、後の処理を軽減するための計算を行っておく
		records.enemayoccupybb[t][3] = records.enemayoccupybb[t][1] | records.enemayoccupybb[t][2];
		records.enemayoccupybb[t][4] = records.enemayoccupybb[t][0] | records.enemayoccupybb[t][2];
		records.enemayoccupybb[t][5] = records.enemayoccupybb[t][0] | records.enemayoccupybb[t][1];
		records.enemayoccupybb[t][6] = records.enemayoccupybb[t][0] | records.enemayoccupybb[t][1] | records.enemayoccupybb[t][2];
	}
}

void IntBoard::clear(const int num) {
	for (int i = 0; i < Pos::possize; i++) {
		data[i] = num;
	}
//	memset(data, num, Pos::possize * sizeof(int));
}

void IntBoard::set(const Pos p, const int setdata) {
	data[p.getpos()] = setdata;
}

void IntBoard::setifmax(const Pos p, const int setdata) {
	if (data[p.getpos()] < setdata) {
		data[p.getpos()] = setdata;
	}
}


int IntBoard::get(const Pos p) const {
	return data[p.getpos()];
}

ostream& operator<<(ostream& os, const IntBoard& ib) {
	os << "      0    1    2    3    4    5    6    7    8    9   10   11   12   13   14" << endl;
	for (int y = 0; y < height; y++) {
		os << setw(2) << y << " ";
		for (int x = 0; x < width; x++) {
			os << setw(4) << ib.data[x + y * 16] << " ";
		}
		os << endl;
	}
	return os;
}

void Records::init(const uint8_t porder) {
	lastoccupyturn[0].clear(0);
	lastoccupyplnum[0].clear(8);
	board[0].clear(8);

	// 0 ターン目のこれらの情報は使わないのでクリアしておく
	appearplbb[0].clear();
	appearallybb[0].clear();
	appearenemybb[0].clear(); // なかった
	appearenemybb[0] = ~appearenemybb[0];
	for (int i = 0; i < 7; i++) {
		enemayoccupybb[0][i].clear();
	}
	visibilitybb[0].clear();
	allyattackplnum[0] = -1; // なかった
	allyattackbb[0].clear();//なかった


	for (int i = 0; i < 3; i++) {
		enemayoccupybb[0][i].set(homepos[1][i]);
		enemayoccupybb[0][6].set(homepos[1][i]);
		visibilitybb[0] |= canseebb[homepos[0][i].getpos()];
		board[0].set(homepos[0][i], i);
		board[0].set(homepos[1][i], i + 3);
	}
	enemayoccupybb[0][3] = enemayoccupybb[0][1] | enemayoccupybb[0][2];
	enemayoccupybb[0][4] = enemayoccupybb[0][0] | enemayoccupybb[0][2];
	enemayoccupybb[0][5] = enemayoccupybb[0][0] | enemayoccupybb[0][1];
	for (int i = 0; i < 6; i++) {
		occupybb[0][i].clear();
		if (i < 6) {
			occupybb[0][i].set(homepos[static_cast<int>(floor(i / 3))][i % 3]);
		}
	}
	occupybb[0][allyindex] = occupybb[0][0] | occupybb[0][1] | occupybb[0][2];
	occupybb[0][enemyindex] = occupybb[0][3] | occupybb[0][4] | occupybb[0][5];
	occupybb[0][neutralindex] = ~(occupybb[0][allyindex] | occupybb[0][enemyindex]) & visibilitybb[0];
	occupybb[0][unknownindex] = ~visibilitybb[0];

	for (int w = 0; w < 3; w++) {
		BitBoard canmovebb;
		enerecord[w].clear();
		addnewenerecord(0, w);
		EneRecord& erecord = enerecord[w].front();
		erecord.eneplacebb[APPEAR].clear();
		erecord.eneplacebb[APPEAR].set(homepos[ENEMY][w]);
		erecord.eneplacebb[HIDDEN].clear();
		erecord.eneplacebb[ALL] = erecord.eneplacebb[APPEAR];
		erecord.eneplacelimitbb[APPEAR].clear();
		erecord.eneplacelimitbb[APPEAR] = ~erecord.eneplacelimitbb[APPEAR];
		erecord.eneplacelimitbb[HIDDEN].clear();
		erecord.eneplacelimitbb[HIDDEN] = ~erecord.eneplacelimitbb[HIDDEN];
		erecord.mustoccupybb.clear();
		erecord.mustoccupybythisturnbb.clear();
		erecord.mustoccupyinthisturnbb.clear();
		erecord.mayoccupybb = erecord.eneplacebb[APPEAR];
		erecord.occupiedbb.clear();
		erecord.recovery = false;
		erecord.mustplacepos = homepos[ENEMY][w];
		eneplacebb[0][APPEAR][w] = erecord.eneplacebb[APPEAR];
		eneplacebb[0][HIDDEN][w] = erecord.eneplacebb[HIDDEN];
		eneplacebb[0][ALL][w] = erecord.eneplacebb[ALL];
		for (int p = 0; p < 2; p++) {
			lastoccupyplnum[0].set(homepos[p][w], p * 3 + w);
		}
	}
	turn = 0;
}

void Records::addnewenerecord(const int turn, const int weapon) {
	EneRecord e;
	e.turn = turn;
	// 存在可能な場所として、入れるすべての場所を入れておく
	e.eneplacebb[APPEAR] = ~cannotenterbb[ENEMY][weapon];
	e.eneplacebb[HIDDEN] = e.eneplacebb[APPEAR];
	e.eneplacebb[ALL] = e.eneplacebb[APPEAR];
	// 存在可能な場所の制限として、すべての場所を設定しておく
	e.eneplacelimitbb[APPEAR].clear();
	e.eneplacelimitbb[APPEAR] = ~e.eneplacelimitbb[APPEAR];
	e.eneplacelimitbb[HIDDEN] = e.eneplacelimitbb[APPEAR];
	// 占領しなければならない場所に関する BitBoard の初期化
	e.mustoccupybb.clear();
	e.mustoccupybythisturnbb.clear();
	e.mustoccupyinthisturnbb.clear();
	e.mayoccupybb.clear();
	// 占領した場所にすべての場所を設定しておく（後でANDをとって狭めていくので）
	e.occupiedbb.clear();
	e.occupiedbb = ~e.occupiedbb;
	// 必ず存在しなければならない場所を不明な場所にしておく
	e.mustplacepos = UNKNOWN_POS;
	// 治療中ではないことにしておく
	e.recovery = false;
	// 記録があれば mayoccupybb は最新の記録のものをコピーする
	if (enerecord[weapon].size() > 0) {
		e.mayoccupybb = records.enerecord[weapon].back().mayoccupybb;
	}
	// 新しく作成した記録を最後に追加する
	enerecord[weapon].push_back(e);
}

void setactiontable(int actionvalue, Pos dest, bool changed, int direction, unordered_map<int, size_t>& actionsindextable, vector<Action>& actions) {
	Action action(actionvalue, dest, changed);
	action.rotate(direction);
	actionsindextable[action.getactionvalue()] = actions.size();
	actions.push_back(action);
}

// actionvalue で指定した行動を反時計回りに direction で回転した行動を movetable に登録する
void setmovetable(int actionvalue, int direction, uint64_t& aindextable, unordered_map<int, size_t>& avitable) {
	// 行動を
	Action action(actionvalue);
	// 回転する
	action.rotate(direction);
	aindextable |= (static_cast<uint64_t>(1) << avitable[action.getactionvalue()]);
}

void dumpbitboardhorizontal(vector<string>& caption, vector<BitBoard>& bb, int type) {
	// キャプションの表示
	for (auto its = caption.begin();  its != caption.end(); ++its) {
		cerr << setw(16) << *its;
	}
	cerr << endl;
	for (auto itb = bb.begin(); itb != bb.end(); ++itb) {
		cerr << " 0123456789ABCDE";
		if (type == 1) {
			++itb;
		}
	}
	cerr << endl;
	for (int y = 0; y < height; y++) {
		for (auto itb = bb.begin(); itb != bb.end(); ++itb) {
			if (y < 10) {
				cerr << y;
			}
			else {
				cerr << static_cast<char>('A' + (y - 10));
			}
			for (int x = 0; x < width; x++) {
				Pos p(x, y);
				if (type == 0) {
					if (itb->isset(p)) {
						cerr << "o";
					}
					else {
						cerr << ".";
					}
				}
				else if (type == 1) {
					if (itb->isset(p)) {
						if ((itb + 1)->isset(p)) {
							cerr << "O";
						}
						else {
							cerr << "o";
						}
					}
					else if ((itb + 1)->isset(p)) {
						cerr << "x";
					}
					else {
						cerr << ".";
					}
				}
			}
			if (type == 1) {
				++itb;
			}
		}
		cerr << endl;
	}
}

// 初期化処理
void init() {
#ifdef DEBUGRTIME
	for (int i = 0; i < 96; i++) {
		rtime[i] = 0;
	}
#endif
	// dist1pos の設定
	dist1pos[0].set(0, 1);
	dist1pos[1].set(1, 0);
	dist1pos[2].set(0, -1);
	dist1pos[3].set(-1, 0);
	dist1pos[4].set(0, 0);

	// zero256 の設定
	memset(&zero256, 0, 32);

	// 後手の場合は本拠地の位置を入れ替える必要がある
	if (playOrder == 1) {
		for (int p = 0; p < 2; p++) {
			for (int i = 0; i < 3; i++) {
				homepos[p][i].set(14 - homepos[p][i].getx(), 14 - homepos[p][i].gety());
			}
		}
	}

	// basebb, allbasebb, cannotenterbb の設定
	allbasebb.clear();
	// 本拠地を表す BitBoard を計算する
	for (int pl = 0; pl < 2; pl++) {
		for (int w = 0; w < 3; w++) {
			basebb[pl][w].clear();
			basebb[pl][w].set(homepos[pl][w]);
			allbasebb |= basebb[pl][w];
		}
	}
	// 各プレーヤーが絶対入れない場所（他人の本拠地）の計算
	for (int pl = 0; pl < 2; pl++) {
		for (int w = 0; w < 3; w++) {
			cannotenterbb[pl][w].clear();
			cannotenterbb[pl][w] = BitBoard::andnot(basebb[pl][w], allbasebb);
		}
	}

	// attackbb の計算
	for (int x = 0; x < width; x++) {
		for (int y = 0; y < height; y++) {
			Pos p(x, y);
			// (x, y)から攻撃した場合に占領される場所を表す BitBoard を計算する
			for (int weapon = 0; weapon < 3; weapon++) {
				BitBoard& abball = attackbb[weapon][4][p.getpos()];
				abball.clear();
				for (int dir = 0; dir < 4; dir++) {
					BitBoard& abb = attackbb[weapon][dir][p.getpos()];
					abb.clear();
					for (int i = 0; i < osize[weapon]; i++) {
						int x2, y2;
						rotate(dir, ox[weapon][i], oy[weapon][i], x2, y2);
						if (isinfield(x + x2, y + y2) && !allbasebb.isset(x + x2, y + y2)) {
							abb.set(x + x2, y + y2);
						}
					}
					abball |= abb;
				}
			}
		}
	}

	// 各マスの視界を表す BitBoard を計算する
	for (int x = 0; x < width; x++) {
		for (int y = 0; y < height; y++) {
			Pos p(x, y);
			canseebb[p.getpos()].clear();
			canattackmovebb[p.getpos()].clear();
			cannoattackmovebb[p.getpos()].clear();
			for (int dx = -5; dx <= 5; dx++) {
				for (int dy = -5; dy <= 5; dy++) {
					if (abs(dx) + abs(dy) <= 5 && isinfield(x + dx, y + dy)) {
						canseebb[p.getpos()].set(p + Pos(dx, dy));
					}
					if (abs(dx) + abs(dy) <= 1 && isinfield(x + dx, y + dy)) {
						canattackmovebb[p.getpos()].set(p + Pos(dx, dy));
					}
					if (abs(dx) + abs(dy) <= 3 && isinfield(x + dx, y + dy)) {
						cannoattackmovebb[p.getpos()].set(p + Pos(dx, dy));
					}
				}
			}
		}
	}

	// 記録の初期化
	records.init(playOrder);
	// ある地点にプレーヤーがいた場合で、攻撃しなかった場合に到達可能な場所をまじめに計算すると時間がかかる。
	// そこで、あらかじめプレーヤーの周囲の状況に応じた到達可能な場所を計算しておくことで、処理の高速化を図る。
	// 以下の4種類の計算を行う。
	// a. プレーヤーが最初に顕現状態で、終了時に顕現状態となる移動
	// b. プレーヤーが最初に顕現状態で、終了時に隠蔽状態となる移動
	// c. プレーヤーが最初に隠蔽状態で、終了時に顕現状態となる移動
	// d. プレーヤーが最初に隠蔽状態で、終了時に隠蔽状態となる移動
	// 以下、「A上に移動可能」とは、地点Aが盤内で他人の本拠地でなく、自分以外の誰も出現していない状態、「A下に移動可能」とは地点Aが盤内で他人の本拠地でなく、味方が占領している状態を表すものとする。
	// このうち a. と d. そして b. と c. はそれぞれ対の関係にあり、「A上に移動可能」を「A下に移動可能」のように読み替えれば同じ条件で到達の可否を調べることができる。従って、以下では、a.とb.の場合のみ移動の条件を列挙することにする
	//a
	// プレーヤーの移動可能は範囲は、1+3+5+7+5+3+1 の 25か所 で、それぞれの場所が顕現状態で移動可能か、隠蔽状態で移動可能かに
	// よって、到達可能な場所は異なる。2^50 のテーブルを作ることはメモリ的にも不可能なので、以下のように分けて考える
	//
	// 下図で 0 をプレーヤーの最初の場所とすると、0,1,2,3の場所に移動できる可能性がある
	// ---3---
	// --323--
	// -32123-
	// 3210123
	// -32123-
	// --323--
	// ---3---
	//
	// 以下、a. および、b. の場合のそれぞれの地点への到達可能な条件を列挙する。
	// 各行のいずれかの条件が満たされれば到達可能と判断できる。ただし、下にある条件は上にある条件を満たさなかった場合の条件であるものとする。
	// また、a.の場合は前提条件として「目的地の上」に移動可能、b.の場合は、「目的地の下」に移動可能であるものとする。
	// 列挙されている条件をすべて満たさなかった場合に移動不可と判定できる。
	// 条件の右の（）の中は、目的地までの移動方法を表す。
	// 2つ上に移動したい場合で、1つ上に直接移動できない場合に「右、上、上、左」のような回り込む移動は4歩以上の移動が必要である。移動可能な最大歩数は3なので、回り込みのような移動はできないため、「上、下」のような逆方向の移動は完全に相殺されるため調べる必要はないので、そのような移動は考えないものとする。（3歩でできる「右、上、左」のような移動は結局「上」と全く同じ）
	//
	// まず、距離が0,1 の場所への到達可能性について考える。
	// 距離0の場合、
	// a.の場合は、そもそも移動しないので必ず到達可能
	// b.の場合、「0下」に移動可能（隠蔽）
	//
	// 距離が1の場合、調べる場所は4か所あるが、対称性を考えると1か所についてのみ考察すれば良い。そこで上の1への移動を考える。
	// a.の場合、前提条件を満たした段階で到達可能。（上）
	// b.の場合、「1上」に移動可能。（上、隠蔽）
	//           「0下」に移動可能。（隠蔽、上）、
	//           下図で「A上」、「A下」、「B下」に移動可能。（左、隠蔽、上、右）
	//          「A上」、「B上」、「B下」に移動可能。（左、隠蔽、上、右）
	//           C,Dを経由するルートはA,Bと同様に考えればよい。
	//	  B1D
	//    A0C
	// 上記のことから、1 に到達可能かどうかは以下の図の A の地点の上に移動可能か、0とAの地点の下に移動可能かがわかればよいことがわかる。
	// これは8+9=17か所  なので17ビット=131072通りの組み合わせがある。この組み合わせそれぞれについて4か所の到達可能性を表すビット列のデータ(4bit<1バイト） を計算すればよいので、
	// 131072byte=0.25MBのメモリが必要。これは充分に確保可能
	//    AAA
	//    A0A
	//    AAA
	//
	// 次に、距離が2,3 の場所への到達可能性について考える。この際、下図のようにA,B,C,D の4分割して考えることにする
	// A,B,C,D は対称なので、Aについて考えることにする。
	// ---A---
	// --DAA--
	// -DD1AA-
	// DD101BB
	// -CC1BB-
	// --CCB--
	// ---C---
	// Aの部分を下図のように距離が2のV,Wと距離が3のX,Y,Zに分けて考える。このとき、YとZは対称なので、Yについてのみ考えればよい。
	// また、Aの部分ではないが、3つの地点を下図のようにR,S,Tと名前をつけるものとする
	//    X
	//    VY
	//    RWZ
	//    0ST
	// まずVについて考える。最大3歩しか移動できないので、0からVへ至るルートは「上、上」しか存在しない。
	// a.の場合、「R上」に移動可能。（上、上）
	//           「0下、R下、V下」に移動可能。（隠蔽、上、上、顕現）
	// b.の場合、「R上、V上」に移動可能。（上、上、隠蔽）
	//           「R上、R下」に移動可能。（上、隠蔽、上）
	//           「0下、R下」に移動可能。（隠蔽、上、上）
	// 次にWについて考える。最大3歩しか移動できないので、0からWへ至るルートは「上、右」または「右、上」の2通りしか存在しない。
	// a.の場合、「R上」に移動可能。（上、右）
	//			 「S上」に移動可能。（右、上）
	//           「0下、R下、W下」に移動可能。（隠蔽、上、右、顕現）
	//           「0下、S下、W下」に移動可能。（隠蔽、右、上、顕現）
	// b.の場合、「R上、W上」に移動可能。（上、右、隠蔽）
	//           「S上、W上」に移動可能。（右、上、隠蔽）
	//           「R上、R下」に移動可能。（上、隠蔽、右）
	//           「S上、S下」に移動可能。（右、隠蔽、上）
	//           「0下、R下」に移動可能。（隠蔽、上、右）
	//           「0下、S下」に移動可能。（隠蔽、右、上）
	// 次にXについて考える、0からXへ至るルートは「上、上、上」しか存在しない。
	// a.の場合、「R上、V上」に移動可能。（上、上、上）
	// b.の場合、「R上、V上、X上」に移動可能。（上、上、上、隠蔽）
	//           「R上、V上、V下」に移動可能。（上、上、隠蔽、上）
	//           「R上、R下、V下」に移動可能。（上、隠蔽、上、上）
	//           「0下、R下、V下」に移動可能。（隠蔽、上、上、上）
	// 次にYについて考える。0からYへ至るルートは「上、上、右」、「上、右、上」、「右、上、上」の3通り
	// a.の場合、「R上、V上」に移動可能。（上、上、右）
	//           「R上、W上」に移動可能。（上、右、上）
	//           「S上、W上」に移動可能。（右、上、上）
	// b.の場合、「R上、V上、Y上」に移動可能。（上、上、右、隠蔽）
	//           「R上、W上、Y上」に移動可能。（上、右、上、隠蔽）
	//           「S上、W上、Y上」に移動可能。（右、上、上、隠蔽）
	//           「R上、V上、V下」に移動可能。（上、上、隠蔽、右）
	//           「R上、W上、W下」に移動可能。（上、右、隠蔽、上）
	//           「S上、W上、W下」に移動可能。（右、上、隠蔽、上）
	//           「R上、R下、V下」に移動可能。（上、隠蔽、上、右）
	//           「R上、R下、W下」に移動可能。（上、隠蔽、右、上）
	//           「S上、S下、W下」に移動可能。（右、隠蔽、上、上）
	//           「0下、R下、V下」に移動可能。（隠蔽、上、上、右）
	//           「0下、R下、W下」に移動可能。（隠蔽、上、右、上）
	//           「0下、S下、W下」に移動可能。（隠蔽、右、上、上）
	//
	// 以上のことから、上記のV,W,X,T,Zの5か所へ到達可能かどうかを調べるためには、上は R,S,T,V,W,X,Y,Z の8赤所、下はそれに 0下 を加えた9箇所の
	// 計17か所の情報があればよい。これは17ビットで131072通り。
	// さらに、これを時計回りに90度、180度、270度ずらした場合について計算して表をつくれば、到達可能なすべての場所の到達可能性を表現した表をつくることができる。
	//
	// まず、15*15のそれぞれの場所について、BitBoardの中で距離が 0,1 の場所への到達可能性を調べるためのビット列、距離が2，3の場所への到達可能性を調べるための4種類のビット列を計算する。
	// 計算したビット列と、_pext_u64 を使えば、BitBoardから到達可能性を計算するために必要な8+8=17ビットのビット列を取得することができる。
	// ただし、盤の端などで、取ってくる場所が盤外のためBitBoard に存在しない場合は、盤内にあるビットデータのみ取得し、それを _pdep_u64 を使って盤外のビットを補完してやる必要がある


	// 移動可能な場所、到達可能な場所の計算に必要な場所を表す配列。右上、左上、左下、右下でそれぞれ必要
	// （順番が重要なので、rotateを使うことはできないので、すべてテーブルに入れる）
	static const Pos placetable[4][9] = {
		{ Pos(0, -3), Pos(0, -2), Pos(1, -2), Pos(0, -1), Pos(1, -1), Pos(2, -1), Pos(0, 0), Pos(1, 0), Pos(2, 0) },
		{ Pos(-1, -2), Pos(0, -2), Pos(-2, -1), Pos(-1, -1), Pos(0, -1), Pos(-3, 0), Pos(-2, 0), Pos(-1, 0), Pos(0, 0) },
		{ Pos(-2, 0), Pos(-1, 0), Pos(0, 0), Pos(-2, 1), Pos(-1, 1), Pos(0, 1), Pos(-1, 2), Pos(0, 2), Pos(0, 3) },
		{ Pos(0, 0), Pos(1, 0), Pos(2, 0), Pos(3, 0), Pos(0, 1), Pos(1, 1), Pos(2, 1), Pos(0, 2), Pos(1, 2) }
	};
	static const Pos arriveplacetable[4][5] = {
		{ Pos(0, -3), Pos(0, -2), Pos(1, -2), Pos(1, -1), Pos(2, -1) },
		{ Pos(-1, -2), Pos(-2, -1), Pos(-1, -1), Pos(-3, 0), Pos(-2, 0) },
		{ Pos(-2, 1), Pos(-1, 1), Pos(-1, 2), Pos(0, 2), Pos(0, 3) },
		{ Pos(2, 0), Pos(3, 0), Pos(1, 1), Pos(2, 1), Pos(1, 2) },
	};
	for (int x = 0; x < width; x++) {
		for (int y = 0; y < height; y++) {
			Pos p(x, y);
			int pindex = p.getpos();
			// 初期化
			for (int i = 0; i < 2; i++) {
				for (int j = 0; j < 5; j++) {
					obstaclemaskbb[i][j][pindex].clear();
					canarrivebb[j][pindex].clear();
					obstaclepdepmask[j][pindex] = 0;
					canarrivepextmask[j][pindex] = 0;
				}
			}
			// まず、距離 0, 1 の場合を計算する。必要なのは p と p の周囲 8 マス
			uint64_t bit1, bit2, bit3;
			bit1 = bit3 = 1;
			bit2 = 1 << 8;
			for (int dy = -1; dy <= 1; dy++) {
				for (int dx = -1; dx <= 1; dx++) {
					// 盤内であれば必要。
					if (isinfield(x + dx, y + dy)) {
						// 移動開始地点を含まないほう
						if (!(dx == 0 && dy == 0)) {
							obstaclemaskbb[0][0][pindex].set(p + Pos(dx, dy));
							// 盤内にあればそこに相当する pdeptable のビットを立てる。
							obstaclepdepmask[0][pindex] |= bit1;
							bit1 <<= 1;
						}
						obstaclemaskbb[1][0][pindex].set(p + Pos(dx, dy));
						obstaclepdepmask[0][pindex] |= bit2;
						bit2 <<= 1;
						if (abs(dx) + abs(dy) <= 1) {
							canarrivebb[0][pindex].set(p + Pos(dx, dy));
							canarrivepextmask[0][pindex] |= bit3;
							bit3 <<= 1;
						}
					}
					else {
						// 盤内になければ pdeptable のビットは立てない
						bit1 <<= 1;
						bit2 <<= 1;
						if (abs(dx) + abs(dy) <= 1) {
							bit3 <<= 1;
						}
					}
				}
			}
			// 次に距離が2,3の場合を計算する
			for (int i = 1; i < 5; i++) {
				bit1 = 1;
				bit2 = 1 << 8;
				for (int j = 0; j < 9; j++) {
					// 盤内であれば必要。
					if (isinfield(x + placetable[i - 1][j].getdirx(), y + placetable[i - 1][j].getdiry())) {
						// 移動開始地点を含まないほう
						if (placetable[i - 1][j] != ZERO_POS) {
							obstaclemaskbb[0][i][pindex].set(p + placetable[i - 1][j]);
							// 盤内にあればそこに相当する pdeptable のビットを立てる。
							obstaclepdepmask[i][pindex] |= bit1;
							bit1 <<= 1;
						}
						obstaclemaskbb[1][i][pindex].set(p + placetable[i - 1][j]);
						obstaclepdepmask[i][pindex] |= bit2;
						bit2 <<= 1;
					}
					else {
						// 盤内になければ pdeptable のビットは立てない
						bit1 <<= 1;
						bit2 <<= 1;
					}
				}
				bit3 = 1;
				for (int j = 0; j < 5; j++) {
					// 盤内であれば必要。
					if (isinfield(x + arriveplacetable[i - 1][j].getdirx(), y + arriveplacetable[i - 1][j].getdiry())) {
						canarrivebb[i][pindex].set(p + arriveplacetable[i - 1][j]);
						canarrivepextmask[i][pindex] |= bit3;
						bit3 <<= 1;
					}
					else {
						// 盤内になければ pdeptable のビットは立てない
						bit3 <<= 1;
					}
				}
			}
		}
	}

	// 0, 1 の距離について、得られた17ビットのデータから到達可能かどうかを計算する。
	// 17ビットのデータは下記の図の点に次のように対応する。ただし、移動前の位置の点をO、大文字は上（顕現状態）を移動可能かどうか（可能時は1）、小文字は下（隠蔽状態）を移動可能かどうか 
	// ABC
	// DOE
	// FGH    17ビットのビット列は以下の通り hgfeodcbaHGFEDCBA
	// 計算結果は、5ビットのビット列で、それぞれ GEODB の点に到達可能（可能時は1）かどうかを表す
	// 17のそれぞれの地点について、移動可能な場合に立っているビットを計算し、dist01umap に格納する。dist01umap の一つ目のインデックスは 0:顕現状態、1:隠蔽状態 を表す
	unordered_map<int, uint64_t> dist01umap[2];
	uint64_t bit = 1;
	for (int y = -1; y <= 1; y++) {
		for (int x = -1; x <= 1; x++) {
			if (!(x == 0 && y == 0)) {
				dist01umap[0][Pos(x, y).getpos()] = bit;
				bit <<= 1;
			}
		}
	}
	for (int y = -1; y <= 1; y++) {
		for (int x = -1; x <= 1; x++) {
			dist01umap[1][Pos(x, y).getpos()] = bit;
			bit <<= 1;
		}
	}

	// 目的地に移動可能な場合に立てるビットを計算する
	unordered_map<int, uint64_t> dist01umapcanmove;
	dist01umapcanmove[Pos(0, -1).getpos()] = 1 << 0;
	dist01umapcanmove[Pos(-1, 0).getpos()] = 1 << 1;
	dist01umapcanmove[Pos(0, 0).getpos()] = 1 << 2;
	dist01umapcanmove[Pos(1, 0).getpos()] = 1 << 3;
	dist01umapcanmove[Pos(0, 1).getpos()] = 1 << 4;
	// 0, 1 の距離に移動する際の移動を登録する
	vector<Action>& actions = actiontable[0];
	actions.clear();
	unordered_map<int, size_t>& avitable = actionvaluetoindextable[0];
	// なにもしない行動の登録
	setactiontable(0, Pos(0, 0), false, 0, avitable, actions);
	// 隠蔽の登録
	setactiontable(9, Pos(0, 0), true, 0, avitable, actions);
	// 下、右、上、左の順でそこへ移動する行動の登録
	for (int i = 0; i < 4; i++) {
		// 以下のコメントは下の場合の行動
		// 下の登録
		setactiontable(5, Pos(0, 1), false, i, avitable, actions);
		// 隠蔽、下の登録
		setactiontable(59, Pos(0, 1), true, i, avitable, actions);
		// 下、隠蔽の登録
		setactiontable(95, Pos(0, 1), true, i, avitable, actions);
		// 右、隠蔽、下、左の登録
		setactiontable(8596, Pos(0, 1), true, i, avitable, actions);
		// 右、下、隠蔽、左の登録
		setactiontable(8956, Pos(0, 1), true, i, avitable, actions);
		// 左、隠蔽、下、右の登録
		setactiontable(6598, Pos(0, 1), true, i, avitable, actions);
		// 左、下、隠蔽、右の登録
		setactiontable(6958, Pos(0, 1), true, i, avitable, actions);
	}

// ysaidata.dat と ysaidata2.datt を作成する場合は SAVEDATA を define する。
//#define SAVEDATA
#ifdef SAVEDATA
	ofstream wf;
	wf.open("ysaidata.dat", ios::out | ios::binary);
	for (uint64_t i = 0; i < (1 << 17); i++) {
		// 初期化
		uint64_t& canmovetable = canarrivetable[0][0][i];
		uint64_t& canarriveh = canarrivetable[1][0][i];
		uint64_t& aindextable = actionsindextable[0][i];
		uint64_t destbit;	// 目的地を表すビット
		canmovetable = canarriveh = aindextable = 0;

		// O への到達可能性を計算する
		// O には必ず到達可能
		destbit = dist01umapcanmove[Pos(0, 0).getpos()];
		canmovetable |= destbit;
		setmovetable(0, 0, aindextable, avitable);

		// o への到達可能性を計算する
		// o には o へ移動可能であれば隠蔽で移動可能
		if (i & dist01umap[1][Pos(0, 0).getpos()]) {
			canarriveh |= destbit;
			setmovetable(9, 0, aindextable, avitable);
		}
		// G から反時計回りに、E,B,Dへの到達可能性を計算する（コメントはGの場合）
		// なお、複数のルートで到達可能であったとしても、そのうちの一つだけわかれば十分である。
		for (int j = 0; j < 4; j++) {
			Action action;
			// D,O,E,F,G,H の座標
			Pos posd = Pos(-1, 0).rotate(j);
			Pos poso = Pos(0, 0).rotate(j);
			Pos pose = Pos(1, 0).rotate(j);
			Pos posf = Pos(-1, 1).rotate(j);
			Pos posg = Pos(0, 1).rotate(j);
			Pos posh = Pos(1, 1).rotate(j);
			destbit = dist01umapcanmove[posg.getpos()];
			// G への到達可能性を計算する
			// G に移動可能であれば移動可能
			if (i & dist01umap[0][posg.getpos()]) {
				canmovetable |= destbit;
				setmovetable(5, j, aindextable, avitable);
			}

			// g への到達可能性を計算する。まず、g へ移動可能である必要がある
			if (i & dist01umap[1][posg.getpos()]) {
				// G へ移動可能な場合は、下、隠蔽で到達できる
				if (i & dist01umap[0][posg.getpos()]) {
					canarriveh |= destbit;
					setmovetable(95, j, aindextable, avitable);
				}
				// o へ移動可能な場合は、隠蔽、下で到達できる
				else if (i & dist01umap[1][poso.getpos()]) {
					canarriveh |= destbit;
					setmovetable(59, j, aindextable, avitable);
				}
				// D,d,fへ移動可能な場合は、左、隠蔽、下、右で到達できる
				else if (i & dist01umap[0][posd.getpos()] && i & dist01umap[1][posd.getpos()] && i & dist01umap[1][posf.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6598, j, aindextable, avitable);
				}
				// D,F,fへ移動可能な場合は、左、下、隠蔽、右で到達できる
				else if (i & dist01umap[0][posd.getpos()] && i & dist01umap[0][posf.getpos()] && i & dist01umap[1][posf.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6958, j, aindextable, avitable);
				}
				// E,e,hへ移動可能な場合は、右、隠蔽、下、左で到達できる
				else if (i & dist01umap[0][pose.getpos()] && i & dist01umap[1][pose.getpos()] && i & dist01umap[1][posh.getpos()]) {
					canarriveh |= destbit;
					setmovetable(8596, j, aindextable, avitable);
				}
				// E,H,hへ移動可能な場合は、右、下、隠蔽、左で到達できる
				else if (i & dist01umap[0][pose.getpos()] && i & dist01umap[0][posh.getpos()] && i & dist01umap[1][posh.getpos()]) {
					canarriveh |= destbit;
					setmovetable(8956, j, aindextable, avitable);
				}
			}
		}
		uint32_t data;
		data = canmovetable;
		wf.write((char *)&data, sizeof(uint32_t));
		data = canarriveh;
		wf.write((char *)&data, sizeof(uint32_t));
		data = aindextable;
		wf.write((char *)&data, sizeof(uint32_t));
		//		wf << canmovetable << " " << canarriveh << " " << aindextable << endl;
	}
	wf.close();

#if 0
	ifstream rf;
	rf.open("data.txt", ios::in | ios::binary);
	const int bufsize = (1 << 17) * 3;
	uint32_t *buf = new uint32_t[bufsize];
	rf.read((char *)buf, sizeof(uint32_t) * bufsize);
	uint32_t *ptr = buf;
	for (uint32_t i = 0; i < (1 << 17); i++) {
		if (canarrivetable[0][0][i] != *(ptr++)) {
			cerr << "error a " << i << endl;
		}
		if (canarrivetable[1][0][i] != *(ptr++)) {
			cerr << "error b " << i << endl;
		}
		if (actionsindextable[0][i] != *(ptr++)) {
			cerr << "error c " << i << endl;
		}
	}
	delete buf;
	rf.close();
#endif
#else 
	ifstream rf;
	rf.open("ysaidata.dat", ios::in | ios::binary);
	const int bufsize = (1 << 17) * 3;
	uint32_t *buf = new uint32_t[bufsize];
	rf.read((char *)buf, sizeof(uint32_t) * bufsize);
	uint32_t *ptr = buf;
	for (uint32_t i = 0; i < (1 << 17); i++) {
		canarrivetable[0][0][i] = *(ptr++);
		canarrivetable[1][0][i] = *(ptr++);
		actionsindextable[0][i] = *(ptr++);
	}
	delete buf;
	rf.close();
#endif

	// 2, 3 の距離について、得られた17ビットのデータから到達可能かどうかを計算する。右上、左上、左下、右下の4か所に分けて計算する必要がある
	// 右上の場合、17ビットのデータは下記の図の点に次のように対応する。ただし、移動前の位置の点をO、大文字は上（顕現状態）を移動可能かどうか（可能時は1）、小文字は下（隠蔽状態）を移動可能かどうか 
	// X
	// VY
	// RWZ
	// OST      17ビットのビット列は以下の通り tsozwrvyxTSZWRYVX
	// 計算結果は、5ビットのビット列で、それぞれ ZWYVX の点に到達可能（可能時は1）かどうかを表す
	//
	// 左上の場合、上の図を90度反時計回りに回転させると以下のようになる
	//   ZT
	//  YWS
	// XVRO    17ビットのビット列は先ほどと異なり次のようになる orvxswytzRVXSWYTZ
	// 計算結果は、5ビットのビット列で、それぞれ VXWYZ の点に到達可能（可能時は1）かどうかを表す
	//
	// 左下の場合、上の図を180度反時計回りに回転させると以下のようになる
	// TSO
	// ZWR
	//  YV
	//   X      17ビットのビット列は先ほどと異なり次のようになる xvyrwzostXVYRWZST
	// 計算結果は、5ビットのビット列で、それぞれ XVYWZ の点に到達可能（可能時は1）かどうかを表す
	//
	// 右下の場合、上の図を270度反時計回りに回転させると以下のようになる
	// ORVX
	// SWY
	// TZ    17ビットのビット列は先ほどと異なり次のようになる ztywsxvroZTYWSXVR
	// 計算結果は、5ビットのビット列で、それぞれ ZYWXV の点に到達可能（可能時は1）かどうかを表す
	//
	// 17のそれぞれの地点について、移動可能な場合に立っているビットを計算し、dist23umap に格納する。dist23umap の一つ目のインデックスは 0:顕現状態、1:隠蔽状態、二つ目のインデックスは 0:右上、1:左上、2:左下、3:右下 を表す
	unordered_map<int, uint64_t> dist23umap[2][4];
	// 目的地に到達可能な場合に立てるビット
	unordered_map<int, uint64_t> dist23umapcanarrive[4];
	for (int i = 0; i < 4; i++) {
		int bit = 1;
		int bit2 = 1 << 8;
		for (int j = 0; j < 9; j++) {
			if (placetable[i][j] != Pos(0, 0)) {
				dist23umap[0][i][placetable[i][j].getpos()] = bit;
				bit <<= 1;
			}
			dist23umap[1][i][placetable[i][j].getpos()] = bit2;
			bit2 <<= 1;
		}
		bit = 1;
		for (int j = 0; j < 5; j++) {
			dist23umapcanarrive[i][arriveplacetable[i][j].getpos()] = bit;
			bit <<= 1;
		}
	}

	// 2,3 の距離に移動する際の移動を登録する
	// 右上、左上、左下、右下の順でそこへ移動する行動の登録
	for (int i = 0; i < 4; i++) {
		vector<Action>& atable = actiontable[i + 1];
		atable.clear();
		unordered_map<int, size_t>& avitable = actionvaluetoindextable[i + 1];
		// 以下のコメントは右上の場合の行動
		// 上、上の登録
		setactiontable(77, Pos(0, -2), false, i, avitable, atable);
		// 隠蔽、上、上、顕現の登録
		setactiontable(9779, Pos(0, -2), false, i, avitable, atable);
		// 上、上、隠蔽の登録
		setactiontable(977, Pos(0, -2), true, i, avitable, atable);
		// 上、隠蔽、上の登録
		setactiontable(797, Pos(0, -2), true, i, avitable, atable);
		// 隠蔽、上、上の登録
		setactiontable(779, Pos(0, -2), true, i, avitable, atable);

		// 上、右の登録
		setactiontable(67, Pos(1, -1), false, i, avitable, atable);
		// 隠蔽、上、右、顕現の登録
		setactiontable(9679, Pos(1, -1), false, i, avitable, atable);
		// 右、上の登録
		setactiontable(76, Pos(1, -1), false, i, avitable, atable);
		// 隠蔽、右、上、顕現の登録
		setactiontable(9769, Pos(1, -1), false, i, avitable, atable);
		// 上、右、隠蔽の登録
		setactiontable(967, Pos(1, -1), true, i, avitable, atable);
		// 上、隠蔽、右の登録
		setactiontable(697, Pos(1, -1), true, i, avitable, atable);
		// 隠蔽、上、右の登録
		setactiontable(679, Pos(1, -1), true, i, avitable, atable);
		// 右、上、隠蔽の登録
		setactiontable(976, Pos(1, -1), true, i, avitable, atable);
		// 右、隠蔽、上の登録
		setactiontable(796, Pos(1, -1), true, i, avitable, atable);
		// 隠蔽、右、上の登録
		setactiontable(769, Pos(1, -1), true, i, avitable, atable);

		// 上、上、上の登録
		setactiontable(777, Pos(0, -3), false, i, avitable, atable);
		// 上、上、上、隠蔽の登録
		setactiontable(9777, Pos(0, -3), true, i, avitable, atable);
		// 上、上、隠蔽、上の登録
		setactiontable(7977, Pos(0, -3), true, i, avitable, atable);
		// 上、隠蔽、上、上の登録
		setactiontable(7797, Pos(0, -3), true, i, avitable, atable);
		// 隠蔽、上、上、上の登録
		setactiontable(7779, Pos(0, -3), true, i, avitable, atable);

		// 上、上、右の登録
		setactiontable(677, Pos(1, -2), false, i, avitable, atable);
		// 上、右、上の登録
		setactiontable(767, Pos(1, -2), false, i, avitable, atable);
		// 右、上、上の登録
		setactiontable(776, Pos(1, -2), false, i, avitable, atable);
		// 上、上、右、隠蔽の登録
		setactiontable(9677, Pos(1, -2), true, i, avitable, atable);
		// 上、上、隠蔽、右の登録
		setactiontable(6977, Pos(1, -2), true, i, avitable, atable);
		// 上、隠蔽、上、右の登録
		setactiontable(6797, Pos(1, -2), true, i, avitable, atable);
		// 隠蔽、上、上、右の登録
		setactiontable(6779, Pos(1, -2), true, i, avitable, atable);
		// 上、右、上、隠蔽の登録
		setactiontable(9767, Pos(1, -2), true, i, avitable, atable);
		// 上、右、隠蔽、上の登録
		setactiontable(7967, Pos(1, -2), true, i, avitable, atable);
		// 上、隠蔽、右、上の登録
		setactiontable(7697, Pos(1, -2), true, i, avitable, atable);
		// 隠蔽、上、右、上の登録
		setactiontable(7679, Pos(1, -2), true, i, avitable, atable);
		// 右、上、上、隠蔽の登録
		setactiontable(9776, Pos(1, -2), true, i, avitable, atable);
		// 右、上、隠蔽、上の登録
		setactiontable(7976, Pos(1, -2), true, i, avitable, atable);
		// 右、隠蔽、上、上の登録
		setactiontable(7796, Pos(1, -2), true, i, avitable, atable);
		// 隠蔽、右、上、上の登録
		setactiontable(7769, Pos(1, -2), true, i, avitable, atable);

		// 上、右、右の登録
		setactiontable(667, Pos(2, -1), false, i, avitable, atable);
		// 右、上、右の登録
		setactiontable(676, Pos(2, -1), false, i, avitable, atable);
		// 右、右、上の登録
		setactiontable(766, Pos(2, -1), false, i, avitable, atable);
		// 上、右、右、隠蔽の登録
		setactiontable(9667, Pos(2, -1), true, i, avitable, atable);
		// 上、右、隠蔽、右の登録
		setactiontable(6967, Pos(2, -1), true, i, avitable, atable);
		// 上、隠蔽、右、右の登録
		setactiontable(6697, Pos(2, -1), true, i, avitable, atable);
		// 隠蔽、上、右、右の登録
		setactiontable(6679, Pos(2, -1), true, i, avitable, atable);
		// 右、上、右、隠蔽の登録
		setactiontable(9676, Pos(2, -1), true, i, avitable, atable);
		// 右、上、隠蔽、右の登録
		setactiontable(6976, Pos(2, -1), true, i, avitable, atable);
		// 右、隠蔽、上、右の登録
		setactiontable(6796, Pos(2, -1), true, i, avitable, atable);
		// 隠蔽、右、上、右の登録
		setactiontable(6769, Pos(2, -1), true, i, avitable, atable);
		// 右、右、上、隠蔽の登録
		setactiontable(9766, Pos(2, -1), true, i, avitable, atable);
		// 右、右、隠蔽、上の登録
		setactiontable(7966, Pos(2, -1), true, i, avitable, atable);
		// 右、隠蔽、右、上の登録
		setactiontable(7696, Pos(2, -1), true, i, avitable, atable);
		// 隠蔽、右、右、上の登録
		setactiontable(7669, Pos(2, -1), true, i, avitable, atable);
	}

#ifdef SAVEDATA
	ofstream wf2;
	wf2.open("ysaidata2.dat", ios::out | ios::binary);
	for (uint64_t i = 0; i < (1 << 17); i++) {
		for (int j = 0; j < 4; j++) {
			// 初期化
			uint64_t& canarrive = canarrivetable[0][j + 1][i];
			uint64_t& canarriveh = canarrivetable[1][j + 1][i];
			uint64_t& aindextable = actionsindextable[j + 1][i];
			uint64_t destbit;	// 目的地を表すビット
			canarrive = canarriveh = aindextable = 0;
			unordered_map<int, size_t>& avitable = actionvaluetoindextable[j + 1];
			// ORSTVWXYZ の座標
			Pos poso = Pos(0, 0).rotate(j);
			Pos posr = Pos(0, -1).rotate(j);
			Pos poss = Pos(1, 0).rotate(j);
			Pos post = Pos(2, 0).rotate(j);
			Pos posv = Pos(0, -2).rotate(j);
			Pos posw = Pos(1, -1).rotate(j);
			Pos posx = Pos(0, -3).rotate(j);
			Pos posy = Pos(1, -2).rotate(j);
			Pos posz = Pos(2, -1).rotate(j);
			// コメントは右上(j == 0)の場合
			// Vへの到達可能性を計算する。まずVへ移動可能である必要がある。
			destbit = dist23umapcanarrive[j][posv.getpos()];
			//if (i == 0x1fcff && j == 1) {
			//	cerr << "aa " << posr << "," << hex << dist23umap[0][j][posr.getpos()] << endl;
			//}
			if (i & dist23umap[0][j][posv.getpos()]) {
				// R へ移動可能な場合は、上、上で移動可能
				if (i & dist23umap[0][j][posr.getpos()]) {
					canarrive |= destbit;
					setmovetable(77, j, aindextable, avitable);
				}
				// o,r,v へ移動可能な場合は、隠蔽、上、上、顕現で移動可能
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posv.getpos()]) {
					canarrive |= destbit;
					setmovetable(9779, j, aindextable, avitable);
				}
			}

			// vへの到達可能性を計算する。まずvへ移動可能である必要がある。
			if (i & dist23umap[1][j][posv.getpos()]) {
				// o,r へ移動可能な場合は、隠蔽、上、上で移動可能
				if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][posr.getpos()]) {
					canarriveh |= destbit;
					setmovetable(779, j, aindextable, avitable);
				}
				// R へ移動可能な場合
				else if (i & dist23umap[0][j][posr.getpos()]) {
					// V へ移動可能であれば、上、上、隠蔽で移動可能
					if (i & dist23umap[0][j][posv.getpos()]) {
						canarriveh |= destbit;
						setmovetable(977, j, aindextable, avitable);
					}
					// r へ移動可能であれば、上、隠蔽、上で移動可能
					else if (i & dist23umap[1][j][posr.getpos()]) {
						canarriveh |= destbit;
						setmovetable(797, j, aindextable, avitable);
					}
				}
			}


			// Wへの到達可能性を計算する。まずWへ移動可能である必要がある。
			destbit = dist23umapcanarrive[j][posw.getpos()];
			if (i & dist23umap[0][j][posw.getpos()]) {
				// R へ移動可能な場合は、上、右で移動可能
				if (i & dist23umap[0][j][posr.getpos()]) {
					canarrive |= destbit;
					setmovetable(67, j, aindextable, avitable);
				}
				// S へ移動可能な場合は、右、上で移動可能
				else if (i & dist23umap[0][j][poss.getpos()]) {
					canarrive |= destbit;
					setmovetable(76, j, aindextable, avitable);
				}
				// o と w へ移動可能な場合
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					// r へ移動可能な場合は、隠蔽、上、右、顕現で移動可能
					if (i & dist23umap[1][j][posr.getpos()]) {
						canarrive |= destbit;
						setmovetable(9679, j, aindextable, avitable);
					}
					// s へ移動可能な場合は、隠蔽、右、上、顕現で移動可能
					else if (i & dist23umap[1][j][poss.getpos()]) {
						canarrive |= destbit;
						setmovetable(9769, j, aindextable, avitable);
					}
				}
			}

			// wへの到達可能性を計算する。まずwへ移動可能である必要がある。
			if (i & dist23umap[1][j][posw.getpos()]) {
				// o,r へ移動可能な場合は、隠蔽、上、右で移動可能
				if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][posr.getpos()]) {
					canarriveh |= destbit;
					setmovetable(679, j, aindextable, avitable);
				}
				// o,s へ移動可能な場合は、隠蔽、右、上で移動可能
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][poss.getpos()]) {
					canarriveh |= destbit;
					setmovetable(769, j, aindextable, avitable);
				}
				// R,W へ移動可能な場合、上、右、隠蔽で移動可能
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(967, j, aindextable, avitable);
				}
				// R,r へ移動可能な場合、上、隠蔽、右で移動可能
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[1][j][posr.getpos()]) {
					canarriveh |= destbit;
					setmovetable(697, j, aindextable, avitable);
				}
				// S,W へ移動可能な場合、右、上、隠蔽で移動可能
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[0][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(976, j, aindextable, avitable);
				}
				// S,s へ移動可能な場合、右、隠蔽、上で移動可能
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[1][j][poss.getpos()]) {
					canarriveh |= destbit;
					setmovetable(796, j, aindextable, avitable);
				}
			}

			// Xへの到達可能性を計算する。R,V,Xへ移動可能な場合は、上、上、上で到達可能
			destbit = dist23umapcanarrive[j][posx.getpos()];
			if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posv.getpos()] && i & dist23umap[0][j][posx.getpos()]) {
				canarrive |= destbit;
				setmovetable(777, j, aindextable, avitable);
			}
			// xへの到達可能性を計算する。まず x へ移動可能である必要がある。
			if (i & dist23umap[1][j][posx.getpos()]) {
				// R, V, X に移動可能であれば、上、上、上、隠蔽で到達可能
				if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posv.getpos()] && i & dist23umap[0][j][posx.getpos()]) {
					canarriveh |= destbit;
					setmovetable(9777, j, aindextable, avitable);
				}
				// R, V, v に移動可能であれば、上、上、隠蔽、上で到達可能
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posv.getpos()] && i & dist23umap[1][j][posv.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7977, j, aindextable, avitable);
				}
				// R, r, v に移動可能であれば、上、隠蔽、上、上で到達可能
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posv.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7797, j, aindextable, avitable);
				}
				// o, r, v に移動可能であれば、隠蔽、上、上、上で到達可能
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posv.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7779, j, aindextable, avitable);
				}
			}

			// Yへの到達可能性を計算する。まず、Yに移動可能である必要がある。
			destbit = dist23umapcanarrive[j][posy.getpos()];
			if (i & dist23umap[0][j][posy.getpos()]) {
				// S, W に移動可能であれば、右、上、上で到達可能 
				if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[0][j][posw.getpos()]) {
					canarrive |= destbit;
					setmovetable(776, j, aindextable, avitable);
				}
				// R に移動可能な場合
				else if (i & dist23umap[0][j][posr.getpos()]) {
					// V に移動可能であれば、上、上、右で到達可能 
					if (i & dist23umap[0][j][posv.getpos()]) {
						canarrive |= destbit;
						setmovetable(677, j, aindextable, avitable);
					}
					// W に移動可能であれば、上、右、上で到達可能 
					else if (i & dist23umap[0][j][posw.getpos()]) {
						canarrive |= destbit;
						setmovetable(767, j, aindextable, avitable);
					}
				}
			}

			// yへの到達可能性を計算する。まず、yに移動可能である必要がある。
			if (i & dist23umap[1][j][posy.getpos()]) {
				// R, V, Y に移動可能であれば、上、上、右、隠蔽で到達可能 
				if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posv.getpos()] && i & dist23umap[0][j][posy.getpos()]) {
					canarriveh |= destbit;
					setmovetable(9677, j, aindextable, avitable);
				}
				// R, V, v に移動可能であれば、上、上、隠蔽、右で到達可能 
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posv.getpos()] && i & dist23umap[1][j][posv.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6977, j, aindextable, avitable);
				}
				// R, r, v に移動可能であれば、上、隠蔽、上、右で到達可能 
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posv.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6797, j, aindextable, avitable);
				}
				// o, r, v に移動可能であれば、隠蔽、上、上、右で到達可能 
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posv.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6779, j, aindextable, avitable);
				}
				// R, W, Y に移動可能であれば、上、右、上、隠蔽で到達可能 
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posw.getpos()] && i & dist23umap[0][j][posy.getpos()]) {
					canarriveh |= destbit;
					setmovetable(9767, j, aindextable, avitable);
				}
				// R, W, w に移動可能であれば、上、右、隠蔽、上で到達可能 
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posw.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7967, j, aindextable, avitable);
				}
				// R, r, w に移動可能であれば、上、隠蔽、右、上で到達可能 
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7697, j, aindextable, avitable);
				}
				// o, r, w に移動可能であれば、隠蔽、上、右、上で到達可能 
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7679, j, aindextable, avitable);
				}
				// S, W, Y に移動可能であれば、右、上、上、隠蔽で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[0][j][posw.getpos()] && i & dist23umap[0][j][posy.getpos()]) {
					canarriveh |= destbit;
					setmovetable(9776, j, aindextable, avitable);
				}
				// S, W, w に移動可能であれば、右、上、隠蔽、上で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[0][j][posw.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7976, j, aindextable, avitable);
				}
				// S, s, w に移動可能であれば、右、隠蔽、上、上で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[1][j][poss.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7796, j, aindextable, avitable);
				}
				// o, s, w に移動可能であれば、隠蔽、右、上、上で到達可能 
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][poss.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7769, j, aindextable, avitable);
				}
			}

			// Zへの到達可能性を計算する。まず、Zに移動可能である必要がある。
			destbit = dist23umapcanarrive[j][posz.getpos()];
			if (i & dist23umap[0][j][posz.getpos()]) {
				// R, W に移動可能であれば、上、右、右で到達可能 
				if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posw.getpos()]) {
					canarrive |= destbit;
					setmovetable(667, j, aindextable, avitable);
				}
				// S に移動可能な場合
				else if (i & dist23umap[0][j][poss.getpos()]) {
					// W に移動可能であれば、右、上、右で到達可能 
					if (i & dist23umap[0][j][posw.getpos()]) {
						canarrive |= destbit;
						setmovetable(676, j, aindextable, avitable);
					}
					// T に移動可能であれば、右、右、上で到達可能 
					else if (i & dist23umap[0][j][post.getpos()]) {
						canarrive |= destbit;
						setmovetable(766, j, aindextable, avitable);
					}
				}
			}

			// zへの到達可能性を計算する。まず、zに移動可能である必要がある。
			if (i & dist23umap[1][j][posz.getpos()]) {
				// R, W, Z に移動可能であれば、上、右、右、隠蔽で到達可能 
				if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posw.getpos()] && i & dist23umap[0][j][posz.getpos()]) {
					canarriveh |= destbit;
					setmovetable(9667, j, aindextable, avitable);
				}
				// R, W, w に移動可能であれば、上、右、隠蔽、右で到達可能 
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[0][j][posw.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6967, j, aindextable, avitable);
				}
				// R, r, w に移動可能であれば、上、隠蔽、右、右で到達可能 
				else if (i & dist23umap[0][j][posr.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6697, j, aindextable, avitable);
				}
				// o, r, w に移動可能であれば、隠蔽、上、右、右で到達可能 
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][posr.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6679, j, aindextable, avitable);
				}
				// S, W, Z に移動可能であれば、右、上、右、隠蔽で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[0][j][posw.getpos()] && i & dist23umap[0][j][posz.getpos()]) {
					canarriveh |= destbit;
					setmovetable(9676, j, aindextable, avitable);
				}
				// S, W, w に移動可能であれば、右、上、隠蔽、右で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[0][j][posw.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6976, j, aindextable, avitable);
				}
				// S, s, w に移動可能であれば、右、隠蔽、上、右で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[1][j][poss.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6796, j, aindextable, avitable);
				}
				// o, s, w に移動可能であれば、隠蔽、右、上、右で到達可能 
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][poss.getpos()] && i & dist23umap[1][j][posw.getpos()]) {
					canarriveh |= destbit;
					setmovetable(6769, j, aindextable, avitable);
				}
				// S, T, Z に移動可能であれば、右、右、上、隠蔽で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[0][j][post.getpos()] && i & dist23umap[0][j][posz.getpos()]) {
					canarriveh |= destbit;
					setmovetable(9766, j, aindextable, avitable);
				}
				// S, T, t に移動可能であれば、右、右、隠蔽、上で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[0][j][post.getpos()] && i & dist23umap[1][j][post.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7966, j, aindextable, avitable);
				}
				// S, s, t に移動可能であれば、右、隠蔽、右、上で到達可能 
				else if (i & dist23umap[0][j][poss.getpos()] && i & dist23umap[1][j][poss.getpos()] && i & dist23umap[1][j][post.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7696, j, aindextable, avitable);
				}
				// o, s, t に移動可能であれば、隠蔽、右、右、上で到達可能 
				else if (i & dist23umap[1][j][poso.getpos()] && i & dist23umap[1][j][poss.getpos()] && i & dist23umap[1][j][post.getpos()]) {
					canarriveh |= destbit;
					setmovetable(7669, j, aindextable, avitable);
				}
			}
			uint32_t data;
			data = canarrive;
			wf2.write((char *)&data, sizeof(uint32_t));
			data = canarriveh;
			wf2.write((char *)&data, sizeof(uint32_t));
			wf2.write((char *)&aindextable, sizeof(uint64_t));
		}
	}
	wf2.close();

#if 0
	ifstream rf2;
	rf2.open("ysaidata2.dat", ios::in | ios::binary);
	const int bufsize2 = (1 << 17) * 4 * 4;
	uint32_t *buf2 = new uint32_t[bufsize2];
	rf2.read((char *)buf2, sizeof(uint32_t) * bufsize2);
	uint32_t *ptr2 = buf2;

	for (uint64_t i = 0; i < (1 << 17); i++) {
		for (int j = 0; j < 4; j++) {
			if (canarrivetable[0][j + 1][i] != *(ptr2++)) {
				cerr << "error d " << i << endl;
			}
			if (canarrivetable[1][j + 1][i] != *(ptr2++)) {
				cerr << "error e " << i << endl;
			}
			if (actionsindextable[j + 1][i] != *(uint64_t *)(ptr2)) {
				cerr << "error f " << i << endl;
			}
			ptr2 += 2;
		}
	}
	rf2.close();
#endif
#else
	ifstream rf2;
	rf2.open("ysaidata2.dat", ios::in | ios::binary);
	const int bufsize2 = (1 << 17) * 4 * 4;
	uint32_t *buf2 = new uint32_t[bufsize2];
	rf2.read((char *)buf2, sizeof(uint32_t) * bufsize2);
	uint32_t *ptr2 = buf2;

	for (uint64_t i = 0; i < (1 << 17); i++) {
		for (int j = 0; j < 4; j++) {
			canarrivetable[0][j +1][i] = *(ptr2++);
			canarrivetable[1][j + 1][i] = *(ptr2++);
			actionsindextable[j + 1][i] = *(uint64_t *)(ptr2);
			ptr2 += 2;
		}
	}
	rf2.close();
#endif

	// periodplacebb の読み込み
	ifstream pf;
	pf.open("count.tsv");
	if (pf.fail()) {
		cerr << "can't open count.tsv" << endl;
		for (int i = 0; i < PERIOD_MAX; i++) {
			for (int p = 0; p < 2; p++) {
				for (int w = 0; w < 3; w++) {
					periodplacebb[i][p][w].clear();
					periodplacebb[i][p][w] = ~periodplacebb[i][p][w];
					periodplaceintb[i][p][w].clear(0);
					periodplacemaxnum = 0;
				}
			}
		}
	}
	else {
		cerr << "ok." << endl;
		for (int i = 0; i < PERIOD_MAX; i++) {
			string txt;
			int num;
			pf >> txt >> num;
					//cerr << txt << "," << num << endl;
			for (int p = 0; p < 2; p++) {
				for (int w = 0; w < 3; w++) {
					pf >> txt >> num;
					//				cerr << txt << "," << num << endl;
					periodplacebb[i][p][w].clear();
					periodplaceintb[i][p][w].clear(0);
					for (int y = 0; y < height; y++) {
						for (int x = 0; x < width; x++) {
							pf >> num;
							if (num > 0) {
								if (i == 0 && p == 0 && w == 0) {
									periodplacemaxnum = num;
								}
								periodplacebb[i][p][w].set(Pos(x, y));
								periodplaceintb[i][p][w].set(Pos(x, y), num);
							}
						}
					}
							//		cerr << i << "," << p << "," << w << endl <<  periodplacebb[i][p][w];
					//cerr << i << "," << p << "," << w << endl << periodplacebyteb[i][p][w];
				}
			}
		}
	}
	pf.close();

	// 検証用のテーブルの作成
	for (auto p : Pos()) {
		int x = p.getx();
		int y = p.gety();
		withindist1bb[p.getpos()].clear();
		withindist3bb[p.getpos()].clear();
		for (int dx = -3; dx <= 3; dx++) {
			for (int dy = -3; dy <= 3; dy++) {
				if (abs(dx) + abs(dy) <= 1 && isinfield(x + dx, y + dy)) {
					withindist1bb[p.getpos()].set(x + dx, y + dy);
				}
				if (abs(dx) + abs(dy) <= 3 && isinfield(x + dx, y + dy)) {
					withindist3bb[p.getpos()].set(x + dx, y + dy);
				}
			}
		}
	}
}

ostream & operator<<(ostream& os, const Action &ac) {
	assert(ac.actionnum <= 5);
	os << static_cast<int>(ac.pid) << " ";
	for (int i = 0; i < ac.actionnum; i++) {
		os << static_cast<int>(ac.actions[i]) << " ";
	}
	os << "0" << endl;
	return os;
}

// canmoveup: 地上で移動可能な場所、canmoveunder: 隠蔽状態で移動可能な場所 の条件で、pos にいた場合に到達可能な場所の BitBoard を計算する
// canarriveup: 地上で到達可能な場所、canarriveunder:隠蔽状態で到達可能な場所
// num が 5 の場合は、すべての移動可能な場所を計算する。num が 1 の場合は、距離が 1 以内の移動可能な場所を計算する
void calccanarriveplace(BitBoard canmoveup, BitBoard canmoveunder, Pos pos, BitBoard& canarriveup, BitBoard& canarriveunder, int num) {
	//benchmarktimer.start();
	c4++;
	assert(num == 1 || num == 5);
	int posindex = pos.getpos();
	// 到達可能な場所の初期化
	canarriveup.clear();
	canarriveunder.clear();
	for (int i = 0; i < num; i++) {
		// uint64_t indexbit = 0;
		// uint64_t bitnum = 0;
		 //obstaclemaskbb から canmoveup のデータを使って、移動の計算に必要な周囲の障害物を表すビット列を取得する、
		//for (int j = 0; j < 4; j++) {
		//	indexbit |= PEXT64(canmoveup.d64[j], obstaclemaskbb[0][i][posindex].d64[j]) << bitnum;
		//	bitnum += _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[j]);
		//}
		// obstaclemaskbb から canmovedown のデータを使って、移動の計算に必要な周囲の障害物を表すビット列を取得する、
		//for (int j = 0; j < 4; j++) {
		//	indexbit |= PEXT64(canmoveunder.d64[j], obstaclemaskbb[1][i][posindex].d64[j]) << bitnum;
		//	bitnum += _mm_popcnt_u64(obstaclemaskbb[1][i][posindex].d64[j]);
		//}

		// for を使わないほうが早いのでこちらを採用する
		uint64_t indexbit = PEXT64(canmoveunder.d64[3], obstaclemaskbb[1][i][posindex].d64[3]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[1][i][posindex].d64[2]);
		indexbit |= PEXT64(canmoveunder.d64[2], obstaclemaskbb[1][i][posindex].d64[2]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[1][i][posindex].d64[1]);
		indexbit |= PEXT64(canmoveunder.d64[1], obstaclemaskbb[1][i][posindex].d64[1]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[1][i][posindex].d64[0]);
		indexbit |= PEXT64(canmoveunder.d64[0], obstaclemaskbb[1][i][posindex].d64[0]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[3]);
		indexbit |= PEXT64(canmoveup.d64[3], obstaclemaskbb[0][i][posindex].d64[3]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[2]);
		indexbit |= PEXT64(canmoveup.d64[2], obstaclemaskbb[0][i][posindex].d64[2]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[1]);
		indexbit |= PEXT64(canmoveup.d64[1], obstaclemaskbb[0][i][posindex].d64[1]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[0]);
		indexbit |= PEXT64(canmoveup.d64[0], obstaclemaskbb[0][i][posindex].d64[0]);

		// 盤の端にいた場合、盤外の場所のビット列は取得できない。盤外の場所のビットを補完する
		indexbit = PDEP64(indexbit, obstaclepdepmask[i][posindex]);

		// 移動可能な場所へ移動する行動の一覧を表示する（デバッグ用）
#if 0
		// 移動可能な場所を表すビット列を取得する
		uint64_t& canmovebit = actionsindextable[i][indexbit];
		cerr << "移動一覧" << endl;
		int count = 0;
		for (size_t j = 0; j < actiontable[i].size(); j++) {
			if (canmovebit & (static_cast<uint64_t>(1) << j)) {
				cerr << count << ":" << actiontable[i][j] << "  " << pos + actiontable[i][j].dest << (actiontable[i][j].changed ? " 隠" : "") << endl;
				count++;
			}
		}
		cerr << "到達可能な場所の数 " << count << endl;
#endif

		// 地上で到達可能な場所を表すビット列を取得する
		// 盤の端にいた場合、盤外の場所へは移動できないので、盤外の場所を表すビットを削除する
		uint64_t canarriveupbit = PEXT64(canarrivetable[0][i][indexbit], canarrivepextmask[i][posindex]);

		// 隠蔽状態で到達可能な場所を表すビット列を取得する
		uint64_t canarriveunderbit = PEXT64(canarrivetable[1][i][indexbit], canarrivepextmask[i][posindex]);

		// 地上と隠蔽状態で到達可能な場所を計算し、canarriveup と canarriveunder との OR を計算する
		for (int j = 0; j < 4; j++) {
			uint64_t maskbit = canarrivebb[i][posindex].d64[j];
			uint64_t popcnt = _mm_popcnt_u64(maskbit);
			canarriveup.d64[j] |= PDEP64(canarriveupbit, maskbit);
			canarriveunder.d64[j] |= PDEP64(canarriveunderbit, maskbit);
			canarriveunderbit >>= popcnt;
			canarriveupbit >>= popcnt;
		}
	}
//	benchmarktimer.stop();

}

// 近似的に移動可能な場所を計算する（侍の区画から、マンハッタン距離だけで計算する
void calccanarriveplaceapproximate(BitBoard canmoveup, BitBoard canmoveunder, Pos pos, BitBoard& canarriveup, BitBoard& canarriveunder, int num) {
	c4++;
	assert(num == 1 || num == 5);
	int posindex = pos.getpos();
	// 到達可能な場所の初期化
	canarriveup.clear();
	canarriveunder.clear();
	if (num == 1) {
		canarriveup = withindist1bb[posindex];
		canarriveunder = canarriveup & canmoveunder;
	}
	else {
		canarriveup = withindist3bb[posindex];
		canarriveunder = canarriveup & canmoveunder;
	}
}

void calccanarriveplacewithoutusingtable(BitBoard canmoveup, BitBoard canmoveunder, Pos pos, BitBoard& canarriveup, BitBoard& canarriveunder, int num) {
	c4++;
	assert(num == 1 || num == 5);
	int posindex = pos.getpos();
	// 到達可能な場所の初期化
	canarriveup.clear();
	canarriveunder.clear();
	int x = pos.getx();
	int y = pos.gety();
	// 今いる地点
	canarriveup.set(pos);
	if (canmoveunder.isset(pos)) {
		canarriveunder.set(pos);
	}
	// 上下左右
	{
		int dx[4] =  { +0, +0, -1, +1 };
		int dy[4] =  { -1, +1, +0, +0 };
		int dx2[4] = { +1, +1, +0, +0 };
		int dy2[4] = { +0, +0, -1, -1 };
		int dx3[4] = { +1, +1, -1, +1 };
		int dy3[4] = { -1, +1, -1, -1 };
		int dx4[4] = { -1, -1, +0, +0 };
		int dy4[4] = { +0, +0, +1, -1 };
		int dx5[4] = { -1, -1, -1, +1 };
		int dy5[4] = { -1, +1, +1, -1 };
		for (int i = 0; i < 4; i++) {
			int x2 = x + dx[i];
			int y2 = y + dy[i];
			int x3 = x + dx2[i];
			int y3 = y + dy2[i];
			int x4 = x + dx3[i];
			int y4 = y + dy3[i];
			int x5 = x + dx4[i];
			int y5 = y + dy4[i];
			int x6 = x + dx5[i];
			int y6 = y + dy5[i];
			if (isinfield(x2, y2)) {
				if (canmoveup.isset(x2, y2)) {
					canarriveup.set(x2, y2);
				}
				if (canmoveunder.isset(x2, y2) && 
					(canmoveup.isset(x2, y2) || canmoveunder.isset(x, y) || 
					(isinfield(x3, y3) && canmoveup.isset(x3, y3) && canmoveunder.isset(x3, y3) && canmoveunder.isset(x4, y4)) ||
						(isinfield(x5, y5) && canmoveup.isset(x5, y5) && canmoveunder.isset(x5, y5) && canmoveunder.isset(x6, y6)))) {
					canarriveunder.set(x2, y2);
				}
			}
		}
	}
	// ２つ上下左右
	{
		int dx[4] = { 0, 0, -1, 1 };
		int dy[4] = { -1, 1, 0, 0 };
		int dx2[4] = { 0, 0, -2, 2 };
		int dy2[4] = { -2, 2, 0, 0 };
		for (int i = 0; i < 4; i++) {
			int x2 = x + dx[i];
			int y2 = y + dy[i];
			int x3 = x + dx2[i];
			int y3 = y + dy2[i];
			if (isinfield(x3, y3)) {
				if (canmoveup.isset(x3, y3) &&
					(canmoveup.isset(x2, y2) ||
					(canmoveunder.isset(x, y) && canmoveunder.isset(x2, y2) && canmoveunder.isset(x3, y3)))) {
					canarriveup.set(x3, y3);
				}
				if (canmoveunder.isset(x3, y3) &&
					((canmoveup.isset(x2, y2) &&
					(canmoveup.isset(x3, y3) || canmoveunder.isset(x2, y2))) || (canmoveunder.isset(x, y) && canmoveunder.isset(x2, y2)))) {
					canarriveunder.set(x3, y3);
				}
			}
		}
	}
	// 斜めの4か所	
	{
		int dx[4] = { 0, 1, 0, -1 };
		int dy[4] = { -1, 0, 1, 0 };
		int dx2[4] = { 1, 0, -1, 0 };
		int dy2[4] = { 0, 1, 0, -1 };
		int dx3[4] = { 1, 1, -1, -1 };
		int dy3[4] = { -1, 1, 1, -1 };
		for (int i = 0; i < 4; i++) {
			int x2 = x + dx[i];
			int y2 = y + dy[i];
			int x3 = x + dx2[i];
			int y3 = y + dy2[i];
			int x4 = x + dx3[i];
			int y4 = y + dy3[i];
			if (isinfield(x4, y4)) {
				if (canmoveup.isset(x4, y4) &&
					(canmoveup.isset(x2, y2) || canmoveup.isset(x3, y3) ||
					(canmoveunder.isset(x, y) && (canmoveunder.isset(x2, y2) || canmoveunder.isset(x3, y3))))) {
					canarriveup.set(x4, y4);
				}
				if (canmoveunder.isset(x4, y4) &&
					((canmoveup.isset(x2, y2) && (canmoveup.isset(x4, y4) || canmoveunder.isset(x2, y2))) ||
					(canmoveup.isset(x3, y3) && (canmoveup.isset(x4, y4) || canmoveunder.isset(x3, y3))) ||
						(canmoveunder.isset(x, y) && (canmoveunder.isset(x2, y2) || canmoveunder.isset(x3, y3))))) {
					canarriveunder.set(x4, y4);
				}
			}
		}
	}
	// 距離３
	{
		int dx[28]  = { +0, +0, +0, +1, +0, +1, +1, +1, +1, +1, +0, +1, +0, +0, +0, +0, +0, -1, +0, -1, -1, -1, -1, -1, +0, -1, +0, +0 };
		int dy[28]  = { -1, -1, -1, +0, -1, +0, +0, +0, +0, +0, +1, +0, +1, +1, +1, +1, +1, +0, +1, +0, +0, +0, +0, +0, -1, +0, -1, -1 };
		int dx2[28] = { +0, +0, +1, +1, +1, +1, +2, +2, +2, +1, +1, +1, +1, +0, +0, +0, -1, -1, -1, -1, -2, -2, -2, -1, -1, -1, -1, +0 };
		int dy2[28] = { -2, -2, -1, -1, -1, -1, +0, +0, +0, +1, +1, +1, +1, +2, +2, +2, +1, +1, +1, +1, +0, +0, +0, -1, -1, -1, -1, -2 };
		int dx3[28] = { +0, +1, +1, +1, +2, +2, +2, +3, +2, +2, +2, +1, +1, +1, +0, -1, -1, -1, -2, -2, -2, -3, -2, -2, -2, -1, -1, -1 };
		int dy3[28] = { -3, -2, -2, -2, -1, -1, -1, +0, +1, +1, +1, +2, +2, +2, +3, +2, +2, +2, +1, +1, +1, +0, -1, -1, -1, -2, -2, -2 };
		for (int i = 0; i < 28; i++) {
			int x2 = x + dx[i];
			int y2 = y + dy[i];
			int x3 = x + dx2[i];
			int y3 = y + dy2[i];
			int x4 = x + dx3[i];
			int y4 = y + dy3[i];
			if (isinfield(x4, y4)) {
				if (canmoveup.isset(x4, y4) && canmoveup.isset(x2, y2) && canmoveup.isset(x3, y3)) {
					canarriveup.set(x4, y4);
				}
				if (canmoveunder.isset(x4, y4) &&
					((canmoveup.isset(x2, y2) &&
					((canmoveup.isset(x3, y3) && (canmoveup.isset(x4, y4) || canmoveunder.isset(x3, y3))) ||
						(canmoveunder.isset(x2, y2) && canmoveunder.isset(x3, y3)))) ||
						(canmoveunder.isset(x, y) && canmoveunder.isset(x2, y2) && canmoveunder.isset(x3, y3)))) {
					canarriveunder.set(x4, y4);
				}
			}
		}
	}
}


void calccanmoveaction(BitBoard canmoveup, BitBoard canmoveunder, Pos pos, Canmovebits& movebits, int num) {
	assert(num == 1 || num == 5);
	int posindex = pos.getpos();
	for (int i = 0; i < num; i++) {
		uint64_t indexbit = PEXT64(canmoveunder.d64[3], obstaclemaskbb[1][i][posindex].d64[3]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[1][i][posindex].d64[2]);
		indexbit |= PEXT64(canmoveunder.d64[2], obstaclemaskbb[1][i][posindex].d64[2]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[1][i][posindex].d64[1]);
		indexbit |= PEXT64(canmoveunder.d64[1], obstaclemaskbb[1][i][posindex].d64[1]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[1][i][posindex].d64[0]);
		indexbit |= PEXT64(canmoveunder.d64[0], obstaclemaskbb[1][i][posindex].d64[0]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[3]);
		indexbit |= PEXT64(canmoveup.d64[3], obstaclemaskbb[0][i][posindex].d64[3]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[2]);
		indexbit |= PEXT64(canmoveup.d64[2], obstaclemaskbb[0][i][posindex].d64[2]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[1]);
		indexbit |= PEXT64(canmoveup.d64[1], obstaclemaskbb[0][i][posindex].d64[1]);
		indexbit <<= _mm_popcnt_u64(obstaclemaskbb[0][i][posindex].d64[0]);
		indexbit |= PEXT64(canmoveup.d64[0], obstaclemaskbb[0][i][posindex].d64[0]);

		// 盤の端にいた場合、盤外の場所のビット列は取得できない。盤外の場所のビットを補完する
		indexbit = PDEP64(indexbit, obstaclepdepmask[i][posindex]);
		movebits.data[i] = actionsindextable[i][indexbit];
		// 移動可能な場所へ移動する行動の一覧を表示する（デバッグ用）
#if 0
		// 移動可能な場所を表すビット列を取得する
		uint64_t& canmovebit = actionsindextable[i][indexbit];
		cerr << "移動一覧" << endl;
		int count = 0;
		for (size_t j = 0; j < actiontable[i].size(); j++) {
			if (canmovebit & (static_cast<uint64_t>(1) << j)) {
				cerr << count << ":" << actiontable[i][j] << "  " << pos + actiontable[i][j].dest << (actiontable[i][j].changed ? " 隠" : "") << endl;
				count++;
			}
		}
		cerr << "到達可能な場所の数 " << count << endl;
#endif
	}
}

#ifdef LOADPARAM
void loadparam(double &param, char* argv, char *msg) {
	param = atof(argv);
	cerr << msg << " " << param << endl;
}
#endif

int main(int argc, char* argv[]) {
#ifdef DEBUGMSG
	cerr << "ver 15.10" << endl;
#endif
	// 時間を計測する
	Timer totaltime;
#ifdef LOADPARAM
	cerr << "load parameter" << endl;
	if (argc < 36) {
		cerr << "not enough parameter" << endl;
	}
	else {

		int num = 1;
		loadparam(HYOUKA_EARLY_BESTACTION, argv[num++], "HYOUKA_EARLY_BESTACTION");
		loadparam(HYOUKA_OCCUPY, argv[num++], "HYOUKA_OCCUPY");
		loadparam(HYOUKA_SIGHT, argv[num++], "HYOUKA_SIGHT");
		loadparam(HYOUKA_NOTALLYOCCUPY_INSIGHT, argv[num++], "HYOUKA_NOTALLYOCCUPY_INSIGHT");
		loadparam(HYOUKA_ENEMYOCCUPY_INSIGHT, argv[num++], "HYOUKA_ENEMYOCCUPY_INSIGHT");
		loadparam(HYOUKA_DISTFROMBASE, argv[num++], "HYOUKA_DISTFROMBASE");
		loadparam(HYOUKA_NOMOVE[0], argv[num++], "HYOUKA_NOMOVE[0]");
		loadparam(HYOUKA_NOMOVE[1], argv[num++], "HYOUKA_NOMOVE[1]");
		loadparam(HYOUKA_NOMOVE[2], argv[num++], "HYOUKA_NOMOVE[2]");
		loadparam(HYOUKA_PASS, argv[num++], "HYOUKA_PASS");
		loadparam(HYOUKA_APPEARED, argv[num++], "HYOUKA_APPEARED");
		loadparam(HYOUKA_LATTER_TURN, argv[num++], "HYOUKA_LATTER_TURN");
		loadparam(HYOUKA_RECOVERY[0][0][0], argv[num++], "HYOUKA_RECOVERY[0][0][0]");
		loadparam(HYOUKA_RECOVERY[0][0][1], argv[num++], "HYOUKA_RECOVERY[0][0][1]");
		loadparam(HYOUKA_RECOVERY[0][0][2], argv[num++], "HYOUKA_RECOVERY[0][0][2]");
		loadparam(HYOUKA_RECOVERY[0][1][0], argv[num++], "HYOUKA_RECOVERY[0][1][0]");
		loadparam(HYOUKA_RECOVERY[0][1][1], argv[num++], "HYOUKA_RECOVERY[0][1][1]");
		loadparam(HYOUKA_RECOVERY[0][1][2], argv[num++], "HYOUKA_RECOVERY[0][1][2]");
		loadparam(HYOUKA_RECOVERY[1][0][0], argv[num++], "HYOUKA_RECOVERY[1][0][0]");
		loadparam(HYOUKA_RECOVERY[1][0][1], argv[num++], "HYOUKA_RECOVERY[1][0][1]");
		loadparam(HYOUKA_RECOVERY[1][0][2], argv[num++], "HYOUKA_RECOVERY[1][0][2]");
		loadparam(HYOUKA_RECOVERY[1][1][0], argv[num++], "HYOUKA_RECOVERY[1][1][0]");
		loadparam(HYOUKA_RECOVERY[1][1][1], argv[num++], "HYOUKA_RECOVERY[1][1][1]");
		loadparam(HYOUKA_RECOVERY[1][1][2], argv[num++], "HYOUKA_RECOVERY[1][1][2]");
		loadparam(HYOUKA_CUREMUL_NORMAL, argv[num++], "HYOUKA_CUREMUL_NORMAL");
		loadparam(HYOUKA_CUREMUL_ENECANMOVE, argv[num++], "HYOUKA_CUREMUL_ENECANMOVE");
		loadparam(HYOUKA_CUREMUL_ALLYCANMOVE, argv[num++], "HYOUKA_CUREMUL_ALLYCANMOVE");
		loadparam(HYOUKA_CUREMUL_NORMAL_MAX, argv[num++], "HYOUKA_CUREMUL_NORMAL_MAX");
		loadparam(HYOUKA_CUREMUL_NORMAL_DIV, argv[num++], "HYOUKA_CUREMUL_NORMAL_DIV");
		loadparam(HYOUKA_CUREMUL_HIDDEN_MAX, argv[num++], "HYOUKA_CUREMUL_HIDDEN_MAX");
		loadparam(HYOUKA_CUREMUL_HIDDEN_DIV, argv[num++], "HYOUKA_CUREMUL_HIDDEN_DIV");
		//loadparam(HYOUKA_CUREMUL_HIDDEN_DANGER_MAX, argv[num++], "HYOUKA_CUREMUL_HIDDEN_DANGER_MAX");
		//loadparam(HYOUKA_CUREMUL_HIDDEN_DANGER_DIV, argv[num++], "HYOUKA_CUREMUL_HIDDEN_DANGER_DIV");
		loadparam(HYOUKA_CUREMUL_MATTACKHIDDEN_MAX, argv[num++], "HYOUKA_CUREMUL_MATTACKHIDDEN_MAX");
		loadparam(HYOUKA_CUREMUL_MATTACKHIDDEN_DIV, argv[num++], "HYOUKA_CUREMUL_MATTACKHIDDEN_DIV");
		loadparam(HYOUKA_CUREMUL_AMOVEHIDDEN_MAX, argv[num++], "HYOUKA_CUREMUL_AMOVEHIDDEN_MAX");
		loadparam(HYOUKA_CUREMUL_AMOVEHIDDEN_DIV, argv[num++], "HYOUKA_CUREMUL_AMOVEHIDDEN_DIV");
	}
#endif

#ifdef DEBUG
	// デバッグ用のパラメータ処理
	debugturn = -1;
	debuganalyze = false;
	debughyouka = false;
	debugusealpha = false;

	// 分析に関する制限時間をデフォルトで100秒にする
	analyzetimelimit = 100000;
	timelimit = 100000;

	if (argc >= 2) {
		if (strchr(argv[1], 'h') != nullptr) {
			cerr << "samurai2016.exe [ahprsu1] turn" << endl << "a: 指定した turn の分析の詳細を表示" << endl << "r: 指定した turn の分析の結果を表示" << endl << "p: 指定した turn の過去の分析の結果を表示" << endl << "s: 指定した turn の思考の評価値の詳細を表示" << endl << "t: 各ターンに制限時間を設ける" << endl << "h: ヘルプを表示" << endl;
		}
		if (strchr(argv[1], 'a') != nullptr) {
			cerr << "debug analyze" << endl;
			debuganalyze = true;
		}
		if (strchr(argv[1], 'r') != nullptr) {
			cerr << "debug analyze result" << endl;
			debuganalyzeresult = true;
		}
		if (strchr(argv[1], 'p') != nullptr) {
			cerr << "debug analyze past" << endl;
			debuganalyzepast = true;
		}
		if (strchr(argv[1], 's') != nullptr) {
			cerr << "debug hyouka" << endl;
			debughyouka = true;
		}
		if (strchr(argv[1], 'u') != nullptr) {
			cerr << "debug use alpha" << endl;
			debugusealpha = true;
		}
		if (strchr(argv[1], 'f') != nullptr) {
			cerr << "save verify data" << endl;
			saveverifydata = true;
		}
		if (strchr(argv[1], 't') != nullptr) {
			cerr << "debug time limit" << endl;
			analyzetimelimit = 50;
			timelimit = 190;
		}
		if (strchr(argv[1], 'd') != nullptr) {
			// 本選提出後にデバッグしたバージョン
			cerr << "debugged version" << endl;
			submitversion = false;
		}
		if (strchr(argv[1], 'b') != nullptr) {
			// 移動可能な区画の計算速度を計算するためのベンチマークを実行するかどうか
			cerr << "benchmark mode" << endl;
			benchmarkflag = true;
		}
		if (strchr(argv[1], 'w') != nullptr) {
			// ベンチマーク時に、calccanarriveplaceをテーブルを使わずに計算するかどうか
			cerr << "calccanarriveplace without using table" << endl;
			calccanarriveplacewithoutusingtableflag = true;
		}
		if (strchr(argv[1], '3') != nullptr) {
			// 侍が移動可能な区画を厳密に計算しない
			cerr << "donot calc arriveplace strictly" << endl;
			donotcalcarriveplacestrictly = true;
		}
		// 以下検証用のオプション。数字で表すことにする
		if (strchr(argv[1], '1') != nullptr) {
			// analyze で1回分の行動しか計算しない
			cerr << "analyze only one action" << endl;
			analyzeonlyoneaction = true;
		}
		if (strchr(argv[1], '2') != nullptr) {
			// analyze の分析結果をrecalculaterecordsで利用しない
			cerr << "donot use analyze result in recalculaterecords" << endl;
			donotuseanalyzeresultinrecalculaterecords = true;
		}
		if (strchr(argv[1], '3') != nullptr) {
			// 侍が移動可能な区画を厳密に計算しない
			cerr << "donot calc arriveplace strictly" << endl;
			donotcalcarriveplacestrictly = true;
		}
	}
	if (argc >= 3) {
		debugturn = strtol(argv[2], nullptr, 0);
		cerr << "analyze turn " << debugturn << endl;
	}
#endif
	// 手番情報の読み込み
	playOrder = getInt();

#ifdef DONOTUSEAI
	// デバッグモード時に、自分の行う行動をAIではなく、（visualizerの行動付きのファイルを使う）ファイルの中に記された行動を使って行うようにする。
	// 武器ID
	int wid;
	// ターン毎に行った行動をファイルから読み込む。自分のターンの行動なので、2ターンおきの行動を読み込む。
	for (int t = 0; t < 96; t += 2) {
		// 武器IDを読み込む
		cin >> wid;
		// 行動を読み込み、recactionに記録する。
		int action = 0;
		int mul = 1;
		// 移動先の相対座標
		int x = 0;
		int y = 0;
		int num;
		while (1) {
			cin >> num;
			if (num == 0) {
				break;
			}
			action += num * mul;
			switch (num) {
			case 5:
				y++;
				break;
			case 6:
				x++;
				break;
			case 7:
				y--;
				break;
			case 8:
				x--;
				break;
			}
			mul *= 10;
		}
		recaction[t + playOrder].setaction(action, wid, x, y);
	}
#endif

	// 初期化処理。初期化にかかった時間を表示する
	Timer inittimer;
	// playOrder を読み込んだ後に init を実行する必要がある点に注意
	init();

	cerr << inittimer;
	// 初期化処理終了後 0 を出力する。
	cout << 0 << endl;

	benchmarktimer.reset();
	benchmarktimer.stop();

	c4 = 0;

	GameInfo info, previnfo;
	while (true) {
		info.readTurnInfo();
		timer.reset();

#ifdef DEBUG
		// ベンチマークモード
		if (benchmarkflag) {
			benchmark(info);
			if (info.turn >= 94) {
				cout << "total time " << totaltime.gettime() << " benchmark time " << benchmarktimer.getmicrotime() << "microsec" << endl;
				break;
			}
			continue;
		}
#endif
		// 0, 1 ターン目は前のターンがないので、現在のターンの情報を previnfo としてコピーして中身を修正
		if (info.turn <= 1) {
			previnfo = info;
			for (int i = 0; i < 3; i++) {
				previnfo.placebb[0][1][i].clear();
				previnfo.placebb[1][1][i].clear();
				previnfo.placebb[0][1][i].set(homepos[1][i]);
				previnfo.sstates[1][i].done = false;
				previnfo.prevactiontype[i] = PREVACTION_MOVE;
			}
		}
		// プレーヤーの直前の行動をコピー
		for (int i = 0; i < 3; i++) {
			info.prevactiontype[i] = previnfo.prevactiontype[i];
		}

		// 状況を分析する
		Timer analyzetimer;
		info.analyze(previnfo);
#ifdef DEBUGMSG
		cerr << "analyze time                                  " << analyzetimer;
#endif
		hc = 0;

		double maxhyouka = 0;
		// 24ターン以前の場合はあらかじめ用意しておいた行動を earlyturnbestaction に代入する（この行動は評価に HYOUKA_EARLY_BESTACTION だけ加算される）
		if (info.turn < 24) {
			for (int i = 0; i < 3; i++) {
				int t = static_cast<int>(floor(info.turn / 6)) * 6 + playOrder + i * 2;
				earlyturnbestaction[i].setaction(autoactions[t][0], autoactions[t][1], autoactions[t][2], autoactions[t][3]);
			}
		}
		// 最善手を計算する関数を呼び出す。
		Timer bestactiontimer;
		maxhyouka = info.calcbestaction();

		if (timer.gettime() > timelimit) {
			ttimeovercount++;
		}
		// 最善手のデバッグ表示
#ifdef DEBUGMSG
		cerr << bestactiontimer;
		cerr << "best action " << info.bestaction << " hyouka " << maxhyouka << " action num " << checkactioncount << " hyouka count " << hc << endl;
#endif

#ifdef DONOTUSEAI
		// デバッグ時に記録された行動をとる場合、計算した最善手と記録された行動が異なる場合は、メッセージを表示する
		if (recaction[info.turn] != info.bestaction) {
			cerr << "diffrent action" << endl;
		}
		// 記録された行動を最善手に差し替える
		info.bestaction = recaction[info.turn];
#endif

#ifdef DEBUGRTIME
		while (timer.gettime() < ((rtime[info.turn] < 190) ? rtime[info.turn] : 190)) {}
#endif
		//t1 += 2;
		// 最善手を出力する
		cout << info.bestaction;
		cout.flush();

		// デバッグ表示
#ifdef DEBUGMSG
		cerr << info.bestaction;
		cerr << "total time                                         " << timer << endl;
#endif
		// 時間が 200ms を越えていた場合はタイムオーバーのデバッグ表示
		if (timer.gettime() >= 200) {
			cerr << "warning time out!" << endl;
		}


		// 94ターン以上の場合は、最終ターンなので終了する（95の時にこの先を実行するとメモリを破壊する！）
		if (info.turn >= 94) {
			ofstream wf2;
#ifdef DEBUG
			if (saveverifydata) {
				wf2.open("verify.dat", ios::out | ios::app);
			}
			//for (int i = 0; i < info.turn; i++) {
			//	cerr << "turn " << i << endl;
			//	cerr << records.lastoccupyplnum[i];
			//	cerr << records.lastoccupyturn[i];
			//}
			if (debuganalyzeresult) {
				int total = 0;
				for (int t = playOrder; t < 96; t += 2) {
					cerr << "Turn " << setw(2) << t << " ";
					int sum = 0;
					for (int w = 0; w < 3; w++) {
						cerr << setw(3) << epopcnt[w][ALL][t] << " ";
						sum += epopcnt[w][ALL][t];
					}
					cerr << setw(3) << sum << endl;
					total += sum;
				}
				cerr << "Total " << total << endl;
				if(saveverifydata) {
					wf2 << total << ",";
				}
			}
#endif
			cerr << "total time " << totaltime.gettime() << endl;
			cerr << "analyze timeover count " << atimeovercount << endl;
			cerr << "think timeover count " << ttimeovercount << endl;
			//cerr << "caclcanmoveplace count " << c4 << endl;
#ifdef DEBUG
			if (saveverifydata) {
				wf2 << atimeovercount << "," << ttimeovercount << "," << c4 << "," << totaltime ;
				wf2.close();
			}
#endif

#ifdef DEBUGMSG
			cerr << ec1 << "," << ec2 << endl;
			cerr << attackplacecount1 << "," << attackplacecount2 << endl;
			cerr << canattackandmovecount1 << "," << canattackandmovecount2 << endl;
#endif

			break;
		}

		// 最善手の行動を反映する
		Action& ac = info.bestaction;
		SamuraiState& ss = info.sstates[0][ac.pid];

		// 確認できる最後の占領状態の次のターンの情報をコピーする。この後のプレーヤーの占領行動は、この次のターンに行ったものとして記録する
		records.board[info.turn + 1] = records.board[info.turn];
		records.lastoccupyturn[info.turn + 1] = records.lastoccupyturn[info.turn];
		records.lastoccupyplnum[info.turn + 1] = records.lastoccupyplnum[info.turn];
		records.allyattackplnum[info.turn + 1] = -1;

		// 占領状況の更新
		for (int i = 0; i < 10; i++) {
			records.occupybb[info.turn + 1][i] = records.occupybb[info.turn][i];
		}
		// 移動前の場所
		Pos prevpos = ss.pos;
		// 移動前に隠蔽状態であったか
		bool prevhidden = ss.hidden;
		// 移動したか
		bool moved = false;
		// 攻撃したか
		bool attacked = false;
		// 攻撃前に移動したか
		bool movedbeforeattack = false;
		// 相手の視界内の可能性のある場所で、攻撃によって変化した場所の数
		int changednuminenemysight = 0;
		// 行動を一つ一つ反映する
		for (int i = 0; i < ac.actionnum; i++) {
			// 移動行動の処理
			if (ac.actions[i] >= 5 && ac.actions[i] <= 8 && moved == false) {
				bool hidden = ss.hidden ^ ac.changed;
				info.move(ac.pid, ss.pos, ss.hidden, ss.pos + ac.dest, hidden);
				moved = true;
			}
			// 攻撃行動の処理
			else if (ac.actions[i] >= 1 && ac.actions[i] <= 4) {
				changednuminenemysight = info.attack(ac.pid, ac.actions[i] - 1, true);
				if (moved == true) {
					movedbeforeattack = true;
				}
				attacked = true;
			}
		}
		info.calcprevactiontype(movedbeforeattack ? 1 : (attacked ? 2 : 0), ac.pid, changednuminenemysight, prevpos, prevhidden);

#ifdef DEBUGMSG
		cerr << "prevactiontype " << info.prevactiontype[ac.pid] << " changednuminenemysight " << changednuminenemysight << endl;
#endif
		// 記録の appearxxbb を更新
		records.appearplbb[info.turn + 1] = info.appearplbb;
		records.appearallybb[info.turn + 1] = info.appearallybb;
		records.appearenemybb[info.turn + 1] = info.appearenemybb;
		// 行動済とする
		ss.done = true;

		// 現時点での info を prevturn にコピーする
		previnfo = info;
	}
}

#ifdef DEBUG
void benchmark(GameInfo& info) {
	for (int w = 0; w < 3; w++) {
		SamuraiState &ss = info.sstates[0][w];
		BitBoard canmoveup, canmoveunder, canarriveup, canarriveunder;
		canmoveup = ~(info.appearplbb | cannotenterbb[ALLY][w]);
		canmoveunder = BitBoard::andnot(cannotenterbb[ALLY][w], records.occupybb[info.turn][allyindex]);
		if (ss.hidden == false) {
			benchmarktimer.start();
			if (!calccanarriveplacewithoutusingtableflag) {
				for (int i = 0; i < 1000; i++) {
					calccanarriveplace(canmoveup, canmoveunder, ss.pos, canarriveup, canarriveunder);
				}
			}
			else {
				for (int i = 0; i < 1000; i++) {
					calccanarriveplacewithoutusingtable(canmoveup, canmoveunder, ss.pos, canarriveup, canarriveunder);
				}
			}
			benchmarktimer.stop();
		}
		else {
			benchmarktimer.start();
			if (!calccanarriveplacewithoutusingtableflag) {
				for (int i = 0; i < 1000; i++) {
					calccanarriveplace(canmoveunder, canmoveup, ss.pos, canarriveunder, canarriveup);
				}
			}
			else {
				for (int i = 0; i < 1000; i++) {
					calccanarriveplacewithoutusingtable(canmoveunder, canmoveup, ss.pos, canarriveunder, canarriveup);
				}
			}
			benchmarktimer.stop();
		}
		//cerr << "Turn " << (int)info.turn << " " << w << endl << canarriveup << canarriveunder;
	}
}
#endif