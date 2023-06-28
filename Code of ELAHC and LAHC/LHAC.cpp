#include<iostream>
#include<cstdio>
#include<cstring>
#include<ctime>
#include<cstdlib>
#include<algorithm>
#include<cmath>
#include<string>
#include<queue>
#include<vector>
#include<map>
#include<set>
#include<utility>
#include<iomanip>
using namespace std;
int randomInt(int leftBound, int rightBound) {
	return leftBound + int((rightBound - leftBound) * (0.999999 * rand() / RAND_MAX));
}

const int MAXM = 128, MAXN = 256; // 排列个数与排列长度
int n, m;
double everytime;

/*
 * borda count 排列聚合
 * @param perm: m个长度为n的排列
 * @param weight: n个位置的权重
 * @return 聚合后的排列
 */

int* borda(int** perm, int* weight) {
	pair<int, int> val[n];
	for (int i = 0; i < n; i++)
		val[i] = make_pair(0, i + 1);
	for (int i = 0; i < m; i++)
		for (int j = 0; j < n; j++)
			val[perm[i][j]].first += weight[j];
	int* ret = new int[n];
	for (int i = n - 1; i >= 0; i--)
		ret[i] = val[i].second;
	return ret;
}

/*
 * 归并排序求逆序对个数
 * @param v: 待排序数组
 * @param L: 排序区间左端点
 * @param R: 排序区间右端点
 * @return 逆序对个数
 */

int rev_order_pair(int* v, int L, int R) {
	static int tmp[MAXN];
	if (L >= R)
		return 0;
	int mid = (L + R) / 2;
	int ret = rev_order_pair(v, L, mid) + rev_order_pair(v, mid + 1, R);
	int i = L, j = mid + 1, k = L;
	while (i <= mid && j <= R) {
		if (v[i] < v[j])
			tmp[k++] = v[i++];
		else {
			tmp[k++] = v[j++];
			ret += mid - i + 1;
		}
	}
	while (i <= mid)
		tmp[k++] = v[i++];
	while (j <= R) {
		tmp[k++] = v[j++];
		ret += mid - i + 1;
	}
	for (int i = L; i <= R; i++)
		v[i] = tmp[i];
	return ret;
}

/*
 * 求两个排列的tau距离
 * @param perm1: 排列1
 * @param perm2: 排列2
 * @return tau距离
 */

int tau(int* perm1, int* perm2) {
	static int occur[MAXN], iperm1[MAXN], iperm2[MAXN];
	memset(occur, 0, (n + 1) * sizeof(int));
	for (int i = 0; i < n; i++)
		occur[perm1[i]]++, occur[perm2[i]]++;
	int r = 0;
	for (int i = 0; i < n; i++) {
		if (perm1[i] == 0) break;
		if (occur[perm1[i]] == 2)
			iperm1[r++] = perm1[i];
	}
	r = 0;
	for (int i = 0; i < n; i++) {
		if (perm2[i] == 0) break;
		if (occur[perm2[i]] == 2)
			iperm2[r++] = perm2[i];
	}
	if (r <= 1)
		return 0;
	pair<int, int>* p = new pair<int, int>[r];
	for (int i = 0; i < r; i++)
		p[i] = make_pair(iperm1[i], iperm2[i]);
	sort(p, p + r);
	int* perm = new int[r];
	for (int i = 0; i < r; i++)
		perm[i] = p[i].second;
	int ret = rev_order_pair(perm, 0, r - 1);
	delete p;
	delete perm;
	return ret;
}

double eval(int** perm, int* cur) {
	int ret = 0;
	for (int i = 0; i < m; i++)
		ret += tau(perm[i], cur);
	return 1.0 * ret / m;
}

void allocate(int**& arr, int m, int n) {
	arr = new int* [m];
	for (int i = 0; i < m; i++)
		arr[i] = new int[n];
}
void erase(int**& arr, int m) {
	for (int i = 0; i < m; i++)
		delete arr[i];
	delete arr;
}
int** Index;
void initialize(int** perm) {
	if (Index == NULL)
		allocate(Index, MAXM, MAXN);
	for (int i = 0; i < m; i++)
		for (int j = 0; j <= n; j++)
			Index[i][j] = -1;
	for (int i = 0; i < m; i++)
		for (int j = 0; j < n; j++)
			Index[i][perm[i][j]] = j;
}

int comp(int x, int y) {
	if (x < y) return -1;
	else if (x > y) return 1;
	return 0;
}

double costDelta(int** perm, int* nxt, int x, int y) {
	if (x == y)return 0;
	int ret = 0;
	for (int i = 0; i < m; i++) {
		if (perm[i][x] > perm[i][y]) swap(x, y);
		if (comp(nxt[x], nxt[y]) == 1)
			ret++;
		else
			ret--;
		for (int j = perm[i][x] + 1; j <= perm[i][y] - 1; j++) {
			if (comp(nxt[Index[i][j]], nxt[y]) != comp(nxt[Index[i][j]], nxt[x])) {
				if (comp(nxt[Index[i][j]], nxt[y]) == 1)
					ret++;
				else
					ret--;
			}
			if (comp(nxt[x], nxt[Index[i][j]]) != comp(nxt[y], nxt[Index[i][j]])) {
				if (comp(nxt[x], nxt[Index[i][j]]) == 1)
					ret++;
				else
					ret--;
			}
		}
	}
	return 1.0 * ret / m;
}



int* LAHC(int** perm, int* weight, int beginWith, int Lh, double timeCutoff, double timeSpan) {
	double prevUpdTime = clock(), startTime = clock(), printTime = timeSpan;
	int* cur = new int[n];

	if (!beginWith) {
		cur = new int[n];
		for (int i = 0; i < n; i++)
			cur[i] = i + 1;
		random_shuffle(cur, cur + n);
	}
	else if (beginWith == -1) //specified begining
		cur = weight;
	else //beginWithBorda
		cur = borda(perm, weight);

	int* nxt = new int[n];
	int* best = new int[n];
	memcpy(nxt, cur, n * sizeof(int));
	memcpy(best, cur, n * sizeof(int));
	double curCost = eval(perm, cur), bestCost;
	//printf("initial: %.4f\n",curCost);
	bestCost = curCost;
	double* f = new double[Lh];
	for (int i = 0; i < Lh; i++)
		f[i] = curCost;
	long long Iter;
	//total time limit
	for (Iter = 0; (clock() - startTime) / CLOCKS_PER_SEC <= timeCutoff; Iter++) {
		//cutoff time limit
		//for(Iter=0;(clock()-prevUpdTime)/CLOCKS_PER_SEC<=timeCutoff;Iter++){

		if ((clock() - startTime) / CLOCKS_PER_SEC >= printTime) {
			//printf("%.4f ", bestCost);
			printTime += timeSpan;
		}

		int id1 = randomInt(0, n), id2 = randomInt(0, n);
		while (id1 == id2)
			id2 = randomInt(0, n);
		swap(nxt[id1], nxt[id2]);
		//double nxtCost = eval(perm, nxt);
		double nxtCost = curCost + costDelta(perm, nxt, id1, id2);
		int v = Iter % Lh;
		if (nxtCost < f[v] || nxtCost <= curCost) {
			curCost = nxtCost;
			swap(cur[id1], cur[id2]);
			if (curCost < bestCost) {
				memcpy(best, cur, n * sizeof(int));
				bestCost = curCost;
				//best = cur;
				prevUpdTime = clock();
			}
		}
		else
			swap(nxt[id1], nxt[id2]);
		if (curCost < f[v])
			f[v] = curCost;

		// if (Iter % 1 == 0) {
		// 	printf("nxtCost: %.4f\n", nxtCost);
		// 	printf("curCost: %.4f\n", curCost);
		// 	printf("bestCost: %.4f\n", bestCost);
		// }
	}
	//printf("\n");
	//printf("time spend find best %.4f\n", 1.0 * (prevUpdTime - startTime) / CLOCKS_PER_SEC);
	everytime=1.0 * (prevUpdTime - startTime) / CLOCKS_PER_SEC;
	return best;
}

double test_LAHC(char* INPUT, int Lh, double timeCutoff) {
	double curCost;
	freopen(INPUT, "r", stdin);
	float f;
	scanf("%d%d%f", &n, &m, &f);
	int** v;
	allocate(v, m, n);
	for (int i = 0; i < m; i++)
		for (int j = 0; j < n; j++)
			scanf("%d", &v[i][j]);
	initialize(v);
	int* w = new int[n];
	for (int i = 0; i < n; i++)
		w[i] = n - i;
	int* cur = LAHC(v, w, 0, Lh, timeCutoff, 1);
	curCost = eval(v, cur);
	delete cur;
	delete w;
	erase(v, m);
	return curCost;
}

void test_all_data(char* OUTPUT, int repeat_times = 10) {
	freopen(OUTPUT, "w", stdout);
	char* DIR[] = { "MM050n0.001dataset02.txt", "MM050n0.001dataset11.txt","MM100n0.200dataset05.txt","MM100n0.200dataset01.txt","MM150n0.100dataset17.txt","MM150n0.100dataset08.txt","MM200n0.010dataset13.txt","MM200n0.010dataset04.txt","MM250n0.001dataset10.txt","MM250n0.001dataset01.txt"};
	char INPUT[128];
	const int LhList[10] = { 1, 10, 100, 300, 600, 1000, 3000, 10000, 30000, 50000 };
	for (int i = 0; i < 10; i++) {
		//printf("%s:\n", DIR[i]);
		//for (int j = 6; j <= 6; j++) {
			//if (j <= 9)
			//	sprintf(INPUT, "%s/dataset0%d.txt", DIR[i], j);
			//else
			//	sprintf(INPUT, "%s/dataset%d.txt", DIR[i], j);
		sprintf(INPUT, "%s", DIR[i]);
		printf("%s:\n", INPUT);
		for (int Lh = 6; Lh < 7; Lh++) {
			//printf("Lh=%d:\n", LhList[Lh]);
			double avg = 0, best = 1e9;
			double timeavg=0.0;
			for (int k = 0; k < repeat_times; k++) {
				double res = test_LAHC(INPUT, LhList[Lh],600);
				timeavg+=everytime;
				avg += res;
				if (res < best)
					best = res;
			}
			avg /= repeat_times;
			timeavg/=repeat_times;
			printf("avg: %.4f, best: %.4f, avgtime: %.4f\n", avg, best,timeavg);
		}
		//}
	}
}

int main() {
	srand(time(NULL));
	test_all_data("Lout1.txt");
	return 0;
}
