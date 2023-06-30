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
#include<assert.h>
using namespace std;
int randomInt(int leftBound, int rightBound) {
	return leftBound + int((rightBound - leftBound) * (0.999999 * rand() / RAND_MAX));
}
const int MAXM = 128, MAXN = 256;
const long long INF = 1LL << 60;
int n, m;

void allocate(int**& arr, int m, int n) {
	arr = new int* [m];
	for (int i = 0; i < m; i++)
		arr[i] = new int[n];
}
void erase(int**& arr, int m) {
	for (int i = 0; i < m; i++)
		if (arr[i] != NULL)
			delete arr[i];
	delete arr;
}

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


int tau(int* perm1, int* perm2) {
	pair<int, int>* p = new pair<int, int>[n];
	for (int i = 0; i < n; i++)
		p[i] = make_pair(perm1[i], perm2[i]);
	sort(p, p + n);
	int* perm = new int[n];
	for (int i = 0; i < n; i++)
		perm[i] = p[i].second;
	int ret = rev_order_pair(perm, 0, n - 1);
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

int** Index;
void initialize(int** perm) {
	if (Index == NULL)
		allocate(Index, MAXM, MAXN);
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
		if (perm[i][x] > perm[i][y])swap(x, y);
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
	printf("initial: %.4f\n", curCost);
	bestCost = curCost;
	double* f = new double[Lh];
	for (int i = 0; i < Lh; i++)
		f[i] = curCost;
	long long Iter;
	//total time limit
	for (Iter = 0; (clock() - startTime) / CLOCKS_PER_SEC <= timeCutoff; Iter++) {
		//cutoff time limit
		//for(Iter=0;(clock()-prevUpdTime)/CLOCKS_PER_SEC<=timeCutoff;Iter++) {

		if ((clock() - startTime) / CLOCKS_PER_SEC >= printTime) {
			printf("%.4f ", bestCost);
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
				prevUpdTime = clock();
			}
		}
		else
			swap(nxt[id1], nxt[id2]);
		if (curCost < f[v])
			f[v] = curCost;
	}
	printf("\n");
	printf("[LAHC] total iters: %lld\n", Iter);
	printf("[LAHC] time spend find best %.4f\n", 1.0 * (prevUpdTime - startTime) / CLOCKS_PER_SEC);
	return best;
}

int* ELAHC(int** perm, int* weight, int beginWith, int Lh, double timeCutoff, double timeSpan) {
	double prevUpdTime = clock(), startTime = clock(), printTime = 0, prevUpdIter = 0;
	int* cur;
	if (!beginWith) {
		cur = new int[n];
		for (int i = 0; i < n; i++)
			cur[i] = i + 1;
		random_shuffle(cur, cur + n);
	}
	else if (beginWith == -1) //specified begining
		cur = weight; //以crossover的结果为起点搜索
	else //beginWithBorda
		cur = borda(perm, weight);
	int* nxt = new int[n];
	int* best = new int[n];
	memcpy(nxt, cur, n * sizeof(int));
	memcpy(best, cur, n * sizeof(int));
	double curCost = eval(perm, cur), bestCost, prevCost;
	//printf("initial: %.4f\n", curCost);
	bestCost = curCost;
	double* f = new double[Lh];
	for (int i = 0; i < Lh; i++)
		f[i] = curCost;
	int N = Lh;
	double maxF = curCost;
	long long Iter;
	//total time limit
	//for (Iter = 0; (clock() - startTime) / CLOCKS_PER_SEC <= timeCutoff && (clock() - prevUpdTime) / CLOCKS_PER_SEC <= 1800; Iter++) {
		//cutoff time limit
		//for(Iter=0;(clock()-prevUpdTime)/CLOCKS_PER_SEC<=timeCutoff;Iter++){
		//cutoff iters
	for(Iter=0;Iter-prevUpdIter<=timeCutoff;Iter++){

		if ((clock() - startTime) / CLOCKS_PER_SEC >= printTime) {
			//printf("%.4f ", bestCost);
			printTime += timeSpan;
		}

		prevCost = curCost;
		int id1 = randomInt(0, n), id2 = randomInt(0, n);
		while (id1 == id2)
			id2 = randomInt(0, n);
		swap(nxt[id1], nxt[id2]);

		/*
		int cnt = 0;
		for(int i = 0; i < n; i++) {
			if(i == id2)
				nxt[cnt++] = cur[id1];
			if(i != id1)
				nxt[cnt++] = cur[i];
		}
		*/

		//double nxtCost = eval(perm, nxt);
		double nxtCost = curCost + costDelta(perm, nxt, id1, id2);
		//assert(fabs(curCost+costDelta(perm, nxt, id1, id2)-nxtCost)<1e-7);
		if (fabs(nxtCost - curCost) < 1e-7 || nxtCost < maxF) {
			swap(cur[id1], cur[id2]);
			//memcpy(cur, nxt, n * sizeof(int));
			curCost = nxtCost;
			if (curCost < bestCost) {
				memcpy(best, cur, n * sizeof(int));
				bestCost = curCost;
				prevUpdTime = clock();
				prevUpdIter = Iter;
			}
		}
		else {
			swap(nxt[id1], nxt[id2]);
		}
		int v = Iter % Lh;
		if (curCost > f[v])
			f[v] = curCost;
		else if (curCost < f[v] && curCost < prevCost) {
			if (fabs(f[v] - maxF) < 1e-7)
				N--;
			f[v] = curCost;
			if (!N) {
				maxF = -1;
				for (int j = 0; j < Lh; j++) {
					if (maxF < f[j])
						maxF = f[j], N = 1;
					else if (fabs(maxF - f[j]) < 1e-7)
						N++;
				}
			}
		}
	}
	//printf("\n");
	//printf("[ELAHC] total iters: %lld \n", Iter);
	//printf("[ELAHC] time spend find best %.4f\n", 1.0 * (prevUpdTime - startTime) / CLOCKS_PER_SEC);
	if (cur) delete cur;
	delete f;
	delete nxt;
	return best;
}

int** pairWise;
int* CPSX(int* perm1, int* perm2) {
	if (pairWise == NULL)
		allocate(pairWise, MAXN, MAXN);
	int* ret = new int[n];
	for (int i = 0; i < n; i++)
		for (int j = i + 1; j < n; j++)
			pairWise[perm1[i] - 1][perm1[j] - 1]++, pairWise[perm2[i] - 1][perm2[j] - 1]++;
	pair<int, int>* item = new pair<int, int>[n];
	int item_length = 0;
	for (int i = 0; i < n; i++) {
		int tmpCnt = 0;
		for (int j = 0; j < n; j++)
			if (pairWise[i][j] == 2)
				tmpCnt++;
		item[item_length++] = make_pair(-tmpCnt, i + 1);
	}
	sort(item, item + item_length);
	for (int i = 0; i < n;) {
		int j = i;
		while (j < n && item[j].first == item[i].first)
			j++;
		random_shuffle(item + i, item + j);
		for (int k = i; k < j; k++)
			ret[k] = item[k].second;
		i = j;
	}
	delete item;
	return ret;
}

bool exist[MAXN];
void mark_exist(int* perm, int x, int y) {
	for (int i = x; i <= y; i++)
		exist[perm[i]] = true;
}
void clear_exist(int* perm, int x, int y) {
	for (int i = x; i <= y; i++)
		exist[perm[i]] = false;
}

int* memetic(int** perm, int* weight, bool beginWithBorda, int Lh, double timeCutoff, double timeSpan, int populationSize, long long maxIter, int totalTime) {
	double startTime = clock(), prevUpdTime;
	int** population = new int* [populationSize];
	double* cost = new double[populationSize];
	double bestCost = 1e9;
	int* best = new int[n];
	int curPopulationSize = 0;
    int maxNoImprove = 60;
	int noImprove = 0;
	for (int i = 0; i < populationSize && (clock() - startTime) / CLOCKS_PER_SEC <= totalTime; i++) {
		population[i] = ELAHC(perm, weight, beginWithBorda, Lh, timeCutoff, timeSpan);
		double curCost = eval(perm, population[i]);
		curPopulationSize = i;
		cost[i] = curCost;
		if (curCost < bestCost) {
			bestCost = curCost;
			memcpy(best, population[i], n * sizeof(int));
			prevUpdTime = clock();
		}
	}
	while (maxIter-- && (clock() - startTime) / CLOCKS_PER_SEC <= totalTime && noImprove < maxNoImprove) {
		int id1 = randomInt(0, populationSize), id2 = randomInt(0, populationSize);
		while (id1 == id2)
			id2 = randomInt(0, populationSize);
		int* offSpring;
		offSpring = CPSX(population[id1], population[id2]);

		//local search
		int* result = ELAHC(perm, offSpring, -1, Lh, timeCutoff, timeSpan);
		double curCost = eval(perm, result);
		if (curCost < bestCost) {
			memcpy(best, result, n * sizeof(int));
			bestCost = curCost;
			prevUpdTime = clock();
			noImprove = 0;
		}
		else {
			noImprove++;
		}
		//weedOut
		double worstCost = 0;
		int worstId;
		for (int i = 0; i < populationSize; i++) {
			if (cost[i] > worstCost) {
				worstCost = cost[i];
				worstId = i;
			}
		}
		if (curCost < cost[worstId]) {
			memcpy(population[worstId], result, n * sizeof(int));
			cost[worstId] = curCost;
		}

		delete result;
		printf("%.4f ", bestCost);
	}
	printf("\n");
	printf("[memetic] time spend find best %.4f\n", 1.0 * (prevUpdTime - startTime) / CLOCKS_PER_SEC);
	erase(population, curPopulationSize);
	delete cost;
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
	printf("solution: ");
	for (int i = 0; i < n; i++)
		printf("%d ", cur[i]);
	printf("\n");
	delete cur;
	delete w;
	erase(v, m);
	return curCost;
}
double test_ELAHC(char* INPUT, int Lh, double timeCutoff) {
	double curCost;
	freopen(INPUT, "r", stdin);
	float f;
	scanf("%d%d%f", &n, &m, &f);
	int** v;
	allocate(v, m, n);
	for (int i = 0; i < m; i++)
		for (int j = 0; j < n; j++)
			scanf("%d", &v[i][j]);
	initialize(v); //IEM 初始化，每个数的索引
	int* w = new int[n];
	for (int i = 0; i < n; i++)
		w[i] = n - i;
	int* cur = ELAHC(v, w, false, Lh, timeCutoff, 1);
	curCost = eval(v, cur);
	printf("solution: ");
	for (int i = 0; i < n; i++)
		printf("%d ", cur[i]);
	printf("\n");
	delete cur;
	delete w;
	erase(v, m);
	return curCost;
}
double test_memetic(char* INPUT, int Lh, double timeCutoff, int populationSize, long long maxIter, double totalTime) {
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
	int* cur = memetic(v, w, false, Lh, timeCutoff, 1, populationSize, maxIter, totalTime);
	curCost = eval(v, cur);
	printf("solution: ");
	for (int i = 0; i < n; i++)
		printf("%d ", cur[i]);
	printf("\n");
	delete cur;
	delete w;
	erase(v, m);
	return curCost;
}
void test_all_data(char* OUTPUT, char* INPUT1, int Lh, int populationSize, int time, int repeat_times = 1) {
	char INPUT[128];
	char OUTPUT1[128];
	sprintf(INPUT, "%s", INPUT1);
	sprintf(OUTPUT1, "%s_%s", OUTPUT, INPUT);
	freopen(OUTPUT1, "w", stdout);
	const int LhList[20] = { 1, 5, 10, 15 };
	int LhLength = 4;
	//const int LhList[10]={1, 10, 100, 1000, 3000, 10000, 30000};
	//int LhLength = 7;
	printf("Lh=%d:\n", Lh);
	double avg = 0, best = 1e9;
	double avgTime = 0, bestTime;
	for (int k = 0; k < repeat_times; k++) {
		printf("repeat %d\n", k);
		double startTime = clock();
		//double res = test_LAHC(FILENAME[i], LhList[Lh], 100);
		//double res = test_ELAHC(FILENAME[i], LhList[Lh], 7200);
		double res = test_memetic(INPUT, Lh, 1e5, populationSize, INF, time);
		double endTime = clock();
		avg += res;
		avgTime += (endTime - startTime) / CLOCKS_PER_SEC;
		if (res < best)
			best = res, bestTime = (endTime - startTime) / CLOCKS_PER_SEC;
	}
	avg /= repeat_times;
	avgTime /= repeat_times;
	printf("avg: %.4f, best: %.4f, avgTime: %.4f, bestTime %.4f\n", avg, best, avgTime, bestTime);
}
int main(int argc, char** argv) {
	srand(time(NULL));
	char* INPUT1 = argv[1];
	int Lh = 1.0 * atoi(argv[2]);
	int populationSize = 1.0 * atoi(argv[3]);
	int time = 1.0 * atoi(argv[4]);
	test_all_data("HER.txt", INPUT1, Lh, populationSize, time);

	return 0;
}
