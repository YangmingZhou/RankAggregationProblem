//============================================================================
// Name        : ILS.cpp
// Author      : 
// Version     :
// Copyright   : Your copyright notice
// Description : Iterated Local Search for Rank Aggregation Problem
//============================================================================
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

//long nbr_ls;

using namespace std;

int randomInt(int leftBound, int rightBound)
{
	return leftBound + int((rightBound - leftBound) * (0.999999 * rand() / RAND_MAX));
}

const int MAXM = 128, MAXN = 256;
const long long INF = 1LL << 60;
int n, m;

void allocate(int**& arr, int m, int n)
{
	arr = new int* [m];
	for (int i = 0; i < m; i++)
		arr[i] = new int[n];
}
void erase(int**& arr, int m)
{
	for (int i = 0; i < m; i++)
		//if(arr[i] != NULL)
		delete arr[i];
	delete arr;
}

int* borda(int** perm, int* weight)
{
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

int rev_order_pair(int* v, int L, int R)
{
	static int tmp[MAXN];
	if (L >= R)
		return 0;
	int mid = (L + R) / 2;
	int ret = rev_order_pair(v, L, mid) + rev_order_pair(v, mid + 1, R);
	int i = L, j = mid + 1, k = L;
	while (i <= mid && j <= R)
	{
		if (v[i] < v[j])
			tmp[k++] = v[i++];
		else
		{
			tmp[k++] = v[j++];
			ret += mid - i + 1;
		}
	}
	while (i <= mid)
		tmp[k++] = v[i++];

	while (j <= R)
	{
		tmp[k++] = v[j++];
		ret += mid - i + 1;
	}
	for (int i = L; i <= R; i++)
		v[i] = tmp[i];
	return ret;
}

int tau(int* perm1, int* perm2)
{
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

double eval(int** perm, int* cur)
{
	int ret = 0;
	for (int i = 0; i < m; i++)
		ret += tau(perm[i], cur);
	return 1.0 * ret / m;
}

int** Index;
void initialize(int** perm)
{
	if (Index == NULL)
		allocate(Index, MAXM, MAXN);
	for (int i = 0; i < m; i++)
		for (int j = 0; j < n; j++)
			Index[i][perm[i][j]] = j;
}

int comp(int x, int y)
{
	if (x < y) return -1;
	else if (x > y) return 1;
	return 0;
}

double costDelta(int** perm, int* nxt, int x, int y)
{
	if (x == y)return 0;
	int ret = 0;
	for (int i = 0; i < m; i++)
	{
		if (perm[i][x] > perm[i][y])swap(x, y);
		if (comp(nxt[x], nxt[y]) == 1)
			ret++;
		else
			ret--;

		for (int j = perm[i][x] + 1; j <= perm[i][y] - 1; j++)
		{
			if (comp(nxt[Index[i][j]], nxt[y]) != comp(nxt[Index[i][j]], nxt[x]))
			{
				if (comp(nxt[Index[i][j]], nxt[y]) == 1)
					ret++;
				else
					ret--;
			}
			if (comp(nxt[x], nxt[Index[i][j]]) != comp(nxt[y], nxt[Index[i][j]]))
			{
				if (comp(nxt[x], nxt[Index[i][j]]) == 1)
					ret++;
				else
					ret--;
			}
		}
	}
	return 1.0 * ret / m;
}

int* HC(int** perm, int* weight, int beginWith, double timeCutoff)
{
	double startTime = clock();
	int* cur;
	if (beginWith == 0)
	{
		cur = new int[n];
		for (int i = 0; i < n; i++)
			cur[i] = i + 1;
		random_shuffle(cur, cur + n);
	}
	else if (beginWith == -1) //specified begining
		cur = weight;
	else //beginWithBorda
		cur = borda(perm, weight);

	double curCost = eval(perm, cur);
	//printf("initial: %.4f\n", curCost);
	long long iters = 0;
	double delta, min_delta;
	int id1, id2;
	//total time limit
	while ((clock() - startTime) / CLOCKS_PER_SEC <= timeCutoff)
	{
		// find a best swap operation
		min_delta = 1e9;
		for (int i = 0; i < n; i++)
			for (int j = i + 1; j < i; j++)
			{
				swap(cur[i], cur[j]);
				delta = costDelta(perm, cur, i, j);
				if (delta < min_delta)
				{
					min_delta = delta;
					id1 = i;
					id2 = j;
				}
				swap(cur[i], cur[j]);
			}
		// execute an improvement swap operation or exist
		double nxtCost = curCost + min_delta;
		if (nxtCost < curCost)
			swap(cur[id1], cur[id2]);
		else
			break;
		iters++;
	}
	return cur;
}

int* LAHC(int** perm, int* weight, int beginWith, int Lh, double timeCutoff, long maxIdleIter)
{
	double startTime = clock();
	int* cur = new int[n];
	if (!beginWith)
	{
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
	//printf("initial: %.4f\n", curCost);
	bestCost = curCost;
	double* f = new double[Lh];
	for (int i = 0; i < Lh; i++)
		f[i] = curCost;
	long long iters = 0;
	long long idle_iters = 0;
	//total time limit
	while (idle_iters < maxIdleIter && (clock() - startTime) / CLOCKS_PER_SEC <= timeCutoff)
	{
		int id1 = randomInt(0, n), id2 = randomInt(0, n);
		while (id1 == id2)
			id2 = randomInt(0, n);
		swap(nxt[id1], nxt[id2]);
		//double nxtCost = eval(perm, nxt);
		double nxtCost = curCost + costDelta(perm, nxt, id1, id2);
		int v = iters % Lh;
		if (nxtCost < f[v] || nxtCost <= curCost)
		{
			curCost = nxtCost;
			swap(cur[id1], cur[id2]);
			if (curCost < bestCost)
			{
				memcpy(best, cur, n * sizeof(int));
				bestCost = curCost;
				idle_iters = 0;
			}
			else
				idle_iters++;
		}
		else
			swap(nxt[id1], nxt[id2]);
		if (curCost < f[v])
			f[v] = curCost;

		iters++;
	}
	return best;
}

int* Shaking(int* perm1, int perturb)
{
	int* sol = new int[n];
	memcpy(sol, perm1, n * sizeof(int));

	int id1, id2;
	int count = 0;
	while (count < perturb)
	{
		id1 = randomInt(0, n);
		id2 = randomInt(0, n);
		while (id1 == id2)
			id2 = randomInt(0, n);
		swap(sol[id1], sol[id2]);
		count++;
	}
	return sol;
}

int* ILS(int** perm, int* weight, int beginWith, double timeCutoff)
{
	double startTime = clock();
	// generate an initial solution
	int* cur;
	double time_to_best;
	if (beginWith == 0) // random initial solution
	{
		cur = new int[n];
		for (int i = 0; i < n; i++)
			cur[i] = i + 1;
		random_shuffle(cur, cur + n);
	}
	else if (beginWith == -1) //specified solution
		cur = weight;
	else //beginWithBorda // initial solution via Borda count
		cur = borda(perm, weight);

	// initialize
	int* best = new int[n];
	memcpy(best, cur, n * sizeof(int));
	double curCost, bestCost;
	curCost = eval(perm, cur);
	printf("initial cost: %.4f\n", curCost);
	bestCost = curCost;
	time_to_best = clock();
	int perturb_strength = ceil(0.2 * n * (n - 1)) + rand() % 3; // perturb strength used in Shaking procedure
	long long iters, idle_iters = 0;

	// run ILS
	while ((clock() - startTime) / CLOCKS_PER_SEC <= timeCutoff)
	{

		// improve it to a local optimum
		int* result = HC(perm, cur, -1, timeCutoff);
		//int* result = LAHC(perm, cur, -1, 1, timeCutoff, 100);
		//nbr_ls++;
		// update the best one
		double curCost = eval(perm, result);
		if (curCost < bestCost)
		{
			memcpy(best, result, n * sizeof(int));
			bestCost = curCost;
			time_to_best = clock();
			idle_iters = 0;
		}
		else
			idle_iters++;

		// perturb to obtain a new solution
		int* cur1;
		cur1 = Shaking(result, perturb_strength);
		memcpy(cur, cur1, n * sizeof(int));
		delete cur1;
		iters++;

		//delete result;
	}
	printf("\n[memetic] the best cost: %.4f, and the time to best: %.4f, the total time: %.4f\n", bestCost, (time_to_best - startTime) / CLOCKS_PER_SEC, (clock() - startTime) / CLOCKS_PER_SEC);
	//if(cur) delete cur;
	return best;
}

double test_ILS(char* INPUT, double timeCutoff)
{
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
	int* cur = ILS(v, w, 0, timeCutoff);
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

void test_all_data(char* OUTPUT, char* INPUT1, int limit_time)
{
	int repeat_times = 1;
	char INPUT[128];
	char OUTPUT1[128];
	sprintf(INPUT, "%s", INPUT1);
	sprintf(OUTPUT1, "%s_%s", OUTPUT, INPUT);
	freopen(OUTPUT1, "w", stdout);

	double avgCost = 0, GbestCost = 1e9;
	double avgTime = 0, GbestTime;
	//double avgLS = 0;
	for (int k = 0; k < repeat_times; k++)
	{
		//nbr_ls = 0;
		printf("repeat %d\n", k);
		double startTime = clock();
		double res = test_ILS(INPUT, limit_time);
		double endTime = clock();
		avgCost += res;
		avgTime += (endTime - startTime) / CLOCKS_PER_SEC;
		//avgLS += nbr_ls;
		if (res < GbestCost)
		{
			GbestCost = res;
			//GbestTime = time_to_best;
		}
	}
	avgCost /= repeat_times;
	avgTime /= repeat_times;
	//avgLS /= repeat_times;
	printf("avgCost: %.4f, bestCost: %.4f, avgTime: %.4f\n", avgCost, GbestCost, avgTime);//, GbestTime, bestTime: %.4f, avgLS, avgLS: %.4f
}

int main(int argc, char** argv)
{
	srand(time(NULL));
	char* a[] = { "dataset_050_0.001_100_02.txt","dataset_050_0.001_100_11.txt","dataset_100_0.2_100_01.txt","dataset_100_0.2_100_05.txt","dataset_150_0.1_100_08.txt","dataset_150_0.1_100_17.txt","dataset_200_0.01_100_04.txt","dataset_200_0.01_100_13.txt","dataset_250_0.001_100_01.txt","dataset_250_0.001_100_10.txt" };
	int Limittime = 1.0 * atoi(argv[1]);
	for (int i = 1; i < 10; i++)
	{
		test_all_data("HER_Results.txt", a[i], Limittime);
		cout << "finish " << i << "-th instance:" << a[i] << endl;
	}

	return 0;
}
