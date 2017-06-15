#include "deploy.h"
#include <stdio.h>
#include <vector>
#include <string.h>
#include <iostream>
#include <queue>
#include <string>
#include <set>
#include <functional>
#include <time.h>
#include <unordered_map>
#include <algorithm>
#include <math.h>
using namespace std;
#define MAX_EDGE_NUM    (2000 * 20)
#define TIMEOVER endt = time(NULL);if(endt-start > TIME){assess(c_best);best = my;best.sendconn(conn);return best.printresult();}
#define TIMEOVER30 if(time(NULL)-start > 30) return;
const int MAXPOINT = 1001;
const int MAXCON = 501;
const int GENENUM = 1000;
const int INTMAX = 2147483645;
const int LOOP = 10000;
const int MAXEDGE = 40001;
const int TIME = 87;
const int JUDGENUM = 900;
const int tabuLength = 2000;

time_t start, endt;
int output[MAXEDGE][MAXPOINT];
int tempEdge[MAXEDGE][3];
int minBandwidth[MAXEDGE];
int last[MAXEDGE] = { 0 };
int serverCode[MAXPOINT];
int serverNum = 0;
char topo_file[50000] = { 0 };
int outputLength = 0;
int big = 0;
int numOfCandidateBFS = 1;
vector<set<int> > candidate;
vector<set<int> > consume_candidate;
set<int> candidate_set;
bool c_best[MAXPOINT];              //迄今为止最好的一条基因
int cost[GENENUM];                  //每条基因代价
int c_min = INTMAX;                 //迄今为止最小的代价
//当前最少费用值
int mincost = INTMAX;
int bandwidth[MAXPOINT];
bool isConsumer[MAXPOINT];
int _num = 0;
//服务器成本
int sercer_fee = 0;
int netNodeNum = 0; //网络节点数量
int chainNum = 0;   //网络链路数量
int consumeNum = 0;  //消费节点数量
int SumOfNeed = 0;
int conn[MAXPOINT];
Mcmf my;
//当前最好的路线选择
Mcmf best;

//zkwzkw
int tot, ans, n, m, V[MAXEDGE], G[MAXEDGE], COST[MAXEDGE], N[MAXEDGE], F[MAXPOINT], PAIR[MAXEDGE], visit[MAXPOINT], slk[MAXPOINT], dis[MAXPOINT];
int zkwflow = 0;
int tot_save, G_save[MAXEDGE], V_save[MAXEDGE], N_save[MAXEDGE], F_save[MAXPOINT], C_save[MAXEDGE], PAIR_save[MAXEDGE];
int S, T;

struct bw
{
	int ID;
	int bandwidth = 0;
};
bw bandwidthSum[MAXPOINT];

//带宽，费用
struct Node
{
	Node() = default;
	~Node() = default;
	int ID = 0;
	//记录与之相邻的节点
	vector<Node *> next;
	bool isConsume = false;
	bool isServer = false;
};
Node net[MAXPOINT];

struct Flow
{
	Flow() = default;
	~Flow() = default;
	int bandwidth = 0;
	int fee = -1;
};
Flow flow[MAXPOINT][MAXPOINT];

//消费节点
struct ConNode
{
	ConNode() = default;
	~ConNode() = default;
	int ID = 0;
	int connectID = 0;
	int need = 0;
};
ConNode connode[MAXCON];
ConNode connode_desc[MAXCON];

struct IndexSave
{
	int index;
	int cost;
};
IndexSave indexSave[MAXPOINT];

bool comp(const ConNode &a, const ConNode &b)
{
	return a.need > b.need;
}

bool compbw(const bw &a, const bw &b)
{
	return a.bandwidth > b.bandwidth;
}

bool compareCost(const IndexSave &a, const IndexSave &b)
{
	return a.cost > b.cost;
}

//zkwzkw
void save_graph()
{
	memcpy(G_save, G, sizeof(G));
	memcpy(C_save, COST, sizeof(COST));
	memcpy(V_save, V, sizeof(V));
	memcpy(N_save, N, sizeof(N));
	memcpy(F_save, F, sizeof(F));
	memcpy(PAIR_save, PAIR, sizeof(PAIR));
	tot_save = tot;
}

inline void reset_graph()
{
	memcpy(G, G_save, sizeof(G));
	memcpy(COST, C_save, sizeof(COST));
	memcpy(V, V_save, sizeof(V));
	memcpy(N, N_save, sizeof(N));
	memcpy(F, F_save, sizeof(F));
	memcpy(PAIR, PAIR_save, sizeof(PAIR));
	tot = tot_save;
}
void reset()
{
	memcpy(G, G_save, sizeof(G));
	memcpy(F, F_save, sizeof(F));
}
void add(int a, int b, int cap, int cost)
{
	V[++tot] = b;
	G[tot] = cap;
	COST[tot] = cost;
	N[tot] = F[a];
	F[a] = tot;
	V[++tot] = a;
	G[tot] = 0;
	COST[tot] = -cost;
	N[tot] = F[b];
	F[b] = tot;
	PAIR[tot] = tot - 1;
	PAIR[tot - 1] = tot;
}

inline void clear(int b)
{
	PAIR[tot] = 0;
	PAIR[tot - 1] = 0;
	N[tot] = 0;
	COST[tot] = 0;
	//G[tot] = 0;
	V[tot--] = 0;
	N[tot] = 0;
	COST[tot] = 0;
	//[tot] = 0;
	V[tot--] = 0;
}

int aug(int u, int f)
{
	int p, t, left = f;
	int delt = -1;
	if (u == T)
	{
		ans += f * dis[S];
		zkwflow += f;
		return f;
	}
	visit[u] = 1;
	for (p = F[u]; p; p = N[p])
	{
		if (G[p] > 0 && !visit[V[p]])
		{
			t = dis[V[p]] + COST[p] - dis[u];
			if (t == 0)
			{
				delt = aug(V[p], G[p] < left ? G[p] : left);
				if (delt > 0) G[p] -= delt, G[PAIR[p]] += delt, left -= delt;
				if (left == 0) return f;
			}
			else
			{
				if (slk[V[p]] > t) slk[V[p]] = t;
			}
		}
	}
	return f - left;
}
bool modlabel()
{
	int delt = INTMAX, i;
	for (i = 1; i <= T; ++i)
		if (!visit[i])
		{
			if (delt > slk[i]) delt = slk[i];
			slk[i] = INTMAX;
		}
	if (delt == INTMAX)
		return true;
	for (i = 1; i <= T; ++i)
		if (visit[i])
			dis[i] += delt;
	return false;
}

int zkw_flow(bool(&g)[MAXPOINT])
{
	int i;
	int servernum = 0;
	for (i = 0; i < netNodeNum; ++i)
	{
		if (g[i])
		{
			++servernum;
			add(i + 1, T, INTMAX, 0);
		}
	}
	if (servernum == 0)
	{
		return 0;
	}
	if (servernum > consumeNum)
	{
		reset_graph();
		return -2;
	}
	ans = 0;
	zkwflow = 0;
	for (i = 1; i <= T; i++)
		dis[i] = 0, slk[i] = INTMAX;
	do
	{
		do
		{
			memset(visit, 0, sizeof(visit));
		} while (aug(S, INTMAX));
	} while (!modlabel());
	reset_graph();
	// for (i = netNodeNum - 1; i >= 0; --i)
	// {
	//     if (g[i])
	//     {
	//         clear(i + 1);
	//     }
	// }
	// reset();
	ans = ans + (servernum * sercer_fee);
	if (zkwflow != SumOfNeed)
		return -1;
	if (ans < mincost)
	{
		memcpy(c_best, g, sizeof(c_best));
		mincost = ans;
		cout << "flow_cost==" << mincost << endl;
	}
	return ans;
}

//评估函数
int assess(bool(&g)[MAXPOINT])
{
	int servernum = 0;
	int consumeFirst = netNodeNum + 1;
	for (int i = 0; i < netNodeNum; ++i)
	{
		if (g[i])
		{
			++servernum;
			flow[consumeFirst][i].bandwidth = -1;
			flow[consumeFirst][i].fee = 0;
			my.set_edge(0, i + 1, INT_MAX, 0);
		}
	}
	if (servernum == 0)
	{
		for (int i = 0; i < netNodeNum; ++i)
		{
			if (g[i])
			{
				my.clear_edge(0, i + 1);
			}
		}
		return 0;
	}
	if (servernum > consumeNum)
	{
		for (int i = 0; i < netNodeNum; ++i)
		{
			if (g[i])
			{
				my.clear_edge(0, i + 1);
			}
		}
		return -2;
	}
	int flow_cost = 0;
	int max_flow = my.run_edmonds(netNodeNum + 2, 0, consumeFirst, flow_cost);
	int ans = flow_cost + servernum * sercer_fee;
	if (max_flow != SumOfNeed)
	{
		for (int i = 0; i < netNodeNum; ++i)
		{
			if (g[i])
			{
				my.clear_edge(0, i + 1);
			}
		}
		return -1;
	}
	if (ans < mincost)
	{
		best = my;
		mincost = ans;
		memcpy(c_best, g, sizeof(g));
		cout << "flow_cost==" << mincost << endl;
	}
	for (int i = 0; i < netNodeNum; ++i)
	{
		if (g[i])
		{
			my.clear_edge(0, i + 1);
		}
	}
	return ans;
}

bool compareGene(bool g[MAXPOINT], bool c[MAXPOINT])
{
	int i;
	for (i = 0; i < netNodeNum; ++i)
	{
		if (g[i] != c[i])
			break;
	}
	if (i >= netNodeNum)
		return true;
	else
		return false;
}

void tabu_search()
{
	bool tabu[tabuLength][MAXPOINT];
	for (int i = 0; i < tabuLength; i++)
		memset(tabu[i], false, sizeof(tabu[i]));
	int best_i = -1;
	bool cur_change[MAXPOINT] = { false };
	bool candiBest[MAXPOINT] = { false };
	bool current[MAXPOINT] = { false };
	// or other
	memcpy(current, c_best, sizeof(c_best));

	int cMin = INTMAX;
	int line = 0;
	c_min = mincost;
	while (true)
	{
		int mcost = INTMAX;
		int noResult = 0;
		int count = 0;
		for (int i = best_i + 1; i < netNodeNum; ++i)
		{
			++count;		//count记录无法求得更优解的次数
			TIMEOVER30
			memcpy(cur_change, current, sizeof(cur_change));
			//if(!isConsumer[i] && netNodeNum >= 555) continue;
			cur_change[i] = !cur_change[i];
			int cost = zkw_flow(cur_change);
			//cout << cost << endl;
			if (cost == -1)
			{
				++noResult;
			}
			if (cost < c_min && cost != -1 && cost != -2)  //破禁准则
			{
				c_min = cost;
				if (i != netNodeNum - 1)
					best_i = i;
				else
					best_i = -1;
				//if(netNodeNum<JUDGENUM)
				{
					if (line >= tabuLength)
					{
						for (int k = 0; k < tabuLength - 1; k++)
						{
							memcpy(tabu[k], tabu[k + 1], sizeof(tabu[k]));
						}
					}
					bool findGene = false; 				//如果不在禁忌表，则加入禁忌表
					for (int k = 0; k < line; k++)
						if (compareGene(tabu[k], cur_change) == true)
						{
							findGene = true;
							break;
						}
					if (findGene == false)
					{

						memcpy(tabu[line], cur_change, sizeof(cur_change));
						line++;
					}
				}

				memcpy(current, cur_change, sizeof(cur_change));
				break;
			}
			if (cost < mcost && cost != -1 && cost != -2 && cost != c_min)  //禁忌准则
			{
				bool findGene = false;
				for (int k = 0; k < line; ++k)
				{
					if (compareGene(tabu[k], cur_change) == true)
					{
						findGene = true;
						break;
					}
				}
				if (findGene == false) //不在禁忌表中
				{
					mcost = cost;
					memcpy(candiBest, cur_change, sizeof(cur_change));
				}
			}
			if (noResult == netNodeNum)		//-1个数等于netCodeNum
			{
				int startNum = consumeNum * 6 / 9;
				for (; startNum < consumeNum; ++startNum)
				{
					current[connode[startNum].connectID] = true;
				}
			}
			if (count == netNodeNum)               //无法继续下降，接受次优解
			{
				cMin = mcost;
				if (line >= tabuLength)
				{
					for (int k = 0; k < line - 1; k++)
					{
						memcpy(tabu[k], tabu[k + 1], sizeof(tabu[k]));
					}
				}
				bool findGene = false;
				for (int k = 0; k < line; k++)
					if (compareGene(tabu[k], candiBest) == true)
					{
						findGene = true;
						break;
					}

				if (findGene == false)			//add to tabu，禁忌步长为禁忌表长度
				{
					memcpy(tabu[line], candiBest, sizeof(cur_change));
					++line;
				}
				memcpy(current, candiBest, sizeof(current));
				break;
			}
			if (i == netNodeNum - 1)
			{
				i = -1;
			}
		}
	}
}


void toChar(char s[][MAX_EDGE_NUM], char *line) {
	int j = 0, k = 0;
	int index = 0;
	while (line[j] != '\0') 
	{
		if (line[j] == ' ') 
		{
			s[index][k] = '\0';
			k = 0;
			++j;
			++index;
		}
		s[index][k] = line[j];
		++k;
		++j;
	}
	s[index][k] = '\0';
}


string exchangeall()
{
	cout << "start exchangeall" << endl;
	bool current[MAXPOINT];
	memcpy(current, c_best, sizeof(current));
	int i = 0, j = 0;
	while (1)
	{
		for (i = 0; i < netNodeNum; ++i)
		{
			memcpy(current, c_best, sizeof(c_best));
			if (current[i] == true) continue;
			current[i] = true;
			for (j = 0; j < netNodeNum; ++j)
			{
				TIMEOVER
					if (current[j] == true && j != i)
					{
						current[j] = false;
						zkw_flow(current);
						current[j] = true;
					}
			}
			current[i] = false;
		}
		if (compareGene(current, c_best)) break;
	}
	assess(c_best);
	best = my; best.sendconn(conn);
	return best.printresult();
}

string exchangecon()
{
	cout << "start exchangecon" << endl;
	bool current[MAXPOINT];
	memcpy(current, c_best, sizeof(current));
	int i = 0, j = 0;
	while (1)
	{
		for (i = 0; i < netNodeNum; ++i)
		{
			memcpy(current, c_best, sizeof(c_best));
			if (current[i] == true || !isConsumer[i]) continue;
			current[i] = true;
			for (j = 0; j < netNodeNum; ++j)
			{
				TIMEOVER
					if (current[j] == true && j != i)
					{
						current[j] = false;
						zkw_flow(current);
						current[j] = true;
					}
			}
			current[i] = false;
		}
		if (compareGene(current, c_best)) break;
	}
	assess(c_best);
	best = my; best.sendconn(conn);
	return best.printresult();
}

string tanxinforbig()
{
	bool current[MAXPOINT];
	int i = 0;
	memset(current, false, sizeof(current));
	for (i = 0; i < consumeNum; ++i)
	{
		current[connode[i].connectID] = true;
	}
	int maxcost = sercer_fee * consumeNum;
	int cha[990];
	memset(cha, 0, sizeof(cha));
	int isfinish = false;
	int ss = consumeNum;
	int maxx = -1;
	int index = 0;
	int flag = 0;
	while (!isfinish)
	{
		memset(cha, 0, sizeof(cha));
		for (i = 0; i < consumeNum; ++i)
		{
			if (current[connode[i].connectID] == true)
			{
				current[connode[i].connectID] = false;
				cha[connode[i].connectID] = maxcost - zkw_flow(current);
				if (cha[connode[i].connectID] >= maxcost) 
					cha[connode[i].connectID] = 0;
				current[connode[i].connectID] = true;
			}
		}
		maxx = -1;
		index = 0;
		// flag = 4;
		// if(ss < 300) flag = 3;
		// if(ss < 160) flag = 2;
		flag = 2;
		while (flag)
		{
			TIMEOVER;
			maxx = 0;
			for (i = 0; i < netNodeNum; ++i)
			{
				if (cha[i] > maxx)
				{
					maxx = cha[i];
					index = i;
				}
			}
			if (maxx <= 0)
			{
				isfinish = true;
				break;
			}
			current[index] = false;
			if (zkw_flow(current) > 0)
			{
				--flag;
				cha[index] = 0;
				--ss;
			}
			else
			{
				current[index] = true;
				cha[index] = 0;
			}
			if (ss < 100)
			{
				isfinish = true;
				break;
			}
		}
	}
	int j = 0;
	while (1)
	{
		for (i = 0; i < netNodeNum; ++i)
		{
			memcpy(current, c_best, sizeof(c_best));
			if (current[i] == true || !isConsumer[i]) continue;
			current[i] = true;
			for (j = 0; j < netNodeNum; ++j)
			{
				TIMEOVER
					if (current[j] == true && j != i)
					{
						current[j] = false;
						zkw_flow(current);
						current[j] = true;
					}
			}
			current[i] = false;
		}
		if (compareGene(current, c_best)) break;
	}
	assess(c_best);
	best = my; best.sendconn(conn);
	return best.printresult();
}

string tanxinforsmallormedium()
{
	bool current[MAXPOINT];
	int i = 0;
	memset(current, false, sizeof(current));
	for (i = 0; i < consumeNum; ++i)
	{
		current[connode[i].connectID] = true;
	}
	int maxcost = sercer_fee * consumeNum;
	int cha[990];
	memset(cha, 0, sizeof(cha));
	int isfinish = false;
	int ss = consumeNum;
	int maxx = -1;
	int index = 0;
	int flag = 1;
	while (!isfinish)
	{
		memset(cha, 0, sizeof(cha));
		for (i = 0; i < consumeNum; ++i)
		{
			if (current[connode[i].connectID] == true)
			{
				current[connode[i].connectID] = false;
				cha[connode[i].connectID] = maxcost - zkw_flow(current);
				if (cha[connode[i].connectID] >= maxcost) 
					cha[connode[i].connectID] = 0;
				current[connode[i].connectID] = true;
			}
		}
		maxx = -1;
		index = 0;
		flag = 1;
		while (flag)
		{
			TIMEOVER;
			maxx = 0;
			for (i = 0; i < netNodeNum; ++i)
			{
				if (cha[i] > maxx)
				{
					maxx = cha[i];
					index = i;
				}
			}
			if (maxx <= 0)
			{
				isfinish = true;
				break;
			}
			current[index] = false;
			if (zkw_flow(current) > 0)
			{
				--flag;
				cha[index] = 0;
				--ss;
			}
			else
			{
				current[index] = true;
				cha[index] = 0;
			}
		}
	}
	int j = 0;
	for (i = 0; i < netNodeNum; ++i)
	{
		memcpy(current, c_best, sizeof(c_best));
		if (current[i] == true) continue;
		current[i] = true;
		for (j = 0; j < netNodeNum; ++j)
		{
			TIMEOVER
				if (current[j] == true && j != i)
				{
					current[j] = false;
					zkw_flow(current);
					current[j] = true;
				}
		}
		current[i] = false;
	}
	assess(c_best);
	best = my; best.sendconn(conn);
	return best.printresult();
}

void deploy_server(char * topo[MAX_EDGE_NUM], int line_num, char * filename)
{
	start = time(NULL);
	//memset(bandwidth, 0, sizeof(bandwidth));
	memset(isConsumer, false, sizeof(isConsumer));
	char s[4][MAX_EDGE_NUM] = { " " };
	toChar(s, topo[0]);
	sscanf(s[0], "%d", &netNodeNum);  //网络节点数量
	sscanf(s[1], "%d", &chainNum);  //网络链路数量
	sscanf(s[2], "%d", &consumeNum);  //消费节点数量
	Mcmf mymy(netNodeNum + 2);
	char *temp1 = topo[2];
	sscanf(temp1, "%d", &sercer_fee);  //服务器部署成本
	for (int j = 0; j < netNodeNum; ++j) 
	{
		net[j].ID = j;
		net[j].isServer = true;
	}
	int k = 4;
	for (; k < 4 + chainNum; ++k)
	{
		int startCode = 0, endCode = 0, bwidth = 0, netPerCost = 0;
		toChar(s, topo[k]);
		sscanf(s[0], "%d", &startCode);
		sscanf(s[1], "%d", &endCode);
		sscanf(s[2], "%d", &bwidth);
		sscanf(s[3], "%d", &netPerCost);
		net[startCode].next.push_back(&net[endCode]);
		net[endCode].next.push_back(&net[startCode]);
		flow[endCode][startCode].bandwidth = bwidth;
		flow[endCode][startCode].fee = netPerCost;
		flow[startCode][endCode].bandwidth = bwidth;
		flow[startCode][endCode].fee = netPerCost;
		mymy.set_edge(startCode + 1, endCode + 1, bwidth, netPerCost);
		mymy.set_edge(endCode + 1, startCode + 1, bwidth, netPerCost);
		add(startCode + 1, endCode + 1, bwidth, netPerCost);
		add(endCode + 1, startCode + 1, bwidth, netPerCost);
	}
	++k;
	for (int i = 0; k < line_num; ++k, ++i) 
	{
		int consumeID = 0, connectID = 0, bandNeed = 0;
		toChar(s, topo[k]);
		sscanf(s[0], "%d", &consumeID);
		sscanf(s[1], "%d", &connectID);
		sscanf(s[2], "%d", &bandNeed);   
		conn[connectID + 1] = consumeID;
		isConsumer[connectID] = true;
		connode[i].ID = i;
		connode[i].connectID = connectID;
		connode[i].need = bandNeed;
		connode_desc[i].ID = i;
		connode_desc[i].connectID = connectID;
		connode_desc[i].need = bandNeed;
		//总需求
		SumOfNeed += bandNeed;
	}
	//总汇点
	// for (int i = 0; i < consumeNum; ++i)
	// {
	// 	flow[connode[i].connectID][consumeNum].bandwidth = connode[i].need;
	// 	flow[connode[i].connectID][consumeNum].fee = 0;
	// }
	//总汇点1 最小费用最大流模板    netNodeNum + 1为总汇点
	S = netNodeNum + 2;
	T = S + 1;

	for (int i = 0; i < consumeNum; ++i)
	{
		mymy.set_edge(connode[i].connectID + 1, netNodeNum + 1, connode[i].need, 0);
		add(S, connode[i].connectID + 1, connode[i].need, 0);
	}
	save_graph();
	my = mymy;
	if (netNodeNum > 600) big = 3;
	else if (netNodeNum > 200 && netNodeNum <= 600) big = 2;
	else big = 1;
	sort(connode_desc, connode_desc + consumeNum, comp);
	while (connode_desc[_num].need < 10) --_num;
	//candidate all points
	//consume_candidate  consume points
	set<int> temp_set;
	set<int> temp_set1;
	queue<int> qq;
	int node = 0;
	for (int i = 0; i < consumeNum; ++i)
	{
		qq.push(connode[i].connectID);
		for (int j = 0; j < numOfCandidateBFS; ++j)
		{
			int nn = qq.size();
			while (!qq.empty() && nn--)
			{
				node = qq.front();
				temp_set.insert(node);
				temp_set1.insert(node);
				qq.pop();
				for (int k = 0; k < net[node].next.size(); ++k)
				{
					if (temp_set.find(net[node].next[k]->ID) == temp_set.end())
					{
						qq.push(net[node].next[k]->ID);
						temp_set.insert(net[node].next[k]->ID);
						if (isConsumer[net[node].next[k]->ID])
						{
							temp_set1.insert(net[node].next[k]->ID);
						}
					}
				}
			}
		}
		while (!qq.empty())
		{
			qq.pop();
		}
		candidate.push_back(temp_set);
		consume_candidate.push_back(temp_set1);
		temp_set.clear();
		temp_set1.clear();
	}

	bool neeg_g[MAXPOINT];
	bool least_best[MAXPOINT];
	int ccmin;
	memset(neeg_g, false, sizeof(neeg_g));
	for (int i = 0; i <= _num; ++i)
	{
		neeg_g[connode_desc[i].connectID] = true;
	}
	while (zkw_flow(neeg_g) > 0)
	{
		neeg_g[connode_desc[_num--].connectID] = false;
	}
	memset(least_best, false, sizeof(least_best));
	while (1)
	{
		auto max_size = consume_candidate[0].size();
		int index = 0;
		int max_need = 0;
		for (size_t i = 0; i < consume_candidate.size(); ++i)
		{
			if (consume_candidate[i].size() > max_size)
			{
				index = i;
				max_size = consume_candidate[i].size();
				max_need = connode[i].need;
			}
			if (consume_candidate[i].size() == max_size && connode[i].need > max_need)
			{
				max_need = connode[i].need;
				index = i;
			}
		}
		if (max_size < 2)
		{
			break;
		}
		least_best[connode[index].connectID] = true;
		auto &visit = consume_candidate[index];
		for (auto &_mem : visit)
		{
			for (auto &__mem : consume_candidate)
			{
				__mem.erase(connode[index].connectID);
			}
		}
		visit.clear();
	}
	while (assess(least_best) <= 0)
	{
		least_best[my.get_max_not_feed()] = true;
	}

	string res;
	if (big == 1)
	{
		tabu_search();
		res = exchangeall();
	}
	else if (big == 2)
	{
		tabu_search();
		res = exchangeall();
		//res = tanxinforsmallormedium();
	}
	else
	{
		res = tanxinforbig();
	}
	char *topo_file = (char*)res.c_str();
	write_result(topo_file, filename);
	cout << "time:" << time(NULL) - start << endl;
}