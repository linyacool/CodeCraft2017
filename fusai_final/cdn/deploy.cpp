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
#define MAX_EDGE_NUM (2000 * 20)
#define TIMEOVER if(time(NULL)-start > 85){exchangeServer();assess(c_best);best = my;best.sendconn(conn,c_best);return best.printresult();}
#define TIMEOVER30 if(time(NULL)-start > 30) return exchangeall();
const int MAXPOINT = 1300;
const int MAXCON = 501;
const int GENENUM = 1000;
const int INTMAX = INT_MAX;
const int LOOP = 10000;
const int MAXEDGE = 40001;
const int TIME = 80;
const int tabuLength = 2000;
const int BIGSCALE = 700;
time_t start, endt;
int serverNum = 0;
char topo_file[50000] = {0};
int numOfCandidateBFS = 1;
vector<set<int> > candidate;
vector<set<int> > consume_candidate;
set<int> candidate_set;
int server_level_table[501];
int nodeFee[MAXPOINT];
bool isConsumer[MAXPOINT];
int _num = 0;
//服务器成本
int sercer_fee = 0;
int netNodeNum = 0; //网络节点数量
int chainNum = 0;   //网络链路数量
int consumeNum = 0;  //消费节点数量
int SumOfNeed = 0;
int conn[MAXPOINT];
int need_g[MAXPOINT];
int least_best[MAXPOINT];
Mcmf my;
//当前最好的路线选择
Mcmf best;
int ServerTypeNum = 0;
int tabu[tabuLength][MAXPOINT]; //tabu list
int c_best[MAXPOINT];              //迄今为止最好的一条基因
int cost[GENENUM];                  //每条基因代价
int c_min = INTMAX;                 //迄今为止最小的代价
int c_max = 0;                      //某次进化中最大代价（将会被迄今为止最优的基因覆盖）
//当前最少费用值
int mincost = INTMAX;
//zkw algorithm
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

struct Server
{
    int maxout;
    int fee;
};
Server server[11];

bool comp(const ConNode &a, const ConNode &b)
{
    return a.need > b.need;
}

bool compbw(const bw &a, const bw &b)
{
    return a.bandwidth > b.bandwidth;
}

//zkw algorithm
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
                delt = aug(V[p], G[p]< left ? G[p] : left);
                if (delt > 0) G[p] -= delt, G[PAIR[p]] += delt, left -= delt;
                if (left == 0) return f;
            }
            else
            {
                if(slk[V[p]] > t) slk[V[p]] = t;
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
            if(delt > slk[i]) delt = slk[i]; 
            slk[i] = INTMAX; 
        }
    if (delt == INTMAX) 
        return true;
    for (i = 1; i <= T; ++i)
        if (visit[i]) 
            dis[i] += delt;
    return false;
}

//0 means servernum is 0;
//-1 means flow is not feed;
//-2 means servernum > consumeNum, it is a bad choice;
int zkw_flow(int(&g)[MAXPOINT])
{
    int i;
    int servernum = 0;
    for (i = 0; i < netNodeNum; ++i)
    {
        if (g[i] != -1)
        {
            ++servernum;
            add(i + 1, T, server[g[i]].maxout, 0);
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
    for (i = 1; i <= T; ++i)
        dis[i] = 0, slk[i] = INTMAX;
    do 
    {
        do 
        { 
            memset(visit, 0, sizeof(visit)); 
        } while (aug(S, INTMAX));
    } while (!modlabel());
    reset_graph();
    for(i = 0; i < netNodeNum; ++i)
    {
        if(g[i] > -1)
        {
           ans = ans + server[g[i]].fee + nodeFee[i];
        }
    }
    if (zkwflow != SumOfNeed)
    {
        return -1;
    }
    if (ans < mincost)
    {
        memcpy(c_best, g, sizeof(c_best));
        mincost = ans;
        cout << "flow_cost==" << mincost << endl;
    }
    return ans;
}

//评估函数
int assess(int(&g)[MAXPOINT])
{
    int servernum = 0;
    int consumeFirst = netNodeNum + 1;
    for (int i = 0; i < netNodeNum; ++i)
    {
        if (g[i] > -1)
        {
            ++servernum;
            my.set_edge(0, i + 1, server[g[i]].maxout, 0);
        }
    }
    if (servernum == 0) 
    {
        for(int i = 0; i < netNodeNum; ++i)
        {
            if (g[i] > -1)
            {
                my.clear_edge(0, i + 1);
            }
        }
        return 0;
    }
    if (servernum > consumeNum)
    {
        for(int i = 0; i < netNodeNum; ++i)
        {
            if (g[i] > -1)
            {
                my.clear_edge(0, i + 1);
            }
        }
        return -2;
    }
    int flow_cost = 0;
    int max_flow = my.run_edmonds(netNodeNum + 2, 0, consumeFirst, flow_cost); 
    int ans = flow_cost;
    for(int i = 0; i < netNodeNum; ++i)
    {
        if(g[i] > -1)
        {
           ans = ans + server[g[i]].fee + nodeFee[i]; 
        }
    }
    if (max_flow != SumOfNeed)
    {
        for(int i = 0; i < netNodeNum; ++i)
        {
            if (g[i] > -1)
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
    for(int i = 0; i < netNodeNum; ++i)
    {
        if (g[i] > -1)
        {
            my.clear_edge(0, i + 1);
        }
    }
    return ans;
}

//only change server type
string exchangeServer()
{
    int i = 0;
    int gee = ServerTypeNum;
    int current[MAXPOINT];
    memcpy(current, c_best, sizeof(current));
    for(i = 0; i < netNodeNum; ++i)
    {
        if(current[i] > -1)
        {
            memcpy(current, c_best, sizeof(current));
            gee = current[i] - 1;
            while(gee >= -1)
            {
                if(time(NULL) - start > 88)
                {
                    assess(c_best);
                    best = my;
                    best.sendconn(conn, c_best);
                    return best.printresult();
                }
                current[i] = gee;
                if(zkw_flow(current) <= 0)
                {
                    break;
                }
                --gee;
            }
        }
    }
    assess(c_best);
    best = my;
    best.sendconn(conn, c_best);
    return best.printresult();
}


string preExchangeServer()
{
    int i = 0;
    int current[MAXPOINT];
    memcpy(current, c_best, sizeof(current));
    assess(c_best);
    vector<int> fnet(my.getfnet());
    for(i = 0; i < netNodeNum; ++i)
    {
        if(current[i] > -1)
        {
            current[i] = server_level_table[fnet[i+1]];
        }
    }
    zkw_flow(current);
    return exchangeServer();
}

string exchangeServerforsmall()
{
    int i = 0;
    int gee = ServerTypeNum;
    int current[MAXPOINT];
    memcpy(current, c_best, sizeof(current));
    for(i = 0; i < netNodeNum; ++i)
    {
        if(current[i] > -1)
        {
            memcpy(current, c_best, sizeof(current));
            gee = current[i] - 1;
            while(gee >= -1)
            {
                if(time(NULL) - start > 86)
                {
                    assess(c_best);
                    best = my;
                    best.sendconn(conn, c_best);
                    return best.printresult();
                }
                current[i] = gee;
                if(zkw_flow(current) <= 0)
                {
                    memcpy(current, c_best, sizeof(current));
                    break;
                }
                --gee;
            }
        }
    }
    assess(c_best);
    best = my;
    best.sendconn(conn, c_best);
    return best.printresult();
}
bool compareGene(int g[MAXPOINT], int c[MAXPOINT])
{
    int i;
    for(i = 0; i < netNodeNum; ++i)
    {
        if(g[i] != c[i])
            break;
    }
    if(i >= netNodeNum)
        return true;
    else
        return false;
}


void toChar(char read_str[][MAX_EDGE_NUM], char *line) 
{
    int j = 0, line_current = 0;
    int index = 0;
    while (line[j] != '\0') 
    {
        if (line[j] == ' ') 
        {
            read_str[index][line_current] = '\0';
            line_current = 0;
            ++j;
            ++index;
        }
        read_str[index][line_current] = line[j];
        ++line_current;
        ++j;
    }
    read_str[index][line_current] = '\0';
}


string exchangeall()
{
    int current[MAXPOINT];
    memcpy(current, c_best, sizeof(current));
    int i = 0,j = 0;
    while(1)
    {
        for(i = 0; i < netNodeNum; ++i)
        {
            memcpy(current, c_best, sizeof(c_best));  
            if(current[i] != -1) continue; 
            current[i] = ServerTypeNum - 1;
            for(j = 0; j < netNodeNum; ++j)
            {
                TIMEOVER
                if(current[j] != -1 && j != i)
                {
                    current[j] = -1;
                    zkw_flow(current);
                    current[j] = ServerTypeNum - 1;
                }
            }
            current[i] = -1;
        }
        if(compareGene(current, c_best)) break;
    }
    exchangeServer();
    assess(c_best);
    best = my;
    best.sendconn(conn, c_best);
    return best.printresult();
}

string exchangeforbig()
{
    int current[MAXPOINT];
    memcpy(current, c_best, sizeof(current));
    int i = 0;
    while(1)
    {
        for(i = 0; i < netNodeNum; ++i)
        {
            if(current[i] == -1) continue;
            memcpy(current, c_best, sizeof(c_best));
            current[i] = -1;
            for(auto _mem: candidate[i])
            {
                if(time(NULL)-start > 80)
                {
                    return preExchangeServer();
                }
                if(current[_mem] == -1)
                {
                    current[_mem] = ServerTypeNum - 1;
                    zkw_flow(current);
                    current[_mem] = -1;
                }
                else
                {
                    current[_mem] = -1;
                    zkw_flow(current);
                    current[_mem] = ServerTypeNum - 1;
                }
            }
            zkw_flow(current);   
        }
    }
    return preExchangeServer();
}

string exchangeforsmall()
{
    int current[MAXPOINT];
    int i = 0;
    while(1)
    {
        for(i = 0; i < netNodeNum; ++i)
        {
            if(current[i] == -1) continue;
            memcpy(current, c_best, sizeof(c_best));
            current[i] = -1;
            for(auto _mem: candidate[i])
            {
                if(time(NULL)-start > 87)
                {
                    return preExchangeServer();
                }
                if(current[_mem] == -1)
                {
                    current[_mem] = ServerTypeNum - 1;
                    zkw_flow(current);
                    current[_mem] = -1;
                }
                else
                {
                    current[_mem] = -1;
                    zkw_flow(current);
                    current[_mem] = ServerTypeNum - 1;
                }
            }
            zkw_flow(current);    
        }
    }
    return preExchangeServer();
}
string exchangeCon()
{
    int i = 0,j = 0;
    int current[MAXPOINT];
    while(1)
    {
        for(i = 0; i < netNodeNum; ++i)
        {
            memcpy(current, c_best, sizeof(c_best));  
            if(current[i] != -1 || !isConsumer[i]) continue; 
            current[i] = ServerTypeNum - 1;
            for(j = 0; j < netNodeNum; ++j)
            {
                TIMEOVER
                if(current[j] != -1 && j != i)
                {
                    current[j] = -1;
                    zkw_flow(current);
                    current[j] = ServerTypeNum - 1;
                }
            }
            current[i] = -1;
        }
        if(compareGene(current, c_best)) break;
    }
    exchangeServer();
    assess(c_best);
    best = my;
    best.sendconn(conn, c_best);
    return best.printresult();
}
string greedy()
{
    int current[MAXPOINT];
    int i = 0;
    memset(current, -1, sizeof(current));
    for (i = 0; i < consumeNum; ++i)
    {
        current[connode[i].connectID] = ServerTypeNum - 1;
    }
    int maxcost = zkw_flow(current);
    int cha[1400];
    memset(cha, 0, sizeof(cha));
    int isfinish = false;
    int ss = consumeNum;
    int maxx = -1;
    int index = 0;
    int flag = 0;
    while(!isfinish)
    {
        memset(cha, 0, sizeof(cha));
        for(i = 0; i < consumeNum; ++i)
        {
            if(current[connode[i].connectID] != -1)
            {
                current[connode[i].connectID] = -1;
                cha[connode[i].connectID] = maxcost - zkw_flow(current);
                if(cha[connode[i].connectID] >= maxcost) cha[connode[i].connectID] = 0;
                current[connode[i].connectID] = ServerTypeNum - 1;
            }
        }
        maxx = -1;
        index = 0;
        flag = 1;
        if(ss > 400) flag = 10;
        if(ss > 300) flag = 8;
        if(ss > 200) flag = 4;
        if(ss > 100) flag = 3;
        while(flag)
        {
            if(time(NULL) - start > 80)
            {
                return exchangeServer();
            }
            maxx = 0;
            for(i = 0; i < netNodeNum; ++i)
            {
                if(cha[i] > maxx)
                {
                    maxx = cha[i];
                    index = i;
                }
            }
            if(maxx <= 0)
            {
                isfinish = true;
                break;
            }
            current[index] = -1;
            if(zkw_flow(current) > 0)
            {
                --flag;
                cha[index] = 0;
                --ss;
            }
            else
            {
                current[index] = ServerTypeNum - 1;
                cha[index] = 0;
            }
            if(ss < 80)
            {
                isfinish = true;
                break;
            }
        }
    }
    return exchangeServer();
}

string serach()
{
    int current[MAXPOINT];
    int i = 0;
    memcpy(current, need_g, sizeof(need_g));
    int maxcost = zkw_flow(current);
    int cha[1300];
    memset(cha, 0, sizeof(cha));
    int isfinish = false;
    int ss = consumeNum;
    int maxx = -1;
    int index = 0;
    int flag = 0;
    while(!isfinish)
    {
        memset(cha, 0, sizeof(cha));
        for(i = 0; i < consumeNum; ++i)
        {
            if(current[connode[i].connectID] != -1)
            {
                current[connode[i].connectID] = -1;
                cha[connode[i].connectID] = maxcost - zkw_flow(current);
                if(cha[connode[i].connectID] >= maxcost) cha[connode[i].connectID] = 0;
                current[connode[i].connectID] = ServerTypeNum - 1;
            }
        }
        maxx = -1;
        index = 0;
        flag = 1;
        while(flag)
        {
            maxx = 0;
            for(i = 0; i < netNodeNum; ++i)
            {
                if(cha[i] > maxx)
                {
                    maxx = cha[i];
                    index = i;
                }
            }
            if(maxx <= 0)
            {
                isfinish = true;
                break;
            }
            current[index] = -1;
            if(zkw_flow(current) > 0)
            {
                --flag;
                cha[index] = 0;
                --ss;
            }
            else
            {
                current[index] = ServerTypeNum - 1;
                cha[index] = 0;
            }
        }
    }
    return exchangeforbig();
}

string tabu_serach()
{
    for(int i = 0; i < tabuLength; ++i)
        memset(tabu[i], -1, sizeof(tabu[i]));
    int best_i = -1;
    int cur_changed[MAXPOINT];
    memset(cur_changed, -1, sizeof(cur_changed));
    int candiBest[MAXPOINT];
    memset(candiBest, -1, sizeof(candiBest));
    int current[MAXPOINT];
    memcpy(current, least_best, sizeof(least_best));
    int cMin = INTMAX;
    int line = 0;
    c_min = mincost;
    while(true)
    {
        int mcost=INTMAX;
        int noResult=0;
        int count = 0;
        for(int i = best_i + 1; i < netNodeNum; ++i)
        {
            count++;        //count记录无法求得更优解的次数
            //if(netNodeNum > 600) {TIMEOVER31}
            TIMEOVER30
            memcpy(cur_changed,current,sizeof(cur_changed));
            //if(!isConsumer[i]) continue;
            if(cur_changed[i] > -1) 
            	cur_changed[i] = -1;
            else
            	cur_changed[i] = ServerTypeNum - 1;
            
            int cost = zkw_flow(cur_changed);
            
            if(cost == -1)
            {
                ++noResult;
            }
            if(cost < c_min && cost != -1 && cost != -2 )  //破禁准则
            {   
                c_min = cost;
                if(i != netNodeNum - 1)
                    best_i = i;
                else
                    best_i = -1;
                if(line >= tabuLength)
                {
                    for(int line_current=0; line_current<tabuLength - 1; ++line_current)
                    {
                        memcpy(tabu[line_current], tabu[line_current+1], sizeof(tabu[line_current]));
                    }
                }
                bool findGene = false;                //如果不在禁忌表，则加入禁忌表
                for(int line_current = 0; line_current < line; ++line_current)
                    if(compareGene(tabu[line_current], cur_changed) == true)
                    {
                        findGene = true;  
                        break;
                    }   
                if(findGene == false)
                {     
                    memcpy(tabu[line], cur_changed, sizeof(cur_changed));
                    ++line;
                }               
                memcpy(current, cur_changed, sizeof(cur_changed));
                break;
            }

            if(cost < mcost && cost != -1 && cost != -2 && cost != c_min)  //禁忌准则
            {
                bool findGene = false;
                for(int line_current = 0; line_current < line; ++line_current)
                {
                    if(compareGene(tabu[line_current], cur_changed) == true)
                    {
                        findGene=true;  
                        break;
                    }
                }
                
                if(findGene == false) //不在禁忌表中
                {
                    mcost = cost;
                    memcpy(candiBest, cur_changed, sizeof(cur_changed));
                }   
                
            }

            if(noResult == netNodeNum)        //-1个数等于netCodeNum
            {
                int startNum=consumeNum * 0.66;
                for(; startNum < consumeNum; ++startNum)
                {
                    current[connode[startNum].connectID] = ServerTypeNum - 1;
                }
            }
            
            if(count == netNodeNum)               //无法继续下降，接受次优解
            {
                cMin = mcost;
                if(line >= tabuLength)
                {
                    for(int line_current=0; line_current < line - 1; ++line_current)
                    {
                        memcpy(tabu[line_current], tabu[line_current+1], sizeof(tabu[line_current]));
                    }
                }
                bool findGene = false;
                for(int line_current = 0; line_current < line; ++line_current)
                    if(compareGene(tabu[line_current], candiBest) == true)
                    {
                        findGene = true;  
                        break;
                    }
                if(findGene == false)         //add to tabu，禁忌步长为禁忌表长度
                {   
                    memcpy(tabu[line], candiBest, sizeof(cur_changed));
                    ++line;
                }   
                memcpy(current, candiBest, sizeof(current));
                break;
            }
            if(i == netNodeNum-1)
            {
                i = -1;
            }
        }
    }
    return exchangeall();
}
void deploy_server(char * topo[MAX_EDGE_NUM], int line_num, char * filename)
{
    start = time(NULL);
    //memset(bandwidth, 0, sizeof(bandwidth));
    memset(isConsumer, false, sizeof(isConsumer));
    char read_str[4][MAX_EDGE_NUM] = { " " };
    toChar(read_str, topo[0]);
    sscanf(read_str[0], "%d", &netNodeNum);//网络节点数量
    sscanf(read_str[1], "%d", &chainNum); //网络链路数量
    sscanf(read_str[2], "%d", &consumeNum); //消费节点数量
    Mcmf temp_mcmf(netNodeNum + 2);
   	int line_current = 2;
   	while (strlen(topo[line_current]) != strlen(topo[1]))
   	{
        int index = 0, out = 0, cost = 0;
   		toChar(read_str, topo[line_current]);
   		sscanf(read_str[0], "%d", &index);
   		sscanf(read_str[1], "%d", &out);
   		sscanf(read_str[2], "%d", &cost);
   		server[index].maxout = out;
   		server[index].fee = cost;
   		++ServerTypeNum;
   		++line_current;
   	}
    int now_type = 0;
    for (int i = 0; i < MAXCON; ++i)
    {
        if(i <= server[now_type].maxout)
        {
            server_level_table[i] = now_type;
        }
        else
        {
            server_level_table[i] = min(++now_type, ServerTypeNum - 1);
        }
    }
    ServerTypeNum = 6;
   	++line_current;
   	while (strlen(topo[line_current]) != strlen(topo[1]))
   	{
        int index = 0, cost = 0;
   		toChar(read_str, topo[line_current]);
   		sscanf(read_str[0], "%d", &index);
   		sscanf(read_str[1], "%d", &cost);
   		nodeFee[index] = cost;
   		++line_current;
   	}
   	++line_current;
    while (strlen(topo[line_current]) != strlen(topo[1])) 
    {
        int startCode = 0, endCode = 0, bwidth = 0, netPerCost = 0;
        toChar(read_str, topo[line_current]);
        sscanf(read_str[0], "%d", &startCode);
        sscanf(read_str[1], "%d", &endCode);
        sscanf(read_str[2], "%d", &bwidth);
        sscanf(read_str[3], "%d", &netPerCost);
        net[startCode].next.push_back(&net[endCode]);
        net[endCode].next.push_back(&net[startCode]);
        net[startCode].ID = startCode;
        net[endCode].ID = endCode;
        flow[endCode][startCode].bandwidth = bwidth;
        flow[endCode][startCode].fee = netPerCost;
        flow[startCode][endCode].bandwidth = bwidth;
        flow[startCode][endCode].fee = netPerCost;
        bandwidthSum[startCode].ID = startCode;
        bandwidthSum[endCode].ID = endCode;
        bandwidthSum[startCode].bandwidth += bwidth;
        bandwidthSum[endCode].bandwidth += bwidth;
        temp_mcmf.set_edge(startCode + 1, endCode + 1, bwidth, netPerCost);
        temp_mcmf.set_edge(endCode + 1, startCode + 1, bwidth, netPerCost);
        add(startCode + 1, endCode + 1, bwidth, netPerCost);
        add(endCode + 1, startCode + 1, bwidth, netPerCost);
        ++line_current;
    }
    line_current++;
    int i=0;
    int index=line_current;
   	while(line_current<index+consumeNum){
        toChar(read_str, topo[line_current]);
        int consumeID = 0;
        sscanf(read_str[0],"%d",&consumeID);//charToInt(read_str[0]);
        int connectID = 0;//
        sscanf(read_str[1],"%d",&connectID);//charToInt(read_str[1]);
        int bandNeed = 0;
        sscanf(read_str[2],"%d",&bandNeed);//charToInt(read_str[2]);      
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
        line_current++;
        i++;
    }
    //candidate_set
    int largeFlowPoint[MAXPOINT];
    memset(largeFlowPoint, -1, sizeof(largeFlowPoint));
    for(int i = 0; i < netNodeNum; ++i)
    {
        if(bandwidthSum[i].bandwidth > 1000 && nodeFee[i] < 2000)
        {
            //candidate_set.insert(i);
            if(bandwidthSum[i].bandwidth > 1000)
            {
                largeFlowPoint[i] = ServerTypeNum - 1;
            }
        }
        if(netNodeNum < BIGSCALE && bandwidthSum[i].bandwidth > 600 && nodeFee[i] < 2000)
        {
            largeFlowPoint[i] = ServerTypeNum - 1;
        }
    }
    S = netNodeNum + 2;
    T = S + 1;
    for (int i = 0; i < consumeNum; ++i)
    {
        temp_mcmf.set_edge(connode[i].connectID + 1, netNodeNum + 1, connode[i].need, 0);
        add(S, connode[i].connectID + 1, connode[i].need, 0);
    }
    save_graph();
    my = temp_mcmf;
    sort(connode_desc, connode_desc + consumeNum, comp);
    int _num = consumeNum / 10;

    //candidate all points
    //consume_candidate  consume points
    set<int> temp_set;
    set<int> temp_set1;
    queue<int> qq;
    int node = 0;
    for (int i = 0; i < consumeNum; ++i)
    {
        qq.push(connode[i].connectID);
        for(int j = 0; j < numOfCandidateBFS; ++j)
        {
            int nn = qq.size();
            while(!qq.empty() && nn--)
            {
                node = qq.front();
                temp_set.insert(node);
                temp_set1.insert(node);
                qq.pop();
                for(int line_current = 0; line_current < net[node].next.size(); ++line_current)
                {
                    if(temp_set.find(net[node].next[line_current]->ID) == temp_set.end())
                    {
                        qq.push(net[node].next[line_current]->ID);
                        temp_set.insert(net[node].next[line_current]->ID);
                        if(isConsumer[net[node].next[line_current]->ID])
                        {
                            temp_set1.insert(net[node].next[line_current]->ID);
                        }
                    }
                }                  
            }
        }
        while(!qq.empty())
        {
            qq.pop();
        }
        //candidate.push_back(temp_set);
        consume_candidate.push_back(temp_set1);
        temp_set.clear();
        temp_set1.clear();
    }

    int j_num = 1;
    for (int i = 0; i < netNodeNum; ++i)
    {
        qq.push(i);
        if(netNodeNum > BIGSCALE)
            j_num = 1;
        else
            j_num = 2;
        for(int j = 0; j < j_num; ++j)
        {
            int nn = qq.size();
            while(!qq.empty() && nn--)
            {
                node = qq.front();
                temp_set.insert(node);
                temp_set1.insert(node);
                qq.pop();
                for(int line_current = 0; line_current < net[node].next.size(); ++line_current)
                {
                    if(temp_set.find(net[node].next[line_current]->ID) == temp_set.end())
                    {
                        qq.push(net[node].next[line_current]->ID);
                        temp_set.insert(net[node].next[line_current]->ID);
                    }
                }          
            }
        }
        while(!qq.empty())
        {
            qq.pop();
        }
        if(netNodeNum > BIGSCALE)
            j_num = 100;
        else
            j_num = INTMAX;
        if(temp_set.size() > j_num) 
        {
            temp_set.clear();
            temp_set.insert(i);
        }
        candidate.push_back(temp_set);
        temp_set.clear();
        //temp_set1.clear();
    }

    memcpy(need_g, largeFlowPoint, sizeof(need_g));
    for(int i = 0; i <= _num; ++i)
    {
        need_g[connode_desc[i].connectID] = ServerTypeNum - 1;
    }

    memcpy(least_best, need_g, sizeof(need_g));
    while(1)
    {
        auto max_size = consume_candidate[0].size();
        int index = 0;
        int max_need = 0;
        for(size_t i = 0; i < consume_candidate.size(); ++i)
        {
            if(consume_candidate[i].size() > max_size)
            {
                index = i;
                max_size = consume_candidate[i].size();
                max_need = connode[i].need;
            }
            if(consume_candidate[i].size() == max_size && connode[i].need > max_need)
            {
                max_need = connode[i].need;
                index = i;
            }
        }
        if(max_size < 4)
        {
            break;
        }
        least_best[connode[index].connectID] = ServerTypeNum - 1;
        auto &visit = consume_candidate[index];
        for(auto &_mem : visit)
        {
            for(auto &__mem : consume_candidate)
            {
                __mem.erase(connode[index].connectID);
            }
        }
        visit.clear();
    }
    while((c_min = assess(least_best)) <= 0)
    {
        cout << "get one point which is not feed" << endl;
        least_best[my.get_max_not_feed()] = ServerTypeNum - 1;
    }

    string res = (netNodeNum > BIGSCALE ? exchangeforbig() : exchangeforsmall());
    char *topo_file = (char*)res.c_str();
    write_result(topo_file, filename);
    cout << "time: " << time(NULL)-start << endl;
}