#ifndef __ROUTE_H__
#define __ROUTE_H__
#include "lib_io.h"
#include <stdlib.h>
#include <iostream>
#include <stdio.h>
#include <climits>
#include <queue>
#include <string>
using namespace std;
#define CLEAR1D(p,v,n) { for(int i=0; i<n; i++) p[i]=v; }
#define CLEAR2D(p,v,n) { int i;int j;for(i=0; i<n; i++) for(j=0; j<n; j++) p[i][j]=v; }
#define HALF_MAX 1073741823
void deploy_server(char * graph[MAX_EDGE_NUM], int edge_num, char * filename);
class Mcmf
{
private:
#define BUBLLE {t = que[i]; que[i] = que[j]; que[j] = t;t = inque[que[i]]; inque[que[i]] = inque[que[j]]; inque[que[j]] = t;}
#define POTENTIAL(u,v) ( dis[u] + pi[u] - pi[v])

private:
    int num_v_cur;
	int qs;
	int NUM_V = 1005;
    int **cap, **cost, **flow_cur, **adj;
    int *num_adj, *pi, *pre, *dis, *que, *inque;
    int *conn;
public:
    //此函数极度危险，请勿模仿
    void sendconn(int *c)
    {
        conn = c;
    }
    Mcmf():NUM_V(1005) 
    {
        allo_arrays();
    }
    Mcmf(int num_v):NUM_V(1005), num_v_cur(num_v) 
    {
        allo_arrays();
    }
    Mcmf& operator =(const Mcmf& a)
    {
        num_v_cur = a.num_v_cur;
        qs = a.qs;
        NUM_V = a.NUM_V;
        int i, j;
        for (i = 0; i < NUM_V; ++i)
        {
            //num_adj[i] = a.num_adj[i];
            //pi[i] = a.pi[i];
            //pre[i] = a.pre[i];
            //dis[i] = a.dis[i];
            que[i] = a.que[i];
            //inque[i] = a.inque[i];
        }
        for (i = 0; i < NUM_V; ++i)
        {
            for (j = 0; j < NUM_V; ++j)
            {
                cap[i][j] = a.cap[i][j];
                cost[i][j] = a.cost[i][j];
                flow_cur[i][j] = a.flow_cur[i][j];
                //adj[i][j] = a.adj[i][j];
            }
        }
        return *this;
    }
    ~Mcmf() 
    {
        free_arrays();
    }
    void clear_all()
    {
        if ( NUM_V > 0) 
        {
            CLEAR2D(cap, 0, NUM_V);
            CLEAR2D(cost, 0, NUM_V);
            CLEAR2D(flow_cur, 0, NUM_V);
            CLEAR2D(adj, 0, NUM_V);
            CLEAR1D(num_adj, 0, NUM_V);
            CLEAR1D(pi, 0, NUM_V);
            CLEAR1D(pre, 0, NUM_V);
            CLEAR1D(dis, 0, NUM_V);
            CLEAR1D(que, 0, NUM_V);
            CLEAR1D(inque, 0, NUM_V);
        }
    }
    void allo_arrays()
    {
        cap = (int**) malloc(NUM_V * sizeof(int *));
        cost = (int**) malloc(NUM_V * sizeof(int *));
        flow_cur = (int**) malloc(NUM_V * sizeof(int *));
        adj = (int**) malloc(NUM_V * sizeof(int *));
        for ( int i = 0; i < NUM_V; ++i)
        {
            cap[i] = (int *) malloc(NUM_V * sizeof(int));
            cost[i] = (int *) malloc(NUM_V * sizeof(int));
            flow_cur[i] = (int *) malloc(NUM_V * sizeof(int));
            adj[i] = (int *) malloc(NUM_V * sizeof(int));
        }
        num_adj = (int*) malloc(NUM_V * sizeof(int));
        pi = (int*) malloc(NUM_V * sizeof(int));
        pre = (int*) malloc(NUM_V * sizeof(int));
        dis = (int*) malloc(NUM_V * sizeof(int));
        que = (int*) malloc(NUM_V * sizeof(int));
        inque = (int*) malloc(NUM_V * sizeof(int));
        clear_all();
    }
    void free_arrays()
    {
        if(cap != nullptr)
            for (int i = 0; i < NUM_V; ++i)
            {
                free(cap[i]); 
                free(cost[i]); 
                free(flow_cur[i]); 
                free(adj[i]);
            }
        free(cap); free(cost); free(flow_cur); free(adj);
        free(num_adj); free(pi); free(pre); free(dis); free(que); free(inque);
    }
    void set_num_vertices(int num_v) 
    {
        num_v_cur = num_v; 
    }
    void set_edge(int i, int j, int edge_capacity, int edge_cost)
    {
        cap[i][j] = edge_capacity; 
        cost[i][j] = edge_cost; 
     }
    void clear_edge(int i, int j)
    {
        cap[i][j] = 0;
        cost[i][j] = 0;
    }
    bool spfa(int n, int s, int t)
    {
        CLEAR1D(dis, HALF_MAX, NUM_V);
        CLEAR1D(pre, -1, NUM_V);
        CLEAR1D(inque, -1, NUM_V);
        dis[s] = qs = 0;
        inque[que[qs++] = s] = 0;
        pre[s] = n;
        int u;
        while (qs) 
        {
            u = que[0];
            inque[u] = -1;
            que[0] = que[--qs];
            if (qs) { inque[que[0]] = 0; }

            for (int i = 0, j = 2 * i + 1, t; j < qs; i = j, j = 2 * i + 1) {
                if (j + 1 < qs && dis[que[j + 1]] < dis[que[j]])
                    ++j;
                if (dis[que[j]] >= dis[que[i]]) 
                    break;
                BUBLLE;
            }
            for (int k = 0, v = adj[u][k]; k < num_adj[u]; v = adj[u][++k])
            {  
                if (flow_cur[v][u] && dis[v] > POTENTIAL(u, v) - cost[v][u])
                    dis[v] = POTENTIAL(u, v) - cost[v][pre[v] = u];
                if (flow_cur[u][v] < cap[u][v] && dis[v] > POTENTIAL(u, v) + cost[u][v])
                    dis[v] = POTENTIAL(u, v) + cost[pre[v] = u][v];
                if (pre[v] == u)
                {
                    if (inque[v] < 0)
                    {
                        inque[que[qs] = v] = qs; 
                        ++qs;
                    }
                    for (int i = inque[v], j = (i - 1) / 2, t; dis[que[i]] < dis[que[j]]; i = j, j = (i - 1) / 2)
                    {
                        BUBLLE;
                    }
                }
            }
        }
        for (int i = 0; i < n; ++i)
        {
            if (pi[i] < HALF_MAX) 
                pi[i] += dis[i];
        }
        return (pre[t] >= 0);
    }
    int run_edmonds(int n, int s, int t, int &flow_cost)
    {
        CLEAR1D(num_adj, 0, NUM_V);
        CLEAR2D(flow_cur, 0, NUM_V);
        CLEAR1D(pi, 0, NUM_V);
        int i, j;
        for (i = 0; i < n; ++i)
        {
            for (j = 0; j < n; ++j)
            {
                if (cap[i][j] || cap[j][i])
                    adj[i][num_adj[i]++] = j;
            }
        }
        int flow = flow_cost = 0;
        int bot = INT_MAX;
        int this_bot = INT_MAX;
        int v = 0, u = 0;
        while (spfa(n, s, t)) 
        {
            bot = INT_MAX;
            this_bot = INT_MAX;
            for (v = t, u = pre[v]; v != s; u = pre[v = u]) 
            {
                this_bot = (flow_cur[v][u] ? flow_cur[v][u] : (cap[u][v] - flow_cur[u][v]));
                bot = (bot < this_bot) ? bot : this_bot;
            }
            for (v = t, u = pre[v]; v != s; u = pre[v = u]) 
            {
                if (flow_cur[v][u])
                {
                    flow_cur[v][u] -= bot;
                    flow_cost -= bot * cost[v][u];
                }
                else
                {
                    flow_cur[u][v] += bot;
                    flow_cost += bot * cost[u][v];
                }
            }
            flow += bot;
        }
        return flow;
    }
    queue<int> passq;
    int dfs(int v, int minFlow)
    {
        int i;
        for (i = 1; i < num_v_cur - 1; ++i)
        {
            if (flow_cur[v][i] != 0)
            {
                passq.push(i);
                return dfs(i, (minFlow <= flow_cur[v][i]) ? minFlow : flow_cur[v][i]);
            }
        }
        return minFlow;
    }

    string printresult()
    {
        string str;
        int i,num = 0;
        int minflow = 0;
        bool flag = false;
        char ans[20];
        do{
            flag = false;
            for (i = 1; i < num_v_cur; ++i)
            {
                if(flow_cur[0][i] > 0)
                {
                    passq.push(i);
                    minflow = dfs(i, flow_cur[0][i]);
                    flag = true;
                    break;
                }
            }
            int fir = 0;
            int sec = 0;
            if (!passq.empty())
            {
                fir = passq.front();
                flow_cur[0][fir] -= minflow;
                sprintf(ans, "%d ", fir - 1);
                str += ans;
                sec = fir;
                passq.pop();
            }
            while(!passq.empty())
            {
                sec = passq.front();
                sprintf(ans, "%d ", sec - 1);
                str += ans;
                passq.pop();
                flow_cur[fir][sec] -= minflow;
                fir = sec;
            }
            if(flag)
            {
                ++num;
                sprintf(ans, "%d %d\n", conn[sec], minflow);
                str += ans;
            }
            else
            {
                sprintf(ans, "%d\n\n", num);
                string temp(ans);
                str.insert(0,temp);
            }
        }while(flag);
        return str;
    }

    int get_max_not_feed()
    {
        int max_not = -1;
        int temp = 0;
        int ID = 0;
        for (int i = 1; i < num_v_cur - 1; ++i)
        {
            temp = cap[i][num_v_cur - 1] - flow_cur[i][num_v_cur - 1];
            if(temp > max_not)
            {
                max_not = temp;
                ID = i;
            }
        }
        return ID - 1;
    }
};
#endif