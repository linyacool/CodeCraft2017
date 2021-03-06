# CodeCraft2017
2017华为软件精英挑战赛 
江山赛区36强。总结一下，避免以后忘记。
## 总体思路
采用的是大多数人用到的最小费用最大流+搜索。底层的费用流最开始用了spfa找增广路，在大case上慢的不行，后来用了zkw费用流，时间有了明显的提升，初赛800点的图从不到500次，提升到80000次。复赛的时候听赛区前几的大佬讲，大case上用单纯形比zkw还要快5倍。其实初赛前就知道单纯形快了，只是自己当时没把这个当重点，也懒得去找，满脑子想着怎么搜索才能搜的更快，以为是自己搜索出了问题，但是成绩一直上不去。最后输出路径dfs使用的流量就好，访问过多少流量就减去。
## 初赛
我是初赛最后两天才把spfa改成zkw，效率一提升，搜索的压力就下来了，按照之前的思路，中小规模的case很容易比较接近全局最优解。初赛最开始的思路是费用流+遗传算法，写完以后各种调参数，在这里花了10多天的时间吧，每次优化一点，排名只能上升一点，勉强续命续个一天。后来换了测试样例随机选点很难有可行解，连遗传算法的初始种群都跑不出来，就开始考虑其它方法。采用了爬山算法(刚开始还是模拟退火，有一定的概率接受次优解，实际跑下来几乎没啥用，就直接爬山了)，爬山的收敛速度很快，最慢的费用流都能很快收敛到局部最优解，但也仅仅是局部最优解，对中小规模的case来说，时间还很充裕，就加入了禁忌搜索，可以回退到某一步，从一个次优解继续寻找局部最优解。经过测试还是能降一些的，这样充分把时间利用起来。爬山当然得有初始解，初始解最笨的方法就是全部在消费点上安装服务器，但是初始代价太高了。我用了两种初始化方式，一种是把消费节点的需求排个序，直接把服务器按在较大的点上，从大了往小了按，直到能满足需求了，写程序是写的从小的往大的删点，删到不能删了为止。另一种方式是，求每个消费点相邻的消费点的数量(即每个消费点直接相邻的消费点的数量)，排序，相邻的消费点多，那么这个消费点是中心点，而且它的出度也大，在它身上装服务器肯定没错，如果与它相邻的只有一个，那就不能说它是中心点了，两个中选个需求大的装服务器，没有相邻点的不装。最后求一次费用流，可能会不满足需求，从消费点上找出那个最不满足需求的点(即它还需要最多的流量才能满足该点的需求)，在它上面放个服务器，循环到满足为止。这样初始化完找到的解就很低，再禁忌搜索，直到最后两天掉到了40多名。采用了zkw费用流后，排名才上去，最后几个小时正式样例的中小case都能找到最优解了(针对一下规模的话~)，但是不敢交了(当时最高分的代码只有一个是最优解)，当时十七八名吧，网站刚崩了一次，怕不稳，就放弃提交了。
## 复赛
复赛对服务器加了很多限制，我首先把所有的服务器都初始化为输出能力最强的那个。中规模600，大规模1200。  
### 中规模case
对中规模的进行换点，这里的换点既可以把点替换成图中其它的任意一个点，也可以删掉该点，也可以增加图中某个点。每次换点，取增、删、替换操作中费用下降最大的一个。
### 大规模case
因为用zkw，大规模采取中规模做法的话跑一轮循环，所以加入候选集，换点之前计算候选集，对图中所有的点计算n轮BFS，作为该点的候选集，就是找该点相邻的一些点，替换就从这些点里面去找，一般找1到2轮就差不多了，因为图比较稠密，多了数量爆炸。如果某个点的候选集太大，说明这个点的度中心性非常高，就直接不设置候选集了，这个点如果被选中了，就不进行替换操作了。  
  
最后统一降服务器的等级，能降多少降多少。因为zkw慢，才这样做，这样做很影响较优解的寻找，如果开始就用了单纯形，我会在换点的时候就降服务器的等级。
