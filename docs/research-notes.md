# Palimpsest research notes

本文件集中给出协议、知识提取定理、完整证明、参数账本和同功能比较。简明入口见 [文档导航](README.md)。

Palimpsest 面向原生环上的 Boolean 齐次二次来源关系，在同一格承诺下合并一个旧累积状态与多个新来源。模型为交互式、固定来源、经典重放和有界深度。

| 提取路线 | 数学状态 | 原型状态 | k=8 的完整递推乘数 |
|---|---|---|---:|
| cap=M 三点首次记录、两点弱锚点 | 本文第一部分及附录 D | 已有局部实现 | 54 |
| 无放回两点首次记录、两点弱锚点 | 附录 E 的独立审查替代定理 | 仅局部算术核验，未实现完整提取器 | 18 |

两条路线使用相同诚实协议和数值实例。R18 以固定坏斜率类界替代三点压缩不变量；它不是对旧代码常数的改名。全部适用范围和默认来源公开恢复的评估影响见 [研究范围](../docs/scope.md)。

## 导航

- [协议与实现基线定理](#part-protocol)
- [参数、成本与 arity](#part-parameters)
- [文献与同功能比较](#part-related)
- [技术附注与精确复算](#part-technical)
- [附录 A：证明细节](#appendix-proofs)
- [附录 B：LatticeFold+ 对照](#appendix-lfplus)
- [附录 C：公开来源恢复](#appendix-public-recovery)
- [附录 D：融合弱锚点与随机停止](#appendix-weak-anchors)
- [附录 E：两点无放回替代定理](#appendix-two-point)

## 符号约定

本文统一使用以下符号。

| 符号 | 含义 |
|---|---|
| $\lambda$ | 渐近安全参数；不与 Cauchy 系数混用 |
| $N,q$ | negacyclic 环次数和奇素数模数 |
| $R=\mathbb Z[X]/(X^N+1)$, $R_q=R/qR$ | 整数环与模环 |
| $\kappa,m$ | 均匀矩阵的环行数、witness 环坐标数 |
| $A,P$ | 均匀承诺矩阵、固定公开字段投影 |
| $r_P$ | $P$ 的行数，默认 9 |
| $n,n'=2^\ell$ | 实际约束行数、补零后的行数 |
| $f,\phi_\beta$ | 完整齐次二次关系、其随机加权压缩 |
| $\mathcal C,M$ | 强挑战集及其大小 |
| $D,T,s$ | 挑战支持长度、乘法算子范数界、固定重量；默认构造 $T=s$，不能把 $D$ 和 $T$ 混为一谈 |
| $k,H,L_{\rm src}=Hk$ | 每轮新来源数、轮数、总来源数 |
| $h_t,\Gamma_t$ | 第 $t$ 轮的诚实范数、逆向提取范数 |
| $G$ | 单步目标 opening 的范数上界 |
| $B_{\max}$ | 归约中所有 Module-SIS 核的统一系数无穷范数界 |
| $Q_3=1+9k/2$ | 三点 raw 提取的带成本乘数 |
| $Q_2=1+2k,\ \mathcal R=Q_3+Q_2=2+13k/2$ | 弱两点及融合全层的成本乘数；默认 k8 时17与54，不是整数环 R |
| $\Delta,\theta_f,\theta_o$ | 单步总统计损失、固定坏 fresh 类和坏 old 类的质量界 |
| $\tau,B_0,U_*,\mathcal T$ | 原对手最坏时间预算、已知局部费用上界、全局期望时间上界、严格截断时间 |
| $\varepsilon,\zeta$ | 原对手实际终端接受率、一次全局截断损失 |
| $\mathsf I$ | 首次挑战前冻结的完整来源输入带 |

---

<a id="part-protocol"></a>

# 第一部分：统一协议与主定理

## 1. 模型、承诺与关系

### 1.1 环和范数

令 $N$ 为 2 的幂，$q$ 为奇素数，

$$
R=\mathbb Z[X]/(X^N+1),\qquad R_q=R/qR.
$$

整数环向量 $z\in R^m$ 的范数为所有环坐标中所有系数的最大绝对值，记 $\|z\|_\infty$。模环元素的规范整数代表取逐系数中心代表。证明中出现的整数差、分子和乘积先在 $R$ 中计算并保留其整数提升，不能先模 $q$ 再把所得代表当作原来的整数范数证明。

对整数环元素 $a$，记乘法算子范数

$$
\|a\|_{\rm op}=\sup_{z\ne0}\frac{\|az\|_\infty}{\|z\|_\infty}.
$$

negacyclic 卷积满足 $\|az\|_\infty\le\|a\|_1\|z\|_\infty$，以及 $\|ab\|_\infty\le N\|a\|_\infty\|b\|_\infty$。整数环 $R$ 是整环，因为 $X^N+1=\Phi_{2N}(X)$ 在 $\mathbb Q[X]$ 上不可约。$R_q$ 可能有零因子，不能把 $R$ 的整环性质直接用于 $R_q$。

### 1.2 承诺与实际 Module-SIS 实验

Setup 均匀采样

$$
A\leftarrow R_q^{\kappa\times m},
$$

并固定公开线性投影 $P\in R_q^{r_P\times m}$。定义

$$
\operatorname{Com}(W)=(AW,PW).
$$

$PW$ 包含需与来源 witness 绑定的公开字段。来源承诺既包括 $AW$，也包括该公开分量；它不是独立可信声明。此承诺不另加隐藏随机性，本文不由它推导零知识或 hiding。

默认 scalar-bit 实例还有更强的公开恢复性质：$\operatorname{vec}(AW)=\widetilde A W$ 的2048×806均匀系数矩阵极高概率满列秩。这使默认来源可公开解码，不只是没有 hiding 保证。完整算法及其对实例定位的影响见附录 C；下述一般参数提取定理并不假定该矩阵满列秩。

给定随机 $A$，$\mathsf{MSIS}(q,N,\kappa,m,B)$ 要求输出整数环向量 $z\in R^m$，满足

$$
Az=0\pmod q,\qquad z\bmod q\ne0,\qquad \|z\|_\infty\le B.
$$

用 $\operatorname{Adv}_{\rm MSIS}(q,N,\kappa,m,B;\mathcal T)$ 表示在指定计费模型下、运行时间至多 $\mathcal T$ 的算法在该实验中的最大成功概率。公共关系与 $P$ 按真实 setup 生成，原对手可在看到 $A$ 后选择来源输入。归约使用的随机对象是 $A$，不是 $[A;P]$：后者的固定投影行不服从同一均匀分布。

### 1.3 来源关系

设 $n'=2^\ell$，必要时给实际 $n$ 条约束补零。向量

$$
W=(u,b_1,\ldots,b_{m-1})\in R_q^m
$$

满足一组固定的齐次二次多项式

$$
f=(f_a)_{a\in\{0,1\}^\ell}:R_q^m\longrightarrow R_q^{n'}.
$$

其中必须包含全部 $b_i^2-u b_i$，其余行是指定语义关系的齐次二次约束。零行视为允许的零多项式。来源公开投影强制 $u=1$。

对完整来源承诺 $C$，定义

$$
\mathsf{Source}(C;W)\iff
\operatorname{Com}(W)=C,\quad f(W)=0,\quad
u=1,\quad b_i\in\{0,1\}\subset R_q\quad(1\le i<m).
$$

最后的 $0/1$ 指常数环元素，不能将 $R_q$ 中任意幂等元视为合法 bit。提取器必须证明这一点。新来源的公开输出、会话与标签属于同一 $PW$；标签只是被绑定的数据，不自动表示所有者身份认证或签名。

### 1.4 压缩关系和 accumulator

对 $\beta=(\beta_0,\ldots,\beta_{\ell-1})\in R_q^\ell$，定义

$$
\beta^a=\prod_{i=0}^{\ell-1}\beta_i^{a_i},\qquad
\phi_\beta(W)=\sum_{a\in\{0,1\}^\ell}\beta^a f_a(W).
$$

accumulator 公开状态为 $x=(C,\beta,e)$。令

$$
\mathsf{Acc}(G,D)(x;W)\iff
\operatorname{Com}(W)=C,\quad\phi_\beta(W)=e,\quad
\|W^\mathbb Z\|_\infty\le G,\quad
\deg W_i^\mathbb Z<D\ \text{for every coordinate }i.
$$

这里 $W^\mathbb Z$ 是中心代表；$\deg<D$ 表示每个环坐标在 $X^D,\ldots,X^{N-1}$ 上的系数为零。accumulator witness 一般不再是 Boolean，也不要求 $u=1$。

### 1.5 强挑战集及环根界

令 $\mathcal C\subset R_q$，$|\mathcal C|=M\ge3$，满足：

1. 任意两个不同元素之差都是 $R_q$ 的单位；
2. 每个元素有指定的整数提升，系数属于 $\{-1,0,1\}$，支持次数小于 $D\le N$；
3. 这些提升的乘法算子范数至多 $T\ge1$；
4. 可以精确均匀抽样，且有已知的多项式期望比特成本。

**引理 1（强挑战集上的根界）。** 非零单变量多项式 $p\in R_q[Z]$ 若次数不超过 $d$，则在 $\mathcal C$ 中最多有 $d$ 个根。

**证明。** 若有 $d+1$ 个不同根，对系数向量构造 Vandermonde 线性系统。其行列式为不同挑战差的乘积，因此是单位。系统可逆，迫使全部系数为零，矛盾。此证明不要求 $R_q$ 是域。多变量非零多项式若总次数不超过 $d$，在 $\mathcal C^k$ 上的零点概率至多 $d/M$；逐变量归纳也给出各变量次数之和除以 $M$ 的较松界。本文统一使用后一种显式界。

### 1.6 模数门槛与对手模型

在单步目标半径 $G$ 下要求

$$
q>4NG^2+4TG.
\tag{1}
$$

若把原生 $R_q$ 关系解释为整数或 $\mathbb F_p$ 关系，还须为实际编译给出整数残差界 $B_{\rm arith}$ 和公开字段无别名界 $B_{\rm public}$，并检查

$$
q>\max\{B_{\rm arith},B_{\rm public}\}.
\tag{2}
$$

原始对手是经典、单会话、可重放的 PPT 算法，并有已知最坏时间预算 $\tau$。提取器可以恢复同一个 checkpoint 和原对手随机带；独立试验重新采样 verifier/extractor 的币。外部不可重放服务、量子重绕、并发多会话不在模型内。嵌套 suffix 提取器可以是已经分析了期望时间的算法；这不将原对手量词自动扩为任意 EPT 对手。

## 2. 实际协议与完备性

### 2.1 初始化和冻结输入

所有 $Hk$ 个来源的完整承诺、公开字段、顺序、会话标识以及 $H,k$ 和 genesis 构成不可变输入带 $\mathsf I$。它可以依赖 $A$，但必须在第一次公共挑战之前冻结。所有重绕分支使用同一个 $\mathsf I$。本协议没有把一个未经验证成员关系的哈希根当作这些来源的替代品。

genesis 为

$$
C^{(0)}=0,\qquad e^{(0)}=0,\qquad W^{(0)}=0,
$$

并采用公开规定的 $\beta^{(0)}$。

### 2.2 一轮消息

输入旧状态 $(C_0,\beta,e)$，以及本节已冻结的 $C_1,\ldots,C_k$。下面所有环运算在 $R_q$ 中进行。

1. **Verifier → Prover：** 均匀采样 $\delta\leftarrow\mathcal C$，令
   $$
   d_i=\delta^{2^i},\qquad 0\le i<\ell.
   $$
2. **Prover → Verifier：** 发送 $F_1,\ldots,F_\ell\in R_q$。验证者固定
   $$
   F(Z)=e+\sum_{r=1}^{\ell}F_r Z^r.
   $$
   常数项必须是已有 $e$，不可自由发送。
3. **Verifier → Prover：** 均匀采样 $\alpha\leftarrow\mathcal C$，更新
   $$
   \beta^*=\beta+\alpha d.
   $$
4. **Prover → Verifier：** 发送 $K_j\in R_q$（$1\le j\le k$）及 $K_{ij}\in R_q$（$1\le i<j\le k$）。不存在自由常数槽，也不存在 $Y_j^2$ 槽。
5. **Verifier → Prover：** 独立均匀采样 $y=(y_1,\ldots,y_k)\leftarrow\mathcal C^k$，双方更新
   $$
   C^*=C_0+\sum_{j=1}^k y_j C_j,
   \tag{3}
   $$
   $$
   e^*=F(\alpha)+\sum_{j=1}^k K_jy_j+
   \sum_{1\le i<j\le k}K_{ij}y_i y_j.
   \tag{4}
   $$

输出 $x^*=(C^*,\beta^*,e^*)$。一轮发送 $k+2$ 个独立挑战；$d$ 由 $\delta$ 派生，不额外发送 $\ell$ 个挑战。验证者做语法、维度、编码和状态更新检查；每轮并没有免费检查完整秘密 witness。最终关系检查由明确的终端接口提供。

### 2.3 诚实消息及二次恒等式

对齐次二次映射 $g$，定义极化

$$
B_g(U,V)=g(U+V)-g(U)-g(V).
$$

它是双线性的；恒等式不需要在环中除以 2。令 $g=\phi_{\beta^*}$，诚实 prover 发送

$$
F(Z)=\phi_{\beta+Zd}(W_0),\quad
K_j=B_g(W_0,W_j),\quad K_{ij}=B_g(W_i,W_j),
$$

并维护

$$
W^*=W_0+\sum_{j=1}^k y_jW_j.
\tag{5}
$$

$F$ 的次数不超过 $\ell$，常数为 $\phi_\beta(W_0)=e$。完整二次展开为

$$
g\!\left(W_0+\sum_j y_j W_j\right)
=g(W_0)+\sum_j y_j^2g(W_j)
+\sum_j y_jB_g(W_0,W_j)
+\sum_{i<j}y_i y_j B_g(W_i,W_j).
\tag{6}
$$

合法来源满足 $f(W_j)=0$，故 $g(W_j)=0$。式 (6) 化为式 (4)，线性承诺给出式 (3)，从而目标关系成立。

由于每个新来源坐标是常数 bit，$y_jW_j$ 的每个整数系数的绝对值至多 1，且支持次数小于 $D$。因此每轮诚实范数增加至多 $k$，并非 $kT$：

$$
h_t=tk,\qquad h_0=0.
\tag{7}
$$

这是确定性完备性账本，没有额外概率性范数失败项。整个 accumulator 不在每轮重编码为 bits；式 (5) 及其线性范数增长就是当前方案。

## 3. 三点 raw 提取

### 3.1 Oracle 接口和采样算法

固定一轮 pre-$\delta$ checkpoint。目标 oracle 在实际目标状态上返回一个通过 $\mathsf{Acc}(G,D)$ 核验的 opening $V$ 及其匹配的后缀，或返回失败；组合时也可返回已核验的同一 $A$ 的 Module-SIS 核。遇到核立即向上返回。

一次 raw trial 实际生成 $\delta/F/\alpha/K$，固定 pre-$y$ checkpoint 以及原对手和子 oracle 的随机带，然后执行下列步骤。同一 star 内的各次调用恢复子 oracle 的全部随机带；不同完整 raw trial 之间重新独立采样子 oracle 和 verifier/extractor 的币，原对手则始终从同一状态和同一随机带重放。

1. 采真正均匀的中心 $y\in\mathcal C^k$，调用目标 oracle。失败则本项失败，核则立即返回。
2. 第一阶段遍历全部坐标 $j$，固定其他坐标，在该 fiber 上独立均匀采样，寻找一个不同于中心的有效点；每坐标最多尝试 $M$ 次。
3. 第二阶段再遍历全部坐标，寻找不同于中心和首个 fork 的第二个有效点；每坐标最多尝试 $M$ 次。
4. 重复值、跳过值均计入尝试次数；任一阶段超时则失败。遇到核立即返回。
5. 完成全部坐标的三点采样后检查斜率。只保留最初中心及其原有后缀，fork 后缀仅作提取辅助。

设中心 opening 为 $V$，第 $j$ 个坐标的两个 fork 为 $V_j^{(1)},V_j^{(2)}$。令

$$
s_h=y_j-y_j^{(h)},\qquad
Y_h=V^\mathbb Z-(V_j^{(h)})^\mathbb Z,\qquad
W_j^{(h)}=s_h^{-1}Y_h\pmod q.
\tag{8}
$$

$s_h$ 是单位，$\|s_h\|_{\rm op}\le2T$，$\|Y_h\|_\infty\le2G$。承诺差分给出 $\operatorname{Com}(W_j^{(h)})=C_j$。此时 $W_j^{(h)}$ 只是弱 opening，尚未证明是 bit 或短向量。

### 3.2 斜率不同：实际非零整数核

若 $W_j^{(1)}\ne W_j^{(2)}$，输出整数向量

$$
z=s_2Y_1-s_1Y_2.
\tag{9}
$$

有

$$
Az=0\pmod q,\qquad
z\bmod q=s_1s_2(W_j^{(1)}-W_j^{(2)})\ne0,
$$

$$
\|z\|_\infty\le(2T)(2G)+(2T)(2G)=8TG.
\tag{10}
$$

非零性由两个单位和不同斜率保证；它不是仅有整数非零但模 $q$ 为零的无效解。

### 3.3 斜率相同：提取随机压缩的 fresh 关系

若两个斜率相同，记为 $W_j$。三个 opening 都在

$$
U(c)=V+(c-y_j)W_j
$$

上。对固定其他坐标，令

$$
P_j(c)=g(U(c))-e^*(y_1,\ldots,y_{j-1},c,y_{j+1},\ldots,y_k).
$$

$P_j$ 次数至多 2，其二次系数正是 $g(W_j)$：右侧消息没有 $Y_j^2$ 槽。它在三个有效挑战处为零。三个点两两差为单位，因此 Vandermonde 可逆，给出

$$
\phi_{\beta^*}(W_j)=0.
\tag{11}
$$

这一步不假定被提取的 witness 在挑战前固定；其结论来自实际三点和斜率一致性。

### 3.4 全部 cap 失败与带成本上界

固定一个 fiber，令有效点数为 $r$。有效中心的无条件质量为 $r/M$。当 $r\le2$ 时无法获得三个不同点，损失至多 $2/M$。当 $r\ge3$ 时，两段搜索中每次新提议的条件成功概率分别为 $(r-1)/M$ 和 $(r-2)/M$，其中心加权超时质量至多

$$
\frac{r}{M}\big(e^{-(r-1)}+e^{-(r-2)}\big)
\le\frac{3(e^{-2}+e^{-1})}{M}<\frac2M.
$$

对 fiber 和随机带平均，再对 $k$ 个坐标求和，raw 返回 record 或核的概率至少为

$$
p-\frac{2k}{M},
\tag{12}
$$

其中 $p$ 是目标 oracle 的 record-or-kernel 质量。这个式子已经包括全部超时，不另加未分析的 $\eta$。

令 $\mu$ 是固定 fiber 上均匀一次 trial 的增广平均成本，包含真实 oracle 成本、抽样、计数、重置、跳过和验证。允许本项成本与本项是否成功相关。中心加权的两段额外成本：$r=1$ 时至多 $\mu$，$r=2$ 时至多 $4\mu$，$r\ge3$ 时至多

$$
\left(\frac r{r-1}+\frac r{r-2}\right)\mu\le\frac92\mu.
$$

加上中心调用，得到

$$
Q_3=1+\frac{9k}{2}.
\tag{13}
$$

这是无条件加权期望，不是“每个条件接受分支”上的最坏时间界。$M$ 可以极大；不能将最多 $M$ 次搜索误称为确定性多项式循环。对含核的 oracle，可将核暂记失败分析 fiber；真实算法遇核早停，成本更低，原中心核质量直接计为成功。

## 4. 独立试验比较的基础引理

本节先给出对称 Gate 作为基础；§5–6.3据此解释两个有效性条件及其根界，实际默认提取器采用§6.4的融合弱锚点算法。

本工具继承 CauchyFold 的 independent-trial comparison（所读 PDF 附录 Lemma 3，物理页 40–41），采用先检查首次记录的安全提前退出版本。

固定 checkpoint，raw 算法 $O$ 的每次独立完整运行返回失败、已核验 kernel 或 candidate。令

$$
s=\Pr[O\ne\bot],\qquad \mu=\mathbb E[\operatorname{cost}(O)].
$$

设有可判定的 $\mathsf{Good}$ 和兼容关系，满足：两个不兼容 candidate 可产生规定半径的实际核；每个固定 bad candidate 的兼容类在未经成功条件化的 raw 分布中的质量至多 $\theta$。

```text
Gate(O, Good, Compatible):
    first = O()                         # 独立完整 raw 试验
    if first is failure or kernel: return first
    if Good(first): return first
    repeat:
        second = O()                    # 从同一 checkpoint 独立重试
    until second is not failure
    if second is kernel: return second
    if not Compatible(first, second): return ActualKernel(first, second)
    return failure
```

**引理 2（Gate）。** 该算法返回 good 或核的概率至少 $s-\theta$，raw 成本期望至多 $2\mu$，另加一次 Good 判断和必要的比较成本。

**证明。** 设首次 bad 质量为 $b\le s$。第二个非失败样本服从 raw 的非失败条件分布，故对每个首次 bad 的兼容概率至多 $\theta/s$。新增失败至多 $b\theta/s\le\theta$。若 $s=0$，算法不进入循环。重试总平均成本为 $\mu/s$：第 $i$ 次是否执行只依赖以前试验，对当次成本应用独立性和 Tonelli 即可；不要求当次成本与结果独立。乘上触发质量 $b\le s$，额外成本至多 $\mu$。

**首次完整记录支配。** Gate 从不返回第二个 candidate。对任意完整 record 集合 $E$，

$$
\Pr[\mathsf{Gate}(O)\in E]\le\Pr[O_{\rm first}\in E].
\tag{14}
$$

“完整”包括来源、中心 $y,V$、消息和 suffix。这是后续根界和历史组合的必要接口，不能降格为“只保留相同来源 tuple”。

## 5. Fresh 条件：从弱 opening 到合法 scalar bits

### 5.1 固定坏 fresh tuple 的质量界

raw 三点提取在非核记录上给出全部 $\phi_{\beta+\alpha d(\delta)}(W_j)=0$。对固定的坏 fresh tuple，取 $f(W_j)\ne0$ 的某个 $j$。在该向量非零行中取最大 Hamming weight $r$。关于 $\alpha$ 的最高非零候选系数为

$$
P_r(\delta)=\sum_{|a|=r}f_a(W_j)\,
\delta^{\sum_i2^i a_i}.
\tag{15}
$$

不同 $a$ 的二进制指数不同，至少一个系数非零，故 $P_r$ 是次数至多 $n'-1$ 的非零多项式。除至多 $(n'-1)/M$ 的 $\delta$ 外，关于 $\alpha$ 的多项式非零且次数至多 $\ell$。由根界，固定坏 fresh 类的 raw 质量至多

$$
\theta_f=\frac{n'-1+\ell}{M}.
\tag{16}
$$

实际质量当然最多 1；在需要一般形式时可将右侧截为 $\min\{1,\theta_f\}$。当前参数处于远小于 1 的区间。这里“固定 tuple”仅用于单类概率分析，未假定真实提取结果与挑战独立。

### 5.2 Fresh Gate 与跨试验核

兼容性定义为 normalized fresh tuple 相同，$\mathsf{Good}_f$ 实际检查全部 $f(W_j)=0$。两个不同 tuple 在某个来源分量上给出 $W=s^{-1}Y\ne(s')^{-1}Y'=W'$。整数向量

$$
z=s'Y-sY'
$$

满足同一 $A$ 的核方程、模 $q$ 非零和 $\|z\|_\infty\le8TG$。应用 Gate 后，有效 fresh 或核的质量至少

$$
p-\frac{2k}{M}-\theta_f.
\tag{17}
$$

### 5.3 缩放幂等引理及证明

**引理 3（弱 opening 的 scalar-bit 恢复）。** 设 $s$ 是单位，$Y=s b\pmod q$，$\|Y\|_\infty\le2G$，$\|s\|_{\rm op}\le2T$，且 $b^2=b$ 在 $R_q$ 成立。若式 (1) 成立，则 $b\in\{0,1\}$ 是常数 bit。

**证明。** 在整数环中，

$$
Y(Y-s)=0\pmod q,
$$

而

$$
\|Y(Y-s)\|_\infty
\le\|Y^2\|_\infty+\|sY\|_\infty
\le4NG^2+4TG<q.
\tag{18}
$$

每个系数既是 $q$ 的倍数又严格小于 $q$，故整数环中 $Y(Y-s)=0$。因为 $R$ 是整环，有 $Y=0$ 或 $Y=s$。模 $q$ 后利用 $s$ 可逆，得到 $b=0$ 或 $1$。

Fresh Gate 已证明全部 Boolean 行成立，公开投影又强制 $u=1$，所以逐坐标应用引理 3，恢复整个来源的规范 scalar-bit opening。顺序不能倒置：先用弱分子做绑定，再证明 full $f$，最后恢复 bits。

## 6. Old 条件与实际融合提取算法

### 6.1 重构短旧 opening

保留 Fresh Gate 首次 raw 中的中心 $y,V$，定义

$$
W_0=V-\sum_{j=1}^k y_jW_j\pmod q.
\tag{19}
$$

由于 fresh 已是 scalar bits，式 (19) 有支持次数小于 $D$ 的整数代表且范数至多 $G+k$。取中心代表不会增大系数范数。因此

$$
\operatorname{Com}(W_0)=C_0,\qquad
\|W_0^\mathbb Z\|_\infty\le G+k.
\tag{20}
$$

所得 $O_{\rm short}$ 返回完整 tuple $(W_0,W_1,\ldots,W_k)$ 及同一中心后缀，或核/失败；尚未过滤旧关系。

### 6.2 固定坏完整 tuple 的根界

固定完整 tuple 且假设 $\phi_\beta(W_0)\ne e$。给定 $\delta$ 以及已冻结的 $F$，多项式

$$
D_0(\alpha)=\phi_{\beta+\alpha d}(W_0)-F(\alpha)
$$

具有非零常数 $\phi_\beta(W_0)-e$，次数至多 $\ell$。因此除至多 $\ell/M$ 的 $\alpha$ 外，它非零。再给定在 $y$ 之前冻结的 $K$，令

$$
Q(Y)=\phi_{\beta^*}\!\left(W_0+\sum_jY_jW_j\right)
-F(\alpha)-\sum_jK_jY_j-\sum_{i<j}K_{ij}Y_iY_j.
\tag{21}
$$

其常数为 $D_0(\alpha)\ne0$，每变量次数至多 2，故对均匀 $y\in\mathcal C^k$，$Q(y)=0$ 的概率至多 $2k/M$。完整记录必须满足该等式。首次完整记录支配保证内层 Gate 不放大固定坏完整 tuple 的输出质量，所以

$$
\theta_o=\frac{\ell+2k}{M}.
\tag{22}
$$

必须固定/比较整个 tuple。仅固定 $W_0$ 时，新来源可能随 $y$ 改变，式 (21) 不再是 $y$ 前固定的多项式。

### 6.3 Old Gate 的兼容关系和核

兼容性为 $(W_0,W_1,\ldots,W_k)$ 完全相同，$\mathsf{Good}_o$ 为旧关系 $\phi_\beta(W_0)=e$。两个不兼容 tuple 若有 fresh 分量不同，两个 bit opening 的整数差给范数至多 1 的核；否则旧 opening 不同，整数差给范数至多 $2(G+k)$ 的核。它们都打开同一个已冻结输入承诺，差模 $q$ 非零。

第二次 Gate 后，单步提取器返回合法旧 opening、本节全部合法来源和首次中心后缀，或者实际核，概率至少

$$
p-\Delta,\qquad
\Delta=\frac{n'-1+2\ell+4k}{M}.
\tag{23}
$$

统一单步核界是 $\max\{8TG,2(G+k),1\}$。当 $G\ge k$、$T\ge1$ 时，等于上界 $8TG$。


### 6.4 默认算法：强三点记录与独立弱两点锚点

令 $S_3$ 是§3的完整三点 raw trial，包括从同一个 pre-$\delta$ checkpoint 重放实际前缀、核验所有目标 opening 和斜率。令 $W_2$ 运行同一前缀分布和中心，仅完成每个坐标的第一个 fork，然后用式 (8)、(19) 产生弱 opening 记录；它不检查压缩 fresh、full $f$、bits 或旧有效性。$W_2$ 的目标 opening 仍须满足实际目标承诺、压缩关系、范数和支持限制。只省略上层语义认证，不能省略目标核验。

**强弱支配。** 对分析使用相同中心、前缀及第一 fork 的地址化随机流；第二 fork 用其他独立流。三点算法先完成全部第一 fork，再完成第二 fork，所以 $S_3$ 返回 candidate 必然使耦合的 $W_2$ 返回 candidate。令 $a=\Pr[S_3\text{ 返回 candidate}]$，$s=\Pr[W_2\ne\bot]$，则 $a\le s$。这只是分布耦合证明；实际第二次独立锚点必须恢复同一 checkpoint 后使用全新的独立 continuation 币。直接跳过单一随机游标的一些调用不能替代该耦合。

```text
FusedStep(S3, W2):
    first = S3()
    if first is failure or verified same-A kernel: return first
    if not FullFreshValid(first):
        anchor = independent W2 trials until nonfailure
        if anchor is verified kernel: return anchor
        compare fresh residues using short numerators
        return resulting kernel, or failure if fresh tuples agree
    tighten first's fresh bits; reconstruct its short old opening
    if OldValid(first): return first with its ORIGINAL center and suffix
    anchor = independent W2 trials until nonfailure
    if anchor is verified kernel: return anchor
    compare fresh residues first; if different: return 8TG kernel
    transfer first's bitness to anchor's equal fresh openings
    reconstruct anchor's old opening from ITS OWN center and y
    compare old openings; return 2(G+k) kernel if different, else failure
```

两处重试采用完全相同的 $W_2$ 分布；首次 fresh 坏分支终止，不能再进入 old 分支。正常返回只可能是首次 $S_3$ 已通过两种实际有效性检查的记录。锚点从不替换该记录或后缀。

**概率。** 记首次强记录的坏 fresh 类质量为 $\sigma_f(u)$，弱锚点相应类质量为 $\omega_f(u)$。由式 (16)，$\sigma_f(u)\le\theta_f$。独立重试的锚点类分布为 $\omega_f(u)/s$，故 fresh 分支的新增失败质量

$$
\sum_{u\text{ bad}}\sigma_f(u)\frac{\omega_f(u)}s\le\theta_f.
$$

对 fresh 已有效而 old 无效的**完整 tuple** 类，式 (22) 给 $\sigma_o(v)\le\theta_o$，相同求和给新增失败至多 $\theta_o$。完整 tuple 的一致性按“先 fresh，再 old”核查；只有 fresh 相等才使用 weak old 的 $G+k$ 界。弱候选本身不需满足这两个根界。$s=0$ 时 $a=0$，重试从不触发。因而本算法仍满足式 (23) 的同一个 $\Delta$ 与 $8TG$ 半径。

**成本。** 设两个坏分支的触发概率为 $b_f,b_o$，则 $b_f+b_o\le a\le s$。若 raw 期望成本分别为 $\mu_3,\mu_2$，重试一次到非失败的平均费用为 $\mu_2/s$，即便当次输出和费用相关也是如此：到达下一次调用只依赖以前的独立试验。因此总 raw 费用

$$
\mu_3+(b_f+b_o)\mu_2/s\le\mu_3+\mu_2.
$$

cap=$M$ 的弱两点采样有 $Q_2=1+2k$：一个 fiber 的有效点数为 $r$，若 $r=1$，中心加权 fork 费用至多 $\mu$；若 $r\ge2$，至多 $r\mu/(r-1)\le2\mu$，再加中心。弱 sampler 的失败不另作为统计损失加入，因为它在本算法中仅通过 $a\le s$ 与独立重试使用。

于是全层 raw 子调用系数为 $Q_3+Q_2=2+13k/2$。这里没有先验将两个 Gate 的时间各乘二；互斥坏分支的联合计账是该改进的必要条件。完整局部成本见§8，弱锚点引理及可选随机停止的进一步证明见附录 D。

## 7. 有界深度历史组合

### 7.1 两套范数必须区分

对 $t=0,1,\ldots,H$，设

$$
h_t=tk,\qquad \Gamma_t=(2H-t)k.
\tag{24}
$$

诚实正向运行使用 $h_t$。逆向提取从 $\Gamma_H=Hk$ 开始，每轮按式 (20) 增加 $k$，恰有 $\Gamma_{t-1}=\Gamma_t+k$。不能声称任意 $\Gamma_{t-1}$ witness 可以正向缩至 $\Gamma_t$。模数门槛在最大单步目标半径 $G=\Gamma_1=(2H-1)k$ 检查。

### 7.2 终端接受实验

作为 RoK，原对手在实际随机交互完成后输出候选 $W_H$，令

$$
\varepsilon=\Pr[\mathsf{Acc}(Hk,D)(x_H;W_H)=1].
$$

在每个重绕分支，提取器实际继续同一个原对手，获得该分支自己的候选并验证；它没有免费 witness oracle。可选的完整在线协议让 prover 向 verifier 明文发送 $W_H$，执行同一终端检查。该方式闭合实际接受接口，但不提供零知识。最终 accept 位或承诺本身不能替代这个目标 witness。

### 7.3 Suffix 算法

```text
Suffix_H(actual final state):
    continue the original adversary to obtain its candidate W_H
    check Acc(H*k,D); return (W_H, empty suffix) or failure

Suffix_(t-1)(actual pre-delta checkpoint):
    run the concrete one-step extractor E_step
    its target oracle replays the selected current-step coins and runs Suffix_t
    validate each target record or same-A kernel
    if a kernel occurs: return it immediately
    if extraction fails: return failure
    prepend this step's source witnesses to the FIRST center's suffix
    return (old opening, that anchored lineage)

Extract(A):
    generate/freeze I as in the real experiment; use this same A everywhere
    run Suffix_0
    propagate failure or kernel
    if the centered genesis opening is nonzero modulo q:
        return it as a kernel
    return all H*k valid source witnesses and their matching center history
```

所有核均核查同一个均匀 $A$、模 $q$ 非零和统一整数范数。非零 genesis opening 范数至多 $\Gamma_0=2Hk$，仍由

$$
B_{\max}=8T(2H-1)k
\tag{25}
$$

覆盖。

### 7.4 组合概率

令 $p_t$ 为先执行真实无条件前 $t$ 轮前缀，再调用 $\mathsf{Suffix}_t$ 返回 record 或核的概率。中止前缀直接计失败，不重采有效前缀。对每个到达的 checkpoint 应用单步式 (23)，再对真实前缀分布平均，得

$$
p_{t-1}\ge p_t-\Delta,\qquad p_H=\varepsilon.
$$

因此

$$
\Pr[\text{完整合法来源历史或实际 same-}A\text{ 核}]
\ge\varepsilon-H\Delta.
\tag{26}
$$

核必须作为吸收成功计入归纳；若将子核当失败，会丢失最终归约所需的概率质量。Gate 仅返回首次记录，star 仅保留中心后缀，所以历史来自同一 $\mathsf I$ 上的一条匹配中心链。不保证它等于另一次预先指定的 transcript。

## 8. 显式时间与计算型主定理

### 8.1 全层提取乘数

§6.4的强三点与弱两点 raw 费用分别满足

$$
\mu_h\le P_{h,t}+Q_h(J_t+C_t)+A_{h,t},\qquad h\in\{3,2\}.
$$

$P_{h,t}$ 包含各自完整 pre-$\delta$ 到 pre-$y$ 前缀；$J_t$ 包含采样、重放、目标校验和调用边界；$A_{h,t}$ 是相应局部 star 代数和核核验。额外五块为：full-f 检查 $V_{f,t}$、首次 bit 紧化 $B_{{\rm bit},t}$、首次 old 重构及检查 $O_{{\rm old},t}$、任一互斥比较分支 $K_{{\rm cmp},t}$（含 weak 短 old 重构及核验证）、本层记录和后缀输出 $R_{{\rm out},t}$。它们是明确可计费工作，不可被当作免费常数。

$$
C_{t-1}\le\mathcal R C_t+D_t,\qquad
\mathcal R=Q_3+Q_2=2+\frac{13k}{2},
\tag{27}
$$

$$
\begin{aligned}
D_t={}&P_{3,t}+P_{2,t}+\mathcal R J_t+A_{3,t}+A_{2,t}\\
&+V_{f,t}+B_{{\rm bit},t}+O_{{\rm old},t}
+K_{{\rm cmp},t}+R_{{\rm out},t}.
\end{aligned}
\tag{28}
$$

固定 checkpoint 上先对采样及重放的增广成本加权，再对真实前缀分布平均；不对接受分支假定成功率下界。重新执行前缀以恢复状态的开销计入 $J_t$。

取已知、可计算的共同 $B_0$，逐项支配上述九个非 $J_t$ 块、$J_t$、终端 continuation/检查，以及初始化与最终输出费用之和。它来自原对手预算 $\tau$、实际尺寸及具体环算法的保守界，包含精确抽样的期望比特费用。于是

$$
D_t\le(\mathcal R+9)B_0,
$$

$$
U_*=B_0\left[1+\mathcal R^H+
(\mathcal R+9)\frac{\mathcal R^H-1}{\mathcal R-1}\right].
\tag{29}
$$

第一项支付初始化和最终处理，第二项支付终端展开，第三项为逐层局部费用。与旧 $4Q_3$ 方案比较时，必须以同时覆盖两种算法的共同 $B_0$ 解释，不能假定新旧具体实现具有相同实测单步时间。

### 8.2 一次整体截断

给定 $0<\zeta<1$，令

$$
\mathcal T=\left\lceil U_*/\zeta\right\rceil.
\tag{30}
$$

只对整台提取器设置一次截止，不对每层另行截断。Markov 给总截止损失至多 $\zeta$。令 $G_{\mathcal T},K_{\mathcal T}$ 为同一截断执行在截止前返回合法历史、实际核的互斥事件，则

$$
\Pr[G_{\mathcal T}\lor K_{\mathcal T}]
\ge\varepsilon-H\Delta-\zeta.
$$

让同一算法在 $K_{\mathcal T}$ 时将核交给 MSIS 挑战者，得到

$$
\Pr[K_{\mathcal T}]
\le\operatorname{Adv}_{\rm MSIS}
(q,N,\kappa,m,B_{\max};\mathcal T).
$$

### 8.3 主定理

**定理 4（具体计算型知识可靠性与有界深度组合）。** 在第 1–7 节定义的关系、消息时序、强挑战集、模数门槛、共享均匀矩阵、经典可重放原对手和冻结输入带模型下，对每个终端接受率为 $\varepsilon$ 的原对手，上述严格时间提取器在时间至多 $\mathcal T$ 内，以至少

$$
\boxed{
\varepsilon-
\frac{H(n'-1+2\ell+4k)}{M}
-\operatorname{Adv}_{\rm MSIS}
\left(q,N,\kappa,m,8T(2H-1)k;\mathcal T\right)
-\zeta
}
\tag{31}
$$

的概率输出全部 $Hk$ 个合法来源 witness 以及与零 genesis 相连的匹配中心历史。$\mathcal T$ 由式 (29)–(30) 明确给出。

**证明。** 单步式 (23) 包括三点搜索超时和两个固定坏类的损失。式 (26) 将所有同矩阵核作为吸收成功跨深度组合。式 (25) 覆盖所有核，包括 genesis。对两个返回分支一起做一次整体截断，再减去同一截断算法作为 MSIS solver 的成功率，得到式 (31)。只有一个线性 advantage 和一次 $\zeta$，没有每层平方根项、没有 $H$ 次 advantage 并集，也没有独立 genesis 计算项。

### 8.4 渐近推论及其量词

对参数族，若表示长度、原对手时间和各局部算法均为多项式，挑战可高效精确采样，$H\Delta$ 可忽略，相应 $B_{\max}$ 下的 Module-SIS 对 PPT 困难，并且

$$
H\log(2+13k/2)=O(\log\lambda),
\tag{32}
$$

则未截断提取器是 EPT，输出合法来源历史的概率至少 $\varepsilon-\operatorname{negl}(\lambda)$。理由是：若 EPT 算法产生核的概率不可忽略，可选择逆多项式量级的截断损失获得 PPT MSIS 攻击。固定 $k$ 时可允许 $H=O(\log\lambda)$。

这一推论没有证明同一个严格 PPT 提取器能同时取得任意可忽略的截断损失，也没有得到任意多项式深度 EPT。具体 $H=64,k=8$ 的时间常数非常大，必须在评估中如实展示。不能从渐近困难性直接推出该具体运行时间下的 128-bit 优势界。

## 9. 历史保存与在线验证的含义

在线 verifier 可访问不可变输入带 $\mathsf I$，并维护当前 $C,\beta,e$、会话和计数。已处理的消息可丢弃。prover 持有相应来源 witnesses 和当前 opening。若要离线转交历史而保留完整 transcript，则必须另计该空间与验证成本。

新 verifier 仅拿到最终状态及 opening，并不能知道此前挑战是诚实生成且按时序冻结的。当前定理是在线交互和真实接受实验中的知识继承；它没有构造离线可转移的 succinct 历史证书。冻结输入带、公开投影和标签的作用分别是固定来源、绑定同 opening 字段以及标识数据，这三者均不等于完整历史真实性证明。

---

<a id="part-parameters"></a>

# 第二部分：参数、成本与 arity 取舍

本节给出固定参数与成本账本。本节固定一个数值实例；arity 扫描保持同一关系，提取器替代不改变诚实通信。以下通信数字是明确编码规则下的公式账本，运行时间是符号计算量或提取器上界，均不冒充完整系统实测。

## 1. 当前唯一默认实例

核心理论对象是原生 $R_q$ 上的 Boolean 齐次二次关系及其知识归约。可审查的小应用是一份来源证明一次标量 $\mathbb F_p$ 乘法 $xy=E$。它不等于早期版本的 512 系数 $R_p$ 乘法任务，因此不能把不同版本的费用差写成同功能加速。

修订后的用途限定：默认806个scalar-bit坐标可通过公开2048×806系数矩阵恢复，该实例用于算术编译、编码与参数审计，不用于展示复杂来源提取的必要性。除了显式opening控制组，本节加入公开恢复控制组；附录 C 给出完整概率、算法、预处理与逐来源成本。

| 参数 | 当前值与含义 |
|---|---|
| $R_q$ | $\mathbb F_q[X]/(X^{512}+1)$ |
| $N$ | 512 |
| $p$ | $2^{51}-165=2251799813685083$ |
| $q$ | $170141573107009798923418825414604921797$ |
| q 的整数编码位宽 | 128；$\log_2q=127.00000330396485$ |
| 均匀承诺矩阵 | $A\in R_q^{4\times806}$，$\kappa=4,m=806$ |
| 固定公开投影 | $P\in R_q^{9\times806}$，共500个非零标量系数 |
| 实际/补齐约束数 | $n=809,n'=1024=2^{10},\ell=10$ |
| 默认 arity / 深度 | $k=8,H=64$ |
| 预先冻结的来源总数 | $Hk=512$ |
| 挑战支持 / 非零重量 | $D=128,s=64$ |
| 挑战系数界 / 乘法算子界 | $\chi=1,T=s=64$，是 coefficient-$\ell_\infty$ 算子范数 |
| 挑战集合大小 | $M=2^{64}\binom{128}{64}=441820661307488846482241581181767610368622944875184128000$ |
| 挑战熵 | $\log_2M=188.1714342001738$ |
| 诚实终端 opening 界 | $Hk=512$ |
| 逆向最大目标 opening 界 | $G_{\max}=\Gamma_1=(2H-1)k=1016$ |
| 全局 SIS 核半径 | $B_{\rm SIS}=8TG_{\max}=520192$，$\log_2B_{\rm SIS}=18.988684686772167$ |
| bit 恢复门槛左侧 | $4NG_{\max}^2+4TG_{\max}=2114320384<q$ |

$q$ 附有实际 Pocklington 素性证书；不是用 $2^{128}$ 占位。精确关系为

$$
q\bmod1024=965,\qquad \operatorname{ord}_{1024}(q)=256.
$$

因此 $X^{512}+1$ 的所有不可约因子次数为256。任意两个不同挑战之差是非零、次数小于128的多项式，不能被这样的不可约因子整除，故在 $R_q$ 中为单位。后续备选允许 $D=256$：差的次数仍至多255，单位性证明不变。

只将 $A$ 视为均匀矩阵。$[A;P]$ 不是均匀矩阵；每个不一致分支返回的实际整数向量仍必须满足 $Az=0\pmod q$、$z\bmod q\ne0$ 和给定范数。所谓“q128”仅表示整数位宽，不能写成“128-bit 计算安全实例”。

## 2. 806 坐标关系与位编码

代码中的七个51-bit字段按以下顺序排列：

| 量 | 零起始坐标区间 | 含义 |
|---|---:|---|
| $u$ | 0 | 齐次坐标，fresh 公开投影要求 $u=1$ |
| $x$ | 1–51 | 第一个乘法输入 |
| $y$ | 52–102 | 第二个乘法输入 |
| $E$ | 103–153 | 公开规范输出 |
| $h$ | 154–204 | 商 $(xy-E)/p$；早期参数说明中的 $t$ 是同一量 |
| $s_x,s_y,s_E$ | 205–255、256–306、307–357 | 规范范围补数 |
| session | 358–613 | 4个64-bit words，共256bits |
| source_label | 614–741 | 2个64-bit words，共128bits |
| sequence | 742–805 | 1个64-bit word |

每个多位字段按小端 bit 权重 $\sum_j2^jb_j$ 解码；每个 bit 占一个**完整环坐标中的标量常数**，并非把512个 bits 打包到同一环元素的不同系数。该选择使短化引理清楚，但必须计入806个环坐标的承诺成本。

四条实际算术行是

$$
u(x+s_x-(p-1)u)=0,\quad
u(y+s_y-(p-1)u)=0,\quad
u(E+s_E-(p-1)u)=0,
$$
$$
xy-uE-puh=0.
$$

再对每个非 u 坐标加入实际关系 $b_i^2-ub_i=0$，共805行。故

$$
m=1+7\cdot51+448=806,\quad n=805+4=809,\quad n'=1024.
$$

前四行是算术行，随后805行是 Boolean 行，最后补215个零行。提取证明先获得 full-f 有效性，再由弱 opening 与整数门槛证明这些坐标真是 scalar bits，不能把 Boolean 属性预先赋给任意弱 opening。

bit 恢复后，$u=1$ 和前三行保证 $x,y,E\in[0,p-1]$。第四行提升为整数等式 $xy-E-ph=0$，故得到真正的 $\mathbb F_p$ 乘法；诚实商 $h\in[0,p-2]$，51bits 足够。即使在提升之前只知道所有原始51-bit字段在 $[0,2^{51}-1]$，第四行残差的绝对值仍有界于

$$
B_{\rm arith}=(2^{51}-1)^2
=5070602400912913102387185451009<q.
$$

这是覆盖未加商补数约束的实际整数界，不只检查诚实商。另有 $q>2^{64}$，防止64-bit公开字段在模 q 下别名。

固定 P 输出：u、E、4个 session words、2个 source_label words、1个 sequence word。P 的非零标量项数为 $1+51+448=500$。fresh 的9个投影值均是常数环元素，但累积后一般是 $R_q$ 元素，不能始终按9个标量字打包。标签只绑定到同一 opening；不代表外部所有者身份已经认证。

## 3. 挑战采样、实际编码与安全预算

挑战空间为

$$
\mathcal C_{D,s}=\{c\in\{-1,0,1\}[X]:\deg c<D,\ \operatorname{wt}(c)=s\}.
$$

其大小 $M_{D,s}=2^s\binom Ds$，指定整数提升的无穷范数为1，negacyclic 乘法的 coefficient-$\ell_\infty$ 算子范数恰为 $s$。采样器先精确均匀抽取 rank，再组合 unrank；无需枚举指数大小的集合。**抽样用 rank 不等于线上使用 rank 编码**：现有传输 codec 使用 D-bit 位置 mask，后接 s 个符号 bits，按位置递增对应，检查重量、支持、padding及长度。每个挑战分别占

$$
c_{D,s}=\left\lceil\frac{D+s}{8}\right\rceil\ \text{bytes}.
$$

默认 $(D,s)=(128,64)$ 为24bytes；备选 $(256,40)$ 为37bytes。不能先拼接所有挑战再统一取整一次。

每轮独立发送 $\delta,\alpha,y_1,\ldots,y_k$，共 **k+2** 个挑战。向量 $d_i=\delta^{2^i}$ 的 $\ell$ 个坐标由 $\delta$ 派生，不是另 $\ell$ 个随机挑战，也没有额外通信。

当前三点提取每次搜索 cap 为 M；全部超时已包含在 $2k/M$ 的坐标采样损失，不再添加旧版 eta。固定 tuple 的两个根界为

$$
\theta_f=(n'-1+\ell)/M,\qquad
\theta_o=(\ell+2k)/M.
$$

单步损失与 H 层纯统计损失为

$$
\Delta=\frac{n'-1+2\ell+4k}{M},\qquad
\Delta_{\rm stat}=H\Delta=\frac{68800}{M}
\approx2^{-172.101313255697}.
$$

它严格小于 $2^{-160}$。这证明的是统计项，不是完整128位知识可靠性。

## 4. 提取运行时间、一次截断与计算假设

当前采用融合 early-good 算法：先取得一个强三点记录，检查 full-f、恢复 bits 并检查 old；任何坏分支只调用独立弱两点锚点作比较。坏分支互斥，只有首次强记录可正常返回。默认系数为

$$
Q_3=37,\qquad Q_2=17,\qquad
\mathcal R=Q_3+Q_2=2+13k/2=54.
$$

按第一部分式 (28) 的九个局部块逐项计费，

$$
C_{t-1}\le\mathcal R C_t+D_t,\quad
D_t\le(\mathcal R+9)B_0,\quad
U_*=B_0\left[1+\mathcal R^H+(\mathcal R+9)
\frac{\mathcal R^H-1}{\mathcal R-1}\right].
$$

共同 $B_0$ 覆盖新旧算法的命名局部工作、重放、抽样、终端和初始/最终输出；不是实测平均成本。域/环运算、矩阵与完整关系检查和记录处理均须计入。默认数值：

| 量 | 旧两强 Gate（归档） | 当前 cap=M 弱锚点 | 可选随机停止弱锚点 |
|---|---:|---:|---:|
| 全层系数 | 148 | 54 | 严格大于且约为26 |
| $\log_2\mathcal R^{64}$ | 461.405015 | 368.312800 | 300.828142 |
| $\log_2(U_*/B_0)$ | 462.472130 | 369.442861 | 302.091176 |
| 纯统计负log2 | 172.101313 | 172.101313 | 172.090617 |

旧式局部界为 $(\mathcal R+13)B_0$，新式为 $(\mathcal R+9)B_0$。可选随机停止的精确系数和证明见附录 D，不能将四舍五入的26当严格上界。两种新算法不改变 honest 消息、参数或SIS半径；默认保留cap=M以保持原统计预算。

示范取 $\zeta=2^{-130}$，**仅作预算示例**假设 $B_0=2^{128}$，默认 $\log_2\lceil U_*/\zeta\rceil\approx627.442861$。该数字仍极大；不是实测运行时间、实际可执行保证或安全位数。也不能把raw $Q_3^H$ 当完整提取成本。

令整台提取器与 kernel solver 共用一次截止 $\mathcal T=\lceil U_*/\zeta\rceil$。严格时间提取器输出合法来源历史的概率至少

$$
\boxed{\varepsilon-\Delta_{\rm stat}
-\operatorname{Adv}_{\rm MSIS}(q,N,\kappa,m,B_{\rm SIS};\mathcal T)-\zeta.}
$$

这是一个全历史 same-A solver 的**线性** advantage，没有逐层平方根项、H 次 advantage 并集或额外 genesis 计算项。witness 与 kernel 两分支一起截断，因此仅扣一次 $\zeta$。不能自行对每个子调用分别截断而保留此公式。

若另行假定 $\operatorname{Adv}_{\rm MSIS}(\mathcal T,B_{\rm SIS})\le2^{-130}$，与 $\zeta=2^{-130}$ 及统计项相加后小于 $2^{-128}$（显示负log2约129）。**项目没有证明这个具体 advantage 条件。**攻击模型输出的 log2 rop 不能代入这里当优势上界，也不能通过“1847减提取时间指数”来宣布安全位数。

渐近 EPT 结论要求参数与局部成本多项式、统计损失可忽略、相应 MSIS 对 PPT 困难，并控制 $H\log(2+13k/2)=O(\log\lambda)$。固定 k 与 $H=O(\log\lambda)$ 是充分情形；任意多项式深度没有得到证明。准确成功陈述是 $\varepsilon-\mathrm{negl}(\lambda)$，而不是不论 $\varepsilon$ 多小都几乎必然成功。

### 同协议两点/三点取舍

二点 oriented 基线也使用 Cauchy 比较，只有一个 gate：$Q_2=1+2k=17$，完整系数 $\mathcal R_2=2Q_2=34$，半径 $2(k+1)G(2T)^k$，统计损失 $H(n'-1+\ell+3k)/M$。在同一默认参数下：

| 提取方法 | $\log_2B_{\rm SIS}$ | $\log_2\mathcal R^H$ |
|---|---:|---:|
| 两点 oriented + 一个 gate | 70.158610 | 325.597622 |
| 三点强记录 + 两点弱锚点（cap=M） | 18.988685 | 368.312800 |

诚实协议消息不变；三点减小 SIS 半径，却增加提取时间。早期双分母比较的 $\log_2$ 半径126.158610只作为历史对照，不再作为当前基线。比较任意完整层系数与另一路线的 raw17 都是不公平口径。可选随机停止须同时更新两点对照：同一规则给两点单 Gate 系数 $2Q_2^*\approx18$，不能只给三点路线记优化收益。

## 5. 完整通信推导

按固定规范编码，每个 $R_q$ 元素有512个128-bit系数，占

$$
b_R=512\cdot128/8=8192\ \text{bytes}.
$$

系数必须规范小于 q；“128 bits”不是允许任意128-bit字符串。均匀 CRS 直接发送所有 $\kappa m$ 个环元素，没有未声明的短 seed 压缩。

每份 fresh packet 含 $\kappa$ 个 A 输出、51-bit规范 E 的7bytes、metadata的56bytes，u固定1不另发送：$b_{\rm src}=\kappa b_R+63=32831$。来源的 P 输出可由这组标量公开字段恢复。

每轮 F 有 $\ell$ 个非恒定系数，K 有 $k+\binom k2=k(k+1)/2$ 个环元素。因此

$$
b_{\rm round}=\left(\ell+\frac{k(k+1)}2\right)b_R,
\quad b_{\rm chal}=H(k+2)c_{D,s}.
$$

可选明文终端只传每个 opening 坐标的前 D 个系数；其余系数须为零。系数范围 $[-Hk,Hk]=[-512,512]$ 可按平移后的整数 $[0,1024]$ 用11bits表示，非法码拒绝。故

$$
b_{\rm terminal}=\left\lceil\frac{mD\lceil\log_2(2Hk+1)\rceil}{8}\right\rceil
=141856.
$$

此终端是明示的非零知识完整接受实验；它不是额外实例化的 succinct PoK。当前实现提供关系与接口测试，下面终端字节数是该规范的编码推导，不是完整网络 prover 的实测日志。

| 对象 | 精确公式 | 默认 bytes |
|---|---|---:|
| 均匀 A CRS | $\kappa m b_R$ | 26411008 |
| 一份 fresh A 承诺 | $\kappa b_R$ | 32768 |
| 一份 fresh 完整公开 packet | $\kappa b_R+63$ | 32831 |
| 冻结输入带 | $Hk(\kappa b_R+63)$ | 16809472 |
| 在线持久状态 | $(\kappa+9+\ell+1)b_R+48$ | 196656 |
| 每轮 F/K | $(10+36)b_R$ | 376832 |
| 全部 F/K | $H b_{\rm round}$ | 24117248 |
| 全部挑战 | $64\cdot10\cdot24$ | 15360 |
| 可选明文终端 | $\lceil806\cdot128\cdot11/8\rceil$ | 141856 |
| 完整会话，不含CRS及framing | 输入带 + F/K + 挑战 + 终端 | **41083936** |

CRS为25.1875MiB；完整会话为39.180695MiB。持久状态的48bytes用于session、sequence与轮号；它不包含 CRS、冻结输入带、证明者持有的 witnesses 或当前轮 F/K 缓冲。不能把196656bytes说成峰值工作内存。F/K可以流式处理，但当前没有实现级峰值内存跑分。

$\kappa=8,16$ 只作为矩阵 rank 敏感性：对应 CRS 为52822016、105644032bytes；同样512来源的输入带为33586688、67141120bytes；会话总量为57861152、91415584bytes。当前默认仍是 $\kappa=4$，不把敏感性行混入主结果。

### 同任务直接 opening 控制基线

**公开恢复是本实例必须展示的更强控制路线。** 在满列秩 setup 上，先对公开矩阵预处理，再从承诺恢复来源并检查全部关系，无需额外发送任何opening或folding消息。其会话通信恰为原输入带 **16,809,472bytes**，比当前fold少 **24,274,464bytes**。全806列保守算法每源恢复及全像检查用2,300,324次域乘，另计完整来源检查；一次性预处理为 $O(2048\cdot806^2)$ 域运算，额外持久缓存10,395,788bytes。这里的域运算不能直接与后文环运算比较时延。公开字段还能缩小未知数，故此基线不是最优恢复实现。

下列显式opening路线仍保留为不需要矩阵求逆预处理的简单对照，不能再称作最强直接基线。

在同一非ZK、冻结来源在线模型下，一个简单控制组直接发送每份来源的805bits（u已固定），分别按101bytes打包。512份合计51712bytes，加同样的来源公开输入带，得到

$$
b_{\rm direct}=16809472+51712=16861184\ \text{bytes}.
$$

这是未删除重复公开字段的简单控制组，不声称最优直接编码。当前累积会话比它多24222752bytes，**没有证明总通信优于直接检查**。最后的状态或 opening 也不是脱离 I 的离线历史证书；verifier仍需持有或访问完整冻结来源带。论文应讨论归约与工作安排的实际价值，而非从“承诺很短”推出“完整历史通信已经压缩”。

## 6. 验证者与证明者的符号计算复杂度

本小节是根据实际消息式新增的可检查符号推导，**不是已有 benchmark**。令 $\mathsf M_R(N,q)$ 表示一次通用 $R_q$ 乘法成本，$\mathsf A_R(N,q)$ 表示一次环加减成本；朴素实现分别至多 $O(N^2)$、$O(N)$ 个模 q 标量运算。支持稀疏、常数乘法或NTT可以优化，但未测量的优化不计入性能主张。

### 每轮在线 verifier

verifier 检查消息尺寸和规范编码，然后更新状态；本身在该轮不直接取得 fresh witness 来计算 full-f。最终可靠性来自具体 RoK 与终端条件。

- 派生 $d=(\delta,\delta^2,\ldots)$ 用 $\ell-1$ 次平方，更新 $\beta^*=\beta+\alpha d$ 用 $\ell$ 次环乘与 $\ell$ 次加法。
- $C^*=C_0+\sum_jy_jC_j$ 对 A 与 P 两部分共 $\kappa+r_P$ 个环坐标更新，通用上界为 $k(\kappa+r_P)$ 次乘法及同数加法。fresh P 值为标量，相关9k项可实现为标量乘稀疏环挑战；但结果与旧 P 状态是环元素，不能在累积后退回标量状态模型。
- 用 Horner 求 $F(\alpha)$ 为 $\ell$ 次乘法、$\ell$ 次加法。$\sum_jK_jy_j$ 为 k 次乘法；每个 $K_{ij}y_iy_j$ 按直接方式为2次乘法。故 e 更新为 $\ell+k^2$ 次环乘，$\ell+k(k+1)/2$ 次加法。

因此一个透明直算上界为

$$
V_{\rm round}^{\rm mul}=k(\kappa+r_P)+k^2+3\ell-1,
$$
$$
V_{\rm round}^{\rm add}=k(\kappa+r_P)+\frac{k(k+1)}2+2\ell.
$$

默认 $(k,\kappa,r_P,\ell)=(8,4,9,10)$ 为 **197次环乘/平方、160次环加减**，另计46个环消息的解析、10个挑战的抽样/编码校验与标签检查。197包含9次派生 d 的平方。这是未优化统一计数，不能写成现有代码的实测操作数。

### 诚实 prover

令 $\mathsf C_f$ 为一次实际 full-f 求值的环运算成本。源承诺在进入本节前已经冻结，应单独计入：一般矩阵乘法为每源 $\kappa m$ 次环乘；对当前 scalar-bit source，可改为选择矩阵列相加，因此 source commitment 不需要把每一项都实现成通用环乘。仍需处理 $\kappa mN$ 个系数量级的矩阵数据，不能据此忽略 CRS 访问。

F 的系数来自 $\phi_{\beta+Xd}(W_0)$。先求 $f(W_0)$，利用多线性权重的二叉递推展开每个 degree≤ell 的权重多项式，可给 $O(\mathsf C_f+n'\ell)$ 环运算的直接构造上界。

K 有 $k+\binom k2$ 个极化值。用 $B_g(U,V)=g(U+V)-g(U)-g(V)$ 逐对构造，朴素上界为

$$
O\big(k^2(\mathsf C_f+n'+m)\big)
$$

环运算，包括权重求值与向量加法。关系的稀疏极化可以进一步简化，但当前没有消除 $O(k^2)$ 个显式 K 消息，不能声称 high arity 下准线性通信。

诚实 $W^*=W_0+\sum_jy_jW_j$ 因 fresh $W_j$ 是 scalar bits，仅需条件地加上挑战；支持为 D，故可在 $O(kmD)$ 个模 q 系数加法内完成该 opening 更新。它不包括 F/K 的关系计算成本。

### 可选明文终端 verifier

终端至少执行：

1. 解析 $mD$ 个有符号系数、检查范数与 support；
2. 验证 $AW_H=C_{A,H}$，通用计数为 $\kappa m=3224$ 次环乘及相应累加；利用 W 的 D 支持可改进卷积，未据此给时延数字；
3. 验证 $PW_H=C_{P,H}$，P有500个标量非零项，是500项标量-环乘累加，不能当作500次独立均匀矩阵乘；
4. 求 $\phi_{\beta_H}(W_H)=e_H$，成本为 full-f 求值、$O(n')$ 个多线性权重与加权求和。

对本关系，一个可选的因式分解直算计数为：805个 Boolean 行各用2次环乘，三个范围行各1次，乘法行3次，共1616次通用环乘；另计七个51-bit命名线性形式的标量运算。全部1024权重可用1023次环乘生成，加权809个非零行至多809次环乘。这样关系/压缩部分的透明上界为3448次环乘，加 A 检查共6672次，另有 P、标量线性形式、加法与解析。这是**新增的代数上界**，不是现有 Python evaluator 的逐指令计量，也不是吞吐量测试。

## 7. Arity 扫描与保留默认的理由

arity 研究 固定相同512个来源、同一小关系、$m806,n'1024,N512,q,\kappa4,P$，扫描

$$
k\in\{2,4,8,16,32,64\},\quad H=512/k,\quad 1\le s\le D\le256.
$$

共检查197376个网格点。严格 $2^{-160}$ 统计门槛下有119118个可行点；严格 $2^{-168}$ 的可选8bit余量下有114378个。筛选用整数比较 $M>\text{statNumerator}\cdot2^b$，浮点 log 仅用于显示。未为不同 arity 发明不同协议，也未重新运行各点的攻击估算器。

固定 $D128/s64$ 的主要数据如下。全部总量包括相同输入带、F/K、挑战与明文终端，不含 CRS 与framing。

| k | H | $\Gamma_1$ / SIS半径 | F/K bytes | 完整会话 bytes（MiB） | 纯统计负log2 | $\log_2(U_*/B_0)$ |
|---:|---:|---:|---:|---:|---:|---:|
|2|256|1022 / 523264|27262976|44238880（42.189484）|170.133887|1001.604565|
|4|128|1020 / 522240|20971520|37941280（36.183624）|171.122947|616.586543|
|8|64|1016 / 520192|24117248|41083936（39.180695）|172.101313|369.442861|
|16|32|1008 / 516096|38273024|55238176（52.679230）|173.058995|216.360569|
|32|16|992 / 507904|70516736|87481120（83.428497）|173.977909|124.462036|
|64|8|960 / 491520|136970240|153934240（146.803131）|174.828248|70.676069|

最后一列已按融合提取基线默认系数 $2+13k/2$ 和九块局部费用重算这六个点；以覆盖相应局部工作和同一对手预算的**共同保守 $B_0$** 比较，不假定各配置真实单步时间相同。相同统计目标也不意味着相同计算安全。

固定总来源数 $S=512$，F/K 环元素数为

$$
\frac{S\ell}{k}+\frac{S(k+1)}2.
$$

连续近似最小点为 $k\approx\sqrt{2\ell}=\sqrt{20}$，所以可选整除 arity 中 k4通信较小是预期结果。k4比默认少约3MiB，但提取倍率大很多；k16降低深度但增加约13.5MiB。正文保留 k4/8/16，**继续以 k8 为稳定默认**。

固定 k8 的挑战参数取舍：

| 选择 | D/s | 挑战 bytes | 终端 bytes | 会话 bytes | SIS半径 | 纯统计负log2 |
|---|---:|---:|---:|---:|---:|---:|
|默认|128/64|24|141856|41083936|520192|172.101313|
|160bit门槛下最少字节|114/71|24|126341|41068421|577088|160.217167|
|160bit门槛下最小半径后取最少字节|245/35|35|271522|41220642|284480|160.107000|
|168bit余量下最少字节|119/74|25|131882|41074602|601472|168.047976|
|简洁备选|256/40|37|283712|41234112|325120|180.129806|

最少字节仅节省15515bytes（约0.0378%），却增大核半径约10.94%并消耗统计余量，不替换默认。D256/s40增加150176bytes（约0.3655%），半径降低37.5%，统计余量更强，是保留的备选；没有因此声称具体计算安全提升若干 bits。

每个 arity 的通信/半径非支配点数依次为33、32、32、32、32、33；arity 研究旧 $4+18k$ 提取倍率下的跨 arity 前沿为161点。该旧扫描快照没有按融合提取基线新时间重新扫描，161不作为新时间目标下的前沿结论。该前沿只优化这些明示指标，不能把所有前沿点都称为“最佳配置”。k2在同一挑战点上被k4三项支配；其余点留作可复查附录。

## 8. 实际格估算器结果：保留全部模型边界

项目确实运行了估算器，环境为 **SageMath10.9 / Python3.14.10**，`malb/lattice-estimator` 固定 commit：

`ccb2c740161b604225d52a746f5ba9a326f5c6c1`

工具源为 <https://github.com/malb/lattice-estimator/tree/ccb2c740161b604225d52a746f5ba9a326f5c6c1>。调用 `SIS.lattice`、infinity norm、`zeta=0`、LGSA，以及默认经典模式ADPS16和BDGL16成本模型；未运行量子攻击模型。

模型输入为

$$
n_{\rm scalar}=512\kappa,\qquad m_{\rm scalar}=512\cdot806=412672,
\quad q=\text{上述实际整数},\quad \beta=B_{\rm SIS}.
$$

真正的矩阵是 negacyclic 块构成的 Module-SIS 矩阵，**不是**均匀的普通 $n_{\rm scalar}\times m_{\rm scalar}$ 矩阵。下面是将结构矩阵用generic均匀SIS代理后的启发筛查：

| $\kappa$ | s | BKZ block | ADPS16 log2 rop | BDGL16 log2 rop |
|---:|---:|---:|---:|---:|
|4|64|6326|1847.192|1885.247|
|4|72|6231|1819.452|1857.507|
|8|64|14253|4161.876|4199.931|
|8|72|14045|4101.140|4139.195|
|16|64|31528|9206.176|9244.231|
|16|72|31078|9074.776|9112.831|

这里 $s=72$ 的半径为585216，默认 s64为520192。以上只是攻击模型成本，不是已证明的安全下界、计算优势上界或后量子安全位数。arity 研究 改变半径的各点没有新估算，不得将默认模型结果贴过去。

原始库在 `floor(2 ** (0.2075 * beta))` 处出现 Python float overflow。所用数值修正将底数/指数转为 Sage RR，攻击公式保持不变。不能把stock溢出解释成无限攻击成本。

扫描使用LGSA首项闭式避免每次分配412672项数组。四个实际q的对照点与原生数组首项log2最大差为 $1.62\times10^{-11}$；在 $\kappa4,s64,\mathrm{BKZ}=6326$ 上，原生完整LGSA数组的独立复跑仍给1847.192。记录包括12个模型扫描点、1个原生核对、1个stock异常。核对证明脚本与所选库公式一致，不证明该大维度启发式本身准确。

常数坐标限制给出的真正均匀标量子族只有806列，而最小 $\kappa N=2048$ 行；一般满列秩时无非零模q核。不能把完整412672列误标为相互独立的均匀列，也不能沿用旧大m实例的常数子族攻击数字。

该满列秩事实同时意味着默认来源可公开唯一恢复。初版材料只讨论无核的攻击含义，漏掉了这个原像恢复后果；现已由本节控制路线及附录 C 补全。一般环opening对应的结构矩阵，与此受限标量来源的均匀矩阵是两个不同对象。

### 已证明的有限 CRT 观察

$q=a^2+b^2$，其中

$$
a=12799962597113490746,\quad b=2510484140460851409.
$$

取 $\theta=a/b\pmod q$，则 $\theta^2=-1$，因子为 $X^{256}\pm\theta$。若某短环元素 $z=U+X^{256}V$ 在一个CRT分量为零，则逐系数 $u_i\pm\theta v_i=0\pmod q$，从而 $u_i^2+v_i^2=0\pmod q$。当 $2\beta^2<q$ 且 $\|z\|_\infty\le\beta$ 时只能全部为零。因此当前界内不存在仅支持一个CRT分量的非零短环元素。显式lift $a+bX^{256}$ 的系数范数约 $2^{63.472773}$，也远超默认 $2^{18.988685}$ 半径。

这排除的是“只解一个分量、另一个置零且不付lift代价”的直接做法；并未排除同时作用于两个分量的结构化攻击。不能由此宣布全部 Module-SIS 结构风险已经解决。

## 9. 复现入口

[参数与编码概要](../docs/parameters.md)连接默认实例和实际素性证书；[提取路线](../docs/extraction.md)区分实现基线与两点替代定理。仓库根运行：

```sh
python -B scripts/run_tests.py
python -B scripts/extraction_costs.py
python -B scripts/check_random_stop_costs.py
python -B scripts/check_local_refinements.py
```

这些入口分别运行局部原型测试、提取费用复算、随机停止精确枚举，以及无放回/坏斜率/低次数/Horner 局部核验。数学证明仍以本文所列实验、时序和量词为准。

---


<a id="part-related"></a>

# 第三部分：文献、贡献归属与同功能比较

本部分用于组织相关工作、贡献定位和评估章节。文献信息已对照所读 PDF首页；技术定位另核查指定定义、定理及评估页。ePrint链接用于定位文献，不表示已核验网站当前最新修订。下文页码均为所读PDF的物理页码，从1开始。不要把所有ePrint预印本统一写成已经同行评审发表的成果，也不要把ePrint编号年份误当本地修订日期。

## 1. 本篇应该提出的主张

Palimpsest目前最准确的定位是：**对原生格承诺下的scalar-Boolean齐次二次来源，给出具体的定量知识归约，并证明预先冻结全部来源、共享同一承诺矩阵时的有界深度在线组合。** 其结果有实际协议、具体提取算法、整数核证书、误差与运行时间账本；不是假设一个尚未实例化的联合证明后端。

本稿可以写清楚以下三项具体成果，但不要加“首个”“首次”或未经比较支持的最优性：

1. 在同一个opening上绑定来源承诺、公开字段和实际Boolean二次关系。三点局部提取先得到弱opening与压缩关系，之后证明完整来源有效性并由整数幂等式恢复真正scalar bits；不把短来源或bit性当作提取前提。
2. 把作者前作的短整数比较及独立试验比较用于这一明确接口，给出半径 `8TG` 的实际同矩阵kernel分支和可审查的来源/旧状态提取。源关系的限制、挑战时序和过滤顺序是定理内容，不是可略去的实现约定。
3. 通过首次中心记录保留、same-A kernel吸收、零genesis和完整期望成本递推，把H步组合落实为单一计算优势项及一次整体截断，并公开高arity的通信、范数与提取时间取舍。

作为RoK，成功实验要求原对手在真实交互末尾输出通过目标关系的候选witness；不等于只输出一个承诺就已经证明来源知识。可选明文终端opening给出完整的在线接受实验。当前结果不宣称零知识、任意深度、离线简洁历史认证、通用PCD、量子重绕、QROM或128位具体计算安全。

可用的英文定位句为：

> We give a quantitative reduction of knowledge for scalar-Boolean quadratic sources under lattice commitments, together with a bounded-depth online composition for a fixed collection of source statements. The construction makes source validity, short openings, and the extraction cost explicit, while retaining a single quadratic accumulator.

这句话是范围表述，不意味着已经证明相对所有已有方案的优越性。

## 2. 作者前作、Residue 与本篇的边界

Compare Before Clearing、Avoiding Product-Denominator Blowup 和 CauchyFold 是作者前作；其比较方法与表示工具在本文中按继承结果引用。

| 工作 | 本地原文确认的结果 | Palimpsest应如何引用 |
|---|---|---|
|Compare Before Clearing|直接比较归一化opening，再构造整数核；对其明确的多项式比较模型给出精确degree前沿和条件重采样。|归属“先比较、后处理分母”的方法。不能用较差的逐分支全分母清除界充当唯一基线。|
|Avoiding Product-Denominator Blowup|同步成功coordinate stars、处理成功偏置的共同challenge，并在其terminalized模型中扩展递归提取。|归属局部slack比较与同步思想。其每个中间accumulator先terminalize的递归接口不同，不能直接搬来宣称Palimpsest已有任意多项式深度。|
|The Residue Is the Resource|在固定公共随机性边界，刻画给定可用信息后所需的新状态宽度；给出restricted-domain、reconstruction和challenge-design结果。|用于说明“是否保留载体”不等于“是否存在必须传递的信息”，以及最优性必须附模型、域和边界。|
|CauchyFold|把Residue的scaled-Cauchy表示做成格协议：快速carrier构造、域内fold、规范重编码、后续field-to-linear归约及有限深度后端；Lemma 3给独立试验比较。|直接引用独立试验Gate；明确Palimpsest选择短环挑战、加性范数增长和显式K交叉项，未采用其Cauchy carrier或完整重编码后端。|

### 2.1 Residue 的确切内容与不可跨越的模型边界

Wang–Xiang的 *The Residue Is the Resource*，Theorem 3.1（PDF pp8–9），固定 admissible input domain X、actual challenge support、incoming state K与被计为免费的函数空间F。预挑战处理可任意非线性，后挑战读取必须对保留状态和incoming state线性。其最小新状态宽度为

`m_min = dim_F ((U(K)+V(H))/U(K))`。

这里的“宽度”是跨指定边界的新域坐标数，不是总通信、总运算量或知识可靠性。改变边界、free信息、incoming state或可接受来源域，都可能改变宽度。特别是该文明确研究了受限来源域，因此不能机械套用全空间下界到Palimpsest的scalar-Boolean来源。

其Section 6（PDF pp23–27）在来源完整乘积域 `S^(k+1)`、source-local信息免费且没有额外mixed incoming信息时，令r为polarization输出张成空间的维数，d_a为实际challenge support上 `a_i` 与 `a_i a_j` 的函数张成维数，则Theorem 6.1给精确直接宽度 `r d_a`。在额外的diagonal separation条件下，Proposition 6.2给 `d_a≥k` 与support大小至少 `2k+1`；Theorem 6.3证明scaled-Cauchy权重在至少 `2k+1` 个非极点上达到 `d_a=k`，从而达到rk。diagonal separation本身不是一般安全性定理。

Palimpsest既改变了来源域，也在最终y之前先通过δ/α压缩二次约束。它没有证明相应边界的最小状态维数。因此不能声称“绕过Residue下界”“无需任何mixed信息”“零宽度”或“residue-optimal”。对当前三点RoK，残差信息如何被认证比其是否最优编码更直接。

### 2.2 CauchyFold 已经做了什么，本篇没有做什么

CauchyFold的PDF pp2–6与Theorem 1明确把宽度/挑战设计归给其companion work Residue，并给两个避免枚举source pairs的carrier算法。固定relation维度时，其carrier构造关于k为quasi-linear；CauchyFold先承诺degree<k的carrier，再用一个Cauchy challenge形成fold，随后规范重编码并证明输出承诺与来源一致。

Palimpsest实际发送 `k` 个K_j及 `k(k−1)/2` 个K_ij，每轮连同F共

`ell+k(k+1)/2`

个完整环元素。故诚实mixed消息为 **O(k²)**，当前没有Cauchy式线性载体压缩或quasi-linear全部mixed生成定理。不能把标题或摘要写成“最优高arity载体”“线性通信”或“比CauchyFold更简洁”。“不额外承诺一个carrier”也不表示F/K中没有携带mixed信息。

本篇可强调的具体接口是：在受限Boolean来源上，直接认证full source relation并恢复tight source bits；维持一个二次accumulator；不额外给fresh添加独立range/projection helper commitments；诚实opening按 `h_t=tk` 增长。相应代价是限定来源关系、显式O(k²)交叉项和有限深度提取成本。它与CauchyFold提供的是不同取舍，未建立整体优越关系。

CauchyFold Lemma 3（PDF pp40–41）已给独立试验comparison的线性成功损失和至多2倍raw期望费用。本稿以该方法证明compatible-class根界、实际kernel与首次完整记录支配，再采用作者提供的《Bounded openings as independent comparison anchors》笔记中的非对称比较原理；本篇具体构造强三点/弱两点耦合，并联合计账两个互斥坏分支。其Lemma 4也已有另一种h-point采样策略；因此当前cap=M的 `Q3=1+9k/2` 应写成**本稿所分析sampler的界**，不要声称是普适最优采样常数。

## 3. 与主要格基路线的关系

| 方向 | 相关文献 | 本篇对照的具体内容 |
|---|---|---|
|知识归约框架|Algebraic Reductions of Knowledge；LatticeFold；Neo and SuperNeo|RoK可作为正式主结果；目标witness、关系包含、量词与提取成本必须明确。本文量化有已知预算的PPT原对手并构造EPT提取器，不冒用文献中更强的任意EPT对手定义。|
|范围和同opening后端|LatticeFold / LatticeFold+|它们提供真实range、linear/evaluation与commitment transformation链。本篇用Boolean结构和弱opening整数引理处理特定来源，不能称前者“不支持Boolean”。|
|有限轮数和范数控制|Cyclo / PikkuFold|有限深度与加性范数增长是已有合理研究范围；无额外helper commitments和小比较半径也不能不加限定写成全新普遍性质。|
|直接多项式fold|ProtogaLattice|一般多项式直接folding及bootstrapping已构成直接相关背景；不能只凭“直接二次”或“高arity”主张首创。当前协议的完备性由自身显式恒等式证明，不借用未经适配的外部图示。|
|累积到递归历史|Proof-Carrying Data from Accumulation Schemes；Accumulation without Homomorphism|有界累积是合法接口，但从在线更新状态到可转交的PCD/离线简洁历史认证还有组合义务。本文当前没有这些额外结论。|
|格证明的压缩后端|LaBRADOR；RoKoko|内部关系/证明压缩可作为后续终端或关系工具；其存在不自动证明本篇的来源历史被认证并继承。|

ProtogaLattice的所读 Figure 2曾在项目审查中出现显式完备性反例，因此本篇改为自己写出齐次二次加性协议。写作时不把这个项目记录扩张成“ProtogaLattice整体不安全”的笼统结论。若论文确需讨论该特定公式问题，应附确切版本、公式和反例，并与主贡献分开；当前相关工作只需承认其一般多项式folding的研究范围。

## 4. 已完成的同功能比较

### 4.1 直接控制路线：公开恢复和显式opening

默认来源可由公开均匀2048×806系数矩阵恢复，不需要发送opening。满列秩坏概率小于 $q^{-1243}/(1-1/q)$，是一个setup事件，不乘512。该控制路线应优先列入评估；其一次预处理和逐来源线性代数费用见本文件第二部分与附录 C。原来的显式opening控制组仍可用于比较不做求逆预处理的方案。

共同任务固定为512个预先冻结来源，同一 `A∈R_q^(4×806)`、同一固定P、同一805-bit私有坐标布局、同一公开字段、同一二次关系与在线验证模型。u=1固定隐含。基线逐来源传输其全部805bits，不假设辅助witness由x/y唯一决定；每个来源按101bytes独立对齐，验证者直接检查AW、PW和完整关系。

默认Palimpsest取 `N512,q128,kappa4,k8,H64,D128,s64`，每环元素8192bytes。以下是完整编码账本，不是实测时延；CRS及传输framing不并入会话总数。

| 对象 | Palimpsest默认 | 逐来源直接opening | 公开恢复后检查 |
|---|---:|---:|---:|
|均匀CRS|26,411,008 bytes|同一CRS|同一CRS|
|冻结的512来源输入带|16,809,472 bytes|16,809,472 bytes|16,809,472 bytes|
|64轮F/K|24,117,248 bytes|0|0|
|全部公共挑战|15,360 bytes|0|0|
|明文终端opening|141,856 bytes|0|0|
|全部直接来源opening|0|51,712 bytes|0|
|会话总通信，不含CRS/framing|**41,083,936 bytes**|**16,861,184 bytes**|**16,809,472 bytes**|

Palimpsest多出24,222,752bytes。直接基线的知识提取直接返回已发送的来源witness，不发生重绕或MSIS绑定损失。当前未证明相对该基线的总通信或完整验证运算/时延优势。这不否定知识归约定理，但禁止把上述表称作已实现的整体效率提升或历史压缩胜利。

上述24,222,752bytes是相对显式opening路线；相对公开恢复路线的差为24,274,464bytes。公开恢复控制checker通过时可直接返回其已验证的来源witness。这是另一套接受实验，不能仅由其存在跳过原folding接受事件到来源有效性与中心历史的安全证明。默认实例只用于编译/编码/参数展示，复杂提取的必要性不能由这个可公开恢复的小实例支撑。

Palimpsest持久在线状态的保守账本为196,656bytes，另需访问不可变输入带和CRS；这不包含每轮F/K临时缓冲。不能通过把输入带留在表外来宣称整个历史存储已压缩成这一个数字。

### 4.2 同一诚实协议下的提取路线取舍

两点oriented bridge和三点方案必须都使用前作Cauchy comparison，保持同一source、P、挑战、q/N/kappa和终端。下面是证明分析取舍，不是两套系统跑分。

| 量 | 两点oriented bridge | 当前三点路线 |
|---|---:|---:|
|SIS半径|`2(k+1)G(2T)^k`|`8TG`|
|默认log2半径|70.158610|18.988685|
|raw sampler系数Q|17|37|
|包括比较的每层系数R（cap=M）|34|54|
|H64时 $\log_2(\mathcal R^H)$|325.597622|368.312800|
|单步统计项|`1057/M`|`1075/M`|
|全历史计算损失|单一Adv+整体截断|单一Adv+整体截断|
|诚实协议新增消息|0|0|

三点确实降低比较半径，同时增大具体提取时间。完整成本应使用另有本地项的 $U_*=B_0[1+\mathcal R^H+(\mathcal R+9)(\mathcal R^H-1)/(\mathcal R-1)]$，不能把表中的 $\mathcal R^H$冒充全部成本。当前三点总纯统计误差约2^-172.101313，仍不能由此得出128位计算安全；启发式攻击成本也不是有限时间Adv上界。

### 4.3 外部LatticeFold+路线：共同知识目标，不同中间关系

已有公式级对照构造了同一Boolean/R1CS来源的具体LF+路线：来源R1CS→MLE线性声明→range/double commitments→commitment transformation→并行fold→decomposition。九个公开P输出作为同一个opening上的线性声明，不把[A;P]当均匀矩阵。两条路线最终都要求提取512个原始合法来源，并采用明文opening终端；Palimpsest末态是一个二次accumulator，LF+末态是两个有界linear/MLE accumulator。不能称两者具有逐字相同的中间目标关系或可直接互换target oracle。

该对照按LF+原版Construction 4.5确认尺寸条件 `n≥kappa d² a ell_d`。取d512、kappa4、a2、B=65536、ell_d16，可用原版保守参考宽度n=2^25满足条件；直接将本篇m806/补齐1024代入不合法。LF+ Remark 4.8给更小n的改造，但更换helper承诺数量并引入额外检查，不能同时沿用原版全部常数。保守补零参考点的大CRS/终端不是LF+最优实现，不能拿它宣称本篇胜出。

LF+ Theorem 5.3给的是主导通信项，且原文候选采用不同d、n、L、公开声明数量；本对照的extension评价与新增P声明也需计入。因此目前没有经核验、同一来源实例与同一具体安全目标下的精确总字节/时延倍率。可写清接口区别、合法尺寸条件与公式代价；不要编造一个最终总数来填满胜负表。

外部文献的PikkuFold 5.72KB、Cyclo约31.8KB、LF+≲100KB均来自不同参数与成本口径：可能不含incoming commitments、CRS、最终历史opening，关系、fresh arity和soundness目标也不同。只能作为带口径说明的背景数据，不能与本篇41MB完整会话直接作优劣判断。CauchyFold的k1024、162.67KiB同样是其特定关系下的无重试双向交互，排除了incoming commitments与CRS，不是本篇512来源任务的同功能数字。

### 4.4 High arity的合理表达

固定总来源512时，`H=512/k`，全部F/K通信为

`H[ell+k(k+1)/2]·8192 bytes`，

而完整提取递推系数为 $\mathcal R=2+13k/2$（默认cap=M融合弱锚点）。更大k减少深度但增加交叉项消息；当前默认k8不是所有指标最优。arity 研究扫描覆盖k2/4/8/16/32/64及强挑战D/s；融合提取基线另重算六个默认挑战点的提取时间，保留原默认，并明确不同SIS半径/截断时间不代表同计算安全。相关工作章节只需据此写“支持高arity并量化取舍”，不写“高arity带来总通信最优”。

## 5. 可靠文献条目与用途

以下标题和作者已直接核对所读 PDF首页；编号见所列链接，Residue编号另由CauchyFold参考文献WX26确认。建议先采用ePrint条目，避免根据二手材料猜正式会议年份、页码或DOI。该列表是写作所需的定向文献集合，不是全领域新颖性搜索。

| 建议键 | 作者；准确标题 | ePrint与主要用途 |
|---|---|---|
|KP-ARK|Abhiram Kothapalli; Bryan Parno. **Algebraic Reductions of Knowledge**.|[2022/009](https://eprint.iacr.org/2022/009)。Definition 8、Theorem 5，PDF pp17–18；RoK与组合标准。|
|BC-LF|Dan Boneh; Binyi Chen. **LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems**.|[2024/257](https://eprint.iacr.org/2024/257)。Definition 2.5、Theorem 3.1，pp15–19；完整range/RoK与CCS接口。|
|BC-LFplus|Dan Boneh; Binyi Chen. **LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems**.|[2025/247](https://eprint.iacr.org/2025/247)。range、double commitments、transformation与成本；对照以pp17–43及Appendix A为准。|
|NS-SuperNeo|Wilson Nguyen; Srinath Setty. **Neo and SuperNeo: Post-quantum folding with pay-per-bit costs over small fields**.|[2026/242](https://eprint.iacr.org/2026/242)。实际interactive-reduction组合、norm-preserving embeddings；Theorem 3及Definitions 9/10，pp17、21。|
|GLLO-Cyclo|Albert Garreta; Helger Lipmaa; Urmas Luhaäär; Michał Osadnik. **Cyclo: Lightweight Lattice-based Folding via Partial Range Checks**.|[2026/359](https://eprint.iacr.org/2026/359)。fresh范围检查、有限轮数与加性范数；评估pp13–14、37–40。|
|O-Pikku|Michał Osadnik. **PikkuFold: Efficient Folding in a Few Kilobytes**.|[2026/1809](https://eprint.iacr.org/2026/1809)。layered projections、无额外内部承诺、提取和采样；评估pp40–43、提取Appendix A。|
|BNP-PGL|David Balbás; Anca Nitulescu; Maxime Plançon. **ProtogaLattice: Lattice-based Algebraic Folding**.|[2026/1317](https://eprint.iacr.org/2026/1317)。一般多项式直接fold及bootstrapping背景；本篇不依赖归档Figure 2作为已验证后端。|
|WF-Compare|Xiang Wang; Shihui Fu. **Compare Before Clearing: Exact Integral-Comparison Frontiers for Lattice Extraction**.|[2026/1962](https://eprint.iacr.org/2026/1962)。作者前作；直接整数比较与比较degree模型。|
|WFO-Avoid|Xiang Wang; Shihui Fu; Michał Osadnik. **Avoiding Product-Denominator Blowup in Lattice-Folding Extraction**.|[2026/1841](https://eprint.iacr.org/2026/1841)。作者前作；局部slack、成功偏置同步及其特定递归接口。|
|WX-Residue|Xiang Wang; Ji Xiang. **The Residue Is the Resource: Exact Fresh-State Complexity, Reconstruction Limits, and Challenge Design in Folding**.|[2026/2019](https://eprint.iacr.org/2026/2019)。Theorem 3.1、6.1、6.3；精确宽度与Cauchy challenge设计。|
|W-Cauchy|Xiang Wang. **CauchyFold: Residue-Optimal High-Arity Lattice Folding via Scaled Cauchy Challenges**.|[2026/2011](https://eprint.iacr.org/2026/2011)。作者前作；Theorem 1快速carrier，Theorems 2/3实际提取，Lemma 3独立试验比较（pp40–41）。|
|BCMS-PCD|Benedikt Bünz; Alessandro Chiesa; Pratyush Mishra; Nicholas Spooner. **Proof-Carrying Data from Accumulation Schemes**.|[2020/499](https://eprint.iacr.org/2020/499)。累积到PCD的额外组合层。此为归档标题；不要无说明替换成其不同发表版本标题。|
|BMNW-AWH|Benedikt Bünz; Pratyush Mishra; Wilson Nguyen; William Wang. **Accumulation without Homomorphism**.|[2024/474](https://eprint.iacr.org/2024/474)。有界深度累积及PCD组合。|
|BS-LaBRADOR|Ward Beullens; Gregor Seiler. **LaBRADOR: Compact Proofs for R1CS from Module-SIS**.|[2022/1341](https://eprint.iacr.org/2022/1341)。可选格证明/终端工具背景，不自动解决来源历史。|
|KLNOT-RoKoko|Michael Klooß; Russell W. F. Lai; Ngoc Khanh Nguyen; Michał Osadnik; Lorenzo Tucci. **RoKoko: Lattice-based Succinct Arguments, a Committed Refinement**.|[2026/575](https://eprint.iacr.org/2026/575)。committed relations与格succinct argument后端背景。|
|LS-Units|Vadim Lyubashevsky; Gregor Seiler. **Short, Invertible Elements in Partially Splitting Cyclotomic Rings and Applications to Lattice-Based Zero-Knowledge Proofs**.|[2017/523](https://eprint.iacr.org/2017/523)。短可逆challenge背景；本篇实际候选另有直接因子次数证明。|
|AL-Subtractive|Martin R. Albrecht; Russell W. F. Lai. **Subtractive Sets over Cyclotomic Rings: Limits of Schnorr-like Arguments over Lattices**.|[2021/202](https://eprint.iacr.org/2021/202)。单位差challenge大小与限制；冒号表示原首页分行的主标题/副标题。|

若需要引用旧Neo单独版本，准确条目为Wilson Nguyen、Srinath Setty，*Neo: Lattice-based folding scheme for CCS over small fields and pay-per-bit commitments*，[2025/294](https://eprint.iacr.org/2025/294)。最终正文优先引用2026/242的合并版本；只有依赖旧版的具体估算脚本或页码时再明确引用2025/294，不把二者误写成独立不相关路线。

---

<a id="part-technical"></a>

# 第四部分：技术附注与精确复算

## 1. 两点路线的整数比较推导（对照材料）

这是与当前三点方案使用相同诚实消息的证明取舍，不是另一个默认协议。设两次 coordinate-star 记录分别有中心 $V,y$ 与 $V',y'$。第一组弱来源为 $W_j=s_j^{-1}Y_j$，其中 $\|Y_j\|_\infty\le2G$、$\|s_j\|_{\rm op}\le2T$。若两组某个 fresh opening 不同，局部比较已经给出 $8TG$ 的整数核；因此下一分支可以假设全部 fresh openings 相同。

令 $S=\prod_{j=1}^k s_j$，$S/s_j$ 表示其余 $k-1$ 个 slack 的整数乘积，**不是在整数环中执行除法**。定义

$$
z=(V^\mathbb Z-(V')^\mathbb Z)S
-\sum_{j=1}^k(y_j^\mathbb Z-(y_j')^\mathbb Z)Y_j(S/s_j).
$$

由两组中心重构关系，

$$
z\bmod q=S(W_0-W_0').
$$

当旧 opening 不同，由所有 $s_j$ 为单位可知 $z\bmod q\ne0$；相同旧承诺给 $Az=0$。第一个整数项的范数至多 $2G(2T)^k$，每个求和项也至多 $2G(2T)^k$，因此

$$
\|z\|_\infty\le2(k+1)G(2T)^k.
$$

相较把两组共同分母全部相乘的朴素界，定向比较只保留一组乘积。三点路线进一步通过 full-f 和 bit 恢复后比较短旧 opening，从而使用 $8TG$ 的统一界。论文若展示这一对照，必须同时展示提取时间和统计损失；不能只展示半径下降。上述技巧继承作者的比较方法体系，并非本篇新颖性声明。

## 2. 必须保留的反例与前提说明

这些反例可入证明附录或内部写作检查，不要求全部进入引言。

### 2.1 只检查中心差可逆不足以三点插值

取环 $\mathbb F_5\times\mathbb F_5$，三个点

$$
(0,0),\quad(1,1),\quad(1,4).
$$

两个非中心点与中心之差都是单位，但两 fork 之差不是单位。多项式

$$
p(Y)=(1,0)Y^2+(4,0)Y
$$

在三个点均为零，而二次系数非零。因此需要三个点**两两**差可逆。

### 2.2 仅有二次关系或 $f(0)=0$ 不足以斜率有效

取非齐次式 $f(x,z)=xz-x$。直线 $U(c)=(c,1)$ 上处处有 $f(U(c))=0$，但斜率 $W=(1,0)$ 满足 $f(W)=-1$。三点论证只读出二次齐次部分；当前关系必须按本文方式齐次化，并严格保留 $u$ 坐标。

### 2.3 模环幂等元不能自动当作 bit

当 $R_q$ 分裂时，CRT 分量可分别取 0 和 1，形成非平凡幂等元。故 $b^2=b\pmod q$ 本身不证明 $b$ 是常数 0/1。本文使用弱分子和模数门槛，将 $Y(Y-s)=0$ 提升到**整数整环**后才得到 bit。

### 2.4 归档中曾检查的外部公式问题

项目早期对所读 ProtogaLattice Figure 2 的特定恒等式作核查时，取 $f(a,b)=ab$、$W_0=(1,0)$、$W_1=(0,1)$，相关替代式会要求 $Y-1=K Y(Y-1)$，在 $Y=0$ 不成立。当前方案已以第一部分式 (6) 的完整二次展开为完备性依据。此处仅记录为什么不能继续套用该归档图式；它不是对外部论文所有版本或整体安全性的判定，不宜作为未经完整文献勘误核查的泛化指控。

### 2.5 不能省略的概率与费用接口

- 先重采到成功再套 raw 单类质量界，会改变分布；需要 Gate 中的显式 $b\theta/s$ 分析。
- Gate 不得返回重试记录来替换首次中心，否则下一层固定坏 tuple 根界和历史对应关系需重新证明。
- Old Gate 不能只比较旧 opening，必须比较完整 $(W_0,W_1,\ldots,W_k)$。
- 子 suffix 返回的核不能作为失败丢弃；它是全局 same-$A$ solver 的成功。
- 不可把 $Q_3^H$ 当作包含两个 Gate 的总时间；当前cap=M融合全层乘数是 $\mathcal R=Q_3+Q_2=54$；旧 $4Q_3=148$ 为归档对照。
- 不可对每个子调用分别截断，却仍只减一次全局 $\zeta$。
- 支持次数 $D$、挑战重量 $s$、算子界 $T$ 是不同角色；具体固定重量构造只有 $T=s$。

## 3. 精确参数复算脚本

下面只使用 Python 标准库，重算默认参数、主要 arity 表、可选挑战以及当前 $q$ 的递归 Pocklington 证书。它用于算术复核，不能替代概率证明、格攻击分析或完整协议实现。脚本仅依赖 Python 标准库。

```python
from fractions import Fraction
from math import comb, gcd, isqrt, log2

N, q, kappa, m = 512, 170141573107009798923418825414604921797, 4, 806
nprime, ell, total_sources = 1024, 10, 512
ring_bytes = N * ((q.bit_length() + 7) // 8)
source_bytes = kappa * ring_bytes + 63  # E:7; session/source/sequence:56
input_bytes = total_sources * source_bytes
crs_bytes = kappa * m * ring_bytes
direct_bytes = input_bytes + total_sources * ((m - 1 + 7) // 8)

def ledger(k, D=128, s=64):
    assert total_sources % k == 0 and 1 <= s <= D <= 256
    H = total_sources // k
    M = (1 << s) * comb(D, s)
    G = (2 * H - 1) * k
    beta = 8 * s * G
    assert q > 4 * N * G * G + 4 * s * G
    assert q > ((1 << 51) - 1) ** 2 and q > (1 << 64)
    stat = Fraction(H * (nprime - 1 + 2 * ell + 4 * k), M)
    challenge_bytes = (D + s + 7) // 8
    fk_bytes = H * (ell + k * (k + 1) // 2) * ring_bytes
    challenges = H * (k + 2) * challenge_bytes
    coeff_bits = (2 * H * k).bit_length()  # ceil(log2(2Hk+1))
    terminal = (m * D * coeff_bits + 7) // 8
    Rcost = Fraction(4 + 13 * k, 2)
    Ufactor = Fraction(1 + Rcost ** H) + Fraction(
        (Rcost + 9) * (Rcost ** H - 1), Rcost - 1)
    return {
        'k': k, 'H': H, 'D': D, 's': s, 'beta': beta,
        'stat_bits': log2(stat.denominator) - log2(stat.numerator),
        'FK_bytes': fk_bytes,
        'session_bytes': input_bytes + fk_bytes + challenges + terminal,
        'log2_U_over_B0': log2(Ufactor.numerator) - log2(Ufactor.denominator),
    }

# Pocklington: each certified factor r divides n-1 and exceeds sqrt(n).
chain = [2147483647, 36028848541794281,
         39614081257699650756468527203, q]
assert all(chain[0] % d for d in range(2, isqrt(chain[0]) + 1))
for r, n in zip(chain, chain[1:]):
    assert (n - 1) % r == 0 and r * r > n
    assert pow(2, n - 1, n) == 1
    assert gcd(pow(2, (n - 1) // r, n) - 1, n) == 1
assert q % (2 * N) == 965
assert pow(q, 256, 2 * N) == 1 and pow(q, 128, 2 * N) != 1

assert crs_bytes == 26411008 and input_bytes == 16809472
assert direct_bytes == 16861184
assert ledger(8)['session_bytes'] == 41083936
assert ledger(8)['beta'] == 520192
assert ledger(8, 256, 40)['session_bytes'] == 41234112
assert ledger(8, 256, 40)['beta'] == 325120
assert input_bytes == 16809472  # public-recovery control: no extra opening
assert 4*N - m + 1 == 1243     # exponent in rank failure bound
assert ledger(8)['session_bytes'] - input_bytes == 24274464
print('public recovery: source packet bytes only =', input_bytes)
print('rank failure bound approximately 2^(-%.6f)' % ((4*N-m+1)*log2(q)))
for k in [2, 4, 8, 16, 32, 64]:
    print(ledger(k))
print('optional:', ledger(8, 256, 40))
# Appendix E: reviewed alternatives; the implemented baseline remains R54.
M = (1 << 64) * comb(128, 64)
for alternative_R, stat_num in [(34, 68416), (26, 68800), (18, 68416)]:
    alternative_U = Fraction(1 + alternative_R**64) + Fraction(
        (alternative_R + 9)*(alternative_R**64 - 1), alternative_R - 1)
    print('Appendix E:', alternative_R,
          'log2(U/B0)=', log2(alternative_U.numerator)-log2(alternative_U.denominator),
          'statistical_bits=', log2(M)-log2(stat_num))
```

$\operatorname{ord}_{1024}(q)=256$ 的检查只需排除 128，因为 256 的所有真因子均整除 128。该结论结合有限域分圆多项式分解定理，给出 $X^{512}+1$ 的两个不可约因子均为 256 次。非零挑战差次数小于 $D\le256$，故不能含其中任何因子，因而是单位。

---

<a id="appendix-proofs"></a>

# 附录 A：关键证明的完整展开

本附录展开第一部分主论证中的条件概率、停止时间、记录对象与量词细节。它保持同一个协议和参数；独立试验比较工具引用 CauchyFold，其用于本关系的兼容类根界、范数和历史组合由下文明确给出。

## A. 统一前提与记录对象

令

$$
R=\mathbb Z[X]/(X^N+1),\qquad
R_q=R/qR,
$$

其中N为2的幂、q为奇素数。所有整数范数均指次数小于N的唯一整数代表的系数$\ell_\infty$范数；模q向量在需要比较或检查目标范数时取逐系数中心代表。整数证书中的乘法是$R$内的negacyclic乘法，不能先模q约减后把所得小数称为原整数界。

均匀矩阵$A\in R_q^{\kappa\times m}$与固定投影P定义

$$
\operatorname{Com}(W)=(AW,PW).
$$

假设只施加于A；$[A;P]$不需要、也通常不服从均匀矩阵分布。P的一行选择u，fresh公开输入强制u=1。其余坐标为$b_i$，实际齐次二次关系f含全部$b_i^2-u b_i$行。记$n'=2^\ell$，零行补齐，定义

$$
\phi_\beta(W)=\sum_{a\in\{0,1\}^\ell}\beta^a f_a(W),
\qquad \beta^a=\prod_{i=0}^{\ell-1}\beta_i^{a_i}.
$$

强挑战集$\mathcal C\subset R_q$有M≥3个元素，任意不同元素之差为单位。指定整数提升满足系数绝对值≤1、支持次数<D、乘法算子范数≤T。实际固定重量挑战有T=s，而不是T=D。

此算子界使用整数negacyclic乘法：其系数矩阵每一行都是输入系数的带符号排列，因此诱导$\ell_\infty$范数恰为系数$\ell_1$范数。恰有s个±1系数时为s，两挑战差的算子范数由三角不等式至多2s；不是用谱范数代替系数无穷范数。

固定一个pre-δ checkpoint σ。它包含旧状态$(C_0,\beta,e)$、本批全部来源$C_1,\ldots,C_k$、原对手状态/可重放随机带以及已发生的历史。所有独立试验都恢复到同一个σ。原对手不会在重试时更换；重采的是verifier/extractor及子suffix的币。

目标oracle可返回失败、有效目标记录，或实际已核验的同A核。有效记录至少包含：本项中心挑战y、目标opening V、实际δ/F/α/K、V所属的目标状态以及锚定该状态的后缀。它满足

$$
\operatorname{Com}(V)=C_0+\sum_jy_j C_j,
\quad \phi_{\beta^*}(V)=e^*(y),
\quad \|V\|_\infty\le G,
\quad \deg V_i<D.
$$

其中

$$
\beta^*=\beta+\alpha d(\delta),\quad
d_i(\delta)=\delta^{2^i},
$$

$$
F(Z)=e+\sum_{r=1}^{\ell}F_rZ^r,
\quad
e^*(Y)=F(\alpha)+\sum_jK_jY_j+\sum_{i<j}K_{ij}Y_iY_j.
$$

F在α之前冻结，K在y之前冻结。不存在自由常数或$Y_j^2$消息槽。这些时序和槽位限制是下文根界及三点论证的前提。

## B. 环上的根界为什么可用

### B.1 一元根界

设$h(Z)=\sum_{i=0}^d h_iZ^i\in R_q[Z]$非零。若它在$d+1$个不同强挑战$c_0,\ldots,c_d$上取零，则系数向量满足Vandermonde线性方程。其行列式为

$$
\prod_{0\le i<j\le d}(c_j-c_i),
$$

是单位之积，故该矩阵在$R_q$上可逆，迫使全部系数为零，矛盾。因此h在$\mathcal C$上至多d个根。

这里不要求首项系数可逆，也不要求$R_q$是域。所需条件是所有不同采样点之差为单位；只验证两个中心差可逆不足以支持三个点的插值。

### B.2 多元保守根界

若非零$h(Y_1,\ldots,Y_k)$对每个变量次数≤2，独立均匀$y_j\leftarrow\mathcal C$，则

$$
\Pr[h(y)=0]\le \min\{1,2k/M\}.
$$

证明可按变量归纳：将h视为最后变量的多项式，选其一个非零系数多项式。除该系数为零的至多$2(k-1)/M$概率外，所得一元多项式非零，再付$2/M$。本篇保留此统一保守界，不借更紧的总次数界更换既定预算。

## C. 三点记录为何给出fresh压缩有效性

固定pre-y状态及全部子oracle随机带。对第j个坐标，取得中心和两个不同fork，分别记$c_0=y_j,c_1,c_2$及$V_0,V_1,V_2$。其余y坐标不变，三个目标均已核验。指定整数提升给

$$
s_h=c_0^{\mathbb Z}-c_h^{\mathbb Z},\qquad
Y_h=V_0^{\mathbb Z}-V_h^{\mathbb Z},\qquad
W_j^{(h)}=s_h^{-1}Y_h\pmod q,
\quad h=1,2.
$$

由目标承诺相减，$\operatorname{Com}(W_j^{(h)})=C_j$。并且

$$
\|s_h\|_{\rm op}\le2T,\qquad \|Y_h\|_\infty\le2G.
$$

若$W_j^{(1)}\ne W_j^{(2)}$，在整数环计算

$$
z=s_2Y_1-s_1Y_2.
$$

它满足$Az=0\pmod q$，且

$$
z\bmod q=s_1s_2(W_j^{(1)}-W_j^{(2)})\ne0,
\qquad \|z\|_\infty\le8TG.
$$

非零性来自两个slack是单位，以及规范环向量确实不同；不是由“整数z看起来非零”推出。投影同时给$Pz=0$，不影响向均匀A的归约。

若两个斜率相同，记共同值为$W_j$，三个opening都在

$$
U(c)=V_0+(c-c_0)W_j
$$

上。置$g=\phi_{\beta^*}$。多项式

$$
h_j(c)=g(U(c))-e^*(y_{-j},c)
$$

次数≤2，且$c^2$系数恰为$g(W_j)$：g齐次二次，而$e^*$对单个变量c是仿射。三点两两差均为单位，所以B.1的插值论证迫使全部系数为零，特别是

$$
\phi_{\beta^*}(W_j)=0.
$$

这一步没有声称fresh在挑战前已固定；它是由实际取得的三点及其opening计算出的恒等式。未齐次化的二次多项式通常不能沿用“平方系数就是g(W_j)”这一步。全体k个坐标通过后，raw记录具有全部fresh的压缩有效性及弱短分子/slack证书，但尚未证明full-f、scalar bits或旧关系。

## D. cap=M的fiber搜索：失败质量与实际成本

### D.1 固定随机带的合法性

一个star内部固定pre-y checkpoint和全部子suffix/extractor随机带，使目标oracle成为确定的结果函数及成本函数$y\mapsto(O(y),c(y))$。每次fork必须从同一随机带入口恢复，不能使用持续前移的游标。完整raw试验之间则重新独立采样这些带。

若子oracle是EPT，其无限运行随机带的概率为零。挑战空间是有限集，故排除有限并的零概率集合后，可以同时定义所有y上的有限结果和成本。先在每组固定带上证明fiber不等式，再以Tonelli平均，允许成本与接受结果任意相关。

### D.2 失败质量

固定其它k−1坐标，一个fiber有r个有效record点，接受中心质量为r/M。每次搜索最多M次独立均匀有放回抽样；抽到中心或已接受fork也计一次trial，只是不调用或不接受为新fork。

若r≤2，不可能获得三个不同record，失败中心质量≤2/M。若r≥3，两次搜索的单次成功率分别为$(r-1)/M$、$(r-2)/M$。第二个数字与第一个成功点的身份无关。故加权失败质量至多

$$
\frac rM\left[\left(1-\frac{r-1}{M}\right)^M
+\left(1-\frac{r-2}{M}\right)^M\right]
\le\frac{r(e^{-(r-1)}+e^{-(r-2)})}{M}
\le\frac{3(e^{-2}+e^{-1})}{M}<\frac2M.
$$

r≤2与r≥3是互斥情形，取最大值，不能把两类上界相加。对k个坐标作并界，得到总损失≤2k/M。可预先定义各坐标的虚拟搜索，再删去此前失败后不再执行的工作；提前终止不会增加这个并界或成本。该2k/M已经包括全部超时，不另有eta项。

### D.3 不独立的成功与成本

固定fiber，给每次均匀点x一个增广成本$c^*(x)\ge0$，包含目标oracle、采样、恢复、计数、比较/跳过重复点的费用上界，令

$$
\mu_{\rm fib}=\frac1M\sum_{x\in\mathcal C}c^*(x).
$$

即使重复点跳过oracle，实际费用也不超过增广费用。对单阶段成功率p、最多M次试验，令$I_i$表示第i次试验会执行；它只依赖过去试验，独立于当前均匀点及其成本。因此

$$
\mathbb E\!\left[\sum_{i=1}^M I_i c^*(X_i)\right]
=\mu_{\rm fib}\sum_{i=1}^M\Pr[I_i=1]
\le\min\{M\mu_{\rm fib},\mu_{\rm fib}/p\}.
$$

无需假设当前$c^*(X_i)$与当前试验成功独立。按中心接受质量r/M加权：

- r=0：无fork成本。
- r=1：第一阶段必耗尽cap，贡献≤$\mu_{\rm fib}$，无第二阶段。
- r=2：第一阶段贡献≤$2\mu_{\rm fib}$；第二阶段至多再付$2\mu_{\rm fib}$。
- r≥3：两阶段合计≤$[r/(r-1)+r/(r-2)]\mu_{\rm fib}\le(9/2)\mu_{\rm fib}$。

第二阶段所排除点的身份改变，但成功数仍为r−2，且增广$c^*$未变；因此第一个成功点与其成本相关不破坏此界。平均所有fiber、随机带及真实prefix，再加第一次中心调用，得

$$
Q_3=1+\frac92k.
$$

中心的k次挑战抽样、有限局部代数和证书序列化可单列基础开销；指数上限M的循环不得整体当作一次确定性多项式操作。均匀rank采样可用$\lceil\log_2M\rceil$位拒绝抽样，接受率>1/2，随后组合数unrank；其已知多项式期望比特成本也须计入逐trial。整个算法最终采用一次全局截断，包含这些随机采样费用。

### D.4 子kernel必须作为成功吸收

若oracle另可返回kernel，构造分析用耦合oracle：同一带上把kernel暂当失败并继续。令真实中心的record、kernel质量分别为$p_r,p_z$。耦合sampler完成star的概率≥$p_r-2k/M$。这些record中心运行在真实算法中要么同样完成，要么更早遇fork kernel而成功；另有互斥的中心kernel质量$p_z$。因此

$$
\Pr[\text{raw record or kernel}]\ge p_r+p_z-2k/M.
$$

真实算法早停只减少耦合成本，故Q3不变。不能把kernel算作子失败后再直接使用这个成功率递推。

## E. 独立试验Gate的完整概率与记录合同

设固定σ下算法O返回失败、核或candidate，非失败质量$s_0$，平均完整成本µ。Good为可判定谓词，兼容关系为$\sim$。假设：不兼容候选能产生实际指定半径核；每个固定bad候选u的整个兼容类在**未经成功条件化**的raw分布中满足

$$
\Pr[O\text{ returns candidate }v\sim u]\le\theta.
$$

Gate先调用O一次；失败/核原样返回，good候选原样返回。仅首次为bad候选u时，独立重试O直到非失败：核直接返回；不兼容候选产生核；兼容则失败。第二次候选无论为何都不作为返回record。

设首次bad质量b≤$s_0$。若$s_0>0$，重试末次结果的分布是raw的非失败条件分布，因此固定u下兼容候选概率≤$\theta/s_0$。全部新增失败质量≤$b\theta/s_0\le\theta$，得到

$$
\Pr[\operatorname{Gate}(O)\text{ good or kernel}]\ge s_0-\theta.
$$

若$s_0=0$，不进入重试，上式仍成立。这不是把所有bad tuple作并界；每个固定兼容类的小质量通过两次独立试验转化为总损失θ，因而没有乘tuple总数。

重试成本由停止求和给出：第i次试验是否执行只依赖前i−1次结果，独立于本项整次成本$C_i$。故

$$
\mathbb E[\text{重试成本}]
=\sum_{i\ge1}(1-s_0)^{i-1}\mu=\mu/s_0.
$$

首次进入概率为b，所以无条件raw成本≤$\mu+b\mu/s_0\le2\mu$，再加Good判定与一次比较费用。结果与自身成本可以相关；不存在隐含的$1/\varepsilon$无条件因子。

还必须记录更强的支配性。将Gate与它的第一次O调用耦合，对任何**完整记录**集合E逐运行有

$$
\mathbf1\{\operatorname{Gate}(O)\text{返回record于}E\}
\le \mathbf1\{O_{\rm first}\text{返回record于}E\}.
\tag{DOM}
$$

这是因为Gate唯一会返回的candidate是第一次原记录。E可同时约束y、V、消息、证书与suffix；不能仅保持fresh tuple相同，却把第二次试验的中心/后缀换进记录。对确定性后处理h同样有事件支配：取$E=h^{-1}(S)$即可。这正是old gate的根界不被内层重试放大的理由。

## F. Fresh固定坏tuple根界的完整展开

固定任意坏fresh规范tuple$\mathbf W=(W_1,\ldots,W_k)$。这里“固定”只用于证明该兼容类的raw质量，不假设实际提取结果与挑战独立。按固定规则选择一个$f(W_j)\ne0$的j，记$v_a=f_a(W_j)$。令

$$
r=\max\{|a|:v_a\ne0\},\qquad
\nu(a)=\sum_{i=0}^{\ell-1}2^i a_i.
$$

考虑形式多项式

$$
\mathscr H(Z,U)=\sum_a v_a\prod_i(\beta_i+U Z^{2^i})^{a_i}.
$$

它关于U的次数≤r，$U^r$系数为

$$
P_r(Z)=\sum_{|a|=r}v_a Z^{\nu(a)}.
$$

$\nu$在Boolean指数a上单射，至少一个系数非零，所以$P_r$在$R_q[Z]$内非零，且次数≤$2^\ell-1=n'-1$。更高Hamming-weight行系数为零，故不存在它们产生的$U^r$抵消；同weight各项的指数互异，也不能抵消。

由B.1，均匀δ使$P_r(\delta)=0$的概率≤$(n'-1)/M$。其余δ下，$\mathscr H(\delta,U)$是非零、次数≤ell的U多项式，所以独立α使其为零的概率≤ell/M。于是

$$
\Pr_{\delta,\alpha}[\phi_{\beta+\alpha d(\delta)}(W_j)=0]
\le\theta_f:=\frac{n'-1+\ell}{M}.
$$

r=0时多项式本身是固定非零常数，实际根概率为零，仍被该保守界覆盖。raw记录若输出固定$\mathbf W$，由C节实际三点结论必满足上述压缩等式，因此它的质量≤$\theta_f$。F、K可以在规定时刻自适应选择，但根等式中没有这些消息；它们不影响本界。

对raw O_comp应用E节Gate：兼容性只比较normalized fresh tuple；Good_f实际检查所有full-f和固定公开投影。两个不同fresh tuple在第一处差上使用各自弱证书

$$
z=s'Y-sY',\quad \|z\|_\infty\le8TG,
\quad z\bmod q=ss'(W-W')\ne0
$$

产生同A核。fresh gate成功质量≥$p-2k/M-\theta_f$，且返回完整第一次记录。尚未调用旧opening的任何短性来得到这一结论。

## G. 弱opening的整数幂等紧化

此步骤确定性地把full-f转化成真正scalar bits，不增加概率损失。固定一个fresh坐标b。P给u=1，full-f给$b^2=b$于$R_q$。其弱证书为

$$
Y=sb\pmod q,\qquad s\in R_q^\times,
\quad \|Y^{\mathbb Z}\|_\infty\le2G,
\quad \|s^{\mathbb Z}\|_{\rm op}\le2T.
$$

在整数环中形成实际残差

$$
E=Y^{\mathbb Z}(Y^{\mathbb Z}-s^{\mathbb Z}).
$$

模q时$E=s^2(b^2-b)=0$。整数negacyclic乘法每个系数至多包含N项，故

$$
\|E\|_\infty
\le N\|Y^{\mathbb Z}\|_\infty^2
+\|s^{\mathbb Z}\|_{\rm op}\|Y^{\mathbb Z}\|_\infty
\le4NG^2+4TG<q.
$$

E的每个整数系数是q的倍数且绝对值严格小于q，所以E=0于$R$。此处需要的是<q，不必改成未经说明的q/2门槛。

$R$是整环：当N为2的幂，$X^N+1$在$\mathbb Q[X]$不可约。例如$(X+1)^N+1$满足素数2的Eisenstein判据；由单项首系数多项式的商环嵌入相应数域，得到无零因子。故

$$
Y^{\mathbb Z}=0\quad\text{或}\quad Y^{\mathbb Z}=s^{\mathbb Z}.
$$

模q再乘单位$s^{-1}$，得到b=0或b=1。它们是常数环元素，因而是scalar bits。

不能省略整数提升：$R_q$本身可以分裂、有零因子和非平凡幂等元，$b^2=b$单独不能推出b∈{0,1}。也不能在full-f之前使用此引理；压缩关系$\phi_{\beta^*}(W)=0$没有逐个Boolean行有效性的含义。

## H. 完整短tuple重建与old固定坏质量

对fresh gate保留的第一次中心，确定性重建

$$
W_0^{\mathbb Z}=V^{\mathbb Z}-\sum_{j=1}^k y_j^{\mathbb Z}W_j.
$$

每个$W_j$坐标为0/1（u为1），所以逐系数$\|y_jW_j\|_\infty\le1$，并且支持仍小于D。因此

$$
\|W_0^{\mathbb Z}\|_\infty\le G+k,\qquad
\operatorname{Com}(W_0)=C_0,\qquad \deg(W_0)_i<D.
$$

取中心代表只会降低范数。这个短old界是在bits恢复之后得到；先验使用它去完成fresh计算绑定会形成循环。

现在固定一个完整规范tuple$\mathsf U=(W_0,W_1,\ldots,W_k)$，满足$\phi_\beta(W_0)\ne e$。在每个固定δ以及由对手实际选择、已冻结的F下，考虑

$$
D_{\delta,F}(Z)=\phi_{\beta+Zd(\delta)}(W_0)-F(Z).
$$

它次数≤ell，常数$\phi_\beta(W_0)-e\ne0$。因此，无论F如何依赖δ，真实均匀α使它为零的概率≤ell/M。

在其余α下，固定α之后实际选择的K，定义

$$
Q(Y)=\phi_{\beta^*}\!\left(W_0+\sum_jY_jW_j\right)
-F(\alpha)-\sum_jK_jY_j-\sum_{i<j}K_{ij}Y_iY_j.
$$

其常数为$D_{\delta,F}(\alpha)\ne0$，所以Q非零，对各变量次数≤2。B.2给均匀y的根概率≤2k/M。K可以依赖α，但在y之前冻结；它没有常数槽，不能改变这一非零常数。

第一次raw记录经上述确定性重建形成固定$\mathsf U$时，目标opening必须为$V=W_0+\sum_jy_jW_j$，且实际目标等式强制Q(y)=0。因此该事件质量至多

$$
\theta_o=\frac{\ell+2k}{M}.
$$

fresh gate返回第一次完整记录，式(DOM)适用于重建映射的原像；故O_short输出这个固定坏完整tuple的质量仍≤$\theta_o$。内层重试只可能过滤或返回核，不能放大这一record事件。

old gate的兼容关系必须比较完整$\mathsf U$。若只固定W0而允许fresh随y改变，就没有一个固定Q可以使用根界。不同完整tuple的第一处差给同一固定输入承诺的两个opening：fresh bits之差范数≤1；old中心代表之差范数≤2(G+k)。其模q非零性直接来自规范tuple不同。

以Good_o检查$\phi_\beta(W_0)=e$，第二次Gate得到

$$
\Pr[\text{合法old、本批来源及中心suffix，或kernel}]
\ge p-\frac{2k}{M}-\theta_f-\theta_o
=p-\Delta,
$$

$$
\Delta=\frac{n'-1+2\ell+4k}{M},\qquad
B(G)=\max\{8TG,2(G+k),1\}.
$$

当前G≥k、T≥1时B(G)=8TG。所有谓词实际可计算；没有假设外层$\Pi_{\rm joint}$或免费认证来源。

上述对称两 Gate 推导展示原来的有效性链。当前实际算法使用第一部分§6.4及附录 D的融合弱锚点，保留同一个 $\Delta$、核界和首次记录支配；以下组合按该实际算法使用这些接口。

## I. 全历史的条件概率、记录拼接与单一核事件

全部Hk来源、来源次序及公开字段组成不可变输入带I，在第一个挑战前冻结；I可依赖均匀A。所有分叉共享A和I。第t轮后诚实范数$h_t=tk$，逆向目标范数

$$
\Gamma_t=(2H-t)k,\quad \Gamma_H=Hk,\quad
\Gamma_{t-1}=\Gamma_t+k.
$$

该逆向关系包含上一节重建结果。它不表示任意半径$\Gamma_{t-1}$的旧witness正向会缩到$\Gamma_t$；诚实完备性使用另一条h族。

令$\mathsf D_t$为真实前t轮的**无条件**prefix分布，abort是失败状态，不重新抽取直到prefix有效。令$p_t$为从$\mathsf D_t$调用Suffix_t后返回有效record或已验证kernel的概率。终端Suffix_H继续原对手，取得该分支实际输出的候选$W_H$，验证目标关系；它不是额外给定的有效witness oracle。因此$p_H=\varepsilon$，恰为实际终端接受率。

固定任一pre-δ状态σ。真实下一轮继续与Suffix_t构成该σ的目标oracle。局部H节结论给其成功质量至少减$\Delta$；对真实σ分布积分，abort项取零，得到

$$
p_{t-1}\ge p_t-\Delta.
$$

重复H次得到

$$
\Pr[\text{完整来源record或同A核}]\ge\varepsilon-H\Delta.
$$

各层核是吸收成功：立即向外返回，无需再提取祖先witness；否则会错误丢失需归约的概率质量。每层返回record时保留其第一次raw中心suffix，本层重建式保证其W_t正是子suffix的输入opening。故逐层拼接为同一I上的一条匹配中心历史。fork后缀只用于提取和比较，不替换返回的中心链；这条链不必等于另一个预先指定的最终transcript。

genesis承诺为零。若最后规范$W_0\ne0\pmod q$，直接输出其整数代表作为同A核；范数≤$2Hk$。否则它等于零genesis，输出全部来源。统一半径为

$$
B_{\max}=\max\{2Hk,\max_t B(\Gamma_t)\}
=8T(2H-1)k
$$

（H,k≥1、T≥1）。所有分支都给同一个均匀A的真实核；不是每层各自承担一个计算失败事件，因此不需H个MSIS advantage或独立genesis advantage。换成每层独立矩阵会改变归约，本定理未涵盖这种变体。

## J. 完整成本递推及一次截断

当前默认采用 $S_3/W_2$ 融合算法，完整推导见第一部分§6.4、§8及附录 D。互斥坏分支的联合重试费用至多 $\mu_2$，所以

$$
C_{t-1}\le\mathcal R C_t+D_t,\qquad
\mathcal R=Q_3+Q_2=2+13k/2.
$$

局部九块为 $P_3,P_2,A_3,A_2,V_f,B_{\rm bit},O_{\rm old},K_{\rm cmp},R_{\rm out}$，逐trial工作为 $\mathcal R J_t$。第二次前缀、目标校验、实际核比较与本层记录输出均已计入。取已知共同 $B_0$ 逐项覆盖这些费用、终端检查及总初始化/最终处理，则

$$
D_t\le(\mathcal R+9)B_0,\qquad C_H\le B_0,
$$
$$
U_*=B_0\left[1+\mathcal R^H+(\mathcal R+9)
\frac{\mathcal R^H-1}{\mathcal R-1}\right].
$$

这个 $B_0$ 必须由对手预算和明确算法取得，不能用未知平均时间或跑分代替；原对手重放开销归入逐trial J。固定checkpoint的带成本证明再对真实无条件前缀积分，没有将成功条件分布冒充无条件分布。旧双强Gate的 $4Q_3$ 和13块是历史对照，不再作为当前默认时间。

给定$\zeta\in(0,1)$，在$\mathcal T=\lceil U_*/\zeta\rceil$个统一计费步骤处对**整台提取器**截断，超时返回失败。令$G_{\mathcal T},K_{\mathcal T}$分别为截止前good与kernel事件。Markov直接给

$$
\Pr[G_{\mathcal T}\lor K_{\mathcal T}]\ge\varepsilon-H\Delta-\zeta.
$$

构造MSIS攻击者：收到均匀A后按真实setup生成其它公开对象，运行这同一截断算法，只在$K_{\mathcal T}$分支输出已核验核。I可由原对手依赖A选取；其生成成本已经计入。故

$$
\Pr[K_{\mathcal T}]\le\operatorname{Adv}_{\rm MSIS}(q,N,\kappa,m,B_{\max};\mathcal T),
$$

相减得

$$
\Pr[G_{\mathcal T}]\ge\varepsilon-H\Delta
-\operatorname{Adv}_{\rm MSIS}(q,N,\kappa,m,B_{\max};\mathcal T)-\zeta.
$$

这里只扣一次ζ，因为good和kernel共用一个全局截止。先给kernel算法截断，再独立截断witness提取器会导致另一次损失，不能仍引用本式。对子调用分别设截止也需要新分析，当前算法没有这样做。

## K. 渐近表述与具体参数不能混淆

定义参数族时需同时要求：全部表示和本地算法成本多项式；B0为已知多项式；总统计项$H\Delta$可忽略；相应B_max的Module-SIS对PPT困难。完整EPT界为$O(B_0\mathcal R^H)$，所以足够且直接可检验的深度条件是

$$
H\log(2+13k/2)=O(\log\lambda).
$$

固定k允许$H=O(\log\lambda)$。若k随λ多项式增长而H也取Θ(logλ)，则通常只有准多项式界；不能把两个增长条件分别满足后自动合并。

在上述多项式EPT条件下，未截断提取器的kernel概率可忽略：否则存在固定d，使其在无限多个λ上≥$\lambda^{-d}$。取全局截止$2U_*\lambda^d$，Markov损失≤$\lambda^{-d}/2$，得到时间多项式、成功率至少$\lambda^{-d}/2$的MSIS攻击，矛盾。因此未截断EPT提取器的good概率≥$\varepsilon-\operatorname{negl}(\lambda)$。

这一论证没有自动给出“同一个严格PPT提取器以$\varepsilon-\operatorname{negl}$成功”：固定逆多项式ζ造成的截断损失一般不是可忽略量，而取可忽略ζ可能使截止超多项式。论文应分别写EPT渐近结论与带明确ζ、$\mathcal T$的具体严格时间结论。

当前k8/H64给$\mathcal R=54$，$\log_2\mathcal R^{64}\approx368.312800$，完整$\log_2(U_*/B_0)\approx369.442861$。这些是已公开的大归约常数，不能从固定常数在渐近意义上允许，就推出实际可运行或128bit具体安全。攻击估算成本也不是$\operatorname{Adv}_{\rm MSIS}$上界。

## L. 写入论文时必须保留的实现与结论边界

`comparison_bridges.py`实际保留整数分子/slack，构造非零核，检查三点和缺平方槽的代数；其sampler在中心或fork收到kernel时立即返回。`comparison_filters.py`实现独立试验Gate及规范tuple比较。它们的callback不能自行保证远端状态或随机带重放，调用方必须满足本模型合同。

固定重量挑战以均匀rank/unrank隐式实现，不枚举指数M；小环测试中的显式强集合穷举只用于测试。正式论文不应把toy callback包装描述成已完成全深度、真实参数端到端提取实现。

主定理给实际协议的RoK及明确终端opening下的完整在线接受实验。公开终端不提供零知识。最后状态和opening也不使新verifier得知旧挑战是否诚实；当前无离线可转移的简洁历史证书结论。历史输入、通信与终端费用须沿用统一账本，不以本补充的安全归约省略它们。

本补充的有效性依赖为：**三点压缩关系 → full-f检查 → 整数bit紧化 → 短old重建及旧关系检查 → 中心历史拼接 → 同A核吸收 → 一次全局截断**。首次记录任一语义检查失败，才进入对应的独立弱锚点比较，随后终止；不存在依次运行两轮弱锚点的控制流。调整这个顺序需要重新证明相应前提；特别是不能提前使用scalar-bit或短old结论。


---

<a id="appendix-lfplus"></a>

# 附录 B：LatticeFold+ 同来源公式级对照

**版本说明：** 本附录保留原LF+公式级比较；出现的三点提取系数148及相应时间为统一协议归档基线。当前提取器默认系数54、九块局部费用，详见第一部分及附录D；同来源布局、诚实通信及SIS半径未变。

> 公开恢复审计评估补充：这里共同的m806来源也可从公开承诺恢复，故外部RoK路线对照须同时列入更简单的公开恢复控制组。本文接口映射和尺寸公式仍保留，但这个小实例不用于展示复杂来源提取的必要性。见 [公开恢复审计](#appendix-public-recovery)。

来源为 [LatticeFold+](https://eprint.iacr.org/2025/247)，54 页；以下页码从 PDF 第 1 页起。

来源归约另核对 [LatticeFold](https://eprint.iacr.org/2024/257)，PDF pp.43–45、67–69。

**本项对照可以完成“相同来源知识目标、相同明文终端类型”的公式级比较，不能声称两个协议具有相同的中间accumulator关系。** LatticeFold+的实际端点是两个有界线性/MLE关系，Palimpsest的端点是一个有界二次accumulator。把LatticeFold+的≲100KB直接贴到m806实例，或把它当作现成的Palimpsest输出关系提取器，都不合法。

本附录明确构造来源接口映射、列出实际后端链、给出一个可满足原版尺寸条件的保守参考点，并列出原文未提供的精确量。它足以支撑理论论文的适用性与成本取舍定位，不支持“Palimpsest整体更快/更小”的性能结论。

## 1. 固定共同任务与两种终端

共同来源关系取当前小语义核，变量W长度m=806：u、七组51-bit整数及448个metadata bits。f有809条齐次二次行：805条Boolean行、三条规范补数行、一条乘法行。公开关系为

`A0 W=c`，`P W=pub=(1,E,session[4],source[2],sequence)`，`f(W)=0`，

其中A0均匀于R_q^(4×806)，P是同一固定九输出投影；q为当前实际q128素数，R_q=F_q[X]/(X^512+1)。来源有效性要求同一个W满足全部条件；source label仍是标签，不增加所有者签名意义。给定512个冻结来源，目标是从接受的明确终端中提取全部来源的合法W。

| 对象 | Palimpsest | 本附录的LF+路线 |
|---|---|---|
|原始来源关系|上述同一f/P/A0|同一来源关系经等价补零表示|
|每轮fresh来源数|8|8|
|旧状态|一个二次accumulator|两个R_lin,B accumulator|
|每轮处理的总关系数|1 old+8 fresh|2 old+8 fresh，即LF+的L=10|
|最终提供的对象|一个W_H，support<128，系数≤512|两个g_0,g_1，各属R_lin,B，系数绝对值<B|
|终端方式|明文opening并直接检查|明文opening并直接检查|
|最终知识目标|全部512个原始来源W有效|全部512个同一原始来源W有效|

最后一行通过各自的RoK链成立；**两种最终witness不是同一个对象**。LF+原文没有从Palimpsest的具体二次accumulator到其R_lin,B的现成归约。这里比较两条完成同一来源认证目标的路线，不把LF+当作可无缝替换的同类型后端；若坚持中间输入/输出关系逐字相同，还需要新的转换定理，当前不声称已有它。

## 2. 具体来源编译与同opening接口

### 2.1 二次行进入R1CS，不引入另一个来源承诺

令X,Y,E,T,Xbar,Ybar,Ebar为七组bit的线性组合。公开P强制u=1，所以四条算术行等价于

`X+Xbar=p−1`，`Y+Ybar=p−1`，`E+Ebar=p−1`，`XY=E+pT`。

Boolean行是 `b(b−u)=0`。前三条可写成 `u·[X+Xbar−(p−1)u]=0` 等；乘法行用 `X·Y=E+pT`。因此在P的u=1条件下，它们是相同witness上的R1CS行，没有额外乘法中间变量。此处只将原来的 `XY−uE−puT=0` 在u=1子关系上改写，不把该改写用于u不固定的Palimpsest旧accumulator。

LF+ AppendixA pp51–53为一般高范数算术变量使用 `z=G_B^T f` 的digit编码。本来源W本来就是已承诺的bit向量，因此本对照采用其Figure1的**直接有界witness特例**：把实际矩阵A_R,B_R,C_R直接作用于W，不再额外作gadget展开；对应线性矩阵是 `I,A_R,B_R,C_R`。这是该sumcheck恒等式的具体特化，不声称Def.A.1里gadget在所有应用都可删去。

若要机械复核：对固定bounded opening，R1CS检查多项式

`g(t)=eq(r,t)[MLE(A_R W)(t)·MLE(B_R W)(t)−MLE(C_R W)(t)]`

的每个变量次数最多3；最后得到四个同W的MLE声明。Figure1的文字把g标作degree≤2，但由显示公式的eq因子可见应使用degree3这一保守界。后端的same-opening/binding仍由实际LF+RoK负责，不能只拿固定witness的Schwartz–Zippel界冒充完整知识提取。

### 2.2 九个公开字段无需把随机矩阵rank从4冒改成13

对P第j行p_j，构造矩阵 `M_{P,j}=1_n p_j`（每一行都是p_j）。由于 `Σ tensor(r)_i=1`，对任意r都有

`<M_{P,j}W,tensor(r)>=p_j W`。

在R_lin,B中加入这九个线性声明，目标值直接设为已公开pub_j；它们使用**同一承诺和同一opening**。这样 `n_lin=4+9=13`，Ajtai随机矩阵rank仍为κ=4。无须把非均匀矩阵[A;P]当作均匀Module-SIS矩阵，也不增加额外源承诺。fresh阶段的这九个目标值已经包含在公开字段中，不重复发送。

在每次LF+归约之后，13个线性声明随其实际线性组合和MLE点更新；末尾直接检查这13项，不只检查A opening。这保证来源公开字段不会在归约中脱离原始c。

### 2.3 真正的范数与Boolean语义

LF+反向给出的是满足实际系数界 `||W||∞<B` 的输入opening。若P保证u=1且

`N(B−1)^2+(B−1)<q`，

则每个Boolean多项式 `b²−b` 可从模q提升到Z[X]/(X^N+1)中的整数恒等式；该整环只有0和1两个幂等元。因此b是scalar bit。随后补数、乘法及metadata编码使用同一整数无wrap论证，得到与原来源完全一致的语义。参考点B=65536满足这一门槛。

这说明LF+已有的精确range RoK足以承载本来源；它的代价不能在比较时删去。Palimpsest的三点路线则先从弱opening/来源二次式证明有效性，再直接恢复bit。这是可以清楚比较的接口差别。

## 3. LF+实际RoK链及所需假设

为避免与Palimpsest的arity k混淆，以下用a表示LF+分解指数，d表示环degree，d'=d/2，`B=(d')^a`，`ell_d=ceil(log_(d') q)`；L表示总输入关系数。

1. **来源R1CS→R_lin,B。** AppendixA pp51–53，源承诺不变，输出四个MLE声明；加入上节九个确定线性声明后n_lin=13。范围界随witness保留。该附录引用LatticeFold §4；本节进一步核对了其AppendixB.1 pp67–69：提取器运行一次协议、检查目标关系后直接返回同一witness，没有额外star重绕。其具体binding adversary运行时间没有另列。
2. **范围与double commitment。** Constructions4.1/4.4，pp17、22–24：对每个v构造系数分解D_v、monomial矩阵M_v∈R_q^(n×da)、τ_D=split(com(M_v))及m_τ；发送C_M和com(m_τ)。Π_rgchk最终证明实际range，而不是只证明一个有slack的短分子。
3. **commitment transformation。** Construction4.5，pp26–29；Theorem4.3 p30：发送com(h)，用两个独立sumchecks建立double与linear commitment的一致性，得到R_com的真实短opening。
4. **并行输入折叠。** Construction5.2 pp39–40、Theorem5.2：从R_lin,B^L得到一个R_lin,B²。旧accumulator的两个关系与8个fresh关系合计L=10。
5. **精确decomposition。** Construction5.3、Lemma5.1，p40：从R_lin,B²得到两个R_lin,B，零knowledge error。下一轮继续使用这两个关系；终端可直接公开两个opening。

Theorem5.1 p37要求

`Gamma_S · L(d'+1+B+da)≤B²`，

且com为 `(2B²,Sbar−Sbar)`-relaxed binding。由Definition2.3 p13，该binding归约的MSIS半径可保守写成

`beta_SIS,LF=2(2B²)||Sbar−Sbar||op≤8 Gamma_S B²`。

矩阵必须是实际使用宽度n的均匀Ajtai矩阵；不能把我们m806、β520192的estimator记录转贴给这个更宽、更大范数的实例。原文Definition2.2的MSIS假设量化**EPT对手**，不是本项目当前显式PPT截断优势函数；这一差别在提取时间对照中必须保留。

## 4. 真正的尺寸条件：小m不能直接代入论文的大实例表

Construction4.5 p26原版需要

`n≥κ d² a ell_d`。

这是double commitment的系数分解要放进n坐标的空间条件，不是仅供性能优化的偏好。用当前q、d=512、κ4、Gamma_S64、L10：

- a=1给B256，式(28)左侧为 `64·10·1025=656000>B²=65536`，不适用；
- a=2给B65536，式(28)左侧42762880，小于B²=4294967296；
- ell_d=16，原版n门槛为 `4·512²·2·16=33554432=2^25`。

因此**把n直接设为1024并引用原版Theorem5.3不是一个有效数值实例**。Remark4.8 pp29–30的确给小n改造：脚注说n只需略大于κ d a ell_d，本组为65536；但它把原来的两个helper commitments替换为四个，并引入新range/consistency检查。原文没有给这组n≈65536、d512、a2、n_lin13的完整具体总通信及误差表，不能默默仍套原版的每输入5个承诺常数。

这里给一个**保守、非最优的可适用参考点**用于核对公式：n=2^25、d512、κ4、a2、B2^16、L10，挑战Sbar取support<128的固定重量64或72集合。所有非零挑战差是单位。若要求按原文Lemma4.10的简化条件 `|C|=|Sbar|`，可在K=F_(q²)中取恰好这么大的sumcheck采样子集，按照AppendixB pp52–54在 `E=K⊗R_q` 中处理评价。此时环witness和Ajtai commitment仍在R_q，MLE/部分消息在E；不能继续把所有评价当成单个R_q元素编码。

### 4.1 等价补零可以保持原始来源承诺

取均匀扩展矩阵 `A_LF=[A0|A_aux]`，把来源W映到 `v=W||0^(n−806)`；其承诺仍恰为原始c。为防止提取器把非零辅助坐标当成另一种来源opening，需要在关系中真正强制这些坐标为0。

可用明确的range辅助线性约束，而不引入另外的承诺。令D=2B+1，将最多7个padding坐标分为一组，要求

`Σ_(j=0..6) D^j v_j=0`。

在实际 `||v||∞<B` 下，每个整数系数的绝对值小于 `(B−1)(D^7−1)/(D−1)<2^119<q/2`；模q零即整数零，平衡base-D表示唯一，强制每个v_j=0。结合公开u=1，每条线性等式可写成一条R1CS行。约束总数为 `809+ceil((n−806)/7)=4794185<n`，所以补零到n行即可。此步骤只建立参考点的等价表示；不是本篇拟主张的新编译贡献。

原版参考点的均匀CRS是 `4·2^25·512·16=2^40 bytes`，两个终端opening在17bit系数编码下为73014444032bytes。这两个大数反映**原版padding参考点**，不能代表LF+最优实现；必须同时展示Remark4.8可以减少宽度这一事实。本文不据此声称Palimpsest优于LF+。

## 5. 逐层通信：哪些能精确计数，哪些只能引用主导项

| 阶段 | 原文定位 | 可靠可列对象 | 本项不能省略或冒称精确的项 |
|---|---|---|---|
|输入|Def3.1 p15；App.A p51|8个fresh原始A0 commitments与同一pub；2个旧acc状态已存储|fresh commitments、CRS均不属于内部fold proof；完整比较仍要另列|
|来源线性化|Fig1 p53|每fresh一个degree3、log n轮sumcheck和4个MLE评价；P九项值已公开|challenge、sumcheck coefficients和评价在C/K/E中的实际编码；不能只保留后续linear fold|
|原版range辅助|Const5.1 pp38–39；Const4.4 pp23–24|每输入C_M、com(m_τ)，共2L个新Ajtai commitments；monomial检查输出da+1个ring/扩展ring评价，range步骤还有d+1个field值|并行batch可以共用sumcheck，但不自动删除被检查的不同列；完整矩阵M_v不发送|
|原版transformation|Const4.5 pp26–28|每输入com(h)，共L个新commitments；3+da个Sbar挑战；两个独立sumchecks与终端评价|额外n_lin线性声明的评价成本必须保留；n_lin=13不是原文示例4|
|压缩评价的可选优化|Remark4.7 pp28–29|每输入另加com(τ_e)、com(exp(τ_e))，即2L个commitments；用2da field评价等替换da个full-ring评价；另加两个fold挑战|这是通信交换，不能只减da ring而忘新增commitments/range/consistency|
|decomposition|Const5.3 p40|两个新commitments及两组线性评价；依协议原样发送为2κ个R_q元素、4n_lin个E元素|是否通过验证等式省发某一项属于进一步编码优化，本对照不预先计入|
|最终终端|两R_lin,B的直接checker|两个实际短opening，逐项检查A_LF与13个线性评价|它不是p43中的fold proof size；未加SNARK，故不得省略|

无小n改造时，原版新helper commitments是3L个；采用Remark4.7后是5L个，再加decomposition的两个。L10对应30或50个helper commitments，以及两个decomposition commitments。**这些是承诺数量，不是总通信。** Palimpsest没有这类新helper commitment，但发送F/K；不能仅凭“0对50”宣布总成本优势。

Theorem5.3 p41给采用Remark4.6/4.7后的**主导项**：

`L(5κ+6)+10` 个R_q元素，

`L(da+5)` 个Sbar元素，

`L(2da+d+1)` 个C元素。

在参考点分别是270、10290、25610。原文用的是“dominated by”，不是完整逐byte账本。尤其本对照用n_lin13、扩展域K及可能的小n优化；其field评价未必属于受限采样子集C，实际消息应按ambient K/E编码。不能简单把270乘8192再加两个challenge编码就当成完整对照总通信，也不能把论文d64、L3、n2^21的≲100KB当成这里的答案。

LF+公布的运算主导量（Theorem5.3）：prover约 `Lnκ` 次R_q乘法及 `O(Lnκda)` 次R_q加法；verifier（不含hash）约 `O(Lda)` 次R_q运算。它们用于解释机制，未给本n_lin13实例的全部低阶项或实际时延。R1CS来源归约另有稀疏矩阵运算和degree3 sumcheck；终端另需两次矩阵opening检查。

## 6. 提取误差与时间：引用实际定理，不用一个抽象Pi替代

令h=log2 n，s=|Sbar|，c=|C|，记ε_bind为LF+定义的实际relaxed-binding错误。原文对未加Remark4.7的核心给：

- Lemma4.4 p20：`epsilon_mon,m=(2d+m+4h)/c+epsilon_bind`；
- Lemma4.5 pp21–22：`epsilon'_rg=epsilon_mon,1+epsilon_bind+h/c`；
- Lemma4.7 p24：`epsilon_rg=epsilon_mon,da+1+epsilon_bind+h/c`；
- Lemma4.10 p31：μ=3+da，`epsilon_sum=(2h/c)^2`，在s=c时

`epsilon_cm,a=(μ+da)/s+3 epsilon_bind+epsilon'_rg+epsilon_rg+2 epsilon_sum+μ[(log2 κ)^2+(2h)^2]/c`；

- Theorem5.2 p40：`epsilon_mlin≤L epsilon_cm,a`；
- Lemma5.1 p40：decomposition错误为0。

参考点h25、d512、a2、κ4给μ1027，从显示公式得

`epsilon_cm=2576983/M+5000/M²+7 epsilon_bind`。

L10、H64时，仅上述cm的线性统计项为 `64·10·2576983/M`：固定weight64时约2^-157.5523，weight72时约2^-164.1171。**这不是完整来源历史的总错误**：来源R1CS→linear的知识误差、可选Remark4.7/4.8新增检查，以及实际binding归约成功率与运行时间都尚须加上。weight64这个原版等集大小实例的显示统计上界达不到2^-160；可调challenge/field或用weight72等方式留余量，不能写LF+“不支持”该安全目标。

对固定witness，来源R1CS的随机行压缩加degree3 sumcheck可给 `4h/c` 的统计检验界；但完整知识可靠性还要固定同一个opening。LF+ AppendixA引用的LatticeFold Lemma4.1及AppendixB.1（PDF pp45、67–69）给出实际identity extractor，原文统计显示界是 `(2b+1)h/c`；在二次情形可取b=2作为覆盖degree3的保守选择，得到5h/c。原证明使用“opening由commitment绑定”来固定多项式，未在这里另外给具体binding优势和运行时间。因此可以将 `epsilon_source` 明确展开为**该实际一次执行归约的统计项≤5h/c，加原文渐近binding例外**，而不能宣称这是已经核准的有限时间Adv界。保守组合形式是

`H[k epsilon_source + L epsilon_cm + epsilon_extra-optimizations]`，

其中k=8，h=25；所有来源的显示统计项合计至多 `64·8·125/M=64000/M`，小于上述cm主项。ε_bind及来源binding例外必须对应实际MSIS归约，不能只保留符号就宣布有限参数计算安全已完成。原版参考路线可令extra-optimizations=0；若使用小n或压缩评价优化，就必须补该项的具体实例化。这里明确披露的是原文未报告的**具体优势/时间损失**，不是以一个未指定的Pi假设替代后端。

### 6.1 原文报告的运行时间粒度

Lemma4.9 p31的坐标star提取器报告μ+1个目标oracle调用的期望界，以及 `<μ|Sbar|` 个调用的最坏界。Lemma4.10 p32将每次oracle调用实现为实际Π_cm执行，并固定末轮双sumcheck点、重采其它随机性。对L个并行输入，p40说fold挑战数乘L；按同一star构造可读出原版完整challenge维数 `μ_L=L(3+da)`，对应 `1+μ_L` 的单次目标oracle调用数量；参考点是10271。

但这不是一个已公布的、与Palimpsest $\mathcal R=148$完全同口径的H层运行时间常数：

1. LF+的定义直接量化EPT对手与EPT MSIS；没有列出H64的已知PPT截断阈值和单个具体Adv函数。
2. 单个oracle还包含更大n、helper矩阵、两个sumchecks以及来源归约；调用数量不是实际计算次数。
3. 可选Remark4.7增加两个fold挑战，Remark4.8改变witness/检查对象；不能保留10271却引用优化通信量。
4. 其发布的组合定理没有提供本参考路线逐层条件成本与单个最终MSIS归约的完整具体常数。不能从“EPT组合”四字擅自给出和当前完整$\mathcal R^H$相同口径的时间优势。

因此可以并列“LF+原文单阶段star调用界”与“Palimpsest完整gate后每层界”，但必须分别命名，不能给一个无条件速度倍率。若需要数值advantage级别的最终公平比较，就必须为LF+路线单独做其具体归约时间审计；在只主张本篇原生RoK定理时，不要求为此重写外部论文的完整安全证明。

## 7. 对当前论文可支持的比较结论

1. LF+能通过具体已知的R1CS/linear/range/transformation/decomposition链承载同一Boolean来源知识目标；它不是“不支持Boolean”，也不是缺少真实后端。
2. 当前m806并非LF+原版double-commitment尺寸条件下的合法直接代入点。需要补零或小n改造，且相应成本必须写出来；这给出了为什么只比较published KB数字不可靠的具体原因。
3. Palimpsest可突出在所限制的scalar-Boolean二次来源上，直接认证来源与tight opening、维持单个二次accumulator、不给fresh添加range/projection helper commitments。其代价是限定关系、显式明文终端、有限深度模型，以及明确的MSIS/提取预算。
4. 不能据保守LF+的1TiB CRS或巨大terminal声称整体性能优胜；这些是为了确保全部原版尺寸前提的参考点，Remark4.8等优化仍可能改变具体费用。
5. 也不能只以source m从990145缩到806为贡献；这里同功能比较固定了同一个f、P、来源数量和明文终端目标。核心区别应落在实际RoK接口与提取证明，而非更换应用后的数字下降。

这条对照完成了投稿主文所需的**具体外部适用性、关系端点差异、公式成本和安全条件**证据。若论文不声称胜过LF+的实际性能，不必为投稿继续建设其全栈实现。精确总通信/统一具体Adv倍率未得到原文直接支持，保持“未报告/不可直接比较”即可，不能编造补齐。


---

<a id="appendix-public-recovery"></a>

# 附录 C：默认来源公开恢复与更强直接基线

日期：2026-10-31。此项经独立理论和成本复核确认。修订对象是默认实例的用途和比较基线；当前协议、一般参数主定理和 统一协议/arity 研究 冻结数值保持不变。

**结论：默认 m806 来源可从公开矩阵与承诺通过域上线性代数恢复。** 原材料已识别常数坐标展开的满列秩，却只讨论了其对某类 SIS 核攻击的影响，遗漏了来源公开可解码的后果。默认实例应明确定位为算术编译、编码和成本账本的可审查示例，不能用来证明复杂格知识提取机制对该小应用是必需的。

## 1. 公开系数矩阵为什么真正均匀

令 $A\leftarrow R_q^{\kappa\times m}$，$R_q=\mathbb F_q[X]/(X^N+1)$，并写

$$
A_{ij}(X)=\sum_{r=0}^{N-1}a_{ijr}X^r.
$$

对 scalar 来源 $W=(w_1,\ldots,w_m)\in\mathbb F_q^m$，乘法没有系数旋转：

$$
(AW)_{i,r}=\sum_{j=1}^m a_{ijr}w_j.
$$

将 $(i,r)$ 作为行索引，定义 $\widetilde A_{(i,r),j}=a_{ijr}$，则

$$
\operatorname{vec}(AW)=\widetilde A W,\qquad
\widetilde A\leftarrow\mathbb F_q^{n_A\times m},\quad n_A=\kappa N.
$$

所有 $a_{ijr}$ 原本独立均匀，因此这个 **2048×806** 矩阵确实是独立均匀标量矩阵。它不是将任意 $R_q^m$ opening 展平后的 **2048×412672** 结构矩阵；后者含 negacyclic 旋转关联。两个判断并不矛盾。

当前 $n_A=4\cdot512=2048$、$m=806$，而合法来源 $W\in\{0,1\}^{806}$ 恰在该标量子空间中。$u=1$ 也是其中一个固定 bit。

## 2. 满列秩概率与公开恢复命题

**命题（默认来源可公开线性恢复）。** 设 $n_A\ge m$。除概率

$$
\epsilon_{\rm rank}=1-\prod_{j=0}^{m-1}(1-q^{j-n_A})
<\frac{q^{-(n_A-m+1)}}{1-1/q}
\tag{PR1}
$$

的 setup 事件外，存在可由公开 $A$ 在多项式时间预处理得到的线性左逆，使每个来源承诺的标量候选可公开唯一恢复。随后检查完整来源关系即可判定该承诺是否存在合法 scalar-bit 来源 opening。

**秩概率证明。** 依次观察矩阵各列。在前 $j$ 列独立的条件下，其张成空间有 $q^j$ 个向量，下一个均匀列属于该空间的概率为 $q^{j-n_A}$。相乘得到满列秩概率。使用 $1-\prod_j(1-x_j)\le\sum_jx_j$，

$$
\epsilon_{\rm rank}
\le\sum_{j=0}^{m-1}q^{j-n_A}
=q^{-(n_A-m+1)}\frac{1-q^{-m}}{1-q^{-1}}
<\frac{q^{-(n_A-m+1)}}{1-q^{-1}}.
$$

默认指数为 $2048-806+1=1243$。代入实际 $q$，该上界约为

$$
2^{-157861.004107}.
$$

这是对同一个 setup 矩阵的事件。一旦满列秩，它同时适用于所有标量候选、所有512个来源，以及看过 $A$ 后才选择来源的对手；**不额外乘512**。不需要来源独立于 $A$。

## 3. 一次预处理和逐来源算法

通过消元找出 $m$ 个原矩阵行，组成可逆子矩阵 $B\in\mathbb F_q^{m\times m}$。设 $E_S$ 选择这些行，则 $B=E_S\widetilde A$，定义

$$
L=B^{-1}E_S,\qquad L\widetilde A=I_m.
$$

可仅存行索引和 $B^{-1}$，不必存完整 $m\times n_A$ 左逆。

```text
PublicPreprocess(A):
    form the scalar coefficient matrix A_tilde
    find m independent original rows S
    if rank < m: report that this recovery route is unavailable
    store S and inverse(A_tilde[S,:])

RecoverAndCheckSource(C=(c,pub)):
    decode and validate the claimed public fields
    v = vec(c)
    W_hat = inverse(A_tilde[S,:]) * v[S]
    if A_tilde * W_hat != v: reject
    if u != 1 or any coordinate is not a scalar bit: reject
    if P * W_hat != pub: reject
    if f(W_hat) != 0: reject
    return W_hat
```

全像检查 $\widetilde A\widehat W=v$ 不可省略。可逆方形子系统对每个右端都有解；恶意承诺可能仅与选中行一致而在其余行不一致。

在满列秩 setup 上，该算法精确判定来源有效性：若有合法来源，左逆恢复的就是它；若通过全部检查，返回向量就是定义要求的 witness。若秩亏，可以显式回退到发送 opening 后直接检查的控制路线。本修订不将主协议的 Setup 改成“重采直到满秩”，也不改变原 Module-SIS 矩阵分布。

该算法只恢复合法来源所要求的标量候选。它没有声称同一承诺不存在其他非标量环 opening；累积 opening 本来就允许非标量系数。

## 4. 通信、预处理、逐来源运算和存储

采用一个透明、保守的全806列直算路线，所有运算数均以 $\mathbb F_q$ 的标量运算为单位，不是环运算，不是实测时延。

### 4.1 一次预处理

对 $n_A\times m$ 系数矩阵选主元行，再求 $B^{-1}$，标准稠密消元成本为

$$
O(n_A m^2+m^3)=O(n_A m^2)
$$

域运算，另有求逆操作或相应域运算实现。默认 $n_A m^2=1,330,454,528$ 是量级参考，**不是已测量或逐操作精确计数**。该开销可在复用同一 $A$ 的来源/会话间摊销。

一个可明确计数的实现选择是对 $[\widetilde A^{\mathsf T}\mid I_m]$ 做整行 Gauss–Jordan。扫描前 $n_A$ 列选出 $m$ 个主元列，记录原行号；若行变换为 $E$，则 $EB^{\mathsf T}=I_m$，右侧得到 $E$，从而 $B^{-1}=E^{\mathsf T}$。每次将一个主元行归一化并对其余 $m-1$ 行更新全部 $n_A+m$ 个位置，给出保守上界：

$$
m^2(n_A+m)=1,854,061,144\quad\text{次域乘},
$$
$$
m(m-1)(n_A+m)=1,851,760,820\quad\text{次域减},
$$

另有806次域求逆、主元搜索和行交换。域求逆不等于一次域乘。此整行算法的理论账本不是轻量测试脚本所用“先选行、再对方阵求逆”实现的实测指令计数。

原 CRS 已有26,411,008bytes。按每域元素16bytes保留 $B^{-1}$ 需10,394,176bytes，806个 uint16 行索引需1,612bytes，额外持久预处理状态合计 **10,395,788bytes**。消元临时缓冲另计；不把该持久状态数字当峰值 RAM。若选择存完整左逆，则另需26,411,008bytes；当前保守路线不必这么做。

### 4.2 逐来源直算

| 项目 | 域乘法上界 | 域加法上界 |
|---|---:|---:|
| 从主元行恢复 $\widehat W$ | $m^2=649636$ | $m(m-1)=648830$ |
| 全2048行回代检查 | $n_A m=1650688$ | $n_A(m-1)=1648640$ |
| 合计 | **2300324** | **2297470** |

512个来源的恢复与全像检查共计1,177,765,888次域乘法，另计预处理、解码和完整来源检查。恢复后的 witness 为标量，Boolean、P和f检查可在 $\mathbb F_q$ 或已验证范围的整数上直接进行，不需要将它们当作一般512系数环向量求值。已为0/1的系数参与 $\widetilde A\widehat W$ 回代时也可以用选列求和减少乘法；上表仍保留通用稠密回代上界。预验证逆矩阵正确后可省去主元行的重复回代，但不将这些未实现优化包装为实测性能。

若将 P 的500个标量项、七个51-bit线性形式及 $xy,ph$ 也用未优化域乘求值，语义检查额外至多 $500+7\cdot51+2=859$ 次域乘/源；这是允许重复计算 E 的保守计数。805个 bit-membership 检查和 $u=1$ 已保证全部 Boolean 行有效，其余算术只需三个补数等式和乘法式。故按上述整行预处理算法，一次预处理加512来源的域乘上界为 **3,032,266,840**，另计806次域求逆、所有加减、比较、解析及内存访问。没有把这些数字转换为未实测的秒数。

不能把这些域运算数直接与 Palimpsest 的“每轮197次环乘”相除得出加速比。还需要统一环乘算法、预处理摊销、关系检查、内存访问和实现环境。当前没有证明任何实际时延优势。

### 4.3 同输入带的三条控制路线

保持原来的完整来源 packet 格式、来源数和均匀 CRS；不删除 packet 中可能可推导的公开字段，不主张最优编码。

| 项目 | 公开恢复后检查 | 显式 opening 后检查 | 当前 Palimpsest |
|---|---:|---:|---:|
| 冻结512来源输入带 | 16809472 | 16809472 | 16809472 |
| 额外来源 opening | 0 | 51712 | 0 |
| F/K 消息 | 0 | 0 | 24117248 |
| 公共挑战 | 0 | 0 | 15360 |
| 明文终端 opening | 0 | 0 | 141856 |
| **会话总 bytes，不含 CRS/framing** | **16809472** | **16861184** | **41083936** |
| 验证者预处理 | 系数矩阵选行/求逆 | 无此求逆要求 | 无此求逆要求 |

公开恢复路线比显式 opening 控制组少51,712bytes，比当前 folding 会话少 **24,274,464bytes**。这里“附加证明通信为0”不表示输入带、CRS、计算或存储为0。此通信数适用于满列秩 setup；如需覆盖秩亏 setup 的完整实现，应明确回退方式及其成本。

当前默认实例已经不能将“需要获得来源 opening”作为 folding 相对这条基线的必要性论据。可能的工作分配或在线验证价值，需要单独证明或测量，不能从存在一个 accumulator 推出。

## 5. 扣除公开字段后的实际未知维数

不能只检查 $m>\kappa N$。需区分**线性公开约束**与**利用 Boolean 编码解释后直接知道的坐标**。

1. 只在 $\mathbb F_q^m$ 上把当前 P 当线性矩阵，它有9个独立行，仿射解空间维数是 $806-9=797$，不是806。一般地，对固定、公开线性约束 $QW=p$，写 $W=W_0(p)+Uz$，$d=\dim\ker Q$。应考察 $\widetilde A U$ 在剩余 $d$ 维方向上的单射性。若 $U$ 与 $A$ 独立且固定满列秩，则 $\widetilde A U$ 仍是均匀 $n_A\times d$ 矩阵；不能对依赖 $A$ 选择的任意子空间直接照搬这个分布。
2. 对**合法 bit 来源**，公开 E 的规范51-bit表示和448个 metadata bits 都可从公开字段解码；再加 u=1，已有500个坐标被确定，固定位置集合中只剩 **306** 个未知 bit。不是 P 有500个独立线性行，而是利用了 bit 编码和无模别名条件。先从 $v$ 中减去已知列的贡献，再对固定306列求解，就足以恢复合法候选。该子矩阵满列秩坏概率小于 $q^{-1743}/(1-1/q)$。即使公开字段值依赖 $A$，未知列的位置仍固定，因此此秩事件界仍可用。
3. 若再使用实际语义关系，$s_E=p-1-E$ 的51bits也可确定，未知数还可降至255。当前比较表未利用这一进一步优化，也不据此声称优化求解器已经实现。

未来若另选更大来源，应报告剩余仿射维数、公开可解码的 bit 数、$\widetilde A$ 在这些方向上的秩，以及其他语义约束。剩余维数大于 $n_A$ 只排除这一种全空间左逆：域上线性系统不唯一，不意味着有效 Boolean 解有多个，更不自动证明恢复困难或 hiding。不能通过补已知零坐标“增加 m”来解决该问题。

## 6. 对当前主定理和论文定位的影响

公开恢复不是主定理的反例：原文没有 hiding 或零知识主张，一般 m 下的协议与提取证明也未因此失效。但是对默认实例，来源知识本身已能公开获得。论文应主动说明这一点，而不是把“不承诺隐藏性”当作无需讨论其应用后果的理由。

应分别讨论两种接受实验：

- **新的直接检查基线：** 自己恢复候选并检查全部来源；在满列秩 setup 上，这个 checker 的接受蕴含合法来源，且 witness 可直接返回。
- **原 folding 协议：** 其接受事件仍来自原消息和终端关系。只运行公开恢复并不能证明原协议几乎不接受非法来源，也不能自动给出与原中心分支相匹配的历史。这两个关联仍由原安全/组合定理承担。

不增加 $\epsilon_{\rm rank}$ 到原主定理误差式：原提取算法和证明不以“标量系数矩阵满秩”为新前提。秩事件属于新增控制路线的适用条件。也不将公开恢复说成求解一般 Module-SIS：它在这个很窄的标量子空间上求唯一原像，而非输出一般环向量短核。

**更新后的写作定位：** 默认 m806 实例用于核验实际算术编译、同 opening 公开投影、挑战编码、范数条件和完整成本。它不展示来源秘密性，也不展示复杂格知识提取在该实例上的必要性。一般参数的知识归约、真实接受事件到来源/历史的联系与受限深度组合仍按原定理陈述；是否用一个更有代表性的来源规模增强说服力，是后续可选增强，不因此重写当前核心协议或增加生产级实现任务。

可直接使用的英文披露：

> Our compact instance is an auditable example of relation compilation and cost accounting. Since its source coordinates are scalar bits and the coefficient matrix has more rows than columns, source openings are publicly recoverable with overwhelming probability over setup. We therefore include public recovery followed by direct relation checking as a control, and do not use this instance to establish the necessity of cryptographic source extraction.

## 7. 原型核验

公开恢复模块的小矩阵测试覆盖合法恢复、像外承诺、非 bit、错误关系、公开字段不一致和秩亏报告。解方形子系统后仍须回代全部方程，才能判定承诺位于矩阵的像中。

---


<a id="appendix-weak-anchors"></a>

# 附录 D：融合弱锚点与可选随机停止的完整证明

2026-10-31。在统一协议的同一诚实协议、固定来源输入带、共享均匀矩阵、经典重放和明确终端关系上，替换提取器的比较控制流。主默认采用cap=M的强三点/弱两点融合提取；随机停止作为单独标注的可选算法。公开恢复审计公开恢复控制路线继续适用。

## 当前结论与取舍

| 结论 | 证据及允许解释 |
|---|---|
| 默认全层系数148降至54 | 下述强弱耦合、两种坏类根界、互斥分支计费；这是符号递推上界，不是实测加速比 |
| 统计项、SIS半径、诚实通信不变 | cap=M默认仍取 $\Delta=(n'-1+2\ell+4k)/M$、$B_{\max}=8T(2H-1)k$；全部来源关系检查保留 |
| 可选系数约26 | 精确 $\mathcal R_*=2+k[2M/(M-1)+M/(M-2)]$，严格大于26（k8）；统计项改为 $(n'-1+2\ell+5k)/M$ |
| 历史组合保持 | 只返回首次强记录及其原中心后缀，核吸收、同一A归约和一次全局截断不变 |
| 局部实现 | [提取器原型](../prototype/anchor_extractors.py)及其局部测试；实际冻结承诺、目标检查、完整checkpoint重放由callback合同保证，不冒称全深度端到端系统 |

比较工具归属：作者提供的技术笔记 *Bounded openings as independent comparison anchors*，以及CauchyFold附录Lemma 3/4。笔记中的四/三倍系数属于另一套布局，未搬用到此处。这里证明本协议的三点/两点支配、完整tuple核比较与互斥计费。该笔记没有提供公开出版编号，不虚构其正式出版状态。


数学前提仍是第一部分所列强单位差挑战集、整数模数门槛 $q>4NG^2+4TG$、实际目标opening验证、全部来源首次挑战前冻结、同一个均匀 $A$、有限深度和原对手预算。没有因节约计算而将语义有效性替换为假设，也没有把默认来源公开恢复性质隐藏在归约里。

## 数值传播（同一个明确B0计费口径）

新算法的九块为 $P_3,P_2,A_3,A_2,V_f,B_{\rm bit},O_{\rm old},K_{\rm cmp},R_{\rm out}$，另有逐trial $\mathcal R J$。共同已知 $B_0$ 覆盖这些块、终端和总init/output。用

$$
U_*=B_0\left[1+\mathcal R^H+(\mathcal R+9)
\frac{\mathcal R^H-1}{\mathcal R-1}\right]
$$

重算新时间；旧148基线使用其原来的13块并将共同B0取足。比较的是同一保守计费包络下的充分上界，不能将指数差称作可测加速或额外安全位数。

| k / H | 原cap=M两强Gate log2(U/B0) | 新cap=M融合 log2(U/B0) | 可选随机停止融合 log2(U/B0) |
|---:|---:|---:|---:|
|2 / 256|1363.651752|1001.604565|769.777608|
|4 / 128|800.863455|616.586543|488.810915|
|8 / 64|462.472130|369.442861|302.091176|
|16 / 32|263.108679|216.360569|181.743576|
|32 / 16|147.895883|124.462036|106.907870|
|64 / 8|82.408123|70.676069|61.836202|

默认k8/H64：原上界462.472130，新默认369.442861，可选302.091176。统计分子分别为68800、68800、69312；负log2分别约172.101313、172.101313、172.090617。默认 $B_{\max}=520192$，会话通信41,083,936bytes均保持。所有log值是显示近似；精确 Q/R 和统计分子可由 [费用脚本](../scripts/extraction_costs.py)复算。

该表固定原挑战配置，只重算六个 arity 点的提取时间。随机停止也适用于两点 oriented 控制路线，其单 Gate 系数为 $2Q_2^*pprox18$。

## 一、融合弱锚点的完整适配证明

**结论。** 两点star足以作为Palimpsest的独立弱比较锚点。按两个非对称Gate逐层套用，可得到完整子oracle成本系数

$$
Q_3+2Q_2=3+\frac{17k}{2},
$$

k8时为71。进一步保留现有`on_failure`的提前Good检查，将两个互斥失败分支合并计费，严格得到

$$
\boxed{\mathcal R_{\rm cap}=Q_3+Q_2=2+\frac{13k}{2}},
\qquad k=8:\ \mathcal R_{\rm cap}=54.
\tag{WA1}
$$

统计损失保留当前已审查的

$$
\Delta_{\rm cap}=\frac{n'-1+2\ell+4k}{M},
\tag{WA2}
$$

不采用更进一步的max型统计改进。所有kernel半径、前向消息、来源关系、冻结输入、终端和中心历史要求不变。71是一个有效但较松的嵌套计费界；54依赖本文明确的融合early-check控制流，不能只把原成本常数替换为54而不说明算法。

### 1. 固定接口：强S与弱W比较同一输入承诺

沿用整数环$R=\mathbb Z[X]/(X^N+1)$、模环$R_q$、均匀A、固定P及$\operatorname{Com}(U)=(AU,PU)$。固定同一个pre-δ checkpoint σ，其中旧状态、k个完整来源承诺、公开字段、原对手状态及随机带均已冻结。

两个raw程序都从σ重新运行实际$\delta/F/\alpha/K$前缀，然后采中心y并调用同一类目标oracle。目标oracle可返回有效短opening及其suffix、已核验same-A kernel或失败。为最稳妥地沿用既有组合接口，下文让弱程序仍调用同一个已核验目标oracle；它不再对**提取出的来源**建立$\phi_{\beta^*}=0$、full-f或旧状态有效性。弱程序没有递归调用本层fresh/old比较Gate。

同一star内部的目标oracle随机带从同一入口冻结重放。不同完整raw运行的verifier/extractor/suffix币相互独立，原对手的固定随机带保持相同。

#### 1.1 强raw程序S3

S3是当前三点raw：每坐标寻找中心之外的两个不同接受fork，每次搜索cap=M；在同线时返回压缩有效的fresh弱opening，斜率不同时返回半径8TG的真实核。

具体实现可先完成全部坐标的第一fork，再完成全部第二fork；各阶段使用预先指定的独立随机流。本文以此first-phase/second-phase顺序为准。成功candidate、fiber失败界和成本界不变，且两点程序成为成功三点程序的字面第一阶段前缀。candidate含

$$
(y,V,\text{实际消息},\text{首中心suffix},(W_j,s_j,Y_j)_{j=1}^k),
$$

并保证

$$
\operatorname{Com}(W_j)=C_j,\quad
Y_j=s_jW_j\pmod q,\quad
\|Y_j\|_\infty\le2G,\quad
\|s_j\|_{\rm op}\le2T,
\quad s_j\in R_q^\times,
$$

$$
\phi_{\beta^*}(W_j)=0.
$$

设目标oracle的record-or-kernel质量为p，则

$$
\Pr[S_3\ne\bot]\ge p-2k/M,
\qquad Q_3=1+9k/2.
\tag{WA3}
$$

#### 1.2 弱raw程序W2

W2只做两点star：取同分布真实中心y，每坐标寻找一个不同于中心的有效fork，每次搜索cap=M。发生kernel立即返回。完整star返回

$$
W'_j=(s'_j)^{-1}Y'_j\pmod q,
\qquad W'_0=V'-\sum_jy'_jW'_j\pmod q,
\tag{WA4}
$$

及规范的弱分子/slack、中心opening/挑战。其保证是同一固定输入承诺的opening：

$$
\operatorname{Com}(W'_i)=C_i\quad(0\le i\le k),
\quad\|Y'_j\|_\infty\le2G,
\quad\|s'_j\|_{\rm op}\le2T,
\quad s'_j\in R_q^\times.
$$

此时不要求$\phi_{\beta'^*}(W'_j)=0$、$f(W'_j)=0$、scalar bits或短$W'_0$。绝不能在此时直接给弱old套G+k界。

每坐标的两点搜索带成本系数为2：固定fiber中r=1个有效点时中心加权cap成本≤µ；r≥2时≤$r/(r-1)\mu\le2\mu$。包括首次中心调用后

$$
Q_2=1+2k.
\tag{WA5}
$$

这个成本证明允许oracle结果与其成本相关，采样、跳过重复值、重放及验证均逐trial计费；包含kernel的情形按既有吸收耦合处理。虽然W2本身另有两点搜索失败界k/M，本方案**不把它另加进最终统计项**：W2只在比较阶段独立重试至非失败，计费依靠下一节的质量支配。

### 2. 关键条件aS≤sW的逐运行耦合

对固定σ，记

$$
a_3=\Pr[S_3\text{返回candidate}],\qquad
s_2=\Pr[W_2\ne\bot].
$$

要证明的是$a_3\le s_2$，不是S3与W2的总非失败概率之间的比较。S3可能只在第二个fork发现kernel，而W2在其它坐标失败；这种情况不影响所需不等式。

构造仅用于分析的耦合：

1. 两者共享此次raw的δ、α及原对手响应、中心y、目标oracle固定随机带。
2. 为每个坐标j的第一fork预先分配独立随机流$\rho_{j,1}$；第二fork另配$\rho_{j,2}$。
3. S3使用全部流；W2只使用$\rho_{j,1}$，从同一中心排除规则开始，每搜索同样cap=M。

若S3最终返回candidate，它的每一个第一fork搜索都成功；W2在相同第一fork流上会得到相同点与opening，因而返回弱candidate。S3增加的第二fork与同线检查只可能删除candidate或产生kernel，不能产生W2尚未取得的第一fork。因此逐运行有

$$
\mathbf1\{S_3\text{ candidate}\}
\le\mathbf1\{W_2\text{ nonfailure}\},
\quad a_3\le s_2.
\tag{WA6}
$$

每个边际算法都保持原来的独立均匀采样分布。不能把同一串行RNG输出在S3中消费第二fork、在W2中直接消费下一坐标后，就声称第一fork相同；应明确按(j,阶段)分配独立流。无需预先生成无限流，可以使用独立随机带和延迟读取。

**实际运行的anchor必须独立。** 上述耦合仅证明两个边际分布的质量不等式；真正的比较重试重新采独立δ/α/y、fork和suffix币，全部从同一个σ恢复。实际共享强candidate的币会破坏非对称比较的乘积概率式。

任何只保留首次S3候选、其余分支只返回失败/kernel的强程序，都继承candidate质量≤$a_3\le s_2$。这解释了fresh gate之后的强程序也可以使用同一个W2作为anchor。

### 3. 非对称比较引理的适用形式

固定σ，强程序S与弱程序W分别有candidate质量a、弱非失败质量s、完整平均成本$\mu_S,\mu_W$。要求a≤s；实际强/弱运行独立；不同兼容类可构造规定短核；每个固定bad强类u满足

$$
\sigma(u)=\Pr[S\text{返回该类candidate}]\le\theta.
$$

设$\omega(u)$为W返回同类candidate的未经条件化质量。S第一次为bad候选时，独立重试W直到非失败。若为核直接返回；不兼容则构造核；兼容则失败。若S第一次候选本来Good，可以直接原样返回，不做anchor。

当s>0，坏兼容质量为

$$
\sum_{u\text{ bad}}\sigma(u)\frac{\omega(u)}s
\le\theta\frac{\sum_{u\text{ bad}}\omega(u)}s\le\theta.
\tag{WA7}
$$

注意固定坏类界在S上；不要求W建立压缩或语义有效性。若首次bad质量b≤a，则独立停止求和给总anchor成本$b\mu_W/s\le\mu_W$。试验成本允许依赖其自身结果，因为某次W是否执行只依赖之前失败。s=0时a=0，没有重试入口。

所以成功质量≥$\Pr[S\ne\bot]-\theta$，raw成本≤$\mu_S+\mu_W$。所有返回candidate都来自第一次S；不会用anchor记录替换中心或suffix。

### 4. Fresh比较与outer比较的实际核

#### 4.1 Fresh不同：两侧都只需弱证书

强、弱规范fresh tuple不同，取第一个不同j。利用两侧整数分子/slack构造

$$
z=s'_jY_j-s_jY'_j.
$$

同一输入承诺给$Az=0\pmod q$，并且

$$
z\bmod q=s_js'_j(W_j-W'_j)\ne0,
\quad \|z\|_\infty\le8TG.
\tag{WA8}
$$

不要求弱方来源有效或短，不形成所有slack的乘积。P只是同opening的额外固定约束，均匀矩阵仍是A。

#### 4.2 Outer比较：只有fresh相同后才使用短old

强方已经通过full-f并由$q>4NG^2+4TG$恢复全部fresh scalar bits。outer比较先检查fresh：若不同，仍用式(WA8)输出核。若所有fresh相同，弱方规范fresh也恰为这些scalar bits。于是弱方中心给出实际整数提升

$$
(W'_0)^{\mathbb Z}=(V')^{\mathbb Z}-\sum_j(y'_j)^{\mathbb Z}W_j,
$$

具有支持次数<D及范数≤G+k。其中心代表不会更大，并打开同一固定旧承诺。

此时比较强、弱old：不同则整数差是模q非零的A核，范数≤2(G+k)；相同则完整tuple兼容。弱方无须满足旧$\phi_\beta(W'_0)=e$，也无须将其自身的目标φ或full-f作为独立证明输入。

这种按顺序比较是必要的。若先对任意弱old直接相减并套G+k，会使用尚未成立的短界。若仅比较old而忽略fresh，固定完整tuple根界又会失效。

### 5. 固定坏类界仍来自强侧

对首次S3的任何固定坏fresh tuple，三点压缩关系与最大Hamming-weight系数论证给

$$
\theta_f=(n'-1+\ell)/M.
$$

弱W2不满足该压缩关系没有关系；非对称引理只用强分布的$\sigma_f(u)\le\theta_f$。

当强候选full-f有效时，先整数bit紧化，再从其首中心重建短old。对一个固定坏完整tuple$(W_0,W_1,\ldots,W_k)$，其首次S3输出质量至多

$$
\theta_o=(\ell+2k)/M.
$$

证明仍是：F在α之前冻结、$\phi_{\beta+\alpha d}(W_0)-F(\alpha)$有非零常数；排除ell/M的α根后，完整tuple定义的最终y多项式非零，根概率≤2k/M。初次记录的确定性检查/短重建只限制这个事件，不放大其质量。

在普通嵌套非对称Gate版本中，fresh Gate保留第一次S3完整record，故outer强分布同样满足此界；在下面的融合版本中，outer分支直接来自首次S3且fresh已Good，记录支配更为直接。

### 6. 从稳妥71到融合54：必须说明控制流

如果机械地将两个Gate都改成非对称比较引理的always-anchor形式，fresh阶段花$\mu_3+\mu_2$，outer再加一次$\mu_2$，所以$Q_3+2Q_2=71$有效。以相同三点raw充当弱anchor时，相应保守界为$3Q_3=111$。

但当前Palimpsest已有先判断Good、只在失败时比较的接口。保留这一点后，整个单步可写成：

```text
FusedStep(sigma):
    strong = S3(sigma)                       # exactly one first strong raw
    if strong is failure or kernel: return it

    if full_f(strong.fresh) is false:
        weak = independent_repeat_W2_until_nonfailure(sigma)
        if weak is kernel: return it
        if fresh tuples differ: return actual fresh kernel
        return failure

    tighten the strong fresh opening to scalar bits
    reconstruct its short old opening from its FIRST center

    if old_relation(strong.old) is true:
        return the strong record and its FIRST center suffix

    weak = independent_repeat_W2_until_nonfailure(sigma)
    if weak is kernel: return it
    if fresh tuples differ: return actual fresh kernel
    # only now weak fresh = strong scalar bits
    reconstruct/bound weak old by G+k
    if old openings differ: return actual short-old kernel
    return failure
```

所有完整输入承诺和原对手checkpoint均是同一σ；两个重试位置调用同分布W2。full-f通过后的bit紧化是已证确定推论，不出现新的概率过滤误差。

令$b_f$为首次S3候选fresh坏的质量，$b_o$为其fresh好但重建old坏的质量。它们互斥，且

$$
b_f+b_o\le a_3\le s_2.
$$

单次FusedStep至多进入一个anchor重试循环。因此无条件raw成本为

$$
\mu_3+(b_f+b_o)\frac{\mu_2}{s_2}
\le\mu_3+\mu_2.
\tag{WA9}
$$

分别对两种坏类使用式(WA7)，兼容失败质量至多$\theta_f+\theta_o$。于是

$$
\Pr[\text{合法old、全部fresh、首中心suffix，或kernel}]
\ge p-2k/M-\theta_f-\theta_o=p-\Delta_{\rm cap}.
\tag{WA10}
$$

第一三点star产生的核、弱anchor产生的核以及比较核均作为成功吸收；不增加单独collision损失。弱程序的搜索失败不会另扣k/M，因为它被独立重试，且式(WA6)已控制总成本。54结论不要求真实运行中把strong与weak耦合；真实独立性仍是式(WA7)的必要前提。

### 7. 完整记录和逐层组合

返回record的唯一分支是首次S3本身fresh/old均有效的分支。它保留首中心y、V、实际消息以及相连的suffix；两个弱比较分支只能返回核或失败。因而对任意完整record事件E，

$$
\Pr[\operatorname{FusedStep}\text{返回record于}E]
\le\Pr[S_3\text{首次record于}E].
$$

这个性质包含完整sidecar，不只是fresh tuple。弱anchor自身的中心及后缀永不被拼入强历史。

所有来源在首次挑战前冻结、所有层共享同一A时，沿用$\Gamma_t=(2H-t)k$。每层目标范数为G=Γt，重建old满足Γt+k=Γt−1，kernel统一由

$$
B_{\max}=8T(2H-1)k
$$

覆盖，包括非零genesis。以真实无条件前缀定义record-or-kernel质量$p_t$，式(WA10)逐prefix成立，平均后

$$
p_{t-1}\ge p_t-\Delta_{\rm cap},\quad p_H=\varepsilon,
$$

从而总good-or-kernel质量≥$\varepsilon-H\Delta_{\rm cap}$。abort不重采；子kernel立即向外传播。融合算法改变的是提取计算，不改变来源、消息、有效性关系或历史模型。

### 8. 九块本地费用、完整U与具体定理

对固定prefix，将两种raw费用写为

$$
\mu_3\le P_3+Q_3(J+C_t)+A_3,
\qquad
\mu_2\le P_2+Q_2(J+C_t)+A_2.
$$

P3/P2分别为完整pre-δ到pre-y continuation及初始化；J是两种程序逐trial局部开销的共同已知上界；A3/A2为各自有限局部star代数。子Suffix_t的成本为Ct。初次中心的k次采样、重放、核验证和跳过重复值等必须归入实际相应块，不视为免费。

另将strong full-f检查、bit紧化、old重建/判定、anchor比较/核验、record输出分别记为$V_f,B_{\rm bit},O_{\rm old},K_{\rm cmp},R_{\rm out}$。其中$K_{\rm cmp}$支配fresh/full任一互斥比较，包括需要时的弱old短重构和实际核验证；$R_{\rm out}$包括本层record及sidecar序列化。选择新统一B0支配以下**九块**及J：

$$
P_3,P_2,A_3,A_2,V_f,B_{\rm bit},O_{\rm old},K_{\rm cmp},R_{\rm out}.
$$

B0还应覆盖终端continuation/验证，并覆盖初始输入生成与最终genesis/输出处理费用之和。B0按新算法的实际检查工作重新取界，不能直接把旧profile中的示意数当作已测得新常数。

由式(WA9)，

$$
C_{t-1}\le\mathcal R_{\rm cap}C_t+D_t,
$$

$$
D_t=P_3+P_2+\mathcal R_{\rm cap}J+A_3+A_2
+V_f+B_{\rm bit}+O_{\rm old}+K_{\rm cmp}+R_{\rm out}
\le(\mathcal R_{\rm cap}+9)B_0.
\tag{WA11}
$$

这些是无条件期望上界；当某些块只在特定分支执行时，使用其已知界只会更保守。所有prefix平均和cost/outcome相关性按既有带成本fiber及独立停止求和处理。

因此可取

$$
\boxed{U_*=B_0\left[1+\mathcal R_{\rm cap}^H+
(\mathcal R_{\rm cap}+9)
\frac{\mathcal R_{\rm cap}^H-1}{\mathcal R_{\rm cap}-1}\right].}
\tag{WA12}
$$

**定理（融合弱锚点版）。** 在当前Palimpsest全部模型、关系、时序、单位差、模数、固定来源与共享A前提下，以上述FusedStep替代两次强比较提取，原终端接受率为ε。对任意$0<\zeta<1$，令$\mathcal T=\lceil U_*/\zeta\rceil$。整台提取器在此截止前输出全部合法来源及零genesis中心历史的概率至少

$$
\boxed{\varepsilon-
\frac{H(n'-1+2\ell+4k)}M
-\operatorname{Adv}_{\rm MSIS}
(q,N,\kappa,m,8T(2H-1)k;\mathcal T)-\zeta.}
\tag{WA13}
$$

证明仍是good-or-kernel归纳、一次全局Markov截断及同一A的单一MSIS solver。没有另设局部重试截止，没有每层单独ζ，没有每次anchor的额外统计损失。

允许增长的参数族仍需$H\log\mathcal R_{\rm cap}=O(\log\lambda)$、局部成本多项式及总统计项可忽略，才能得到EPT渐近结论。较小常数不自动给任意多项式深度或具体128bit安全。

### 9. Random-stop是独立备选，不与cap=M币规则混用

该部分与另一个独立稿`palimpsest_random_stop_derivation.md`交叉核对；这里给出弱锚点组合所需表达。固定oracle带、fiber有a个有效record点，当前已排除r个不同有效点。每次从剩余M−r点均匀抽样；若是新record则该阶段成功；若失败则以r/M概率停止，否则继续。kernel仍立即吸收。

该阶段单次record概率$u=(a-r)/(M-r)$，成功或停止的总概率为

$$
u+(1-u)r/M=a/M.
$$

对中心接受质量a/M加权，阶段失败质量≤r/M。已排除点后单次平均增广成本至多$M/(M-r)$倍原fiber均值；中心质量恰抵消期望停止时间$M/a$。因此

$$
Q_2^*=1+k\frac M{M-1},\qquad
Q_3^*=1+k\left(\frac M{M-1}+\frac M{M-2}\right).
$$

强三点sampling损失为3k/M。第一fork的排除规则与stop币在强弱边际耦合中完全相同，故candidate支配仍成立；实际anchor保持独立。使用同一融合early-check得到

$$
\boxed{\mathcal R_*=Q_3^*+Q_2^*
=2+k\left(\frac{2M}{M-1}+\frac M{M-2}\right)},
$$

$$
\Delta_*=(n'-1+2\ell+5k)/M.
$$

k8时$\mathcal R_*=26+16/(M-1)+16/(M-2)$，略大于26。使用完整有理数R*代入式(WA11)–(WA13)，九块费用与一次截断规则不变；不能把26当精确乘数。

本节保留cap=M、R54为主推导。random-stop更小的期望系数交换了sampling统计项，留作备选。不能直接把cap=M强S3与random-stop弱W2混用后沿用零slack支配：不同第一fork停止规则可能使强candidate出现时弱程序已失败，需另证质量条件。


## 二、随机停止的独立概率与带成本证明

### 1. 必须按原文执行的随机停止规则

一个完整raw trial从固定pre-delta checkpoint实际产生delta/F/alpha/K，随后固定pre-y状态及原对手和目标子oracle的完整随机带。目标oracle输出已核验record、已核验same-A kernel或失败。其record带真实中心目标opening、公开状态和匹配suffix；每次调用从相同入口恢复。新的挑战抽样和停止币是提取器自己的独立外层币。

先采真正均匀的中心 `y∈C^k` 并调用oracle。中心失败即本trial失败，中心kernel即返回kernel。对某坐标j，当已经排除r个**成功点**时，E只包含中心以及该坐标此前已接受的fork，执行：

```text
RandomStopStage(j, E), where |E|=r:
    repeat:
        x <- exactly uniform from C \ E
        reply <- replay the target oracle at (y_-j, x)
        if reply is a verified kernel: return kernel
        if reply is a valid record: return (x, reply)
        # Only an unsuccessful oracle reply reaches this line.
        independently stop with probability r/M
        if stopped: return failure
```

三点依次需要r=1和r=2；两点只需r=1。**没有cap=M或其它未分析的截断。** 失败查询不加入E；只有真正获得新成功fork时E才增大。不能改成“每次查询前以r/M停止”，也不能把停止币改成成功后才掷，否则以下分布不同。

从 `C\E` 精确均匀抽样可用完整rank提议并拒绝E，也可从 `0..M−r−1` 抽rank后跳过已排除的r个位置。前者有排除拒绝开销，后者有rank映射开销；都必须计入实际费用。停止币可以独立抽 `U←{0,…,M−1}` 后检查 `U<r`。M≥3保证三点阶段的候选集合非空。

### 2. 固定fiber的成功与停止概率

先用CauchyFold原证明的稍一般写法。固定其它坐标，记一次新调用在点x成功的概率为a(x)，fiber平均成功率为

`delta=(1/M) Σ_x a(x)`。

给定选出E的过去，|E|=r。一个保留提议的成功率为

`u_E = [M delta − Σ_(e∈E) a(e)]/(M−r)`。

一次提议结束本阶段的概率为

```text
D_E = u_E +(1−u_E) r/M
    = delta +(r−Σ_(e∈E)a(e))/M
    >= delta.
```

阶段停止而非成功的概率为 `(1−u_E)r/(M D_E)`，阶段提议次数期望为 `1/D_E`。该公式允许调用结果是随机的，但要求新的调用从约定入口恢复，所用oracle分布不随之前失败秘密改变。

在Palimpsest的固定完整子随机带实现中，a(x)是0/1指示函数。E中的r个点都成功，若fiber有a个成功点，则 `delta=a/M`、`u_E=(a−r)/(M−r)`，并且**恰有** `D_E=delta`。不能把“阶段成功率”写成u_E；u_E是每次新提议的成功率，整段阶段成功率是 `u_E/D_E`。

对每个原始中心，后续某阶段被到达的概率至多该中心最初的成功概率a(y)。因此在原始均匀中心分布下，到达质量至多delta。由 `D_E>=delta`，该阶段的停止质量至多 `r/M`。delta=0时没有成功中心，不会进入该阶段。

对坐标和阶段求和，h点star的失败损失至多

`binom(h,2) k/M`。

具体地，三点是3k/M，两点是k/M。CauchyFold Lemma 4正文规定h≥3；此处h=2是其相同r=1证明的直接特例，已独立展开，而不是误引原文的字面适用范围。

对固定的确定接受集，单fiber拥有a个成功点时还可直接核对完整成功率：a<h时为0；a≥h时为

`(a/M) Π_(r=1)^(h−1) [M(a−r)/(a(M−r))]`。

这条公式用于下面的精确枚举；证明的通用损失不依赖独立接受集合或均匀成功成本。

### 3. 不能把oracle调用数量直接乘以无条件平均成本

CauchyFold原文的 `1+(h−1)k` 是oracle调用**次数**的期望界。组合中子Suffix可能是EPT，成本又可以与挑战和成功相关；因此不能直接将该次数乘以一个无条件平均子成本。

一个实际数值反例：M=3，一个成功点，其调用费用为1；另两个失败点的费用各为10。均匀调用平均费用mu=7。两点随机停止在成功中心后只能查询失败点，每次费用10，阶段以1/3概率停止，所以该阶段条件费用30；中心质量1/3，总费用为 `7+10=17`。尽管平均oracle调用次数至多2，`2mu=14`却不足。下面的带成本界给 `2.5mu=17.5`，正确覆盖。

### 4. 带任意成本相关性的fiber加权界

固定fiber及完整子随机带，令c(x)≥0是点x的实际oracle增广成本，包含必要的目标核验、重放等。记均匀平均为 `mu=(1/M)Σ_x c(x)`。先忽略抽样常数，给定E后每次保留提议的平均费用为

`mu_E=(1/(M−r))Σ_(x∉E)c(x) <= [M/(M−r)]mu`。

当前提议的费用可与其成功相关。是否执行第i次提议只依赖前i−1次结果，所以独立新采样与Tonelli给阶段费用

`E[cost | E] = mu_E/D_E <= [M/(M−r)]mu/delta`。

对原始中心和选出E的全部历史积分，到达质量至多delta，故该阶段的无条件增广费用至多

`[M/(M−r)]mu`。

这一点不对成功条件化后的平均成本作无依据假设。均匀中心费用再加一次mu，得

```text
Q2* = 1 + k M/(M−1),
Q3* = 1 + k [ M/(M−1) + M/(M−2) ].
```

对不同坐标大小M_j可逐坐标替换并求和；本文实例所有大小同为M。

#### 4.1 抽样、排除拒绝与停止币的真实费用

若通过从C采样并拒绝E来生成一个保留提议，每次被拒绝的rank也要付出抽样、计数和成员判断费用。可为每个假想完整提议增广一个统一已知费用上界b，覆盖一次rank抽样、一次停止币抽样及固定处理；即使某次被排除、无需调用oracle或无需停止币，也保守计入。于是每个保留提议的平均总费用不超过

`[M/(M−r)] (mu_oracle+b)`。

不能在用了该系数后又把同一排除拒绝开销漏掉，或把原始调用数界当作完整执行时间。直接rank跳过法的费用也可由同一保守包络覆盖。

精确均匀rank的内部bit拒绝采样也须计费：对b-bit提议，若a=M/2^b，则提议次数J和返回rankU满足

`Pr[J=j,U=u]=(1−a)^(j−1)/2^b=Pr[J=j]/M`。

二者独立。canonical `b=ceil(log2 M)` 给期望次数<2；当前Python `randbelow` 用 `M.bit_length()`，M为2幂时有期望恰为2，所以统一可用≤2。把其已知期望增量先积分到c(x)即可。随机时间不是确定最坏常数，但不会新增抽样误差，也不改变Q2*/Q3*。

对完整子随机带逐点证明后再平均；因为挑战集合有限且子算法在相关真实分布下有有限期望，可排除零测度的非终止带。计费最终落在真实原始前缀分布，而不是经过接受条件化的前缀。初始中心k个坐标的抽样、delta/alpha的抽样分别纳入相应center或prefix费用。

### 5. kernel作为吸收成功

固定pre-y状态及子随机带，将输出分为record、kernel、failure，均匀中心质量分别为p_rec、p_ker与其余。分析用一个virtual sampler：将kernel暂记为失败，继续执行上述随机停止规则；record点形成接受集合。

virtual完整star的record质量至少 `p_rec−binom(h,2)k/M`。真实中心为kernel时，真实算法立即成功，质量p_ker；virtual在record中心完成star时，真实算法要么同样完成，要么更早遇到kernel而成功。这两个中心事件互斥，故真实raw的record-or-kernel质量至少

`p_rec+p_ker−binom(h,2)k/M`。

真实算法在kernel处早停，费用不大于同币virtual执行。virtual费用包括kernel调用的实际费用与可能的后续停止币，因此上述加权Q界仍适用。不能把中心kernel当普通失败丢掉，也不能仅把子kernel写成未经核验的“binding failure”标志。

### 6. 强三点与弱两点的prefix coupling

定义弱W和强S使用同一pre-delta接口、同一个实际目标oracle及同一种随机停止机制。弱W在中心和每个坐标的首fork后，返回weak证书：V/y、每个Y_j与s_j、`W_j=s_j^−1Y_j`、原始消息及中心suffix。它检查目标opening和单位/语法条件，**不要求** `phi_beta*(W_j)=0`、full f或scalar-bit性。

推荐如下强S调度：

```text
Phase 1: center, then r=1 stage for every j=1..k
         (exactly the weak sampler W)
Phase 2: r=2 stage for every j=1..k
         compare slopes; on discrepancy return actual kernel
         otherwise return strong candidate and the original center suffix
```

所有搜索始终沿原中心的coordinate fiber进行。前面的概率与费用证明只用“阶段到达质量≤原中心成功质量”，所以这种先完成全部首fork、再完成全部第二fork的调度同样合法。

在同一个初始raw币流与相同原对手/子oracle带上，W是S的字面首阶段。因此：

1. S若返回candidate，则W必返回candidate；两者中心、每坐标首fork、由首fork得到的fresh tuple、消息和中心suffix完全相同。
2. S的第二阶段产生kernel或失败不要求W同样失败；该方向不用于candidate包含。
3. 采用该两阶段调度时，S若在首阶段返回kernel，W也返回该kernel；S在第二阶段返回kernel时W已经有candidate，所以还可得到S非失败蕴含W非失败。

只需要第一条即可推出 `a_S<=a_W<=s_W`，其中a表示candidate质量、s_W含弱kernel质量。若实现仍按“每个j先r1再r2”的顺序，则不能依赖同一顺序RNG游标：须给center及每个(j,r)阶段分配独立索引币带，证明同一candidate包含。不能忽略调度改变带来的随机游标错位。

这是一种**边际实验之间的证明耦合**。在实际非对称重采时，重新运行的W必须从同一pre-delta checkpoint使用独立完整raw币，包括新delta/alpha和子Suffix随机带。不得拿与首次S相关的耦合W直接代替独立重采，否则下一节的概率乘积不成立。单个star内固定子随机带、完整raw之间独立子随机带，仍是两个同时需要的合同。


## 三、实现与复核范围

实现统一采用先完成全部第一fork、再完成第二fork的调度；强弱采样模式必须一致。`sample_rank_star`接受size/unrank隐式挑战域，不枚举M；`sample_excluding`在M-r个rank中均匀抽样后跳过已排除位置。随机停止仅在oracle失败后掷r/M币，失败点不加入排除集。实现分别记录挑战rank、fork、oracle、排除与停止币调用数；uniform integer内部bit拒绝成本另计。

融合函数只返回首次强记录。弱候选非Boolean且fresh不同时，正确构造8TG核；fresh相同时才重构其短old，使用未取模整数差验证核。两个坏分支至多触发一轮重试。dataclass/type检查不能验证kernel；callback调用方必须先核查实际A、非零模q、范数和实际冻结承诺。这些是已列明的实现合同，不能由测试替代。

局部测试覆盖有限强弱分布、成本与输出相关、分支互斥、首记录保留、弱非bit比较、短old整数核、挑战rank映射、两种采样规则、kernel吸收及真实188bit挑战域。独立数学复核另核对随机停止的小域概率和3576个非负成本基向量；复算入口为 `scripts/check_random_stop_costs.py`。均不构成任意对手定理的机器验证或完整实际提取器benchmark。


---

<a id="appendix-two-point"></a>

# 附录 E：两点不放回候选的独立核验与取舍

本附录给出两点、无放回采样、低次数 bit 恢复及 Horner 求值的独立推导，采用本文统一的关系和目标 oracle 接口。

两点无放回路线是已审查的替代定理；系数 18 表示所列计费包络下的理论递推乘数，原型仍执行 R54 基线。

## 1. 核验结论与采用顺序

| 项目 | 核验结论 | 建议与代价 |
|---|---|---|
| A 不放回fiber搜索 | 逐点费用支配成立；两点/三点的加权系数分别为1+k、1+2k，采样损失分别为k/M、2k/M | 与B配套作为推荐定稿路线；必须保存每条fiber的剩余排列，计入数据结构、抽样、清理和空间成本 |
| B 固定坏斜率类界 | 在当前目标关系、强单位差和冻结随机带模型下，固定坏斜率的质量≤2/M；可替换三点压缩不变量 | 最值得纳入主知识定理的改进；原cap=M即可得到R34，与A组合得到R18。必须重新表述raw接口，不能继续保证每个两点候选都压缩有效 |
| C 低次数bit恢复 | 成立；在2D−2<N、s为单位且Y/s满足幂等关系时得到scalar bit | 建议作为当前D128/D256实例的首选短证明，保留整数提升引理覆盖其它支持范围；不据此改变q |
| D 张量Horner与因式分解 | 808、3224、810及4842的通用环乘上界均成立 | 建议写入算法/评估；不是实测时延。mixed特化只用于合法fresh来源，差值在Fq/整数提升中计算 |
| E 进一步缩小根界常数 | 总次数2根界和实际非零行上界可进一步收紧 | 数学上可用，但本节保留更保守统计账本，不为这些小常数增加投稿工作 |

**取舍建议：** 理论稿以A+B的两点不放回版本作为下一次统一定稿的推荐方案；C简化证明，D更新明确算法的成本。B配现有cap采样的34版本是最少新增采样状态的对照。两点不放回18版本需要更多提取器存储，诚实协议消息、来源关系、SIS半径和历史模型均不变。没有必要再并列推广多个默认参数、重跑格估算器或增加完整端到端实现。

这次核验没有进行全领域文献新颖性检索。可以强调本协议中“用固定坏类质量界替代确定性压缩有效性”的作用；不能据此声称一般两点提取方法首创或全局最优。

## 2. A：不放回的逐点带成本证明

固定pre-y状态、其它挑战坐标和**完整**目标oracle随机带。该fiber共有M点，其中a点返回已核验record。先从全部M点均匀取中心；中心失败时停止。对有效中心，按其余M−1点的独立均匀随机排列查询，直到取得t个额外record或耗尽。两点取t=1，三点取t=2。

对任意点x，记额外查询次数为N_x。因为不放回，N_x∈{0,1}。若x为record点，则

$$
\Pr[N_x=1]=\frac{\min\{t,a-1\}}M.
\tag{NR1}
$$

当a−1≥t时，中心为另外record的质量是(a−1)/M，x进入另外record排列的前t名的概率是t/(a−1)；否则其余record均被访问。若x为失败点，则

$$
\Pr[N_x=1]=\frac{\min\{t,a\}}M.
\tag{NR2}
$$

当a−1≥t时，在x与其余a−1个record的相对次序中，x在第t个record之前的概率为t/a，再乘有效中心质量a/M；record不足时穷尽，质量为a/M。这些公式包含a=0等不进入搜索的边界。

令c(x)为该固定oracle带上一次目标调用的任意非负费用，$\mu=M^{-1}\sum_xc(x)$。费用可与结果任意相关。由(NR1)–(NR2)，

$$
\mathbb E\sum_xN_xc(x)\le\frac tM\sum_xc(x)=t\mu.
\tag{NR3}
$$

加中心调用，对各坐标逐fiber平均，得到

$$
Q_2^{\rm nr}=1+k,\qquad Q_3^{\rm nr}=1+2k.
\tag{NR4}
$$

其它坐标失败只会删除本坐标的查询事件，可用“无视其它坐标失败、仍完成本fiber搜索”的潜在执行上界。先按完整oracle带逐点证明再平均，不对被接受或被到达的前缀重新条件化并声称其成本与原分布相同。

### 2.1 成功概率及kernel

当a≥t+1时该fiber终能取得t个fork。否则有效中心质量a/M≤t/M。因此两点raw至少保留目标record质量减k/M，三点减2k/M。

为处理kernel，分析一个将kernel暂记为失败的虚拟oracle；虚拟record事件与真实相同，真实执行可能在更早的kernel处停止并吸收成功。再加原中心的kernel质量，得到相同的record-or-kernel成功界。真实费用不超过包含相应清理计费的虚拟执行包络。

### 2.2 原文需要明确的计费补充

稀疏Fisher–Yates映射可以惰性生成剩余rank的均匀排列，无需枚举M。用平衡树维护交换位置，访问数v≤M时每次查询、更新有O(log(v+1))≤O(log M)次键比较；每个键长O(log M)。均匀rank抽样、unrank、状态重放、验证和数据结构清理都须计入局部开销。

**c(x)只代表固定oracle带上的目标费用；采样管理的费用通常依赖访问历史。** 对后者另取所有合法访问历史上的统一已知包络J，把每次查询及其延后清理摊销都覆盖，再对c(x)+J使用(NR3)。不能直接宣称Python字典每次操作最坏常数，或把无限增长的管理费用藏进旧B0。精确rank内部拒绝抽样的期望费用按原分析积分，不产生新的统计近似。

本层排列状态必须放在目标oracle恢复边界之外：每次恢复的是原对手/子suffix入口，不是复制、回滚或重建不断增长的已访问表。若每次查询都扫描此前全部点，罕见分支的费用可能变成平方量级，前述统一J包络就不成立。也不跨不同坐标共享失败点缓存，因为它们属于不同fiber。

空间至多随访问数线性增长，每个rank条目需O(log M)比特。稀有分支可能访问指数多个点，**未截断算法没有逐分支多项式空间/时间保证**；完整期望分析和一次全局严格截止仍必要。新的共同B0须覆盖这些实际算法费用。

### 2.3 必须跨phase保留同一条排列

三点版本先完成所有坐标的第一fork，再继续各坐标的第二fork，必须继续其原排列并保留已失败点。若phase2重建排列、只排除两个成功点，费用界会失效。

例如M=4，有3个record点，唯一失败点费用1，其余点费用0。第一fork前失败点被查询的无条件质量为1/4；重建排列后第二fork再次查询它的质量为3/8，总费用为5/8，超过2/M=1/2。沿用原排列时，它只被查询一次，质量恰为1/2。

## 3. B：固定坏斜率类为何只需要两个点

固定真实pre-y消息、oracle完整随机带及其它坐标。令g=φ_{β*}，c处返回record的opening为确定向量V(c)，满足实际目标方程

$$
g(V(c))=e^*(y_{-j},c).
$$

协议没有自由Y_j²消息槽，右侧关于c至多一次。固定候选斜率w且g(w)≠0，将record点按截距Z=V(c)−cw分组。组内点满足

$$
h_Z(c)=g(Z+cw)-e^*(y_{-j},c)=0.
\tag{SL1}
$$

因为g齐次二次，h_Z的二次系数为非零g(w)。三个不同挑战若都为根，强单位差条件使三阶Vandermonde可逆，迫使全部系数为零，矛盾。因此每组至多2点；每个有效中心至多有一个不同record fork能产生w。**g(w)无需为单位；非零零因子同样适用。**

设record点数为a≥2，产生w的有向record配对数为E_w，则E_w≤a。虚拟采样中首个有效fork在其它a−1个record中均匀，故不放回两点的固定斜率质量为

$$
\frac{E_w}{M(a-1)}\le\frac a{M(a-1)}\le\frac2M.
\tag{SL2}
$$

原cap=M两点采样中，找到fork的概率至多1，条件于找到的record仍对其它record均匀，因此不增大该界。a<2时无两点candidate。

**kernel的必要处理：** 有kernel点时，真实算法可能在到达某些record前吸收终止。不能直接声称“真实返回record条件下fork均匀”。应在kernel当失败的虚拟采样中证明(SL2)，再用真实candidate事件包含于虚拟candidate事件。这里没有额外扣除kernel概率。

多坐标时，固定整个fresh tuple并按确定规则挑选一个坏坐标j；完整tuple输出事件包含于该坐标的潜在配对事件。每坐标有独立随机流，其他坐标的失败只删除事件，故仍得2/M，**不需将2/M再乘k**。

### 3.1 固定坏fresh tuple的完整根界

对f(W_j)≠0的固定来源，原δ/α最高Hamming-weight系数证明仍给

$$
\Pr[\phi_{\beta+\alpha d(\delta)}(W_j)=0]
\le\theta_f=\frac{n'-1+\ell}M.
$$

在其余前缀上应用(SL2)，得到两点raw的每个固定坏fresh类质量

$$
\theta_f^{(2)}\le\frac{n'-1+\ell+2}M.
\tag{SL3}
$$

这里固定tuple仅用于分析兼容类，没有假设实际提取结果与挑战独立。F可以依赖δ，K可以依赖α；它们分别在α、y之前冻结。缺失平方槽和目标检查不能删除：若允许e*(c)=c²、g(v)=v²且V(c)=c，则两点总返回斜率1，g(1)≠0，固定坏斜率质量为1，直接违反M>2时的2/M界。

## 4. 审查通过的替代单步与组合定理

定义O2为同一pre-δ checkpoint上的完整两点raw：真实δ/F/α/K前缀、均匀中心、每坐标一个有效fork、原目标核验、弱分子Y_j与单位slack s_j以及原中心后缀。它返回失败、同A核，或candidate。**candidate不再承诺φ_{β*}(W_j)=0。**

```text
TwoPointStep(checkpoint):
    first = O2(checkpoint)
    if failure or verified same-A kernel: return it
    if first.fresh fails full-f:
        anchor = independent O2 trials until nonfailure
        return anchor kernel, or fresh comparison kernel, or failure
    derive first.fresh scalar bits
    reconstruct first.old from its original center
    if old relation holds: return the ORIGINAL first record and suffix
    anchor = independent O2 trials until nonfailure
    if anchor is kernel: return it
    compare fresh first; if different: return numerator/slack kernel
    now transfer first's bits to anchor's equal fresh openings
    reconstruct anchor.old from its OWN center
    return short-old difference kernel, or failure if old openings agree
```

原始与anchor使用相同分布、实际独立币，故candidate质量a不超过anchor非失败质量s。两个坏分支互斥，总触发质量b_f+b_o≤a≤s。独立重试的平均费用为μ₂/s，允许当次费用与输出相关，因此总raw费用≤2μ₂。正常返回只能是首次candidate，保留完整中心、实际消息和suffix。

Fresh比较仍用两个整数弱证书构造

$$
z=s'_jY_j-s_jY'_j,
\quad Az=0,\quad z\bmod q\ne0,\quad\|z\|_\infty\le8TG.
$$

Old坏分支先比较fresh；fresh相等时weak继承已证bits，才可由其自己的中心重构范数≤G+k的old。不同old给≤2(G+k)的真实整数核。全部核仍针对同一个均匀A，P是额外固定投影，不把[A;P]误当均匀矩阵。

旧固定坏**完整tuple**的界$\theta_o=(\ell+2k)/M$只需要真实有效中心及消息时序，不依赖三点raw不变量，因此保留。对两种坏类分别应用独立比较求和

$$
\sum_u\sigma(u)\frac{\omega(u)}s\le\theta
$$

并计入两点采样损失，单步得到

$$
\boxed{\Delta_2=\frac{n'-1+2\ell+3k+2}M.}
\tag{NEW1}
$$

当k≥2，它不超过融合提取基线预算；k=1时比旧预算大1/M，不能无条件声称全部arity的误差不变。默认k8/H64时HΔ₂=68416/M，约2^(-172.109388)，原值为68800/M。

### 4.1 两种采样实现的明确时间界

cap=M两点raw取Q₂=1+2k，故$\mathcal R_{\rm cap,2}=2+4k$。不放回两点raw取Q₂=1+k，故

$$
\boxed{\mathcal R_{\rm nr,2}=2+2k.}
\tag{NEW2}
$$

k8时分别为34、18。沿用九块账本，但重新取足各块：两份独立raw的prefix与有限代数各计一次，加full-f、bit恢复、强old重构/检查、任一互斥比较/核验以及本层记录输出；逐trial费用由R·J覆盖。J须满足§2.2的新采样管理包络。

令已知B0支配上述九块、J、终端continuation/检查及总init/output，则

$$
C_{t-1}\le\mathcal R C_t+(\mathcal R+9)B_0,
$$
$$
U_*=B_0\left[1+\mathcal R^H+(\mathcal R+9)
\frac{\mathcal R^H-1}{\mathcal R-1}\right].
\tag{NEW3}
$$

这些是同一个新取足的共同B0下的充分界；局部管理成本可能增加，不能从系数之比直接推导实际加速。

### 4.2 有界深度结论

在原固定来源、共享A、经典完整重放、实际终端接受实验下，采用上述O2和相应采样方式。bit恢复可以使用原整数门槛，也可以在支持条件满足时使用§5引理。保留$\Gamma_t=(2H-t)k$和$B_{\max}=8T(2H-1)k$。若原终端接受率为ε，令$\mathcal T=\lceil U_*/\zeta\rceil$，则提取全部合法来源和与零genesis相连的匹配中心历史的概率至少

$$
\boxed{\varepsilon-
\frac{H(n'-1+2\ell+3k+2)}M
-\operatorname{Adv}_{\rm MSIS}
(q,N,\kappa,m,8T(2H-1)k;\mathcal T)-\zeta.}
\tag{NEW4}
$$

证明接口逐项闭合：单步损失为(NEW1)；任何返回record都是首次中心记录，中心opening等于其子suffix的输入；所有层的核吸收成功，包含可能的非零genesis核。对真实无条件前缀积分后，H层good-or-kernel质量至少ε−HΔ₂；对两分支一起做一次全局截断，再减同A的单一MSIS solver优势，得到(NEW4)。没有每层额外ζ、重复kernel损失或免费终端witness oracle。

渐近EPT仍须局部成本多项式、统计项可忽略、相应MSIS困难，并要求$H\log\mathcal R=O(\log\lambda)$。R18也不提供任意多项式深度或具体128位计算安全。

| 路线（H64） | R | log₂(U*/B0) | 统计分子 |
|---|---:|---:|---:|
| 原两强Gate，13块 |148|462.472130|68800|
| 融合提取基线三点/弱两点cap=M，9块 |54|369.442861|68800|
| 本项两点/两点cap=M，9块 |34|326.801155|68416|
| 不放回三点/两点，9块 |26|302.091176|68800|
| 推荐不放回两点/两点，9块 |18|268.247169|68416|

随机停止的旧“约26”严格大于26；本表不放回三点路线才精确等于26。诚实通信仍为41,083,936bytes、默认核半径520192；默认来源公开恢复现象与其控制路线均保持。

## 5. C：低支持次数的bit恢复

在$R_q=\mathbb F_q[X]/(X^N+1)$中，假设q为素数、s为单位，Y=sb、b²=b，且Y和s在$\mathbb F_q[X]$的代表次数均小于D。若2D−2<N，则

$$
Y(Y-s)=0\pmod{X^N+1},\qquad \deg(Y(Y-s))<N
$$

迫使普通多项式Y(Y−s)本身为零。在整环$\mathbb F_q[X]$中Y=0或Y=s，乘s⁻¹得到b=0或1。没有使用商环为整环这一错误前提。

目标opening的实际support<D保证两点整数差Y的模q代表同样低支持；挑战差s也是如此。Full-f与公开投影u=1给每个坐标b²=b，三项前提都不可省。只有低支持并不能自行证明Boolean性。

默认N512/D128及备选D256分别满足254<512、510<512。故在这些配置下，这个bit恢复步骤不再需要q>4NG²+4TG。仍保留原整数提升引理供更大支持范围使用；来源算术残差、公开字段无别名、挑战单位性、MSIS条件和其它参数约束继续单独检查，不据此降低默认q。

边界反例为$\mathbb F_5[X]/(X^2+1)$中的b=3+4X：b²=b且非常数。取s=1、Y=b、D=2，恰有2D−2=N；结论不成立。s的单位性同样必要，例如s=Y=0无法排除这个非平凡b。

## 6. D：正确的算法计数与mixed特化边界

### 6.1 张量Horner

对按二进制索引排列的关系值，从最低位到最高位收缩

$$
v'_r=v_{2r}+\beta_i v_{2r+1}.
$$

无右孩子时原样传递，不把已知尾部零项重新填回。每次合并减少一个节点，因此809个连续非零候选槽的压缩只需808次通用环乘；对完整2^ell槽为n′−1次。它不要求实际值每项非零，只要求布局已知尾部补零。

将β_i替换为线性多项式β_i+Zd_i，即可生成F(Z)全部系数。第i层右多项式度数≤i，一次合并至多2(i+1)次通用环乘。因此完整槽上界

$$
2\sum_{i=0}^{\ell-1}(i+1)2^{\ell-i-1}
=4n'-2\ell-4=O(n').
$$

当前809槽的每层合并数为404、202、101、51、25、13、6、3、2、1，故保守上界为3224次。另计已有f(W₀)的取得及加法。F常数仍必须等于原e，消息时序与发送的ell个非恒定系数不变。

### 6.2 终端4842是何种计数

对于**任意terminal环witness**，Boolean行可写成b(b−u)，三个范围行是u乘一个线性形式，乘法行为xy−u(E+ph)。故full-f共805+3+2=810次通用环乘；不依赖terminal本身为bits或u=1。

再加张量压缩808次和A检查κm=3224次，得到4842次，替代原透明直算模型的6672次。P的500个非零标量项、七个51-bit命名形式、乘p及其它标量×环运算、加法、解析和CRS访问均另计。不能将所有标量运算抹去后把4842当完整验证指令数或实际时延。

### 6.3 mixed-term公式需限定数据与底域

实际实现的行顺序为range0–2、product3、Boolean4–808，故$\rho_{\rm mul}=\rho_3$，第i个Boolean坐标对应行i+3。对于两个合法scalar fresh来源，

$$
B_{b^2-ub}(W_i,W_j)=2b_ib_j-b_i-b_j
=-\mathbf1_{b_i\ne b_j},
$$

$$
B_{xy-uE-puh}(W_i,W_j)
=x_iy_j+x_jy_i-(E_i+ph_i)-(E_j+ph_j)
=-(x_i-x_j)(y_i-y_j).
$$

于是可用原笔记的加权差异公式计算K_ij。范围极化对合法来源为零；若旧opening是合法来源的诚实线性组合，其范围线性关系也为零。不得据此跳过恶意candidate、未知旧opening或完整terminal关系中的检查。

**差积须在Fq中，或先在整数提升中计算再模q。** 不能把xi−xj先在Fp中规范化后直接代入：取两源(x_i,y_i)=(p−1,p−1)、(x_j,y_j)=(0,0)，原关系给差积(p−1)²，而Fp约化给1，两者作为Fq标量一般不同。公式的化简使用的是xy=E+ph在Fq中的同一个编码等式。

这只减少生成这些消息的算术，仍有O(k²)个显式mixed消息，没有线性通信或准线性high-arity结论。

## 7. 局部算术核验

[局部改进核验脚本](../scripts/check_local_refinements.py)使用精确算术检查以下有限实例：

| 检查 | 数量 |
|---|---:|
| 无放回逐点费用基系数，M3–7 | 320 |
| F5 确定响应函数 / 固定坏斜率 | 880 / 3520 |
| F3×F3 响应映射 / 固定坏斜率 | 648 / 5184 |
| 低次数多项式对 | 17060 |
| 多项式张量收缩 | 132 |

脚本还复算 808、3224、810、4842 的运算账本与各递推系数对应的完整时间公式。以上检查辅助发现局部错误；§2–§4 的一般证明给出任意对手结论。


## 8. 替代定理的使用

采用 R18 时，应同时采用本附录的两点 raw 接口、固定坏类证明、持久无放回采样及完整成本递推。首次候选仍实际检查 full-f，弱旧 opening 只在 fresh 相等后取得短界，返回记录始终来自首次中心。R54 的三点实现保留为独立基线。
