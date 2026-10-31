# 协议

完整定义与证明见 [研究笔记第一部分](../paper/research-notes.md#part-protocol)。

在 $R_q=\mathbb F_q[X]/(X^N+1)$ 上，使用同一承诺

$$
\operatorname{Com}(W)=(AW,PW),\qquad A\gets R_q^{\kappa\times m}.
$$

A 均匀，P 固定并绑定公开字段。来源关系 $f(W)=0$ 为 Boolean 齐次二次关系，包含 $b_i^2-u b_i=0$，fresh 投影指定 $u=1$。压缩关系为

$$
\phi_\beta(W)=\sum_{a\in\{0,1\}^\ell}\beta^a f_a(W).
$$

全部来源承诺、公开字段、顺序及 genesis 在第一次挑战前冻结。一轮合并旧状态 $(C_0,\beta,e)$ 与 k 个新来源：

1. 验证者采样 δ；证明者发送 $F(Z)=e+\sum_{r=1}^{\ell}F_rZ^r$。
2. 验证者采样 α，设 $\beta^*=\beta+\alpha d(\delta)$，$d_i(\delta)=\delta^{2^i}$。
3. 证明者发送 $K_j,K_{ij}$；验证者随后采样 $y\in\mathcal C^k$。
4. 更新承诺与残差：

$$
C^*=C_0+\sum_j y_j C_j,
\qquad e^*=F(\alpha)+\sum_jK_jy_j+\sum_{i<j}K_{ij}y_i y_j.
$$

诚实 opening 为 $W^*=W_0+\sum_jy_jW_j$。齐次二次展开和 fresh 的 $f(W_j)=0$ 消去平方项，证明 $\phi_{\beta^*}(W^*)=e^*$。F 在 α 前、K 在 y 前冻结；K 没有自由常数或 $y_j^2$ 槽。

终端公开短 opening，并实际检查承诺、压缩关系、系数范数和支持范围。该目标记录及其真实中心后缀是 [提取定理](extraction.md) 的输入。
