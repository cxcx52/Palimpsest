# 提取路线

两条路线使用同一协议、参数和核半径。完整证明分别见 [融合弱锚点](../paper/research-notes.md#appendix-weak-anchors) 与 [两点无放回](../paper/research-notes.md#appendix-two-point)。

| 路线 | 首次记录 / 独立锚点 | 单步统计损失 Δ | 完整乘数 $\mathcal R$ | 状态 |
|---|---|---|---|---|
| 实现基线 | cap=M 三点 / 两点 | $(n'-1+2\ell+4k)/M$ | $2+13k/2$，k8 为 54 | 局部原型 |
| 已审查替代 | 无放回两点 / 两点 | $(n'-1+2\ell+3k+2)/M$ | $2+2k$，k8 为 18 | 证明及有限算术核验 |

首次候选实际检查 full-f，再恢复 scalar bits 和短旧 opening。只有失败分支启动独立弱锚点；两分支互斥。fresh 不同产生半径 $8TG$ 的分子/slack 核；fresh 相同后，旧 opening 差的半径至多 $2(G+k)$。所有正常输出保留首次中心和原后缀。

三点基线逐次建立 fresh 压缩有效性。两点变体改用固定坏类界：沿一个坐标，固定坏斜率将接受点按截距分成至多两点的组，因此单类质量至多 $2/M$；与 δ/α 根界组合后仍足以独立比较。无放回搜索持续保留每条 fiber 的排列，逐点带成本界给 $Q_2=1+k$。

统一范数与期望时间为

$$
\Gamma_t=(2H-t)k,\quad B_{\max}=8T(2H-1)k,
$$
$$
U=B_0\left[1+\mathcal R^H+(\mathcal R+9)
\frac{\mathcal R^H-1}{\mathcal R-1}\right].
$$

对实际终端接受率 ε，一次全局截止 $\mathcal T=\lceil U/\zeta\rceil$ 后，来源及匹配零 genesis 历史的提取概率至少

$$
\varepsilon-H\Delta-
\operatorname{Adv}_{\rm MSIS}(q,N,\kappa,m,B_{\max};\mathcal T)-\zeta.
$$

B0 覆盖九块局部工作、逐次采样/重放/核验、终端及总初始化/输出。渐近 EPT 要求 $H\log\mathcal R=O(\log\lambda)$ 及多项式局部成本。具体实现合同见 [原型](../prototype/anchor_extractors.py)；有限核验见 [局部改进脚本](../scripts/check_local_refinements.py)。
