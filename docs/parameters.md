# 参数与成本

完整推导见 [参数账本](../paper/research-notes.md#part-parameters)。默认实例是一份来源对应一次标量 $\mathbb F_p$ 乘法；其评估用途见 [研究范围](scope.md)。

| 参数 | 值 |
|---|---:|
| 环次数 N / 矩阵环行数 κ | 512 / 4 |
| 来源坐标 m / 关系行 n / 补齐 n′ | 806 / 809 / 1024 |
| p | 2251799813685083 |
| q | 170141573107009798923418825414604921797 |
| arity k / 深度 H / 来源数 | 8 / 64 / 512 |
| 挑战支持 D / 重量 s=T | 128 / 64 |
| 挑战集合 M | $2^{64}\binom{128}{64}$ |
| 最大目标 opening 范数 | 1016 |
| SIS 系数无穷范数半径 | 520192 |

q 的整数编码用 128 bits，实际 $\log_2q\approx127.0000033$。$q\bmod1024=965$，乘法阶为 256，故支持次数小于 256 的非零挑战差是单位。素性证书见 [承诺模数](../prototype/data/commitment_prime_certificate.json) 和 [语义模数](../prototype/data/semantic_prime_certificate.json)。

| 明确编码的对象 | Bytes |
|---|---:|
| 均匀 CRS A | 26,411,008 |
| 512 个来源输入带 | 16,809,472 |
| 全部 F/K 消息 | 24,117,248 |
| 全部挑战 | 15,360 |
| 明文终端 opening | 141,856 |
| 完整会话，不含 CRS/framing | **41,083,936** |
| verifier 持久状态 | 196,656 |

持久状态不含 CRS、来源带、witness 或临时 F/K 缓冲。单个挑战采用位置 mask 加符号，24 bytes；终端按每坐标 D 个系数、每系数 11 bits 编码。

| 提取路线 | 全历史统计损失 | $\log_2(U/B_0)$ |
|---|---|---:|
| R54 实现基线 | $68800/M\approx2^{-172.101313}$ | 369.442861 |
| R18 已审查替代 | $68416/M\approx2^{-172.109388}$ | 268.247169 |

以下命令从仓库根运行：

```sh
python -B scripts/extraction_costs.py
python -B scripts/check_local_refinements.py
```

第一条复算已实现提取路线，第二条包含 R18 理论公式和局部改进核验。公开恢复控制路线只发送原输入带 16,809,472 bytes，其预处理及逐来源成本见 [公开恢复推导](../paper/research-notes.md#appendix-public-recovery)。
