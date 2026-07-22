# Recon: "general-N 框架" 在 Shen_work 中的状态

日期: 2026-07-22, by mini cron 窗口 (Xiang 问的)

## 结论

Shen_work 里**没有** general-N（N 物种系统）框架。Fable 起草的是 **general-m**（扩散指数从 m=1 推广到一般 m ≥ 1），不是 N 物种。

## Fable 已有的 general-m 工作

三份 doctrine 文件，全在 `ShenWork/Paper3/`：

| Doctrine | Owner | 目标 | 状态 |
|----------|-------|------|------|
| `DOCTRINE_thm22_fable.md` | Fable#3 | Thm 2.2 general-m (小数据局部稳定) | **HEADLINE CLOSED** 2026-07-16 |
| `DOCTRINE_thm23_fable.md` | Fable#5 | Thm 2.3 general-m (χ₀≤0 全局稳定) | 7 文件计划，尚未开始 |
| `DOCTRINE_thm24_fable.md` | Fable#4 | Thm 2.4 general-m (强 logistic Lyapunov) | **UNCONDITIONAL** 2026-07-16 |

核心改动：`intervalDomain`（硬编码 m=1 flux）→ `intervalDomainM`（paper-faithful u^m 趋化通量），去掉 `hm : p.m = 1` 门。

## 另：N 维 Brouwer

Paper1 有 `BrouwerNDim*.lean` 系列（N 维 Brouwer 不动点定理），但这是拓扑基建（Rothe/Schauder 存在性），不是 N 物种 PDE 框架。

## 如果确实想做 general-N

目前 Shen 论文本身是 2-species (u,v) 系统，没有 N 物种版本。如果爸爸在考虑 N 物种推广，这是新工作，不在现有代码库里。
