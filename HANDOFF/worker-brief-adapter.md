# Worker Brief: constExtend adapter 三个 sorry + provider 机械 fields

你是 shen-work 的执行 worker（opus 4.6）。Master（cron 窗口的紫楠）负责
Picard 链改道设计；你负责下面这些定义清楚、可单文件验证的证明。

启动后先读：
- `UNDERSTANDING.md`（repo 根目录）
- 本文件

## 环境硬规则

- **不许本地 `lake build`**（block_local_lake.sh 会拦；24G mini 全量 build 会 kernel panic）。
- **单文件验证用：`lake env lean <file>` —— 这个本地允许**，repo 的 .lake 缓存齐全。
- 每证完一个 sorry：单文件 `lake env lean` 过了（EXIT 0）才算数，然后 git commit（小步提交）。
- 不许 axiom，不许把 sorry 换成更弱的陈述。证不过去先怀疑定义错（Proof Stuck = Bug）。
- 不要动这些文件（已证完，0 sorry）：
  - ShenWork/Paper2/IntervalLemma31Closure.lean
  - ShenWork/Paper2/IntervalDomainMaxPointSolution.lean
  - ShenWork/Paper2/IntervalDomainSliceMaxDini.lean
  - ShenWork/Paper2/IntervalLemma31Heat.lean
  - ShenWork/Paper2/IntervalDomainLimitSourceRepresentation.lean
  - ShenWork/PDE/ 下除 IntervalDomainContinuousExtension.lean 和 IntervalNeumannFullKernel.lean 以外的所有文件

## Task 1: constExtend_continuous（IntervalDomainContinuousExtension.lean:59）

关键事实：`intervalDomainPoint = Subtype (Set.Icc (0:ℝ) 1)`，而
`intervalDomainConstExtend` 逐点就是 Mathlib 的 `Set.IccExtend zero_le_one f`
（= `f ∘ Set.projIcc 0 1 zero_le_one`，clamp 扩张）。

路线：
1. 先证 bridge lemma：
   ```
   theorem constExtend_eq_IccExtend (f : intervalDomainPoint → ℝ) :
       intervalDomainConstExtend f = Set.IccExtend zero_le_one f
   ```
   funext x，unfold 双方（`Set.IccExtend`、`Set.projIcc`），按 x ≤ 0 / 1 ≤ x /
   中间 三段 case split。projIcc 定义是 `⟨max a (min b x), ...⟩` 形状，注意
   case 对齐用 `min_eq_*`/`max_eq_*` 或 `Subtype.ext` + simp 收。
2. `constExtend_continuous` 改写后直接用 Mathlib 连续性 lemma：
   `Continuous.Icc_extend'`（在 Mathlib.Topology.Order.ProjIcc，名字以
   exact? / loogle 确认，可能是 `Continuous.IccExtend'` 或
   `(continuous_projIcc.comp …)` 形式）。
3. 现有的 sorry 证明骨架（continuous_def / isOpen）整个删掉换成上面两步。

## Task 2: cosineCoeffs_constExtend_eq_lift（同文件 :74）

`cosineCoeffs f n = unitIntervalNeumannCosineCoeff (fun x => (f x : ℂ)) n`
（定义在 ShenWork/PDE/IntervalNeumannFullKernel.lean:83，
unitIntervalNeumannCosineCoeff 在 HeatKernelGradientEstimates，先读它的定义
确认积分形式——应该是 [0,1] 上的（interval）积分）。

ChatGPT R4 给的 API（已验证 Mathlib 确有此 lemma）：
```
intervalIntegral.integral_congr : Set.EqOn f g (Set.uIcc a b) →
    (∫ x in a..b, f x) = ∫ x in a..b, g x
```
EqOn 从 `constExtend_eq_lift_on_Icc`（本文件 :43，已证）来；
uIcc → Icc 用 `Set.uIcc_of_le zero_le_one`：
```
have h' : Set.EqOn F G (Set.uIcc 0 1) := by
  simpa [Set.uIcc_of_le zero_le_one] using h
```
若积分形式是 `∫ x in Icc.. ∂(volume.restrict ...)` 而非 interval integral，
改用 `MeasureTheory.setIntegral_congr_fun`（measurableSet_Icc + EqOn）。
注意被积函数是 ℂ 值（f x : ℂ coercion），EqOn 要 lift 到 ℂ：逐点 congr。

## Task 3: semigroupOperator_constExtend_eq_lift（同文件 :81）

`intervalFullSemigroupOperator t f x = ∫ y, K t x y * f y ∂(intervalMeasure 1)`。
先读 `intervalMeasure` 的定义（应该是 volume.restrict (Icc 0 1) 之类）。
路线：`MeasureTheory.integral_congr_ae`，ae 等式从
`(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ ...)` +
`constExtend_eq_lift_on_Icc` 得到。现有骨架里的 `congr 1; ext y` 是死路
（逐点不等，只 ae 等），删掉重写。

## Task 4: provider 机械 fields（Task 1-3 完成后）

文件 ShenWork/Paper2/IntervalDomainThm11ChiZeroCoreProvider.lean：
- **hLc**: 目标 `Continuous (intervalLogisticSource ...)`（subtype 上），
  从 D.hcont 出发，logistic source 是多项式表达式，组合 continuity lemma。
- **hu₀_bound**: 用 `cosineCoeffs_abs_le_of_continuous_bounded`，
  ContinuousOn 从 subtype Continuous 来（restrict / comp continuous_subtype_val）。

每个 field 单独 commit。改 provider 时只动你负责的 field，
别的 sorry 不要顺手"清理"。

## 汇报

- 进度写 `HANDOFF/worker-status.md`（追加式，带时间戳：哪个 task、
  单文件验证 EXIT 码、commit SHA）。
- 卡住超过 ~40 分钟：把卡点（目标 + 已试 tactic + 错误信息）写进
  status 文件标 BLOCKED，换下一个 task 继续，不要空转。
