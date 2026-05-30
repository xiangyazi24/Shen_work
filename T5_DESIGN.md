# T5_DESIGN — 抛物边界正则性（设计文档，三轮 Phase 1）

> 状态：**设计完成，待爸爸定方向再实现。** 0 代码改动。
> 目标：`hSol` 抛物边界正则性 —— `∂ₜ, ∂ₓ, ∂ₓₓ` 连续/可积一直到空间端点 `x→0⁺,1⁻`。
> 作用：一旦落地，同时 discharge **T4-b 的全部 residual**（C² up-to-boundary / `hLpTime` 链式法则 / `hPDEIntegral` PDE 代入），让 `Eprime ≤ K·E` 变无条件；也是 Paper1 Thm 1.1 gluing 的 closed-slab envelope 前置（T7）。

---

## 0. 起点：正则性谓词**已经定义好了**（关键发现）

`intervalDomainClassicalRegularity T u v`（`ShenWork/PDE/IntervalDomain.lean`）是一个 **9-conjunct** 谓词，已经包含 up-to-boundary 的内容：

| # | conjunct | 内容 |
|---|----------|------|
| 1–2 | sup-norm 单调 | 极大值原理（与 T5 无关） |
| 3 | **内部 C²** | `ContDiffOn ℝ 2 (lift (u t)) (Ioo 0 1)` |
| 4 | 内部时间可微 + `∂ₜ` 时间连续 | per-fixed-`x` 时间 C¹ |
| 5 | `∂ₜ` 场 `(t,x)` 联合连续（开内部 `Ioo×Ioo`） | (D2) envelope 种子 |
| 6 | **端点单边导数 → 0** | `Tendsto (deriv (lift (u t))) (𝓝[Ioi 0] 0) (𝓝 0)` 及 `x=1` |
| **7** | **闭边界 C² + 端点 Neumann 值** | `ContDiffOn ℝ 2 (lift (u t)) (Icc 0 1) ∧ deriv (lift (u t)) 0 = 0 ∧ deriv (lift (u t)) 1 = 0` |
| **8** | **`∂ₜ` 场闭 slab 联合连续** | `ContinuousOn (uncurry ∂ₜ) (Ioo 0 T ×ˢ Icc 0 1)` |
| **9** | **解场闭 slab 联合连续** | `ContinuousOn (uncurry lift u) (Ioo 0 T ×ˢ Icc 0 1)` |

且 `IsPaper2ClassicalSolution.regularity`（`Statements.lean:145`）直接暴露它。

**结论 / 重新定位 T5**：T5 的内容**不是定义正则性**（已定义），而是 **证明一个真构造的解满足 conjunct 7/8/9（以及 6）**。即把这些目前作为 `IsPaper2ClassicalSolution` *假设字段* 携带的正则性，对一个**真构造的解**变成 *被证明的*。

---

## 1. Round 1 — 原子分解（每个数学事实 + Mathlib 状态 + 难度）

构造的解就是 full-kernel Duhamel 不动点
（`intervalFullKernelCoupledDuhamelOperator`, `IntervalFullKernelDuhamelGradEq.lean:39`）：

```
u(t,x) = S_full(t)(lift u₀)(x)  +  ∫₀ᵗ S_full(t−s)(lift F(u(s)))(x) ds
         └──────── A：初值半群 ────────┘   └──────── B：Duhamel 源项 D_t ────────┘
```

其中 `S_full(t)f x = intervalFullSemigroupOperator t f x = ∫₀¹ K_full(t,x,y) f(y) dy`，
`K_full` 是周期化全 Neumann 核（method of images），其谱形式
`K_full(t,x,y) = ∑_{m∈ℤ} e^{−t(mπ)²} cos(mπx)cos(mπy)`（Poisson summation，T2 已证）。

### A. 初值半群 `S_full(t)(lift u₀)` —— **基本已 DONE**

| 原子 | 陈述 | Mathlib / repo | 难度 |
|------|------|----------------|------|
| A1 | 谱热值空间 `C²`（**全 ℝ 上**，故闭 `[0,1]` 平凡） | ✅ `unitIntervalCosineHeatValue_spatial_contDiff_two`（`ContDiff ℝ 2`） | DONE |
| A2 | 端点 Neumann `∂ₓ = 0`（x=0,1） | ✅ `unitIntervalCosineHeatGradientValue_eq_zero_at_{zero,one}`, `unitIntervalCosineHeatValue_deriv_zero_at_endpoint` | DONE |
| A3 | 核↔谱桥（用 A1/A2 的前提） | ✅ `intervalFullSemigroupOperator_eqOn_cosineHeatValue` + `gaussianLatticeSum_poisson_complex` | DONE |
| A4 | conjunct 3 已对半群 profile 放出 | ✅ `intervalFullSemigroupProfile_classicalRegularity_third_conjunct` | DONE（内部）|
| A5 | conjunct 6（端点单边导 →0） | A2 直接给（一侧 = cosine′ = 0） | 近 DONE |
| A6 | `∂ₜ` 逐模时间可微 | ✅ `unitIntervalCosineHeatPointWeight_hasDerivAt_time` | DONE（逐模）|
| A7 | conjunct 9（解场 `(t,x)` 联合连续，闭 slab） | Weierstrass-M 联合可和（`∑ e^{−tλₙ}f̂ₙcos(nπx)` 一致收敛） | ⚠️ 需装配 |
| A8 | conjunct 8（`∂ₜ` 场联合连续，闭 slab） | A6 逐模 + Weierstrass-M（`∑ ∂ₜ(…)` 一致） | ⚠️ 需装配 |

→ **A 块的硬数学（C² + 端点 Neumann）已完成**；剩 A7/A8 是 Weierstrass-M 联合连续的装配（中等，有 `continuousOn_tsum` 模板，T1/T2 用过）。

### B. Duhamel 源项 `D_t = ∫₀ᵗ S_full(t−s)(lift F(u(s)))(x) ds` —— **真正的 gap**

repo 已把它精确命名为单一义务 `DuhamelTermInteriorC2`（`IntervalFullKernelRegularity.lean:261`）。

| 原子 | 陈述 | 工具 / 路线 | 难度 |
|------|------|------------|------|
| B1 | **内部 C²** `DuhamelTermInteriorC2`：C² 空间族的时间积分仍 C² | Mathlib **无** `contDiff_under_integral`；路线 = 对 `x` 在积分号下求导**两次**（`hasDerivAt_integral_of_dominated_loc_of_deriv_le`，T1 已用于 ∂ₓ 一次）+ 核空间二阶光滑界 `∂ₓₓ K_full` window bound | **最难原子** |
| B2 | 闭边界 C²（延伸到 x=0,1） | 全核 `∂ₓK_full` 端点 = 0（构造性 Neumann）→ 端点值受控；B1 + 端点 dominated | 难 |
| B3 | Duhamel 端点 Neumann `∂ₓ D_t = 0`（x=0,1） | 每个 `S_full(t−s)` 端点 `∂ₓ=0`（A2 型逐 slice）+ Leibniz 交换（T2 `intervalFullCoupledDuhamel_grad_leibniz` 已建积分号下求导一次） | 中（积分号下求导一次已有）|
| B4 | 时间正则 `∂ₜ D_t`（变上限 Leibniz + 被积 ∂ₜ + 边界项 `S_full(0)·F`） | 变上限积分求导 `intervalIntegral.deriv_integral…` + `∂ₜ S_full`（核 ∂ₜ = ∂ₓₓ 热方程）| 难 |
| B5 | `D_t`、`∂ₜD_t` 的 `(t,x)` 闭 slab 联合连续（conjunct 8/9 的 Duhamel 半） | 积分号下连续（dominated）+ B1/B4 | 中–难 |
| B6 | 源场 `F(u(s)) = intervalCoupledSource p (u s)(R(u s))` 连续 + 系数有界（喂给 A/B 的前提） | 依赖 `u` 自身正则（不动点 bootstrap）→ **与 T6 不动点循环** | ⚠️ 结构性 |

→ **B 块是 T5 的真硬骨**：B1（最难，二次积分号下求导 + 核二阶界）、B4（变上限时间导）、B2（边界延伸）。B3（端点 Neumann）相对可控——T2 已建积分号下求导一次的机器（`intervalFullCoupledDuhamel_grad_leibniz`），加端点 `∂ₓK_full=0` 即得。

### C. 装配/表示

| 原子 | 陈述 | 状态 |
|------|------|------|
| C1 | 构造解切片 = A + B（定义展开） | 定义直接 |
| C2 | **抽象解 = 半群演化其初值迹**（parabolic 表示定理） | **不存在于 repo，且不存在于 Mathlib**（见 `IntervalDomainJointTimeRegularity.lean` 诚实 gap 报告）|

---

## 2. Round 2 — 定义审查（差距精确化 + lift 端点导数陷阱）

### 2.1 现有 9-conjunct vs "up-to-boundary C^{2,1}" 的精确差距

| 维度 | up-to-boundary C^{2,1} 需要 | 现有 conjunct | 半群部分 | Duhamel 部分 |
|------|------|------|------|------|
| 空间 C²（闭）| `lift u ∈ C²[0,1]` | 7 | ✅ A1 | ⚠️ B2 |
| 端点 Neumann | `∂ₓu(0)=∂ₓu(1)=0` | 6,7 | ✅ A2 | ⚠️ B3 |
| 时间 C¹（闭）| `∂ₜu ∈ C(closed slab)` | 4,8 | ⚠️ A8 | ⚠️ B4,B5 |
| 解场连续（闭）| `u ∈ C(closed slab)` | 9 | ✅ A7(装配) | ⚠️ B5 |
| `∂ₓₓ` 可积到端点 | （hLpTime/hPDEIntegral 需）| 蕴含于 7 | ✅ | ⚠️ B1,B2 |

**净差距 = B 块（Duhamel 项的闭边界 C^{2,1} + Neumann + 联合连续）+ A7/A8 装配 + B6 源场正则。**

### 2.2 lift 端点 ordinary vs one-sided 导数（关键陷阱，T3/T4 已踩过）

- `lift (u t)` 是**零延拓**：`[0,1]` 上 = 真值，外部 = 0 → 端点 `x∈{0,1}` 处一般**不连续**（真值 ≠ 0），故 `deriv (lift) 0`（两边）= Lean junk = 0。
- conjunct 7 写的是 `deriv (lift (u t)) 0 = 0`（**ordinary**，junk-0），T3 的 `intervalDomainNormalDeriv` 是 `derivWithin (Ici 0) 0`（**genuine 单边**）。
- **Neumann 下两者都 = 0**（单边 = cosine′(0) = 0；ordinary 因跳变 = junk 0）—— 一致。这正是 T4-a 用 `_of_hasDeriv_right`（右导数版）绕端点 kink 的原因，T5 须沿用同一约定。
- ⚠️ **设计警戒**：conjunct 7 的 `ContDiffOn ℝ 2 (lift) (Icc 0 1)` 是 *within* `[0,1]`，只看闭区间内值（= 谱值，C²），**不**要求 lift 在 ℝ 上 C²（外部跳变无碍）。证 B2 时必须用 `ContDiffOn … (Icc 0 1)` 而非 `ContDiff ℝ`。

---

## 3. Round 3 — 路径选择（**关键决策点，surface 给爸爸**）

### Path α — 借 full Neumann 核显式正则（**推荐**）

对**构造的** full-kernel Duhamel 解证 T5。A 块基本已完成（谱），集中攻 B1–B5 + A7/A8。

- **优点**：复用全部 T1/T2 基础设施（核连续/梯度/Leibniz/window bounds、Poisson summation、谱热值 C²）；gap 已被 repo 精确命名（`DuhamelTermInteriorC2`）；端点 Neumann 由核构造**自动**满足，不需独立 Schauder。
- **代价**：B1（二次积分号下求导 + `∂ₓₓK_full` window bound）、B4（变上限时间导）是真多步硬证；与 T6 不动点**耦合**（T5 只对构造解成立，B6 源场正则依赖 `u` 的 bootstrap）。
- **可行性**：高。每个原子都有 Mathlib 工具或 repo 先例。

### Path β — parabolic 表示/唯一性定理（抽象解）

证"任意 `IsPaper2ClassicalSolution u v` = 其初值迹的 Neumann 热半群演化"，再套谱正则。

- **优点**：一劳永逸，T5 对**任意** `hsol` 成立，彻底 discharge T4-b residual（无 T6 耦合）。
- **代价**：表示定理 = parabolic 唯一性/最大正则（Henry §3.3 / Amann），**Mathlib 无，repo 无**，自建是又一面深墙，大概率需 textbook-level `sorry`。`IntervalDomainJointTimeRegularity.lean` 已诚实记此为"NOT closed — blocking field"。
- **可行性**：低（在 0-sorry 约束下）。

### Path γ — 经典抛物 Schauder（interior + boundary estimates）

建 Hölder 空间 + Schauder `|u|_{C^{2,1}} ≤ C(|F|_{C^α}+|u₀|_{C^{2,α}})` up to boundary。

- **优点**：教科书标准路线（Shen 原文走这条；Wang 2013 review 背景）。
- **代价**：Mathlib **无** Hölder 空间 / Schauder 理论；从零建是数月级工程，远超 Path α。
- **可行性**：最低。

### 推荐

**Path α**，分阶段：先 B3（端点 Neumann，T2 机器最接近）+ A7/A8（Weierstrass 装配）拿下"边界 + 联合连续"半，再攻 B1（内部 C²，命名 gap）→ B2（闭边界）→ B4/B5（时间）。接受 T5 与 T6 的耦合（T5 本就是 localExistence 构造的正则性子块）。

---

## 4. 需爸爸定夺的问题

1. **路线**：接受 **Path α**（对构造的 full-kernel 解证 T5，与 T6 耦合）？还是坚持 **Path β**（抽象解，需自建 parabolic 表示定理，可能要 textbook `sorry`）？
   - 我的判断：Path α 是 0-sorry 约束下唯一可行的真证路线；Path β/γ 在当前 Mathlib 下不现实。

2. **scope/切分**：B 块是多步。建议**第一个最小 commit** 攻哪个？
   - 选项 (i)：B3（Duhamel 端点 Neumann `∂ₓD_t=0`）—— 最接近现成 T2 Leibniz 机器，快速兑现"边界项真证"。
   - 选项 (ii)：A7/A8（谱解场/∂ₜ 场闭 slab 联合连续）—— 兑现 conjunct 9/8 的半群半，纯 Weierstrass 装配。
   - 选项 (iii)：B1（`DuhamelTermInteriorC2`，命名 gap，最难但最核心）。
   - 我的建议：先 (i)+(ii)（兑现边界 + 联合连续的"已近"部分，巩固 A 块 + B3），再啃 B1/B2/B4。

3. **B6 源场正则 / 不动点循环**：`F(u(s))` 的连续+有界系数依赖 `u` 自身正则。这块算 T5 还是推给 T6（localExistence 不动点 bootstrap 一并处理）？
   - 我的判断：作为 T5 的*假设*（"给定源场 C^α"），把循环留给 T6 的 Schauder/contraction 收尾，保持 T5 = "源场正则 ⟹ 解正则"的单向桥。

4. **交付形态**：T5 落地后，是直接 discharge T4-b 的 8 个 regularity 假设（从 `hsol.regularity` conjunct 7 抽取，做成 `intervalDomain_l2_half_energy_inequality_of_solution` 只吃 `hsol`），还是先把正则性引理独立放出、暂不接 T4-b？
   - 我的建议：T5 每兑现一个 conjunct 就独立 commit；最后做一个"从 `hsol.regularity` 抽取 T4-b 包"的 bridge commit，让 `Eprime≤K·E` 对**构造解**无条件。

---

## 附：相关文件索引

- 正则性谓词：`ShenWork/PDE/IntervalDomain.lean`（`intervalDomainClassicalRegularity`, conjunct 7/8/9）
- 谱正则（A 块，已 DONE）：`ShenWork/PDE/IntervalFullKernelRegularity.lean`, `ShenWork/Paper2/IntervalDomainJointTimeRegularity.lean`
- 命名 gap：`IntervalFullKernelRegularity.lean:261` `DuhamelTermInteriorC2`
- 构造解：`IntervalFullKernelDuhamelGradEq.lean:39` `intervalFullKernelCoupledDuhamelOperator`
- 积分号下求导机器（B1/B3 种子）：`IntervalFullKernelLeibniz.lean`（T2）
- 核谱/Poisson：`IntervalNeumannFullKernel.lean`（T2）
- T4-b 消费端：`ShenWork/Paper2/IntervalDomainNeumannIBP.lean`
- 诚实 gap 报告：`IntervalDomainJointTimeRegularity.lean` 末尾 status note

---

## 5. 实现进度（Path α，自主推进，2026-05-30+）

**空间正则半边（∂ₓ, ∂ₓₓ up-to-boundary）整条 DONE**，对任意被 bounded-coeff cosine
heat value 表示的解切片成立（覆盖齐次半群 + Duhamel 项 + 完整解 S_t u₀ + D_t）：

| commit | 内容 |
|--------|------|
| T5-a | 闭 `[0,1]` C² of 半群 profile（`intervalFullSemigroupProfile_contDiffOn_two_closed`）—— operator=cosineValue 在全 x 成立（`_eq_cosineHeatValue` 的 `hx` unused）→ ContDiff ℝ 2 on ℝ → ContDiffOn.congr |
| T5-b | **无条件** `deriv (lift g) {0,1} = 0`（任意 g）—— 零延拓在外部射线恒 0，单边导=0 + uniqueDiffWithinAt |
| T5-c | up-to-boundary C¹ 连续 `ContinuousOn (deriv (lift g)) (Icc)` —— 内部=deriv S，端点都=0（T5-b + Neumann `_deriv_zero_at_endpoint`） |
| T5-d | 全部 T4-b package：内部 HasDerivWithinAt ×2、deriv/deriv² 区间可积（deriv²=deriv² S a.e. on [0,1]） |
| T5-e | `intervalDomain_spatial_IBP_of_semigroup` —— 真证 hIBP（正则性 DERIVED） |
| T5-f | `intervalDomain_l2_half_energy_inequality_of_semigroup` —— L2 E'≤K·E |
| T5-g | **抽象 C² Neumann profile package**（`IntervalProfileBoundaryRegularity`）+ `intervalDomain_spatial_IBP_of_{profile,cosineProfile}` —— 一招通吃半群/Duhamel/完整解 |
| T5-h | `intervalDomain_l2_half_energy_inequality_of_cosineProfile` —— **完整解** L2 E'≤K·E，conditional on 闭边界 cosine 表示 hrep |
| T5-i | **R3 闭边界升级 DONE**：`eqOn_Icc_of_eqOn_Ioo_of_continuousOn`（密度桥，`Set.EqOn.of_subset_closure`+`closure_Ioo`）+ `intervalDomain_spatial_IBP_of_{profile,cosineProfile}_interior` + `intervalDomain_l2_half_energy_inequality_of_cosineProfile_interior`。能量不等式的最深输入从「闭边界表示 hrep（Icc）」降为「开区间表示（Ioo，= `DuhamelHeatValueRepresentation` 的天然形态）+ conjunct 7 闭 C²」。端点值由连续性免费补出，不再单独假设。|
| T5-j | **R1 hL2Time 归约 DONE**（`IntervalDomainL2HalfEnergyTimeLeibniz`，单解）：`intervalDomain_l2_half_energy_hL2Time_of_slabContinuous` 把 `hL2Time`（`d/dt ½∫u² = ∫u·∂ₜu`）归约到 integrand-deriv 场的闭 slab 联合连续（conjunct 8/9）+ 可测性 side conditions。镜像差能量 `..._hasDerivAt_of_slabContinuous`。关键简化：导数在**时间**方向，lift 的空间端点跳变无关 —— `lift(u r) y = u r⟨y⟩` 对所有 `y∈[0,1]`、所有 `r` 成立，故 deriv 场与 `lift(u·∂ₜu)` 在**整个** [0,1] 逐点相等（无需 a.e.）。|

净效果：`hIBP` frontier 对完整解真证（正则性是真分析内容，不是假设）；L2 能量不等式
对完整解成立，只剩诚实 frontier：`hL2Time`/`hPDEIntegral`/`hrep`/cross-controls。

**剩余 tail（∂ₜ 时间正则 + 代数 + 表示）——精确 scope**：

- **R1（∂ₜ 时间正则 / `hL2Time`）**：`d/dt ½∫u² = ∫u·∂ₜu`。工具齐：
  `intervalIntegral_hasDerivAt_time_of_local`（参数时间积分求导）+ slab 连续 envelope
  (`exists_bound_of_continuousOn_slab`)。需 conjunct 4（逐点时间可微）+ 8/9（∂ₜu, u 的
  `(t,x)` 闭 slab 联合连续）。**陷阱**：cosine value 的 ∂ₜ 不是 bounded-coeff cosine
  value（∂ₜ weight = −λₙe^{−τλₙ}，系数 −λₙbₙ 不有界）——时间方向的 parabolic gain 比
  空间更细，要在 τ>0 用 e^{−τλₙ} 的衰减压住 λₙ 增长（per-τ bounded，τ-uniform on
  compact slab）。这是 conjunct 8 的真内容。
- **R2（`hPDEIntegral` PDE 代入）**：积分 pointwise PDE
  (`intervalDomain_solution_l2_weighted_timeDeriv_eq_pde`) + 线性拆分，需各项可积
  （u·laplacian ✓ from T5-d；u·chemoDiv 含 `(1+v)^β` 分母，可积性是真 bookkeeping）。
- **R3（`hrep` 闭边界 cosine 表示）**：把 `DuhamelHeatValueRepresentation` 从 `Ioo` 升到
  `Icc`（端点 cosine value 直接有定义，平凡延伸）；其本体（Fubini ∫₀ᵗ↔∑'ₙ + parabolic
  gain `parabolicGain_le_one`）是 `IntervalDuhamelRegularity` 已 isolate 的单一深 step。

依赖：R1 ⟸ conjunct 8（联合连续，⟸ R3 表示的联合连续 / Weierstrass-M）；R2 独立；
R3 是最深 step（Fubini + parabolic gain）。

**进度更新（2026-05-30，T5-i/T5-j）**：R3 的**闭边界升级**与 R1 的 **slab-continuous
hL2Time bridge** 均已落地（见上表）。两者都是「归约」层：

- **R3 现状**：能量不等式 `_of_cosineProfile_interior` 只需 *开区间* cosine 表示
  （`Set.EqOn … (Ioo 0 1)`）+ conjunct 7。**剩**：证 `DuhamelHeatValueRepresentation`
  本体（Fubini ∫₀ᵗ↔∑'ₙ + `parabolicGain_le_one`）—— 现在它就是 hrep 的唯一缺口。
- **R1 现状**：`hL2Time` 归约到 integrand-deriv 场的**闭 slab 联合连续**（conjunct 8/9）
  + 可测性 side conditions。**剩**：(a) 对 cosine 解证 conjunct 8（∂ₜ 场闭 slab 连续，
  Weierstrass-M + 时间 parabolic gain `−λₙe^{−τλₙ}`）；(b) 三个可测性 side conditions
  （`hF_meas`/`hF_int`/`hF'_meas`，从连续性可得，bookkeeping）。
- **R2（`hPDEIntegral`）**：本轮未动，独立。

下一步候选：(i) 攻 conjunct 8 对 cosine 解的 Weierstrass-M 装配（同时喂 R1 与 R3 的
联合连续）；(ii) discharge R1 的三个可测性 side conditions（把 hL2Time 进一步降到只剩
conjunct 8/9）；(iii) R2 `hPDEIntegral` 的线性拆分 + 可积 bookkeeping。
