# 硬骨头清单 — ShenWork Formalization

按依赖顺序排列。每一项标注：前置依赖、目标文件、难度估计。

---

## Tier 0: 核心分析基础设施（Mathlib 可能有、需要找或自建）

### H0.1 — Neumann heat semigroup on [0,L]: L^p → L^q smoothing
- **内容**: `‖e^{tΔ} f‖_{L^q} ≤ C t^{-N/2(1/p-1/q)} ‖f‖_{L^p}` for Neumann Laplacian on interval
- **现状**: 全线热核 `heatKernel` 有 130 lemmas (HeatSemigroup.lean); 区间 cosine 展开有 82 lemmas (CosineSpectrum.lean); 但 L^p→L^q 估计未组装
- **前置**: Mathlib MeasureTheory.Function.LpSeminorm, cosine series convergence
- **目标文件**: `ShenWork/PDE/HeatKernelLpEstimates.lean`
- **产出**: `intervalHeatSemigroup_Lp_Lq_bound`
- **下游**: Paper2 Lemma 2.1, Lemma 4.1

### H0.2 — Neumann heat semigroup gradient estimate (partial — spectral/helper bounds done; semigroup equivalence still open)
- **内容**: `‖∇ e^{tΔ} f‖_{L^q} ≤ C t^{-1/2-N/2(1/p-1/q)} ‖f‖_{L^p}`
- **前置**: H0.1 + cosine series term-by-term differentiation
- **目标文件**: `ShenWork/PDE/HeatKernelGradientEstimates.lean`
- **产出**: `intervalHeatSemigroup_grad_Lp_Lq_bound`
- **当前前沿** (2026-05-24): 已在 `HeatKernelGradientEstimates.lean` 形式化 cosine heat 系数模型的梯度层：
  `unitIntervalCosineHeatValue_deriv_of_l2`（L² 系数下逐项求导）、
  `intervalCosineHeatGradient_L2_L2_coeff_bound`（系数空间 L²→L²）、
  `unitIntervalCosineHeatGradientValue_L2_Linfty_smoothing`（系数空间点值 L²→L∞）。
- **Parseval bridge 进展** (2026-05-24): `CosineParsevalBridge.lean` 已封装 Mathlib 的 AddCircle Fourier API：
  `fourierBasis : HilbertBasis ℤ ℂ L²(AddCircle T)`、`hasSum_fourier_series_L2`、
  `tsum_sq_fourierCoeff`、`tsum_sq_fourierCoeffOn`。新增可构建 lemmas：
  `unitIntervalEvenReflection_fourier_parseval_raw`（`[-1,1]` Fourier Parseval）、
  `unitIntervalEvenReflection_fourier_parseval_unit_mass`（偶延拓质量回到 `[0,1]`）、
  `unitIntervalCosine_eq_fourier_pair`（`(e^{inπx}+e^{-inπx})/2 = cos(nπx)`）。
- **Parseval bridge 已落地** (2026-05-24): 已证明
  `unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff`，并在
  `HeatKernelGradientEstimates.lean` 中得到
  `unitIntervalCosineRawCoeff_tsum_sq_le_integral`、
  `unitIntervalNeumannCosineCoeff_l2_bound`，把 cosine coefficient `ℓ²`
  控到 interval `L²` mass。
- **新增已证明端点** (2026-05-24): `HeatKernelGradientEstimates.lean`
  已证明 unit-interval spectral cosine semigroup 的实值梯度估计
  `unitIntervalNeumannHeatSemigroup_grad_Lp_Lq_bound` 和
  `unitIntervalNeumannHeatSemigroup_grad_Lp_Linfty_bound`，目前是
  absolute-convergence 端点，时间奇性为非 sharp `t⁻²`。同文件还证明了
  H0.1 当前 helper operator `intervalSemigroupOperator` 的 unit-interval
  梯度配套估计：
  `unitIntervalSemigroupOperator_grad_Lp_Lq_lpNorm_bound`、
  `unitIntervalSemigroupOperator_grad_Lp_Linfty_lpNorm_bound`。
- **仍未完成缺口**: 还不能把上述结果诚实改写成最终
  `intervalHeatSemigroup_grad_Lp_Lq_bound`。缺少：
  (1) `unitIntervalNeumannHeatSemigroup` 与 repository 中真正要用的
  intervalDomain Neumann semigroup 的等价定理；
  (2) 从 unit interval 推到 `[0,L]` 的 scaling bridge，包括 cosine
  coefficients、`intervalMeasure L` 下的 `lpNorm` scaling、梯度 scaling；
  (3) sharp 指数 `t^{-1/2-N/2(1/p-1/q)}` 的插值/Young/Schur 链。Mathlib
  未找到现成 Riesz-Thorin/Young convolution API；若坚持 sharp 指数，需要
  先自建最小插值或梯度核 `L^r` norm lemma；
  (4) 确认/替换 H0.1 当前 `intervalSemigroupOperator`：该 operator 在
  `IntervalDomain.lean` 明确标注为 zeroth-reflection helper，不是完整
  Neumann heat kernel。
- **Focused close attempt** (2026-05-24): 搜索 `intervalHeatSemigroup`,
  `NeumannHeatSemigroup`, `SemigroupEstimateData`, `intervalSemigroupOperator`
  后确认仓库中没有独立的 abstract interval Neumann heat semigroup 定义；
  H0.1 的 `intervalHeatSemigroup_Lp_Lq_bound` 展开后仍是
  `intervalSemigroupOperator`。`Paper2/Statements.lean` 也明确说明当前
  interval bridges 不是 `SemigroupEstimateData` projections，而是 restricted
  reflected helper estimates。因而 Parseval/HilbertBasis bridge 不能单独闭合
  H0.2；还需先引入完整 Neumann interval heat semigroup（spectral 或全
  image-sum kernel）并把 H0.1/H0.2 的最终 theorem target rebased 到该对象。
- **下游**: Paper2 Lemma 2.1 (derivative part)

### H0.3 — Gagliardo-Nirenberg interpolation on [0,L] ✅ DONE
- **内容**: Moser iteration endpoint `‖f‖_{L^4}^2 ≤ (C_L ‖f‖_{L^2} + C_L ‖f'‖_{L^2}) ‖f‖_{L^2}` (the `r=4`, `p=q=2`, `θ=1/2` case with lower-order interval term)
- **完成**: `ShenWork/PDE/GagliardoNirenberg.lean` (2026-05-24; 0 sorry; axioms `[propext, Classical.choice, Quot.sound]`)
- **现状**: Mathlib 没有 (checked 2026-05)
- **前置**: Sobolev embedding 1D (H0.4), fundamental theorem of calculus
- **目标文件**: `ShenWork/PDE/GagliardoNirenberg.lean` (new)
- **产出**: `gagliardoNirenberg_interval`
- **下游**: Paper2 Lemma 2.6 (Moser iteration), Lemma 4.1

### H0.4 — Sobolev embedding H^1([0,L]) → L^∞([0,L]) ✅ DONE
- **内容**: 1D Sobolev: `‖f‖_{L^∞} ≤ C(‖f‖_{L^2} + ‖f'‖_{L^2})`
- **完成**: `ShenWork/PDE/SobolevEmbedding.lean` (2026-05-24; 0 sorry; axioms `[propext, Classical.choice, Quot.sound]`)
- **前置**: Fundamental theorem of calculus on [0,L], Cauchy-Schwarz
- **目标文件**: `ShenWork/PDE/SobolevEmbedding.lean` (new)
- **产出**: `sobolev_H1_Linfty_interval`
- **下游**: H0.3, Lemma 4.1

### H0.5 — ODE uniqueness for locally Lipschitz vector fields ✅ DONE
- **内容**: Picard-Lindelöf uniqueness for Bernoulli logistic and decay ODEs
- **完成**: commits 5124e6c, f3a4f6e (2026-05-24)
- **文件**: `ShenWork/PDE/ODEUniqueness.lean` (0 sorry, 6 lemmas/theorems)
- **产出**: `bernoulliLogistic_unique`, `bernoulliDecay_unique`
- **下游**: Paper3 Theorem 2.1 (part1 nonminimal on interval), Theorem 2.3

---

## Tier 1: Paper 2 Key Lemmas (on intervalDomain)

### H1.1 — Paper2 Lemma 2.1 on intervalDomain
- **内容**: heat semigroup estimate `HeatSemigroupEstimateData` instantiated for interval Neumann semigroup
- **前置**: H0.1, H0.2
- **目标文件**: `ShenWork/Paper2/Statements.lean` (or new bridge file)
- **产出**: `Lemma_2_1_intervalDomain`

### H1.2 — Paper2 Lemma 2.6 on intervalDomain (Moser iteration)
- **内容**: from `AbstractLpBootstrapHypothesis` + energy inequality, conclude L^p bound for all p
- **前置**: H0.3 (Gagliardo-Nirenberg), H1.1
- **目标文件**: `ShenWork/Paper2/Statements.lean`
- **产出**: `Lemma_2_6_intervalDomain`
- **NOTE**: 这是整个 global existence 链条的核心 — Lp bootstrap
- **进展** (2026-05-24): `ShenWork/Paper2/IntervalDomainChain.lean`
  proves the single-step/chain Moser algebra; `ShenWork/Paper2/IntervalDomainMoserClosure.lean`
  proves the Archimedean exponent closure: bounds on `p₀+nρ` plus downward
  Lp monotonicity imply bounds for every `p>1`; `ShenWork/Paper2/IntervalDomainLpMonotonicity.lean`
  proves the `[0,1]` finite-interval Lp monotonicity bridge under nonnegativity
  and time-slice power integrability; `ShenWork/Paper2/IntervalDomainEnergyStep.lean`
  converts `LpBootstrapEnergyInequality` into the Moser step under explicit
  dissipation and interpolation hypotheses, and converts
  `LpMassGradientInterpolationEstimate` plus chain-rule/mass-control bridges
  into the `ε·G + Cε` interpolation interface.  Not marked done until those
  hypotheses are proved from the interval PDE data.

### H1.3 — Paper2 Lemma 4.1 on intervalDomain (L^p → L^∞)
- **内容**: from L^p bounds for all p, conclude L^∞ bound
- **前置**: H0.4 (Sobolev), H1.2
- **目标文件**: `ShenWork/Paper2/Statements.lean`
- **产出**: `Lemma_4_1_intervalDomain`

### H1.4 — Paper2 Corollary 2.1 on intervalDomain
- **内容**: cross-diffusion bootstrap → L^p for all p
- **前置**: H1.2
- **目标文件**: `ShenWork/Paper2/Statements.lean`
- **产出**: `Corollary_2_1_intervalDomain`
- **进展** (2026-05-24): `ShenWork/Paper2/IntervalDomainCorollary21.lean`
  proves the honest conditional bridge
  `Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy`:
  `Lemma_2_6 intervalDomain` plus the PDE energy derivation from
  `CrossDiffusionBootstrapEstimate` implies `Corollary_2_1 intervalDomain p`.
  Not marked done until H1.2 and the energy derivation are closed.

---

## Tier 2: Paper 2 Main Theorems (on intervalDomain)

### H2.1 — Paper2 Theorem 1.1 on intervalDomain
- **内容**: global existence + boundedness for χ ≤ 0
- **前置**: H1.2 (Lemma 2.6), H1.3 (Lemma 4.1), Lemma 3.1 (done!)
- **证明链**: Lemma 3.1 (sup norm monotonicity) → energy estimate → Lemma 2.6 (Lp bootstrap) → Lemma 4.1 (L∞) → global existence
- **目标文件**: `ShenWork/Paper2/IntervalDomainBridge.lean` (new)
- **产出**: `Theorem_1_1_intervalDomain`

### H2.2 — Paper2 Theorem 1.2 on intervalDomain
- **前置**: H2.1 基本相同的链
- **产出**: `Theorem_1_2_intervalDomain`

### H2.3 — Paper2 Theorem 1.3 on intervalDomain
- **前置**: H2.1 + strong logistic condition
- **产出**: `Theorem_1_3_intervalDomain`

---

## Tier 3: Paper 3 Infrastructure

### H3.1 — Sectorial operator / analytic semigroup framework
- **内容**: linearized operator -Δ + lower-order 是 sectorial 的 → 生成解析半群
- **现状**: 完全未做; Mathlib 没有 sectorial operator 理论
- **前置**: spectral theory on bounded domain, resolvent estimates
- **目标文件**: `ShenWork/PDE/SectorialOperator.lean` (new)
- **产出**: `SectorialLocalExponentialRaw`
- **下游**: Paper3 Lemma A.1, Theorem 2.2

### H3.2 — Lyapunov function for chemotaxis system
- **内容**: 构造 Lyapunov functional `E[u,v]` 并证 dE/dt ≤ -c E
- **前置**: H0.3 (Gagliardo-Nirenberg), Poincaré inequality
- **目标文件**: `ShenWork/PDE/LyapunovFunction.lean` (new)
- **产出**: Lyapunov decay estimate
- **下游**: Paper3 Theorem 2.3, 2.4 (global stability)

### H3.3 — Paper3 Theorem 2.1 part1 on intervalDomain
- **内容**: eventual lower bound for PGBS on a real domain
- **前置**: H0.5 (ODE uniqueness) or Harnack inequality
- **NOTE**: unitPoint 版本用了 ODE 直接算; intervalDomain 需要 Harnack 或 strong maximum principle

---

## Tier 4: Paper 3 Main Theorems

### H4.1 — Theorem 2.2 on intervalDomain (local stability)
- **前置**: H3.1 (sectorial semigroup), spectral analysis (partly done)

### H4.2 — Theorem 2.3 on intervalDomain (global stability χ≤0)
- **前置**: H3.2 (Lyapunov), H3.3 (persistence)

### H4.3 — Theorem 2.4 on intervalDomain (global stability strong logistic)
- **前置**: H3.2 (Lyapunov), H2.1 (global existence)

---

## Tier 5: Paper 1 (Traveling Waves)

### H5.1 — Picard iteration local existence ✅ DONE
- **前置**: Mathlib Banach fixed point, function space norms
- **产出**: local ODE solution existence
- **完成** (2026-05-24): `ShenWork/PDE/TravelingWaveODE.lean`
  proves the Picard local-flow theorem for the autonomous 4D wave-profile ODE:
  `localFlowExists`, building on `picardLindelofData` and Mathlib
  `IsPicardLindelof`.  Single-file check:
  `lake env lean ShenWork/PDE/TravelingWaveODE.lean`; axioms for
  `localFlowExists` are `[propext, Classical.choice, Quot.sound]`.

### H5.2 — C² bootstrap for traveling wave profile ✅ DONE
- **前置**: H5.1, elliptic regularity
- **产出**: C² profile
- **完成** (2026-05-24): `ShenWork/PDE/TravelingWaveODE.lean`
  proves the ODE/profile bootstrap from any first-order solution
  `SolvesTWODE p z`: `SolvesTWODE.contDiff_two`,
  `SolvesTWODE.profile_c2_bootstrap`, and
  `TravelingWave.profile_c2_bootstrap`.  The result gives
  `ContDiff ℝ 2` for the `U = z 0` and `V = z 2` profile components plus the
  second-derivative ODE identities.  Axioms for the two profile bootstrap
  theorems are `[propext, Classical.choice, Quot.sound]`.

### H5.3 — Wave stability (Theorem 1.2)
- **前置**: H3.1 (sectorial), weighted Sobolev spaces

---

## 推荐攻坚顺序

**Phase 1 (最高优先级 — 解锁整条链):**
1. H0.4 Sobolev embedding 1D — 最基础，Cauchy-Schwarz + FTC
2. H0.1 Neumann heat semigroup L^p→L^q — 连接 cosine spectrum 到估计
3. H0.3 Gagliardo-Nirenberg 1D — 解锁 Moser iteration

**Phase 2 (Paper 2 核心链):**
4. H1.2 Lemma 2.6 Moser iteration — 整个 global existence 的瓶颈
5. H1.3 Lemma 4.1 L^p→L^∞ — 从 Lp 到 sup norm
6. H2.1 Theorem 1.1 intervalDomain — 第一个真正的 PDE 主定理

**Phase 3 (Paper 3 稳定性):**
7. H3.1 Sectorial semigroup — 解锁 Theorem 2.2
8. H3.2 Lyapunov function — 解锁 Theorem 2.3/2.4
