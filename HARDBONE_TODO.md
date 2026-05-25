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

### H0.2 — Neumann heat semigroup gradient estimate ✅ DONE
- **内容**: `‖∇ e^{tΔ} f‖_{L^q} ≤ C t^{-γ} ‖f‖_{L^p}` for the spectral Neumann heat semigroup on `[0,L]`
- **前置**: H0.1 + cosine series term-by-term differentiation
- **目标文件**: `ShenWork/PDE/HeatKernelGradientEstimates.lean`
- **产出**: `intervalHeatSemigroup_grad_Lp_Lq_bound`
- **完成** (2026-05-24): `HeatKernelGradientEstimates.lean` 定义并使用 scaled
  spectral interval semigroup
  `intervalHeatSemigroup L t f x =
  unitIntervalNeumannHeatSemigroup (t/L^2) (fun y => f (L*y)) (x/L)`，
  证明最终有限指数估计
  `intervalHeatSemigroup_grad_Lp_Lq_bound`。当前时间奇性沿用已证明的
  absolute-convergence 端点，非 sharp `t⁻²`。
- **证明链**: cosine heat 系数模型的梯度层：
  `unitIntervalCosineHeatValue_deriv_of_l2`（L² 系数下逐项求导）、
  `intervalCosineHeatGradient_L2_L2_coeff_bound`（系数空间 L²→L²）、
  `unitIntervalCosineHeatGradientValue_L2_Linfty_smoothing`（系数空间点值 L²→L∞）。
- **Parseval bridge**: `CosineParsevalBridge.lean` 已封装 Mathlib 的 AddCircle Fourier API：
  `fourierBasis : HilbertBasis ℤ ℂ L²(AddCircle T)`、`hasSum_fourier_series_L2`、
  `tsum_sq_fourierCoeff`、`tsum_sq_fourierCoeffOn`。新增可构建 lemmas：
  `unitIntervalEvenReflection_fourier_parseval_raw`（`[-1,1]` Fourier Parseval）、
  `unitIntervalEvenReflection_fourier_parseval_unit_mass`（偶延拓质量回到 `[0,1]`）、
  `unitIntervalCosine_eq_fourier_pair`（`(e^{inπx}+e^{-inπx})/2 = cos(nπx)`）。
- **Parseval bridge 已落地**: 已证明
  `unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff`，并在
  `HeatKernelGradientEstimates.lean` 中得到
  `unitIntervalCosineRawCoeff_tsum_sq_le_integral`、
  `unitIntervalNeumannCosineCoeff_l2_bound`，把 cosine coefficient `ℓ²`
  控到 interval `L²` mass。
- **已证明端点与缩放**: `HeatKernelGradientEstimates.lean` 已证明
  unit-interval spectral cosine semigroup 的实值梯度估计
  `unitIntervalNeumannHeatSemigroup_grad_Lp_Lq_bound` 和
  `unitIntervalNeumannHeatSemigroup_grad_Lp_Linfty_bound`，并新增
  `map_mul_intervalMeasure_one`、`lpNorm_comp_mul_intervalMeasure_one_eq`、
  `memLp_comp_mul_intervalMeasure_one`、
  `unitIntervalNeumannHeatSemigroup_grad_Lp_pointwise_bound`、
  `interval_lpNorm_le_of_forall_norm_le`，完成从 `[0,1]` 到 `[0,L]`
  的 input/gradient/measure scaling。
- **验证**: `~/.elan/bin/lake build ShenWork.PDE.HeatKernelGradientEstimates`
  通过；`#print axioms
  ShenWork.HeatKernelGradientEstimates.intervalHeatSemigroup_grad_Lp_Lq_bound`
  只依赖 `[propext, Classical.choice, Quot.sound]`；0 `sorry` / 0 `axiom` /
  0 `admit` / 0 `native_decide`。
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
- **进展** (2026-05-24): `ShenWork/Paper2/IntervalDomainLemma21.lean`
  now connects the H0.1/H0.2 estimates to the concrete `intervalDomain`
  function interface.  It defines the lifted interval-domain `LpSeminorm`,
  the unit-interval helper heat operator on point functions, proves the
  lift/operator `lpNorm` bridge, and proves:
  `intervalDomainHeat_Lp_Lq_bound_from_memLp`,
  `intervalDomainHeat_grad_Lp_Lq_bound_from_memLp`, and
  `intervalDomainHeat_grad_Lp_Linfty_bound_from_memLp`.
- **新增进展** (2026-05-24): the same file now proves the fractional-time
  heat multiplier facts needed for the `S(t)-I` branch,
  `heat_time_multiplier_difference_le_fractional` and
  `heat_time_multiplier_smoothing_le`, plus finite Neumann spectral
  coefficient-energy estimates
  `finiteSpectralCoeff_heat_difference_energy_le` and
  `finiteSpectralCoeff_heat_smoothing_energy_le`.  These are real
  coefficient-level fractional estimates; the remaining work is the
  `tsum`/Hilbert-basis transport to the statement-layer total norm below.
- **Hilbert-basis bridge increment** (2026-05-24):
  `unitIntervalCosineHilbertCoeff_finite_sq_le_norm_sq` proves the finite
  Bessel inequality for the complete normalized cosine Hilbert basis, and
  `intervalDomainCosineHilbertCoeff_finite_sq_le_lpNorm_sq` transports it to
  interval-domain point functions through `intervalDomainLiftComplexLp2`.
  This fixes the finite-mode Parseval side needed before passing to infinite
  spectral fractional norms.
- **`tsum` coefficient increment** (2026-05-24):
  `spectralCoeff_heat_difference_tsum_le` and
  `spectralCoeff_heat_smoothing_tsum_le` lift the finite multiplier estimates
  to infinite coefficient series under explicit `Summable` domain hypotheses.
  This proves the Hilbert-space coefficient part of the fractional
  `S(t)-I` and `A^σ e^{-tA}` bounds for `0 < σ ≤ 1`; it still does not
  identify those coefficient energies with the total statement-layer
  `fractionalNorm`.
- **L² coefficient model increment** (2026-05-24):
  `cosineCoeffLp2`, `unitIntervalCosineLpFromCoeffs`, and
  `unitIntervalCosineHeatLpFromCoeffs` package square-summable normalized
  cosine coefficients as actual `Lp ℂ 2 (intervalMeasure 1)` vectors via
  `unitIntervalCosineHilbertBasis.repr.symm`; the repr lemmas prove the
  coefficients are exactly recovered, and `spectralHeatCoeff_l2_summable`
  proves the heat multiplier preserves `ℓ²`.
- **L² vectorized fractional increment** (2026-05-24):
  `cosineCoeffLp2_norm_sq`, `unitIntervalCosineLpFromCoeffs_norm_sq`, and
  `unitIntervalCosineHeatLpFromCoeffs_norm_sq` identify Hilbert-basis
  reconstructed `Lp ℂ 2` norms with coefficient energies.  The same file now
  also proves actual interval `L²` squared-norm estimates for the spectral
  `S(t)-I` and `A^σS(t)` vectors:
  `unitIntervalCosineHeatDifferenceLpFromCoeffs_norm_sq_le` and
  `unitIntervalCosineFractionalHeatLpFromCoeffs_norm_sq_le`.  Follow-up
  norm-form estimates
  `unitIntervalCosineHeatDifferenceLpFromCoeffs_norm_le` and
  `unitIntervalCosineFractionalHeatLpFromCoeffs_norm_le` now state the same
  bounds with square-root coefficient norms.  `unitIntervalCosineLpFromRepr_eq`
  closes the Hilbert-basis round trip from any interval `Lp ℂ 2` vector to its
  cosine coefficients and back; `unitIntervalCosineHilbertBasis_repr_energy_eq_norm_sq`
  and `intervalDomainCosineHilbertCoeff_l2_energy_eq_lpNorm_sq` give the
  corresponding Parseval energy identity for interval-domain real inputs.
- **BLOCKER / Point 17**: the full `Lemma_2_1 intervalDomain` statement is
  still not discharged.  The missing piece is not H0.1/H0.2 smoothing; it is
  the fractional-domain part of the abstract `SemigroupEstimateData` package:
  a concrete Neumann-generator norm `X^σ_q` plus
  `‖S(t)u - u‖₂ ≤ C t^σ ‖u‖_{X^σ_2}` for all interval inputs, and the
  matching analytic-semigroup smoothing
  `‖S(t)u‖_{X^σ_q} ≤ C t^{-σ} e^{-δt} ‖u‖_q`.  The current statement encodes
  `fractionalNorm : ℝ → ℝ → (D.Point → ℝ) → ℝ` as a total real-valued field,
  with no domain predicate or `∞`; a genuine interval proof therefore needs a
  spectral fractional-power construction for the Neumann Laplacian (or a
  statement-layer change to an extended/domain-restricted norm).  H0.1/H0.2
  alone do not imply the required `S(t)-I` rate.

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
- **进展** (2026-05-24): `ShenWork/Paper2/IntervalDomainTheorem11.lean`
  exposes `Lemma_4_1_intervalDomain_of_GN_frontier`, composing the existing
  `IntervalDomainInterpolation` frontier into `Lemma_4_1 intervalDomain p`.
  Not marked done until the interval interpolation frontier is proved.

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
  `ShenWork/Paper2/IntervalDomainTheorem11.lean` additionally composes the
  mass-gradient Moser frontier into
  `Corollary_2_1_intervalDomain_of_mass_gradient_frontier`.  Not marked done
  until H1.2 and the energy derivation are closed.

---

## Tier 2: Paper 2 Main Theorems (on intervalDomain)

### H2.1 — Paper2 Theorem 1.1 on intervalDomain
- **内容**: global existence + boundedness for χ ≤ 0
- **前置**: H1.2 (Lemma 2.6), H1.3 (Lemma 4.1), Lemma 3.1 (done!)
- **证明链**: Lemma 3.1 (sup norm monotonicity) → energy estimate → Lemma 2.6 (Lp bootstrap) → Lemma 4.1 (L∞) → global existence
- **目标文件**: `ShenWork/Paper2/IntervalDomainBridge.lean` (new)
- **产出**: `Theorem_1_1_intervalDomain`
- **进展** (2026-05-24): `ShenWork/Paper2/IntervalDomainTheorem11.lean`
  proves `Theorem_1_1_intervalDomain_of_corollary21_and_proposition25`:
  conditional on interval existence/initial approach/global extension,
  `Corollary_2_1`, `Proposition_2_5`, and the bootstrap seed, the full
  `Theorem_1_1 intervalDomain p` follows.  The same file also proves
  `Theorem_1_1_intervalDomain_of_mass_gradient_frontier_and_proposition25`,
  replacing the `Corollary_2_1` input by the explicit mass-gradient Moser
  frontier and cross-diffusion energy derivation.  Not marked done until those
  named frontier hypotheses are proved.
- **链条汇总** (2026-05-24): `ShenWork/Paper2/IntervalDomainTierChain.lean`
  proves `intervalDomain_tier1_theorem11_chain_of_frontiers`, a single
  conditional theorem returning `Lemma_2_6`, `Lemma_4_1`, `Corollary_2_1`, and
  `Theorem_1_1` from the explicit interval interpolation, mass-gradient Moser,
  energy-derivation, `Proposition_2_5`, existence/global-extension, and
  bootstrap-seed frontiers.

### H2.2 — Paper2 Theorem 1.2 on intervalDomain
- **前置**: H2.1 基本相同的链
- **产出**: `Theorem_1_2_intervalDomain`
- **进展** (2026-05-24): `ShenWork/Paper2/IntervalDomainTheorem12.lean`
  已加入 full statement-layer conditional assembly
  `Theorem_1_2_intervalDomain`。证明从显式 Tier-1/H0 前沿
  (`Lemma_2_1`, `Lemma_2_6`, `Lemma_4_1`, `Corollary_2_1`)、当前
  `Proposition_2_5` Lp→bounded bridge、interval Cauchy/global-extension
  bridge、weak/critical branch bootstrap seeds 和 long-time boundedness bridge
  推出完整 `Theorem_1_2 intervalDomain p`；另有
  `Theorem_1_2_intervalDomain_vacuous_when_beta_lt_one`。仍未标 DONE：
  H1.x、branch bootstrap seeds、全局最终有界性 bridge 还未无条件闭合。

### H2.3 — Paper2 Theorem 1.3 on intervalDomain
- **前置**: H2.1 + strong logistic condition
- **产出**: `Theorem_1_3_intervalDomain`
- **进展** (2026-05-24): `ShenWork/Paper2/IntervalDomainTheorem13.lean`
  已加入 full statement-layer conditional assembly
  `Theorem_1_3_intervalDomain`。证明从显式 Tier-1/H0 前沿、当前
  `Proposition_2_5` Lp→bounded bridge、interval Cauchy/global-extension
  bridge、strong-logistic branch bootstrap seed 和 long-time boundedness bridge
  推出完整 `Theorem_1_3 intervalDomain p C`；另有 `a=0`、`b=0`、
  `m≤0` 三个 vacuous interval-domain lemmas。仍未标 DONE：H1.x、
  strong-logistic bootstrap seed、全局最终有界性 bridge 还未无条件闭合。

---

## Tier 3: Paper 3 Infrastructure

### H3.1 — Sectorial operator / analytic semigroup framework
- **内容**: linearized operator -Δ + lower-order 是 sectorial 的 → 生成解析半群
- **现状**: 完全未做; Mathlib 没有 sectorial operator 理论
- **当前前沿** (2026-05-24): `ShenWork/Paper3/Statements.lean`
  已有诚实 raw 接口 `SectorialLocalExponentialRaw`，以及把该 raw
  假设接到 `LocallyExponentiallyStableFromSup` /
  `MassConstrainedLocallyExponentiallyStableFromSup` 的桥接定理。尚未证明
  intervalDomain 上线性化 Neumann operator 的 sectoriality、解析半群生成、
  resolvent/谱界到指数衰减的完整链条。`ShenWork/Paper3/IntervalDomainSectorial.lean`
  已把该 raw hypothesis 专门化到 `intervalDomain` +
  `unitIntervalNeumannSpectrum`，并暴露 `X^σ_p ≤ supNorm` 与 small-data
  existence 作为独立前沿；非正敏感度正平衡的 linear 部分已从 unit-interval
  Neumann spectrum 直接接上。minimal equilibrium (`a=b=0`) 分支也已通过
  `intervalDomain_minimalEquilibrium_localStability_chi_nonpos_of_sectorialHypothesis`
  与
  `intervalDomain_minimalEquilibrium_massStability_chi_nonpos_of_sectorialHypothesis`
  接到同一 H3.1 raw sectorial/small-data/norm-comparison 前沿。新增
  critical-threshold wrappers
  `intervalDomain_positiveEquilibrium_localStability_of_chi_lt_critical_of_sectorialHypothesis`,
  `intervalDomain_positiveEquilibrium_massStability_of_chi_lt_critical_of_sectorialHypothesis`,
  `intervalDomain_minimalEquilibrium_localStability_of_chi_lt_critical_of_sectorialHypothesis`,
  and
  `intervalDomain_minimalEquilibrium_massStability_of_chi_lt_critical_of_sectorialHypothesis`:
  the unit-interval linear threshold is discharged, while raw sectoriality,
  branch norm-comparison, and branch small-data existence remain honest
  frontiers.  新增
  `intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers`，把
  `LinearStabilityInstabilityNonminimalRaw` /
  `LinearStabilityInstabilityMinimalRaw` 的 intervalDomain 版本接到同样的
  branch-specific H3.1 前沿，避免 generic `∀ uStar` norm/small-data 假设。
  新增 `intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers_criticalSpectrum`，
  用 `Paper3ConstantsUsesCriticalSpectrum` 把 concrete constants 的
  `C.chiCritical` 接到同一 branch-specific raw package；这只 discharge
  constants/critical-spectrum identification，sectoriality、branch norm-comparison
  与 branch small-data existence 仍是 H3.1 state③ 前沿。
- **前置**: spectral theory on bounded domain, resolvent estimates
- **目标文件**: `ShenWork/PDE/SectorialOperator.lean` (new)
- **产出**: `SectorialLocalExponentialRaw`
- **下游**: Paper3 Lemma A.1, Theorem 2.2

### H3.2 — Lyapunov function for chemotaxis system ✅ DONE (conditional analytic bridge)
- **内容**: 构造 Lyapunov functional `E[u,v]` 并证 dE/dt ≤ -c E
- **完成**: `ShenWork/Paper3/LyapunovFunction.lean` (2026-05-24; 0 proof holes in file; axioms core only)
- **前置**: H0.3 (Gagliardo-Nirenberg), Poincaré inequality
- **目标文件**: `ShenWork/Paper3/LyapunovFunction.lean`
- **产出**: Paper3 entropy density/functionals, entropy monotonicity theorem, and signal-energy exponential decay estimate
- **Point 17 状态**: ③ 条件于未证 analytic inputs。现有 `BoundedDomainData`
  还没有 gradient dot product、divergence theorem、Neumann integration by
  parts、time-chain rule, or abstract Poincaré bridge fields, so the PDE
  derivation of the differential inequality is exposed as named theorem
  hypotheses (`hderiv`, `hdiss`, `hcontrol`) rather than faked.
- **下游**: Paper3 Theorem 2.3, 2.4 (global stability)

### H3.3 — Paper3 Theorem 2.1 part1 on intervalDomain
- **内容**: eventual lower bound for PGBS on a real domain
- **前置**: H0.5 (ODE uniqueness) or Harnack inequality
- **NOTE**: unitPoint 版本用了 ODE 直接算; intervalDomain 需要 Harnack 或 strong maximum principle
- **进展** (2026-05-24): `ShenWork/Paper3/IntervalDomainTheorem21Part1.lean`
  已组装条件版
  `Theorem_2_1_part1_intervalDomain_of_pointwise_persistence`。该定理把
  Paper3 Section 4.1 的两个真实缺口显式暴露为命名假设：
  (1) time-translate compactness + Neumann strong maximum principle + ODE
  subsolution 给出 `u` 的 eventual pointwise lower bound；
  (2) elliptic Neumann comparison 把 `u` 的 lower bound 转成 `v` 的 lower
  bound。另证明 helper
  `intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower`，把
  intervalDomain 上的 pointwise lower bound 转为 statement 层的
  `EventuallyLowerBound`，并新增反向语义桥
  `intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound` 与
  `Theorem_2_1_part1_intervalDomain_pointwise_of_lowerEnvelope`，在显式
  `BddBelow (Set.range (u t))` time-slice 条件下把 lower-envelope statement
  读回 pointwise persistence。新增
  `Theorem_2_1_part1_intervalDomain_pointwise_of_pointwise_persistence`，从同
  两个 Section 4.1 前沿直接给出 intended pointwise persistence，避免把
  语义读回依赖混入 statement-layer 组装。新增
  `Theorem_2_1_part1_intervalDomain_of_pointwise_lower_bounds` 和
  `Theorem_2_1_part1_intervalDomain_iff_pointwise_lower_bounds`，把
  statement-layer `Theorem_2_1_part1` 与 intended pointwise persistence
  精确对齐；反向仍显式要求 time-slice `BddBelow`，因为 abstract
  `BoundedDomainData.infValue` 本身不携带 lower-envelope correctness。
  新增 `intervalDomain_pointwise_lower_of_inside_boundary_lower`,
  `intervalDomain_eventually_pointwise_lower_of_inside_boundary_lower`,
  `intervalDomain_eventuallyLowerBound_of_inside_boundary_lower`, and
  `Theorem_2_1_part1_intervalDomain_of_inside_boundary_lower_bounds`，把
  open-interior lower bounds 和 endpoint lower bounds 机械组合为全
  intervalDomain lower-envelope persistence；这只 discharge `[0,1]` 的
  interior/boundary 覆盖步骤，interior persistence 和 boundary lower-bound
  仍是分析前沿。新增
  `intervalDomain_eventually_pointwise_lower_iff_inside_boundary_lower`,
  `intervalDomain_eventuallyLowerBound_iff_inside_boundary_lower`,
  `Theorem_2_1_part1_intervalDomain_pointwise_of_inside_boundary_lower_bounds`,
  and
  `Theorem_2_1_part1_intervalDomain_iff_inside_boundary_lower_bounds`，把
  statement-layer、全 pointwise、open-interior+endpoint 三种 H3.3 表述对齐；
  反向读回仍需要显式 `BddBelow`。
  按 17-point standard 属于状态③：条件于未证但明确命名的分析前沿；不是
  无条件完成。

---

## Tier 4: Paper 3 Main Theorems

### H4.1 — Theorem 2.2 on intervalDomain (local stability)
- **前置**: H3.1 (sectorial semigroup), spectral analysis (partly done)
- **进展** (2026-05-24): `ShenWork/Paper3/IntervalDomainStabilityChain.lean`
  proves `intervalDomain_Theorem_2_2_of_sectorial_frontiers`, the full
  intervalDomain `Theorem_2_2` statement from the concrete unit-interval
  Neumann spectrum plus explicit H3.1 frontiers: raw sectorial local
  exponential estimate, `X^σ_p`/sup-norm comparison, ordinary small-data
  existence, and mass-constrained small-data existence.  It also proves
  `intervalDomain_Theorem_2_2_of_xpSigma_le_supNorm_frontiers`, discharging
  the abstract `SupControlsXpSigmaDistance` condition from the primitive
  pointwise comparison `X^σ_p ≤ supNorm`, and
  `intervalDomain_Theorem_2_2_for_concrete_constants`, discharging the
  constants package and critical-spectrum identity through
  `intervalDomainPaper3Constants`.  It further proves
  `intervalDomain_Theorem_2_2_for_concrete_constants_branch_frontiers`,
  replacing the over-strong `∀ uStar : ℝ` norm/small-data frontiers by exactly
  the branches used in Theorem 2.2: positive equilibria and minimal
  equilibria with `0 < uStar`.  This is state③, not DONE: the sectorial,
  primitive branch norm-comparison, and branch local-existence frontiers are
  still unproved.  New increment:
  `intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw` composes the
  raw stable local-exponential branches with the unit-interval critical
  spectrum to recover the full `Theorem_2_2` unstable branches, and
  `intervalDomain_Theorem_2_2_for_concrete_constants_branch_frontiers_via_linearRaw`
  routes the concrete branch frontiers through
  `intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers`.  This
  closes the H3.1 raw-package-to-H4.1 statement bridge, while the same analytic
  H3.1 frontiers remain open.  New increment:
  `intervalDomain_Theorem_2_2_of_branch_frontiers_criticalSpectrum` removes the
  concrete constants restriction from that composition: any constants package
  whose `chiCritical` field is identified with the unit-interval spectral
  threshold now composes from the branch-specific H3.1 frontiers to the full
  `Theorem_2_2`.

### H4.2 — Theorem 2.3 on intervalDomain (global stability χ≤0)
- **前置**: H3.2 (Lyapunov), H3.3 (persistence)
- **进展** (2026-05-24): `ShenWork/Paper3/IntervalDomainStabilityChain.lean`
  proves
  `intervalDomain_Theorem_2_3_of_lyapunov_moment_and_exponential_frontiers`.
  It derives global-attractor convergence from explicit Lyapunov
  theta-dissipation decay frontiers plus `MomentConvergenceToUniformRaw`, and
  derives the theorem's uniform C¹ exponential branch from explicit
  critical-threshold uniform exponential-upgrade frontiers.  This is state③:
  the moment-decay, moment-to-uniform, and uniform exponential-upgrade
  frontiers are still analytic gaps.  The same file now also proves
  `intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul` and
  `intervalDomain_Theorem_2_3_of_theta_derivative_frontiers`, reducing the
  theta moment-decay input to a direct differential estimate
  `D'(t) ≤ -rate * D(t)` plus eventual slice nonnegativity.  New increment:
  `intervalDomain_integral_nonneg_of_inside_nonneg`,
  `intervalDomain_chemotaxisThetaDissipation_nonneg_of_positiveGlobalBoundedSolution`,
  `intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul_of_solution`,
  and
  `intervalDomain_Theorem_2_3_of_theta_derivative_frontiers_from_solution_positivity`
  discharge that nonnegativity side condition from the statement-level
  `PositiveGlobalBoundedSolution` interior positivity and the zero measure of
  the interval endpoints.  New increment:
  `intervalDomain_momentToUniform_of_corollary51` projects the
  moment-to-uniform bridge out of `Corollary_5_1`, and
  `intervalDomain_Theorem_2_3_of_corollary51_theta_derivative_solution`
  composes that projection with the theta-derivative solution wrapper.
  Still state③: deriving the direct differential estimate from the PDE and
  proving the theorem-level uniform C¹ exponential constants remain open
  analytic frontiers.  `Corollary_5_1` gives per-solution exponential constants;
  this is strictly weaker than the `∃ A rate, ∀ u v` constants in
  `Theorem_2_3`, so the uniform-constant frontier is not discharged.

### H4.3 — Theorem 2.4 on intervalDomain (global stability strong logistic)
- **前置**: H3.2 (Lyapunov), H2.1 (global existence)
- **进展** (2026-05-24): `ShenWork/Paper3/IntervalDomainStabilityChain.lean`
  proves
  `intervalDomain_Theorem_2_4_of_lyapunov_moment_and_exponential_frontiers`.
  It composes the strong-logistic Lyapunov moment-decay frontier with
  `MomentConvergenceToUniformRaw`; `Lemma_A_7` plus the unit-interval
  critical-spectrum identity supplies the critical-threshold input for the
  uniform C¹ exponential-upgrade frontier.  The concrete-constants wrappers
  `intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_and_frontiers`
  and
  `intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_formula_frontiers`
  discharge the constants package, critical-spectrum identity, `Lemma_A_7`,
  and the package-shaped strong-logistic condition down to the explicit
  first-mode/formula frontiers.  This is state③, not DONE: H2.1/global
  existence, moment-to-uniform, Lyapunov formula decay, and uniform exponential
  upgrade remain explicit frontiers.  The same file now proves
  `intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_formula_derivative_frontiers`,
  further reducing the Lyapunov formula-decay frontier to the direct
  theta-dissipation differential estimate plus eventual slice nonnegativity.
  New increment:
  `intervalDomain_Theorem_2_4_formula_derivative_frontiers_from_solution_positivity`
  removes that nonnegativity side condition using `PositiveGlobalBoundedSolution`.
  New increment:
  `intervalDomain_Theorem_2_4_formula_derivative_solution_of_corollary51`
  supplies the moment-to-uniform input from `Corollary_5_1`.  This does not
  close H4.3: the PDE derivation of the direct differential estimate,
  H2.1/global existence, and theorem-level uniform exponential constants
  remain open.  The same quantifier gap remains: `Corollary_5_1` provides
  solution-dependent exponential constants, while `Theorem_2_4` requires one
  `A, rate` for the whole branch.

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
- **当前前沿** (2026-05-24): ODE/profile side now has the local Picard
  flow, C² bootstrap, scalar profile ODE identities
  (`SolvesTWODE.profile_equations`, `TravelingWave.profile_equations`),
  heteroclinic-to-profile wrappers
  (`HasHeteroclinicE1E0.exists_profile_equations`,
  `HasHeteroclinicE1E0.exists_profile_c2_bootstrap`,
  `HasHeteroclinicE1E0.exists_profileData`), packaged C²/boundary/left-positive
  profile data (`WaveProfileData`, `TravelingWave.to_profileData`), profile
  endpoint limits (`TravelingWave.profile_boundary_limits`), shift invariance
  for ODE solutions/profile data/heteroclinics (`SolvesTWODE.shift`,
  `WaveProfileData.shift`, `HasHeteroclinicE1E0.shift`), and the exact bridge
  from the Nat-exponent ODE layer to root `IsTravelingWave` under explicit
  positive-speed and global-positivity assumptions
  (`WaveProfileData.to_isTravelingWave`, `TravelingWave.to_isTravelingWave`).
  It also has E1/E0 linearized eigenmodes with decay
  (`unstableLinearModeAtOne_solves_and_decays`,
  `stableLinearModeAtZero_solves_and_decays`), the E0 stable local shooting
  segment in `ShenWork/PDE/TravelingWaveODE.lean`, the linearized solution
  regularity/closure facts (`SolvesLinearized.contDiff_two`,
  `SolvesLinearized.add`, `SolvesLinearized.const_smul`), and logistic C² plus
  strict-derivative facts (`logisticProfile_contDiff_two`,
  `logisticProfile_deriv_neg`,
  `logisticProfile_facts_with_contDiff_exp_bound_and_strict_deriv`) in
  `ShenWork/PDE/TravelingWaveConstruction.lean`.
  This does not prove Paper1 Theorem 1.2.  The missing analytic load is the
  global positivity of the heteroclinic `U` needed to turn an arbitrary
  `HasHeteroclinicE1E0` into root `IsTravelingWave`, plus the nonlinear
  weighted Cauchy stability chain for perturbations of a wave: global
  well-posedness from nearby weighted data, weighted energy/semigroup decay,
  uniform moving-frame convergence, and the exact bridge from these estimates
  to `Paper1.Theorem_1_2`.  Status by point 17: ③ conditional on named
  upstream positivity/PDE/weighted-Sobolev stability inputs, not weakened or
  faked.

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
