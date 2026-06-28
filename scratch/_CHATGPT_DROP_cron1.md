# Q1803 (cron1) -- `Rderiv` tail bound

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was only:

```text
Q1803 (cron1): cron1 /tmp/q_cron1_Rderiv.txt
```

The local file `/tmp/q_cron1_Rderiv.txt` was not present in the runtime I can inspect, and it is not readable through the GitHub connector. I used the repository state and the name `Rderiv` to identify the intended gap.

I did **not** use Python, `/mnt/data`, the sandbox, or a sandbox link. I did not run Lean locally.

## Inferred target

The relevant live gap is in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

inside:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
```

at the `i = 1` tail block:

```lean
have hR_deriv_bounded : ∃ B_R' : ℝ, ∀ t : ℝ, c + 1 < t →
    |deriv R t| ≤ B_R' := by
  -- deriv R = w_k * deriv srcTimeCoeff
  -- deriv srcTimeCoeff = cosineCoeffs(srcSlice1(t), k) from d0 HasDerivAt
  -- |cosineCoeffs(srcSlice1, k)| ≤ 2·νγ·M_sup^{γ-1}·M₀·C_Δ/(c+1)²
  -- from cosineCoeffs_abs_le_of_continuous_bounded + L∞ contraction +
  -- unitIntervalCosineHeatSecondPointWeight_abs_le
  sorry
```

## Verdict

The direct `Rderiv` route should be split into two pieces:

1. Extract the exact derivative formula for the resolver coefficient:

```lean
deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t =
  ShenWork.PDE.intervalNeumannResolverWeight p k *
    cosineCoeffs
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k
```

for `0 < t`.

2. Prove one reusable tail estimate for the coefficient of `srcSlice1`.

Do **not** try to close this by using `ContDiffAt` opaquely.  The exact derivative is already constructed inside `heatLevel0_srcTimeCoeff_contDiffAt_two`; it should be exposed as a named `HasDerivAt` lemma and then transferred through `resolverTimeCoeff_eq_weight_smul`.

## Extract the source and resolver derivative lemmas

Add these near the existing Layer 1 / Layer 2 block in `IntervalHeatResolverJointC2.lean`.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete
  (srcSlice srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatSemigroup_d0)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Extract the `d0` source-coefficient derivative that is currently buried inside
`heatLevel0_srcTimeCoeff_contDiffAt_two`. -/
theorem heatLevel0_srcTimeCoeff_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k)
      (cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k)
      t := by
  obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
    heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor t ht
  have hint : ∀ᶠ r in 𝓝 t, IntervalIntegrable
      (srcSlice p (conjugatePicardIter p u₀ 0) r)
      MeasureTheory.volume (0 : ℝ) 1 :=
    hcont.mono fun r hr =>
      (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
  have hH := cosineCoeffs_hasDerivAt_of_smooth_param
    (f := srcSlice p (conjugatePicardIter p u₀ 0))
    (f' := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
    (τ := t) (δ := δ) (n := k) hδ hint hdiff hcd
  have heq :
      (fun r => cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) r) k) =
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k := by
    funext r
    simp [srcTimeCoeff_eq_cosineCoeffs]
  rw [heq] at hH
  simpa using hH

/-- Resolver coefficient derivative: source derivative times the constant elliptic
weight. -/
theorem heatLevel0_resolverTimeCoeff_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k)
      (ShenWork.PDE.intervalNeumannResolverWeight p k *
        cosineCoeffs
          (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k)
      t := by
  have hsrc := heatLevel0_srcTimeCoeff_hasDerivAt
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor ht k
  have hEq : resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k =
      fun s => ShenWork.PDE.intervalNeumannResolverWeight p k *
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
    funext s
    exact resolverTimeCoeff_eq_weight_smul p _ k s
  rw [hEq]
  simpa using hsrc.const_mul (ShenWork.PDE.intervalNeumannResolverWeight p k)

/-- Convenient `deriv` rewrite form for the tail estimate. -/
theorem heatLevel0_resolverTimeCoeff_deriv_eq
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t =
      ShenWork.PDE.intervalNeumannResolverWeight p k *
        cosineCoeffs
          (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k := by
  exact (heatLevel0_resolverTimeCoeff_hasDerivAt
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor ht k).deriv

end ShenWork.Paper2.HeatResolverJointC2Direct
```

The first lemma is almost copied from the internal `hd0` portion of `heatLevel0_srcTimeCoeff_contDiffAt_two`, so it is a low-risk extraction.

## Factor the analytic bound once

The remaining analytic content is a tail bound for `srcSlice1` coefficients.  The clean shape is:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData (heatDu)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Uniform bound for the heat Laplacian tail.

Implementation route:
* unfold `heatDu` at positive time;
* expose or locally reproduce the private `heatDu_eq_secondValue` bridge;
* use `IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight_abs_le`;
* use `IntervalDomainRegularityBootstrap.reciprocalSquareTerm_summable`;
* lower-bound `t` by `c + 1` in the denominator. -/
private theorem heatDu_tail_linf_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ∃ CΔ : ℝ, 0 ≤ CΔ ∧
      ∀ t : ℝ, c + 1 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |heatDu u₀ t x| ≤ CΔ := by
  -- A good concrete constant is:
  --   CΔ = |M₀| * (4 / ((c + 1)^2 * Real.pi^2)) *
  --          (∑' n, IntervalDomainRegularityBootstrap.reciprocalSquareTerm n)
  -- The proof is an M-test / `abs_tsum_le_tsum_abs` argument.
  sorry

/-- Uniform bound for `(S(t)u₀)^(γ-1)`.

This helper should use compact min/max of the strictly positive continuous initial
profile plus Neumann heat comparison.  It is safer than using only `M_sup^(γ-1)`,
because `CM2Params` assumes `0 < γ`, not `1 ≤ γ`. -/
private theorem heatLevel0_rpow_gamma_sub_one_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ Cpow : ℝ, 0 ≤ Cpow ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) ≤ Cpow := by
  -- Get `m₀ ≤ S(t)u₀(x) ≤ M₀sup` for all positive time, then bound
  -- `r ↦ r^(p.γ - 1)` on `[m₀, M₀sup]`.
  sorry

/-- Bound the source first time-derivative coefficient on the positive-time tail. -/
private theorem heatLevel0_srcTimeCoeff_deriv_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (k : ℕ) :
    ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
      |cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
  obtain ⟨CΔ, hCΔ_nonneg, hCΔ⟩ :=
    heatDu_tail_linf_bound (u₀ := u₀) (M₀ := M₀) (c := c) hc hu₀_bound
  obtain ⟨Cpow, hCpow_nonneg, hCpow⟩ :=
    heatLevel0_rpow_gamma_sub_one_bound (p := p) (u₀ := u₀) hu₀_cont hu₀_pos
  let Csrc : ℝ := p.ν * p.γ * Cpow * CΔ
  refine ⟨2 * Csrc, fun t ht => ?_⟩
  have ht_pos : 0 < t := by linarith
  have hCsrc_nonneg : 0 ≤ Csrc := by
    dsimp [Csrc]
    positivity
  have hsrc_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x| ≤ Csrc := by
    intro x hx
    unfold srcSlice1
    -- Use `hCpow t ht_pos x hx` and `hCΔ t ht x hx` after `abs_mul`.
    -- The final arithmetic is multiplicative monotonicity with nonnegative factors.
    sorry
  have hsrc_cont : ContinuousOn
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
      (Set.Icc (0 : ℝ) 1) := by
    -- Take the time-slice of the joint continuity `hcd` returned by
    -- `heatSemigroup_d0` at time `t`.
    sorry
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hsrc_cont hCsrc_nonneg hsrc_bound k

/-- The exact `Rderiv` helper needed by the local tail proof. -/
private theorem heatLevel0_resolverTimeCoeff_deriv_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (k : ℕ) :
    ∃ BR : ℝ, ∀ t : ℝ, c + 1 < t →
      |deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t| ≤ BR := by
  obtain ⟨Bsrc, hBsrc⟩ :=
    heatLevel0_srcTimeCoeff_deriv_tail_bound
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
      hc hu₀_bound hu₀_cont hu₀_pos hfloor k
  refine ⟨|ShenWork.PDE.intervalNeumannResolverWeight p k| * Bsrc, fun t ht => ?_⟩
  have ht_pos : 0 < t := by linarith
  rw [heatLevel0_resolverTimeCoeff_deriv_eq
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor ht_pos k, abs_mul]
  exact mul_le_mul_of_nonneg_left (hBsrc t ht) (abs_nonneg _)

end ShenWork.Paper2.HeatResolverJointC2Direct
```

## Drop-in replacement for the local block

Once `heatLevel0_resolverTimeCoeff_deriv_tail_bound` exists, the local `hR_deriv_bounded` becomes:

```lean
have hR_deriv_bounded : ∃ B_R' : ℝ, ∀ t : ℝ, c + 1 < t →
    |deriv R t| ≤ B_R' := by
  simpa [R] using
    heatLevel0_resolverTimeCoeff_deriv_tail_bound
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
      hc hu₀_bound hu₀_cont hu₀_pos hfloor k
```

The existing wrapper after this is right:

```lean
obtain ⟨B_R', hB_R'⟩ := hR_deriv_bounded
refine ⟨B_R', fun t ht => ?_⟩
rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
simp only [iteratedDeriv_succ', iteratedDeriv_zero, Real.norm_eq_abs]
have hev : A =ᶠ[𝓝 t] R := by
  filter_upwards [Ioi_mem_nhds (show c < t by linarith)] with s hs
  show smoothRightCutoff (c / 2) c s * R s = R s
  rw [smoothRightCutoff_eq_one_of_ge (by linarith : c / 2 < c) (le_of_lt hs)]
  exact one_mul _
rw [Filter.EventuallyEq.deriv_eq hev]
exact hB_R' t ht
```

## Important correction to the old comment

The old comment says:

```text
‖srcSlice1(t)‖∞ ≤ νγ·M_sup^{γ-1}·‖Δu(t)‖∞
```

That is only safe if `1 ≤ γ`, or if a uniform positive lower bound for `S(t)u₀` is also carried.  `CM2Params` only has `0 < γ`.  The robust bound should use both a compact positive lower bound and an upper bound for the heat semigroup, then bound `r^(γ-1)` on that positive compact interval.

## Bottom line

For `Q1803/Rderiv`, add:

```lean
heatLevel0_srcTimeCoeff_hasDerivAt
heatLevel0_resolverTimeCoeff_hasDerivAt
heatLevel0_resolverTimeCoeff_deriv_eq
heatLevel0_resolverTimeCoeff_deriv_tail_bound
```

Then `hR_deriv_bounded` is one `simpa [R]` call, and the `hA1_tail` proof remains the existing cutoff-localization argument.
