# Q1803 (cron1) -- `Rderiv` tail bound

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1803 (cron1): cron1 /tmp/q_cron1_Rderiv.txt
```

The local file `/tmp/q_cron1_Rderiv.txt` was not present in the runtime I can inspect, and it is not readable through the GitHub connector. I therefore used the repository state and the file name `Rderiv` to identify the relevant live gap.

I did **not** use Python, `/mnt/data`, the sandbox, or any sandbox link. I did not run Lean locally.

## Inferred target

The relevant gap is in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

inside:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
```

in the `i = 1` tail branch:

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

The right fix is **not** to use `ContDiffAt` opaquely.  The current file already proves the source coefficient `ContDiffAt` theorem by constructing the exact first derivative internally.  Extract that internal `hd0` proof as a named `HasDerivAt` lemma, then transfer it across the constant elliptic resolver weight.

The core derivative identity should be:

```lean
deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t =
  ShenWork.PDE.intervalNeumannResolverWeight p k *
    cosineCoeffs
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k
```

for `0 < t`.

After that, `hR_deriv_bounded` is a bounded-coefficient estimate for the coefficient of `srcSlice1`, not a new resolver regularity problem.

## Minimal helper sequence

Add these helpers near the existing Layer 1 / Layer 2 block in `IntervalHeatResolverJointC2.lean`, just before `heatLevel0_srcTimeCoeff_contDiffAt_two` or immediately after it.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice srcTimeCoeff_eq_cosineCoeffs)
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

/-- Convenient `deriv`-rewrite form for the tail estimate. -/
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

The first lemma is almost literally lines from the existing proof of `heatLevel0_srcTimeCoeff_contDiffAt_two`; extracting it is low risk and avoids re-proving `ContDiffAt` machinery.

## The missing bound should be factored once

Do not inline all of the heat-Laplacian estimate inside `hR_deriv_bounded`.  Add one source-side tail helper.

Suggested shape:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalDomainRegularityBootstrap

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData (heatDu)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Uniform bound for the heat Laplacian tail.  This is the reusable form of the
`unitIntervalCosineHeatSecondPointWeight_abs_le` argument.

Implementation notes:
* unfold `heatDu` at `0 < t`;
* rewrite it to `unitIntervalCosineHeatSecondValue` or make the existing private
  `heatDu_eq_secondValue` public;
* use `unitIntervalCosineHeatSecondPointWeight_abs_le`;
* use `reciprocalSquareTerm_summable` and the coefficient bound `hu₀_bound`;
* replace `t` by the lower bound `c + 1` in the denominator. -/
private theorem heatDu_tail_linf_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ∃ CΔ : ℝ, 0 ≤ CΔ ∧
      ∀ t : ℝ, c + 1 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |heatDu u₀ t x| ≤ CΔ := by
  -- Concrete constant:
  --   CΔ = |M₀| * (4 / ((c + 1)^2 * Real.pi^2)) *
  --          (∑' n, IntervalDomainRegularityBootstrap.reciprocalSquareTerm n)
  -- The proof is a standard `abs_tsum_le_tsum_abs` / `Summable.of_norm_bounded`
  -- argument using `unitIntervalCosineHeatSecondPointWeight_abs_le`.
  -- If this is painful because `heatDu_eq_secondValue` is private, make that lemma
  -- public in `IntervalHeatSemigroupFlooredSourceTimeData.lean`.
  sorry

/-- Uniform bound for `(S(t)u₀)^(γ-1)` on the whole positive-time tail.

This helper is safer than writing `M_sup^(γ-1)` directly, because `CM2Params` only
assumes `0 < γ`, not `1 ≤ γ`.  Use compact min/max of the positive continuous
initial datum and the Neumann heat semigroup comparison principle:

* `m₀ ≤ S(t)u₀(x) ≤ M₀sup` for all `t > 0`, `x ∈ [0,1]`;
* then bound `r ↦ r^(γ-1)` on `[m₀, M₀sup]` by a finite constant. -/
private theorem heatLevel0_rpow_gamma_sub_one_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x) :
    ∃ Cpow : ℝ, 0 ≤ Cpow ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) ≤ Cpow := by
  -- Use min/max of `u₀` on compact `intervalDomainPoint`, then the heat semigroup
  -- lower/upper comparison bounds.  For the final rpow bound, either split on
  -- `0 ≤ p.γ - 1` or use compactness of `[m₀, Msup]` and continuity of `rpow` on
  -- positive reals.
  sorry

/-- Source first-time-derivative coefficient bound on the tail. -/
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
    -- Target after unfolding:
    -- |ν * γ * u^(γ-1) * heatDu| ≤ ν * γ * Cpow * CΔ.
    -- Use `hCpow t ht_pos x hx` and `hCΔ t ht x hx`.
    nlinarith [p.hν, p.hγ, hCpow_nonneg, hCΔ_nonneg,
      hCpow t ht_pos x hx, hCΔ t ht x hx]
  have hsrc_cont : ContinuousOn
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
      (Set.Icc (0 : ℝ) 1) := by
    -- This is available from the `hcd` field returned by `heatSemigroup_d0` at `t`.
    -- Take the time-slice of the joint continuity of `Function.uncurry srcSlice1`.
    -- Alternatively package this as a small helper next to `heatSemigroup_d0`.
    sorry
  exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hsrc_cont hCsrc_nonneg hsrc_bound k

/-- The exact helper needed by the local `hR_deriv_bounded` block. -/
private theorem heatLevel0_resolverTimeCoeff_deriv_tail_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k ≤ M₀)
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

There is a small typo to avoid in the final theorem statement above: the line

```lean
(hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k ≤ M₀)
```

must be:

```lean
(hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
```

I left the theorem body in the file as a patch skeleton because the two reusable analytic estimates should be separate lemmas, not hidden inside `hR_deriv_bounded`.

## Drop-in replacement for the local `hR_deriv_bounded`

Once the helper above exists, replace the current `sorry` block by:

```lean
have hR_deriv_bounded : ∃ B_R' : ℝ, ∀ t : ℝ, c + 1 < t →
    |deriv R t| ≤ B_R' := by
  simpa [R] using
    heatLevel0_resolverTimeCoeff_deriv_tail_bound
      (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
      hc hu₀_bound hu₀_cont hu₀_pos hfloor k
```

Then the existing wrapper in `hA1_tail` is correct:

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

## Why this is the right decomposition

The direct proof has three logically distinct jobs:

1. **Derivative identification**: `R' = w_k * coeff(srcSlice1)`.  This is already present implicitly in `heatLevel0_srcTimeCoeff_contDiffAt_two`; extract it.
2. **Tail boundedness of `srcSlice1`**: use heat semigroup comparison for `u^(γ-1)` and the spectral second-derivative bound for `heatDu`.
3. **Cutoff localization**: on `t > c + 1`, `smoothRightCutoff (c/2) c = 1` near `t`, so `A' = R'` by `EventuallyEq.deriv_eq`.

Only item 2 is analytic.  Items 1 and 3 are mechanical Lean infrastructure and should be named separately.

## Important correction to the old comment

The comment saying

```text
‖srcSlice1(t)‖∞ ≤ νγ·M_sup^{γ-1}·‖Δu(t)‖∞
```

is only automatically safe if `1 ≤ γ` or if a uniform positive lower bound is also carried.  `CM2Params` has only `0 < γ`.  Therefore the robust helper should bound `u^(γ-1)` using both the compact positive lower bound and upper bound for the heat semigroup, not just `M_sup`.

## Bottom line

For `Q1803/Rderiv`, add the exposed derivative lemmas:

```lean
heatLevel0_srcTimeCoeff_hasDerivAt
heatLevel0_resolverTimeCoeff_hasDerivAt
heatLevel0_resolverTimeCoeff_deriv_eq
```

then close the local `hR_deriv_bounded` via a single tail estimate:

```lean
heatLevel0_resolverTimeCoeff_deriv_tail_bound
```

This keeps `cutoffResolverMajorant_bddAbove_direct` from becoming an unmaintainable proof containing derivative extraction, heat-kernel summability, rpow lower-bound bookkeeping, and cutoff localization all at once.
