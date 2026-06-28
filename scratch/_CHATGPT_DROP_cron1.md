# Q1983 (cron1) — `product` response for `/tmp/q_cron1_product.txt`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt references:

```text
Q1983 (cron1): cron1 /tmp/q_cron1_product.txt
```

That local `/tmp/...` file is not readable through the GitHub connector, and the delivery rules prohibit using the sandbox, Python/code-interpreter, `/mnt/data`, or any sandbox file. I therefore used only the GitHub connector and inspected the current repository state.

The likely target is the product-estimate subgoal inside the remaining `hBsrc` sorry in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

Specifically, after obtaining:

```lean
hpow_le : ∀ t, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
  (intervalDomainLift (u t) x) ^ (p.γ - 1) ≤ Bpow

hDu : ∀ t : ℝ, c + 1 < t → ∀ x : ℝ, |heatDu u₀ t x| ≤ CΔ
```

you need to prove the pointwise bound for the product appearing in `srcSlice1`:

```lean
|p.ν * p.γ * u(t,x)^(p.γ - 1) * heatDu u₀ t x| ≤
  p.ν * p.γ * Bpow * CΔ
```

The important details are:

1. Use `abs_mul` to expose the product.
2. Rewrite `|p.ν|` and `|p.γ|` with `abs_of_pos p.hν` and `abs_of_pos p.hγ`.
3. Rewrite `|u^(γ-1)|` with `abs_of_nonneg`, using positivity of `u` and `Real.rpow_nonneg`.
4. Prove the core two-factor estimate with `mul_le_mul`.
5. Multiply by the nonnegative scalar `p.ν * p.γ`.

## Drop-in product block for `hsrc_bound`

Use this as the body of the local pointwise-bound proof:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant
   boundedWeightJointTerm_contDiff boundedWeightJointTerm_iteratedFDeriv_le)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data)
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
  (norm_iteratedFDeriv_comp_fst_le)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatD2u heatSemigroup_d0 heatSemigroup_d1)
open ShenWork.IntervalResolverSpectralJointC2Cutoff (smoothRightCutoff
  smoothRightCutoff_contDiff smoothRightCutoff_eq_zero_of_le
  smoothRightCutoff_eq_one_of_ge smoothRightCutoff_eventually_eq_one)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

-- This block belongs inside:
--   have hsrc_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
--       |srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x| ≤ Bpt := by
-- after `intro x hx`, and in a context containing:
--   u := conjugatePicardIter p u₀ 0
--   Bpt := p.ν * p.γ * Bpow * CΔ
--   ht_pos : 0 < t
--   ht_tail : c + 1 < t
--   hm0_pos, hprofile_lower, hpow_le, hDu, hCΔ_nn, hBpow_nonneg

have hu_pos : 0 < intervalDomainLift (u t) x :=
  lt_of_lt_of_le hm0_pos (hprofile_lower t ht_pos x hx)

have hpow_nonneg : 0 ≤ (intervalDomainLift (u t) x) ^ (p.γ - 1) :=
  Real.rpow_nonneg hu_pos.le _

have hdu_abs_nonneg : 0 ≤ |heatDu u₀ t x| := abs_nonneg _

have hsmall :
    (intervalDomainLift (u t) x) ^ (p.γ - 1) * |heatDu u₀ t x| ≤
      Bpow * CΔ := by
  exact mul_le_mul
    (hpow_le t ht_pos x hx)
    (hDu t ht_tail x)
    hCΔ_nn
    hpow_nonneg

unfold srcSlice1
change |p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) *
    heatDu u₀ t x| ≤ Bpt
rw [abs_mul, abs_mul, abs_mul,
  abs_of_pos p.hν, abs_of_pos p.hγ, abs_of_nonneg hpow_nonneg]
calc
  p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * |heatDu u₀ t x|
      = (p.ν * p.γ) *
          ((intervalDomainLift (u t) x) ^ (p.γ - 1) * |heatDu u₀ t x|) := by
          ring
  _ ≤ (p.ν * p.γ) * (Bpow * CΔ) := by
          exact mul_le_mul_of_nonneg_left hsmall
            (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ))
  _ = Bpt := by
          dsimp [Bpt]
          ring

end ShenWork.Paper2.HeatResolverJointC2Direct

end -- noncomputable section
```

## If `change` does not match

If the line

```lean
change |p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) *
    heatDu u₀ t x| ≤ Bpt
```

does not match because the local `set u := ...` is not unfolding in the expected direction, use this variant:

```lean
unfold srcSlice1
show |p.ν * p.γ *
    (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) *
      heatDu u₀ t x| ≤ Bpt
change |p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) *
    heatDu u₀ t x| ≤ Bpt
```

If Lean still refuses to recognize the `u` abbreviation, avoid `change` entirely and add `simp only [u]` at the `show` line:

```lean
unfold srcSlice1
show |p.ν * p.γ *
    (intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) ^ (p.γ - 1) *
      heatDu u₀ t x| ≤ Bpt
rw [abs_mul, abs_mul, abs_mul,
  abs_of_pos p.hν, abs_of_pos p.hγ]
```

Then replace every occurrence of `intervalDomainLift (u t) x` in the subsequent `calc` with:

```lean
intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

The proof is identical; only the local abbreviation changes.

## Closing the coefficient bound after the product block

After the pointwise product bound and the `ContinuousOn` proof from Q1903, the coefficient estimate closes as follows. This assumes you are proving:

```lean
have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
    |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
```

and have already set:

```lean
set Bpt : ℝ := p.ν * p.γ * Bpow * CΔ
have hBpt_nonneg : 0 ≤ Bpt := by
  dsimp [Bpt]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ)) hBpow_nonneg)
    hCΔ_nn
```

Use:

```lean
refine ⟨2 * Bpt, fun t ht_tail => ?_⟩
have ht_pos : 0 < t := by linarith [hc, ht_tail]

have hsrc_cont : ContinuousOn
    (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
    (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨δt, hδt, _hsrc, _hderiv, hsrc1_joint⟩ :=
    heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor t ht_pos
  have ht_mem : t ∈ Set.Icc (t - δt) (t + δt) := by
    exact ⟨by linarith, by linarith⟩
  simpa [Function.uncurry] using
    hsrc1_joint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mem_prod.mpr ⟨ht_mem, hx⟩)

have hsrc_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x| ≤ Bpt := by
  intro x hx
  -- paste the product block from the previous section here

exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
  hsrc_cont hBpt_nonneg hsrc_bound k
```

The repository already uses this coefficient-bound lemma in the nearby `i = 0` tail proof, so the expected output is `≤ 2 * Bpt`, matching the witness `⟨2 * Bpt, ...⟩`.

## Why this is the right product proof

The central monotonicity step is:

```lean
u^(γ-1) * |heatDu| ≤ Bpow * CΔ
```

This is a valid `mul_le_mul` application because:

```lean
u^(γ-1) ≤ Bpow
|heatDu| ≤ CΔ
0 ≤ CΔ
0 ≤ u^(γ-1)
```

Then multiplication by `p.ν * p.γ` is order-preserving because both parameters are strictly positive:

```lean
0 ≤ p.ν * p.γ
```

This avoids the common mistake of trying to let `ring` or `nlinarith` solve the whole inequality after `abs_mul`; the inequality is not algebraic until the two monotonicity steps have been supplied explicitly.
