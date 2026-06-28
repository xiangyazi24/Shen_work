# Q2108 (cron1) — summability response for `/tmp/codex_summability.md`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt references a local file:

```text
/tmp/codex_summability.md
```

That path is not part of the GitHub repository and is not readable through the GitHub connector. The delivery rules also explicitly prohibit using Python, the sandbox, `/mnt/data`, or any local-file fallback. I therefore used only the GitHub connector.

I searched the repository for `codex_summability`/`summability` context and found no repository file corresponding to `/tmp/codex_summability.md`. The visible repository context points to the same summability bottleneck in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

namely the `hDu_bound` proof inside `cutoffResolverMajorant_bddAbove_direct`, around the line:

```lean
refine (abs_tsum_le_tsum_of_abs_le (fun n => ?_) (heig_summ.mul_left M₀)).trans ?_
```

The robust fix is still: **do not ask Lean to infer the majorant sequence through `heig_summ.mul_left M₀` while the pointwise bound is being elaborated. Name the sequence being summed and name the majorant sequence.**

## Recommended local proof shape

The cleanest version avoids the final `tsum_mul_left` normalization entirely. Instead of choosing

```lean
maj_sum = M₀ * ∑' n, base n
```

choose the witness as

```lean
CΔ = ∑' n, maj n
```

where

```lean
base n = λₙ * exp (-(c+1) * λₙ)
maj n  = M₀ * base n
```

Then `abs_tsum_le_tsum_of_abs_le` closes directly with `(g := maj)` and `hmaj_summable`; no scalar-tsum rewrite is needed at the end.

## Drop-in replacement for the `hDu_bound` block

This block is meant to replace only the local proof of:

```lean
have hDu_bound : ∃ CΔ : ℝ, 0 ≤ CΔ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
    |heatDu u₀ t x| ≤ CΔ := by
  ...
```

inside `cutoffResolverMajorant_bddAbove_direct`. The imports shown are the file-level imports already needed by the surrounding file.

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
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

-- Local replacement block, to be pasted where the existing `hDu_bound` proof occurs.
have hDu_bound : ∃ CΔ : ℝ, 0 ≤ CΔ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
    |heatDu u₀ t x| ≤ CΔ := by
  have hc1 : 0 < c + 1 := by
    linarith

  let base : ℕ → ℝ := fun n =>
    unitIntervalCosineEigenvalue n *
      Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)
  let maj : ℕ → ℝ := fun n => M₀ * base n
  let CΔ : ℝ := ∑' n : ℕ, maj n

  have hM₀_nonneg : 0 ≤ M₀ :=
    le_trans (abs_nonneg _) (hu₀_bound 0)

  have hbase_summable : Summable base := by
    simpa [base] using
      ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
        hc1

  have hmaj_summable : Summable maj := by
    simpa [maj, base, mul_assoc] using hbase_summable.mul_left M₀

  have hbase_nonneg : ∀ n : ℕ, 0 ≤ base n := by
    intro n
    dsimp [base]
    exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _)

  have hmaj_nonneg : ∀ n : ℕ, 0 ≤ maj n := by
    intro n
    dsimp [maj]
    exact mul_nonneg hM₀_nonneg (hbase_nonneg n)

  refine ⟨CΔ, tsum_nonneg hmaj_nonneg, fun t ht x => ?_⟩

  have ht_pos : 0 < t := by
    linarith

  simp only [heatDu, if_pos ht_pos]
  unfold ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue

  let term : ℕ → ℝ := fun n =>
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n

  change |∑' n : ℕ, term n| ≤ CΔ

  have hterm_le : ∀ n : ℕ, |term n| ≤ maj n := by
    intro n
    dsimp [term, maj, base]
    unfold ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight
    rw [abs_mul, abs_mul, abs_neg]

    have heig_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity

    have hpw_le : |unitIntervalCosineHeatPointWeight t x n| ≤
        Real.exp (-t * unitIntervalCosineEigenvalue n) := by
      unfold unitIntervalCosineHeatPointWeight
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)

    have hexp_le : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
        Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) := by
      apply Real.exp_le_exp.mpr
      have hmul : (c + 1) * unitIntervalCosineEigenvalue n ≤
          t * unitIntervalCosineEigenvalue n :=
        mul_le_mul_of_nonneg_right (le_of_lt ht) heig_nn
      linarith

    have hcoeff_le : |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀ :=
      hu₀_bound n

    calc
      |unitIntervalCosineEigenvalue n| *
          |unitIntervalCosineHeatPointWeight t x n| *
          |cosineCoeffs (intervalDomainLift u₀) n|
          ≤ unitIntervalCosineEigenvalue n *
              Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by
              rw [abs_of_nonneg heig_nn]
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left hpw_le heig_nn)
                hcoeff_le
                (abs_nonneg _)
                (mul_nonneg heig_nn (Real.exp_nonneg _))
      _ ≤ unitIntervalCosineEigenvalue n *
              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) * M₀ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hexp_le heig_nn)
                hM₀_nonneg
      _ = M₀ *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)) := by
              ring

  exact abs_tsum_le_tsum_of_abs_le
    (f := term) (g := maj) hterm_le hmaj_summable

end ShenWork.Paper2.HeatResolverJointC2Direct

end
```

## Why this is better than the original line

The original line:

```lean
refine (abs_tsum_le_tsum_of_abs_le (fun n => ?_) (heig_summ.mul_left M₀)).trans ?_
```

is mathematically fine, but elaboration is fragile because Lean must infer the hidden `g : ℕ → ℝ` from `heig_summ.mul_left M₀` while the pointwise goal is simultaneously being transformed by `rw [abs_mul, abs_mul, abs_neg]`, ring-normalization, and scalar reassociation.

The replacement makes all of the hidden objects explicit:

```lean
let base : ℕ → ℝ := fun n => λₙ * exp (-(c+1) * λₙ)
let maj  : ℕ → ℝ := fun n => M₀ * base n
have hmaj_summable : Summable maj := ...
exact abs_tsum_le_tsum_of_abs_le (f := term) (g := maj) hterm_le hmaj_summable
```

That removes the majorant inference problem completely.

## If you want to preserve the old witness `M₀ * ∑' base`

If some downstream proof or readability reason prefers the old witness shape, keep `CΔ := M₀ * ∑' n, base n`, but still name `base` and `maj`. Then after applying `abs_tsum_le_tsum_of_abs_le`, close the final equality explicitly:

```lean
  calc
    |∑' n : ℕ, term n| ≤ ∑' n : ℕ, maj n := by
      exact abs_tsum_le_tsum_of_abs_le
        (f := term) (g := maj) hterm_le hmaj_summable
    _ = M₀ * ∑' n : ℕ, base n := by
      dsimp [maj]
      simpa using (tsum_mul_left M₀ base)
```

If this Mathlib snapshot has the theorem oriented the other way, use:

```lean
      simpa using (tsum_mul_left M₀ base).symm
```

But the `CΔ := ∑' maj` version is preferable because it avoids orientation issues entirely.

## Secondary small fix

The exponential monotonicity proof should use `Real.exp_le_exp.mpr` plus an explicit multiplication inequality:

```lean
have hexp_le : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
    Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) := by
  apply Real.exp_le_exp.mpr
  have hmul : (c + 1) * unitIntervalCosineEigenvalue n ≤
      t * unitIntervalCosineEigenvalue n :=
    mul_le_mul_of_nonneg_right (le_of_lt ht) heig_nn
  linarith
```

This is more robust than asking `nlinarith` to solve the negated product inequality directly after `Real.exp_le_exp_of_le`.

## Bottom line

Use the named-majorant version. It is a local proof-engineering patch: no mathematical content changes, no new theorem is required, and it avoids Lean's brittle summability metavariable inference at exactly the failing point.
