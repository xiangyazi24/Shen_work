# Q2114 (cron1) — summability response for `/tmp/codex_summability.md`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt references a local file:

```text
/tmp/codex_summability.md
```

That path is not part of the GitHub repository and is not readable through the GitHub connector. The delivery rules explicitly prohibit using Python, code-interpreter, the sandbox, `/mnt/data`, or any local-file fallback. I therefore used only the GitHub connector.

A connector search for `codex_summability` in `xiangyazi24/Shen_work` found no repository file corresponding to that local `/tmp` path. The repository-visible summability issue is the same local bottleneck in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

inside the `hDu_bound` proof used in `cutoffResolverMajorant_bddAbove_direct`, where the fragile line is:

```lean
refine (abs_tsum_le_tsum_of_abs_le (fun n => ?_) (heig_summ.mul_left M₀)).trans ?_
```

The proof idea is mathematically correct, but the elaboration is brittle: Lean has to infer the hidden majorant `g : ℕ → ℝ` from `heig_summ.mul_left M₀` while the termwise proof is still changing shape under `rw [abs_mul, abs_mul, abs_neg]`, reassociation, and the final `tsum_mul_left` rewrite.

## Deterministic fix

Name all three relevant objects:

```lean
base n = λₙ * exp (-(c+1) * λₙ)
maj n  = M₀ * base n
CΔ     = ∑' n, maj n
```

Then call the local helper with explicit implicit arguments:

```lean
exact abs_tsum_le_tsum_of_abs_le
  (f := term) (g := maj) hterm_le hmaj_summable
```

This avoids both hard parts:

1. Lean no longer has to infer the majorant sequence from `heig_summ.mul_left M₀`.
2. There is no final scalar-tsum normalization goal, because the witness is already `∑' maj`.

## Drop-in replacement for the local `hDu_bound`

Paste this where the current local proof of `hDu_bound` occurs. The imports below are the file-level imports already present or needed by the surrounding file; the actual replacement block begins at `have hDu_bound`.

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

  have hCΔ_nonneg : 0 ≤ CΔ := by
    dsimp [CΔ]
    exact tsum_nonneg hmaj_nonneg

  refine ⟨CΔ, hCΔ_nonneg, fun t ht x => ?_⟩

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

## If the `change` line does not match

Depending on how much unfolding Lean performs before the local goal, this line:

```lean
change |∑' n : ℕ, term n| ≤ CΔ
```

may fail because the expression is not syntactically the same as `term`. In that case, use the two-step explicit version:

```lean
  change |∑' n : ℕ,
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n| ≤ CΔ

  let term : ℕ → ℝ := fun n =>
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n

  change |∑' n : ℕ, term n| ≤ CΔ
```

Then keep the rest of the proof unchanged.

## If `Real.exp_le_exp.mpr` is unavailable in this Mathlib snapshot

The current source nearby already uses `Real.exp_le_exp_of_le`. If the `.mpr` form is rejected, replace the `hexp_le` proof with:

```lean
    have hexp_le : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
        Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) := by
      apply Real.exp_le_exp_of_le
      have hmul : (c + 1) * unitIntervalCosineEigenvalue n ≤
          t * unitIntervalCosineEigenvalue n :=
        mul_le_mul_of_nonneg_right (le_of_lt ht) heig_nn
      linarith
```

This avoids a fragile `nlinarith [heig_nn]` on the negated product expression.

## If you must keep the old witness shape

If later code expects the witness to be exactly:

```lean
M₀ * ∑' n, base n
```

then keep the named `base`/`maj` setup but close the final step explicitly:

```lean
  let CΔ : ℝ := M₀ * ∑' n : ℕ, base n
  ...
  calc
    |∑' n : ℕ, term n| ≤ ∑' n : ℕ, maj n := by
      exact abs_tsum_le_tsum_of_abs_le
        (f := term) (g := maj) hterm_le hmaj_summable
    _ = CΔ := by
      dsimp [CΔ, maj]
      simpa using (tsum_mul_left M₀ base)
```

If orientation differs, use:

```lean
      simpa using (tsum_mul_left M₀ base).symm
```

But for this local existential proof, `CΔ := ∑' n, maj n` is simpler and more deterministic.

## Bottom line

The fix is local proof engineering, not new analysis. The sequence `λₙ exp (-(c+1)λₙ)` is already summable; multiplying by `M₀` is already summable. The only problem is elaboration pressure from an anonymous majorant. Name the majorant, call `abs_tsum_le_tsum_of_abs_le` with `(f := term) (g := maj)`, and choose the existential constant as `∑' maj` to avoid any final `tsum_mul_left` orientation issue.
