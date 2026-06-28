# Q2071 (cron1) — `summable` response for `/tmp/q_cron1_summable.txt`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt references:

```text
Q2071 (cron1): cron1 /tmp/q_cron1_summable.txt
```

That local `/tmp/...` file is not readable through the GitHub connector, and the delivery rules prohibit using the sandbox, Python/code-interpreter, `/mnt/data`, or any sandbox file. I therefore used only the GitHub connector and inspected the current repository state.

The likely target is the `Summable`/majorant subgoal in the `heatDu` tail estimate inside:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

Current local code has the fragile line:

```lean
refine (abs_tsum_le_tsum_of_abs_le (fun n => ?_) (heig_summ.mul_left M₀)).trans ?_
```

This can fail because Lean has to infer the majorant function `g` through a large expression containing scalar multiplication, exponential damping, and later `tsum_mul_left`. The robust fix is to **name the base sequence and the majorant sequence**, prove their summability separately, and pass all implicit arguments to `abs_tsum_le_tsum_of_abs_le` explicitly.

## Drop-in replacement for the `hDu_bound` body

Replace the current inner `hDu_bound` proof with this version. It keeps the same mathematical estimate, but avoids fragile summability inference.

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

-- This block belongs in the local context of `cutoffResolverMajorant_bddAbove_direct`,
-- inside the `i = 1` branch, replacing:
--
--   have hDu_bound : ∃ CΔ : ℝ, 0 ≤ CΔ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
--       |heatDu u₀ t x| ≤ CΔ := by
--     ...
--
-- It assumes the surrounding variables/hypotheses:
--   c M₀ u₀ hu₀_bound

have hDu_bound : ∃ CΔ : ℝ, 0 ≤ CΔ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
    |heatDu u₀ t x| ≤ CΔ := by
  have hc1 : 0 < c + 1 := by linarith
  let base : ℕ → ℝ := fun n =>
    unitIntervalCosineEigenvalue n *
      Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)
  let maj : ℕ → ℝ := fun n => M₀ * base n
  let CΔ : ℝ := M₀ * ∑' n : ℕ, base n

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

  have hCΔ_nonneg : 0 ≤ CΔ := by
    dsimp [CΔ]
    exact mul_nonneg hM₀_nonneg (tsum_nonneg hbase_nonneg)

  refine ⟨CΔ, hCΔ_nonneg, fun t ht x => ?_⟩
  have ht_pos : 0 < t := by linarith

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

  calc
    |∑' n : ℕ, term n| ≤ ∑' n : ℕ, maj n := by
      exact abs_tsum_le_tsum_of_abs_le
        (f := term) (g := maj) hterm_le hmaj_summable
    _ = CΔ := by
      dsimp [CΔ, maj, base]
      rw [tsum_mul_left]

end ShenWork.Paper2.HeatResolverJointC2Direct

end -- noncomputable section
```

## Why this fixes the summability problem

The old line asks Lean to infer the majorant from:

```lean
heig_summ.mul_left M₀
```

while the termwise proof is still being elaborated. When the majorant is hidden inside expressions like:

```lean
M₀ * (unitIntervalCosineEigenvalue n * Real.exp (...))
```

Lean can infer the wrong shape, for example with the scalar on the right:

```lean
unitIntervalCosineEigenvalue n * Real.exp (...) * M₀
```

or it can leave a metavariable for the summable sequence. Naming the sequences fixes that:

```lean
let base n := λₙ * exp (-(c+1)λₙ)
let maj n := M₀ * base n
```

Then the summability proof is completely explicit:

```lean
have hbase_summable : Summable base := by
  simpa [base] using
    ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable hc1

have hmaj_summable : Summable maj := by
  simpa [maj, base, mul_assoc] using hbase_summable.mul_left M₀
```

and the `abs_tsum` helper is called with explicit implicit arguments:

```lean
exact abs_tsum_le_tsum_of_abs_le
  (f := term) (g := maj) hterm_le hmaj_summable
```

That removes the inference ambiguity.

## If the final `rw [tsum_mul_left]` goes the wrong way

Depending on the local Mathlib snapshot, `tsum_mul_left` may rewrite in the opposite direction. Replace the final equality with one of these variants.

```lean
    _ = CΔ := by
      dsimp [CΔ, maj, base]
      simpa using
        (tsum_mul_left M₀
          (fun n : ℕ => unitIntervalCosineEigenvalue n *
            Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)))
```

If the theorem expects named arguments:

```lean
    _ = CΔ := by
      dsimp [CΔ, maj, base]
      simpa using
        (tsum_mul_left
          (a := M₀)
          (f := fun n : ℕ => unitIntervalCosineEigenvalue n *
            Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)))
```

If the theorem in this snapshot states the equality in the reverse orientation, use `.symm`:

```lean
    _ = CΔ := by
      dsimp [CΔ, maj, base]
      simpa using
        (tsum_mul_left M₀
          (fun n : ℕ => unitIntervalCosineEigenvalue n *
            Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n))).symm
```

The repository already uses `rw [tsum_mul_left]` successfully nearby, so the first version should usually work.

## If `change |∑' n, term n| ≤ CΔ` does not match

Sometimes unfolding `heatDu` leaves a slightly different syntactic shape. Use this instead:

```lean
  change |∑' n : ℕ,
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n| ≤ CΔ

  let term : ℕ → ℝ := fun n =>
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n

  change |∑' n : ℕ, term n| ≤ CΔ
```

The rest of the proof is unchanged.

## Minimal local patch if you want to keep the old structure

If you want the smallest edit around the old line, insert these named facts immediately before the `refine (abs_tsum...)` line:

```lean
let base : ℕ → ℝ := fun n =>
  unitIntervalCosineEigenvalue n *
    Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)
let maj : ℕ → ℝ := fun n => M₀ * base n
have hbase_summable : Summable base := by
  simpa [base] using heig_summ
have hmaj_summable : Summable maj := by
  simpa [maj, base, mul_assoc] using hbase_summable.mul_left M₀
```

Then call:

```lean
refine (abs_tsum_le_tsum_of_abs_le
  (f := fun n : ℕ =>
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n)
  (g := maj) (fun n => ?_) hmaj_summable).trans ?_
```

and end with:

```lean
· dsimp [maj_sum, maj, base]
  rw [tsum_mul_left]
```

The full replacement above is safer because it also names `term`, making the termwise absolute-value proof easier to elaborate.
