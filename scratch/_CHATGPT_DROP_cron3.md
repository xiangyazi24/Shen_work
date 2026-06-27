# Q1254 (cron3): `heatLaplacianTerm_hasDerivAt_time`

## Target

In `ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean`, the local theorem currently has this shape:

```lean
local notation "λ_" n => unitIntervalCosineEigenvalue n

private theorem heatLaplacianTerm_hasDerivAt_time
    (a : ℕ → ℝ) (x t : ℝ) (n : ℕ) :
    HasDerivAt
      (fun τ : ℝ =>
        ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight τ x n * a n)
      ((λ_ n) ^ 2 * (Real.exp (-t * (λ_ n)) * a n) * ShenWork.CosineSpectrum.cosineMode n x) t := by
  sorry
```

The proof is just the scalar chain rule for

```text
τ ↦ -λ_n * exp(-τ λ_n) * cos(nπx) * a_n.
```

The derivative is

```text
λ_n^2 * exp(-t λ_n) * cos(nπx) * a_n.
```

## Replacement proof body

Use this as the body of the theorem:

```lean
  let lam : ℝ := λ_ n

  -- derivative of the linear exponent `τ ↦ -τ * lam`
  have hlin : HasDerivAt (fun τ : ℝ => -τ * lam) (-lam) t := by
    have hneg : HasDerivAt (fun τ : ℝ => -τ) (-1 : ℝ) t := by
      simpa using (hasDerivAt_id t).neg
    simpa [lam] using hneg.mul_const lam

  -- derivative of `τ ↦ exp (-τ * lam)`
  have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-τ * lam))
      ((-lam) * Real.exp (-t * lam)) t := by
    simpa using hlin.exp

  -- Multiply by the constants `cos(nπx)`, `-lam`, and `a n`.
  have hterm :
      HasDerivAt
        (fun τ : ℝ =>
          (-lam) * (Real.exp (-τ * lam) *
            ShenWork.CosineSpectrum.cosineMode n x) * a n)
        (((-lam) * (((-lam) * Real.exp (-t * lam)) *
            ShenWork.CosineSpectrum.cosineMode n x)) * a n) t := by
    simpa [mul_assoc] using
      (((hexp.mul_const (ShenWork.CosineSpectrum.cosineMode n x)).const_mul (-lam)).mul_const (a n))

  -- Unfold the Laplacian point-weight and normalize the algebra.
  convert hterm using 1
  · ext τ
    simp [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
      unitIntervalCosineHeatPointWeight, unitIntervalCosineMode,
      ShenWork.CosineSpectrum.cosineMode, lam]
    ring
  · simp [lam]
    ring
```

## Full theorem snippet with imports

```lean
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate
import ShenWork.PDE.HasDerivWithinAtTsum
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On
import ShenWork.Paper2.IntervalMildRegularityBootstrap

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice sliceFam FlooredSourceTimeData)
open ShenWork.IntervalFlooredSourceTimeDataIterate
  (srcSlice1 srcSlice2 hasDerivAt_srcSlice hasDerivAt_srcSlice1)
open ShenWork.IntervalPicardLevel0SourceTimeC1On
  (heatCoeff heatSlice_field_hasDerivWithinAt heatSlice_profile_jointContinuousOn
   heatSlice_secondValue_jointContinuousOn)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

local notation "λ_" n => unitIntervalCosineEigenvalue n

private theorem heatLaplacianTerm_hasDerivAt_time
    (a : ℕ → ℝ) (x t : ℝ) (n : ℕ) :
    HasDerivAt
      (fun τ : ℝ =>
        ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight τ x n * a n)
      ((λ_ n) ^ 2 * (Real.exp (-t * (λ_ n)) * a n) * ShenWork.CosineSpectrum.cosineMode n x) t := by
  let lam : ℝ := λ_ n

  -- derivative of the linear exponent `τ ↦ -τ * lam`
  have hlin : HasDerivAt (fun τ : ℝ => -τ * lam) (-lam) t := by
    have hneg : HasDerivAt (fun τ : ℝ => -τ) (-1 : ℝ) t := by
      simpa using (hasDerivAt_id t).neg
    simpa [lam] using hneg.mul_const lam

  -- derivative of `τ ↦ exp (-τ * lam)`
  have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-τ * lam))
      ((-lam) * Real.exp (-t * lam)) t := by
    simpa using hlin.exp

  -- Multiply by the constants `cos(nπx)`, `-lam`, and `a n`.
  have hterm :
      HasDerivAt
        (fun τ : ℝ =>
          (-lam) * (Real.exp (-τ * lam) *
            ShenWork.CosineSpectrum.cosineMode n x) * a n)
        (((-lam) * (((-lam) * Real.exp (-t * lam)) *
            ShenWork.CosineSpectrum.cosineMode n x)) * a n) t := by
    simpa [mul_assoc] using
      (((hexp.mul_const (ShenWork.CosineSpectrum.cosineMode n x)).const_mul (-lam)).mul_const (a n))

  -- Unfold the Laplacian point-weight and normalize the algebra.
  convert hterm using 1
  · ext τ
    simp [ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
      unitIntervalCosineHeatPointWeight, unitIntervalCosineMode,
      ShenWork.CosineSpectrum.cosineMode, lam]
    ring
  · simp [lam]
    ring

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

## Notes

The proof deliberately differentiates only `Real.exp (-τ * lam)`. Everything else is constant in `τ`. The final `convert` is needed because the named point-weight unfolds to the same expression but with slightly different associativity and because the target derivative is written as `λ_n ^ 2 * (exp * a_n) * cos(nπx)` rather than `(-λ_n) * ((-λ_n) * exp * cos) * a_n`.
