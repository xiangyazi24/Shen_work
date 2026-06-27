# Q1252 (cron2) — filling `heatDu_hasDerivAt`

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Answer

Do **not** reuse

```lean
unitIntervalCosineHeatValue_hasDerivAt_time
```

with the naive modified coefficients

```lean
fun n => -unitIntervalCosineEigenvalue n * cosineCoeffs (intervalDomainLift u₀) n
```

because the theorem requires a bounded coefficient sequence, and bounded `aₙ` does **not** imply bounded `λₙ aₙ`.

But you still do **not** need to reprove the whole `hasDerivAt_tsum_of_isPreconnected` argument.  Reuse the existing theorem with a **positive-time shift**.  At fixed `0 < t`, write, near `r = t`,

```text
heatDu u₀ r x
  = ∑ n, -λₙ exp(-r λₙ) aₙ cos(nπx)
  = unitIntervalCosineHeatValue (r - t/2)
      (fun n => -λₙ exp(-(t/2)λₙ) aₙ) x.
```

The shifted coefficient

```lean
bₙ = -λₙ * Real.exp (-(t / 2) * λₙ) * aₙ
```

**is bounded** from boundedness of `aₙ`, by the scalar spectral multiplier bound.  Then apply

```lean
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
```

at heat time `t / 2`, compose with `r ↦ r - t / 2`, and simplify the derivative series to `heatD2u`.

So the correct answer is: **yes, reuse the existing heat-value theorem, but only after shifting half the heat time into the coefficients.**  A direct `hasDerivAt_tsum_of_isPreconnected` proof is valid but unnecessary.

## Patch-style proof

In `ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean`, add this import:

```lean
import ShenWork.Paper2.IntervalSpectralMultiplierBound
```

Then place the following helper block before the current `private theorem heatDu_hasDerivAt`, and replace the `sorry` body with the theorem below.

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.Paper2.IntervalSpectralMultiplierBound

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalDomainRegularityBootstrap

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

/-- The shifted coefficient sequence used to represent `heatDu` near a positive
base time `t` as an ordinary heat-value series at time `r - t/2`. -/
private abbrev heatDuShiftCoeff
    (u₀ : intervalDomainPoint → ℝ) (t : ℝ) : ℕ → ℝ :=
  fun n => -unitIntervalCosineEigenvalue n *
    Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n

/-- The shifted coefficients are bounded for `0 < t` when the original cosine
coefficients are bounded.  This is the key reason the existing heat-value time
lemma applies after shifting half the heat time into the coefficients. -/
private theorem heatDuShiftCoeff_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (ht : 0 < t) :
    ∀ n,
      |heatDuShiftCoeff u₀ t n| ≤
        ((1 : ℝ) ^ (1 : ℝ) * Real.exp (-(1 : ℝ))) *
          ((1 : ℝ) * (t / 2)) ^ (-(1 : ℝ)) * |M₀| := by
  intro n
  have hλ_nonneg : 0 ≤ unitIntervalCosineEigenvalue n := by
    dsimp [unitIntervalCosineEigenvalue]
    positivity
  have hsmooth :=
    ShenWork.Paper2.SpectralMultiplierBound.spectral_multiplier_bound_explicit
      (θ := (1 : ℝ)) (d := (1 : ℝ)) (r := t / 2)
      (lam := unitIntervalCosineEigenvalue n)
      (by norm_num) (by norm_num) (half_pos ht) hλ_nonneg
  have hλexp :
      |(-unitIntervalCosineEigenvalue n *
          Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n))| ≤
        ((1 : ℝ) ^ (1 : ℝ) * Real.exp (-(1 : ℝ))) *
          ((1 : ℝ) * (t / 2)) ^ (-(1 : ℝ)) := by
    have hleft :
        |(-unitIntervalCosineEigenvalue n *
            Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n))| =
          unitIntervalCosineEigenvalue n ^ (1 : ℝ) *
            Real.exp (-((1 : ℝ) * (t / 2) * unitIntervalCosineEigenvalue n)) := by
      rw [abs_mul, abs_neg, abs_of_nonneg hλ_nonneg,
        abs_of_nonneg (Real.exp_nonneg _), Real.rpow_one]
      congr 1
      ring
    rw [hleft]
    exact hsmooth
  have hM : |cosineCoeffs (intervalDomainLift u₀) n| ≤ |M₀| :=
    le_trans (hu₀_bound n) (le_abs_self M₀)
  have hfactor_nonneg :
      0 ≤ ((1 : ℝ) ^ (1 : ℝ) * Real.exp (-(1 : ℝ))) *
        ((1 : ℝ) * (t / 2)) ^ (-(1 : ℝ)) := by
    positivity
  calc
    |heatDuShiftCoeff u₀ t n|
        = |(-unitIntervalCosineEigenvalue n *
            Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n)) *
              cosineCoeffs (intervalDomainLift u₀) n| := by
            rfl
    _ = |(-unitIntervalCosineEigenvalue n *
            Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n))| *
          |cosineCoeffs (intervalDomainLift u₀) n| := by
            rw [abs_mul]
    _ ≤ (((1 : ℝ) ^ (1 : ℝ) * Real.exp (-(1 : ℝ))) *
          ((1 : ℝ) * (t / 2)) ^ (-(1 : ℝ))) * |M₀| :=
            mul_le_mul hλexp hM (abs_nonneg _) hfactor_nonneg
    _ = ((1 : ℝ) ^ (1 : ℝ) * Real.exp (-(1 : ℝ))) *
          ((1 : ℝ) * (t / 2)) ^ (-(1 : ℝ)) * |M₀| := by
            ring

/-- Near `t > 0`, `heatDu` is the heat-value series with the shifted bounded
coefficients `heatDuShiftCoeff u₀ t` and heat time `r - t/2`. -/
private theorem heatDu_eq_shiftedHeatValue_eventually
    (u₀ : intervalDomainPoint → ℝ) {t x : ℝ} (ht : 0 < t) :
    (fun r : ℝ => heatDu u₀ r x) =ᶠ[𝓝 t]
      (fun r : ℝ =>
        unitIntervalCosineHeatValue (r - t / 2) (heatDuShiftCoeff u₀ t) x) := by
  filter_upwards [Metric.ball_mem_nhds t (t / 2) (half_pos ht)] with r hr
  have hrpos : 0 < r := by
    rw [Metric.mem_ball, Real.dist_eq] at hr
    have hleft := (abs_lt.mp hr).1
    linarith
  simp only [heatDu, if_pos hrpos,
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue,
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight,
    unitIntervalCosineHeatValue, unitIntervalCosineHeatPointWeight,
    heatDuShiftCoeff]
  congr 1
  ext n
  have hexp :
      Real.exp (-(r - t / 2) * unitIntervalCosineEigenvalue n) *
          Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n) =
        Real.exp (-r * unitIntervalCosineEigenvalue n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hexp]
  ring

/-- The derivative produced by the shifted heat-value theorem is exactly the
explicit `heatD2u` series. -/
private theorem shiftedHeatSecondValue_eq_heatD2u
    (u₀ : intervalDomainPoint → ℝ) {t x : ℝ} (ht : 0 < t) :
    unitIntervalCosineHeatSecondValue (t / 2) (heatDuShiftCoeff u₀ t) x =
      heatD2u u₀ t x := by
  simp only [heatD2u, if_pos ht, heatDuShiftCoeff,
    unitIntervalCosineHeatSecondValue,
    unitIntervalCosineHeatSecondPointWeight,
    unitIntervalCosineMode, ShenWork.CosineSpectrum.cosineMode]
  congr 1
  ext n
  rw [show ((n : ℝ) * Real.pi) ^ 2 = unitIntervalCosineEigenvalue n by rfl]
  have hexp :
      Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n) *
          Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n) =
        Real.exp (-t * unitIntervalCosineEigenvalue n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hexp]
  ring

/-- Time derivative of the heat-Laplacian slice. -/
private theorem heatDu_hasDerivAt
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => heatDu u₀ r x) (heatD2u u₀ t x) t := by
  classical
  let b : ℕ → ℝ := heatDuShiftCoeff u₀ t
  let Mb : ℝ :=
    ((1 : ℝ) ^ (1 : ℝ) * Real.exp (-(1 : ℝ))) *
      ((1 : ℝ) * (t / 2)) ^ (-(1 : ℝ)) * |M₀|
  have hb : ∀ n, |b n| ≤ Mb := by
    simpa [b, Mb] using heatDuShiftCoeff_bound _hu₀_bound ht
  have hheat :
      HasDerivAt
        (fun s : ℝ => unitIntervalCosineHeatValue s b x)
        (unitIntervalCosineHeatSecondValue (t / 2) b x)
        (t / 2) :=
    ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
      (r := t / 2) (x := x) (a := b) (M := Mb) (half_pos ht) hb
  have hshift : HasDerivAt (fun r : ℝ => r - t / 2) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (t / 2)
  have hcomp :
      HasDerivAt
        (fun r : ℝ => unitIntervalCosineHeatValue (r - t / 2) b x)
        (unitIntervalCosineHeatSecondValue (t / 2) b x) t := by
    simpa using hheat.comp t hshift
  have hEq :
      (fun r : ℝ => heatDu u₀ r x) =ᶠ[𝓝 t]
        (fun r : ℝ => unitIntervalCosineHeatValue (r - t / 2) b x) := by
    simpa [b] using heatDu_eq_shiftedHeatValue_eventually u₀ (t := t) (x := x) ht
  have hdu :
      HasDerivAt (fun r : ℝ => heatDu u₀ r x)
        (unitIntervalCosineHeatSecondValue (t / 2) b x) t :=
    hcomp.congr_of_eventuallyEq hEq
  refine hdu.congr_deriv ?_
  simpa [b] using shiftedHeatSecondValue_eq_heatD2u u₀ (t := t) (x := x) ht

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

## Why this is preferable to the direct tsum route

The direct route would differentiate the Laplacian series itself and require a local summable majorant for the `λₙ² exp(-τ λₙ) aₙ cos(nπx)` derivative terms. That is true for `τ ≥ t/2`, but it duplicates the exact machinery already encapsulated in `unitIntervalCosineHeatValue_hasDerivAt_time`.

The shifted-coefficient representation packages the extra `λₙ` into a damped coefficient sequence:

```lean
bₙ = -λₙ * exp(-(t/2)λₙ) * aₙ
```

This is bounded, so the existing theorem applies without opening the `hasDerivAt_tsum_of_isPreconnected` box again.

## Likely minor elaboration nits

I expect the mathematical proof shape above to be the right one. If Lean complains, the likely points are only syntactic:

1. `hcomp.congr_of_eventuallyEq hEq` may want `hEq.symm`, depending on the exact orientation of the local Mathlib lemma in this checkout.
2. The two `ring` calls after `rw [← mul_assoc, hexp]` may need one extra `ring_nf` or a slightly more explicit `calc` if the products are associated differently after unfolding.
3. If `unitIntervalCosineHeatValue` or `unitIntervalCosineHeatSecondValue` are not in scope in the target file, the broad `open ShenWork.HeatKernelGradientEstimates` and `open ShenWork.IntervalDomainRegularityBootstrap` lines above fix that.
