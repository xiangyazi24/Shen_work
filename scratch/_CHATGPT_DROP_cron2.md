# Q1267 (cron2) — joint `ContinuousOn` of `heatD2u` on a positive slab

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Answer

You do **not** need a fresh Weierstrass M-test for `heatD2u`.

The direct M-test you described is mathematically right:

```text
|λ_k^2 exp(-t λ_k) a_k cos(kπx)| ≤ |M| · λ_k^2 exp(-c λ_k),   t ∈ Icc c T,
```

and the required summability is the expected exponential-tail/spectral-polynomial summability.  But the repo already has a stronger reusable continuity engine:

```lean
ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod
```

for

```text
unitIntervalCosineHeatSecondValue τ b x
  = ∑ k, exp(-τ λ_k) · (-(kπ)^2 cos(kπx)) · b_k.
```

To represent `heatD2u`, shift half of the positive lower time `c` into the coefficients.  Define

```text
b_k := -λ_k · exp(-(c/2) λ_k) · a_k.
```

Then, for `t ≥ c`,

```text
unitIntervalCosineHeatSecondValue (t - c/2) b x
  = ∑ exp(-(t-c/2)λ_k) · (-λ_k cos(kπx)) · (-λ_k exp(-(c/2)λ_k) a_k)
  = ∑ λ_k^2 exp(-tλ_k) a_k cos(kπx)
  = heatD2u u₀ t x.
```

The shifted coefficient sequence `b` is bounded because `λ exp(-(c/2)λ)` is bounded for `c > 0`.  Therefore the existing `unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod` applies, and the map `(t,x) ↦ (t - c/2, x)` sends `Icc c T ×ˢ Icc 0 1` into `Ioi 0 ×ˢ univ`.

## Drop-in proof

In `ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean`, replace the current `sorry` body of `heatD2u_jointContinuousOn` with the final theorem below.  The helper definitions can go immediately above it.

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.PDE.IntervalSemigroupNeumann

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalDomainRegularityBootstrap

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

/-- Shifted coefficient sequence used to write `heatD2u` as a shifted
`unitIntervalCosineHeatSecondValue`. -/
private abbrev heatD2uSecondCoeff
    (u₀ : intervalDomainPoint → ℝ) (c : ℝ) : ℕ → ℝ :=
  fun n => -unitIntervalCosineEigenvalue n *
    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n

/-- For `0 < c`, the shifted coefficients
`-λₙ exp(-(c/2)λₙ) aₙ` are bounded whenever the original coefficients `aₙ` are
bounded. -/
private theorem heatD2uSecondCoeff_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ} (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ∀ n, |heatD2uSecondCoeff u₀ c n| ≤ |M₀| / (c / 2) := by
  intro n
  have hc2 : 0 < c / 2 := half_pos hc
  have hλ_nonneg : 0 ≤ unitIntervalCosineEigenvalue n := by
    simp [unitIntervalCosineEigenvalue]
    positivity
  have hλexp_nonneg :
      0 ≤ unitIntervalCosineEigenvalue n *
        Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) := by
    positivity
  have hλexp_bound :
      unitIntervalCosineEigenvalue n *
          Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) ≤
        1 / (c / 2) := by
    rw [le_div_iff₀ hc2]
    have hcx_nonneg : 0 ≤ (c / 2) * unitIntervalCosineEigenvalue n := by
      exact mul_nonneg hc2.le hλ_nonneg
    calc
      unitIntervalCosineEigenvalue n *
            Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) * (c / 2)
          = ((c / 2) * unitIntervalCosineEigenvalue n) *
              Real.exp (-((c / 2) * unitIntervalCosineEigenvalue n)) := by
              ring
      _ ≤ 1 := real_mul_exp_neg_le_one hcx_nonneg
  have hM : |cosineCoeffs (intervalDomainLift u₀) n| ≤ |M₀| :=
    le_trans (hu₀_bound n) (le_abs_self M₀)
  have hdiv_nonneg : 0 ≤ 1 / (c / 2) := by
    positivity
  calc
    |heatD2uSecondCoeff u₀ c n|
        = (unitIntervalCosineEigenvalue n *
              Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)) *
            |cosineCoeffs (intervalDomainLift u₀) n| := by
            rw [heatD2uSecondCoeff, abs_mul, abs_mul, abs_neg,
              abs_of_nonneg hλ_nonneg, abs_of_nonneg (Real.exp_nonneg _)]
            ring
    _ ≤ (1 / (c / 2)) * |M₀| :=
          mul_le_mul hλexp_bound hM (abs_nonneg _) hdiv_nonneg
    _ = |M₀| / (c / 2) := by ring

/-- Algebraic identification of the shifted `secondValue` series with `heatD2u`. -/
private theorem shiftedSecondValue_eq_heatD2u
    (u₀ : intervalDomainPoint → ℝ) {c t x : ℝ} (hc : 0 < c) (hct : c ≤ t) :
    unitIntervalCosineHeatSecondValue (t - c / 2) (heatD2uSecondCoeff u₀ c) x =
      heatD2u u₀ t x := by
  have ht : 0 < t := lt_of_lt_of_le hc hct
  simp only [heatD2u, if_pos ht, heatD2uSecondCoeff,
    unitIntervalCosineHeatSecondValue, unitIntervalCosineHeatSecondPointWeight,
    unitIntervalCosineMode, ShenWork.CosineSpectrum.cosineMode]
  congr 1
  ext n
  have hλsq : ((n : ℝ) * Real.pi) ^ 2 = unitIntervalCosineEigenvalue n := by
    simp [unitIntervalCosineEigenvalue]
    ring
  rw [hλsq]
  have hexp :
      Real.exp (-(t - c / 2) * unitIntervalCosineEigenvalue n) *
          Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) =
        Real.exp (-t * unitIntervalCosineEigenvalue n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-(t - c / 2) * unitIntervalCosineEigenvalue n) *
          (-(unitIntervalCosineEigenvalue n) * Real.cos ((n : ℝ) * Real.pi * x)) *
          (-(unitIntervalCosineEigenvalue n) *
            Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n)
        = unitIntervalCosineEigenvalue n ^ 2 *
            (Real.exp (-(t - c / 2) * unitIntervalCosineEigenvalue n) *
              Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n) *
            Real.cos ((n : ℝ) * Real.pi * x) := by
            ring
    _ = unitIntervalCosineEigenvalue n ^ 2 *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineCoeffs (intervalDomainLift u₀) n) *
          Real.cos ((n : ℝ) * Real.pi * x) := by
          rw [hexp]
          ring

/-- Joint continuity of the explicit second time-derivative heat slice on a
positive closed time slab. -/
private theorem heatD2u_jointContinuousOn
    {u₀ : intervalDomainPoint → ℝ} {M₀ c T : ℝ} (hc : 0 < c)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ContinuousOn (fun q : ℝ × ℝ => heatD2u u₀ q.1 q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  classical
  let b : ℕ → ℝ := heatD2uSecondCoeff u₀ c
  let Mb : ℝ := |M₀| / (c / 2)
  have hb : ∀ n, |b n| ≤ Mb := by
    simpa [b, Mb] using heatD2uSecondCoeff_bound (u₀ := u₀) (M₀ := M₀)
      (c := c) hc _hu₀_bound
  have hsecond : ContinuousOn
      (fun q : ℝ × ℝ => unitIntervalCosineHeatSecondValue q.1 b q.2)
      (Ioi (0 : ℝ) ×ˢ univ) :=
    ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod
      (a := b) (M := Mb) hb
  have hmap_cont : ContinuousOn
      (fun q : ℝ × ℝ => (q.1 - c / 2, q.2))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    fun_prop
  have hmap_mem : ∀ q ∈ Icc c T ×ˢ Icc (0 : ℝ) 1,
      (q.1 - c / 2, q.2) ∈ Ioi (0 : ℝ) ×ˢ univ := by
    intro q hq
    obtain ⟨ht, _hx⟩ := mem_prod.mp hq
    exact mem_prod.mpr ⟨by linarith [ht.1, half_pos hc], mem_univ _⟩
  have hshifted : ContinuousOn
      (fun q : ℝ × ℝ => unitIntervalCosineHeatSecondValue (q.1 - c / 2) b q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    simpa using hsecond.comp hmap_cont hmap_mem
  refine hshifted.congr ?_
  intro q hq
  obtain ⟨ht, _hx⟩ := mem_prod.mp hq
  simpa [b] using shiftedSecondValue_eq_heatD2u u₀ (c := c) (t := q.1)
    (x := q.2) hc ht.1

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

## Notes

The existing `unitIntervalCosineHeatValue_continuousOn_Ioi_prod` can also be used, but then you would shift into coefficients

```lean
fun k => unitIntervalCosineEigenvalue k ^ 2 *
  Real.exp (-(c / 2) * unitIntervalCosineEigenvalue k) *
  cosineCoeffs (intervalDomainLift u₀) k
```

and represent `heatD2u` as a shifted `unitIntervalCosineHeatValue`.  That requires proving boundedness of `λ² exp(-(c/2)λ) a_k`.  Reusing `unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod` is slightly cleaner: the theorem already carries one `λ`, so the shifted coefficient only needs one damped eigenvalue factor.

If you prefer the direct M-test route with `M * λ_k^2 * exp(-c λ_k)`, it is correct, but it duplicates the M-test already packaged in `unitIntervalCosineHeatSecondValue_continuousOn_Ioi_prod`.
