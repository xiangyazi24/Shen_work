import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

/-!
# Windowed spectral form of the Duhamel term

`duhamelSpectral_eq_cosineSeries_on`: the windowed version of
`IntervalDuhamelClosedC2.duhamelSpectral_eq_cosineSeries`.  Takes
`DuhamelSourceTimeC1On a 0 T` instead of the global `DuhamelSourceTimeC1 a`,
since for `t ∈ (0, T]` the integral `∫₀ᵗ` lives inside `[0, T]`.
-/

open MeasureTheory Set
open scoped Topology
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff duhamelValue_adot_eq_tsum_on)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)

noncomputable section

namespace ShenWork.IntervalDuhamelSpectralEqCosineSeriesOn

/-- Derive `ContinuousOn` of coefficients from `HasDerivWithinAt` data. -/
private theorem continuousOn_coeff_of_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T) (n : ℕ) :
    ContinuousOn (fun s => a s n) (Icc 0 T) :=
  fun s hs => (src.hderiv s hs n).continuousWithinAt

/-- **Windowed spectral Duhamel series.**
`∫₀ᵗ S(t−s) g(s)(x) ds = ∑'ₙ bₙ(t) cos(nπx)` from
`DuhamelSourceTimeC1On a 0 T` for `0 < t` and `t ≤ T`. -/
theorem duhamelSpectral_eq_cosineSeries_on {a : ℝ → ℕ → ℝ} {T : ℝ}
    (src : DuhamelSourceTimeC1On a 0 T)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) {x : ℝ} :
    (∫ s in (0:ℝ)..t, unitIntervalCosineHeatValue (t - s) (a s) x)
      = ∑' n, duhamelSpectralCoeff a t n * cosineMode n x := by
  have hnn : ∀ n, 0 ≤ src.envelope n :=
    fun n => le_trans (abs_nonneg _)
      (src.henv_bound 0 (left_mem_Icc.mpr (le_trans ht.le htT)) n)
  have hunif : ∀ s, 0 ≤ s → s ≤ T → ∀ i, |a s i| ≤ ∑' k, src.envelope k := by
    intro s hs hsT i
    refine le_trans (src.henv_bound s ⟨hs, hsT⟩ i) ?_
    have := src.henv_summable.sum_le_tsum {i} (fun j _ => hnn j)
    simpa using this
  have hcont_a : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Icc 0 T) :=
    continuousOn_coeff_of_on src
  rw [duhamelValue_adot_eq_tsum_on (adot := a) (Mdot := ∑' k, src.envelope k)
      ht htT hunif hcont_a (b := t) ht.le (le_refl t)]
  refine tsum_congr (fun n => ?_)
  calc (∫ s in (0:ℝ)..t, unitIntervalCosineHeatPointWeight (t - s) x n * a s n)
      = ∫ s in (0:ℝ)..t,
          (Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n)
            * cosineMode n x :=
        intervalIntegral.integral_congr (fun s _ => by
          simp only [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode,
            cosineMode]; ring)
    _ = (∫ s in (0:ℝ)..t,
            Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * a s n)
          * cosineMode n x := intervalIntegral.integral_mul_const _ _
    _ = duhamelSpectralCoeff a t n * cosineMode n x := rfl

end ShenWork.IntervalDuhamelSpectralEqCosineSeriesOn
