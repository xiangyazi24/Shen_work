import ShenWork.PDE.IntervalDuhamelSpectralC2
import ShenWork.PDE.IntervalSourceCoefficientTimeC1

/-!
# Basic coefficient ladder estimates

This file isolates the bounded-source Duhamel gain and two lightweight restart
coefficient packaging lemmas for the local coefficient ladder.
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace ShenWork.Paper2.IntervalCoeffLadderPassBasic

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSpectralC2 (intervalExpKernel_time_integral)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)

/-- Bounded source coefficients gain one heat eigenvalue in the Duhamel
coefficient.  No time regularity of the source is used: the majorant
`E * exp (-(t-s)λ_k)` is continuous and integrable, and the kernel mass is
computed by `intervalExpKernel_time_integral`. -/
theorem duhamelSpectralCoeff_abs_le_div_eigenvalue
    {a : ℝ → ℕ → ℝ} {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : k ≠ 0)
    {E : ℝ} (hE : ∀ s, 0 ≤ s → s ≤ t → |a s k| ≤ E) :
    |duhamelSpectralCoeff a t k| ≤ E / unitIntervalCosineEigenvalue k := by
  set lam := unitIntervalCosineEigenvalue k with hlam_def
  have hE_nonneg : 0 ≤ E := le_trans (abs_nonneg _) (hE 0 le_rfl ht.le)
  have hlam_pos : 0 < lam := by
    rw [hlam_def]
    unfold unitIntervalCosineEigenvalue
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    positivity
  have hmajorant_int : IntervalIntegrable
      (fun s : ℝ => E * Real.exp (-(t - s) * lam)) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Set.Ioc (0 : ℝ) t →
        ‖Real.exp (-(t - s) * lam) * a s k‖ ≤
          E * Real.exp (-(t - s) * lam) :=
    Filter.Eventually.of_forall (fun s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      calc Real.exp (-(t - s) * lam) * |a s k|
          ≤ Real.exp (-(t - s) * lam) * E := by
            exact mul_le_mul_of_nonneg_left (hE s (le_of_lt hs.1) hs.2)
              (Real.exp_nonneg _)
        _ = E * Real.exp (-(t - s) * lam) := by ring)
  have habs : |duhamelSpectralCoeff a t k| ≤
      ∫ s in (0 : ℝ)..t, E * Real.exp (-(t - s) * lam) := by
    unfold duhamelSpectralCoeff
    rw [hlam_def, ← Real.norm_eq_abs]
    exact intervalIntegral.norm_integral_le_of_norm_le ht.le hbound hmajorant_int
  have hint : (∫ s in (0 : ℝ)..t, E * Real.exp (-(t - s) * lam)) =
      E * ((1 - Real.exp (-t * lam)) / lam) := by
    rw [intervalIntegral.integral_const_mul,
      intervalExpKernel_time_integral (ne_of_gt hlam_pos)]
  have hfactor : (1 - Real.exp (-t * lam)) / lam ≤ 1 / lam := by
    rw [div_le_div_iff_of_pos_right hlam_pos]
    linarith [Real.exp_nonneg (-t * lam)]
  calc |duhamelSpectralCoeff a t k|
      ≤ ∫ s in (0 : ℝ)..t, E * Real.exp (-(t - s) * lam) := habs
    _ = E * ((1 - Real.exp (-t * lam)) / lam) := hint
    _ ≤ E * (1 / lam) := mul_le_mul_of_nonneg_left hfactor hE_nonneg
    _ = E / unitIntervalCosineEigenvalue k := by rw [hlam_def]; ring

/-- Pass-1 restart envelope for a nonzero mode: a supplied homogeneous restart
bound plus the bounded-source Duhamel gain.  If the source bound itself is
`O(k)`, this is the advertised `O(k^{-1})` restart contribution. -/
theorem restartCoeff_pass1_envelope
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {τ M₀ Msource : ℝ}
    (hτ : 0 < τ) {k : ℕ} (hk : k ≠ 0)
    (hhom : |Real.exp (-τ * unitIntervalCosineEigenvalue k) * a₀ k| ≤ M₀)
    (hsrc : ∀ s, 0 ≤ s → s ≤ τ → |a s k| ≤ Msource) :
    |localRestartCoeff a₀ a τ k| ≤
      M₀ + Msource / unitIntervalCosineEigenvalue k := by
  have hduh := duhamelSpectralCoeff_abs_le_div_eigenvalue
    (a := a) hτ hk hsrc
  unfold localRestartCoeff
  exact (abs_add_le _ _).trans (add_le_add hhom hduh)

/-- Pass-2 summability packaging: once the eigenvalue-weighted restart
coefficients are dominated by a `p`-series tail with exponent `1+ε`, the
weighted coefficient sequence is summable. -/
theorem restartCoeff_eigenvalue_weighted_summable_of_pass2_envelope
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {τ C ε : ℝ}
    (_hC : 0 ≤ C) (hε : 0 < ε)
    (henv : ∀ k,
      unitIntervalCosineEigenvalue k * |localRestartCoeff a₀ a τ k| ≤
        C / (((k : ℝ) + 1) ^ (1 + ε))) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |localRestartCoeff a₀ a τ k|) := by
  have hp : 1 < 1 + ε := by linarith
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (1 + ε))⁻¹) :=
    (Real.summable_nat_rpow_inv).2 hp
  have htail_nat :
      Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (1 + ε))⁻¹) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => ((n : ℝ) ^ (1 + ε))⁻¹) 1).mpr hbase
  have htail : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (1 + ε))⁻¹) := by
    refine htail_nat.congr ?_
    intro n
    norm_num
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (htail.mul_left C)
  · exact mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _)
  · simpa [div_eq_mul_inv] using henv n

end ShenWork.Paper2.IntervalCoeffLadderPassBasic

