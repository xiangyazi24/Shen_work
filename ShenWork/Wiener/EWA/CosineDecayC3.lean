import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.HeatKernelGradientEstimates

/-!
# Certified cubic decay for Neumann cosine coefficients

This file contains the summability consequence needed by the Wiener lifting
bridge from an explicit cubic-decay certificate.  It intentionally does not
claim that the current paper datum hypotheses imply this certificate.
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

/-- Explicit cubic-decay certificate for normalized unit-interval cosine
coefficients. -/
structure CosineCubicDecay (f : ℝ → ℝ) where
  A : ℝ
  hA : 0 ≤ A
  hdecay : ∀ n : ℕ, 1 ≤ n →
    |cosineCoeffs f n| ≤ A / (((n : ℝ) * Real.pi) ^ 3)

/-- A positive cubic coefficient bound implies the `A¹` cosine-side weighted
`ℓ¹` summability needed by `memW_ofCosineCoeffs`. -/
theorem weighted_one_summable_of_cubic_decay
    {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hdecay : ∀ n : ℕ, 1 ≤ n →
      |c n| ≤ A / (((n : ℝ) * Real.pi) ^ 3)) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (1 : ℕ) * |c n|) := by
  have hcomp :
      Summable (fun n : ℕ => (2 * A / Real.pi ^ 3) * (1 / (n : ℝ) ^ 2)) := by
    exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hcomp ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hdec := hdecay n hn
  have hden_pos : 0 < (((n : ℝ) * Real.pi) ^ 3) := by positivity
  have hdec_nonneg : 0 ≤ A / (((n : ℝ) * Real.pi) ^ 3) := by positivity
  have hleft_nonneg : 0 ≤ (1 + (n : ℝ)) ^ (1 : ℕ) := by positivity
  have hone_le_two : 1 + (n : ℝ) ≤ 2 * (n : ℝ) := by
    have hn_ge : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft_nonneg (abs_nonneg _))]
  calc
    (1 + (n : ℝ)) ^ (1 : ℕ) * |c n|
        ≤ (1 + (n : ℝ)) * (A / (((n : ℝ) * Real.pi) ^ 3)) := by
          simpa using mul_le_mul_of_nonneg_left hdec hleft_nonneg
    _ ≤ (2 * (n : ℝ)) * (A / (((n : ℝ) * Real.pi) ^ 3)) := by
          exact mul_le_mul_of_nonneg_right hone_le_two hdec_nonneg
    _ = (2 * A / Real.pi ^ 3) * (1 / (n : ℝ) ^ 2) := by
          have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
          have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
          rw [mul_pow]
          field_simp [hn_ne, hpi_ne]

/-- Certified cubic decay gives `A¹` cosine-side summability. -/
theorem weighted_one_summable_cosineCoeffs_of_cubic_decay
    {f : ℝ → ℝ}
    (hdecay : CosineCubicDecay f) :
    Summable
      (fun n : ℕ => (1 + (n : ℝ)) ^ (1 : ℕ) * |cosineCoeffs f n|) := by
  exact weighted_one_summable_of_cubic_decay
    (c := cosineCoeffs f) hdecay.hA hdecay.hdecay

end ShenWork.EWA
