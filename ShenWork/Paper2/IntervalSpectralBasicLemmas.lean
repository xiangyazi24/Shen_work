import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.PDE.CosineSpectrum
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Small interval spectral lemmas

This file contains the two elementary analytic facts used by the active
Paper 3 route.  They are independent of the experimental truncated spectral
bootstrap and therefore must not inherit that module's unfinished ladder.
-/

open MeasureTheory Set
open scoped BigOperators Topology ENNReal

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugateCosineSeries (intervalSineInner)
open ShenWork.CosineSpectrum
  (cosineMode cosineMode_hasDerivAt)
open ShenWork.IntervalMildPicardRegularity
   (cosineCoeffs_eq_factor_mul_integral cosineCoeffs_pos_eq_integral)

private theorem continuous_cosineMode (n : ℕ) : Continuous (cosineMode n) := by
  change Continuous fun x : ℝ ↦ Real.cos ((n : ℝ) * Real.pi * x)
  fun_prop

/-- A continuous function on the closed interval belongs to `L²` for the
interval measure. -/
lemma memLp_two_of_continuousOn_Icc
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    MemLp f (2 : ℝ≥0∞) (intervalMeasure 1) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hfm : AEStronglyMeasurable f (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.continuousOn_aestronglyMeasurable_intervalMeasure
      hf
  refine MemLp.of_bound hfm C ?_
  unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

/-- For a `C¹` flux vanishing at both endpoints, the frequency-weighted
sine pairing is the Neumann cosine coefficient of its derivative. -/
theorem freq_sineInner_eq_cosineCoeffs_deriv
    {g : ℝ → ℝ} {s_g : Set ℝ} (hs_g : s_g.Countable)
    (hgc : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hg : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s_g, HasDerivAt g (deriv g x) x)
    (hg'i : IntervalIntegrable (deriv g) volume 0 1)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (n : ℕ) :
    ((n : ℝ) * Real.pi) * intervalSineInner g n =
      cosineCoeffs (deriv g) n := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le (by norm_num)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hFTC : (∫ x in (0 : ℝ)..1, deriv g x) = g 1 - g 0 :=
      MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        g (deriv g) (by norm_num : (0 : ℝ) ≤ 1) hs_g hgc hg hg'i
    have hcoeff : cosineCoeffs (deriv g) 0 =
        ∫ x in (0 : ℝ)..1, deriv g x := by
      rw [cosineCoeffs_eq_factor_mul_integral]
      simp
    rw [hcoeff, hFTC, h0, h1]
    simp [intervalSineInner]
  · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    have hFc : ContinuousOn (fun y ↦ cosineMode n y * g y)
        (Set.Icc (0 : ℝ) 1) :=
      ((continuous_cosineMode n).continuousOn).mul hgc
    have hFd : ∀ x ∈ Set.Ioo (0 : ℝ) 1 \ s_g,
        HasDerivAt (fun y ↦ cosineMode n y * g y)
          (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) * g x
            + cosineMode n x * deriv g x) x := by
      intro x hx
      exact (cosineMode_hasDerivAt n x).mul (hg x hx)
    have hAi : IntervalIntegrable
        (fun x ↦ -((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * x) * g x) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      exact (Continuous.continuousOn (by fun_prop)).mul hgc
    have hBi : IntervalIntegrable
        (fun x ↦ cosineMode n x * deriv g x) volume 0 1 :=
      hg'i.continuousOn_mul ((continuous_cosineMode n).continuousOn)
    have hFTC :=
      MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        (fun y ↦ cosineMode n y * g y)
        (fun x ↦ -((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * x) * g x +
          cosineMode n x * deriv g x)
        (by norm_num : (0 : ℝ) ≤ 1) hs_g hFc hFd (hAi.add hBi)
    have hbdry : cosineMode n 1 * g 1 - cosineMode n 0 * g 0 = 0 := by
      rw [h0, h1]
      ring
    rw [hbdry] at hFTC
    have hsplit :
        (∫ x in (0 : ℝ)..1,
            -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) * g x) +
          (∫ x in (0 : ℝ)..1, cosineMode n x * deriv g x) = 0 := by
      rw [← intervalIntegral.integral_add hAi hBi]
      exact hFTC
    have hsin_int :
        (∫ x in (0 : ℝ)..1,
            -((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x) * g x) =
          -((n : ℝ) * Real.pi) *
            ∫ x in (0 : ℝ)..1,
              Real.sin ((n : ℝ) * Real.pi * x) * g x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ ↦ ?_
      ring
    rw [cosineCoeffs_pos_eq_integral hne]
    simp only [intervalSineInner, hne, if_false]
    rw [hsin_int] at hsplit
    have hpair : (∫ x in (0 : ℝ)..1, cosineMode n x * deriv g x) =
        ((n : ℝ) * Real.pi) *
          ∫ x in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * x) * g x := by
      linarith
    rw [show (fun x ↦ Real.cos ((n : ℝ) * Real.pi * x) * deriv g x) =
        fun x ↦ cosineMode n x * deriv g x from rfl]
    rw [hpair]
    ring

#print axioms memLp_two_of_continuousOn_Icc
#print axioms freq_sineInner_eq_cosineCoeffs_deriv

end ShenWork.Paper2.BFormPositiveDatumNegPart
