import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
  Fourier-to-cosine Parseval bridge scaffolding.

  The cosine basis on `[0,1]` should be transported from the even part of the
  Fourier basis on `AddCircle 2`.  This file records the Mathlib Fourier
  Parseval input and the first concrete even-reflection integral identity.
-/

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace ShenWork.CosineParsevalBridge

/-- Even reflection of a unit-interval function to the doubled interval. -/
def unitIntervalEvenReflection (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f |x|

theorem unitIntervalEvenReflection_apply_of_nonneg
    (f : ℝ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    unitIntervalEvenReflection f x = f x := by
  simp [unitIntervalEvenReflection, abs_of_nonneg hx]

theorem unitIntervalEvenReflection_apply_neg
    (f : ℝ → ℂ) (x : ℝ) :
    unitIntervalEvenReflection f (-x) = unitIntervalEvenReflection f x := by
  simp [unitIntervalEvenReflection]

/-- The negative half of the doubled interval contributes the same squared
`L²` mass as the positive half for an even reflection. -/
theorem unitIntervalEvenReflection_norm_sq_integral_neg
    (f : ℝ → ℂ) :
    (∫ x in (-1 : ℝ)..0, ‖unitIntervalEvenReflection f x‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  have heven :
      (∫ x in (-1 : ℝ)..0, ‖unitIntervalEvenReflection f x‖ ^ 2)
        =
          ∫ x in (-1 : ℝ)..0,
            ‖unitIntervalEvenReflection f (-x)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    simp [unitIntervalEvenReflection_apply_neg]
  calc
    (∫ x in (-1 : ℝ)..0, ‖unitIntervalEvenReflection f x‖ ^ 2)
        =
          ∫ x in (-1 : ℝ)..0,
            ‖unitIntervalEvenReflection f (-x)‖ ^ 2 := heven
    _ = ∫ x in (0 : ℝ)..1, ‖unitIntervalEvenReflection f x‖ ^ 2 := by
          simpa using
            (intervalIntegral.integral_comp_neg
              (f := fun x : ℝ => ‖unitIntervalEvenReflection f x‖ ^ 2)
              (a := (-1 : ℝ)) (b := 0))
    _ = ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx_nonneg : 0 ≤ x := by
            have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
            exact hxIcc.1
          simp [unitIntervalEvenReflection, abs_of_nonneg hx_nonneg]

/-- Squared `L²` mass of the even reflection on `[-1,1]`. -/
theorem unitIntervalEvenReflection_norm_sq_integral
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    (∫ x in (-1 : ℝ)..1, ‖unitIntervalEvenReflection f x‖ ^ 2) =
      2 * ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  let g : ℝ → ℝ := fun x => ‖unitIntervalEvenReflection f x‖ ^ 2
  have hpos : IntervalIntegrable g volume 0 1 := by
    refine hf.congr (fun x hx => ?_)
    have hx_nonneg : 0 ≤ x := by
      have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact hxIoc.1.le
    simp [g, unitIntervalEvenReflection, abs_of_nonneg hx_nonneg]
  have hneg :
      IntervalIntegrable g volume (-1) 0 := by
    have hcomp :
        IntervalIntegrable (fun x => g (-x)) volume 0 (-1) :=
      by
        simpa only [neg_zero] using
          (IntervalIntegrable.iff_comp_neg (f := g) (a := 0) (b := 1)).mp hpos
    exact hcomp.symm.congr (fun x _hx => by
      simp [g, unitIntervalEvenReflection_apply_neg])
  calc
    (∫ x in (-1 : ℝ)..1, g x)
        =
          (∫ x in (-1 : ℝ)..0, g x) +
            ∫ x in (0 : ℝ)..1, g x := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos]
    _ =
          (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) +
            ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
          dsimp [g]
          rw [unitIntervalEvenReflection_norm_sq_integral_neg]
          congr 1
          apply intervalIntegral.integral_congr
          intro x hx
          have hx_nonneg : 0 ≤ x := by
            have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
            exact hxIcc.1
          simp [unitIntervalEvenReflection, abs_of_nonneg hx_nonneg]
    _ = 2 * ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by ring

/-- Mathlib's Parseval identity on the doubled interval, specialized to the
even reflection.  This is the Fourier side from which cosine Parseval should
be extracted by proving coefficient symmetry/equality. -/
theorem unitIntervalEvenReflection_fourier_parseval_raw
    {f : ℝ → ℂ}
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1))) :
    (∑' i : ℤ,
        ‖fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
          (unitIntervalEvenReflection f) i‖ ^ 2)
      =
        (2 : ℝ)⁻¹ *
          ∫ x in (-1 : ℝ)..1, ‖unitIntervalEvenReflection f x‖ ^ 2 := by
  have h :=
    tsum_sq_fourierCoeffOn
      (hab := show (-1 : ℝ) < 1 by norm_num)
      (f := unitIntervalEvenReflection f) hL2
  norm_num at h ⊢
  simpa using h

/-- Parseval on the doubled interval after reducing the even-reflection mass
back to the unit interval.  The remaining missing bridge is the coefficient
identity between these Fourier coefficients and the Neumann cosine
coefficients. -/
theorem unitIntervalEvenReflection_fourier_parseval_unit_mass
    {f : ℝ → ℂ}
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    (∑' i : ℤ,
        ‖fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
          (unitIntervalEvenReflection f) i‖ ^ 2)
      =
        ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  rw [unitIntervalEvenReflection_fourier_parseval_raw hL2,
    unitIntervalEvenReflection_norm_sq_integral hf]
  ring

/-- On the doubled circle, the paired Fourier characters are exactly the
unit-interval cosine mode.  This is the pointwise algebraic kernel used to turn
even Fourier coefficients into cosine coefficients. -/
theorem unitIntervalCosine_eq_fourier_pair (n : ℕ) (x : ℝ) :
    ((Real.cos ((n : ℝ) * Real.pi * x) : ℂ)) =
      (1 / 2 : ℂ) *
        (fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ)) +
          fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ))) := by
  let θ : ℂ := ((n : ℝ) * Real.pi * x : ℝ)
  have hpos :
      fourier (T := (2 : ℝ)) (n : ℤ) (x : AddCircle (2 : ℝ)) =
        Complex.exp (θ * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp [θ]
    norm_num
    ring
  have hneg :
      fourier (T := (2 : ℝ)) (-(n : ℤ)) (x : AddCircle (2 : ℝ)) =
        Complex.exp (-θ * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp [θ]
    norm_num
    ring
  rw [hpos, hneg, ← Complex.two_cos]
  rw [← Complex.ofReal_cos]
  ring

end ShenWork.CosineParsevalBridge
