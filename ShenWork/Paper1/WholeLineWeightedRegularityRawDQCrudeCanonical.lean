import ShenWork.Paper1.WholeLineWeightedRegularityH0ToRawCap

open Real

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical-step form of the crude raw-DQ ceiling

The crude ceiling is used only to establish boundedness of a fixed-step
Henry profile.  Its inverse-step loss must therefore be displayed as
`K0 + |h⁻¹| K1`, with `K0` and `K1` independent of the canonical step.
-/

/-- The square-root factor in the crude raw-DQ radius is uniformly bounded
for all steps of absolute value at most one. -/
theorem rawDQCrudeSqrtFactor_le_abs_inv_mul_one
    {eta h : ℝ} (heta : 0 ≤ eta) (habs : |h| ≤ 1) :
    Real.sqrt
        (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) ≤
      |h⁻¹| * Real.sqrt (2 * (Real.exp (2 * eta) + 1)) := by
  let A : ℝ := 2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)
  let B : ℝ := 2 * (Real.exp (2 * eta) + 1)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hexp : Real.exp (2 * eta * |h|) ≤ Real.exp (2 * eta) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hAB : A ≤ |h⁻¹| ^ 2 * B := by
    dsimp only [A, B]
    have hm := mul_le_mul_of_nonneg_left
      (add_le_add_right hexp 1) (sq_nonneg |h⁻¹|)
    nlinarith
  have hright : 0 ≤ |h⁻¹| * Real.sqrt B :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  apply Real.sqrt_le_iff.mpr
  refine ⟨hright, ?_⟩
  calc
    A ≤ |h⁻¹| ^ 2 * B := hAB
    _ = (|h⁻¹| * Real.sqrt B) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hB]

/-- Canonical fixed-step form of the full crude raw-DQ radius. -/
theorem rawDQCrudeRadius_le_fixedStep_form
    {eta h F : ℝ} (heta : 0 ≤ eta) (hF : 0 ≤ F)
    (habs : |h| ≤ 1) :
    eta * F +
        Real.sqrt
          (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F ≤
      eta * F + |h⁻¹| *
        (Real.sqrt (2 * (Real.exp (2 * eta) + 1)) * F) := by
  have hs := mul_le_mul_of_nonneg_right
    (rawDQCrudeSqrtFactor_le_abs_inv_mul_one heta habs) hF
  calc
    eta * F +
        Real.sqrt
          (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F ≤
      eta * F +
        (|h⁻¹| * Real.sqrt (2 * (Real.exp (2 * eta) + 1))) * F :=
      by simpa only [add_comm] using add_le_add_left hs (eta * F)
    _ = eta * F + |h⁻¹| *
        (Real.sqrt (2 * (Real.exp (2 * eta) + 1)) * F) := by ring

/-- Every canonical nonzero step `(n+1)⁻¹` has absolute value at most
one. -/
theorem canonicalRawDQStep_ne_zero_abs_le_one (n : ℕ) :
    (1 : ℝ) / (n + 1) ≠ 0 ∧ |(1 : ℝ) / (n + 1)| ≤ 1 := by
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  constructor
  · exact one_div_ne_zero (ne_of_gt hden)
  · rw [abs_of_pos (one_div_pos.mpr hden)]
    apply (div_le_iff₀ hden).2
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith

end ShenWork.Paper1

#print axioms ShenWork.Paper1.rawDQCrudeSqrtFactor_le_abs_inv_mul_one
#print axioms ShenWork.Paper1.rawDQCrudeRadius_le_fixedStep_form
#print axioms ShenWork.Paper1.canonicalRawDQStep_ne_zero_abs_le_one
