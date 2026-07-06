/-
  ShenWork/Paper2/IntervalInitialHolderFoldedKernel.lean

  First real-space folded-kernel atoms for producing the common folded-noise
  interface used by `IntervalInitialHolder`.
-/
import ShenWork.Paper2.IntervalInitialHolder
import ShenWork.PDE.IntervalFullKernelMass

open MeasureTheory
open scoped Real Topology

namespace ShenWork.Paper2

noncomputable section

open ShenWork.IntervalDomain (intervalDomainPoint)
open AddSubgroup

/-- Adding an integer multiple of the period does not change the period-2
additive-circle point. -/
theorem addCircle_two_coe_add_period_eq (a : ℝ) (k : ℤ) :
    (((a + 2 * (k : ℝ) : ℝ) : AddCircle (2 : ℝ))) =
      (a : AddCircle (2 : ℝ)) := by
  rw [← sub_eq_zero]
  rw [← QuotientAddGroup.mk_sub]
  simp only [add_sub_cancel_left, QuotientAddGroup.eq_zero_iff]
  rw [mul_comm, ← zsmul_eq_mul]
  exact AddSubgroup.zsmul_mem_zmultiples (2 : ℝ) k

/-- Folding `y + 2k` on the period-2 circle gives `y` for `y ∈ [0,1]`. -/
theorem addCircleTwoFoldPoint_coe_add_period_eq
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    (addCircleTwoFoldPoint (((y + 2 * (k : ℝ) : ℝ) : AddCircle (2 : ℝ)))).1 =
      y := by
  have hper := addCircle_two_coe_add_period_eq y k
  have hdist := addCircle_two_dist_coe_eq_abs_Icc hy
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  rw [hper]
  simpa [addCircleTwoFoldPoint, abs_of_nonneg hy.1] using hdist

/-- Folding `-y + 2k` on the period-2 circle gives `y` for `y ∈ [0,1]`. -/
theorem addCircleTwoFoldPoint_neg_add_period_eq
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) (k : ℤ) :
    (addCircleTwoFoldPoint (((-y + 2 * (k : ℝ) : ℝ) : AddCircle (2 : ℝ)))).1 =
      y := by
  have hper := addCircle_two_coe_add_period_eq (-y) k
  have habs_le : |(-y) - 0| ≤ 1 := by
    rw [sub_zero, abs_neg, abs_of_nonneg hy.1]
    exact hy.2
  have hdist :=
    addCircle_two_dist_coe_eq_abs_of_abs_le_one (x := -y) (y := 0) habs_le
  rw [hper]
  simpa [addCircleTwoFoldPoint, abs_of_nonneg hy.1] using hdist

/-- The real-line folded Gaussian representation candidate for the interval
Neumann semigroup. -/
noncomputable def foldedHeatIntegral
    (t : ℝ) (x : intervalDomainPoint) (f : ℝ → ℝ) : ℝ :=
  ∫ z : ℝ, heatKernel t z * f (addCircleTwoFoldTranslatePoint x z).1

end

end ShenWork.Paper2
