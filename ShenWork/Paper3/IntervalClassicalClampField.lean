import ShenWork.Paper2.IntervalDomainMFlux
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open Set Filter Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM

/-- A physical interval trajectory represented on the real line by constant
extension at the two endpoints.  Unlike `intervalDomainLift`, this field is
continuous at the boundary. -/
def classicalClampField
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℝ → ℝ :=
  fun t => liftRepr (u t)

private theorem clamp01_eq_zero_of_le {x : ℝ} (hx : x ≤ 0) :
    clamp01 x = 0 := by
  rw [clamp01, min_eq_right (hx.trans (by norm_num : (0 : ℝ) ≤ 1)),
    max_eq_left hx]

private theorem clamp01_eq_one_of_le {x : ℝ} (hx : 1 ≤ x) :
    clamp01 x = 1 := by
  rw [clamp01, min_eq_left hx, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

/-- Constant extension is genuinely differentiable at the left endpoint when
the physical one-sided derivative is zero. -/
theorem liftRepr_hasDerivAt_zero_of_neumann
    {w : intervalDomainPoint → ℝ}
    (hC1 : ContDiffOn ℝ 1 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1))
    (h0 : derivWithin (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) 0 = 0) :
    HasDerivAt (liftRepr w) 0 0 := by
  have hleft : HasDerivWithinAt (liftRepr w) 0 (Set.Iic (0 : ℝ)) 0 := by
    refine (hasDerivAt_const (x := (0 : ℝ)) (c := liftRepr w 0)).hasDerivWithinAt.congr ?_ rfl
    intro x hx
    simp only [liftRepr]
    rw [clamp01_eq_zero_of_le hx, clamp01_eq_zero_of_le le_rfl]
  have hright : HasDerivWithinAt (liftRepr w) 0
      (Set.Icc (0 : ℝ) 1) 0 := by
    have hd :=
      ((hC1.differentiableOn (by norm_num)) 0
        (Set.left_mem_Icc.mpr (by norm_num))).hasDerivWithinAt
    rw [h0] at hd
    exact hd.congr (fun x hx => liftRepr_eq_on_Icc hx) (liftRepr_eq_on_Icc
      (Set.left_mem_Icc.mpr (by norm_num)))
  have hunion := hleft.union hright
  rw [Set.Iic_union_Icc (by norm_num : min (0 : ℝ) 1 ≤ 0)] at hunion
  exact hunion.hasDerivAt
    (Iic_mem_nhds (by norm_num : (0 : ℝ) < max 0 1))

/-- Constant extension is genuinely differentiable at the right endpoint when
the physical one-sided derivative is zero. -/
theorem liftRepr_hasDerivAt_one_of_neumann
    {w : intervalDomainPoint → ℝ}
    (hC1 : ContDiffOn ℝ 1 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1))
    (h1 : derivWithin (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) 1 = 0) :
    HasDerivAt (liftRepr w) 0 1 := by
  have hleft : HasDerivWithinAt (liftRepr w) 0
      (Set.Icc (0 : ℝ) 1) 1 := by
    have hd :=
      ((hC1.differentiableOn (by norm_num)) 1
        (Set.right_mem_Icc.mpr (by norm_num))).hasDerivWithinAt
    rw [h1] at hd
    exact hd.congr (fun x hx => liftRepr_eq_on_Icc hx) (liftRepr_eq_on_Icc
      (Set.right_mem_Icc.mpr (by norm_num)))
  have hright : HasDerivWithinAt (liftRepr w) 0 (Set.Ici (1 : ℝ)) 1 := by
    refine (hasDerivAt_const (x := (1 : ℝ)) (c := liftRepr w 1)).hasDerivWithinAt.congr ?_ rfl
    intro x hx
    simp only [liftRepr]
    rw [clamp01_eq_one_of_le hx, clamp01_eq_one_of_le le_rfl]
  have hunion := hleft.union hright
  rw [Set.Icc_union_Ici (by norm_num : (1 : ℝ) ≤ max 0 1)] at hunion
  exact hunion.hasDerivAt
    (Ici_mem_nhds (by norm_num : min (0 : ℝ) 1 < 1))

/-- On the physical interval the clamp field is the original lifted slice. -/
theorem classicalClampField_eq_lift
    {u : ℝ → intervalDomainPoint → ℝ} {t x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    classicalClampField u t x = intervalDomainLift (u t) x :=
  liftRepr_eq_on_Icc hx

/-- A faithful classical solution gives genuine endpoint Neumann derivatives
for the globally continuous clamp representative. -/
theorem classicalClampField_neumann
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    deriv (classicalClampField u t) 0 = 0 ∧
      deriv (classicalClampField u t) 1 = 0 := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hC2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hC1 : ContDiffOn ℝ 1 (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) := hC2.of_le (by norm_num)
  have hd0 := derivWithin_left_zero hsol ht0 htT u (Or.inl rfl)
  have hd1 := derivWithin_right_zero hsol ht0 htT u (Or.inl rfl)
  exact
    ⟨(liftRepr_hasDerivAt_zero_of_neumann hC1 hd0).deriv,
      (liftRepr_hasDerivAt_one_of_neumann hC1 hd1).deriv⟩

end ShenWork.Paper3

#print axioms ShenWork.Paper3.classicalClampField_neumann
