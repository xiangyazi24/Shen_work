import ShenWork.Paper3.IntervalDomainPersistenceActualLinearInterior
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearBoundaryLeft
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearBoundaryRight

open ShenWork.IntervalDomain ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

theorem intervalDomain_actualLinear_min_point_slope_bound
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmin : ∀ y, u t x ≤ u t y) :
    actualLinearLogisticRhs p (intervalDomainLift (u t) x.1) ≤
      intervalDomain.timeDeriv u t x := by
  rcases lt_or_eq_of_le x.2.1 with h0 | h0
  · rcases lt_or_eq_of_le x.2.2 with h1 | h1
    · have hx_lift : intervalDomainLift (u t) x.1 = u t x := by
        unfold intervalDomainLift
        split_ifs with hx
        · exact congrArg (u t) (Subtype.ext rfl)
        · exact False.elim (hx x.2)
      rw [hx_lift]
      exact intervalDomain_actualLinear_interior_min_point_of_solution
        hχ0 hβ hsol ht0 htT ⟨h0, h1⟩ hmin
    · have hx11 : x.1 = 1 := h1
      have hminlift : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
          intervalDomainLift (u t) 1 ≤ intervalDomainLift (u t) y := by
        intro y hy
        have hlift1 : intervalDomainLift (u t) 1 = u t x := by
          rw [intervalDomainLift,
            dif_pos (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_refl _⟩)]
          exact congrArg (u t) (Subtype.ext hx11.symm)
        have hlifty : intervalDomainLift (u t) y =
            u t ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
          rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
        rw [hlift1, hlifty]
        exact hmin ⟨y, Set.Ioo_subset_Icc_self hy⟩
      have hb := intervalDomain_actualLinear_boundary_min_point_right
        hχ0 hβ hsol ht0 htT hminlift
      have htd : intervalDomain.timeDeriv u t x =
          deriv (fun r => intervalDomainLift (u r) 1) t := by
        show deriv (fun s => u s x) t =
          deriv (fun r => intervalDomainLift (u r) 1) t
        congr 1; funext r
        rw [intervalDomainLift,
          dif_pos (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_refl _⟩)]
        exact (congrArg (u r) (Subtype.ext hx11.symm)).symm
      rw [hx11, htd]
      exact hb
  · have hx10 : x.1 = 0 := h0.symm
    have hminlift : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y := by
      intro y hy
      have hlift0 : intervalDomainLift (u t) 0 = u t x := by
        rw [intervalDomainLift,
          dif_pos (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_refl _, zero_le_one⟩)]
        exact congrArg (u t) (Subtype.ext hx10.symm)
      have hlifty : intervalDomainLift (u t) y =
          u t ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
        rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]
      rw [hlift0, hlifty]
      exact hmin ⟨y, Set.Ioo_subset_Icc_self hy⟩
    have hb := intervalDomain_actualLinear_boundary_min_point_left
      hχ0 hβ hsol ht0 htT hminlift
    have htd : intervalDomain.timeDeriv u t x =
        deriv (fun r => intervalDomainLift (u r) 0) t := by
      show deriv (fun s => u s x) t =
        deriv (fun r => intervalDomainLift (u r) 0) t
      congr 1; funext r
      rw [intervalDomainLift,
        dif_pos (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_refl _, zero_le_one⟩)]
      exact (congrArg (u r) (Subtype.ext hx10.symm)).symm
    rw [hx10, htd]
    exact hb

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomain_actualLinear_min_point_slope_bound
