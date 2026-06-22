import ShenWork.Paper3.IntervalDomainPersistenceActualLinearMinPoint
import ShenWork.Paper2.IntervalDomainInteriorArgmin
import ShenWork.Paper2.IntervalDomainInteriorDeriv2
import ShenWork.Paper2.IntervalDomainC2Extraction
import ShenWork.Paper2.Statements

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

private theorem lift_eq_interior (f : intervalDomain.Point → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- Interior spatial argmin slope bound for the actual-linear Paper3 branch. -/
theorem intervalDomain_actualLinear_interior_min_point_of_solution
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {x : intervalDomain.Point}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hmin : ∀ y, u t x ≤ u t y) :
    actualLinearLogisticRhs p (u t x) ≤
      intervalDomain.timeDeriv u t x := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, _, _, _, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u t))
      (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t))
      (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).2
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs with hy
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hux := interior_argmin_deriv_zero hmin hint
    ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hint).1.differentiableAt)
  have hvpair := contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hint
  have huxx := interior_argmin_deriv2_nonneg hmin hint hu_c2
  have hux_lift : intervalDomainLift (u t) x.1 = u t x := by
    rw [lift_eq_interior (u t) hint]
    exact congrArg (u t) (Subtype.ext rfl)
  have hu_nonneg : 0 ≤ intervalDomainLift (u t) x.1 := by
    rw [hux_lift]
    exact (hsol.u_pos' ht0 htT (x := x)).le
  have hpdev : deriv (deriv (intervalDomainLift (v t))) x.1 =
      p.μ * intervalDomainLift (v t) x.1 -
        p.ν * (intervalDomainLift (u t) x.1) ^ p.γ := by
    have hpv := hsol.pde_v ht0 htT
      (x := x) (by simpa [intervalDomain] using hint)
    have hlap : intervalDomain.laplacian (v t) x =
        deriv (deriv (intervalDomainLift (v t))) x.1 := rfl
    have hv_lift : intervalDomainLift (v t) x.1 = v t x := by
      rw [lift_eq_interior (v t) hint]
      exact congrArg (v t) (Subtype.ext rfl)
    rw [hlap, ← hux_lift, ← hv_lift] at hpv
    linarith [hpv]
  have hpdeu : intervalDomain.timeDeriv u t x =
      deriv (deriv (intervalDomainLift (u t))) x.1
        - p.χ₀ * intervalDomainChemotaxisDiv p (u t) (v t) x
        + intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) := by
    rw [hux_lift]
    exact hsol.pde_u ht0 htT (by simpa [intervalDomain] using hint)
  have hmain := intervalDomain_actual_linear_minPoint_estimate
    (p := p) (u := u t) (v := v t) (x := x)
    (vx := deriv (intervalDomainLift (v t)) x.1)
    (vxx := deriv (deriv (intervalDomainLift (v t))) x.1)
    (uxx := deriv (deriv (intervalDomainLift (u t))) x.1)
    (uT := intervalDomain.timeDeriv u t x)
    hχ0 hβ hux hvpair.1 hvpair.2 hv_nn hu_nonneg huxx hpdev hpdeu
  rwa [hux_lift] at hmain

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomain_actualLinear_interior_min_point_of_solution
