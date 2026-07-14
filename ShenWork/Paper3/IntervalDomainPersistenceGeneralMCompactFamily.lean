import ShenWork.Paper3.IntervalDomainPersistenceActualLinearCompactFamily
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMBoundary

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-!
# Compact spatial-minimum family for the faithful general-m domain

The Danskin family itself is independent of the chemotaxis exponent.  What
changes is the classical-solution witness from which its closed-interval
regularity is extracted.
-/

theorem intervalDomainM_lift_slice_continuousOn_of_positive
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {s : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) (hs : 0 < s) :
    ContinuousOn (intervalDomainLift (u s)) (Set.Icc (0 : ℝ) 1) := by
  have hT : 0 < s + 1 := by linarith
  have hclass := hsol.classical.classical (T := s + 1) hT
  obtain ⟨_, _, _, _, _, _, hField⟩ := hclass.regularity
  intro y hy
  have hc := hField.1 (s, y) ⟨⟨hs, by linarith⟩, hy⟩
  exact (hc.comp (Continuous.continuousWithinAt (by fun_prop))
    (fun z hz => ⟨⟨hs, by linarith⟩, hz⟩) :
      ContinuousWithinAt (fun z => intervalDomainLift (u s) z)
        (Set.Icc (0 : ℝ) 1) y)

theorem intervalDomainM_generalM_compactMinFamily
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    CompactMinFamily (Set.Icc (0 : ℝ) 1)
      (intervalDomainActualLinearDanskinF u) (intervalDomainSpatialMin u) := by
  constructor
  · intro s x hx
    by_cases hs : 0 < s
    · have hcont :=
        intervalDomainM_lift_slice_continuousOn_of_positive
          (p := p) (v := v) hsol hs
      have hbdd : BddBelow
          (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) :=
        (isCompact_Icc.image_of_continuousOn hcont).bddBelow
      rw [intervalDomainActualLinearDanskinF, if_pos hs,
        intervalDomainSpatialMin_eq_lift_sInf]
      exact csInf_le hbdd (Set.mem_image_of_mem _ hx)
    · simp [intervalDomainActualLinearDanskinF, hs]
  · intro s
    by_cases hs : 0 < s
    · have hcont :=
        intervalDomainM_lift_slice_continuousOn_of_positive
          (p := p) (v := v) hsol hs
      rcases intervalDomainSpatialMin_attained hcont with ⟨x, hx⟩
      refine ⟨x.1, x.2, ?_⟩
      rw [intervalDomainActualLinearDanskinF, if_pos hs]
      have hlift : intervalDomainLift (u s) x.1 = u s x := by
        simp [intervalDomainLift]
      rw [hlift]
      exact hx
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      simp [intervalDomainActualLinearDanskinF, hs]

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_generalM_compactMinFamily
