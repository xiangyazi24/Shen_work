import ShenWork.Paper3.IntervalDomainPersistenceActualLinearDini
import ShenWork.Paper3.IntervalDomainPersistenceDiniAudit2
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.MinPersistenceAtoms

namespace ShenWork.Paper3

noncomputable section

def intervalDomainActualLinearDanskinF
    (u : ℝ → intervalDomain.Point → ℝ) : ℝ → ℝ → ℝ :=
  fun s x => if 0 < s then intervalDomainLift (u s) x
    else intervalDomainSpatialMin u s

def intervalDomainActualLinearDanskinFt
    (u : ℝ → intervalDomain.Point → ℝ) : ℝ → ℝ → ℝ :=
  fun s x => if 0 < s then deriv (fun r => intervalDomainLift (u r) x) s else 0

theorem intervalDomain_lift_slice_continuousOn_of_positive
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {s : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) (hs : 0 < s) :
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

theorem intervalDomain_actualLinear_compactMinFamily
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    CompactMinFamily (Set.Icc (0 : ℝ) 1)
      (intervalDomainActualLinearDanskinF u) (intervalDomainSpatialMin u) := by
  constructor
  · intro s x hx
    by_cases hs : 0 < s
    · have hcont :=
        intervalDomain_lift_slice_continuousOn_of_positive (p := p) (v := v) hsol hs
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
        intervalDomain_lift_slice_continuousOn_of_positive (p := p) (v := v) hsol hs
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

#print axioms ShenWork.Paper3.intervalDomain_actualLinear_compactMinFamily
