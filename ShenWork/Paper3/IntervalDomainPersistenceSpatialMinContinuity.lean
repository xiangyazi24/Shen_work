import ShenWork.Paper3.IntervalDomainPersistenceDiniAudit2
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms
import ShenWork.Paper2.IntervalDomainSliceMinPos

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- The positive global bounded interval solution package supplies continuity
of the spatial minimum trajectory on every compact positive time window. -/
theorem intervalDomainSpatialMin_continuousOn_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 T : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hT0 : 0 < T0) (hT0T : T0 ≤ T) :
    ContinuousOn (intervalDomainSpatialMin u) (Set.Icc T0 T) := by
  have hTbig : 0 < T + 1 := by linarith
  have hclass := hsol.classical.classical (T := T + 1) hTbig
  have hsub : Set.Icc T0 T ⊆ Set.Ioo (0 : ℝ) (T + 1) := by
    intro s hs
    exact ⟨lt_of_lt_of_le hT0 hs.1, by linarith [hs.2]⟩
  have hsubprod : Set.Icc T0 T ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      Set.Ioo (0 : ℝ) (T + 1) ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono hsub (le_refl _)
  obtain ⟨_, _, _, _, _, _, h9⟩ := hclass.regularity
  set F : ℝ → ℝ → ℝ := fun t y => intervalDomainLift (u t) y
  have hF : ContinuousOn (Function.uncurry F)
      (Set.Icc T0 T ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [F] using h9.1.mono hsubprod
  have hm : ContinuousOn
      (fun t => sInf (F t '' Set.Icc (0 : ℝ) 1)) (Set.Icc T0 T) :=
    ShenWork.MinPersistenceAtoms.sliceMin_continuousOn hF
  refine hm.congr ?_
  intro t _ht
  simpa [F] using intervalDomainSpatialMin_eq_lift_sInf u t

/-- The spatial minimum is strictly positive at every positive time. -/
theorem intervalDomainSpatialMin_pos_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hT0 : 0 < T0) :
    0 < intervalDomainSpatialMin u T0 := by
  have hTbig : 0 < T0 + 1 := by linarith
  have hclass := hsol.classical.classical (T := T0 + 1) hTbig
  have hpos :=
    ShenWork.MinPersistenceAtoms.sliceMin_pos_of_solution
      hclass hT0 (by linarith : T0 < T0 + 1)
  rw [intervalDomainSpatialMin_eq_lift_sInf]
  exact hpos

#print axioms intervalDomainSpatialMin_continuousOn_of_positiveGlobalBoundedSolution
#print axioms intervalDomainSpatialMin_pos_of_positiveGlobalBoundedSolution

end

end ShenWork.Paper3
