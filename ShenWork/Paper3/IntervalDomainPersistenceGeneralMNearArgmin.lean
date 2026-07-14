import ShenWork.Paper3.CompactNearArgmin
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMCompactFamily

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- Near every faithful general-`m` spatial argmin, the time slope is bounded
below by the scalar minimum vector field, up to an arbitrary error. -/
theorem intervalDomainM_generalM_nearArgmin_ft_lower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∀ t ∈ Set.Ioi (0 : ℝ), ∀ eps > 0, ∃ rho > 0,
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        intervalDomainActualLinearDanskinF u t x ≤
          intervalDomainSpatialMin u t + rho →
          generalMLogisticRhs p (intervalDomainSpatialMin u t) - eps ≤
            intervalDomainActualLinearDanskinFt u t x := by
  intro t ht
  have htpos : 0 < t := ht
  have hTpos : 0 < t + 1 := by linarith
  have hclass := hsol.classical.classical (T := t + 1) hTpos
  obtain ⟨_, _, _, _, _, hJDt, _⟩ := hclass.regularity
  set F0 : ℝ → ℝ := fun x => intervalDomainActualLinearDanskinF u t x
  set dF0 : ℝ → ℝ := fun x => intervalDomainActualLinearDanskinFt u t x
  have H := intervalDomainM_generalM_compactMinFamily (p := p) (v := v) hsol
  have hF0 : ContinuousOn F0 (Set.Icc (0 : ℝ) 1) := by
    have hbase :=
      intervalDomainM_lift_slice_continuousOn_of_positive (p := p) (v := v)
        hsol htpos
    simpa [F0, intervalDomainActualLinearDanskinF, htpos] using hbase
  have hdFbase : ContinuousOn
      (fun x => deriv (fun r => intervalDomainLift (u r) x) t)
      (Set.Icc (0 : ℝ) 1) := by
    have hmap : Set.MapsTo (fun x : ℝ => (t, x)) (Set.Icc (0 : ℝ) 1)
        (Set.Ioo (0 : ℝ) (t + 1) ×ˢ Set.Icc (0 : ℝ) 1) :=
      fun x hx => ⟨⟨htpos, by linarith⟩, hx⟩
    exact hJDt.1.comp (Continuous.continuousOn (by fun_prop)) hmap
  have hdF0 : ContinuousOn dF0 (Set.Icc (0 : ℝ) 1) := by
    simpa [dF0, intervalDomainActualLinearDanskinFt, htpos] using hdFbase
  refine compact_near_argmin_lower_of_exact isCompact_Icc
    (fun x hx => H.z_le t x hx) hF0 hdF0 ?_
  intro x hx hFx
  let xp : intervalDomain.Point := ⟨x, hx⟩
  have hFx_lift : intervalDomainLift (u t) x = intervalDomainSpatialMin u t := by
    simpa [F0, intervalDomainActualLinearDanskinF, htpos] using hFx
  have hmin : ∀ y : intervalDomain.Point, u t xp ≤ u t y := by
    intro y
    have hzy := H.z_le t y.1 y.2
    have hzyu : intervalDomainSpatialMin u t ≤ u t y := by
      simpa [intervalDomainActualLinearDanskinF, htpos,
        intervalDomainLift] using hzy
    have hliftx : intervalDomainLift (u t) x = u t xp := by
      rw [intervalDomainLift, dif_pos hx]
    have hux : u t xp = intervalDomainSpatialMin u t := by
      rw [← hliftx]
      exact hFx_lift
    rw [hux]
    exact hzyu
  have hbd := intervalDomain_generalM_min_point_slope_bound
    hχ0 hβ hclass htpos (by linarith : t < t + 1) (x := xp) hmin
  have hfun : (fun r => intervalDomainLift (u r) x) =
      fun r => u r xp := by
    funext r
    rw [intervalDomainLift, dif_pos hx]
  have hleft : generalMLogisticRhs p (intervalDomainSpatialMin u t) =
      generalMLogisticRhs p (intervalDomainLift (u t) x) := by
    rw [hFx_lift]
  simpa [dF0, intervalDomainActualLinearDanskinFt, htpos, hfun,
    hleft] using hbd

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_generalM_nearArgmin_ft_lower
