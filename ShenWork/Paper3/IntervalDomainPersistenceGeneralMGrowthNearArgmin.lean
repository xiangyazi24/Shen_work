import ShenWork.Paper3.CompactNearArgmin
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMCompactFamily
import ShenWork.Paper2.IntervalDomainMMinimumPersistence

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMMinPersistence

namespace ShenWork.Paper3

noncomputable section

/-- Near every faithful general-`m` spatial argmin, a common slice ceiling
gives the all-sign time-slope lower bound that retains linear logistic growth.
The ceiling is an explicit hypothesis, so this theorem can be applied after a
small-minimum/oscillation argument without assuming a global small solution. -/
theorem intervalDomainM_generalM_growth_nearArgmin_ft_lower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    ∀ t ∈ Set.Ioi (0 : ℝ), ∀ M ≥ 0,
      (∀ y, |intervalDomainLift (u t) y| ≤ M) →
      ∀ eps > 0, ∃ rho > 0,
        ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
          intervalDomainActualLinearDanskinF u t x ≤
              intervalDomainSpatialMin u t + rho →
            generalMMinGrowthRate p M * intervalDomainSpatialMin u t - eps ≤
              intervalDomainActualLinearDanskinFt u t x := by
  intro t ht M hM hu_bd
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
  have hFx_lift : intervalDomainLift (u t) x = intervalDomainSpatialMin u t := by
    simpa [F0, intervalDomainActualLinearDanskinF, htpos] using hFx
  have hargmin : intervalDomainLift (u t) x =
      sInf (intervalDomainLift (u t) '' Set.Icc (0 : ℝ) 1) :=
    hFx_lift.trans (intervalDomainSpatialMin_eq_lift_sInf u t)
  have hbd :=
    ShenWork.Paper2.IntervalDomainMMinPersistence.hbound_closed_M_allChi_with_growth
      hm hclass htpos (by linarith : t < t + 1) hM hu_bd hx hargmin
  simpa [dF0, intervalDomainActualLinearDanskinFt, htpos,
    intervalDomainSpatialMin_eq_lift_sInf] using hbd

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_generalM_growth_nearArgmin_ft_lower
