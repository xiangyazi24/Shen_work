import ShenWork.Paper3.IntervalDomainPersistenceGeneralMRegularity
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMNearArgmin
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMSlopeBounds
import ShenWork.Paper3.IntervalDomainPersistenceDiniBridge

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- Lower-right Dini inequality for the faithful general-`m` spatial minimum. -/
def GeneralMSpatialMinimumDini
    (p : CM2Params) (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∀ t ∈ Set.Ioi (0 : ℝ),
    generalMLogisticRhs p (intervalDomainSpatialMin u t) ≤
      compactMinLowerRightDini (intervalDomainSpatialMin u) t

theorem GeneralMSpatialMinimumDini.of_Danskin
    {p : CM2Params} {u : ℝ → intervalDomain.Point → ℝ}
    {f ft : ℝ → ℝ → ℝ}
    (H : CompactMinFamily (Set.Icc (0 : ℝ) 1) f
      (intervalDomainSpatialMin u))
    (hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      UniformRightDerivLowerOnCompact (Set.Icc (0 : ℝ) 1) f ft t)
    (htime : ∀ t ∈ Set.Ioi (0 : ℝ),
      UniformTimeContinuityOnCompact (Set.Icc (0 : ℝ) 1) f t)
    (hnear : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ eps > 0, ∃ rho > 0,
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        f t x ≤ intervalDomainSpatialMin u t + rho →
          generalMLogisticRhs p (intervalDomainSpatialMin u t) - eps ≤ ft t x)
    (hcobdd : ∀ t ∈ Set.Ioi (0 : ℝ),
      IsCoboundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) -
              intervalDomainSpatialMin u t) / h))
    (hbdd : ∀ t ∈ Set.Ioi (0 : ℝ),
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) -
              intervalDomainSpatialMin u t) / h)) :
    GeneralMSpatialMinimumDini p u := by
  intro t ht
  exact lowerRightDini_min_ge_of_near_argmin_ft_lower H
    (hderiv t ht) (htime t ht) (hnear t ht) (hcobdd t ht) (hbdd t ht)

theorem intervalDomainM_generalMSpatialMinimumDini
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    GeneralMSpatialMinimumDini p u :=
  GeneralMSpatialMinimumDini.of_Danskin
    (intervalDomainM_generalM_compactMinFamily (p := p) (v := v) hsol)
    (intervalDomainM_generalM_uniformRightDerivLower hsol)
    (intervalDomainM_generalM_uniformTimeContinuity hsol)
    (intervalDomainM_generalM_nearArgmin_ft_lower hχ0 hβ hsol)
    (intervalDomainM_spatialMin_slope_isCoboundedUnder hsol)
    (intervalDomainM_spatialMin_slope_isBoundedUnder hsol)

theorem GeneralMSpatialMinimumDini.to_RightLowerDiniGE
    {p : CM2Params} {u : ℝ → intervalDomain.Point → ℝ}
    (hD : GeneralMSpatialMinimumDini p u)
    (hbdd : ∀ t ∈ Set.Ioi (0 : ℝ),
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) -
              intervalDomainSpatialMin u t) / h)) :
    RightLowerDiniGE (intervalDomainSpatialMin u)
      (generalMLogisticRhs p) (Set.Ioi (0 : ℝ)) :=
  rightLowerDiniGE_of_compactMinLowerRightDini hD hbdd

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_generalMSpatialMinimumDini
#print axioms ShenWork.Paper3.GeneralMSpatialMinimumDini.to_RightLowerDiniGE
