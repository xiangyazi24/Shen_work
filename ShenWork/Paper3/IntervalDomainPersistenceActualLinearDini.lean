import ShenWork.Paper3.CompactMinDanskin
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearMinPoint

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

def ActualLinearSpatialMinimumDini
    (p : CM2Params) (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∀ t ∈ Set.Ioi (0 : ℝ),
    actualLinearLogisticRhs p (intervalDomainSpatialMin u t) ≤
      compactMinLowerRightDini (intervalDomainSpatialMin u) t

theorem ActualLinearSpatialMinimumDini.of_Danskin
    {p : CM2Params} {u : ℝ → intervalDomain.Point → ℝ}
    {f ft : ℝ → ℝ → ℝ}
    (H : CompactMinFamily (Set.Icc (0 : ℝ) 1) f (intervalDomainSpatialMin u))
    (hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      UniformRightDerivLowerOnCompact (Set.Icc (0 : ℝ) 1) f ft t)
    (htime : ∀ t ∈ Set.Ioi (0 : ℝ),
      UniformTimeContinuityOnCompact (Set.Icc (0 : ℝ) 1) f t)
    (hnear : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ eps > 0, ∃ rho > 0,
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        f t x ≤ intervalDomainSpatialMin u t + rho →
          actualLinearLogisticRhs p (intervalDomainSpatialMin u t) - eps ≤ ft t x)
    (hcobdd : ∀ t ∈ Set.Ioi (0 : ℝ),
      IsCoboundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) - intervalDomainSpatialMin u t) / h))
    (hbdd : ∀ t ∈ Set.Ioi (0 : ℝ),
      IsBoundedUnder GE.ge (𝓝[>] (0 : ℝ))
        (fun h : ℝ =>
          (intervalDomainSpatialMin u (t + h) - intervalDomainSpatialMin u t) / h)) :
    ActualLinearSpatialMinimumDini p u := by
  intro t ht
  exact lowerRightDini_min_ge_of_near_argmin_ft_lower H
    (hderiv t ht) (htime t ht) (hnear t ht) (hcobdd t ht) (hbdd t ht)

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.ActualLinearSpatialMinimumDini.of_Danskin
