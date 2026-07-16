import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorClosure

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive generator regularization of a full mild restart

This file records the exact algebra needed before the endpoint-generator
limit.  Applying a positive generator regularization to the full mild state
shifts every heat lag by the same positive amount.  No endpoint generator
domain or time derivative is assumed.
-/

/-- A positive generator regularization commutes through the full mild
candidate.  The only analytic premise is Bochner integrability of the
original heat history; boundedness of the regularizing continuous linear map
then supplies integrability after applying it. -/
theorem weightedMovingHeatL2Generator_apply_fullGeneratorCandidate
    {eta c a t eps : ℝ} (hat : a ≤ t) (heps : 0 < eps)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t) :
    weightedMovingHeatL2Generator eta c eps
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t) =
      weightedMovingHeatL2Generator eta c (eps + (t - a)) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Generator eta c (eps + (t - q)) (F q) := by
  let Aeps : WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
    weightedMovingHeatL2Generator eta c eps
  have hhom :
      Aeps (weightedMovingHeatL2Semigroup eta c (t - a) Z₀) =
        weightedMovingHeatL2Generator eta c (eps + (t - a)) Z₀ := by
    have hcomp := weightedMovingHeatL2Generator_comp_semigroup_add
      (eta := eta) (c := c) heps (sub_nonneg.mpr hat)
    exact DFunLike.congr_fun hcomp Z₀
  have hcommute := Aeps.intervalIntegral_comp_comm hhist
  have hint :
      Aeps (∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q)) =
        ∫ q in a..t,
          weightedMovingHeatL2Generator eta c (eps + (t - q)) (F q) := by
    rw [← hcommute]
    apply intervalIntegral.integral_congr
    intro q hq
    have hqt : q ≤ t := by
      rw [uIcc_of_le hat] at hq
      exact hq.2
    have hcomp := weightedMovingHeatL2Generator_comp_semigroup_add
      (eta := eta) (c := c) heps (sub_nonneg.mpr hqt)
    exact DFunLike.congr_fun hcomp (F q)
  unfold weightedMovingHeatFullGeneratorCandidate
  rw [map_add, hhom, hint]

section AxiomAudit

#print axioms
  weightedMovingHeatL2Generator_apply_fullGeneratorCandidate

end AxiomAudit

end ShenWork.Paper1
