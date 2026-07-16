import ShenWork.Paper1.WholeLineWeightedRegularityActualRightDerivativeNatural
import ShenWork.Paper1.WholeLineWeightedRegularitySemigroupHistoryNatural

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Actual weighted right derivatives from continuous forcing

The natural heat-history theorem makes both Duhamel integrability premises
of the actual-state endpoint-generator argument automatic.
-/

/-- Candidate equality and one continuous Hölder forcing trajectory suffice
for the full right derivative of the actual exact-weight state. -/
theorem paper5WeightedPopulation_hasDerivWithinAt_right_of_candidate_window_continuous
    {eta c a r t theta H K : ℝ}
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {F : ℝ → WholeLineRealL2}
    (hat : a < t) (htr : t < r)
    (htheta : 0 < theta) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hactual : ∀ s ∈ Set.Icc a r,
      wholeLineRealL2Total (paper5WeightedPopulation eta u U s) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta u U a)) F s)
    (hFbound : ∀ s ∈ Set.Icc a t, ‖F s‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a t, ∀ q ∈ Set.Icc a t,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hFcont : Continuous F) :
    HasDerivWithinAt
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta u U s))
      (weightedMovingHeatFullGeneratorValue eta c a t
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta u U a)) F + F t)
      (Set.Ici t) t := by
  apply
    paper5WeightedPopulation_hasDerivWithinAt_right_of_candidate_window_continuous_forcing
      hat htr htheta hH hK hactual hFbound hFholder
  · exact weightedMovingHeatL2Semigroup_intervalIntegrable_of_continuous
      hat.le hFcont
  · exact hFcont
  · intro h hh
    exact weightedMovingHeatL2Semigroup_intervalIntegrable_of_continuous
      (by linarith [hat]) hFcont

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedPopulation_hasDerivWithinAt_right_of_candidate_window_continuous
