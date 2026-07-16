import ShenWork.Paper1.WholeLineWeightedRegularityActualRightDerivative
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorHistoryNatural

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural right derivative of the actual weighted state

Continuity of the exact-weight forcing supplies the positive-lag generator
history measurability needed by the endpoint-generator argument.  Combining
that fact with the local equality between the actual state and its full mild
candidate removes both technical history premises from the actual-state
right-derivative theorem.
-/

/-- The actual weighted state has the full-generator right derivative on a
candidate window whenever the forcing is continuous and Hölder there. -/
theorem paper5WeightedPopulation_hasDerivWithinAt_right_of_candidate_window_continuous_forcing
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
    (hhist_t : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hFcont : Continuous F)
    (hhist_full : ∀ h, 0 < h → IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      volume a (t + h)) :
    HasDerivWithinAt
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta u U s))
      (weightedMovingHeatFullGeneratorValue eta c a t
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta u U a)) F + F t)
      (Set.Ici t) t := by
  let C : ℝ → WholeLineRealL2 :=
    weightedMovingHeatFullGeneratorCandidate eta c a
      (wholeLineRealL2Total (paper5WeightedPopulation eta u U a)) F
  have hC : HasDerivWithinAt C
      (weightedMovingHeatFullGeneratorValue eta c a t
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta u U a)) F + F t)
      (Set.Ici t) t := by
    exact
      weightedMovingHeatFullGeneratorCandidate_hasDerivWithinAt_right_of_continuous_forcing
        hat htheta hH hK hFbound hFholder hhist_t hFcont hhist_full
  have heq : (fun s => wholeLineRealL2Total
      (paper5WeightedPopulation eta u U s)) =ᶠ[𝓝[Set.Ici t] t] C := by
    have hright : ∀ᶠ s in 𝓝[Set.Ici t] t, t ≤ s :=
      self_mem_nhdsWithin
    have hupper_nhds : ∀ᶠ s in 𝓝 t, s < r := Iio_mem_nhds htr
    have hupper : ∀ᶠ s in 𝓝[Set.Ici t] t, s < r :=
      hupper_nhds.filter_mono inf_le_left
    filter_upwards [hright, hupper] with s hts hsr
    exact hactual s ⟨hat.le.trans hts, hsr.le⟩
  have heqAt : wholeLineRealL2Total
      (paper5WeightedPopulation eta u U t) = C t :=
    hactual t ⟨hat.le, htr.le⟩
  exact hC.congr_of_eventuallyEq heq heqAt

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedPopulation_hasDerivWithinAt_right_of_candidate_window_continuous_forcing
