import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartNatural
import ShenWork.Paper1.WholeLineWeightedRegularitySemigroupHistoryNatural

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Continuity inherited from an exact full-generator restart

Once the physical weighted state equals its full mild candidate on a compact
window, continuity is a consequence rather than an independent hypothesis.
-/

/-- Uniformly bounded measurable forcing on an ambient window already makes
the full candidate continuous.  Equality with that candidate transfers the
continuity to the physical weighted state. -/
theorem paper5WeightedPopulation_continuousOn_of_candidate_window_uniform_forcing
    {eta c L R a r K : ℝ}
    (hLa : L < a) (har : a ≤ r) (hrR : r < R)
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {F : ℝ → WholeLineRealL2}
    (hK : 0 ≤ K)
    (hFbound : ∀ q ∈ Set.Icc L R, ‖F q‖ ≤ K)
    (hhist : ∀ t : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.uIoc L R)))
    (hactual : ∀ s ∈ Set.Icc a r,
      wholeLineRealL2Total (paper5WeightedPopulation eta u U s) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta u U a)) F s) :
    ContinuousOn
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta u U s))
      (Set.Icc a r) := by
  have hcandidate : ContinuousOn
      (weightedMovingHeatFullGeneratorCandidate eta c a
        (wholeLineRealL2Total
          (paper5WeightedPopulation eta u U a)) F)
      (Set.Icc a r) :=
    weightedMovingHeatFullGeneratorCandidate_continuousOn_of_uniform_norm_bound
      (eta := eta) (c := c) hLa har hrR _ hK hFbound hhist
  exact hcandidate.congr hactual

/-- Equality with a full-generator candidate driven by a continuous forcing
makes the actual weighted state continuous on the restart window. -/
theorem paper5WeightedPopulation_continuousOn_of_candidate_window_continuous_forcing
    {eta c a r : ℝ} (har : a ≤ r)
    {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {F : ℝ → WholeLineRealL2}
    (hFcont : Continuous F)
    (hactual : ∀ s ∈ Set.Icc a r,
      wholeLineRealL2Total (paper5WeightedPopulation eta u U s) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta u U a)) F s) :
    ContinuousOn
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta u U s))
      (Set.Icc a r) := by
  let L : ℝ := a - 1
  let R : ℝ := r + 1
  have hLa : L < a := by dsimp only [L]; linarith
  have hrR : r < R := by dsimp only [R]; linarith
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hFcont.continuousOn.norm
  let K : ℝ := max B 0
  have hK : 0 ≤ K := le_max_right _ _
  have hFbound : ∀ q ∈ Set.Icc L R, ‖F q‖ ≤ K := by
    intro q hq
    exact (hB (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)
  have hhist : ∀ t : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      (volume.restrict (Set.uIoc L R)) := by
    intro t
    exact
      (weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable
        (eta := eta) (c := c) (tau := t) hFcont).mono_measure
          Measure.restrict_le_self
  exact paper5WeightedPopulation_continuousOn_of_candidate_window_uniform_forcing
    hLa har hrR hK hFbound hhist hactual

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedPopulation_continuousOn_of_candidate_window_uniform_forcing
#print axioms
  ShenWork.Paper1.paper5WeightedPopulation_continuousOn_of_candidate_window_continuous_forcing
