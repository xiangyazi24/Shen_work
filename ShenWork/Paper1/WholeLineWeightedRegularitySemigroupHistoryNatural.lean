import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartNatural

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural exact-weight heat histories

A continuous `L²` forcing trajectory automatically gives measurable and
interval-integrable weighted heat histories.  The totalized semigroup has a
jump across negative lag, but for a terminal history that jump occurs at one
time slice only and is discarded by the Lebesgue measure.
-/

/-- A positive-lag heat orbit remains continuous when its datum varies
continuously. -/
theorem weightedMovingHeatL2Semigroup_variableDatum_continuousAt_of_pos
    {eta c tau q0 : ℝ} (hpos : 0 < tau - q0)
    {F : ℝ → WholeLineRealL2} (hF : ContinuousAt F q0) :
    ContinuousAt
      (fun q => weightedMovingHeatL2Semigroup eta c (tau - q) (F q))
      q0 := by
  let r0 : ℝ := tau - q0
  let l : ℝ := r0 / 2
  let R : ℝ := 2 * r0
  let C : ℝ := Real.exp (|eta ^ 2 - c * eta| * R)
  let D : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Semigroup eta c (tau - q) (F q - F q0)
  have hr0 : 0 < r0 := by simpa only [r0] using hpos
  have hl : 0 < l := by dsimp only [l]; linarith
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hlag : Tendsto (fun q : ℝ => tau - q) (𝓝 q0) (𝓝 r0) := by
    simpa only [r0] using continuousAt_const.sub continuousAt_id
  have hnear : ∀ᶠ q : ℝ in 𝓝 q0, tau - q ∈ Set.Ioo l R :=
    hlag (Ioo_mem_nhds (by dsimp only [l]; linarith)
      (by dsimp only [R]; linarith))
  have hdiff : Tendsto (fun q : ℝ => F q - F q0) (𝓝 q0) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => F q0) (𝓝 q0) (𝓝 (F q0)) :=
      tendsto_const_nhds
    have hraw : Tendsto (fun q : ℝ => F q - F q0) (𝓝 q0)
        (𝓝 (F q0 - F q0)) := hF.sub hconst
    simpa only [sub_self] using hraw
  have hdiff_norm : Tendsto (fun q : ℝ => ‖F q - F q0‖)
      (𝓝 q0) (𝓝 0) := by
    simpa only [norm_zero] using hdiff.norm
  have hmajor : Tendsto (fun q : ℝ => C * ‖F q - F q0‖)
      (𝓝 q0) (𝓝 0) := by
    simpa only [mul_zero] using hdiff_norm.const_mul C
  have hD0 : Tendsto D (𝓝 q0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun q => norm_nonneg (D q)) ?_
      hmajor
    filter_upwards [hnear] with q hq
    have hlagIcc : tau - q ∈ Set.Icc (0 : ℝ) R :=
      ⟨hl.le.trans hq.1.le, hq.2.le⟩
    exact
      (weightedMovingHeatL2Semigroup_norm_apply_le_on_lag_window
        (eta := eta) (c := c) hlagIcc (F q - F q0)).trans_eq rfl
  have hfixed : ContinuousAt
      (fun q : ℝ => weightedMovingHeatL2Semigroup eta c (tau - q) (F q0))
      q0 := by
    have horbit :=
      (weightedMovingHeatL2Semigroup_orbit_continuousAt_of_ne_zero
        (eta := eta) (c := c) (F q0) hr0.ne').tendsto.comp hlag
    simpa only [r0, Function.comp_apply] using horbit
  have hsum := hD0.add hfixed
  simpa only [D, map_sub, sub_add_cancel, zero_add] using hsum

/-- A continuous forcing gives a continuous terminal heat history before
the terminal slice. -/
theorem weightedMovingHeatL2Semigroup_terminal_history_continuousOn_Iio
    {eta c tau : ℝ} {F : ℝ → WholeLineRealL2} (hF : Continuous F) :
    ContinuousOn
      (fun q => weightedMovingHeatL2Semigroup eta c (tau - q) (F q))
      (Set.Iio tau) := by
  intro q hq
  exact
    (weightedMovingHeatL2Semigroup_variableDatum_continuousAt_of_pos
      (eta := eta) (c := c) (sub_pos.mpr hq) hF.continuousAt).continuousWithinAt

/-- The terminal heat history of a continuous forcing is strongly
measurable.  Its sole totalization seam is a null singleton. -/
theorem weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable
    {eta c tau : ℝ} {F : ℝ → WholeLineRealL2} (hF : Continuous F) :
    AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (tau - q) (F q))
      volume := by
  let G : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Semigroup eta c (tau - q) (F q)
  have hGlt : AEStronglyMeasurable G (volume.restrict (Set.Iio tau)) :=
    (weightedMovingHeatL2Semigroup_terminal_history_continuousOn_Iio
      (eta := eta) (c := c) (tau := tau) hF).aestronglyMeasurable
        measurableSet_Iio
  have hind : AEStronglyMeasurable ((Set.Iio tau).indicator G) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hGlt
  refine hind.congr ?_
  filter_upwards [Measure.ae_ne volume tau] with q hq
  by_cases hlt : q < tau
  · simp [Set.indicator, hlt, G]
  · have hgt : tau < q := lt_of_le_of_ne (le_of_not_gt hlt) hq.symm
    have hlag : tau - q < 0 := sub_neg.mpr hgt
    simp [Set.indicator, hlt, G, weightedMovingHeatL2Semigroup,
      not_lt.mpr hlag.le, hlag.ne]

/-- A continuous forcing with a uniform norm bound has an integrable heat
history on a finite forward interval. -/
theorem weightedMovingHeatL2Semigroup_intervalIntegrable_of_continuous_bound
    {eta c a r K : ℝ} (har : a ≤ r) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2} (hF : Continuous F)
    (hFbound : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K) :
    IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      volume a r := by
  apply weightedMovingHeatL2Semigroup_intervalIntegrable_of_uniform_norm_bound
    har hK hFbound
  exact
    (weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable
      (eta := eta) (c := c) (tau := r) hF).mono_measure
      Measure.restrict_le_self

/-- Continuity alone supplies the compact-interval norm bound, hence every
finite forward terminal heat history is interval-integrable. -/
theorem weightedMovingHeatL2Semigroup_intervalIntegrable_of_continuous
    {eta c a r : ℝ} (har : a ≤ r)
    {F : ℝ → WholeLineRealL2} (hF : Continuous F) :
    IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      volume a r := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hF.continuousOn.norm
  let K : ℝ := max B 0
  have hK : 0 ≤ K := le_max_right _ _
  have hFbound : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K := by
    intro q hq
    exact (hB (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)
  exact weightedMovingHeatL2Semigroup_intervalIntegrable_of_continuous_bound
    har hK hF hFbound

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.weightedMovingHeatL2Semigroup_variableDatum_continuousAt_of_pos
#print axioms
  ShenWork.Paper1.weightedMovingHeatL2Semigroup_terminal_history_continuousOn_Iio
#print axioms
  ShenWork.Paper1.weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable
#print axioms
  ShenWork.Paper1.weightedMovingHeatL2Semigroup_intervalIntegrable_of_continuous_bound
#print axioms
  ShenWork.Paper1.weightedMovingHeatL2Semigroup_intervalIntegrable_of_continuous
