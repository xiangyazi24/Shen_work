import ShenWork.Paper1.WholeLineWeightedRegularityMildRightDerivative

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural measurability of positive generator histories

At every strictly positive lag, the generator-regularized heat orbit is
strongly continuous.  A locally uniform operator-norm bound lets the datum
vary continuously as well.  Consequently the generator histories occurring
in the exact-weight mild right-derivative theorem are automatically strongly
measurable; they need not be carried as separate hypotheses.
-/

/-- The positive-lag generator stays continuous when its `L²` datum varies
continuously.  The proof separates the fixed-datum orbit from the datum
increment and controls the latter by the local positive-time operator norm. -/
theorem weightedMovingHeatL2Generator_variableDatum_continuousAt_of_pos
    {eta c tau r0 : ℝ} (hr0 : 0 < r0)
    {F : ℝ → WholeLineRealL2}
    (hF : ContinuousAt F (tau - r0)) :
    ContinuousAt
      (fun r => weightedMovingHeatL2Generator eta c r (F (tau - r)))
      r0 := by
  let l : ℝ := r0 / 2
  let R : ℝ := 2 * r0
  let C : ℝ :=
    weightedMovingHeatGeneratorHorizonConst eta c R * l⁻¹
  let D : ℝ → WholeLineRealL2 := fun r =>
    weightedMovingHeatL2Generator eta c r
      (F (tau - r) - F (tau - r0))
  have hl : 0 < l := by
    dsimp only [l]
    linarith
  have hR : 0 ≤ R := by
    dsimp only [R]
    linarith
  have harg : ContinuousAt (fun r : ℝ => tau - r) r0 :=
    continuousAt_const.sub continuousAt_id
  have hFarg : Tendsto (fun r : ℝ => F (tau - r)) (nhds r0)
      (nhds (F (tau - r0))) := hF.comp harg
  have hdiff : Tendsto
      (fun r : ℝ => F (tau - r) - F (tau - r0))
      (nhds r0) (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => F (tau - r0)) (nhds r0)
        (nhds (F (tau - r0))) := tendsto_const_nhds
    simpa only [sub_self] using hFarg.sub hconst
  have hdiff_norm : Tendsto
      (fun r : ℝ => ‖F (tau - r) - F (tau - r0)‖)
      (nhds r0) (nhds 0) := by
    simpa only [norm_zero] using hdiff.norm
  have hmajor : Tendsto
      (fun r : ℝ => C * ‖F (tau - r) - F (tau - r0)‖)
      (nhds r0) (nhds 0) := by
    simpa only [mul_zero] using hdiff_norm.const_mul C
  have hnear : ∀ᶠ r : ℝ in nhds r0, r ∈ Set.Ioo l R := by
    apply Ioo_mem_nhds <;> dsimp only [l, R] <;> linarith
  have hD0 : Tendsto D (nhds r0) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg (D r)) ?_ hmajor
    filter_upwards [hnear] with r hr
    have hrpos : 0 < r := hl.trans hr.1
    have hAnorm := weightedMovingHeatL2Generator_norm_le_horizon
      eta c R r ⟨hrpos, hr.2.le⟩
    have hinv : r ^ (-(1 : ℝ)) ≤ l⁻¹ := by
      rw [Real.rpow_neg_one]
      simpa only [one_div] using one_div_le_one_div_of_le hl hr.1.le
    have hAcoarse :
        ‖weightedMovingHeatL2Generator eta c r‖ ≤ C := by
      have hCnonneg :
          0 ≤ weightedMovingHeatGeneratorHorizonConst eta c R :=
        weightedMovingHeatGeneratorHorizonConst_nonneg
          (eta := eta) (c := c) hR
      have hmul := mul_le_mul_of_nonneg_left hinv
        hCnonneg
      exact hAnorm.trans (by simpa only [C] using hmul)
    calc
      ‖D r‖ ≤ ‖weightedMovingHeatL2Generator eta c r‖ *
          ‖F (tau - r) - F (tau - r0)‖ := by
        exact (weightedMovingHeatL2Generator eta c r).le_opNorm _
      _ ≤ C * ‖F (tau - r) - F (tau - r0)‖ := by
        exact mul_le_mul_of_nonneg_right hAcoarse (norm_nonneg _)
  have hfixed := weightedMovingHeatL2Generator_orbit_continuousAt_of_pos
    (eta := eta) (c := c) hr0 (F (tau - r0))
  have hsum := hD0.add hfixed
  simpa only [D, map_sub, sub_add_cancel, zero_add] using hsum

/-- A continuous forcing trajectory gives a continuous generator history on
the entire positive-lag half-line. -/
theorem weightedMovingHeatL2Generator_history_continuousOn_Ioi
    {eta c tau : ℝ} {F : ℝ → WholeLineRealL2}
    (hF : Continuous F) :
    ContinuousOn
      (fun r => weightedMovingHeatL2Generator eta c r (F (tau - r)))
      (Set.Ioi 0) := by
  intro r hr
  exact
    (weightedMovingHeatL2Generator_variableDatum_continuousAt_of_pos
      (eta := eta) (c := c) (tau := tau) hr hF.continuousAt).continuousWithinAt

/-- Restricting a positive-lag generator history to a measurable set preserves
strong measurability. -/
theorem weightedMovingHeatL2Generator_history_aestronglyMeasurable_restrict
    {eta c tau : ℝ} {F : ℝ → WholeLineRealL2}
    (hF : Continuous F) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Set.Ioi 0) :
    AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r (F (tau - r)))
      (volume.restrict s) := by
  exact
    ((weightedMovingHeatL2Generator_history_continuousOn_Ioi
      (eta := eta) (c := c) (tau := tau) hF).mono hsub).aestronglyMeasurable hs

/-- The base generator history is strongly measurable on every interval
`(0,H]`; no condition on the sign of `H` is needed. -/
theorem weightedMovingHeatL2Generator_history_aestronglyMeasurable_Ioc
    {eta c tau H : ℝ} {F : ℝ → WholeLineRealL2}
    (hF : Continuous F) :
    AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r (F (tau - r)))
      (volume.restrict (Set.Ioc 0 H)) := by
  apply weightedMovingHeatL2Generator_history_aestronglyMeasurable_restrict
    (eta := eta) (c := c) (tau := tau) hF measurableSet_Ioc
  intro r hr
  exact hr.1

/-- A generator history is strongly measurable on every closed interval whose
left endpoint is strictly positive. -/
theorem weightedMovingHeatL2Generator_history_aestronglyMeasurable_Icc_of_pos
    {eta c tau e H : ℝ} {F : ℝ → WholeLineRealL2}
    (hF : Continuous F) (he : 0 < e) :
    AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r (F (tau - r)))
      (volume.restrict (Set.Icc e H)) := by
  apply weightedMovingHeatL2Generator_history_aestronglyMeasurable_restrict
    (eta := eta) (c := c) (tau := tau) hF measurableSet_Icc
  intro r hr
  exact he.trans_le hr.1

/-- Natural version of the exact-weight mild right-derivative theorem.
Continuity of the forcing trajectory automatically supplies both generator
history measurability inputs and its endpoint continuity. -/
theorem weightedMovingHeatFullGeneratorCandidate_hasDerivWithinAt_right_of_continuous_forcing
    {eta c a t theta H K : ℝ}
    (hat : a < t) (htheta : 0 < theta)
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hFbound : ∀ s ∈ Set.Icc a t, ‖F s‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a t, ∀ q ∈ Set.Icc a t,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hhist_t : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t)
    (hF : Continuous F)
    (hhist_full : ∀ h, 0 < h → IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t + h - q) (F q))
      volume a (t + h)) :
    HasDerivWithinAt
      (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F)
      (weightedMovingHeatFullGeneratorValue eta c a t Z₀ F + F t)
      (Set.Ici t) t := by
  apply weightedMovingHeatFullGeneratorCandidate_hasDerivWithinAt_right
    (F := F) (Z₀ := Z₀) hat htheta hH hK hFbound hFholder hhist_t
  · exact weightedMovingHeatL2Generator_history_aestronglyMeasurable_Ioc
      (eta := eta) (c := c) (tau := t) hF
  · intro e he _
    exact weightedMovingHeatL2Generator_history_aestronglyMeasurable_Icc_of_pos
      (eta := eta) (c := c) (tau := t + e) hF he
  · exact hF.continuousAt
  · exact hhist_full

section AxiomAudit

#print axioms
  weightedMovingHeatL2Generator_variableDatum_continuousAt_of_pos
#print axioms weightedMovingHeatL2Generator_history_continuousOn_Ioi
#print axioms
  weightedMovingHeatL2Generator_history_aestronglyMeasurable_restrict
#print axioms
  weightedMovingHeatL2Generator_history_aestronglyMeasurable_Ioc
#print axioms
  weightedMovingHeatL2Generator_history_aestronglyMeasurable_Icc_of_pos
#print axioms
  weightedMovingHeatFullGeneratorCandidate_hasDerivWithinAt_right_of_continuous_forcing

end AxiomAudit

end ShenWork.Paper1
