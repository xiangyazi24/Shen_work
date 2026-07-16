import ShenWork.Paper1.WholeLineWeightedRegularityRawDQHistory

open scoped Interval
open Set Filter MeasureTheory intervalIntegral

namespace ShenWork.Paper1

noncomputable section

/-!
# Local restart-window Fubini formulas for raw spatial difference quotients

The raw-DQ histories are totalized below time zero and at the terminal time
`r`.  On a physical restart subwindow `a..r`, with `0 ≤ a < r`, the lower
clamp is inactive.  These two formulas therefore identify the Bochner
integrals of the canonical `L²(ℝ)` histories with the genuine physical
chemotaxis and reaction source histories on exactly that restart window.
-/

/-- Exact physical-source Fubini representation for the flux raw-DQ history
on an arbitrary positive restart subwindow `a..r`. -/
theorem capWeightedCoMovingFluxRawDQL2History_local_integral_rep_physical
    (p : CMParams) {M T eta R c h a r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (ha : 0 ≤ a) (har : a < r) (hrT : r ≤ T)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume)
    (hZint : IntervalIntegrable
      (capWeightedCoMovingFluxRawDQL2History
        p hM hT eta R c h heta Traj W r hF2) volume a r) :
    ((((∫ s in a..r,
        capWeightedCoMovingFluxRawDQL2History
          p hM hT eta R c h heta Traj W r hF2 s) : WholeLineRealL2) :
          ℝ → ℝ) =ᵐ[volume] fun x =>
      ∫ s in a..r,
        capWeightSqrt eta R x *
          paper5MovingFrameHeatGradOp c (r - s)
            (rawSpatialDifferenceQuotient eta h (fun y =>
              wholeLineCauchyCoMovingFluxSource p c hM hT Traj s y -
                wholeLineChemotaxisFlux p W.1 y)) x) := by
  have hr : 0 < r := lt_of_le_of_lt ha har
  let Fh := capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
    p hM hT eta R c h heta Traj W r
  let Zbase := wholeLineRealL2Section
    (fun s x => (Fh s).1 x)
    (fun s => (Fh s).1.continuous.aestronglyMeasurable) hF2
  let Ztot := capWeightedCoMovingFluxRawDQL2History
    p hM hT eta R c h heta Traj W r hF2
  have hEq : Ztot =ᵐ[volume.restrict (Set.uIoc a r)] Zbase := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume r)] with s hs hne
    rw [Set.uIoc_of_le har.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hne
    simp only [Ztot, Zbase, capWeightedCoMovingFluxRawDQL2History,
      if_pos hsr, Fh]
  have hZbaseInt : IntervalIntegrable Zbase volume a r :=
    hZint.congr_ae hEq
  have hFmeas : AEStronglyMeasurable Fh
      (volume.restrict (Set.Ioc a r)) :=
    (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_aestronglyMeasurable
      p hM hT heta hr Traj W).restrict
  have hIoc : Set.Ioc a r ⊆ Set.Ioc (0 : ℝ) r := by
    intro s hs
    exact ⟨lt_of_le_of_lt ha hs.1, hs.2⟩
  have hFnorm : Integrable (fun s => ‖Fh s‖)
      (volume.restrict (Set.Ioc a r)) := by
    have hfull :=
      capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_norm_integrable
        p hM hT (R := R) (c := c) (h := h) heta hr Traj W
    exact hfull.mono_measure (Measure.restrict_mono hIoc le_rfl)
  have hrep := wholeLineRealL2_intervalIntegral_coe_ae_of_buc_history
    har.le hFmeas hFnorm hF2 hZbaseInt
  have hintEq : (∫ s in a..r, Ztot s) = ∫ s in a..r, Zbase s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume r] with s hne hs
    rw [Set.uIoc_of_le har.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hne
    simp only [Ztot, Zbase, capWeightedCoMovingFluxRawDQL2History,
      if_pos hsr, Fh]
  have hrepBase :
      ((((∫ s in a..r, Ztot s) : WholeLineRealL2) : ℝ → ℝ)
        =ᵐ[volume] fun x => ∫ s in a..r, (Fh s).1 x) := by
    simpa only [hintEq] using hrep
  filter_upwards [hrepBase] with x hx
  rw [hx]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume r] with s hne hs
  rw [Set.uIoc_of_le har.le] at hs
  have hsr : s < r := lt_of_le_of_ne hs.2 hne
  have hs0 : 0 ≤ s := ha.trans hs.1.le
  have hsT : s ∈ Set.Icc (0 : ℝ) T :=
    ⟨hs0, hs.2.trans hrT⟩
  dsimp only [Fh]
  rw [capWeightedCoMovingFluxRawDQBUCHistoryClampedIio,
    if_pos hsr, max_eq_right hs0]
  exact capWeightedCoMovingFluxRawDQBUCHistory_apply_fixedWave_of_lt
    p hM hT heta Traj W hWmem hsT hsr x

/-- Exact physical-source Fubini representation for the reaction raw-DQ
history on an arbitrary positive restart subwindow `a..r`. -/
theorem capWeightedCoMovingReactionRawDQL2History_local_integral_rep_physical
    (p : CMParams) {M T eta R c h a r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (ha : 0 ≤ a) (har : a < r) (hrT : r ≤ T)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume)
    (hZint : IntervalIntegrable
      (capWeightedCoMovingReactionRawDQL2History
        p hM hT eta R c h heta Traj W r hF2) volume a r) :
    ((((∫ s in a..r,
        capWeightedCoMovingReactionRawDQL2History
          p hM hT eta R c h heta Traj W r hF2 s) : WholeLineRealL2) :
          ℝ → ℝ) =ᵐ[volume] fun x =>
      ∫ s in a..r,
        capWeightSqrt eta R x *
          paper5MovingFrameHeatOp c (r - s)
            (rawSpatialDifferenceQuotient eta h (fun y =>
              wholeLineCauchyCoMovingReactionSource p c hM hT Traj s y -
                wholeLineCauchyShiftedReaction p W.1 y)) x) := by
  have hr : 0 < r := lt_of_le_of_lt ha har
  let Fh := capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
    p hM hT eta R c h heta Traj W r
  let Zbase := wholeLineRealL2Section
    (fun s x => (Fh s).1 x)
    (fun s => (Fh s).1.continuous.aestronglyMeasurable) hF2
  let Ztot := capWeightedCoMovingReactionRawDQL2History
    p hM hT eta R c h heta Traj W r hF2
  have hEq : Ztot =ᵐ[volume.restrict (Set.uIoc a r)] Zbase := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume r)] with s hs hne
    rw [Set.uIoc_of_le har.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hne
    simp only [Ztot, Zbase, capWeightedCoMovingReactionRawDQL2History,
      if_pos hsr, Fh]
  have hZbaseInt : IntervalIntegrable Zbase volume a r :=
    hZint.congr_ae hEq
  have hFmeas : AEStronglyMeasurable Fh
      (volume.restrict (Set.Ioc a r)) :=
    (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_aestronglyMeasurable
      p hM hT heta hr Traj W).restrict
  have hIoc : Set.Ioc a r ⊆ Set.Ioc (0 : ℝ) r := by
    intro s hs
    exact ⟨lt_of_le_of_lt ha hs.1, hs.2⟩
  have hFnorm : Integrable (fun s => ‖Fh s‖)
      (volume.restrict (Set.Ioc a r)) := by
    have hfull :=
      capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_norm_integrable
        p hM hT (R := R) (c := c) (h := h) heta hr Traj W
    exact hfull.mono_measure (Measure.restrict_mono hIoc le_rfl)
  have hrep := wholeLineRealL2_intervalIntegral_coe_ae_of_buc_history
    har.le hFmeas hFnorm hF2 hZbaseInt
  have hintEq : (∫ s in a..r, Ztot s) = ∫ s in a..r, Zbase s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume r] with s hne hs
    rw [Set.uIoc_of_le har.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hne
    simp only [Ztot, Zbase, capWeightedCoMovingReactionRawDQL2History,
      if_pos hsr, Fh]
  have hrepBase :
      ((((∫ s in a..r, Ztot s) : WholeLineRealL2) : ℝ → ℝ)
        =ᵐ[volume] fun x => ∫ s in a..r, (Fh s).1 x) := by
    simpa only [hintEq] using hrep
  filter_upwards [hrepBase] with x hx
  rw [hx]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume r] with s hne hs
  rw [Set.uIoc_of_le har.le] at hs
  have hsr : s < r := lt_of_le_of_ne hs.2 hne
  have hs0 : 0 ≤ s := ha.trans hs.1.le
  have hsT : s ∈ Set.Icc (0 : ℝ) T :=
    ⟨hs0, hs.2.trans hrT⟩
  dsimp only [Fh]
  rw [capWeightedCoMovingReactionRawDQBUCHistoryClampedIio,
    if_pos hsr, max_eq_right hs0]
  exact capWeightedCoMovingReactionRawDQBUCHistory_apply_fixedWave_of_lt
    p hM hT heta Traj W hWmem hsT hsr x

#print axioms
  ShenWork.Paper1.capWeightedCoMovingFluxRawDQL2History_local_integral_rep_physical
#print axioms
  ShenWork.Paper1.capWeightedCoMovingReactionRawDQL2History_local_integral_rep_physical

end

end ShenWork.Paper1
