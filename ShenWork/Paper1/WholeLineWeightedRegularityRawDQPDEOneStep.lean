import ShenWork.Paper1.WholeLineWeightedRegularityRawDQVolterraStep
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQIccProfile
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQLocalFubini
import ShenWork.Paper1.WholeLineWeightedRegularityWeightedRawDQRestart

open Filter MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Concrete one-step PDE inequality for the canonical raw-DQ profile

The source histories are realized with a crude uniform raw-energy bound, but
their pointwise estimates use the norm of the canonical profile itself.  This
is the non-circular input required by the singular Volterra closure.
-/

def rawDQHomogeneousMajorant
    (eta c T q F : ℝ) : ℝ :=
  ((2 * capMildGrowthBound eta c T * eta) +
      Real.exp eta *
        (2 * capMildGrowthBound eta c T * eta +
          (2 * capMildGrowthBound eta c T *
            (2 / Real.sqrt (4 * Real.pi))) *
              q ^ (-(1 / 2 : ℝ)))) * F

def rawDQFluxMajorant
    (p : CMParams) (M Brel DU eta c T h X F tau : ℝ) : ℝ :=
  (2 * capMildGrowthBound eta c T * eta +
      (2 * capMildGrowthBound eta c T *
        (2 / Real.sqrt (4 * Real.pi))) *
          tau ^ (-(1 / 2 : ℝ))) *
    (Real.sqrt (matchedFluxRawQSquareConstant p M eta) * X +
      Real.sqrt
        (matchedFluxRawWSquareConstant p M Brel DU eta h) * F)

def rawDQReactionMajorant
    (p : CMParams) (M DU eta c T X F : ℝ) : ℝ :=
  2 * capMildGrowthBound eta c T *
    (Real.sqrt (matchedShiftedReactionRawQSquareConstant p M) * X +
      Real.sqrt
        (matchedShiftedReactionRawWSquareConstant p M eta DU) * F)

/-- One-step raw-DQ estimate from the exact weighted restart identity.  All
`L²` representatives, history integrability, and physical Fubini formulas are
constructed internally. -/
theorem capWeightedCoMovingRawDQL2ProfileIcc_norm_le_restart_of_weighted_identity
    (p : CMParams) {M T Brel DU eta R c h a r X0 F : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hh : h ≠ 0) (habs : |h| ≤ 1)
    (ha0 : 0 ≤ a) (har : a < r) (hrT : r ≤ T)
    (hX0 : 0 ≤ X0) (hF : 0 ≤ F)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hWpos : ∀ x, 0 < W.1 x)
    (hbase : ∀ x, |(W.1 (x + h) - W.1 x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      |(W.1 (x + h) - W.1 x) / h| ≤
        Brel * (theta * W.1 (x + h) + (1 - theta) * W.1 x))
    (hvalue : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x =>
      capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2))
    (hraw : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x =>
      capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2))
    (hraw_energy : ∀ s ∈ Set.Icc (0 : ℝ) r,
      (∫ x : ℝ, capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2) ≤ X0 ^ 2)
    (hvalue_energy : ∀ s ∈ Set.Icc (0 : ℝ) r,
      (∫ x : ℝ, capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2) ≤ F ^ 2)
    (hidentity : ∀ x,
      capWeightSqrt eta R x *
          rawSpatialDifferenceQuotient eta h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj r).1 (y + c * r) -
              W.1 y) x =
        capWeightSqrt eta R x *
          paper5MovingFrameHeatOp c (r - a)
            (rawSpatialDifferenceQuotient eta h (fun y =>
              (wholeLineBUCTrajectoryExtend hT Traj a).1 (y + c * a) -
                W.1 y)) x +
        (-p.χ) * (∫ s in a..r,
          capWeightSqrt eta R x *
            paper5MovingFrameHeatGradOp c (r - s)
              (rawSpatialDifferenceQuotient eta h (fun y =>
                wholeLineCauchyCoMovingFluxSource p c hM hT Traj s y -
                  wholeLineChemotaxisFlux p W.1 y)) x) +
        ∫ s in a..r,
          capWeightSqrt eta R x *
            paper5MovingFrameHeatOp c (r - s)
              (rawSpatialDifferenceQuotient eta h (fun y =>
                wholeLineCauchyCoMovingReactionSource p c hM hT Traj s y -
                  wholeLineCauchyShiftedReaction p W.1 y)) x) :
    let hr0 : 0 ≤ r := ha0.trans har.le
    let hraw' : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x : ℝ =>
        capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2) volume := by
      intro s hs
      simpa only [rawSpatialDifferenceQuotient] using hraw s hs
    let hP2 := capWeightedCoMovingRawDQBUCHistoryIcc_sq_integrable
      hT hr0 eta R c h heta0 Traj W hraw'
    let P := capWeightedCoMovingRawDQL2ProfileIcc
      hT hr0 eta R c h heta0 Traj W hP2
    ‖P r‖ ≤ rawDQHomogeneousMajorant eta c T (r - a) F +
      |p.χ| * (∫ s in a..r,
        rawDQFluxMajorant p M Brel DU eta c T h ‖P s‖ F (r - s)) +
      ∫ s in a..r,
        rawDQReactionMajorant p M DU eta c T ‖P s‖ F := by
  dsimp only
  have hr0 : 0 ≤ r := ha0.trans har.le
  have hr : 0 < r := lt_of_le_of_lt ha0 har
  have hraw' : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x : ℝ =>
      capWeight eta R x *
        |rawSpatialDifferenceQuotient eta h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
            W.1 y) x| ^ 2) volume := by
    intro s hs
    simpa only [rawSpatialDifferenceQuotient] using hraw s hs
  let hP2 := capWeightedCoMovingRawDQBUCHistoryIcc_sq_integrable
    hT hr0 eta R c h heta0 Traj W hraw'
  let P := capWeightedCoMovingRawDQL2ProfileIcc
    hT hr0 eta R c h heta0 Traj W hP2
  have hPbound : ∀ s ∈ Set.Icc (0 : ℝ) r, ‖P s‖ ≤ X0 := by
    intro s hs
    apply (sq_le_sq₀ (norm_nonneg (P s)) hX0).mp
    rw [← capWeightedCoMovingRawDQL2ProfileIcc_energy_eq_norm_sq
      hT hr0 eta R c h heta0 Traj W hP2 hs]
    simpa only [rawSpatialDifferenceQuotient] using hraw_energy s hs
  have hPint0 : IntervalIntegrable P volume 0 r := by
    exact capWeightedCoMovingRawDQL2ProfileIcc_intervalIntegrable_of_bound
      hT hr0 eta R c h heta0 Traj W hP2 hPbound
  have huIcc : Set.uIcc a r ⊆ Set.uIcc (0 : ℝ) r := by
    rw [Set.uIcc_of_le har.le, Set.uIcc_of_le hr0]
    exact Set.Icc_subset_Icc_left ha0
  have hPint : IntervalIntegrable P volume a r := hPint0.mono_set huIcc
  let C0 : ℝ := 2 * capMildGrowthBound eta c T * eta
  let C1 : ℝ := 2 * capMildGrowthBound eta c T *
    (2 / Real.sqrt (4 * Real.pi))
  let AQ : ℝ := Real.sqrt (matchedFluxRawQSquareConstant p M eta)
  let AW : ℝ :=
    Real.sqrt (matchedFluxRawWSquareConstant p M Brel DU eta h)
  let RQ : ℝ := Real.sqrt (matchedShiftedReactionRawQSquareConstant p M)
  let RW : ℝ :=
    Real.sqrt (matchedShiftedReactionRawWSquareConstant p M eta DU)
  let gG : ℝ → ℝ := fun s =>
    rawDQFluxMajorant p M Brel DU eta c T h ‖P s‖ F (r - s)
  let gR : ℝ → ℝ := fun s =>
    rawDQReactionMajorant p M DU eta c T ‖P s‖ F
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0, capMildGrowthBound]
    positivity
  have hC1 : 0 ≤ C1 := by
    dsimp only [C1, capMildGrowthBound]
    positivity
  have hAQ : 0 ≤ AQ := Real.sqrt_nonneg _
  have hAW : 0 ≤ AW := Real.sqrt_nonneg _
  have hRQ : 0 ≤ RQ := Real.sqrt_nonneg _
  have hRW : 0 ≤ RW := Real.sqrt_nonneg _
  have hk0 : IntervalIntegrable
      (fun s : ℝ => C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) volume 0 r :=
    intervalIntegrable_const_add_mul_invSqrt_sub
  have hk : IntervalIntegrable
      (fun s : ℝ => C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) volume a r :=
    hk0.mono_set huIcc
  have hbG : IntervalIntegrable
      (fun s : ℝ => AQ * ‖P s‖ + AW * F) volume a r := by
    exact (hPint.norm.const_mul AQ).add intervalIntegrable_const
  have hBG : 0 ≤ AQ * X0 + AW * F :=
    add_nonneg (mul_nonneg hAQ hX0) (mul_nonneg hAW hF)
  have hgGcrude : IntervalIntegrable
      (fun s : ℝ =>
        (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) *
          (AQ * X0 + AW * F)) volume a r := hk.mul_const _
  have hgG_int : IntervalIntegrable gG volume a r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le har.le] at hk
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le har.le] at hbG
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le har.le] at hgGcrude
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le har.le]
    apply Integrable.mono' hgGcrude
    · simpa only [gG, rawDQFluxMajorant, C0, C1, AQ, AW] using
        hk.aestronglyMeasurable.mul hbG.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have hs0r : s ∈ Set.Icc (0 : ℝ) r := ⟨ha0.trans hs.1, hs.2⟩
      have hk_nonneg : 0 ≤ C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ)) :=
        add_nonneg hC0
          (mul_nonneg hC1 (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
      have hb_nonneg : 0 ≤ AQ * ‖P s‖ + AW * F :=
        add_nonneg (mul_nonneg hAQ (norm_nonneg _)) (mul_nonneg hAW hF)
      have hb_le : AQ * ‖P s‖ + AW * F ≤ AQ * X0 + AW * F := by
        gcongr
        exact hPbound s hs0r
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_mul_of_nonneg_left hb_le hk_nonneg
      · simpa only [gG, rawDQFluxMajorant, C0, C1, AQ, AW] using
          mul_nonneg hk_nonneg hb_nonneg
  have hbR : IntervalIntegrable
      (fun s : ℝ => RQ * ‖P s‖ + RW * F) volume a r := by
    exact (hPint.norm.const_mul RQ).add intervalIntegrable_const
  have hgR_int : IntervalIntegrable gR volume a r := by
    simpa only [gR, rawDQReactionMajorant, RQ, RW] using
      hbR.const_mul (2 * capMildGrowthBound eta c T)
  have hWquot : ∀ x, |spatialDifferenceQuotient h W.1 x| ≤ DU := by
    intro x
    simpa only [spatialDifferenceQuotient] using hbase x
  let hGF2 := capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_sq_integrable
    p hM hT hBrel hDU heta0 heta1 hh hr hrT hX0 hF Traj hstrip W
      hWmem hWpos hbase hrelative hvalue hraw hraw_energy hvalue_energy
  let hRF2 := capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_sq_integrable
    p hM hT hDU heta0 hh hr hrT hX0 hF Traj hstrip W hWmem hWquot
      hvalue hraw hraw_energy hvalue_energy
  let ZG : ℝ → WholeLineRealL2 := capWeightedCoMovingFluxRawDQL2History
    p hM hT eta R c h heta0 Traj W r hGF2
  let ZR : ℝ → WholeLineRealL2 := capWeightedCoMovingReactionRawDQL2History
    p hM hT eta R c h heta0 Traj W r hRF2
  have hZG0 : IntervalIntegrable ZG volume 0 r := by
    simpa only [ZG, hGF2] using
      capWeightedCoMovingFluxRawDQL2History_intervalIntegrable_of_uniform_cap
        p hM hT hBrel hDU heta0 heta1 hh hr hrT hX0 hF Traj hstrip W
          hWmem hWpos hbase hrelative hvalue hraw hraw_energy hvalue_energy
  have hZR0 : IntervalIntegrable ZR volume 0 r := by
    simpa only [ZR, hRF2] using
      capWeightedCoMovingReactionRawDQL2History_intervalIntegrable_of_uniform_cap
        p hM hT hDU heta0 hh hr hrT hX0 hF Traj hstrip W hWmem hWquot
          hvalue hraw hraw_energy hvalue_energy
  have hZG_int : IntervalIntegrable ZG volume a r := hZG0.mono_set huIcc
  have hZR_int : IntervalIntegrable ZR volume a r := hZR0.mono_set huIcc
  have hZG : ∀ s ∈ Set.Icc a r, ‖ZG s‖ ≤ gG s := by
    intro s hs
    by_cases hsr : s < r
    · have hs0r : s ∈ Set.Icc (0 : ℝ) r := ⟨ha0.trans hs.1, hs.2⟩
      have hE : (∫ x : ℝ, capWeight eta R x *
          |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
              W.1 x) +
            spatialDifferenceQuotient h (fun y =>
              (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
                W.1 y) x| ^ 2) ≤ ‖P s‖ ^ 2 := by
        rw [← capWeightedCoMovingRawDQL2ProfileIcc_energy_eq_norm_sq
          hT hr0 eta R c h heta0 Traj W hP2 hs0r]
        rfl
      have hnorm := capWeightedCoMovingFluxRawDQL2History_norm_le
        p hM hT hBrel hDU heta0 heta1 hh hrT (norm_nonneg (P s)) hF
          Traj hstrip W hWmem hWpos hbase hrelative (hvalue s hs0r)
          (hraw s hs0r) hE (hvalue_energy s hs0r) hGF2
          ⟨hs0r.1, hsr⟩
      simpa only [ZG, gG, rawDQFluxMajorant] using hnorm
    · have hsr' : ¬ s < r := hsr
      have hsEq : s = r := le_antisymm hs.2 (not_lt.mp hsr)
      subst s
      change ‖capWeightedCoMovingFluxRawDQL2History
        p hM hT eta R c h heta0 Traj W r hGF2 r‖ ≤ gG r
      rw [capWeightedCoMovingFluxRawDQL2History, if_neg (lt_irrefl r),
        norm_zero]
      dsimp only [gG, rawDQFluxMajorant]
      exact mul_nonneg
        (add_nonneg hC0 (mul_nonneg hC1 (Real.rpow_nonneg (by norm_num) _)))
        (add_nonneg
          (mul_nonneg hAQ (norm_nonneg _)) (mul_nonneg hAW hF))
  have hZR : ∀ s ∈ Set.Icc a r, ‖ZR s‖ ≤ gR s := by
    intro s hs
    by_cases hsr : s < r
    · have hs0r : s ∈ Set.Icc (0 : ℝ) r := ⟨ha0.trans hs.1, hs.2⟩
      have hE : (∫ x : ℝ, capWeight eta R x *
          |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
              W.1 x) +
            spatialDifferenceQuotient h (fun y =>
              (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
                W.1 y) x| ^ 2) ≤ ‖P s‖ ^ 2 := by
        rw [← capWeightedCoMovingRawDQL2ProfileIcc_energy_eq_norm_sq
          hT hr0 eta R c h heta0 Traj W hP2 hs0r]
        rfl
      have hnorm := capWeightedCoMovingReactionRawDQL2History_norm_le
        p hM hT hDU heta0 hh hrT (norm_nonneg (P s)) hF Traj hstrip W
          hWmem hWquot (hvalue s hs0r) (hraw s hs0r) hE
          (hvalue_energy s hs0r) hRF2 ⟨hs0r.1, hsr⟩
      simpa only [ZR, gR, rawDQReactionMajorant] using hnorm
    · have hsEq : s = r := le_antisymm hs.2 (not_lt.mp hsr)
      subst s
      change ‖capWeightedCoMovingReactionRawDQL2History
        p hM hT eta R c h heta0 Traj W r hRF2 r‖ ≤ gR r
      rw [capWeightedCoMovingReactionRawDQL2History,
        if_neg (lt_irrefl r), norm_zero]
      dsimp only [gR, rawDQReactionMajorant]
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (show 0 ≤ capMildGrowthBound eta c T by
            dsimp only [capMildGrowthBound]
            positivity))
        (add_nonneg
          (mul_nonneg hRQ (norm_nonneg _)) (mul_nonneg hRW hF))
  let f : WholeLineBUC := wholeLineBUCPointwiseSub
    (wholeLineBUCTranslate (c * a) (wholeLineBUCTrajectoryExtend hT Traj a)) W
  have ha0r : a ∈ Set.Icc (0 : ℝ) r := ⟨ha0, har.le⟩
  have hcap : Integrable (fun y : ℝ => capWeight eta R y * |f.1 y| ^ 2) := by
    simpa only [f, wholeLineBUCPointwiseSub_apply,
      wholeLineBUCTranslate_apply] using hvalue a ha0r
  have hcapE : (∫ y : ℝ, capWeight eta R y * |f.1 y| ^ 2) ≤ F ^ 2 := by
    simpa only [f, wholeLineBUCPointwiseSub_apply,
      wholeLineBUCTranslate_apply] using hvalue_energy a ha0r
  have hq : 0 < r - a := sub_pos.mpr har
  have hqT : r - a ≤ T := by linarith
  rcases exists_capWeightedMovingHeat_rawDQL2_le_const_add_invSqrt
      heta0 hq hqT hh habs hF f hcap hcapE with ⟨Z0, hZ0rep, hZ0norm⟩
  have hPrep : (((P r : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => capWeightSqrt eta R x *
        rawSpatialDifferenceQuotient eta h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj r).1 (y + c * r) -
            W.1 y) x) := by
    filter_upwards [capWeightedCoMovingRawDQL2ProfileIcc_coe_ae
      hT hr0 eta R c h heta0 Traj W hP2 (s := r)] with x hx
    rw [hx, capWeightedCoMovingRawDQBUCHistoryIcc_of_mem
      hT hr0 eta R c h heta0 Traj W ⟨hr0, le_rfl⟩]
    exact capWeightedCoMovingRawDQBUCHistory_apply
      hT eta R c h heta0 Traj W
  have hZGrep :=
    capWeightedCoMovingFluxRawDQL2History_local_integral_rep_physical
      p hM hT heta0 ha0 har hrT Traj W hWmem hGF2 hZG_int
  have hZRrep :=
    capWeightedCoMovingReactionRawDQL2History_local_integral_rep_physical
      p hM hT heta0 ha0 har hrT Traj W hWmem hRF2 hZR_int
  have hmain := wholeLineRealL2_norm_le_of_threeLeg_interval_with_coeff
    har.le (P r) Z0 ZG ZR
    (fun x => capWeightSqrt eta R x *
      rawSpatialDifferenceQuotient eta h (fun y =>
        (wholeLineBUCTrajectoryExtend hT Traj r).1 (y + c * r) - W.1 y) x)
    (fun x => capWeightSqrt eta R x *
      paper5MovingFrameHeatOp c (r - a)
        (rawSpatialDifferenceQuotient eta h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj a).1 (y + c * a) - W.1 y)) x)
    (fun x => ∫ s in a..r,
      capWeightSqrt eta R x * paper5MovingFrameHeatGradOp c (r - s)
        (rawSpatialDifferenceQuotient eta h (fun y =>
          wholeLineCauchyCoMovingFluxSource p c hM hT Traj s y -
            wholeLineChemotaxisFlux p W.1 y)) x)
    (fun x => ∫ s in a..r,
      capWeightSqrt eta R x * paper5MovingFrameHeatOp c (r - s)
        (rawSpatialDifferenceQuotient eta h (fun y =>
          wholeLineCauchyCoMovingReactionSource p c hM hT Traj s y -
            wholeLineCauchyShiftedReaction p W.1 y)) x)
    gG gR hZG_int hZR_int hgG_int hgR_int hZ0norm hZG hZR
    hPrep (by
      filter_upwards [hZ0rep] with x hx
      simpa only [f, wholeLineBUCPointwiseSub_apply,
        wholeLineBUCTranslate_apply] using hx)
    hZGrep hZRrep hidentity
  simpa only [gG, gR, rawDQHomogeneousMajorant, abs_neg] using hmain

#print axioms
  ShenWork.Paper1.capWeightedCoMovingRawDQL2ProfileIcc_norm_le_restart_of_weighted_identity

end ShenWork.Paper1
