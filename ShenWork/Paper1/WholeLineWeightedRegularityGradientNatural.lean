import ShenWork.Paper1.WholeLineWeightedRegularityRawDQH0Wave
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQPDEOneStep
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQScalarization
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQTargetHenry
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQDerivativeClosure
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQCrudeCanonical
import ShenWork.Paper1.WholeLineWeightedRegularitySlice

open Filter Function MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural positive-time weighted gradient producer

The exact-weight `H0` estimate is selected once, independently of both the
cap radius and the canonical spatial-difference step.  Fixed-horizon raw-DQ
profiles then satisfy a common Henry inequality, and the cap/step-uniform
bound passes to the classical spatial derivative by Fatou.
-/

/-- The traveling-wave `H0` producer can be normalized so that its exact
exponential-weight radius is chosen before any spatial-difference step. -/
theorem exists_uniform_fullWeighted_mildFixedPoint_wave_value_inputs_finiteHorizon
    (p : CMParams)
    {M T eta c B₀ D E Kflux FD B : ℝ}
    (hT : 0 ≤ T) (heta : 0 < eta) (heta_one : eta < 1)
    (hB₀ : 0 ≤ B₀)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hMChi : MChi p ≤ M)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ t, 0 < t → ∀ x, IntervalIntegrable
      (fun q : ℝ => paper5MovingFrameHeatGradOp c q
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 t)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀.1 y - Uw y| ^ 2))
    (hdata_energy : (∫ y : ℝ, Real.exp (2 * eta * y) *
      |u₀.1 y - Uw y| ^ 2) ≤ B₀ ^ 2) :
    ∃ F : ℝ, 0 ≤ F ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
          |(wholeLineBUCTrajectoryExtend hT
              (wholeLineCauchyBUCMildFixedPoint p
                (zero_le_one.trans
                  ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
                hT u₀ hsmall) s).1 (x + c * s) - Uw x| ^ 2) ∧
        (∫ x : ℝ, Real.exp (2 * eta * x) *
          |(wholeLineBUCTrajectoryExtend hT
              (wholeLineCauchyBUCMildFixedPoint p
                (zero_le_one.trans
                  ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
                hT u₀ hsmall) s).1 (x + c * s) - Uw x| ^ 2) ≤ F ^ 2 := by
  have hM : 0 ≤ M :=
    zero_le_one.trans ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi)
  obtain ⟨F, X, hF, _hX, _hXeq, hcap⟩ :=
    exists_uniform_capWeighted_mildFixedPoint_wave_value_rawDQ_inputs_finiteHorizon
      p hT heta heta_one (by norm_num : (1 : ℝ) ≠ 0) hB₀ u₀ hsmall
        hTW hbound hreg hMChi hD hFD hB hUd hUdd hUddcont hflux
        hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
        hdata_full hdata_energy
  refine ⟨F, hF, ?_⟩
  intro s hs
  let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let w : ℝ → ℝ := fun x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - Uw x
  have hw : Continuous w := by
    exact ((wholeLineBUCTrajectoryExtend hT Traj s).1.continuous.comp
      (continuous_id.add continuous_const)).sub hreg.U_cont
  have hcap_int : ∀ n : ℕ,
      Integrable (fun x : ℝ => capWeight eta (n : ℝ) x * |w x| ^ 2) := by
    intro n
    simpa only [w, Traj] using (hcap (n : ℝ)).1 s hs
  have hcap_bound : ∀ n : ℕ,
      (∫ x : ℝ, capWeight eta (n : ℝ) x * |w x| ^ 2) ≤ F ^ 2 := by
    intro n
    simpa only [w, Traj] using (hcap (n : ℝ)).2.2.2 s hs
  have hfull : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |w x| ^ 2) :=
    fullWeightedL2_integrable_of_uniform_cap
      (C := F ^ 2) heta hw hcap_int hcap_bound
  refine ⟨?_, ?_⟩
  · simpa only [w, Traj] using hfull
  · have hlimit := tentEnergy_mono_limit heta hw hfull
    have hle := le_of_tendsto hlimit (Eventually.of_forall hcap_bound)
    simpa only [w, Traj] using hle

/-- Exact-weight `H0` control and the physical strip give one target-time
raw-DQ representative bound, uniform in both cap radius and canonical step. -/
theorem exists_uniform_target_rawDQ_representatives_mildFixedPoint_wave
    (p : CMParams)
    {M T Blog eta c t F D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht : 0 < t) (htT : t ≤ T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (hF : 0 ≤ F)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hMChi : MChi p ≤ M)
    (hlog : ∀ y, |deriv Uw y / Uw y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hfull : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1
              (x + c * s) - Uw x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1
              (x + c * s) - Uw x| ^ 2) ≤ F ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N n : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta (N : ℝ) x *
          rawSpatialDifferenceQuotient eta ((1 : ℝ) / (n + 1))
            (fun y =>
              (wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1
                  (y + c * t) - Uw y) x) ∧
      ‖Z‖ ≤ C := by
  let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let W := wholeLineTravelingWavePopulationBUC p hTW hbound hreg
  let Brel : ℝ := Blog * Real.exp (2 * Blog)
  let DU : ℝ := Brel * M
  let A0 : ℝ := rawDQHenryA0 eta c T F
  let A1 : ℝ := rawDQHenryA1 eta c T F
  let C0 : ℝ := rawDQHenryC0 p M eta c T
  let C1 : ℝ := rawDQHenryC1 p M eta c T
  let D0 : ℝ := rawDQHenryD0 p M Brel DU eta c T
  let D1 : ℝ := rawDQHenryD1 p M Brel DU eta c T
  have hA0 : 0 ≤ A0 := rawDQHenryA0_nonneg heta.le hF
  have hA1 : 0 ≤ A1 := rawDQHenryA1_nonneg heta.le hF
  have hC0 : 0 ≤ C0 := rawDQHenryC0_nonneg p heta.le
  have hC1 : 0 ≤ C1 := rawDQHenryC1_nonneg p heta.le
  have hD0 : 0 ≤ D0 := rawDQHenryD0_nonneg p heta.le
  have hD1 : 0 ≤ D1 := rawDQHenryD1_nonneg p heta.le
  have htHalf : 0 < t / 2 := by linarith
  obtain ⟨H, hH, hHt, hHenry⟩ :=
    exists_pos_le_henryProfileMass_lt_one htHalf hC0 hC1
  let Q : ℝ :=
    ((A0 + A1 + F * (D0 * H + 2 * D1 * Real.sqrt H)) *
      (1 + Real.sqrt H)) /
      (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H))
  let C : ℝ := Q / Real.sqrt H
  have hden : 0 < 1 -
      (2 * C0 * H + Real.pi * C1 * Real.sqrt H) := by linarith
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact div_nonneg
      (mul_nonneg
        (add_nonneg (add_nonneg hA0 hA1)
          (mul_nonneg hF
            (add_nonneg (mul_nonneg hD0 hH.le)
              (mul_nonneg (mul_nonneg (by norm_num) hD1)
                (Real.sqrt_nonneg _)))))
        (add_nonneg zero_le_one (Real.sqrt_nonneg _))) hden.le
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg hQ (Real.sqrt_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro N n
  let delta : ℝ := (1 : ℝ) / (n + 1)
  obtain ⟨hdelta, habs⟩ := canonicalRawDQStep_ne_zero_abs_le_one n
  have hdelta' : delta ≠ 0 := by simpa only [delta] using hdelta
  have habs' : |delta| ≤ 1 := by simpa only [delta] using habs
  let X : ℝ := eta * F +
    Real.sqrt
      (2 * |delta⁻¹| ^ 2 * (Real.exp (2 * eta * |delta|) + 1)) * F
  have hX : 0 ≤ X := by
    dsimp only [X]
    exact add_nonneg (mul_nonneg heta.le hF)
      (mul_nonneg (Real.sqrt_nonneg _) hF)
  have hfullW : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2) ≤ F ^ 2 := by
    intro s hs
    simpa only [Traj, W, wholeLineTravelingWavePopulationBUC_apply] using
      hfull s hs
  have hinputsT := capWeighted_coMoving_value_rawDQ_window_inputs_of_fullWeightedL2
    hT heta.le hdelta' hF Traj W (fun s hs => (hfullW s hs).1)
      (fun s hs => (hfullW s hs).2) (N : ℝ)
  have ht0 : 0 ≤ t := ht.le
  have hvalue : ∀ s ∈ Set.Icc (0 : ℝ) t, Integrable (fun x =>
      capWeight eta (N : ℝ) x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          Uw x| ^ 2) := by
    intro s hs
    simpa only [W, wholeLineTravelingWavePopulationBUC_apply] using
      hinputsT.1 s ⟨hs.1, hs.2.trans htT⟩
  have hraw : ∀ s ∈ Set.Icc (0 : ℝ) t, Integrable (fun x =>
      capWeight eta (N : ℝ) x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            Uw x) +
          spatialDifferenceQuotient delta (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              Uw y) x| ^ 2) := by
    intro s hs
    simpa only [rawSpatialDifferenceQuotient, W,
      wholeLineTravelingWavePopulationBUC_apply] using
      hinputsT.2.1 s ⟨hs.1, hs.2.trans htT⟩
  have hrawEnergy : ∀ s ∈ Set.Icc (0 : ℝ) t,
      (∫ x : ℝ, capWeight eta (N : ℝ) x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            Uw x) +
          spatialDifferenceQuotient delta (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              Uw y) x| ^ 2) ≤ X ^ 2 := by
    intro s hs
    simpa only [X, rawSpatialDifferenceQuotient, W,
      wholeLineTravelingWavePopulationBUC_apply] using
      hinputsT.2.2.1 s ⟨hs.1, hs.2.trans htT⟩
  have hvalueEnergy : ∀ s ∈ Set.Icc (0 : ℝ) t,
      (∫ x : ℝ, capWeight eta (N : ℝ) x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          Uw x| ^ 2) ≤ F ^ 2 := by
    intro s hs
    simpa only [W, wholeLineTravelingWavePopulationBUC_apply] using
      hinputsT.2.2.2 s ⟨hs.1, hs.2.trans htT⟩
  let hraw' : ∀ s ∈ Set.Icc (0 : ℝ) t, Integrable (fun x : ℝ =>
      capWeight eta (N : ℝ) x *
        |rawSpatialDifferenceQuotient eta delta (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
            W.1 y) x| ^ 2) volume := by
    intro s hs
    simpa only [rawSpatialDifferenceQuotient, W,
      wholeLineTravelingWavePopulationBUC_apply] using hraw s hs
  let hP2 := capWeightedCoMovingRawDQBUCHistoryIcc_sq_integrable
    hT ht0 eta (N : ℝ) c delta heta.le Traj W hraw'
  let P := capWeightedCoMovingRawDQL2ProfileIcc
    hT ht0 eta (N : ℝ) c delta heta.le Traj W hP2
  have hPbound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖P s‖ ≤ X := by
    intro s hs
    have heq := capWeightedCoMovingRawDQL2ProfileIcc_energy_eq_norm_sq
      hT ht0 eta (N : ℝ) c delta heta.le Traj W hP2 hs
    have hle := hrawEnergy s hs
    simp only [rawSpatialDifferenceQuotient, W,
      wholeLineTravelingWavePopulationBUC_apply] at heq
    nlinarith [heq, hle, norm_nonneg (P s)]
  have hPint : IntervalIntegrable P volume 0 t :=
    capWeightedCoMovingRawDQL2ProfileIcc_intervalIntegrable_of_bound
      hT ht0 eta (N : ℝ) c delta heta.le Traj W hP2 hPbound
  have hrestart : ∀ a r : ℝ, 0 < a → a < r → r ≤ t →
      ‖P r‖ ≤
        A0 * (r - a) ^ (-(1 / 2 : ℝ)) + A1 +
          F * (D0 * (r - a) + 2 * D1 * Real.sqrt (r - a)) +
          ∫ s in a..r,
            (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * ‖P s‖ := by
    intro a r ha har hrt
    have hstep :=
      capWeightedCoMovingRawDQL2ProfileIcc_norm_le_restart_fixedPoint_wave_of_logDerivative_fixedProfile
        p hM hT hBlog heta.le heta_one hdelta' habs' ha har hrt htT hX hF
          u₀ hsmall hstrip hTW hbound hreg hMChi hlog hD hFD hB hUd hUdd
          hUddcont hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
          (fun x => hgrad_int (r - a) (sub_pos.mpr har) x)
          hvalue hraw hrawEnergy hvalueEnergy
    have hstep' :
        ‖P r‖ ≤ rawDQHomogeneousMajorant eta c T (r - a) F +
          |p.χ| * (∫ s in a..r,
            rawDQFluxMajorant p M Brel DU eta c T delta ‖P s‖ F (r - s)) +
          ∫ s in a..r,
            rawDQReactionMajorant p M DU eta c T ‖P s‖ F := by
      simpa only [Brel, DU, Traj, W, hraw', hP2, P] using hstep
    have hseg : IntervalIntegrable P volume a r := by
      apply hPint.mono_set
      rw [Set.uIcc_of_le har.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc ha.le hrt
    have hxint : IntervalIntegrable
        (fun q : ℝ => ‖P (a + q)‖) volume 0 (r - a) := by
      have hs := wholeLineRealL2_norm_restart_intervalIntegrable
        (P := P) (a := a) (q := r - a) (by
          simpa only [show a + (r - a) = r by ring] using hseg)
      exact hs
    have hxb : ∀ q ∈ Set.Icc (0 : ℝ) (r - a),
        |‖P (a + q)‖| ≤ X := by
      intro q hq
      rw [abs_of_nonneg (norm_nonneg _)]
      apply hPbound
      constructor
      · exact ha.le.trans (le_add_of_nonneg_right hq.1)
      · calc
          a + q ≤ a + (r - a) := by
            simpa only [add_comm] using add_le_add_left hq.2 a
          _ = r := by ring
          _ ≤ t := hrt
    have hconv : IntervalIntegrable
        (fun q : ℝ => (r - a - q) ^ (-(1 / 2 : ℝ)) * ‖P (a + q)‖)
        volume 0 (r - a) :=
      intervalIntegrable_invSqrt_sub_mul_of_abs_le
        (sub_pos.mpr har) hX hxint hxb
    have hstep'' :
        ‖P (a + (r - a))‖ ≤
          rawDQHomogeneousMajorant eta c T (r - a) F +
            |p.χ| * (∫ s in a..a + (r - a),
              rawDQFluxMajorant p M Brel DU eta c T delta
                ‖P s‖ F (a + (r - a) - s)) +
            ∫ s in a..a + (r - a),
              rawDQReactionMajorant p M DU eta c T ‖P s‖ F := by
      simpa only [show a + (r - a) = r by ring] using hstep'
    have hs := rawDQPDE_majorants_le_henry_restart
      (x := fun s => ‖P s‖) (M := M) (Brel := Brel) (DU := DU)
      (eta := eta) (c := c) (T := T) (h := delta) (a := a)
      p (sub_pos.mpr har) heta.le habs' hF hxint hconv hstep''
    have hint := intervalIntegral_restart_invSqrtKernel_eq
      a (r - a) C0 C1 (fun s => ‖P s‖)
    have hint' :
        (∫ s in a..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * ‖P s‖) =
        ∫ q in (0 : ℝ)..r - a,
          (C0 + C1 * (r - a - q) ^ (-(1 / 2 : ℝ))) * ‖P (a + q)‖ := by
      simpa only [show a + (r - a) = r by ring,
        show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring] using hint
    rw [← hint'] at hs
    simpa only [A0, A1, C0, C1, D0, D1,
      show a + (r - a) = r by ring] using hs
  have hXcrude : X ≤ eta * F + |delta⁻¹| *
      (Real.sqrt (2 * (Real.exp (2 * eta) + 1)) * F) := by
    exact rawDQCrudeRadius_le_fixedStep_form heta.le hF habs'
  have hscaled := target_norm_bound_of_restart_henry_on_fixed_window
    ht hH hHt hA0 hA1 hF hD0 hD1 hC0 hC1 hX
      (mul_nonneg heta.le hF)
      (mul_nonneg (Real.sqrt_nonneg _) hF) hdelta'
      P hPint hPbound hXcrude hHenry hrestart
  have hnorm : ‖P t‖ ≤ C := by
    have hd := norm_le_div_sqrt_of_sqrt_mul_norm_le hH hscaled
    simpa only [Q, C] using hd
  refine ⟨P t, ?_, hnorm⟩
  have hcoe := capWeightedCoMovingRawDQL2ProfileIcc_coe_ae
    (s := t) hT ht0 eta (N : ℝ) c delta heta.le Traj W hP2
  rw [capWeightedCoMovingRawDQBUCHistoryIcc_of_mem
    hT ht0 eta (N : ℝ) c delta heta.le Traj W
    (show t ∈ Set.Icc (0 : ℝ) t from ⟨ht.le, le_rfl⟩)] at hcoe
  simpa only [P, delta, capWeightedCoMovingRawDQBUCHistory_apply,
    capWeightedCoMovingRawDQScalar, Traj, W,
    wholeLineTravelingWavePopulationBUC_apply] using hcoe

/-- Natural local fixed-point producer for the exact weighted spatial
gradient at every positive time of the contraction horizon.  The only
weighted datum is exact-weight `L²` integrability at the initial face; its
numeric radius is selected internally. -/
theorem paper5WeightedPopulationX_sq_integrable_mildFixedPoint_wave_positive
    (p : CMParams)
    {M T Blog eta c t D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht : 0 < t) (htT : t ≤ T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hMChi : MChi p ≤ M)
    (hlog : ∀ y, |deriv Uw y / Uw y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀.1 y - Uw y| ^ 2)) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) Uw t x ^ 2)
      volume := by
  dsimp only
  let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let E₀ : ℝ := ∫ y : ℝ,
    Real.exp (2 * eta * y) * |u₀.1 y - Uw y| ^ 2
  let B₀ : ℝ := Real.sqrt E₀
  have hE₀ : 0 ≤ E₀ := by
    dsimp only [E₀]
    exact integral_nonneg fun y =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hB₀ : 0 ≤ B₀ := Real.sqrt_nonneg _
  have hdata_energy :
      (∫ y : ℝ, Real.exp (2 * eta * y) * |u₀.1 y - Uw y| ^ 2) ≤
        B₀ ^ 2 := by
    dsimp only [B₀, E₀]
    rw [Real.sq_sqrt hE₀]
  obtain ⟨F, hF, hfullAuto⟩ :=
    exists_uniform_fullWeighted_mildFixedPoint_wave_value_inputs_finiteHorizon
      p hT heta heta_one hB₀ u₀ hsmall hTW hbound hreg hMChi
        hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
        hreact hreact_cont hgrad_int hdata_full hdata_energy
  have hfull : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          Uw x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          Uw x| ^ 2) ≤ F ^ 2 := by
    intro s hs
    simpa only [Traj] using hfullAuto s hs
  obtain ⟨C, hC, hrepRaw⟩ :=
    exists_uniform_target_rawDQ_representatives_mildFixedPoint_wave
      p hM hT ht htT hBlog heta heta_one hF u₀ hsmall hstrip
        hTW hbound hreg hMChi hlog hD hFD hB hUd hUdd hUddcont hflux
        hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int hfull
  have hrep : ∀ N n : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta (N : ℝ) x *
          rawSpatialDifferenceQuotient eta ((1 : ℝ) / (n + 1))
            (fun y => coMovingPath c u t y - Uw y) x) ∧
      ‖Z‖ ≤ C := by
    intro N n
    simpa only [u, Traj, coMovingPath] using hrepRaw N n
  let z : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT⟩
  have hwindow : ∀ s ∈ Set.Icc (t / 2) t, ∀ x,
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x ∈
        Set.Icc (0 : ℝ) M := by
    intro s hs x
    have hsT : s ∈ Set.Icc (0 : ℝ) T := by
      constructor
      · have htHalf : 0 < t / 2 := by linarith
        exact htHalf.le.trans hs.1
      · exact hs.2.trans htT
    rw [wholeLineBUCTrajectoryExtend_eq hT Traj hsT]
    exact hstrip ⟨s, hsT⟩ x
  have hslice2 : ContDiff ℝ 2 (fun x => (Traj z).1 x) := by
    exact wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
      (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ)) p hM hT u₀ hsmall
        z ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hwindow
  have hext : wholeLineBUCTrajectoryExtend hT Traj t = Traj z :=
    wholeLineBUCTrajectoryExtend_eq hT Traj ⟨ht.le, htT⟩
  have hslice2ext : ContDiff ℝ 2
      (fun x => (wholeLineBUCTrajectoryExtend hT Traj t).1 x) := by
    rw [hext]
    exact hslice2
  have hu1 : ContDiff ℝ 1 (coMovingPath c u t) := by
    have hshift2 : ContDiff ℝ 2 (coMovingPath c u t) := by
      simpa only [u, coMovingPath] using
        ContDiff.two_shift hslice2ext (c * t)
    exact hshift2.of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 Uw := by
    exact contDiff_one_iff_deriv.2
      ⟨fun x => hreg.U_diff x, hreg.deriv_U_cont⟩
  exact paper5WeightedPopulationX_sq_integrable_of_uniform_rawDQ
    heta hC hu1 hU1 hrep

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exists_uniform_fullWeighted_mildFixedPoint_wave_value_inputs_finiteHorizon

#print axioms
  ShenWork.Paper1.exists_uniform_target_rawDQ_representatives_mildFixedPoint_wave

#print axioms
  ShenWork.Paper1.paper5WeightedPopulationX_sq_integrable_mildFixedPoint_wave_positive
