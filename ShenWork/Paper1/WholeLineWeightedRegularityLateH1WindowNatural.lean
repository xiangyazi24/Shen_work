import ShenWork.Paper1.WholeLineWeightedRegularityWeightedConvergenceNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGradientWindowBudget

open Filter Function MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Uniform late-time exact-weight H1 windows

This file isolates the quantitative input needed to use the scaled wave-trap
producer uniformly on late canonical restart segments.  The first step is an
exact identification of the phase-normalized restart datum with a genuine
slice of the glued global orbit.  Thus weighted convergence gives a common
late-time `H0` radius; no uniform `H1` estimate is inferred from mere
slice-wise integrability.
-/

/-- The phase-normalized datum of segment `n` is exactly the global orbit at
the restart time `n * delta`, observed in the traveling coordinate. -/
theorem wholeLineCauchyGlobalTranslatedDatumIndex_eq_coMoving_step
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (c : ℝ) (n : ℕ) :
    (wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n).1 =
      coMovingPath c (wholeLineCauchyGlobalU p u₀)
        ((n : ℝ) * wholeLineCauchyGlobalStep p u₀) := by
  funext x
  let delta := wholeLineCauchyGlobalStep p u₀
  let t : ℝ := (n : ℝ) * delta
  have hdelta : 0 < delta := wholeLineCauchyGlobalStep_pos p u₀
  have htcell : t ∈ Set.Ico ((n : ℝ) * delta) (((n : ℝ) + 1) * delta) := by
    constructor
    · exact le_rfl
    · nlinarith
  have hglobal := wholeLineCauchyGlobalBUC_eq_next_on_cell
    p hregime u₀ hu₀ n (by simpa only [delta, t] using htcell)
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨le_rfl, (wholeLineCauchyGlobalSegmentTime_pos p u₀).le⟩
  have hext : wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalSegment p u₀ n) 0 =
      wholeLineCauchyGlobalSegment p u₀ n ⟨0, hzero⟩ :=
    wholeLineBUCTrajectoryExtend_eq
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalSegment p u₀ n) hzero
  have hinit : wholeLineCauchyGlobalSegment p u₀ n ⟨0, hzero⟩ =
      wholeLineCauchyGlobalDatum p u₀ n := by
    simpa only [wholeLineCauchyGlobalSegment] using
      (wholeLineCauchyBUCMildFixedPoint_initial p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalDatum p u₀ n)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) hzero)
  have hglobalDatum :
      wholeLineCauchyGlobalBUC p u₀ t =
        wholeLineCauchyGlobalDatum p u₀ n := by
    calc
      wholeLineCauchyGlobalBUC p u₀ t =
          wholeLineBUCTrajectoryExtend
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
            (wholeLineCauchyGlobalSegment p u₀ n) 0 := by
        simpa only [t, delta, sub_self] using hglobal
      _ = wholeLineCauchyGlobalSegment p u₀ n ⟨0, hzero⟩ := hext
      _ = wholeLineCauchyGlobalDatum p u₀ n := hinit
  simp only [wholeLineCauchyGlobalTranslatedDatumIndex,
    wholeLineBUCTranslate_apply, coMovingPath, wholeLineCauchyGlobalU]
  rw [show (n : ℝ) * wholeLineCauchyGlobalStep p u₀ = t by rfl]
  rw [show c * ((n : ℝ) * wholeLineCauchyGlobalStep p u₀) = c * t by rfl]
  rw [hglobalDatum]

/-- Weighted convergence supplies one numerical `H0` radius for all
sufficiently late phase-normalized restart data.  This is the legitimate
uniform input for a late-window smoothing argument. -/
theorem eventually_translatedDatumIndex_fullWeightedL2_le_one
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {eta c : ℝ} {U : ℝ → ℝ}
    (hconv : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U) :
    ∀ᶠ n in atTop,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n).1 x -
          U x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n).1 x -
          U x| ^ 2) ≤ 1 := by
  let delta := wholeLineCauchyGlobalStep p u₀
  have hdelta : 0 < delta := wholeLineCauchyGlobalStep_pos p u₀
  have hseq : Tendsto (fun n : ℕ => (n : ℝ) * delta) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hdelta
  have hint : ∀ᶠ n : ℕ in atTop, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) *
        |wholeLineCauchyGlobalU p u₀ ((n : ℝ) * delta)
          (x + c * ((n : ℝ) * delta)) - U x| ^ 2) :=
    hseq.eventually hconv.1
  have henergy : ∀ᶠ n : ℕ in atTop,
      coMovingWeightedL2Energy eta c (wholeLineCauchyGlobalU p u₀) U
        ((n : ℝ) * delta) < 1 :=
    hseq.eventually ((tendsto_order.1 hconv.2).2 1 zero_lt_one)
  filter_upwards [hint, henergy] with n hn hEn
  have heq := wholeLineCauchyGlobalTranslatedDatumIndex_eq_coMoving_step
    p hregime u₀ hu₀ c n
  constructor
  · simpa only [delta, heq, coMovingPath] using hn
  · have hEn' :
        (∫ x : ℝ, Real.exp (2 * eta * x) *
          |wholeLineCauchyGlobalU p u₀ ((n : ℝ) * delta)
            (x + c * ((n : ℝ) * delta)) - U x| ^ 2) < 1 := by
      simpa only [coMovingWeightedL2Energy] using hEn
    simpa only [delta, heq, coMovingPath] using hEn'.le

/-- Uniform-family form of the finite-horizon exact-weight `H0` estimate.
The artificial damping rate is selected before the datum index is
introduced, so one numerical radius works for the entire family. -/
theorem exists_common_fullWeighted_mildFixedPoint_wave_value_inputs_family
    (p : CMParams) {ι : Type*}
    {M T eta c B₀ D E Kflux FD B : ℝ}
    (hT : 0 ≤ T) (heta : 0 < eta) (heta_one : eta < 1)
    (hB₀ : 0 ≤ B₀)
    (datum : ι → WholeLineBUC)
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
    (hdata_full : ∀ i, Integrable (fun y : ℝ =>
      Real.exp (2 * eta * y) * |(datum i).1 y - Uw y| ^ 2))
    (hdata_energy : ∀ i, (∫ y : ℝ,
      Real.exp (2 * eta * y) * |(datum i).1 y - Uw y| ^ 2) ≤ B₀ ^ 2) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p
              (zero_le_one.trans
                ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
              hT (datum i) hsmall) s).1 (x + c * s) - Uw x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p
              (zero_le_one.trans
                ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
              hT (datum i) hsmall) s).1 (x + c * s) - Uw x| ^ 2) ≤ F ^ 2 := by
  have hM1 : 1 ≤ M :=
    (MChi_ge_one_of_travelingWave hTW hbound).trans hMChi
  have hM : 0 ≤ M := zero_le_one.trans hM1
  let hUunif : UniformContinuous Uw :=
    travelingWave_U_uniformContinuous hTW hreg.U_cont
  let hUM : ∀ x, |Uw x| ≤ M := fun x => by
    rw [abs_of_pos (hTW.U_pos x)]
    exact (hbound.le_MChi x).trans hMChi
  let uW : WholeLineBUC :=
    wholeLineTranslatedProfileBUC Uw hUunif M hUM c 0
  let W : WholeLineBUCTrajectory T :=
    wholeLineTranslatedProfileTrajectoryFrom hT Uw hUunif M hUM c 0
  have hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT uW) W := by
    simpa only [hUunif, hUM, uW, W] using
      (IsTravelingWave.translatedProfileTrajectoryFrom_isFixedPt
        p hTW hbound hreg hT hMChi
        hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
        hreact hreact_cont hgrad_int (a := 0))
  let C : ℝ := capMildKernelCommonConstant p M eta c T
  rcases exists_pos_capMildDampedKernelMass_lt_one C with
    ⟨lambda, hlambda, hqC⟩
  have hq : ShenWork.PDE.restartedKernelMassPositive
      (capMildKernelCommonConstant p M eta c T)
      (1 / 2 : ℝ) lambda < 1 := by
    simpa only [C] using hqC
  let D₀ : ℝ := capMildDampedBallRadius p M T eta c B₀ lambda
  let F : ℝ := D₀ * Real.exp (lambda * T)
  have hD₀ : 0 ≤ D₀ := by
    dsimp only [D₀, capMildDampedBallRadius]
    have hG : 0 ≤ capMildGrowthBound eta c T := by
      unfold capMildGrowthBound
      exact (Real.exp_pos _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hG) hB₀)
      (sub_nonneg.mpr hq.le)
  have hF : 0 ≤ F := by
    exact mul_nonneg hD₀ (Real.exp_nonneg _)
  refine ⟨F, hF, ?_⟩
  intro i s hs
  let z : Set.Icc (0 : ℝ) T := ⟨s, hs⟩
  have hdata_full' : Integrable (fun y : ℝ =>
      Real.exp (2 * eta * y) * |(datum i).1 y - uW.1 y| ^ 2) := by
    simpa only [uW, wholeLineTranslatedProfileBUC_apply, mul_zero, sub_zero]
      using hdata_full i
  have hdata_energy' : (∫ y : ℝ,
      Real.exp (2 * eta * y) * |(datum i).1 y - uW.1 y| ^ 2) ≤ B₀ ^ 2 := by
    simpa only [uW, wholeLineTranslatedProfileBUC_apply, mul_zero, sub_zero]
      using hdata_energy i
  have hz :=
    coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_and_integral_le_damped
      p hM hT heta heta_one hB₀ hlambda hq (datum i) uW W hfixed
        hsmall hdata_full' hdata_energy' z
  have hext : wholeLineBUCTrajectoryExtend hT
      (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall) s =
      wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall z :=
    wholeLineBUCTrajectoryExtend_eq hT _ hs
  have hWshift : ∀ x, (W z).1 (x + c * s) = Uw x := by
    intro x
    dsimp only [W, wholeLineTranslatedProfileTrajectoryFrom_apply, z]
    congr 1
    ring
  constructor
  · simpa only [z, hext, hWshift] using hz.1
  · have hexp : Real.exp (lambda * s) ≤ Real.exp (lambda * T) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hs.2 hlambda.le
    have hDF : D₀ * Real.exp (lambda * s) ≤ F := by
      exact mul_le_mul_of_nonneg_left hexp hD₀
    have hsq : (D₀ * Real.exp (lambda * s)) ^ 2 ≤ F ^ 2 :=
      (sq_le_sq₀
        (mul_nonneg hD₀ (Real.exp_nonneg _)) hF).2 hDF
    simpa only [z, hext, hWshift, D₀] using hz.2.trans hsq

/-- One Henry constant controls every cap radius, canonical quotient step,
and target time in a compact positive window. -/
theorem exists_common_uniform_window_rawDQ_representatives_mildFixedPoint_wave_family
    (p : CMParams) {ι : Type*}
    {M T a b Blog eta c F D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hbT : b ≤ T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (hF : 0 ≤ F)
    (datum : ι → WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ i, ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall z).1 x ∈
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
    (hfull : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall) s).1
              (x + c * s) - Uw x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall) s).1
              (x + c * s) - Uw x| ^ 2) ≤ F ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ tau ∈ Set.Icc a b, ∀ N n : ℕ,
      ∃ Z : WholeLineRealL2,
        ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
          capWeightSqrt eta (N : ℝ) x *
            rawSpatialDifferenceQuotient eta ((1 : ℝ) / (n + 1))
              (fun y =>
                (wholeLineBUCTrajectoryExtend hT
                  (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall)
                    tau).1 (y + c * tau) - Uw y) x) ∧
        ‖Z‖ ≤ C := by
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
  have haHalf : 0 < a / 2 := by linarith
  obtain ⟨H, hH, hHa, hHenry⟩ :=
    exists_pos_le_henryProfileMass_lt_one haHalf hC0 hC1
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
  intro i
  let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall
  intro tau htau N n
  have htau0 : 0 < tau := ha.trans_le htau.1
  have htauT : tau ≤ T := htau.2.trans hbT
  have hHtau : H ≤ tau / 2 :=
    hHa.trans (div_le_div_of_nonneg_right htau.1 zero_le_two)
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
      hfull i s hs
  have hinputsT :=
    capWeighted_coMoving_value_rawDQ_window_inputs_of_fullWeightedL2
      hT heta.le hdelta' hF Traj W (fun s hs => (hfullW s hs).1)
        (fun s hs => (hfullW s hs).2) (N : ℝ)
  have htauNonneg : 0 ≤ tau := htau0.le
  have hvalue : ∀ s ∈ Set.Icc (0 : ℝ) tau, Integrable (fun x =>
      capWeight eta (N : ℝ) x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          Uw x| ^ 2) := by
    intro s hs
    simpa only [W, wholeLineTravelingWavePopulationBUC_apply] using
      hinputsT.1 s ⟨hs.1, hs.2.trans htauT⟩
  have hraw : ∀ s ∈ Set.Icc (0 : ℝ) tau, Integrable (fun x =>
      capWeight eta (N : ℝ) x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1
              (x + c * s) - Uw x) +
          spatialDifferenceQuotient delta (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              Uw y) x| ^ 2) := by
    intro s hs
    simpa only [rawSpatialDifferenceQuotient, W,
      wholeLineTravelingWavePopulationBUC_apply] using
      hinputsT.2.1 s ⟨hs.1, hs.2.trans htauT⟩
  have hrawEnergy : ∀ s ∈ Set.Icc (0 : ℝ) tau,
      (∫ x : ℝ, capWeight eta (N : ℝ) x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1
              (x + c * s) - Uw x) +
          spatialDifferenceQuotient delta (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              Uw y) x| ^ 2) ≤ X ^ 2 := by
    intro s hs
    simpa only [X, rawSpatialDifferenceQuotient, W,
      wholeLineTravelingWavePopulationBUC_apply] using
      hinputsT.2.2.1 s ⟨hs.1, hs.2.trans htauT⟩
  have hvalueEnergy : ∀ s ∈ Set.Icc (0 : ℝ) tau,
      (∫ x : ℝ, capWeight eta (N : ℝ) x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          Uw x| ^ 2) ≤ F ^ 2 := by
    intro s hs
    simpa only [W, wholeLineTravelingWavePopulationBUC_apply] using
      hinputsT.2.2.2 s ⟨hs.1, hs.2.trans htauT⟩
  let hraw' : ∀ s ∈ Set.Icc (0 : ℝ) tau, Integrable (fun x : ℝ =>
      capWeight eta (N : ℝ) x *
        |rawSpatialDifferenceQuotient eta delta (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
            W.1 y) x| ^ 2) volume := by
    intro s hs
    simpa only [rawSpatialDifferenceQuotient, W,
      wholeLineTravelingWavePopulationBUC_apply] using hraw s hs
  let hP2 := capWeightedCoMovingRawDQBUCHistoryIcc_sq_integrable
    hT htauNonneg eta (N : ℝ) c delta heta.le Traj W hraw'
  let P := capWeightedCoMovingRawDQL2ProfileIcc
    hT htauNonneg eta (N : ℝ) c delta heta.le Traj W hP2
  have hPbound : ∀ s ∈ Set.Icc (0 : ℝ) tau, ‖P s‖ ≤ X := by
    intro s hs
    have heq := capWeightedCoMovingRawDQL2ProfileIcc_energy_eq_norm_sq
      hT htauNonneg eta (N : ℝ) c delta heta.le Traj W hP2 hs
    have hle := hrawEnergy s hs
    simp only [rawSpatialDifferenceQuotient, W,
      wholeLineTravelingWavePopulationBUC_apply] at heq
    nlinarith [heq, hle, norm_nonneg (P s)]
  have hPint : IntervalIntegrable P volume 0 tau :=
    capWeightedCoMovingRawDQL2ProfileIcc_intervalIntegrable_of_bound
      hT htauNonneg eta (N : ℝ) c delta heta.le Traj W hP2 hPbound
  have hrestart : ∀ a' r : ℝ, 0 < a' → a' < r → r ≤ tau →
      ‖P r‖ ≤
        A0 * (r - a') ^ (-(1 / 2 : ℝ)) + A1 +
          F * (D0 * (r - a') + 2 * D1 * Real.sqrt (r - a')) +
          ∫ s in a'..r,
            (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * ‖P s‖ := by
    intro a' r ha' har hrt
    have hstep :=
      capWeightedCoMovingRawDQL2ProfileIcc_norm_le_restart_fixedPoint_wave_of_logDerivative_fixedProfile
        p hM hT hBlog heta.le heta_one hdelta' habs' ha' har hrt htauT
          hX hF (datum i) hsmall (hstrip i) hTW hbound hreg hMChi hlog hD hFD hB
          hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
          hreact_cont (fun x => hgrad_int (r - a') (sub_pos.mpr har) x)
          hvalue hraw hrawEnergy hvalueEnergy
    have hstep' :
        ‖P r‖ ≤ rawDQHomogeneousMajorant eta c T (r - a') F +
          |p.χ| * (∫ s in a'..r,
            rawDQFluxMajorant p M Brel DU eta c T delta
              ‖P s‖ F (r - s)) +
          ∫ s in a'..r,
            rawDQReactionMajorant p M DU eta c T ‖P s‖ F := by
      simpa only [Brel, DU, Traj, W, hraw', hP2, P] using hstep
    have hseg : IntervalIntegrable P volume a' r := by
      apply hPint.mono_set
      rw [Set.uIcc_of_le har.le, Set.uIcc_of_le htau0.le]
      exact Set.Icc_subset_Icc ha'.le hrt
    have hxint : IntervalIntegrable
        (fun q : ℝ => ‖P (a' + q)‖) volume 0 (r - a') := by
      exact wholeLineRealL2_norm_restart_intervalIntegrable
        (P := P) (a := a') (q := r - a') (by
          simpa only [show a' + (r - a') = r by ring] using hseg)
    have hxb : ∀ q ∈ Set.Icc (0 : ℝ) (r - a'),
        |‖P (a' + q)‖| ≤ X := by
      intro q hq
      rw [abs_of_nonneg (norm_nonneg _)]
      apply hPbound
      constructor
      · exact ha'.le.trans (le_add_of_nonneg_right hq.1)
      · calc
          a' + q ≤ a' + (r - a') := by
            simpa only [add_comm] using add_le_add_left hq.2 a'
          _ = r := by ring
          _ ≤ tau := hrt
    have hconv : IntervalIntegrable
        (fun q : ℝ => (r - a' - q) ^ (-(1 / 2 : ℝ)) *
          ‖P (a' + q)‖) volume 0 (r - a') :=
      intervalIntegrable_invSqrt_sub_mul_of_abs_le
        (sub_pos.mpr har) hX hxint hxb
    have hstep'' :
        ‖P (a' + (r - a'))‖ ≤
          rawDQHomogeneousMajorant eta c T (r - a') F +
            |p.χ| * (∫ s in a'..a' + (r - a'),
              rawDQFluxMajorant p M Brel DU eta c T delta
                ‖P s‖ F (a' + (r - a') - s)) +
            ∫ s in a'..a' + (r - a'),
              rawDQReactionMajorant p M DU eta c T ‖P s‖ F := by
      simpa only [show a' + (r - a') = r by ring] using hstep'
    have hs := rawDQPDE_majorants_le_henry_restart
      (x := fun s => ‖P s‖) (M := M) (Brel := Brel) (DU := DU)
      (eta := eta) (c := c) (T := T) (h := delta) (a := a')
      p (sub_pos.mpr har) heta.le habs' hF hxint hconv hstep''
    have hint := intervalIntegral_restart_invSqrtKernel_eq
      a' (r - a') C0 C1 (fun s => ‖P s‖)
    have hint' :
        (∫ s in a'..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * ‖P s‖) =
        ∫ q in (0 : ℝ)..r - a',
          (C0 + C1 * (r - a' - q) ^ (-(1 / 2 : ℝ))) *
            ‖P (a' + q)‖ := by
      simpa only [show a' + (r - a') = r by ring,
        show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring] using hint
    rw [← hint'] at hs
    simpa only [A0, A1, C0, C1, D0, D1,
      show a' + (r - a') = r by ring] using hs
  have hXcrude : X ≤ eta * F + |delta⁻¹| *
      (Real.sqrt (2 * (Real.exp (2 * eta) + 1)) * F) :=
    rawDQCrudeRadius_le_fixedStep_form heta.le hF habs'
  have hscaled := target_norm_bound_of_restart_henry_on_fixed_window
    htau0 hH hHtau hA0 hA1 hF hD0 hD1 hC0 hC1 hX
      (mul_nonneg heta.le hF)
      (mul_nonneg (Real.sqrt_nonneg _) hF) hdelta'
      P hPint hPbound hXcrude hHenry hrestart
  have hnorm : ‖P tau‖ ≤ C := by
    have hd := norm_le_div_sqrt_of_sqrt_mul_norm_le hH hscaled
    simpa only [Q, C] using hd
  refine ⟨P tau, ?_, hnorm⟩
  have hcoe := capWeightedCoMovingRawDQL2ProfileIcc_coe_ae
    (s := tau) hT htauNonneg eta (N : ℝ) c delta heta.le Traj W hP2
  rw [capWeightedCoMovingRawDQBUCHistoryIcc_of_mem
    hT htauNonneg eta (N : ℝ) c delta heta.le Traj W
    (show tau ∈ Set.Icc (0 : ℝ) tau from ⟨htau0.le, le_rfl⟩)] at hcoe
  simpa only [P, delta, capWeightedCoMovingRawDQBUCHistory_apply,
    capWeightedCoMovingRawDQScalar, Traj, W,
    wholeLineTravelingWavePopulationBUC_apply] using hcoe

/-- Quantitative exact-weight `H¹` data for an arbitrary family of
canonical fixed points.  The common raw-DQ Henry radius is selected before
the family index, so the resulting gradient budget is genuinely uniform. -/
theorem
    exists_common_uniform_window_weightedPopulationX_data_mildFixedPoint_wave_family
    (p : CMParams) {ι : Type*}
    {M T a b Blog eta c F D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hbT : b ≤ T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (hF : 0 ≤ F)
    (datum : ι → WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ i, ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall z).1 x ∈
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
    (hfull : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall) s).1
              (x + c * s) - Uw x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |(wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall) s).1
              (x + c * s) - Uw x| ^ 2) ≤ F ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ tau ∈ Set.Icc a b,
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      Integrable (fun x =>
        paper5WeightedPopulationX eta (coMovingPath c u) Uw tau x ^ 2) ∧
      (∫ x : ℝ,
        paper5WeightedPopulationX eta (coMovingPath c u) Uw tau x ^ 2) ≤
        C ^ 2 := by
  obtain ⟨C, hC, hrep⟩ :=
    exists_common_uniform_window_rawDQ_representatives_mildFixedPoint_wave_family
      p hM hT ha hbT hBlog heta heta_one hF datum hsmall hstrip
        hTW hbound hreg hMChi hlog hD hFD hB hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int hfull
  refine ⟨C, hC, ?_⟩
  intro i tau htau
  dsimp only
  let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT (datum i) hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  have htau0 : 0 < tau := ha.trans_le htau.1
  have htauT : tau ≤ T := htau.2.trans hbT
  let ztau : Set.Icc (0 : ℝ) T := ⟨tau, htau0.le, htauT⟩
  have hwindow : ∀ s ∈ Set.Icc (tau / 2) tau, ∀ x,
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x ∈
        Set.Icc (0 : ℝ) M := by
    intro s hs x
    have hsT : s ∈ Set.Icc (0 : ℝ) T := by
      constructor
      · exact (half_pos htau0).le.trans hs.1
      · exact hs.2.trans htauT
    rw [wholeLineBUCTrajectoryExtend_eq hT Traj hsT]
    exact hstrip i ⟨s, hsT⟩ x
  have hslice2 : ContDiff ℝ 2 (fun x => (Traj ztau).1 x) := by
    exact wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
      (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
      p hM hT (datum i) hsmall ztau htau0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hwindow
  have hext : wholeLineBUCTrajectoryExtend hT Traj tau = Traj ztau :=
    wholeLineBUCTrajectoryExtend_eq hT Traj ztau.2
  have hslice2ext : ContDiff ℝ 2
      (fun x => (wholeLineBUCTrajectoryExtend hT Traj tau).1 x) := by
    rw [hext]
    exact hslice2
  have hu1 : ContDiff ℝ 1 (coMovingPath c u tau) := by
    have hshift2 : ContDiff ℝ 2 (coMovingPath c u tau) := by
      simpa only [u, coMovingPath] using
        ContDiff.two_shift hslice2ext (c * tau)
    exact hshift2.of_le (by norm_num)
  have hU1 : ContDiff ℝ 1 Uw :=
    contDiff_one_iff_deriv.2
      ⟨fun x => hreg.U_diff x, hreg.deriv_U_cont⟩
  simpa only [u, Traj, coMovingPath] using
    (paper5WeightedPopulationX_data_of_uniform_rawDQ
      heta hC hu1 hU1 (hrep i tau htau))

/-- A convergent nonpositive-sensitivity global orbit has one exact-weight
`H0/H1` numerical budget on every sufficiently late canonical restart
segment.  The local gradient window is the fixed interior interval
`[delta, 2*delta]`, hence it stays uniformly away from the singular restart
face. -/
theorem exists_eventual_common_weighted_H1_restart_window_chi_nonpos
    (p : CMParams) (hchi : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c D E Kflux FD B : ℝ}
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
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
    (hconv : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) Uw) :
    ∃ N : ℕ, ∃ F G : ℝ, 0 ≤ F ∧ 0 ≤ G ∧
      ∀ n : ℕ, N ≤ n →
        let datum := wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n
        let Traj := wholeLineCauchyBUCMildFixedPoint p
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le datum
          (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        let u : ℝ → ℝ → ℝ := fun s x =>
          (wholeLineBUCTrajectoryExtend
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 x
        (∀ s ∈ Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀),
          Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
            |u s (x + c * s) - Uw x| ^ 2) ∧
          (∫ x : ℝ, Real.exp (2 * eta * x) *
            |u s (x + c * s) - Uw x| ^ 2) ≤ F ^ 2) ∧
        (∀ s ∈ Set.Icc (wholeLineCauchyGlobalStep p u₀)
            (wholeLineCauchyGlobalSegmentTime p u₀),
          Integrable (fun x : ℝ =>
            paper5WeightedPopulationX eta (coMovingPath c u) Uw s x ^ 2) ∧
          (∫ x : ℝ,
            paper5WeightedPopulationX eta (coMovingPath c u) Uw s x ^ 2) ≤
              G ^ 2) := by
  let M := wholeLineCauchyGlobalClamp p u₀
  let T := wholeLineCauchyGlobalSegmentTime p u₀
  let a := wholeLineCauchyGlobalStep p u₀
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi
  have hM : 0 ≤ M := by
    simpa only [M] using (wholeLineCauchyGlobalClamp_pos p u₀).le
  have hT : 0 ≤ T := by
    simpa only [T] using (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
  have ha : 0 < a := by
    simpa only [a] using wholeLineCauchyGlobalStep_pos p u₀
  have hMChi : MChi p ≤ M := by
    rw [MChi_eq_one_of_chi_nonpos p hchi]
    have hstable : 1 ≤ wholeLineCauchyStableCeiling p u₀ :=
      wholeLineCauchyStableCeiling_one_le hregime u₀
    unfold M wholeLineCauchyGlobalClamp
    linarith
  have hevent := eventually_translatedDatumIndex_fullWeightedL2_le_one
    p hregime u₀ hu₀ hconv
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let ι := {n : ℕ // N ≤ n}
  let datum : ι → WholeLineBUC := fun n =>
    wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n.1
  have hdata_full : ∀ i : ι, Integrable (fun y : ℝ =>
      Real.exp (2 * eta * y) * |(datum i).1 y - Uw y| ^ 2) := by
    intro i
    exact (hN i.1 i.2).1
  have hdata_energy : ∀ i : ι, (∫ y : ℝ,
      Real.exp (2 * eta * y) * |(datum i).1 y - Uw y| ^ 2) ≤ (1 : ℝ) ^ 2 := by
    intro i
    simpa only [one_pow] using (hN i.1 i.2).2
  have hstrip : ∀ i : ι, ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT (datum i)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) z).1 x ∈
        Set.Icc (0 : ℝ) M := by
    intro i z x
    let d : ℝ := c * ((i.1 : ℝ) * a)
    have htranslate : datum i = wholeLineBUCTranslate d
        (wholeLineCauchyGlobalDatum p u₀ i.1) := by
      rfl
    have hfp := wholeLineCauchyBUCMildFixedPoint_spatialTranslate
      (d := d) p hM hT (wholeLineCauchyGlobalDatum p u₀ i.1)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
    have heq : wholeLineCauchyBUCMildFixedPoint p hM hT (datum i)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) =
      wholeLineBUCTrajectorySpatialTranslate hT d
        (wholeLineCauchyGlobalSegment p u₀ i.1) := by
      rw [htranslate]
      simpa only [wholeLineCauchyGlobalSegment, M, T] using hfp
    rw [heq]
    simpa only [wholeLineBUCTrajectorySpatialTranslate_apply, M, T] using
      (wholeLineCauchyGlobalDatum_segment_bounds
        p hregime u₀ hu₀ i.1).2.1 z (x + d)
  obtain ⟨F, hF, hfull⟩ :=
    exists_common_fullWeighted_mildFixedPoint_wave_value_inputs_family
      (M := M) (T := T) (eta := eta) (c := c) (B₀ := 1)
      (D := D) (E := E) (Kflux := Kflux) (FD := FD) (B := B)
      p hT heta heta_one (by norm_num) datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        hTW hbound hreg hMChi hD hFD hB hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
        hdata_full hdata_energy
  obtain ⟨G, hG, hgrad⟩ :=
    exists_common_uniform_window_weightedPopulationX_data_mildFixedPoint_wave_family
      (M := M) (T := T) (a := a) (b := T) (Blog := Blog)
      (eta := eta) (c := c) (F := F)
      (D := D) (E := E) (Kflux := Kflux) (FD := FD) (B := B)
      p hM hT ha le_rfl hBlog heta heta_one hF datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) hstrip
        hTW hbound hreg hMChi hlog hD hFD hB hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int hfull
  refine ⟨N, F, G, hF, hG, ?_⟩
  intro n hn
  let i : ι := ⟨n, hn⟩
  have hfull_i := hfull i
  have hgrad_i := hgrad i
  simpa only [datum, i, M, T, a] using And.intro hfull_i hgrad_i

section AxiomAudit

#print axioms wholeLineCauchyGlobalTranslatedDatumIndex_eq_coMoving_step
#print axioms eventually_translatedDatumIndex_fullWeightedL2_le_one
#print axioms
  exists_common_fullWeighted_mildFixedPoint_wave_value_inputs_family
#print axioms
  exists_common_uniform_window_rawDQ_representatives_mildFixedPoint_wave_family
#print axioms
  exists_common_uniform_window_weightedPopulationX_data_mildFixedPoint_wave_family
#print axioms exists_eventual_common_weighted_H1_restart_window_chi_nonpos

end AxiomAudit

end ShenWork.Paper1
