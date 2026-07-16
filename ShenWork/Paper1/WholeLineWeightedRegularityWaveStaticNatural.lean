import ShenWork.Paper1.WholeLineWeightedRegularityForcingWindowNatural
import ShenWork.Paper1.Theorem12EnergyProducer

open Filter Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical traveling-wave data for the natural weighted energy route

The positive-time energy producer only needs static bounds and regularity of
the reference wave.  This file derives those fields from the corrected speed
condition and the traveling-wave hypotheses, with explicit constants.
-/

/-- Uniform bound for the stationary chemotaxis flux `U^m V'`. -/
def paper5WaveFluxBound (p : CMParams) : ℝ :=
  (MChi p) ^ p.m * (MChi p) ^ p.γ

/-- Uniform bound for the derivative of the stationary chemotaxis flux. -/
def paper5WaveFluxDerivativeBound (p : CMParams) : ℝ :=
  p.m * (MChi p) ^ (p.m - 1) * paper5ConcreteLu p *
      (MChi p) ^ p.γ +
    (MChi p) ^ p.m * (MChi p) ^ p.γ

/-- Uniform bound for the shifted stationary reaction. -/
def paper5WaveShiftedReactionBound (p : CMParams) : ℝ :=
  MChi p + MChi p * (1 + (MChi p) ^ p.α)

/-- Uniform bound for `U''`, obtained from the moving-generator balance. -/
def paper5WaveSecondDerivativeBound (p : CMParams) (c : ℝ) : ℝ :=
  |c| * paper5ConcreteLu p + MChi p +
    |p.χ| * paper5WaveFluxDerivativeBound p +
      paper5WaveShiftedReactionBound p

/-- All wave-static inputs consumed by the natural weighted-energy producer,
at the canonical explicit budgets. -/
structure Paper5WaveStaticNaturalData
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop where
  hBlog : 0 ≤ (1 : ℝ)
  hD : 0 ≤ paper5ConcreteLu p
  hE : 0 ≤ paper5WaveSecondDerivativeBound p c
  hKflux : 0 ≤ paper5WaveFluxBound p
  hFD : 0 ≤ paper5WaveFluxDerivativeBound p
  hB : 0 ≤ paper5WaveShiftedReactionBound p
  hlog : ∀ y, |deriv U y / U y| ≤ (1 : ℝ)
  hUd : ∀ y, |deriv U y| ≤ paper5ConcreteLu p
  hUdd : ∀ y,
    |deriv (deriv U) y| ≤ paper5WaveSecondDerivativeBound p c
  hUddcont : Continuous (deriv (deriv U))
  hflux : ∀ y,
    |wholeLineTravelingWaveFlux p U V y| ≤ paper5WaveFluxBound p
  hfluxd : ∀ y,
    |deriv (wholeLineTravelingWaveFlux p U V) y| ≤
      paper5WaveFluxDerivativeBound p
  hflux_has : ∀ y, HasDerivAt
    (wholeLineTravelingWaveFlux p U V)
    (deriv (wholeLineTravelingWaveFlux p U V) y) y
  hfluxd_cont : Continuous
    (deriv (wholeLineTravelingWaveFlux p U V))
  hreact : ∀ y,
    |wholeLineCauchyShiftedReaction p U y| ≤
      paper5WaveShiftedReactionBound p
  hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U)
  hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
    (fun r : ℝ => paper5MovingFrameHeatGradOp c r
      (wholeLineTravelingWaveFlux p U V) x) volume 0 q

/-- The moving-frame heat-gradient history of a bounded continuous stationary
flux is interval-integrable.  The proof freezes the observation point at the
final time, shifts the source, and then reverses time. -/
theorem paper5MovingFrameHeatGradOp_waveFlux_intervalIntegrable
    (p : CMParams) {c q : ℝ} {U V : ℝ → ℝ}
    (hq : 0 < q)
    (hflux_cont : Continuous (wholeLineTravelingWaveFlux p U V))
    (hK : 0 ≤ paper5WaveFluxBound p)
    (hflux : ∀ y,
      |wholeLineTravelingWaveFlux p U V y| ≤ paper5WaveFluxBound p)
    (x : ℝ) :
    IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q := by
  let Flux : ℝ → ℝ := wholeLineTravelingWaveFlux p U V
  let F : ℝ → ℝ → ℝ := fun s y => Flux (y - c * s)
  have hFcont : Continuous (Function.uncurry F) := by
    dsimp only [F, Function.uncurry, Flux]
    exact hflux_cont.comp
      (continuous_snd.sub (continuous_const.mul continuous_fst))
  have hraw : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (q - s) (F s)
        (x + c * q)) volume 0 q := by
    apply wholeLineHeatGradOp_intervalIntegrable_of_jointMeasurable
      hq hK hFcont.aestronglyMeasurable
    · intro s _hs y
      simpa only [F, Flux] using hflux (y - c * s)
  have hreflected : IntervalIntegrable
      (fun s : ℝ => paper5MovingFrameHeatGradOp c (q - s)
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q := by
    apply hraw.congr_ae
    filter_upwards with s
    unfold paper5MovingFrameHeatGradOp
    have hshift := wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift
      (q - s) (-c * s) (wholeLineTravelingWaveFlux p U V) (x + c * q)
    rw [show x + c * (q - s) = x + c * q + -(c * s) by ring]
    simpa only [F, Flux, sub_eq_add_neg, neg_mul] using hshift.symm
  have hback := (hreflected.comp_sub_left q).symm
  simpa only [sub_self, sub_zero, sub_sub_cancel] using hback

set_option maxHeartbeats 4000000 in
-- Expanding the explicit rpow product bounds and generator balance requires
-- a larger elaboration budget than the project default.
/-- The corrected speed condition and regular traveling-wave data construct
the complete canonical wave-static package. -/
theorem paper5WaveStaticNaturalData_of_wave
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V) :
    Paper5WaveStaticNaturalData p c U V := by
  have hM1 : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hM0 : 0 ≤ MChi p := zero_le_one.trans hM1
  have hMpos : 0 < MChi p := zero_lt_one.trans_le hM1
  have hm0 : 0 ≤ p.m := zero_le_one.trans p.hm
  have hm10 : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
  have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
  have hD : 0 ≤ paper5ConcreteLu p := paper5ConcreteLu_nonneg p hMpos
  have hK : 0 ≤ paper5WaveFluxBound p := by
    unfold paper5WaveFluxBound
    positivity
  have hFD : 0 ≤ paper5WaveFluxDerivativeBound p := by
    unfold paper5WaveFluxDerivativeBound
    positivity
  have hB : 0 ≤ paper5WaveShiftedReactionBound p := by
    unfold paper5WaveShiftedReactionBound
    positivity
  have hE : 0 ≤ paper5WaveSecondDerivativeBound p c := by
    unfold paper5WaveSecondDerivativeBound
    positivity
  have hU2 : ContDiff ℝ 2 U := hreg.U_contDiff_two hTW
  have hV2 : ContDiff ℝ 2 V := hreg.V_contDiff_two hTW
  have hspeed := remark5SpeedCondition_of_correctedCStarStar_lt p hc
  have hbarrier := barrierSpeed_lt_of_correctedCStarStar_lt p hc
  have hlog : ∀ y, |deriv U y / U y| ≤ (1 : ℝ) :=
    abs_waveLogDerivative_le_one_of_barrier_speed
      p hbarrier hTW hreg hbound
  have hUd : ∀ y, |deriv U y| ≤ paper5ConcreteLu p := by
    intro y
    simpa only [paper5ConcreteLu] using
      remark_5_1_smooth_part1 p c paper5Sigma
        (by norm_num [paper5Sigma]) hchi hspeed U V hTW hbound
        hreg.U_diff hreg.V_deriv_diff hreg.deriv_U_cont
        hreg.deriv_U_diff hreg.deriv_U_tendszero hreg.V_nn hreg.V_bound y
  have hUIcc : ∀ y, U y ∈ Set.Icc (0 : ℝ) (MChi p) := fun y =>
    ⟨(hTW.U_pos y).le, hbound.le_MChi y⟩
  have hUpowm : ∀ y, (U y) ^ p.m ≤ (MChi p) ^ p.m := fun y =>
    Real.rpow_le_rpow (hUIcc y).1 (hUIcc y).2 hm0
  have hUpowm1 : ∀ y, (U y) ^ (p.m - 1) ≤
      (MChi p) ^ (p.m - 1) := fun y =>
    Real.rpow_le_rpow (hUIcc y).1 (hUIcc y).2 hm10
  have hUpowgamma : ∀ y, (U y) ^ p.γ ≤ (MChi p) ^ p.γ := fun y =>
    Real.rpow_le_rpow (hUIcc y).1 (hUIcc y).2 hgamma0
  have hVdiff : ∀ y, |V y - (U y) ^ p.γ| ≤ (MChi p) ^ p.γ := by
    intro y
    have hVle : V y ≤ (MChi p) ^ p.γ :=
      le_trans (le_abs_self (V y)) (hreg.V_bound y).1
    have hV0 := hreg.V_nn y
    have hUg0 : 0 ≤ (U y) ^ p.γ := Real.rpow_nonneg (hUIcc y).1 _
    rw [abs_le]
    constructor <;> linarith [hUpowgamma y]
  have hflux : ∀ y,
      |wholeLineTravelingWaveFlux p U V y| ≤ paper5WaveFluxBound p := by
    intro y
    unfold wholeLineTravelingWaveFlux paper5WaveFluxBound
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hUIcc y).1 _)]
    exact mul_le_mul (hUpowm y) (hreg.V_bound y).2
      (abs_nonneg _) (Real.rpow_nonneg hM0 _)
  have hfluxDiff : Differentiable ℝ
      (wholeLineTravelingWaveFlux p U V) := by
    intro y
    unfold wholeLineTravelingWaveFlux
    exact ((hreg.U_diff y).hasDerivAt.rpow_const (Or.inr p.hm)).differentiableAt.mul
      (hreg.V_deriv_diff y)
  have hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y :=
    fun y => (hfluxDiff y).hasDerivAt
  have hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤
        paper5WaveFluxDerivativeBound p := by
    intro y
    change |deriv (fun y => (U y) ^ p.m * deriv V y) y| ≤
      paper5WaveFluxDerivativeBound p
    rw [paper5WaveFluxDerivative_realization p hTW
      (hU2.of_le (by norm_num)) hV2]
    apply (abs_add_le _ _).trans
    unfold paper5WaveFluxDerivativeBound
    apply add_le_add
    · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm0,
        abs_of_nonneg (Real.rpow_nonneg (hUIcc y).1 _)]
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul le_rfl (hUpowm1 y) (Real.rpow_nonneg (hUIcc y).1 _)
            hm0)
          (hUd y) (abs_nonneg _) (mul_nonneg hm0
            (Real.rpow_nonneg hM0 _)))
        (hreg.V_bound y).2 (abs_nonneg _)
        (mul_nonneg (mul_nonneg hm0 (Real.rpow_nonneg hM0 _)) hD)
    · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hUIcc y).1 _)]
      exact mul_le_mul (hUpowm y) (hVdiff y) (abs_nonneg _)
        (Real.rpow_nonneg hM0 _)
  have hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)) := by
    have heq : deriv (wholeLineTravelingWaveFlux p U V) = fun y =>
        p.m * (U y) ^ (p.m - 1) * deriv U y * deriv V y +
          (U y) ^ p.m * (V y - (U y) ^ p.γ) := by
      funext y
      exact paper5WaveFluxDerivative_realization p hTW
        (hU2.of_le (by norm_num)) hV2
    rw [heq]
    have hpowm1 : Continuous (fun y => (U y) ^ (p.m - 1)) :=
      (Real.continuous_rpow_const hm10).comp hreg.U_cont
    have hpowm : Continuous (fun y => (U y) ^ p.m) :=
      (Real.continuous_rpow_const hm0).comp hreg.U_cont
    have hpowgamma : Continuous (fun y => (U y) ^ p.γ) :=
      (Real.continuous_rpow_const hgamma0).comp hreg.U_cont
    exact (((continuous_const.mul hpowm1).mul hreg.deriv_U_cont).mul
      (hV2.continuous_deriv (by norm_num))).add
        (hpowm.mul (hV2.continuous.sub hpowgamma))
  have hflux_cont : Continuous (wholeLineTravelingWaveFlux p U V) :=
    hfluxDiff.continuous
  have hreact : ∀ y,
      |wholeLineCauchyShiftedReaction p U y| ≤
        paper5WaveShiftedReactionBound p := by
    intro y
    simpa only [paper5WaveShiftedReactionBound] using
      wholeLineCauchyShiftedReaction_abs_le p hM0 hUIcc y
  have hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U) :=
    wholeLineCauchyShiftedReaction_continuous p hreg.U_cont
  have hUdd : ∀ y,
      |deriv (deriv U) y| ≤ paper5WaveSecondDerivativeBound p c := by
    intro y
    have hbal := wholeLineTravelingWave_movingGenerator_balance
      p hTW (x := y)
    have heq : deriv (deriv U) y =
        -(c * deriv U y) + U y -
          wholeLineTravelingWaveShiftedSource p U V y := by
      linarith
    rw [heq]
    calc
      |-(c * deriv U y) + U y -
          wholeLineTravelingWaveShiftedSource p U V y| ≤
          |c * deriv U y| + |U y| +
            |wholeLineTravelingWaveShiftedSource p U V y| := by
        exact (abs_sub _ _).trans (add_le_add
          (by simpa only [abs_neg] using abs_add_le (-(c * deriv U y)) (U y)) le_rfl)
      _ ≤ |c| * paper5ConcreteLu p + MChi p +
          (|p.χ| * paper5WaveFluxDerivativeBound p +
            paper5WaveShiftedReactionBound p) := by
        apply add_le_add
        · apply add_le_add
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hUd y) (abs_nonneg c)
          · rw [abs_of_pos (hTW.U_pos y)]
            exact hbound.le_MChi y
        · unfold wholeLineTravelingWaveShiftedSource
          calc
            |-p.χ * deriv (wholeLineTravelingWaveFlux p U V) y +
                wholeLineCauchyShiftedReaction p U y| ≤
                |-p.χ * deriv (wholeLineTravelingWaveFlux p U V) y| +
                  |wholeLineCauchyShiftedReaction p U y| := abs_add_le _ _
            _ ≤ _ := by
              rw [abs_mul, abs_neg]
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hfluxd y) (abs_nonneg p.χ))
                (hreact y)
      _ = paper5WaveSecondDerivativeBound p c := by
        unfold paper5WaveSecondDerivativeBound
        ring
  have hUddcont : Continuous (deriv (deriv U)) := by
    have hiter := hU2.continuous_iteratedDeriv 2 (by norm_num)
    have heq : iteratedDeriv 2 U = deriv (deriv U) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one]
    simpa only [heq] using hiter
  have hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q := by
    intro q hq x
    exact paper5MovingFrameHeatGradOp_waveFlux_intervalIntegrable
      p hq hflux_cont hK hflux x
  exact
    { hBlog := zero_le_one
      hD := hD
      hE := hE
      hKflux := hK
      hFD := hFD
      hB := hB
      hlog := hlog
      hUd := hUd
      hUdd := hUdd
      hUddcont := hUddcont
      hflux := hflux
      hfluxd := hfluxd
      hflux_has := hflux_has
      hfluxd_cont := hfluxd_cont
      hreact := hreact
      hreact_cont := hreact_cont
      hgrad_int := hgrad_int }

section AxiomAudit

#print axioms paper5MovingFrameHeatGradOp_waveFlux_intervalIntegrable
#print axioms paper5WaveStaticNaturalData_of_wave

end AxiomAudit

end ShenWork.Paper1
