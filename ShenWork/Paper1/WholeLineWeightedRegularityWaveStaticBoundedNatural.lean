import ShenWork.Paper1.WholeLineWeightedRegularityWaveStaticNatural

open Filter Function MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Wave-static bounds without division by the sensitivity

The explicit derivative budget used in the nonzero-sensitivity branch divides
by a positive power of `|chi|` and therefore degenerates at `chi = 0`.  For
the zero-sensitivity energy route only finiteness is needed.  The wave
regularity package already gives continuity of `U'` and convergence of `U'`
to zero at both spatial ends, so compactness supplies a genuine global bound.
-/

/-- A continuous real function converging to zero at both ends of the line is
globally bounded in absolute value, with a nonnegative bound. -/
theorem exists_nonneg_abs_bound_of_continuous_tendsto_zero_both_ends
    {f : ℝ → ℝ}
    (hcont : Continuous f)
    (htop : Tendsto f atTop (𝓝 0))
    (hbot : Tendsto f atBot (𝓝 0)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |f x| ≤ D := by
  have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds _ one_pos
  have htop_event : ∀ᶠ x in atTop, |f x| < 1 := by
    filter_upwards [htop hball] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hbot_event : ∀ᶠ x in atBot, |f x| < 1 := by
    filter_upwards [hbot hball] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  obtain ⟨R, hR⟩ := eventually_atTop.1 htop_event
  obtain ⟨L, hL⟩ := eventually_atBot.1 hbot_event
  obtain ⟨B, hB⟩ :=
    isCompact_Icc.bddAbove_image hcont.abs.continuousOn
  let D : ℝ := max 1 B
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro x
  by_cases hxL : x ≤ L
  · exact (hL x hxL).le.trans (le_max_left _ _)
  · by_cases hxR : R ≤ x
    · exact (hR x hxR).le.trans (le_max_left _ _)
    · have hxIcc : x ∈ Set.Icc L R :=
        ⟨le_of_not_ge hxL, le_of_not_ge hxR⟩
      exact (hB (Set.mem_image_of_mem _ hxIcc)).trans (le_max_right _ _)

/-- Flux-derivative bound obtained from an arbitrary global bound for `U'`. -/
def paper5WaveFluxDerivativeBoundOf
    (p : CMParams) (D : ℝ) : ℝ :=
  p.m * (MChi p) ^ (p.m - 1) * D * (MChi p) ^ p.γ +
    (MChi p) ^ p.m * (MChi p) ^ p.γ

/-- Wave second-derivative bound obtained from an arbitrary global bound for
`U'` and the corresponding flux-derivative bound. -/
def paper5WaveSecondDerivativeBoundOf
    (p : CMParams) (c D : ℝ) : ℝ :=
  |c| * D + MChi p +
    |p.χ| * paper5WaveFluxDerivativeBoundOf p D +
      paper5WaveShiftedReactionBound p

/-- Wave-static inputs for the exact-weight energy route, with a derivative
budget selected by compactness rather than the nonzero-sensitivity formula. -/
structure Paper5WaveStaticBoundedData
    (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) (D : ℝ) : Prop where
  hBlog : 0 ≤ (1 : ℝ)
  hD : 0 ≤ D
  hE : 0 ≤ paper5WaveSecondDerivativeBoundOf p c D
  hKflux : 0 ≤ paper5WaveFluxBound p
  hFD : 0 ≤ paper5WaveFluxDerivativeBoundOf p D
  hB : 0 ≤ paper5WaveShiftedReactionBound p
  hlog : ∀ y, |deriv U y / U y| ≤ (1 : ℝ)
  hUd : ∀ y, |deriv U y| ≤ D
  hUdd : ∀ y,
    |deriv (deriv U) y| ≤ paper5WaveSecondDerivativeBoundOf p c D
  hUddcont : Continuous (deriv (deriv U))
  hflux : ∀ y,
    |wholeLineTravelingWaveFlux p U V y| ≤ paper5WaveFluxBound p
  hfluxd : ∀ y,
    |deriv (wholeLineTravelingWaveFlux p U V) y| ≤
      paper5WaveFluxDerivativeBoundOf p D
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

/-- The corrected speed condition and ordinary traveling-wave regularity
construct finite wave-static bounds for every sensitivity, including zero. -/
theorem paper5WaveStaticBoundedData_of_wave
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V) :
    ∃ D : ℝ, Paper5WaveStaticBoundedData p c U V D := by
  have hM1 : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hM0 : 0 ≤ MChi p := zero_le_one.trans hM1
  have hm0 : 0 ≤ p.m := zero_le_one.trans p.hm
  have hm10 : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
  have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
  obtain ⟨D, hD, hUd⟩ :=
    exists_nonneg_abs_bound_of_continuous_tendsto_zero_both_ends
      hreg.deriv_U_cont hreg.deriv_U_tendszero.1
        hreg.deriv_U_tendszero.2
  have hK : 0 ≤ paper5WaveFluxBound p := by
    unfold paper5WaveFluxBound
    positivity
  have hFD : 0 ≤ paper5WaveFluxDerivativeBoundOf p D := by
    unfold paper5WaveFluxDerivativeBoundOf
    positivity
  have hB : 0 ≤ paper5WaveShiftedReactionBound p := by
    unfold paper5WaveShiftedReactionBound
    positivity
  have hE : 0 ≤ paper5WaveSecondDerivativeBoundOf p c D := by
    unfold paper5WaveSecondDerivativeBoundOf
    positivity
  have hU2 : ContDiff ℝ 2 U := hreg.U_contDiff_two hTW
  have hV2 : ContDiff ℝ 2 V := hreg.V_contDiff_two hTW
  have hbarrier := barrierSpeed_lt_of_correctedCStarStar_lt p hc
  have hlog : ∀ y, |deriv U y / U y| ≤ (1 : ℝ) :=
    abs_waveLogDerivative_le_one_of_barrier_speed
      p hbarrier hTW hreg hbound
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
    exact ((hreg.U_diff y).hasDerivAt.rpow_const
      (Or.inr p.hm)).differentiableAt.mul (hreg.V_deriv_diff y)
  have hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y :=
    fun y => (hfluxDiff y).hasDerivAt
  have hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤
        paper5WaveFluxDerivativeBoundOf p D := by
    intro y
    change |deriv (fun y => (U y) ^ p.m * deriv V y) y| ≤
      paper5WaveFluxDerivativeBoundOf p D
    rw [paper5WaveFluxDerivative_realization p hTW
      (hU2.of_le (by norm_num)) hV2]
    apply (abs_add_le _ _).trans
    unfold paper5WaveFluxDerivativeBoundOf
    apply add_le_add
    · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm0,
        abs_of_nonneg (Real.rpow_nonneg (hUIcc y).1 _)]
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul le_rfl (hUpowm1 y)
            (Real.rpow_nonneg (hUIcc y).1 _) hm0)
          (hUd y) (abs_nonneg _)
          (mul_nonneg hm0 (Real.rpow_nonneg hM0 _)))
        (hreg.V_bound y).2 (abs_nonneg _)
        (mul_nonneg (mul_nonneg hm0
          (Real.rpow_nonneg hM0 _)) hD)
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
      |deriv (deriv U) y| ≤
        paper5WaveSecondDerivativeBoundOf p c D := by
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
          (by simpa only [abs_neg] using
            abs_add_le (-(c * deriv U y)) (U y)) le_rfl)
      _ ≤ |c| * D + MChi p +
          (|p.χ| * paper5WaveFluxDerivativeBoundOf p D +
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
                  |wholeLineCauchyShiftedReaction p U y| :=
              abs_add_le _ _
            _ ≤ _ := by
              rw [abs_mul, abs_neg]
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hfluxd y) (abs_nonneg p.χ))
                (hreact y)
      _ = paper5WaveSecondDerivativeBoundOf p c D := by
        unfold paper5WaveSecondDerivativeBoundOf
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
  refine ⟨D, ?_⟩
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

#print axioms exists_nonneg_abs_bound_of_continuous_tendsto_zero_both_ends
#print axioms paper5WaveStaticBoundedData_of_wave

end AxiomAudit

end ShenWork.Paper1
