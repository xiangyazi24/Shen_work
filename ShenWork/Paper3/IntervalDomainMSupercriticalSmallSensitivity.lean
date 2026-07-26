import ShenWork.Paper3.IntervalDomainMNegativePowerBox
import ShenWork.Paper3.IntervalDomainMMinimalEntropyGlobal
import ShenWork.Paper3.IntervalDomainMMinimalWeakSupBasinEntry

/-!
# Small-sensitivity supercritical minimal stability

This file closes the general-`m` good-slice route.  A certified local
supremum radius is reached at an arbitrarily late entropy good slice; an
autonomous time shift then feeds the existing mass-constrained strong
bootstrap.  The resulting capstone applies for every `m > 1`, with no upper
bound on `m`.
-/

open Filter MeasureTheory Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.PDE.SectorialOperator

namespace ShenWork.Paper3

noncomputable section

/-- A certified `C⁰` local basin radius for the minimal mass-constrained
general-`m` dynamics.  The fixed strong exponent is `sigma = 7/8`; the
spectral gap and finite smoothing window are packaged existentially. -/
def IntervalDomainMMinimalSupBasinRadius
    (p : CM2Params) (uStar vStar delta : ℝ) : Prop :=
  ∃ heq : Paper3ConstantEquilibrium p uStar vStar,
    ∃ gap : ℝ, UnitIntervalLinearMassSpectralGap p uStar vStar gap ∧
      ∃ T > 0,
        ∀ u₀ : intervalDomainPoint → ℝ,
          PositiveInitialDatum intervalDomainM u₀ →
          SupCloseToConstant intervalDomainM u₀ uStar delta →
          ∀ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomainM p u v →
            InitialTrace intervalDomainM u₀ u →
            HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
              IntervalDomainX2SigmaPerturbation (7 / 8) uStar (u T) ∧
              intervalDomainX2SigmaDistance (7 / 8) uStar (u T) ≤
                intervalDomainStrongBootstrapRadiusGeneralM
                  p (7 / 8) uStar vStar gap heq / 2

/-- Every linearly stable positive minimal equilibrium has a positive local
sup basin radius smaller than its equilibrium mass. -/
theorem exists_intervalDomainMMinimalSupBasinRadius_of_linearlyStable
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    ∃ delta > 0, delta < uStar ∧
      IntervalDomainMMinimalSupBasinRadius p uStar vStar delta := by
  obtain ⟨gap, _hgapPos, hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
  have hsigmaStrong : (3 / 4 : ℝ) < 7 / 8 := by norm_num
  have hsigma1 : (7 / 8 : ℝ) < 1 := by norm_num
  obtain ⟨delta₀, hdelta₀, T, hT, henter⟩ :=
    intervalDomainMassSupToStrongBasinEntryGeneralM_proved
      p hsigmaStrong hsigma1 ha0 hb0 heq hgap
  let delta : ℝ := min delta₀ (uStar / 2)
  have hdelta : 0 < delta :=
    lt_min hdelta₀ (div_pos heq.u_pos (by norm_num))
  have hdeltaStar : delta < uStar := by
    have hle : delta ≤ uStar / 2 := min_le_right _ _
    linarith [heq.u_pos]
  refine ⟨delta, hdelta, hdeltaStar, heq, gap, hgap, T, hT, ?_⟩
  intro u₀ hu₀ hclose u v hglobal htrace hmass
  apply henter u₀ hu₀
  · change intervalDomainM.supNorm (fun x => u₀ x - uStar) < delta₀
    exact hclose.lt.trans_le (min_le_left _ _)
  · exact hglobal
  · exact htrace
  · exact hmass

/-- Restart from one slice already lying in a certified local sup basin. -/
theorem intervalDomainM_minimal_eventualC1_of_supBasinSlice
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar delta : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hbasin : IntervalDomainMMinimalSupBasinRadius p uStar vStar delta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    {tau : ℝ} (htau : 0 < tau)
    (hclose : SupCloseToConstant intervalDomainM (u tau) uStar delta) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomainM intervalDomainMSectorialStabilityNorms
          u v uStar vStar C rate t₀ := by
  obtain ⟨heqBasin, gap, hgap, T, hT, henter⟩ := hbasin
  have hsol := huv.classical (tau + 1) (by linarith)
  have hpid : PositiveInitialDatum intervalDomainM (u tau) :=
    positiveInitialDatum_of_paperPositiveInitialDatumM
      (classicalSolution_slice_paperPositiveInitialDatumM
        hsol ⟨htau, by linarith⟩)
  let us : ℝ → intervalDomainPoint → ℝ := fun t x => u (t + tau) x
  let vs : ℝ → intervalDomainPoint → ℝ := fun t x => v (t + tau) x
  have hshiftGlobal :
      IsPaper2GlobalClassicalSolution intervalDomainM p us vs := by
    intro T₂ hT₂
    have hsum : 0 < T₂ + tau := by linarith
    have hsolT := huv.classical (T₂ + tau) hsum
    have hshift := classicalSolution_timeShiftM hsolT htau (by linarith)
    simpa only [add_sub_cancel_right] using hshift
  have hshiftTrace : InitialTrace intervalDomainM (u tau) us := by
    simpa [us] using timeShiftInitialTraceM hsol htau (by linarith)
  have hshiftMass :
      HasEquilibriumMassOnPositiveTimes intervalDomainM us uStar := by
    intro t ht
    exact hmass (t + tau) (by linarith)
  have hentry := henter (u tau) hpid hclose us vs
    hshiftGlobal hshiftTrace hshiftMass
  let tauRestart : ℝ := T + tau
  have htauRestart : 0 < tauRestart := by
    dsimp [tauRestart]
    linarith
  have hrestart :
      intervalDomainX2SigmaDistance (7 / 8) uStar (u tauRestart) ≤
        intervalDomainStrongBootstrapRadiusGeneralM
          p (7 / 8) uStar vStar gap heq / 2 := by
    change intervalDomainX2SigmaDistance (7 / 8) uStar (u (T + tau)) ≤ _
    simpa [us] using hentry.2
  have hresult :=
    intervalDomainM_minimal_eventualC1_of_X2Sigma_restart_of_massGap
      p ha0 hb0 heq hgap huv.1 hmass htauRestart hrestart
  let sigma : ℝ := 7 / 8
  let R := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  let rate := gap / 4
  let Cu := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C := (1 + Cu + Cv) * R * Real.exp (rate * tauRestart)
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  have hR : 0 < R := intervalDomainStrongBootstrapRadiusGeneralM_pos
    p heq hgap.1 (by norm_num [sigma] : 0 < sigma) hsigma1
  have hrate : 0 < rate := by
    dsimp [rate]
    linarith [hgap.1]
  have hCu : 0 ≤ Cu := add_nonneg
    (intervalDomainX2SigmaValueTrace_nonneg sigma)
    (intervalDomainX2SigmaDerivativeTrace_nonneg sigma)
  have hCv : 0 ≤ Cv := mul_nonneg
    (mul_nonneg (by norm_num)
      (paper3UniformSignalStrongConstant_pos p uStar heq.u_pos).le)
    (intervalDomainX2SigmaC1Envelope_pos sigma).le
  have hC : 0 < C := mul_pos
    (mul_pos (by linarith : (0 : ℝ) < 1 + Cu + Cv) hR)
    (Real.exp_pos _)
  exact ⟨C, hC, rate, hrate, tauRestart, htauRestart, hresult⟩

/-- A certified local radius together with the exact small-sensitivity
threshold yields eventual exponential `C¹` convergence of each bounded
mass-constrained orbit. -/
theorem intervalDomainM_minimal_eventualC1_supercritical_smallSensitivity
    (p : CM2Params) (hm : 1 < p.m)
    (ha0 : p.a = 0) (hb0 : p.b = 0) (hbeta : 1 ≤ p.β)
    {uStar vStar delta : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hchi : 0 < p.χ₀)
    (hdelta : 0 < delta) (hdeltaStar : delta < uStar)
    (hbasin : IntervalDomainMMinimalSupBasinRadius p uStar vStar delta)
    (hsmall :
      p.χ₀ < supercriticalSmallSensitivityThresholdM p uStar delta)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomainM intervalDomainMSectorialStabilityNorms
          u v uStar vStar C rate t₀ := by
  obtain ⟨tau, htauOne, hclose⟩ :=
    intervalDomainM_minimal_exists_late_supClose_smallSensitivity
      p hm hb0 hbeta hchi heq hdelta hdeltaStar hsmall
        huv hmass (T := (1 : ℝ)) one_pos
  exact intervalDomainM_minimal_eventualC1_of_supBasinSlice
    p ha0 hb0 heq hbasin huv hmass
      (lt_of_lt_of_le one_pos htauOne) hclose

/-- **Paper 3 Theorem 2.5, supercritical small-sensitivity branch.**

For every `m > 1`, including `m > 2`, a linearly stable positive minimal
equilibrium is eventually globally exponentially stable on its mass
hyperplane whenever `chi₀` is below the explicit negative-power threshold
associated with a certified local `C⁰` basin radius. -/
theorem intervalDomainM_Theorem_2_5_supercritical_smallSensitivity
    (p : CM2Params) (_hN : p.N = 1)
    (hm : 1 < p.m) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar delta : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
    (hlinear : p.χ₀ < minimalEquilibriumLinStabThresholdM p uStar)
    (hdelta : 0 < delta) (hdeltaStar : delta < uStar)
    (hbasin : IntervalDomainMMinimalSupBasinRadius p
      (minimalEquilibrium p uStar).1 (minimalEquilibrium p uStar).2 delta)
    (hsmall :
      p.χ₀ < supercriticalSmallSensitivityThresholdM p uStar delta) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  let eq := minimalEquilibrium p uStar
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_minimal p ha0 hb0 uStar huStar
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    have hcrit : p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      lt_of_lt_of_le hlinear
        (paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
          unitIntervalNeumannSpectrum p
          unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar)
    simpa [eq] using
      minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hcrit
  obtain ⟨_gap, _hgapPos, _hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
      HasEquilibriumMassOnPositiveTimes intervalDomainM u eq.1 →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith
          intervalDomainM intervalDomainMSectorialStabilityNorms
            u v eq.1 eq.2 C rate t₀ := by
    intro u v huv hmass
    apply intervalDomainM_minimal_eventualC1_supercritical_smallSensitivity
      p hm ha0 hb0 hbeta heq hchi hdelta hdeltaStar
        (by simpa [eq] using hbasin)
        (by simpa [eq] using hsmall) huv hmass
  refine ⟨?_, hproduce⟩
  intro u v huv hmass
  obtain ⟨C, _hC, rate, hrate, _t₀, _ht₀, hbound⟩ :=
    hproduce u v huv hmass
  exact intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

/-- The linearly stable range always supplies at least one admissible local
radius.  For that radius, the displayed small-sensitivity threshold is a
complete sufficient condition for the all-`m > 1` capstone. -/
theorem intervalDomainM_supercritical_smallSensitivity_exists_threshold
    (p : CM2Params) (hN : p.N = 1)
    (hm : 1 < p.m) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
    (hlinear : p.χ₀ < minimalEquilibriumLinStabThresholdM p uStar) :
    ∃ delta > 0, delta < uStar ∧
      (p.χ₀ < supercriticalSmallSensitivityThresholdM p uStar delta →
        EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
          intervalDomainMSectorialStabilityNorms
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2) := by
  let eq := minimalEquilibrium p uStar
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_minimal p ha0 hb0 uStar huStar
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    have hcrit : p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      lt_of_lt_of_le hlinear
        (paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
          unitIntervalNeumannSpectrum p
          unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar)
    simpa [eq] using
      minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hcrit
  obtain ⟨delta, hdelta, hdeltaStar, hbasin⟩ :=
    exists_intervalDomainMMinimalSupBasinRadius_of_linearlyStable
      p ha0 hb0 heq hstable
  refine ⟨delta, hdelta, ?_, ?_⟩
  · simpa [eq] using hdeltaStar
  · intro hsmall
    exact intervalDomainM_Theorem_2_5_supercritical_smallSensitivity
      p hN hm ha0 hb0 hbeta huStar hchi hlinear hdelta
        (by simpa [eq] using hdeltaStar)
        (by simpa [eq] using hbasin) hsmall

#print axioms
  exists_intervalDomainMMinimalSupBasinRadius_of_linearlyStable
#print axioms intervalDomainM_minimal_eventualC1_of_supBasinSlice
#print axioms
  intervalDomainM_minimal_eventualC1_supercritical_smallSensitivity
#print axioms
  intervalDomainM_Theorem_2_5_supercritical_smallSensitivity
#print axioms
  intervalDomainM_supercritical_smallSensitivity_exists_threshold

end

end ShenWork.Paper3
