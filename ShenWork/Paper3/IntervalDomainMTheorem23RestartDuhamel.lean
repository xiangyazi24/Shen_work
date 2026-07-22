import ShenWork.Paper3.IntervalDomainMTheorem23Eventual

/-!
# Explicit-rate restart--Duhamel form of general-`m` Theorem 2.3

The faithful eventual theorem already reaches the nonlinear strong bootstrap
after a late sup-norm basin entry.  In the positive logistic branch, however,
its public route first forgets the explicit nonpositive-sensitivity spectral
gap and later extracts an unspecified one from modewise stability.

This file keeps the same restart--Duhamel scaffold but feeds it the available
gap directly.  Consequently the positive branch has the fixed rate
`(p.a * p.α) / 4`, while the minimal mass-constrained branch has the fixed
rate `unitIntervalNeumannSpectrum.firstNonzero / 4`.
-/

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- A positive strong restart with a specified full spectral gap gives the
eventual physical `C¹` estimate with the fixed nonlinear rate `gap / 4`.

This is the nonminimal counterpart of
`intervalDomainM_minimal_eventualC1_of_X2Sigma_restart_of_massGap`; both consume
the same general-`m` weighted quadratic Duhamel bootstrap. -/
theorem intervalDomainM_eventualC1_of_X2Sigma_restart_of_spectralGap
    (p : CM2Params) {uStar vStar gap : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    {tau : ℝ} (htau : 0 < tau)
    (hrestart :
      let sigma : ℝ := 7 / 8
      intervalDomainX2SigmaDistance sigma uStar (u tau) ≤
        intervalDomainStrongBootstrapRadiusGeneralM
          p sigma uStar vStar gap heq / 2) :
    let sigma : ℝ := 7 / 8
    let R := intervalDomainStrongBootstrapRadiusGeneralM
      p sigma uStar vStar gap heq
    let rate := gap / 4
    let Cu := intervalDomainX2SigmaValueTrace sigma +
      intervalDomainX2SigmaDerivativeTrace sigma
    let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
      intervalDomainX2SigmaC1Envelope sigma
    let C := (1 + Cu + Cv) * R * Real.exp (rate * tau)
    EventualExponentialC1ConvergenceWith
      intervalDomainM intervalDomainMSectorialStabilityNorms
        u v uStar vStar C rate tau := by
  dsimp only
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  change intervalDomainX2SigmaDistance sigma uStar (u tau) ≤
    intervalDomainStrongBootstrapRadiusGeneralM
      p sigma uStar vStar gap heq / 2 at hrestart
  let R : ℝ := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  let rate : ℝ := gap / 4
  let t₀ : ℝ := tau
  let Cu : ℝ := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv : ℝ := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C : ℝ := (1 + Cu + Cv) * R * Real.exp (rate * t₀)
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadiusGeneralM_pos
      p heq hgap.1 (by norm_num [sigma] : 0 < sigma) hsigma1
  have hrate : 0 < rate := by dsimp [rate]; linarith [hgap.1]
  have ht₀ : 0 < t₀ := by simpa [t₀] using htau
  have hCu : 0 ≤ Cu := by
    dsimp [Cu]
    exact add_nonneg (intervalDomainX2SigmaValueTrace_nonneg sigma)
      (intervalDomainX2SigmaDerivativeTrace_nonneg sigma)
  have hCv : 0 ≤ Cv := by
    dsimp [Cv]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (paper3UniformSignalStrongConstant_pos p uStar heq.u_pos).le)
      (intervalDomainX2SigmaC1Envelope_pos sigma).le
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by linarith) hR) (Real.exp_pos _)
  have hdecay := intervalDomainX2SigmaDistance_restart_exponential_bound_generalM
    hglobal htau heq hgap hsigmaStrong hsigma1 hrestart
  intro t htt₀
  let r : ℝ := t - t₀
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have htpos : 0 < t := lt_of_lt_of_le ht₀ htt₀
  have htime : tau + r = t := by dsimp [r, t₀]; ring
  have hdist : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      R * Real.exp (-rate * r) := by
    simpa [R, rate, htime] using hdecay r hr
  let H : ℝ := t + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  let hsol := hglobal H hH
  have htmem : t ∈ Set.Ioo (0 : ℝ) H := ⟨htpos, htH⟩
  have hmem : IntervalDomainX2SigmaPerturbation sigma uStar (u t) :=
    intervalDomainMX2SigmaPerturbation_of_classical_positive
      hsol htmem hsigma1.le
  have hcont : Continuous (u t) := solutionSlice_continuous hsol htmem
  have Hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) :=
    intervalDomainX2SigmaRealizationBounds_of_continuous
      hsigmaStrong hcont hmem
  have hexple : Real.exp (-rate * r) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [hrate.le, hr]
  have hdistR : intervalDomainX2SigmaDistance sigma uStar (u t) ≤ R := by
    calc
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
          R * Real.exp (-rate * r) := hdist
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left hexple hR.le
      _ = R := mul_one R
  have hlocal : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar :=
    hdistR.trans (intervalDomainStrongBootstrapRadiusGeneralM_le_positivity
      p sigma uStar vStar gap heq)
  have huC1 := Hreal.c1Distance_le
  have hvC1 := intervalDomainMSignal_c1Distance_le_X2Sigma
    hsol htmem heq Hreal hlocal
  have hsumC1 :
      intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
          intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
        (Cu + Cv) * intervalDomainX2SigmaDistance sigma uStar (u t) := by
    calc
      _ ≤ Cu * intervalDomainX2SigmaDistance sigma uStar (u t) +
          Cv * intervalDomainX2SigmaDistance sigma uStar (u t) := by
        exact add_le_add (by simpa [Cu] using huC1)
          (by simpa [Cv] using hvC1)
      _ = _ := by ring
  have hexpShift :
      Real.exp (-rate * r) =
        Real.exp (rate * t₀) * Real.exp (-rate * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [r]
    ring
  calc
    intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
        intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
      (Cu + Cv) * intervalDomainX2SigmaDistance sigma uStar (u t) := hsumC1
    _ ≤ (Cu + Cv) * (R * Real.exp (-rate * r)) :=
      mul_le_mul_of_nonneg_left hdist (add_nonneg hCu hCv)
    _ ≤ C * Real.exp (-rate * t) := by
      rw [hexpShift]
      dsimp [C]
      have he0 : 0 ≤ Real.exp (rate * t₀) := (Real.exp_pos _).le
      have het0 : 0 ≤ Real.exp (-rate * t) := (Real.exp_pos _).le
      nlinarith [mul_nonneg hR.le (mul_nonneg he0 het0)]

/-- Uniform sup attraction followed by the faithful general-`m` basin entry
and a specified-gap restart.  Unlike the older public wrapper, this theorem
does not discard `gap`, so its rate is definitionally `gap / 4`. -/
theorem intervalDomainM_eventualC1_of_uniformSup_of_spectralGap
    (p : CM2Params) {uStar vStar gap : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hconv : UniformConvergesInSup intervalDomainM u uStar) :
    ∃ C > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomainM intervalDomainMSectorialStabilityNorms
          u v uStar vStar C (gap / 4) t₀ := by
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  obtain ⟨deltaBasin, hdeltaBasin, T, hT, henter⟩ :=
    intervalDomainMSupToStrongBasinEntry_proved
      p sigma uStar vStar gap hsigmaStrong hsigma1 heq hgap
  have hevent : ∀ᶠ t : ℝ in atTop,
      intervalDomainM.supNorm (fun x => u t x - uStar) < deltaBasin :=
    hconv.eventually (Iio_mem_nhds hdeltaBasin)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hevent
  let tau₁ : ℝ := max threshold 1
  have htau₁ : 0 < tau₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hclose : SupCloseToConstant intervalDomainM (u tau₁) uStar deltaBasin :=
    hthreshold tau₁ (le_max_left _ _)
  have hsol := huv.classical (tau₁ + 1) (by linarith)
  have hpid : PositiveInitialDatum intervalDomainM (u tau₁) :=
    positiveInitialDatum_of_paperPositiveInitialDatumM
      (classicalSolution_slice_paperPositiveInitialDatumM
        hsol ⟨htau₁, by linarith⟩)
  let us : ℝ → intervalDomainPoint → ℝ := fun t x => u (t + tau₁) x
  let vs : ℝ → intervalDomainPoint → ℝ := fun t x => v (t + tau₁) x
  have hshiftGlobal :
      IsPaper2GlobalClassicalSolution intervalDomainM p us vs := by
    intro T₂ hT₂
    have hsum : 0 < T₂ + tau₁ := by linarith
    have hsolT := huv.classical (T₂ + tau₁) hsum
    have hshift := classicalSolution_timeShiftM hsolT htau₁ (by linarith)
    simpa only [add_sub_cancel_right] using hshift
  have hshiftTrace : InitialTrace intervalDomainM (u tau₁) us := by
    simpa [us] using timeShiftInitialTraceM hsol htau₁ (by linarith)
  have hentry := henter (u tau₁) hpid hclose us vs
    hshiftGlobal hshiftTrace
  let tauRestart : ℝ := T + tau₁
  have htauRestart : 0 < tauRestart := by dsimp [tauRestart]; linarith
  have hrestart :
      intervalDomainX2SigmaDistance sigma uStar (u tauRestart) ≤
        intervalDomainStrongBootstrapRadiusGeneralM
          p sigma uStar vStar gap heq / 2 := by
    change intervalDomainX2SigmaDistance sigma uStar (u (T + tau₁)) ≤ _
    simpa [us] using hentry.2
  have hresult :=
    intervalDomainM_eventualC1_of_X2Sigma_restart_of_spectralGap
      p heq hgap huv.1 htauRestart hrestart
  let R := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  let rate := gap / 4
  let Cu := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C := (1 + Cu + Cv) * R * Real.exp (rate * tauRestart)
  have hR : 0 < R := intervalDomainStrongBootstrapRadiusGeneralM_pos
    p heq hgap.1 (by norm_num [sigma] : 0 < sigma) hsigma1
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
  refine ⟨C, hC, tauRestart, htauRestart, ?_⟩
  simpa [sigma, R, rate, Cu, Cv, C] using hresult

/-- Mass-constrained counterpart with the fixed rate `gap / 4`. -/
theorem
intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap_with_rate
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar gap : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hconv : UniformConvergesInSup intervalDomainM u uStar) :
    ∃ C > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomainM intervalDomainMSectorialStabilityNorms
          u v uStar vStar C (gap / 4) t₀ := by
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  obtain ⟨deltaBasin, hdeltaBasin, T, hT, henter⟩ :=
    intervalDomainMassSupToStrongBasinEntryGeneralM_proved
      p hsigmaStrong hsigma1 ha0 hb0 heq hgap
  have hevent : ∀ᶠ t : ℝ in atTop,
      intervalDomainM.supNorm (fun x => u t x - uStar) < deltaBasin :=
    hconv.eventually (Iio_mem_nhds hdeltaBasin)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hevent
  let tau₁ : ℝ := max threshold 1
  have htau₁ : 0 < tau₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hclose : SupCloseToConstant intervalDomainM (u tau₁) uStar deltaBasin :=
    hthreshold tau₁ (le_max_left _ _)
  have hsol := huv.classical (tau₁ + 1) (by linarith)
  have hpid : PositiveInitialDatum intervalDomainM (u tau₁) :=
    positiveInitialDatum_of_paperPositiveInitialDatumM
      (classicalSolution_slice_paperPositiveInitialDatumM
        hsol ⟨htau₁, by linarith⟩)
  let us : ℝ → intervalDomainPoint → ℝ := fun t x => u (t + tau₁) x
  let vs : ℝ → intervalDomainPoint → ℝ := fun t x => v (t + tau₁) x
  have hshiftGlobal :
      IsPaper2GlobalClassicalSolution intervalDomainM p us vs := by
    intro T₂ hT₂
    have hsum : 0 < T₂ + tau₁ := by linarith
    have hsolT := huv.classical (T₂ + tau₁) hsum
    have hshift := classicalSolution_timeShiftM hsolT htau₁ (by linarith)
    simpa only [add_sub_cancel_right] using hshift
  have hshiftTrace : InitialTrace intervalDomainM (u tau₁) us := by
    simpa [us] using timeShiftInitialTraceM hsol htau₁ (by linarith)
  have hshiftMass :
      HasEquilibriumMassOnPositiveTimes intervalDomainM us uStar := by
    intro t ht
    exact hmass (t + tau₁) (by linarith)
  have hentry := henter (u tau₁) hpid hclose us vs
    hshiftGlobal hshiftTrace hshiftMass
  let tauRestart : ℝ := T + tau₁
  have htauRestart : 0 < tauRestart := by dsimp [tauRestart]; linarith
  have hrestart :
      intervalDomainX2SigmaDistance sigma uStar (u tauRestart) ≤
        intervalDomainStrongBootstrapRadiusGeneralM
          p sigma uStar vStar gap heq / 2 := by
    change intervalDomainX2SigmaDistance sigma uStar (u (T + tau₁)) ≤ _
    simpa [us] using hentry.2
  have hresult :=
    intervalDomainM_minimal_eventualC1_of_X2Sigma_restart_of_massGap
      p ha0 hb0 heq hgap huv.1 hmass htauRestart hrestart
  let R := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  let rate := gap / 4
  let Cu := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C := (1 + Cu + Cv) * R * Real.exp (rate * tauRestart)
  have hR : 0 < R := intervalDomainStrongBootstrapRadiusGeneralM_pos
    p heq hgap.1 (by norm_num [sigma] : 0 < sigma) hsigma1
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
  refine ⟨C, hC, tauRestart, htauRestart, ?_⟩
  simpa [sigma, R, rate, Cu, Cv, C] using hresult

/-- Global attraction plus a single fixed exponential rate for every orbit.
The prefactor and entrance time remain orbit-dependent, as they must for a
global theorem with no uniform initial-size bound. -/
def EventuallyGloballyExponentiallyStableNonminimalWithRate
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar rate : ℝ) : Prop :=
  GloballyAsymptoticallyStableNonminimal D p uStar vStar ∧
    0 < rate ∧
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
        ∃ C > 0, ∃ t₀ > 0,
          EventualExponentialC1ConvergenceWith
            D N u v uStar vStar C rate t₀

/-- Mass-constrained fixed-rate global stability. -/
def EventuallyGloballyExponentiallyStableMinimalWithRate
    (D : BoundedDomainData) (p : CM2Params) (N : StabilityNorms D)
    (uStar vStar rate : ℝ) : Prop :=
  GloballyAsymptoticallyStableMinimalOnPhysicalMass D p uStar vStar ∧
    0 < rate ∧
    ∀ u v : ℝ → D.Point → ℝ,
      PositiveGlobalBoundedSolution D p u v →
      HasEquilibriumMassOnPositiveTimes D u uStar →
        ∃ C > 0, ∃ t₀ > 0,
          EventualExponentialC1ConvergenceWith
            D N u v uStar vStar C rate t₀

/-- The positive branch of general-`m` Theorem 2.3 with the explicit uniform
rate `(p.a * p.α) / 4`. -/
theorem intervalDomainM_Theorem_2_3_positive_via_restartDuhamel
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) :
    ∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      EventuallyGloballyExponentiallyStableNonminimalWithRate
        intervalDomainM p intervalDomainMSectorialStabilityNorms
          eq.1 eq.2 ((p.a * p.α) / 4) := by
  intro ha hb
  dsimp
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_positive p ha hb
  have hgap : UnitIntervalLinearSpectralGap p eq.1 eq.2 (p.a * p.α) := by
    simpa [eq] using
      positiveEquilibrium_UnitIntervalLinearSpectralGap_of_chi_nonpos
        p hχ ha hb
  have hglobal : GloballyAsymptoticallyStableNonminimal
      intervalDomainM p eq.1 eq.2 := by
    simpa [eq] using
      intervalDomainM_chiNonpos_globallyAsymptoticallyStableNonminimal
        p hχ ha hb
  refine ⟨hglobal, div_pos (mul_pos ha p.hα) (by norm_num), ?_⟩
  intro u v huv
  simpa [eq] using
    intervalDomainM_eventualC1_of_uniformSup_of_spectralGap
      p heq hgap huv (hglobal u v huv)

/-- The minimal branch with the explicit uniform rate
`unitIntervalNeumannSpectrum.firstNonzero / 4`. -/
theorem intervalDomainM_Theorem_2_3_minimal_via_restartDuhamel
    (p : CM2Params) (hχ : p.χ₀ ≤ 0)
    (ha0 : p.a = 0) (hb0 : p.b = 0) :
    ∀ uStar > 0,
      let eq := minimalEquilibrium p uStar
      EventuallyGloballyExponentiallyStableMinimalWithRate
        intervalDomainM p intervalDomainMSectorialStabilityNorms
          eq.1 eq.2 (unitIntervalNeumannSpectrum.firstNonzero / 4) := by
  intro uStar huStar
  let eq := minimalEquilibrium p uStar
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_minimal
      p ha0 hb0 uStar huStar
  have hgap : UnitIntervalLinearMassSpectralGap p eq.1 eq.2
      unitIntervalNeumannSpectrum.firstNonzero := by
    simpa [eq] using
      minimalEquilibrium_UnitIntervalLinearMassSpectralGap_of_chi_nonpos
        p hχ ha0 huStar
  have hglobal : GloballyAsymptoticallyStableMinimalOnPhysicalMass
      intervalDomainM p eq.1 eq.2 := by
    simpa [eq] using
      intervalDomainM_chiNonpos_globallyAsymptoticallyStableMinimal
        p ha0 hb0 hχ huStar
  refine ⟨hglobal, by linarith [hgap.1], ?_⟩
  intro u v huv hmass
  simpa [eq] using
    intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap_with_rate
      p ha0 hb0 heq hgap huv hmass (hglobal u v huv hmass)

/-- Fixed-rate form of the full faithful general-`m` Theorem 2.3.  This is a
strict refinement of `intervalDomainM_Theorem_2_3_EventualGlobalStability`:
the rate is outside the orbit quantifier in both branches. -/
theorem intervalDomainM_Theorem_2_3_via_restartDuhamel
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) :
    (∀ (ha : 0 < p.a) (hb : 0 < p.b),
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      EventuallyGloballyExponentiallyStableNonminimalWithRate
        intervalDomainM p intervalDomainMSectorialStabilityNorms
          eq.1 eq.2 ((p.a * p.α) / 4)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        EventuallyGloballyExponentiallyStableMinimalWithRate
          intervalDomainM p intervalDomainMSectorialStabilityNorms
            eq.1 eq.2 (unitIntervalNeumannSpectrum.firstNonzero / 4)) := by
  exact ⟨intervalDomainM_Theorem_2_3_positive_via_restartDuhamel p hχ,
    fun ha0 hb0 =>
      intervalDomainM_Theorem_2_3_minimal_via_restartDuhamel
        p hχ ha0 hb0⟩

#print axioms intervalDomainM_eventualC1_of_X2Sigma_restart_of_spectralGap
#print axioms intervalDomainM_eventualC1_of_uniformSup_of_spectralGap
#print axioms
  intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap_with_rate
#print axioms intervalDomainM_Theorem_2_3_positive_via_restartDuhamel
#print axioms intervalDomainM_Theorem_2_3_minimal_via_restartDuhamel
#print axioms intervalDomainM_Theorem_2_3_via_restartDuhamel

end

end ShenWork.Paper3
