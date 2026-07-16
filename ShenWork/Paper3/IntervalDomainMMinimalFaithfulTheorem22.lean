/- Faithful general-`m` Paper 3 Theorem 2.2 on the minimal mass hyperplane,
and the complete four-branch faithful eventual Theorem 2.2 headline for the
`intervalDomainM` model.

This mirrors `IntervalDomainMinimalFaithfulTheorem22.lean` with every
`p.m = 1` hypothesis removed: mass conservation, basin entry, strong
bootstrap, and small-data global existence are the faithful general-`m`
mass-projected statements. -/
import ShenWork.Paper3.IntervalDomainMMinimalSmallDataGlobalExistence
import ShenWork.Paper3.IntervalDomainMFaithfulTheorem22

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- The datum mass and the exact faithful minimal-model mass ODE give the
physical positive-time mass interface on a constructed global solution. -/
theorem intervalDomainM_minimal_hasEquilibriumMassOnPositiveTimes_of_trace
    (p : CM2Params) {uStar : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hmass₀ : intervalDomainM.integral u₀ = intervalDomainM.volume * uStar) :
    HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar := by
  intro t ht0
  let H : ℝ := t + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  calc
    intervalDomainM.integral (u t) = intervalDomainM.integral u₀ :=
      intervalDomainM_minimal_mass_eq_initial_before
        p ha0 hb0 hu₀ (hglobal H hH) htrace ht0 htH
    _ = intervalDomainM.volume * uStar := hmass₀

/-- A strong mass-constrained restart at one positive time already contains
the whole eventual physical `C1` conclusion for the faithful general-`m`
minimal model. -/
theorem intervalDomainM_minimal_eventualC1_of_X2Sigma_restart_of_massGap
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar gap : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
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
  have hdecay := intervalDomainMassX2SigmaDistance_restart_exponential_bound_generalM
    hglobal ha0 hb0 htau heq hgap hsigmaStrong hsigma1 hmass hrestart
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

/-- Fully discharged faithful general-`m` Stage B for the neutral minimal
equilibrium.  The small-data global orbit and its physical mass are
constructed internally. -/
theorem
intervalDomainM_eventualMassConstrainedLocallyExponentiallyStableFromSup_unconditional
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    EventualMassConstrainedLocallyExponentiallyStableFromSup
      intervalDomainM p intervalDomainMSectorialStabilityNorms
        uStar vStar := by
  obtain ⟨gap, hgap0, hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
  obtain ⟨deltaGlobal, hdeltaGlobal, hglobalExistence⟩ :=
    intervalDomainM_massConstrainedSmallDataGlobalExistence_of_linearlyStable
      p ha0 hb0 heq hstable
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  obtain ⟨deltaEntry, hdeltaEntry, T, hT, hentry⟩ :=
    intervalDomainMassSupToStrongBasinEntryGeneralM_proved
      p hsigmaStrong hsigma1 ha0 hb0 heq hgap
  let delta := min deltaGlobal deltaEntry
  have hdelta : 0 < delta := lt_min hdeltaGlobal hdeltaEntry
  let R := intervalDomainStrongBootstrapRadiusGeneralM
    p sigma uStar vStar gap heq
  let rate := gap / 4
  let Cu := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C := (1 + Cu + Cv) * R * Real.exp (rate * T)
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadiusGeneralM_pos
      p heq hgap.1 (by norm_num [sigma] : 0 < sigma) hsigma1
  have hrate : 0 < rate := by dsimp [rate]; linarith
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
  refine ⟨delta, hdelta, C, hC, rate, hrate, T, hT, ?_⟩
  intro u₀ hu₀ hclose hmass₀
  have hcloseGlobal : SupCloseToConstant
      intervalDomainM u₀ uStar deltaGlobal :=
    lt_of_lt_of_le hclose.lt (by dsimp [delta]; exact min_le_left _ _)
  have hcloseEntry : SupCloseToConstant
      intervalDomainM u₀ uStar deltaEntry :=
    lt_of_lt_of_le hclose.lt (by dsimp [delta]; exact min_le_right _ _)
  obtain ⟨u, v, hglobal, htrace⟩ :=
    hglobalExistence u₀ hu₀ hcloseGlobal hmass₀
  have hmass :=
    intervalDomainM_minimal_hasEquilibriumMassOnPositiveTimes_of_trace
      p ha0 hb0 hu₀ hglobal htrace hmass₀
  have hrestart :=
    hentry u₀ hu₀ hcloseEntry u v hglobal htrace hmass
  refine ⟨u, v, hglobal, htrace, ?_⟩
  simpa [sigma, R, rate, Cu, Cv, C] using
    intervalDomainM_minimal_eventualC1_of_X2Sigma_restart_of_massGap
      p ha0 hb0 heq hgap hglobal hmass hT hrestart.2

/-- Complete faithful general-`m` stable branch at a neutral
mass-parametrized equilibrium. -/
theorem intervalDomainM_Theorem_2_2_minimalEventual_branch_unconditional
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (C : Paper3Constants intervalDomainM p)
    (hC : Paper3ConstantsUsesCriticalSpectrum
      unitIntervalNeumannSpectrum p C)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : p.χ₀ < C.chiCritical uStar) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      EventualMassConstrainedLocallyExponentiallyStableFromSup
        intervalDomainM p intervalDomainMSectorialStabilityNorms
          eq.1 eq.2 := by
  dsimp
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p
      (minimalEquilibrium p uStar).1 (minimalEquilibrium p uStar).2 :=
    hC.minimalEquilibrium_linearlyStable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hchi
  exact ⟨hstable,
    intervalDomainM_eventualMassConstrainedLocallyExponentiallyStableFromSup_unconditional
      p ha0 hb0
        (paper3ConstantEquilibrium_minimal p ha0 hb0 uStar huStar) hstable⟩

/-- Faithful general-`m` eventual Theorem 2.2 on the neutral minimal
parameter slice. -/
theorem intervalDomainM_Theorem_2_2_Eventual_minimal_unconditional
    (p : CM2Params) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (C : Paper3Constants intervalDomainM p)
    (hC : Paper3ConstantsUsesCriticalSpectrum
      unitIntervalNeumannSpectrum p C) :
    Theorem_2_2_EventualExponentialStability
      intervalDomainM p unitIntervalNeumannSpectrum
        intervalDomainMSectorialStabilityNorms C := by
  refine Theorem_2_2_EventualExponentialStability.of_parts ?_ ?_ ?_ ?_
  · intro ha _hb
    exact False.elim ((ne_of_gt ha) ha0)
  · intro ha _hb
    exact False.elim ((ne_of_gt ha) ha0)
  · intro _ha0 _hb0 uStar huStar
    dsimp
    intro hchi
    exact intervalDomainM_Theorem_2_2_minimalEventual_branch_unconditional
      p ha0 hb0 C hC huStar hchi
  · intro _ha0 _hb0 uStar huStar
    dsimp
    intro hchi
    exact hC.minimalEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hchi

/-- Unconditional faithful general-`m` eventual Theorem 2.2 for every
admissible parameter tuple.  The only two nonempty equilibrium regimes are
the positive-logistic slice and the neutral mass-constrained slice; mixed
boundary slices make all four implications vacuous for elementary sign
reasons. -/
theorem intervalDomainM_Theorem_2_2_Eventual_unconditional
    (p : CM2Params)
    (C : Paper3Constants intervalDomainM p)
    (hC : Paper3ConstantsUsesCriticalSpectrum
      unitIntervalNeumannSpectrum p C) :
    Theorem_2_2_EventualExponentialStability
      intervalDomainM p unitIntervalNeumannSpectrum
        intervalDomainMSectorialStabilityNorms C := by
  by_cases hpos : 0 < p.a ∧ 0 < p.b
  · exact intervalDomainM_Theorem_2_2_Eventual_positiveLogistic_unconditional
      p hpos.1 hpos.2 C hC
  by_cases hzero : p.a = 0 ∧ p.b = 0
  · exact intervalDomainM_Theorem_2_2_Eventual_minimal_unconditional
      p hzero.1 hzero.2 C hC
  refine Theorem_2_2_EventualExponentialStability.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    exact False.elim (hpos ⟨ha, hb⟩)
  · intro ha hb
    exact False.elim (hpos ⟨ha, hb⟩)
  · intro ha0 hb0
    exact False.elim (hzero ⟨ha0, hb0⟩)
  · intro ha0 hb0
    exact False.elim (hzero ⟨ha0, hb0⟩)

/-- Concrete, non-vacuous unit-interval instantiation of the complete
faithful general-`m` eventual Theorem 2.2.  The only hypotheses are the
parameter pack and the three constant parameters of the concrete spectral
formulas: no `p.m = 1`, no smallness, no carried analytic side conditions. -/
theorem intervalDomainM_Theorem_2_2_Eventual_concrete_unconditional
    (p : CM2Params) (M0 uBar vLower : ℝ) :
    Theorem_2_2_EventualExponentialStability
      intervalDomainM p unitIntervalNeumannSpectrum
        intervalDomainMSectorialStabilityNorms
        (intervalDomainMSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomainM_Theorem_2_2_Eventual_unconditional p
    (intervalDomainMSectorialPaper3Constants p M0 uBar vLower)
    (intervalDomainMSectorialPaper3Constants_usesCriticalSpectrum
      p M0 uBar vLower)

#print axioms
  intervalDomainM_minimal_hasEquilibriumMassOnPositiveTimes_of_trace
#print axioms
  intervalDomainM_minimal_eventualC1_of_X2Sigma_restart_of_massGap
#print axioms
  intervalDomainM_eventualMassConstrainedLocallyExponentiallyStableFromSup_unconditional
#print axioms
  intervalDomainM_Theorem_2_2_minimalEventual_branch_unconditional
#print axioms
  intervalDomainM_Theorem_2_2_Eventual_minimal_unconditional
#print axioms intervalDomainM_Theorem_2_2_Eventual_unconditional
#print axioms intervalDomainM_Theorem_2_2_Eventual_concrete_unconditional

end

end ShenWork.Paper3
