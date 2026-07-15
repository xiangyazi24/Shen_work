import ShenWork.Paper3.IntervalDomainMinimalSmallDataGlobalExistence
import ShenWork.Paper3.IntervalDomainMinimalEventualConvergenceUpgrade
import ShenWork.Paper3.IntervalDomainFaithfulTheorem22

/-!
# Faithful Paper 3 Theorem 2.2 on the minimal mass hyperplane

This file closes the neutral minimal branch and then joins it with the already
proved positive-logistic branch.  The nonlinear conclusion is the faithful
positive-time `C1` estimate recorded by
`Theorem_2_2_EventualExponentialStability`.
-/

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- The datum mass and the exact minimal-model mass ODE give the physical
positive-time mass interface on a constructed global solution. -/
theorem intervalDomain_minimal_hasEquilibriumMassOnPositiveTimes_of_trace
    (p : CM2Params) {uStar : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hmass₀ : intervalDomain.integral u₀ = intervalDomain.volume * uStar) :
    HasEquilibriumMassOnPositiveTimes intervalDomain u uStar := by
  intro t ht0
  let H : ℝ := t + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  rw [intervalDomain_minimal_mass_eq_initial_before
    p hm ha0 hb0 hu₀ (hglobal H hH) htrace ht0 htH, hmass₀]

/-- A strong mass-constrained restart at one positive time already contains
the whole eventual physical `C1` conclusion. -/
theorem intervalDomain_minimal_eventualC1_of_X2Sigma_restart_of_massGap
    (p : CM2Params) (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar gap : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    {tau : ℝ} (htau : 0 < tau)
    (hrestart :
      let sigma : ℝ := 7 / 8
      intervalDomainX2SigmaDistance sigma uStar (u tau) ≤
        intervalDomainStrongBootstrapRadius
          p sigma uStar vStar gap heq / 2) :
    let sigma : ℝ := 7 / 8
    let R := intervalDomainStrongBootstrapRadius
      p sigma uStar vStar gap heq
    let rate := gap / 4
    let Cu := intervalDomainX2SigmaValueTrace sigma +
      intervalDomainX2SigmaDerivativeTrace sigma
    let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
      intervalDomainX2SigmaC1Envelope sigma
    let C := (1 + Cu + Cv) * R * Real.exp (rate * tau)
    EventualExponentialC1ConvergenceWith
      intervalDomain intervalDomainSectorialStabilityNorms
        u v uStar vStar C rate tau := by
  dsimp only
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  change intervalDomainX2SigmaDistance sigma uStar (u tau) ≤
    intervalDomainStrongBootstrapRadius
      p sigma uStar vStar gap heq / 2 at hrestart
  let R : ℝ := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  let rate : ℝ := gap / 4
  let t₀ : ℝ := tau
  let Cu : ℝ := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv : ℝ := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C : ℝ := (1 + Cu + Cv) * R * Real.exp (rate * t₀)
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
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
  have hdecay := intervalDomainMassX2SigmaDistance_restart_exponential_bound
    hglobal hm ha0 hb0 htau heq hgap hsigmaStrong hsigma1 hmass hrestart
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
    intervalDomainX2SigmaPerturbation_of_classical_positive
      hsol htmem hsigma1.le
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol
  have hcont : Continuous (u t) :=
    ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM htmem
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
      intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar :=
    hdistR.trans (intervalDomainStrongBootstrapRadius_le_positivity
      p sigma uStar vStar gap heq)
  have huC1 := Hreal.c1Distance_le
  have hvC1 := intervalDomainSignal_c1Distance_le_X2Sigma
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

/-- Fully discharged faithful Stage B for the neutral minimal equilibrium.
The small-data global orbit and its physical mass are constructed internally. -/
theorem
intervalDomain_eventualMassConstrainedLocallyExponentiallyStableFromSup_unconditional
    (p : CM2Params) (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    EventualMassConstrainedLocallyExponentiallyStableFromSup
      intervalDomain p intervalDomainSectorialStabilityNorms
        uStar vStar := by
  obtain ⟨gap, hgap0, hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
  obtain ⟨deltaGlobal, hdeltaGlobal, hglobalExistence⟩ :=
    intervalDomain_massConstrainedSmallDataGlobalExistence_of_linearlyStable
      p hm ha0 hb0 heq hstable
  let sigma : ℝ := 7 / 8
  have hsigmaStrong : 3 / 4 < sigma := by norm_num [sigma]
  have hsigma1 : sigma < 1 := by norm_num [sigma]
  obtain ⟨deltaEntry, hdeltaEntry, T, hT, hentry⟩ :=
    intervalDomainMassSupToStrongBasinEntry_proved
      p hsigmaStrong hsigma1 hm ha0 hb0 heq hgap
  let delta := min deltaGlobal deltaEntry
  have hdelta : 0 < delta := lt_min hdeltaGlobal hdeltaEntry
  let R := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  let rate := gap / 4
  let Cu := intervalDomainX2SigmaValueTrace sigma +
    intervalDomainX2SigmaDerivativeTrace sigma
  let Cv := 4 * paper3UniformSignalStrongConstant p uStar heq.u_pos *
    intervalDomainX2SigmaC1Envelope sigma
  let C := (1 + Cu + Cv) * R * Real.exp (rate * T)
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
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
      intervalDomain u₀ uStar deltaGlobal :=
    lt_of_lt_of_le hclose.lt (by dsimp [delta]; exact min_le_left _ _)
  have hcloseEntry : SupCloseToConstant
      intervalDomain u₀ uStar deltaEntry :=
    lt_of_lt_of_le hclose.lt (by dsimp [delta]; exact min_le_right _ _)
  obtain ⟨u, v, hglobal, htrace⟩ :=
    hglobalExistence u₀ hu₀ hcloseGlobal hmass₀
  have hmass :=
    intervalDomain_minimal_hasEquilibriumMassOnPositiveTimes_of_trace
      p hm ha0 hb0 hu₀ hglobal htrace hmass₀
  have hrestart :=
    hentry u₀ hu₀ hcloseEntry u v hglobal htrace hmass
  refine ⟨u, v, hglobal, htrace, ?_⟩
  simpa [sigma, R, rate, Cu, Cv, C] using
    intervalDomain_minimal_eventualC1_of_X2Sigma_restart_of_massGap
      p hm ha0 hb0 heq hgap hglobal hmass hT hrestart.2

/-- Complete faithful stable branch at a neutral mass-parametrized
equilibrium.  Both the spectral statement and the nonlinear global orbit are
constructed from the strict critical-sensitivity inequality. -/
theorem intervalDomain_Theorem_2_2_minimalEventual_branch_unconditional
    (p : CM2Params) (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum
      unitIntervalNeumannSpectrum p C)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : p.χ₀ < C.chiCritical uStar) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      EventualMassConstrainedLocallyExponentiallyStableFromSup
        intervalDomain p intervalDomainSectorialStabilityNorms eq.1 eq.2 := by
  dsimp
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p
      (minimalEquilibrium p uStar).1 (minimalEquilibrium p uStar).2 :=
    hC.minimalEquilibrium_linearlyStable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hchi
  exact ⟨hstable,
    intervalDomain_eventualMassConstrainedLocallyExponentiallyStableFromSup_unconditional
      p hm ha0 hb0
        (paper3ConstantEquilibrium_minimal p ha0 hb0 uStar huStar) hstable⟩

/-- Faithful eventual Theorem 2.2 on the neutral minimal parameter slice. -/
theorem intervalDomain_Theorem_2_2_Eventual_minimal_unconditional
    (p : CM2Params) (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum
      unitIntervalNeumannSpectrum p C) :
    Theorem_2_2_EventualExponentialStability
      intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms C := by
  refine Theorem_2_2_EventualExponentialStability.of_parts ?_ ?_ ?_ ?_
  · intro ha _hb
    exact False.elim ((ne_of_gt ha) ha0)
  · intro ha _hb
    exact False.elim ((ne_of_gt ha) ha0)
  · intro _ha0 _hb0 uStar huStar
    dsimp
    intro hchi
    exact intervalDomain_Theorem_2_2_minimalEventual_branch_unconditional
      p hm ha0 hb0 C hC huStar hchi
  · intro _ha0 _hb0 uStar huStar
    dsimp
    intro hchi
    exact hC.minimalEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hchi

/-- Unconditional faithful eventual Theorem 2.2 for every admissible parameter
tuple.  The only two nonempty equilibrium regimes are the positive-logistic
slice and the neutral mass-constrained slice; mixed boundary slices make all
four implications vacuous for elementary sign reasons. -/
theorem intervalDomain_Theorem_2_2_Eventual_unconditional
    (p : CM2Params) (hm : p.m = 1)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum
      unitIntervalNeumannSpectrum p C) :
    Theorem_2_2_EventualExponentialStability
      intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms C := by
  by_cases hpos : 0 < p.a ∧ 0 < p.b
  · exact intervalDomain_Theorem_2_2_Eventual_positiveLogistic_unconditional
      p hm hpos.1 hpos.2 C hC
  by_cases hzero : p.a = 0 ∧ p.b = 0
  · exact intervalDomain_Theorem_2_2_Eventual_minimal_unconditional
      p hm hzero.1 hzero.2 C hC
  refine Theorem_2_2_EventualExponentialStability.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    exact False.elim (hpos ⟨ha, hb⟩)
  · intro ha hb
    exact False.elim (hpos ⟨ha, hb⟩)
  · intro ha0 hb0
    exact False.elim (hzero ⟨ha0, hb0⟩)
  · intro ha0 hb0
    exact False.elim (hzero ⟨ha0, hb0⟩)

/-- Concrete, non-vacuous unit-interval instantiation of the complete faithful
eventual Theorem 2.2. -/
theorem intervalDomain_Theorem_2_2_Eventual_concrete_unconditional
    (p : CM2Params) (hm : p.m = 1) (M0 uBar vLower : ℝ) :
    Theorem_2_2_EventualExponentialStability
      intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_Eventual_unconditional p hm
    (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
    (intervalDomainSectorialPaper3Constants_usesCriticalSpectrum
      p M0 uBar vLower)

#print axioms
  intervalDomain_minimal_hasEquilibriumMassOnPositiveTimes_of_trace
#print axioms
  intervalDomain_minimal_eventualC1_of_X2Sigma_restart_of_massGap
#print axioms
  intervalDomain_eventualMassConstrainedLocallyExponentiallyStableFromSup_unconditional
#print axioms
  intervalDomain_Theorem_2_2_minimalEventual_branch_unconditional
#print axioms
  intervalDomain_Theorem_2_2_Eventual_minimal_unconditional
#print axioms intervalDomain_Theorem_2_2_Eventual_unconditional
#print axioms intervalDomain_Theorem_2_2_Eventual_concrete_unconditional

end

end ShenWork.Paper3
