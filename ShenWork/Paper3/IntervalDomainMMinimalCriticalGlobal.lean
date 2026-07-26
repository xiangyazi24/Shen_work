import ShenWork.Paper3.IntervalDomainMMinimalCriticalBox
import ShenWork.Paper3.IntervalDomainMMinimalSignalEnergyGlobal

/-!
# M-native minimal-equilibrium Theorem 2.5 at `m = 2`

The critical eventual box supplies the only input that is not already covered
by the general-`m` downstream theory.  Both the entropy (minimal1) and
signal-energy (minimal2) basin-entry chains require only `1 ≤ m`, so they apply
at `m = 2` without alteration.
-/

open Filter MeasureTheory Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.PDE.SectorialOperator

namespace ShenWork.Paper3

noncomputable section

/-- Critical `m = 2` minimal1 branch: the entropy recurrence chain consumes
the critical canonical eventual box. -/
theorem
    intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal1_critical
    (p : CM2Params) (_hN : p.N = 1)
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
    (hadm : CriticalMinimalLpAdmissibility p uStar)
    (hthreshold : p.χ₀ < chiMinimal1FormulaM p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  let eq := minimalEquilibrium p uStar
  let uBar := (intervalDomainMMinimalEventualBoxConstants p uStar).1
  let vLower := (intervalDomainMMinimalEventualBoxConstants p uStar).2
  have hmLe : 1 ≤ p.m := by
    rw [hm]
    norm_num
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using
      paper3ConstantEquilibrium_minimal p ha0 hb0 uStar huStar
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    have hcrit : p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      lt_of_lt_of_le
        (lt_of_lt_of_le hthreshold (min_le_left _ _))
        (paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
          unitIntervalNeumannSpectrum p
          unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar)
    simpa [eq] using
      minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hcrit
  obtain ⟨gap, _hgapPos, hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
  have hχent :
      p.χ₀ < chiMinimal1EntropyThresholdM p uStar uBar vLower :=
    lt_of_lt_of_le hthreshold (min_le_right _ _)
  have hbox :=
    intervalDomainMMinimalEventualBoxConstants_critical_spec
      p hm ha0 hb0 hbeta hchi huStar hadm
  change IntervalDomainMMinimalEventualBox p uStar uBar vLower at hbox
  obtain ⟨huBar, hvLower, hboxes⟩ := hbox
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
      HasEquilibriumMassOnPositiveTimes intervalDomainM u eq.1 →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith
          intervalDomainM intervalDomainMSectorialStabilityNorms
            u v eq.1 eq.2 C rate t₀ := by
    intro u v huv hmass
    obtain ⟨hupper, hfloor⟩ := hboxes u v huv hmass
    refine
      intervalDomainM_minimal_eventualC1_of_lateSupClose_of_massGap
        p ha0 hb0 heq hgap huv hmass ?_
    intro eps heps
    exact intervalDomainM_minimal1_exists_late_supClose
      p hmLe hb0 heq huBar hvLower.le hchi hχent
        huv hmass hupper hfloor (T := (1 : ℝ)) heps
  refine ⟨?_, hproduce⟩
  intro u v huv hmass
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ :=
    hproduce u v huv hmass
  exact intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

/-- Critical `m = 2` minimal1 formula capstone. -/
theorem
    intervalDomainM_Theorem_2_5_minimal1_critical_EventualGlobalStabilityFormula
    (p : CM2Params) (hN : p.N = 1)
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hadm : CriticalMinimalLpAdmissibility p uStar)
    (hcond : MinimalGlobalStabilityFormulaConditionM p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
  intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal1_critical
    p hN hm ha0 hb0 hbeta huStar hcond.1 hadm hcond.2

/-- Critical `m = 2` minimal2 branch for one orbit.  The signal-energy chain
uses only `1 ≤ m`; critical admissibility is used to obtain its eventual box. -/
theorem intervalDomainM_minimal2_critical_eventualC1
    (p : CM2Params) (_hN : p.N = 1)
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hgamma : p.γ = 1) (hbeta : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
    (hadm : CriticalMinimalLpAdmissibility p uStar)
    (hthreshold : p.χ₀ < chiMinimal2FullFormulaM p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar) :
    ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
      EventualExponentialC1ConvergenceWith
        intervalDomainM intervalDomainMSectorialStabilityNorms u v
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 C rate t₀ := by
  let eq := minimalEquilibrium p uStar
  let uBar := (intervalDomainMMinimalEventualBoxConstants p uStar).1
  let vLower := (intervalDomainMMinimalEventualBoxConstants p uStar).2
  have hmLe : 1 ≤ p.m := by
    rw [hm]
    norm_num
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using
      paper3ConstantEquilibrium_minimal p ha0 hb0 uStar huStar
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
    have hcrit : p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      lt_of_lt_of_le
        (lt_of_lt_of_le hthreshold (min_le_left _ _))
        (paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
          unitIntervalNeumannSpectrum p
          unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar)
    simpa [eq] using
      minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
        unitIntervalNeumannSpectrum p
        unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hcrit
  obtain ⟨gap, _hgapPos, hgap⟩ :=
    unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable
  have hχ2 : p.χ₀ < chiMinimal2FormulaM p uBar vLower :=
    lt_of_lt_of_le hthreshold (min_le_right _ _)
  have hbox :=
    intervalDomainMMinimalEventualBoxConstants_critical_spec
      p hm ha0 hb0 hbeta hchi huStar hadm
  change IntervalDomainMMinimalEventualBox p uStar uBar vLower at hbox
  obtain ⟨huBar, hvLower, hboxes⟩ := hbox
  obtain ⟨hupper, hfloor⟩ := hboxes u v huv hmass
  refine intervalDomainM_minimal_eventualC1_of_lateSupClose_of_massGap
    p ha0 hb0 heq hgap huv hmass ?_
  intro eps heps
  exact intervalDomainM_minimal2_exists_late_supClose
    p hmLe ha0 hb0 hgamma hbeta heq huBar hvLower.le hchi hχ2
      huv hmass hupper hfloor (T := (1 : ℝ)) heps

/-- Unconditional critical `m = 2` minimal2 branch. -/
theorem
    intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal2_critical
    (p : CM2Params) (hN : p.N = 1)
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hgamma : p.γ = 1) (hbeta : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
    (hadm : CriticalMinimalLpAdmissibility p uStar)
    (hthreshold : p.χ₀ < chiMinimal2FullFormulaM p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  have hproduce : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      PositiveGlobalBoundedSolution intervalDomainM p u v →
      HasEquilibriumMassOnPositiveTimes intervalDomainM u
        (minimalEquilibrium p uStar).1 →
      ∃ C > 0, ∃ rate > 0, ∃ t₀ > 0,
        EventualExponentialC1ConvergenceWith
          intervalDomainM intervalDomainMSectorialStabilityNorms
            u v (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 C rate t₀ := by
    intro u v huv hmass
    exact intervalDomainM_minimal2_critical_eventualC1
      p hN hm ha0 hb0 hgamma hbeta huStar hchi hadm
        hthreshold huv hmass
  refine ⟨?_, hproduce⟩
  intro u v huv hmass
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ :=
    hproduce u v huv hmass
  exact intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

/-- Critical `m = 2` minimal2 formula capstone. -/
theorem
    intervalDomainM_Theorem_2_5_minimal2_critical_EventualGlobalStabilityFormula
    (p : CM2Params) (hN : p.N = 1)
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hadm : CriticalMinimalLpAdmissibility p uStar)
    (hcond : MinimalGlobalStabilityFormulaCondition2M p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
  intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal2_critical
    p hN hm ha0 hb0 hcond.1 hbeta huStar hcond.2.1
      hadm hcond.2.2

/-- **Critical capstone.**  At `m = 2`, the parameter-only strict
admissibility condition supplies the eventual box; either existing minimal
formula disjunct then yields mass-constrained global convergence and orbitwise
eventual exponential `C¹` convergence. -/
theorem intervalDomainM_Theorem_2_5_critical_EventualGlobalStabilityFormula
    (p : CM2Params) (hN : p.N = 1)
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hadm : CriticalMinimalLpAdmissibility p uStar)
    (hcond : MinimalGlobalStabilityFormulaConditionFullM p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  rcases hcond with hcond | hcond
  · exact
      intervalDomainM_Theorem_2_5_minimal1_critical_EventualGlobalStabilityFormula
        p hN hm ha0 hb0 hbeta huStar hadm hcond
  · exact
      intervalDomainM_Theorem_2_5_minimal2_critical_EventualGlobalStabilityFormula
        p hN hm ha0 hb0 hbeta huStar hadm hcond

#print axioms
  intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal1_critical
#print axioms
  intervalDomainM_Theorem_2_5_minimal1_critical_EventualGlobalStabilityFormula
#print axioms intervalDomainM_minimal2_critical_eventualC1
#print axioms
  intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal2_critical
#print axioms
  intervalDomainM_Theorem_2_5_minimal2_critical_EventualGlobalStabilityFormula
#print axioms
  intervalDomainM_Theorem_2_5_critical_EventualGlobalStabilityFormula

end

end ShenWork.Paper3
