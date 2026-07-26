import ShenWork.Paper3.IntervalDomainMMinimalSignalEnergy
import ShenWork.Paper3.IntervalDomainMMinimalEntropyGlobal

/-!
# M-native χ₀>0 minimal2 branch of faithful eventual Theorem 2.5 (`1 ≤ m < 2`)

Assembly of the general-`m` minimal2 disjunct on the faithful `u^m`-flux
domain (`γ = 1`).  The signal-energy chain produces arbitrarily late
supremum-close slices (`intervalDomainM_minimal2_exists_late_supClose`); the
recurrence-variant general-`m` mass-constrained bootstrap
(`intervalDomainM_minimal_eventualC1_of_lateSupClose_of_massGap`) upgrades a
single such slice to eventual exponential `C¹` convergence; the general-`m`
minimal linear-stability threshold (`minimalEquilibriumLinStabThresholdM`)
supplies the spectral gap.  The file closes with the full two-disjunct
general-`m` capstone combining the minimal1 (entropy) and minimal2
(signal-energy) branches.
-/

open Filter MeasureTheory Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.PDE.SectorialOperator

namespace ShenWork.Paper3

noncomputable section

/-- The full general-`m` minimal2 sensitivity threshold: the minimum of the
general-`m` linear-stability threshold and the general-`m` signal-energy
threshold.  Mirrors `chiMinimal1FormulaM`. -/
def chiMinimal2FullFormulaM (p : CM2Params) (uStar uBar vLower : ℝ) : ℝ :=
  min (minimalEquilibriumLinStabThresholdM p uStar)
    (chiMinimal2FormulaM p uBar vLower)

/-- The second minimal formula branch, evaluated at the canonical M-native
constants: the signal-energy chain produces one late basin-entry slice, and
the general-`m` mass-constrained bootstrap then gives eventual exponential
`C¹` convergence (`1 ≤ m < 2`, `γ = 1`). -/
theorem intervalDomainM_minimal2_eventualC1
    (p : CM2Params) (hN : p.N = 1)
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hgamma : p.γ = 1) (hbeta : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
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
  have heq : Paper3ConstantEquilibrium p eq.1 eq.2 := by
    simpa [eq] using paper3ConstantEquilibrium_minimal p ha0 hb0 uStar huStar
  -- Linear stability at general `m` via the firstNonzero-lower critical bound.
  have hstable : LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
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
  have hbox := intervalDomainMMinimalEventualBoxConstants_spec
    p hm ha0 hb0 hbeta hchi huStar
  change IntervalDomainMMinimalEventualBox p uStar uBar vLower at hbox
  obtain ⟨huBar, hvLower, hboxes⟩ := hbox
  obtain ⟨hupper, hfloor⟩ := hboxes u v huv hmass
  refine intervalDomainM_minimal_eventualC1_of_lateSupClose_of_massGap
    p ha0 hb0 heq hgap huv hmass ?_
  intro eps heps
  exact intervalDomainM_minimal2_exists_late_supClose
    p hm.1 ha0 hb0 hgamma hbeta heq huBar hvLower.le hchi hχ2
      huv hmass hupper hfloor (T := (1 : ℝ)) heps

/-- Unconditional second minimal-formula branch of the faithful eventual
Theorem 2.5 on the general-`m` unit-interval equation (`1 ≤ m < 2`, `γ = 1`,
`χ₀ > 0`, `a = b = 0`).  No `p.m = 1` hypothesis. -/
theorem intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal2M
    (p : CM2Params) (hN : p.N = 1)
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hgamma : p.γ = 1) (hbeta : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hchi : 0 < p.χ₀)
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
    exact intervalDomainM_minimal2_eventualC1
      p hN hm ha0 hb0 hgamma hbeta huStar hchi hthreshold huv hmass
  refine ⟨?_, hproduce⟩
  intro u v huv hmass
  obtain ⟨C, hC, rate, hrate, t₀, ht₀, hbound⟩ := hproduce u v huv hmass
  exact intervalDomainM_uniformConvergesInSup_of_eventualExponentialC1
    hrate hbound

/-- Minimal2 disjunct of the general-`m` minimal global-stability condition. -/
def MinimalGlobalStabilityFormulaCondition2M
    (p : CM2Params) (uStar uBar vLower : ℝ) : Prop :=
  p.γ = 1 ∧ 0 < p.χ₀ ∧
    p.χ₀ < chiMinimal2FullFormulaM p uStar uBar vLower

/-- **Capstone (minimal2 branch).**  Faithful eventual Theorem 2.5, minimal2
branch, on the general-`m` unit interval (`1 ≤ m < 2`, `γ = 1`). -/
theorem intervalDomainM_Theorem_2_5_minimal2_EventualGlobalStabilityFormula
    (p : CM2Params) (hN : p.N = 1)
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityFormulaCondition2M p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
  intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal2M
    p hN hm ha0 hb0 hcond.1 hbeta huStar hcond.2.1 hcond.2.2

/-- Full general-`m` minimal global-stability formula condition: the minimal1
(entropy) disjunct or the minimal2 (signal-energy, `γ = 1`) disjunct.  Mirrors
the `m = 1` `MinimalGlobalStabilityFormulaCondition`. -/
def MinimalGlobalStabilityFormulaConditionFullM
    (p : CM2Params) (uStar uBar vLower : ℝ) : Prop :=
  MinimalGlobalStabilityFormulaConditionM p uStar uBar vLower ∨
    MinimalGlobalStabilityFormulaCondition2M p uStar uBar vLower

/-- **Capstone (full).**  Faithful eventual Theorem 2.5 on the general-`m`
unit interval (`1 ≤ m < 2`): either minimal disjunct of the full formula
condition yields mass-constrained global sup convergence together with
orbitwise eventual exponential `C¹` convergence. -/
theorem intervalDomainM_Theorem_2_5_EventualGlobalStabilityFormula
    (p : CM2Params) (hN : p.N = 1)
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) {uStar : ℝ} (huStar : 0 < uStar)
    (hcond : MinimalGlobalStabilityFormulaConditionFullM p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2) :
    EventuallyGloballyExponentiallyStableMinimal intervalDomainM p
      intervalDomainMSectorialStabilityNorms
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  rcases hcond with hcond | hcond
  · exact intervalDomainM_Theorem_2_5_minimal1_EventualGlobalStabilityFormula
      p hN hm ha0 hb0 hbeta huStar hcond
  · exact intervalDomainM_Theorem_2_5_minimal2_EventualGlobalStabilityFormula
      p hN hm ha0 hb0 hbeta huStar hcond

#print axioms intervalDomainM_minimal2_eventualC1
#print axioms
  intervalDomainM_eventuallyGloballyExponentiallyStableMinimal_minimal2M
#print axioms
  intervalDomainM_Theorem_2_5_minimal2_EventualGlobalStabilityFormula
#print axioms intervalDomainM_Theorem_2_5_EventualGlobalStabilityFormula

end

end ShenWork.Paper3
