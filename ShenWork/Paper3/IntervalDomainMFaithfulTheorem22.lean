/- Faithful general-`m` Paper3 Theorem 2.2 assembly for the positive
logistic branch on `intervalDomainM`.  No `p.m = 1` hypothesis appears. -/
import ShenWork.Paper3.IntervalDomainMWeakSupStageB

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

/-- The positive stable branch of the faithful general-`m` Theorem 2.2 with
small-data global existence discharged by the all-exponent continuation
producer. -/
theorem intervalDomainM_Theorem_2_2_positiveEventual_branch_unconditional
    (p : CM2Params)
    (C : Paper3Constants intervalDomainM p)
    (hC :
      Paper3ConstantsUsesCriticalSpectrum
        unitIntervalNeumannSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    p.χ₀ < C.chiCritical eq.1 →
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      EventualLocallyExponentiallyStableFromSup
        intervalDomainM p intervalDomainMSectorialStabilityNorms eq.1 eq.2 := by
  dsimp
  intro hchi
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    hC.positiveEquilibrium_linearlyStable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hchi
  exact ⟨hstable,
    intervalDomainM_eventualLocallyExponentiallyStableFromSup_unconditional
      p ha (paper3ConstantEquilibrium_positive p ha hb) hstable⟩

/-- Complete faithful general-`m` eventual Theorem 2.2 on the positive
logistic parameter slice.  The two minimal branches are vacuous because
`p.a > 0`. -/
theorem intervalDomainM_Theorem_2_2_Eventual_positiveLogistic_unconditional
    (p : CM2Params)
    (haP : 0 < p.a) (hbP : 0 < p.b)
    (C : Paper3Constants intervalDomainM p)
    (hC :
      Paper3ConstantsUsesCriticalSpectrum
        unitIntervalNeumannSpectrum p C) :
    Theorem_2_2_EventualExponentialStability
      intervalDomainM p unitIntervalNeumannSpectrum
        intervalDomainMSectorialStabilityNorms C := by
  refine Theorem_2_2_EventualExponentialStability.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    dsimp
    intro hchi
    have hbranch :=
      intervalDomainM_Theorem_2_2_positiveEventual_branch_unconditional
        p C hC ha hb hchi
    rcases hbranch with
      ⟨hstable, delta, hdelta, A, hA, rate, hrate, t₀, ht₀, hmain⟩
    exact
      ⟨hstable, delta, hdelta, A, hA, rate, hrate, t₀, ht₀, hmain⟩
  · intro ha hb
    dsimp
    intro hchi
    exact hC.positiveEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hchi
  · intro _ha0 hb0
    exact False.elim ((ne_of_gt hbP) hb0)
  · intro ha0 _hb0
    exact False.elim ((ne_of_gt haP) ha0)

/-- Concrete non-vacuous capstone on the positive logistic slice: the abstract
constants package is instantiated by the unit-interval spectral formulas over
the faithful general-`m` model. -/
theorem
intervalDomainM_Theorem_2_2_Eventual_positiveLogistic_concrete_unconditional
    (p : CM2Params)
    (haP : 0 < p.a) (hbP : 0 < p.b)
    (M0 uBar vLower : ℝ) :
    Theorem_2_2_EventualExponentialStability
      intervalDomainM p unitIntervalNeumannSpectrum
        intervalDomainMSectorialStabilityNorms
        (intervalDomainMSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomainM_Theorem_2_2_Eventual_positiveLogistic_unconditional
    p haP hbP
      (intervalDomainMSectorialPaper3Constants p M0 uBar vLower)
      (intervalDomainMSectorialPaper3Constants_usesCriticalSpectrum
        p M0 uBar vLower)

#print axioms intervalDomainM_Theorem_2_2_positiveEventual_branch_unconditional
#print axioms intervalDomainM_Theorem_2_2_Eventual_positiveLogistic_unconditional
#print axioms
  intervalDomainM_Theorem_2_2_Eventual_positiveLogistic_concrete_unconditional

end

end ShenWork.Paper3
