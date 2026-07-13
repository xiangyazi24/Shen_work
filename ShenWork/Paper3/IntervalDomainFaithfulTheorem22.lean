/- Faithful Paper3 Theorem 2.2 assembly for the positive logistic branch. -/
import ShenWork.Paper3.IntervalDomainWeakSupStageB
import ShenWork.PDE.IntervalDomainExistence

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2

noncomputable section

/-- The nonlinear positive-equilibrium branch of the corrected Theorem 2.2.
Its initial topology is the physical sup norm and its `C¹` conclusion is
eventual.  The linear condition is the exact discrete Neumann condition
carried by `Paper3ConstantsUsesCriticalSpectrum`. -/
theorem intervalDomain_Theorem_2_2_positiveEventual_branch
    (p : CM2Params) (hm : p.m = 1)
    (C : Paper3Constants intervalDomain p)
    (hC :
      Paper3ConstantsUsesCriticalSpectrum
        unitIntervalNeumannSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    p.χ₀ < C.chiCritical eq.1 →
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      EventualLocallyExponentiallyStableFromSup
        intervalDomain p intervalDomainSectorialStabilityNorms eq.1 eq.2 := by
  dsimp
  intro hchi
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    hC.positiveEquilibrium_linearlyStable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hchi
  exact ⟨hstable,
    intervalDomain_eventualLocallyExponentiallyStableFromSup
      p hm ha (paper3ConstantEquilibrium_positive p ha hb)
      hstable hexist⟩

/-- The positive stable branch with small-data global existence discharged by
the finite-horizon continuation producer. -/
theorem intervalDomain_Theorem_2_2_positiveEventual_branch_unconditional
    (p : CM2Params) (hm : p.m = 1)
    (C : Paper3Constants intervalDomain p)
    (hC :
      Paper3ConstantsUsesCriticalSpectrum
        unitIntervalNeumannSpectrum p C)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    p.χ₀ < C.chiCritical eq.1 →
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      EventualLocallyExponentiallyStableFromSup
        intervalDomain p intervalDomainSectorialStabilityNorms eq.1 eq.2 := by
  dsimp
  intro hchi
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    hC.positiveEquilibrium_linearlyStable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hchi
  exact ⟨hstable,
    intervalDomain_eventualLocallyExponentiallyStableFromSup_unconditional
      p hm ha (paper3ConstantEquilibrium_positive p ha hb) hstable⟩

/-- Complete faithful Theorem 2.2 on the positive logistic parameter slice.

The positive stable branch uses the proved Stage-B orbit theorem.  The
positive unstable branch is the existing exact discrete spectral theorem.
The two minimal branches are vacuous because `p.a>0`. -/
theorem intervalDomain_Theorem_2_2_Eventual_positiveLogistic
    (p : CM2Params) (hm : p.m = 1)
    (haP : 0 < p.a) (hbP : 0 < p.b)
    (C : Paper3Constants intervalDomain p)
    (hC :
      Paper3ConstantsUsesCriticalSpectrum
        unitIntervalNeumannSpectrum p C)
    (hexist :
      ∀ uStar, ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p uStar delta) :
    Theorem_2_2_EventualExponentialStability
      intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms C := by
  refine Theorem_2_2_EventualExponentialStability.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    dsimp
    intro hchi
    have hbranch := intervalDomain_Theorem_2_2_positiveEventual_branch
      p hm C hC ha hb
        (hexist (positiveEquilibrium p ⟨ha, hb⟩).1) hchi
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

/-- Unconditional faithful eventual Theorem 2.2 on the positive logistic
slice.  In particular, this capstone has no `SmallDataGlobalExistence` or
global-solution hypothesis. -/
theorem intervalDomain_Theorem_2_2_Eventual_positiveLogistic_unconditional
    (p : CM2Params) (hm : p.m = 1)
    (haP : 0 < p.a) (hbP : 0 < p.b)
    (C : Paper3Constants intervalDomain p)
    (hC :
      Paper3ConstantsUsesCriticalSpectrum
        unitIntervalNeumannSpectrum p C) :
    Theorem_2_2_EventualExponentialStability
      intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms C := by
  refine Theorem_2_2_EventualExponentialStability.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    dsimp
    intro hchi
    have hbranch :=
      intervalDomain_Theorem_2_2_positiveEventual_branch_unconditional
        p hm C hC ha hb hchi
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

/-- Concrete non-vacuous capstone: the abstract constants package is
instantiated by the unit-interval spectral formulas. -/
theorem
intervalDomain_Theorem_2_2_Eventual_positiveLogistic_concrete_unconditional
    (p : CM2Params) (hm : p.m = 1)
    (haP : 0 < p.a) (hbP : 0 < p.b)
    (M0 uBar vLower : ℝ) :
    Theorem_2_2_EventualExponentialStability
      intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_Eventual_positiveLogistic_unconditional
    p hm haP hbP
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
      (intervalDomainSectorialPaper3Constants_usesCriticalSpectrum
        p M0 uBar vLower)

/-- Global Cauchy existence discharges the only non-stability input in the
faithful positive-logistic Theorem 2.2 assembly. -/
theorem
intervalDomain_Theorem_2_2_Eventual_positiveLogistic_of_globalSolutionExists
    (p : CM2Params) (hm : p.m = 1)
    (haP : 0 < p.a) (hbP : 0 < p.b)
    (C : Paper3Constants intervalDomain p)
    (hC :
      Paper3ConstantsUsesCriticalSpectrum
        unitIntervalNeumannSpectrum p C)
    (hglobal : IntervalDomainGlobalSolutionExists p) :
    Theorem_2_2_EventualExponentialStability
      intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms C := by
  apply intervalDomain_Theorem_2_2_Eventual_positiveLogistic
    p hm haP hbP C hC
  intro _uStar _delta _hdelta u₀ hu₀ _hclose
  exact hglobal.globalSolutionExists u₀ hu₀ (by simp [hm])

#print axioms intervalDomain_Theorem_2_2_positiveEventual_branch
#print axioms
  intervalDomain_Theorem_2_2_positiveEventual_branch_unconditional
#print axioms intervalDomain_Theorem_2_2_Eventual_positiveLogistic
#print axioms
  intervalDomain_Theorem_2_2_Eventual_positiveLogistic_unconditional
#print axioms
  intervalDomain_Theorem_2_2_Eventual_positiveLogistic_concrete_unconditional
#print axioms
  intervalDomain_Theorem_2_2_Eventual_positiveLogistic_of_globalSolutionExists

end

end ShenWork.Paper3
