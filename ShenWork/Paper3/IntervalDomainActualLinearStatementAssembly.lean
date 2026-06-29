import ShenWork.Paper3.IntervalDomainStatementAssembly
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearSectorial

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-!
Actual-linear small-sensitivity entry points for the interval-domain Paper3
Theorem 2.1 persistence statement and the interval-domain mainline assembly.

The analytic producer
`intervalDomain_sectorialTheorem21Persistence_actualLinearSmall` already
constructs the concrete persistence package in the `m = 1`, `β ≥ 1`,
small-positive-sensitivity regime.  This file wires that producer through the
statement-level `of_persistence` wrappers, so these endpoints no longer carry
an explicit `IntervalDomainSectorialTheorem21Persistence` input.
-/

/-- Concrete interval-domain Paper3 Theorem 2.1 in the actual-linear
small-sensitivity regime, with the persistence package produced internally. -/
theorem intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_1_of_persistence
    p M0 uBar vLower
    (intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
      (uBar := uBar) ha hb hχ0 hm hβ hχ)

/-- Concrete interval-domain Paper3 Theorem 2.1 and its four named parts in the
actual-linear small-sensitivity regime. -/
theorem intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    IntervalDomainPaper3Theorem21PartTargets p M0 uBar vLower :=
  intervalDomain_paper3_Theorem_2_1_partTargets_of_persistence
    p M0 uBar vLower
    (intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
      (uBar := uBar) ha hb hχ0 hm hβ hχ)

/-- Sectorial-constant interval-domain Paper3 Theorem 2.1 in the actual-linear
small-sensitivity regime. -/
theorem intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_1_sectorial_of_persistence
    p M0 uBar vLower
    (intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
      (uBar := uBar) ha hb hχ0 hm hβ hχ)

/-! ### A-priori mainline route with actual-linear persistence -/

/-- Sectorial mainline facts for the actual-linear small-sensitivity regime.

Compared with `IntervalDomainSectorialMainlineAprioriFacts`, this package no
longer carries pointwise persistence frontiers: the four raw persistence fields
are produced by `intervalDomain_sectorialTheorem21Persistence_actualLinearSmall`.
-/
structure IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts
    (p : CM2Params) where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingRouteResiduals p

/-- The mass/Lp/smoothing a-priori bound used by the actual-linear-small
mainline route. -/
def IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.aprioriBound
    {p : CM2Params}
    (h : IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.massLpSmoothing.aprioriBound

/-- The actual-linear-small a-priori route supplies the interval-domain global
solution package used by the small-data Cauchy fields. -/
def
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.to_globalSolutionExists
    {p : CM2Params}
    (h : IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p) :
    IntervalDomainGlobalSolutionExists p :=
  intervalDomainGlobalSolutionExists_of_standardContinuation_gluing_and_massLpSmoothing
    p h.continuation h.aprioriBound

/-- Construct the canonical sectorial core package in the actual-linear
small-sensitivity regime. -/
def IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts.to_coreExistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    IntervalDomainSectorialMainlineCoreExistence p uBar :=
  let hpersist : IntervalDomainSectorialTheorem21Persistence p uBar :=
    intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
      (uBar := uBar) ha hb hχ0 hm hβ hχ
  { spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
    smallDataGlobal :=
      intervalDomain_smallDataGlobal_of_globalSolutionExists
        p h.to_globalSolutionExists (by simp [hm])
    massConstrainedSmallDataGlobal :=
      intervalDomain_massConstrainedSmallDataGlobal_of_globalSolutionExists
        p h.to_globalSolutionExists (by simp [hm])
    persistencePart1 := hpersist.part1
    persistencePart2 := hpersist.part2
    persistencePart3 := hpersist.part3
    persistencePart4 := hpersist.part4 }

/-- Sectorial mainline target from a-priori global-existence facts and the
proved actual-linear-small persistence producer. -/
theorem
    intervalDomain_sectorialMainline_unconditionalTarget_of_aprioriActualLinearSmallFacts
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hfacts : IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
    p M0 uBar vLower
    (hfacts.to_coreExistence ha hb hχ0 hm hβ hχ)

/-- Concrete interval-domain Paper3 mainline frontiers in the actual-linear
small-sensitivity regime.  The persistence inputs are produced internally from
the parameter hypotheses. -/
structure IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline in the
actual-linear small-sensitivity regime, without carrying pointwise persistence
frontiers. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_frontierData
    p M0 uBar vLower K
    { core := hData.core.to_coreExistence ha hb hχ0 hm hβ hχ
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline in the
actual-linear small-sensitivity regime. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers in the actual-linear
small-sensitivity regime, with the mainline persistence fields produced
internally. -/
structure IntervalDomainPaper3StatementAprioriActualLinearSmallFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target in the
actual-linear small-sensitivity regime. -/
theorem
    intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementAprioriActualLinearSmallFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target in the
actual-linear small-sensitivity regime. -/
theorem
    intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementAprioriActualLinearSmallFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallFrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

end

end ShenWork.Paper3

namespace ShenWork.Paper3

#print axioms
  intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall
#print axioms
  intervalDomain_paper3_Theorem_2_1_partTargets_of_actualLinearSmall
#print axioms
  intervalDomain_paper3_Theorem_2_1_sectorial_of_actualLinearSmall
#print axioms
  intervalDomain_sectorialMainline_unconditionalTarget_of_aprioriActualLinearSmallFacts
#print axioms
  intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallFrontierData

end ShenWork.Paper3
