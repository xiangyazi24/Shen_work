import ShenWork.Paper3.IntervalDomainStatementAssembly
import ShenWork.Paper3.IntervalDomainMoserLadderHeadline
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearSectorial
import ShenWork.PDE.P3MoserLemmaDischarge

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.Paper2.IntervalDomainMoserClosure
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

/-! ### Moser-ladder route with actual-linear persistence -/

/-- Moser-ladder mass/Lp/smoothing residuals for the actual-linear-small
regime.  The parameter-side fields `a_pos` and `chi_nonneg` are supplied by the
actual-linear-small wrapper hypotheses. -/
structure IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals
    (p : CM2Params) where
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

/-- Build the generic Moser-ladder residual package from the actual-linear
small-sensitivity parameter hypotheses. -/
def IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals.to_moserLadder
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingMoserLadderResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  moserDissipation := h.moserDissipation
  relativeMoserInterpolation := h.relativeMoserInterpolation
  quantitativeEndpoint := h.quantitativeEndpoint

/-! ### Closed-energy seed variant -/

/-- Moser-ladder mass/Lp/smoothing residuals with the L² seed field replaced
by the closed integrated energy identity package.  The conversion to
`IntervalDomainL2SeedRegularityFrontier` is proved in
`P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData`. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals
    (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  closedEnergyTrace :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        Nonempty
          (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u)
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

/- Convert the closed-energy seed variant back to the current actual-linear
Moser residual surface. -/
namespace IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals

def to_actualLinearSmallResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals p where
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  moserDissipation := h.moserDissipation
  relativeMoserInterpolation := h.relativeMoserInterpolation
  quantitativeEndpoint := h.quantitativeEndpoint

end IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals

/-- Sectorial mainline facts with the Paper3 Moser-ladder mass route and the
actual-linear-small persistence producer. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallFacts
    (p : CM2Params) where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals p

/-- Convert the Moser-ladder actual-linear-small facts to the a-priori
actual-linear-small package. -/
def
    IntervalDomainSectorialMainlineMoserActualLinearSmallFacts.to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h : IntervalDomainSectorialMainlineMoserActualLinearSmallFacts p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := (h.massLpSmoothing.to_moserLadder ha hχ0).to_routeResiduals

/-- Sectorial mainline facts with the L² seed supplied as a closed integrated
energy identity. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals p

/- Convert the closed-energy seed sectorial facts to the current Moser
actual-linear-small facts. -/
namespace IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts

def to_moserActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_actualLinearSmallResiduals

end IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts

/-- Construct the canonical sectorial core from Moser-ladder facts and the
proved actual-linear-small persistence producer. -/
def IntervalDomainSectorialMainlineMoserActualLinearSmallFacts.to_coreExistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineMoserActualLinearSmallFacts p)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    IntervalDomainSectorialMainlineCoreExistence p uBar :=
  (h.to_aprioriActualLinearSmallFacts ha hχ0).to_coreExistence
    ha hb hχ0 hm hβ hχ

/-- Sectorial mainline target from Moser-ladder facts and actual-linear-small
persistence. -/
theorem
    intervalDomain_sectorialMainline_unconditionalTarget_of_moserActualLinearSmallFacts
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hfacts : IntervalDomainSectorialMainlineMoserActualLinearSmallFacts p) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
    p M0 uBar vLower
    (hfacts.to_coreExistence ha hb hχ0 hm hβ hχ)

/-- Concrete interval-domain Paper3 mainline frontiers using the Moser-ladder
mass route and the actual-linear-small persistence producer. -/
structure IntervalDomainPaper3MainlineMoserActualLinearSmallFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainSectorialMainlineMoserActualLinearSmallFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from Moser-ladder
facts and the actual-linear-small persistence producer. -/
theorem intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_frontierData
    p M0 uBar vLower K
    { core := hData.core.to_coreExistence ha hb hχ0 hm hβ hχ
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline from Moser-ladder
facts and actual-linear-small persistence. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the Moser-ladder mass
route and the actual-linear-small persistence producer. -/
structure IntervalDomainPaper3StatementMoserActualLinearSmallFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from
Moser-ladder facts and actual-linear-small persistence. -/
theorem intervalDomain_paper3_statementTargets_of_moserActualLinearSmallFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from
Moser-ladder facts and actual-linear-small persistence. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallFrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Moser-ladder route with closed-energy L² seed -/

/-- Concrete interval-domain Paper3 mainline frontiers using the Moser-ladder
mass route, with the L² seed supplied by a closed integrated energy identity. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallClosedEnergyFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the closed-energy
Moser route and the actual-linear-small persistence producer. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallClosedEnergyFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallClosedEnergyFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { core := hData.core.to_moserActualLinearSmallFacts
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline from the
closed-energy Moser route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallClosedEnergyFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallClosedEnergyFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallClosedEnergyFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the closed-energy
Moser mass route and the actual-linear-small persistence producer. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallClosedEnergyFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallClosedEnergyFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
closed-energy Moser route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallClosedEnergyFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallClosedEnergyFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallClosedEnergyFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
closed-energy Moser route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallClosedEnergyFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallClosedEnergyFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallClosedEnergyFrontierData
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
#print axioms
  intervalDomain_sectorialMainline_unconditionalTarget_of_moserActualLinearSmallFacts
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallFrontierData
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallClosedEnergyFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallClosedEnergyFrontierData

end ShenWork.Paper3
