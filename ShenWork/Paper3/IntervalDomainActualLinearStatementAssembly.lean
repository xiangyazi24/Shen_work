import ShenWork.Paper3.IntervalDomainStatementAssembly
import ShenWork.Paper3.IntervalDomainMoserLadderHeadline
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearSectorial
import ShenWork.PDE.P3MoserLemmaDischarge
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.PDE.IntervalDomainMoserLadderAtoms

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2.IntervalDomainEnergyStep
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

/-! ### Raw-linear Theorem 2.2 route with actual-linear persistence -/

/-- Core Paper3 statement data in the actual-linear-small regime, with
Theorem 2.1 persistence produced from the parameter hypotheses and Theorem 2.2
supplied directly by raw linear-stability branches. -/
structure IntervalDomainPaper3CoreStatementActualLinear22Data
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  theorem22Nonminimal :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  theorem22Minimal :
    LinearStabilityInstabilityMinimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical

/-- Convert actual-linear-small raw Theorem 2.2 data into the generic linear
Theorem 2.2 statement package by producing the persistence field internally. -/
def IntervalDomainPaper3CoreStatementActualLinear22Data.to_linear22Data
    {p : CM2Params} {M0 uBar vLower : ℝ}
    (h : IntervalDomainPaper3CoreStatementActualLinear22Data
      p M0 uBar vLower)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    IntervalDomainPaper3CoreStatementLinear22Data p M0 uBar vLower where
  initialContinuity := h.initialContinuity
  persistence :=
    intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
      (uBar := uBar) ha hb hχ0 hm hβ hχ
  theorem22Nonminimal := h.theorem22Nonminimal
  theorem22Minimal := h.theorem22Minimal

/-- Core statement targets in the actual-linear-small regime from raw
linear Theorem 2.2 branches. -/
theorem intervalDomain_paper3_coreStatementTargets_of_actualLinear22Data
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3CoreStatementActualLinear22Data
        p M0 uBar vLower) :
    IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower :=
  intervalDomain_paper3_coreStatementTargets_of_linear22Data
    p M0 uBar vLower
    (hData.to_linear22Data ha hb hχ0 hm hβ hχ)

/-- Instance-facing core statement targets in the actual-linear-small regime
from raw linear Theorem 2.2 branches. -/
theorem intervalDomain_paper3_coreStatementTargets_of_actualLinear22DataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3CoreStatementActualLinear22Data
        p M0 uBar vLower)] :
    IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower :=
  intervalDomain_paper3_coreStatementTargets_of_actualLinear22Data
    p M0 uBar vLower ha hb hχ0 hm hβ hχ hData.out

/-- Paper3 mainline frontiers in the actual-linear-small regime, with
Theorem 2.2 supplied directly by raw linear-stability data. -/
structure IntervalDomainPaper3MainlineActualLinear22FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainPaper3CoreStatementActualLinear22Data
    p M0 uBar vLower
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete Paper3 mainline in the actual-linear-small regime
from raw linear Theorem 2.2 branches. -/
theorem intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineActualLinear22FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_linear22FrontierData
    p M0 uBar vLower K
    { core := hData.core.to_linear22Data ha hb hχ0 hm hβ hχ
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete Paper3 mainline in the actual-linear-small regime
from raw linear Theorem 2.2 branches. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineActualLinear22FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Thin actual-linear raw-Theorem-2.2 route -/

/-- In the actual-linear-small route, the only non-vacuous Theorem 2.3--2.5
stability frontiers are the positive-sensitivity nonminimal Theorem 2.4
branches.  The `χ₀ ≤ 0` Theorem 2.3 branches contradict `0 < χ₀`, and the
minimal Theorem 2.5 branches contradict `0 < a`. -/
structure IntervalDomainPaper3Stability24ActualLinearFrontierData
    (p : CM2Params) (C : Paper3Constants intervalDomain p) : Prop where
  global24 :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
          GloballyAsymptoticallyStableNonminimal intervalDomain p
            eq.1 eq.2
  exp24 :
    0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
              UniformConvergesInSup intervalDomain u eq.1 →
                ExponentialC1ConvergenceWith intervalDomain
                  intervalDomainStabilityNorms u v eq.1 eq.2 A rate

/-- Expand the actual-linear-small Theorem 2.4-only stability frontier to the
current Theorem 2.3--2.5 frontier surface. -/
def IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h : IntervalDomainPaper3Stability24ActualLinearFrontierData p C)
    (ha_pos : 0 < p.a) (hχ_pos : 0 < p.χ₀) :
    IntervalDomainPaper3Stability23To25FrontierData p C where
  globalNonminimal23 := by
    intro hχ_nonpos _hm _ha _hb
    exact False.elim (not_le_of_gt hχ_pos hχ_nonpos)
  globalMinimal23 := by
    intro hχ_nonpos _hm _ha0 _hb0 _uStar _huStar
    exact False.elim (not_le_of_gt hχ_pos hχ_nonpos)
  expNonminimal23 := by
    intro hχ_nonpos _hm _ha _hb
    exact False.elim (not_le_of_gt hχ_pos hχ_nonpos)
  expMinimal23 := by
    intro hχ_nonpos _hm _ha0 _hb0 _uStar _huStar
    exact False.elim (not_le_of_gt hχ_pos hχ_nonpos)
  global24 := h.global24
  exp24 := h.exp24
  global25 := by
    intro ha0 _hb0 _hm _hβ _uStar _huStar
    exact False.elim ((ne_of_gt ha_pos) ha0)
  exp25 := by
    intro ha0 _hb0 _hm _hβ _uStar _huStar
    exact False.elim ((ne_of_gt ha_pos) ha0)

/-- Canonical sup-envelope compactness/regularization data in the
actual-linear-small route after using the shared initial-continuity field and
`0 < a` to make the minimal-upper branch vacuous. -/
structure IntervalDomainPaper3SupNormCompactnessAPosData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  compact : TimeTranslateCompactnessRaw intervalDomain p locallyConverges
  resolvent :
    NeumannResolventGradientBoundExistsRaw intervalDomain
      neumannResolventGradientBound

/-- Convert positive-`a` compactness data into the existing canonical
sup-envelope compactness package. -/
def IntervalDomainPaper3SupNormCompactnessAPosData.toSupNormData
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop}
    {neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop}
    (h : IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound)
    (ha_pos : 0 < p.a)
    (hcont : IntervalDomainInitialContinuityRaw p) :
    IntervalDomainPaper3SupNormCompactnessRegularizationData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound where
  compact := h.compact
  initialContinuity := hcont
  minimalUpper := by
    intro ha0 _hb0 _hm _hβ _hχ0 _hχ _u _v _huv
    exact False.elim ((ne_of_gt ha_pos) ha0)
  resolvent := h.resolvent

/-- Thin actual-linear raw-Theorem-2.2 mainline data.  Persistence is produced
from the actual-linear-small parameter hypotheses, initial continuity is carried
once, the compactness upper-envelope equality is definitional, and the remaining
minimal branches are vacuous from `0 < a`. -/
structure IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  theorem22Nonminimal :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  theorem22Minimal :
    LinearStabilityInstabilityMinimalRaw intervalDomain p
      unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms.c1Distance
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the thin actual-linear data to the current full mainline frontier
surface. -/
def IntervalDomainPaper3MainlineActualLinear22ThinFrontierData.toCurrent
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop}
    {neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop}
    (h : IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound)
    (ha_pos : 0 < p.a) (hχ_pos : 0 < p.χ₀) :
    IntervalDomainPaper3MainlineActualLinear22FrontierData
      p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) where
  core :=
    { initialContinuity := h.initialContinuity
      theorem22Nonminimal := h.theorem22Nonminimal
      theorem22Minimal := h.theorem22Minimal }
  compactness :=
    (h.compactness.toSupNormData ha_pos h.initialContinuity).toConcrete
  stability := h.stability24.toStability23To25 ha_pos hχ_pos

/-- Mainline target from the thin actual-linear raw-Theorem-2.2 route. -/
theorem intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    ha hb hχ0 hm hβ hχ (hData.toCurrent ha hχ0)

/-- Instance-facing mainline target from the thin actual-linear raw-Theorem-2.2
route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData
    p M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-- Full Paper3 statement frontiers in the actual-linear-small regime, with
Theorem 2.2 supplied directly by raw linear-stability data. -/
structure IntervalDomainPaper3StatementActualLinear22FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineActualLinear22FrontierData
      p M0 uBar vLower K

/-- Assemble the full Paper3 statement target in the actual-linear-small
regime from raw linear Theorem 2.2 branches. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementActualLinear22FrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full Paper3 statement target in the actual-linear-small
regime from raw linear Theorem 2.2 branches. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22FrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementActualLinear22FrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_actualLinear22FrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full Paper3 statement frontiers in the actual-linear-small regime, with
Proposition 1.3/1.4 routed through Paper2 main theorem targets and Theorem 2.2
supplied directly by raw linear-stability data. -/
structure IntervalDomainPaper3StatementActualLinear22P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineActualLinear22FrontierData
      p M0 uBar vLower K

/-- Assemble the full Paper3 statement target in the actual-linear-small
regime from raw linear Theorem 2.2 branches and Paper2 main theorem targets. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementActualLinear22P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full Paper3 statement target in the actual-linear-small
regime from raw linear Theorem 2.2 branches and Paper2 main theorem targets. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementActualLinear22P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_actualLinear22P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- In the actual-linear-small regime `0 < χ₀`, the negative-sensitivity
Proposition 1.2 residual is vacuous. -/
theorem intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
    (p : CM2Params) (hχ0 : 0 < p.χ₀) :
    NegativeSensitivityGlobalEventualBound intervalDomain p := by
  intro hχ_nonpos _hm _u₀ _hu₀
  exact False.elim (not_le_of_gt hχ0 hχ_nonpos)

/-- Full Paper3 statement frontiers in the actual-linear-small regime, with the
negative-sensitivity residual discharged from `0 < χ₀` and Proposition 1.3/1.4
routed through supplied Paper2 main theorem targets. -/
structure IntervalDomainPaper3StatementActualLinear22P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineActualLinear22FrontierData
      p M0 uBar vLower K

/-- Assemble the actual-linear raw-Theorem-2.2 statement target from Paper2 main
theorem targets, without carrying a separate negative-sensitivity residual. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementActualLinear22P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_actualLinear22P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing actual-linear raw-Theorem-2.2 statement target from Paper2
main theorem targets, with the negative-sensitivity residual discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_actualLinear22P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementActualLinear22P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_actualLinear22P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full Paper3 statement frontiers in the actual-linear-small regime, with
Proposition 1.3/1.4 routed through Paper2 main theorem targets and the mainline
supplied by the thin raw-Theorem-2.2 route. -/
structure IntervalDomainPaper3StatementActualLinear22ThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the full Paper3 statement target from Paper2 main theorem targets
and the thin actual-linear raw-Theorem-2.2 mainline route. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementActualLinear22ThinP2MainData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
      ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full Paper3 statement target from Paper2 main theorem targets
and the thin actual-linear raw-Theorem-2.2 mainline route. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementActualLinear22ThinP2MainData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-- Full Paper3 statement frontiers in the actual-linear-small regime, with
the negative-sensitivity Proposition 1.2 residual discharged from `0 < χ₀`
and Proposition 1.3/1.4 routed through supplied Paper2 main theorem targets. -/
structure IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the actual-linear-small Paper3 statement target from Paper2 main
theorem targets, without carrying a separate negative-sensitivity residual. -/
theorem intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing actual-linear-small Paper3 statement target from Paper2
main theorem targets, with the negative-sensitivity residual discharged by
`0 < χ₀`. -/
theorem
    intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

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

/-- Full interval-domain Paper3 statement frontiers in the actual-linear-small
regime, using Paper2 main theorem targets for Proposition 1.3/1.4 and
discharging negative sensitivity from `0 < χ₀`. -/
structure IntervalDomainPaper3StatementAprioriActualLinearSmallP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineAprioriActualLinearSmallFrontierData
      p M0 uBar vLower K

/-- A-priori actual-linear-small Paper3 statement target from Paper2 main
theorem targets, with the negative-sensitivity residual discharged by
`0 < χ₀`. -/
theorem
    intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementAprioriActualLinearSmallP2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C
      { negativeBound :=
          intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
            p hχ0
        paper2Main := hData.paper2Main },
    intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing a-priori actual-linear-small Paper3 statement target from
Paper2 main theorem targets, with no separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementAprioriActualLinearSmallP2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegData
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

/-! ### Closed-energy seed plus mass-gradient interpolation variant -/

/-- Closed-energy Moser residuals with the relative interpolation field
replaced by the mass-gradient/lower-order interface that already produces it.

This is still a conditional analytic frontier, but it no longer carries
`RelativeMoserInterpolationBefore` as a black-box field. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals
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
  relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∃ cGrad : ℝ → ℝ,
          (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
          (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
            LpMassGradientInterpolationEstimate intervalDomain
              (pExp + rho) eta Ceta T u) ∧
          (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
            intervalDomain.integral (fun x =>
              (u t x) ^ (pExp + rho - 2) *
                (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad pExp * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
          MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0
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

/- Convert the mass-gradient interpolation variant back to the closed-energy
Moser residual surface. -/
namespace IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals

def to_closedEnergyResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  moserDissipation := h.moserDissipation
  relativeMoserInterpolation := by
    intro T rho p0 u v hsol hcross hboot
    rcases h.relativeMassGradient hsol hcross hboot with
      ⟨cGrad, hcGrad, hMG, hgrad, hmassToLp⟩
    exact
      P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient
        cGrad hcGrad hMG hgrad hmassToLp
  quantitativeEndpoint := h.quantitativeEndpoint

end IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals

/-! ### Closed-energy seed plus raw dissipation and mass-gradient inputs -/

/-- Closed-energy Moser residuals with both the dissipation and relative
interpolation fields replaced by lower-level interfaces. -/
structure IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals
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
  rawMoserDrop :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ∀ pExp, p0 ≤ pExp → ∀ B, 0 ≤ B →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / pExp) *
              deriv (fun τ =>
                intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ pExp)
  relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∃ cGrad : ℝ → ℝ,
          (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
          (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
            LpMassGradientInterpolationEstimate intervalDomain
              (pExp + rho) eta Ceta T u) ∧
          (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
            intervalDomain.integral (fun x =>
              (u t x) ^ (pExp + rho - 2) *
                (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad pExp * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
          MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0
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

namespace IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals

def to_CEGradResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  moserDissipation := by
    intro T rho p0 u v hsol hcross hboot
    exact
      moserDissipationDropBeforeNonnegB_of_raw_drop
        (h.rawMoserDrop hsol hcross hboot)
  relativeMassGradient := h.relativeMassGradient
  quantitativeEndpoint := h.quantitativeEndpoint

end IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals

/-! ### Closed-energy, raw-gradient inputs plus terminal pointwise endpoint -/

/-- The remaining parameter-side boundedness core needed by the terminal
Moser route once the actual-linear theorem wrapper supplies `0 < b` and the
base parameter record supplies `0 < γ`. -/
structure IntervalDomainMoserActualLinearSmallBoundednessCore
    (p : CM2Params) : Prop where
  alphaAbsorption : 2 * p.γ < p.α
  gammaDimension : p.γ * (p.N : ℝ) < 2

namespace IntervalDomainMoserActualLinearSmallBoundednessCore

def to_boundednessHyp
    {p : CM2Params}
    (h : IntervalDomainMoserActualLinearSmallBoundednessCore p)
    (hb : 0 < p.b) :
    IntervalDomainBoundednessHyp p :=
  ⟨Or.inr h.alphaAbsorption, hb, h.alphaAbsorption, p.hγ,
    h.gammaDimension⟩

end IntervalDomainMoserActualLinearSmallBoundednessCore

/-- Closed-energy Moser residuals with the endpoint tower replaced by a direct
terminal pointwise power-control input. -/
structure IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals
    (p : CM2Params) : Prop where
  boundednessCore : IntervalDomainMoserActualLinearSmallBoundednessCore p
  closedEnergyTrace :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        Nonempty
          (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u)
  rawMoserDrop :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ∀ pExp, p0 ≤ pExp → ∀ B, 0 ≤ B →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / pExp) *
              deriv (fun τ =>
                intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ pExp)
  relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∃ cGrad : ℝ → ℝ,
          (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
          (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
            LpMassGradientInterpolationEstimate intervalDomain
              (pExp + rho) eta Ceta T u) ∧
          (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
            intervalDomain.integral (fun x =>
              (u t x) ^ (pExp + rho - 2) *
                (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad pExp * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
          MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0
  terminalPointwise :
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
        ∃ q R, 0 < q ∧ 0 ≤ R ∧
          IntervalDomainMoserPointwisePowerControlBefore u T q R

/-- A terminal pointwise Moser estimate gives the older quantitative endpoint
interface by taking constant exponent and root-bound sequences. -/
theorem intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl
    {p : CM2Params}
    (hterminal :
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
          ∃ q R, 0 < q ∧ 0 ≤ R ∧
            IntervalDomainMoserPointwisePowerControlBefore u T q R)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (pExp : ℝ)
    (hpExp :
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp)
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u) :
    ∃ pSeq rootBound : ℕ → ℝ,
      (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound := by
  rcases hterminal hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨q, R, hq, hR, hpoint⟩
  refine ⟨fun _ => q, fun _ => R, ?_⟩
  intro _hAll
  exact ⟨R, hR, 0, hq, hR, le_rfl, hpoint⟩

namespace IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals

def to_CERawGradResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals
        p)
    (hb : 0 < p.b) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals p where
  boundednessHyp := h.boundednessCore.to_boundednessHyp hb
  closedEnergyTrace := h.closedEnergyTrace
  rawMoserDrop := h.rawMoserDrop
  relativeMassGradient := h.relativeMassGradient
  quantitativeEndpoint := by
    intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
    exact
      intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl
        h.terminalPointwise hu₀ hT hsol htrace pExp hpExp hLp

end IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals

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

/-- Sectorial mainline facts with the L² seed supplied by closed energy and
the relative interpolation supplied by the mass-gradient bridge. -/
structure
    IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals
      p

namespace IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts

def to_closedEnergyFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallClosedEnergyFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_closedEnergyResiduals

end IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts

/-- Sectorial mainline facts with closed-energy seed, raw Moser dissipation,
and mass-gradient relative interpolation inputs. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals p

namespace IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts

def to_CEGradFacts
    {p : CM2Params}
    (h : IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_CEGradResiduals

end IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts

/-- Sectorial mainline facts with the terminal pointwise endpoint input. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals p

namespace IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts

def to_CERawGradFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts p)
    (hb : 0 < p.b) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_CERawGradResiduals hb

end IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts

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

/-! ### Moser-ladder route with closed-energy seed and mass-gradient input -/

/-- Concrete interval-domain Paper3 mainline frontiers using closed energy for
the L² seed and the mass-gradient bridge for relative Moser interpolation. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallCEGradFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallCEGradFacts
      p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the
closed-energy/mass-gradient Moser route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEGradFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallCEGradFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallClosedEnergyFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { core := hData.core.to_closedEnergyFacts
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline from the
closed-energy/mass-gradient Moser route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEGradFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallCEGradFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEGradFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using closed energy for
the L² seed and the mass-gradient bridge for relative Moser interpolation. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallCEGradFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallCEGradFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
closed-energy/mass-gradient Moser route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCEGradFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallCEGradFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEGradFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
closed-energy/mass-gradient Moser route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCEGradFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallCEGradFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCEGradFrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Moser-ladder route with closed-energy, raw-drop, and CEGrad inputs -/

/-- Concrete interval-domain Paper3 mainline frontiers using closed energy,
raw Moser dissipation, and the mass-gradient bridge. -/
structure IntervalDomainPaper3MainlineMoserActualLinearSmallCERawGradFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallCERawGradFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the
closed-energy/raw-drop/CEGrad Moser route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCERawGradFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallCERawGradFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEGradFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { core := hData.core.to_CEGradFacts
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline from the
closed-energy/raw-drop/CEGrad Moser route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCERawGradFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallCERawGradFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCERawGradFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using closed energy, raw
Moser dissipation, and the mass-gradient bridge. -/
structure IntervalDomainPaper3StatementMoserActualLinearSmallCERawGradFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallCERawGradFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
closed-energy/raw-drop/CEGrad Moser route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCERawGradFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallCERawGradFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCERawGradFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
closed-energy/raw-drop/CEGrad Moser route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCERawGradFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallCERawGradFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCERawGradFrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Moser-ladder route with a terminal pointwise endpoint input -/

/-- Concrete interval-domain Paper3 mainline frontiers using the direct
terminal pointwise endpoint input. -/
structure IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the
terminal-endpoint Moser route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCERawGradFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { core := hData.core.to_CERawGradFacts hb
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline from the
terminal-endpoint Moser route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the direct terminal
pointwise endpoint input. -/
structure IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
terminal-endpoint Moser route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
terminal-endpoint Moser route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalFrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Terminal route with Paper2 theorem proposition inputs -/

/-- Full interval-domain Paper3 statement frontiers using the direct terminal
pointwise endpoint input, with Paper3 Proposition 1.3 and Proposition 1.4
routed through Paper2 Theorems 1.3 and 1.2. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2TheoremsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
terminal-endpoint Moser route and Paper2 theorem proposition inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2FrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
terminal-endpoint Moser route and Paper2 theorem proposition inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2FrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2FrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2FrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Terminal route with Paper2 main theorem target inputs -/

/-- Full interval-domain Paper3 statement frontiers using the direct terminal
pointwise endpoint input, with Proposition 1.3/1.4 routed through the Paper2
main theorem target bundle.

This is the preferred current actual-linear terminal statement route.  The
terminal Moser endpoint is no longer inline: `terminalPointwise` is converted to
`quantitativeEndpoint` by
`intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl`.
The route is still intentionally conditional: it carries the independent
`negativeBound` residual for Paper3 Proposition 1.2, the sectorial nonlinear
orbit bound, continuation/gluing, the terminal Moser analytic atoms,
compactness/regularization frontiers, and Theorem 2.3--2.5 stability frontiers.
Paper2 main targets discharge only the Proposition 1.3/1.4 branches, not
`negativeBound`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
terminal-endpoint Moser route and Paper2 main theorem target inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
terminal-endpoint Moser route and Paper2 main theorem target inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the terminal Moser route,
with the negative-sensitivity residual discharged by `0 < χ₀` and Proposition
1.3/1.4 routed through supplied Paper2 main theorem targets. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData
      p M0 uBar vLower K

/-- Assemble the terminal Moser Paper3 statement target from Paper2 main theorem
targets, without carrying a separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing terminal Moser Paper3 statement target from Paper2 main
theorem targets, with the negative-sensitivity residual discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Integrated first-crossing step route

The following structures replace the `rawMoserDrop` + `relativeMassGradient`
pair with a single `IntegratedMoserFirstCrossingStep` supplier.  The conversion
to the existing Moser-ladder route uses
`intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms` and
`intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms` from
`P3MoserActualWiring`. -/

/-- Closed-energy Moser residuals with the dissipation and relative
interpolation fields replaced by a single integrated first-crossing step
supplier.  This is thinner than the `CERawGrad` variant: one field replaces
two. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
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
  integratedStep :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals

/-- Convert the Paper3 actual-linear-small integrated-step residual surface to
the reusable integrated-step mass/Lp/smoothing residual package. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  integratedStep := h.integratedStep
  quantitativeEndpoint := h.quantitativeEndpoint

def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_integratedStepResiduals ha hχ0).to_routeResiduals

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals

/-- Actual-linear-small mass/Lp/smoothing residuals for the regular-energy
coefficient-gap route.

This is a thin wrapper over the reusable PDE residual
`IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals`: the actual-linear
wrapper does not store the parameter-side `a_pos` and `chi_nonneg` fields,
because those are supplied by the actual-linear-small theorem hypotheses. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
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
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTC :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyWindowFTC intervalDomain u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals

/-- Convert the actual-linear-small regular-energy coefficient-gap residuals to
the reusable PDE residual package. -/
def to_regularEnergyCoeffGapResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  classicalRegularity := h.classicalRegularity
  energyWindowFTC := h.energyWindowFTC
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Convert the regular-energy coefficient-gap residuals to the existing
actual-linear integrated-step residual surface. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
      hsol hcross hboot
      (h.classicalRegularity hsol hcross hboot)
      (h.energyWindowFTC hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (h.coeffGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Direct route residuals from the regular-energy coefficient-gap
actual-linear surface. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_regularEnergyCoeffGapResiduals ha hχ0).to_routeResiduals

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals

/-- Actual-linear-small mass/Lp/smoothing residuals for the local-FTC-data
regular-energy coefficient-gap route. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals
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
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTCData :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserEnergyWindowFTCLocalData u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals

/-- Collapse the local-FTC-data actual-linear residuals to the existing
regular-energy coefficient-gap actual-linear residual surface. -/
def to_regularEnergyCoeffGapResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
      p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  classicalRegularity := h.classicalRegularity
  energyWindowFTC := fun hsol hcross hboot =>
    intervalDomain_integratedMoserEnergyWindowFTC_of_localData
      hsol (h.energyWindowFTCData hsol hcross hboot)
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Convert the local-FTC-data regular-energy coefficient-gap residuals to the
existing actual-linear integrated-step residual surface. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals p :=
  h.to_regularEnergyCoeffGapResiduals.to_integratedStepResiduals

/-- Direct route residuals from the local-FTC-data regular-energy coefficient
gap actual-linear surface. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_regularEnergyCoeffGapResiduals.to_routeResiduals ha hχ0

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals

/-- Actual-linear-small mass/Lp/smoothing residuals for the derivative-window
regular-energy coefficient-gap route.  The endpoint power-energy continuity
needed for the energy-window FTC comes from the same classical regularity
field. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals
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
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  derivativeWindowIntegrability :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals

/-- Add the endpoint continuity already present in `classicalRegularity` and
collapse the derivative-window actual-linear residuals to the local-FTC-data
surface. -/
def to_FTCLocalDataResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals
      p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  classicalRegularity := h.classicalRegularity
  energyWindowFTCData := fun hsol hcross hboot =>
    let hreg := h.classicalRegularity hsol hcross hboot
    { endpointEnergy := hreg.endpointEnergy
      derivativeWindowIntegrability :=
        h.derivativeWindowIntegrability hsol hcross hboot }
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint

def to_regularEnergyCoeffGapResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
      p :=
  h.to_FTCLocalDataResiduals.to_regularEnergyCoeffGapResiduals

def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals p :=
  h.to_FTCLocalDataResiduals.to_integratedStepResiduals

/-- Direct route residuals from the derivative-window regular-energy
coefficient-gap actual-linear surface. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_FTCLocalDataResiduals.to_routeResiduals ha hχ0

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals

/-- Actual-linear-small mass/Lp/smoothing residuals for the
derivative-boundary regular-energy coefficient-gap route.  The strict
interior derivative windows come from classical regularity. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals
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
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  derivativeBoundaryData :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserEnergyDerivativeBoundaryData u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals

/-- Produce the derivative-window actual-linear residual from endpoint
derivative data and strict interior classical regularity. -/
def to_derivativeWindowResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals
      p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  classicalRegularity := h.classicalRegularity
  derivativeWindowIntegrability := fun hsol hcross hboot =>
    intervalDomain_derivativeWindowIntegrability_of_classical_boundary
      hsol (h.derivativeBoundaryData hsol hcross hboot)
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint

def to_FTCLocalDataResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals
      p :=
  h.to_derivativeWindowResiduals.to_FTCLocalDataResiduals

def to_regularEnergyCoeffGapResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
      p :=
  h.to_derivativeWindowResiduals.to_regularEnergyCoeffGapResiduals

def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals p :=
  h.to_derivativeWindowResiduals.to_integratedStepResiduals

/-- Direct route residuals from the derivative-boundary regular-energy
coefficient-gap actual-linear surface. -/
def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_derivativeWindowResiduals.to_routeResiduals ha hχ0

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals

/-- Sectorial mainline facts with the integrated first-crossing step input. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts

def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_routeResiduals ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts

/-- Sectorial mainline facts for the regular-energy coefficient-gap Moser
route. -/
structure
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals
      p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts

/-- Convert the regular-energy coefficient-gap sectorial facts to the existing
integrated-step sectorial facts. -/
def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_integratedStepResiduals

/-- Convert the regular-energy coefficient-gap sectorial facts to the existing
a-priori actual-linear-small facts. -/
def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p :=
  h.to_integratedStepFacts.to_aprioriActualLinearSmallFacts ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts

/-- Sectorial mainline facts for the local-FTC-data regular-energy
coefficient-gap Moser route. -/
structure
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals
      p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts

/-- Collapse local-FTC-data sectorial facts to the existing regular-energy
coefficient-gap sectorial facts. -/
def to_regularEnergyCoeffGapFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
      p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_regularEnergyCoeffGapResiduals

/-- Convert the local-FTC-data regular-energy coefficient-gap sectorial facts
to the existing integrated-step sectorial facts. -/
def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p :=
  h.to_regularEnergyCoeffGapFacts.to_integratedStepFacts

/-- Convert the local-FTC-data regular-energy coefficient-gap sectorial facts
to the existing a-priori actual-linear-small facts. -/
def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p :=
  h.to_integratedStepFacts.to_aprioriActualLinearSmallFacts ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts

/-- Sectorial mainline facts for the derivative-window regular-energy
coefficient-gap Moser route. -/
structure
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals
      p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts

/-- Collapse derivative-window sectorial facts to the existing local-FTC-data
sectorial facts. -/
def to_FTCLocalDataFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts
      p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_FTCLocalDataResiduals

def to_regularEnergyCoeffGapFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
      p :=
  h.to_FTCLocalDataFacts.to_regularEnergyCoeffGapFacts

/-- Convert the derivative-window regular-energy coefficient-gap sectorial
facts to the existing integrated-step sectorial facts. -/
def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p :=
  h.to_FTCLocalDataFacts.to_integratedStepFacts

/-- Convert the derivative-window regular-energy coefficient-gap sectorial
facts to the existing a-priori actual-linear-small facts. -/
def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p :=
  h.to_FTCLocalDataFacts.to_aprioriActualLinearSmallFacts ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts

/-- Sectorial mainline facts for the derivative-boundary regular-energy
coefficient-gap Moser route. -/
structure
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals
      p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts

/-- Collapse derivative-boundary sectorial facts to the existing
derivative-window sectorial facts. -/
def to_derivativeWindowFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts
      p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_derivativeWindowResiduals

def to_FTCLocalDataFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts
      p :=
  h.to_derivativeWindowFacts.to_FTCLocalDataFacts

def to_regularEnergyCoeffGapFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
      p :=
  h.to_derivativeWindowFacts.to_regularEnergyCoeffGapFacts

/-- Convert the derivative-boundary regular-energy coefficient-gap sectorial
facts to the existing integrated-step sectorial facts. -/
def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p :=
  h.to_derivativeWindowFacts.to_integratedStepFacts

/-- Convert the derivative-boundary regular-energy coefficient-gap sectorial
facts to the existing a-priori actual-linear-small facts. -/
def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p :=
  h.to_derivativeWindowFacts.to_aprioriActualLinearSmallFacts ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts

/-- Concrete interval-domain Paper3 mainline frontiers using the integrated
first-crossing step route and the actual-linear-small persistence producer. -/
structure IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the integrated
first-crossing step route and the actual-linear-small persistence producer. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { core := hData.core.to_aprioriActualLinearSmallFacts ha hχ0
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline from the
integrated first-crossing step route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the integrated
first-crossing step route and the actual-linear-small persistence producer. -/
structure IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
integrated first-crossing step route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
integrated first-crossing step route. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepFrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the integrated
first-crossing step route, with Proposition 1.3/1.4 routed through Paper2
main theorem targets. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
integrated first-crossing step route and Paper2 main theorem target inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
integrated first-crossing step route and Paper2 main theorem target inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the integrated-step
Moser route, with the negative-sensitivity residual discharged by `0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
      p M0 uBar vLower K

/-- Assemble the integrated-step Moser Paper3 statement target from Paper2 main
theorem targets, without carrying a separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing integrated-step Moser Paper3 statement target from Paper2
main theorem targets, with the negative-sensitivity residual discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Integrated first-crossing step route with Stability24 input -/

/-- Integrated-step Moser mainline data with the actual-linear-small stability
package reduced to its non-vacuous Theorem 2.4 branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the Stability24-thinned integrated-step Moser mainline data to the
current full integrated-step frontier surface. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData.toCurrent
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
        p M0 uBar vLower K)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
      p M0 uBar vLower K where
  core := h.core
  compactness := h.compactness
  stability := h.stability24.toStability23To25 ha hχ0

/-- Mainline target from integrated-step Moser frontiers and the Stability24-only
actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    (hData.toCurrent ha hχ0)

/-- Instance-facing mainline target from integrated-step Moser frontiers and the
Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using integrated-step Moser
frontiers, Paper2 main theorem targets for Proposition 1.3/1.4, and the
Stability24-only actual-linear stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from
integrated-step Moser frontiers, Paper2 main theorem target inputs, and
Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from
integrated-step Moser frontiers, Paper2 main theorem target inputs, and
Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the integrated-step
Stability24 route, with the negative-sensitivity residual discharged by
`0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the integrated-step Stability24 Paper3 statement target from Paper2
main theorem targets, without carrying a separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing integrated-step Stability24 Paper3 statement target from
Paper2 main theorem targets, with the negative-sensitivity residual discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Regular-energy coefficient-gap route with Stability24 input -/

/-- Regular-energy coefficient-gap Moser mainline data with the
actual-linear-small stability package reduced to its non-vacuous Theorem 2.4
branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts
      p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the regular-energy coefficient-gap mainline data to the existing
integrated-step Stability24 route. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData.toIntegratedStepStability24
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K where
  core := h.core.to_integratedStepFacts
  compactness := h.compactness
  stability24 := h.stability24

/-- Mainline target from the regular-energy coefficient-gap Moser route and the
Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    hData.toIntegratedStepStability24

/-- Instance-facing mainline target from the regular-energy coefficient-gap
Moser route and the Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the regular-energy
coefficient-gap route, Paper2 main theorem targets for Proposition 1.3/1.4,
and the Stability24-only actual-linear stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
regular-energy coefficient-gap Moser route, Paper2 main theorem target inputs,
and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
regular-energy coefficient-gap Moser route, Paper2 main theorem target inputs,
and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the regular-energy
coefficient-gap Stability24 route, with the negative-sensitivity residual
discharged by `0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the regular-energy coefficient-gap Stability24 Paper3 statement
target from Paper2 main theorem targets, without a separate negative-sensitivity
residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapStability24P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing regular-energy coefficient-gap Stability24 Paper3 statement
target from Paper2 main theorem targets, with the negative-sensitivity residual
discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapStability24P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### FTC-local-data regular-energy coefficient-gap route with Stability24 input -/

/-- FTC-local-data regular-energy coefficient-gap Moser mainline data with the
actual-linear-small stability package reduced to its non-vacuous Theorem 2.4
branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts
      p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the FTC-local-data coefficient-gap mainline data to the
regular-energy coefficient-gap Stability24 route. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData.toRegularEnergyCoeffGapStability24
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
      p M0 uBar vLower K where
  core := h.core.to_regularEnergyCoeffGapFacts
  compactness := h.compactness
  stability24 := h.stability24

/-- Mainline target from the FTC-local-data regular-energy coefficient-gap
Moser route and the Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    hData.toRegularEnergyCoeffGapStability24

/-- Instance-facing mainline target from the FTC-local-data regular-energy
coefficient-gap Moser route and the Stability24-only actual-linear stability
package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the FTC-local-data
regular-energy coefficient-gap route, Paper2 main theorem targets for
Proposition 1.3/1.4, and the Stability24-only actual-linear stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
FTC-local-data regular-energy coefficient-gap Moser route, Paper2 main theorem
target inputs, and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
FTC-local-data regular-energy coefficient-gap Moser route, Paper2 main theorem
target inputs, and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the FTC-local-data
regular-energy coefficient-gap Stability24 route, with the negative-sensitivity
residual discharged by `0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the FTC-local-data regular-energy coefficient-gap Stability24
Paper3 statement target from Paper2 main theorem targets, without a separate
negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing FTC-local-data regular-energy coefficient-gap Stability24
Paper3 statement target from Paper2 main theorem targets, with the
negative-sensitivity residual discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Derivative-window regular-energy coefficient-gap route with Stability24 input -/

/-- Derivative-window regular-energy coefficient-gap Moser mainline data with
the actual-linear-small stability package reduced to its non-vacuous Theorem
2.4 branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts
      p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the derivative-window coefficient-gap mainline data to the
FTC-local-data coefficient-gap Stability24 route. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData.toFTCLocalDataStability24
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
      p M0 uBar vLower K where
  core := h.core.to_FTCLocalDataFacts
  compactness := h.compactness
  stability24 := h.stability24

/-- Mainline target from the derivative-window regular-energy coefficient-gap
Moser route and the Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    hData.toFTCLocalDataStability24

/-- Instance-facing mainline target from the derivative-window regular-energy
coefficient-gap Moser route and the Stability24-only actual-linear stability
package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the derivative-window
regular-energy coefficient-gap route, Paper2 main theorem targets for
Proposition 1.3/1.4, and the Stability24-only actual-linear stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
derivative-window regular-energy coefficient-gap Moser route, Paper2 main
theorem target inputs, and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
derivative-window regular-energy coefficient-gap Moser route, Paper2 main
theorem target inputs, and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the derivative-window
regular-energy coefficient-gap Stability24 route, with the negative-sensitivity
residual discharged by `0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the derivative-window regular-energy coefficient-gap Stability24
Paper3 statement target from Paper2 main theorem targets, without a separate
negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing derivative-window regular-energy coefficient-gap
Stability24 Paper3 statement target from Paper2 main theorem targets, with the
negative-sensitivity residual discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Derivative-boundary regular-energy coefficient-gap route with Stability24 input -/

/-- Derivative-boundary regular-energy coefficient-gap Moser mainline data with
the actual-linear-small stability package reduced to its non-vacuous Theorem
2.4 branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts
      p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the derivative-boundary coefficient-gap mainline data to the
regular-energy coefficient-gap Stability24 route. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData.toRegularEnergyCoeffGapStability24
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
      p M0 uBar vLower K where
  core := h.core.to_regularEnergyCoeffGapFacts
  compactness := h.compactness
  stability24 := h.stability24

/-- Mainline target from the derivative-boundary regular-energy coefficient-gap
Moser route and the Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    hData.toRegularEnergyCoeffGapStability24

/-- Instance-facing mainline target from the derivative-boundary regular-energy
coefficient-gap Moser route and the Stability24-only actual-linear stability
package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the derivative-boundary
regular-energy coefficient-gap route, Paper2 main theorem targets for
Proposition 1.3/1.4, and the Stability24-only actual-linear stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
derivative-boundary regular-energy coefficient-gap Moser route, Paper2 main
theorem target inputs, and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
derivative-boundary regular-energy coefficient-gap Moser route, Paper2 main
theorem target inputs, and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the derivative-boundary
regular-energy coefficient-gap Stability24 route, with the negative-sensitivity
residual discharged by `0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the derivative-boundary regular-energy coefficient-gap Stability24
Paper3 statement target from Paper2 main theorem targets, without a separate
negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing derivative-boundary regular-energy coefficient-gap
Stability24 Paper3 statement target from Paper2 main theorem targets, with the
negative-sensitivity residual discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Integrated first-crossing step route with thin compactness and stability inputs -/

/-- Thin integrated-step Moser mainline frontiers for the actual-linear headline
route.  This chooses the canonical sup-norm compactness package, shares initial
continuity once, uses `0 < a` to discharge the minimal-upper branch, and carries
only the non-vacuous Theorem 2.4 stability frontiers. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p
  initialContinuity : IntervalDomainInitialContinuityRaw p
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the thin
integrated-step actual-linear headline route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    ha hb hχ0 hm hβ hχ
    { core := hData.core
      compactness :=
        (hData.compactness.toSupNormData ha hData.initialContinuity).toConcrete
      stability := hData.stability24.toStability23To25 ha hχ0 }

/-- Instance-facing concrete interval-domain Paper3 mainline from the thin
integrated-step actual-linear headline route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
        p M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
    p M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the thin integrated-step
actual-linear headline route, with Proposition 1.3/1.4 routed through Paper2
main theorem targets. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the full interval-domain Paper3 statement target from the thin
integrated-step actual-linear headline route and Paper2 main theorem target
inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
      ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the thin
integrated-step actual-linear headline route and Paper2 main theorem target
inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the thin integrated-step
actual-linear headline route, with the negative-sensitivity Proposition 1.2
residual discharged by `0 < χ₀` and Proposition 1.3/1.4 routed through Paper2
main theorem targets. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the full interval-domain Paper3 statement target from the thin
integrated-step actual-linear headline route and Paper2 main theorem targets,
without carrying a separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing full interval-domain Paper3 statement target from the thin
integrated-step actual-linear headline route and Paper2 main theorem targets,
with the negative-sensitivity residual discharged by `0 < χ₀`. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainNoNegData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-! ### Integrated-Moser direct threshold-plan route -/

/-- Actual-linear-small Moser residuals whose first-crossing step is produced
directly from classical integrated-Moser regularity, integrated dissipation,
and relative interpolation. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals
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
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals

/-- Convert the actual-linear integrated-Moser surface to the reusable PDE-level
integrated-Moser residual package. -/
def to_integratedMoserResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingIntegratedMoserResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  classicalRegularity := h.classicalRegularity
  integratedDissipation := h.integratedDissipation
  relativeMoserInterpolation := h.relativeMoserInterpolation
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Convert the direct integrated-Moser actual-linear surface to the existing
integrated-step actual-linear residual surface. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
      p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
      (h.classicalRegularity hsol hcross hboot)
      hsol
      (h.integratedDissipation hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_integratedStepResiduals.to_routeResiduals ha hχ0

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals

/-- Sectorial mainline facts with the direct integrated-Moser residual surface. -/
structure
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedMoserFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals
      p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedMoserFacts

def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedMoserFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_integratedStepResiduals

def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedMoserFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p :=
  h.to_integratedStepFacts.to_aprioriActualLinearSmallFacts ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedMoserFacts

/-- Direct integrated-Moser mainline data with the actual-linear-small
stability package reduced to its non-vacuous Theorem 2.4 branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedMoserStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedMoserFacts
      p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert direct integrated-Moser mainline data to the existing integrated-step
Stability24 route. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedMoserStability24FrontierData.toIntegratedStepStability24
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedMoserStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K where
  core := h.core.to_integratedStepFacts
  compactness := h.compactness
  stability24 := h.stability24

/-- Mainline target from the direct integrated-Moser Moser route and the
Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedMoserStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedMoserStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    hData.toIntegratedStepStability24

/-- Instance-facing mainline target from the direct integrated-Moser route and
the Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedMoserStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedMoserStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedMoserStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the direct
integrated-Moser route, Paper2 main theorem targets for Proposition 1.3/1.4,
and the Stability24-only actual-linear stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedMoserStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedMoserStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from direct
integrated-Moser frontiers, Paper2 main theorem target inputs, and
Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedMoserStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedMoserStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from direct
integrated-Moser frontiers, Paper2 main theorem target inputs, and
Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedMoserStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the direct
integrated-Moser Stability24 route, with the negative-sensitivity residual
discharged by `0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedMoserStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedMoserStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the direct integrated-Moser Stability24 Paper3 statement target
from Paper2 main theorem targets, without a separate negative-sensitivity
residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedMoserStability24P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing direct integrated-Moser Stability24 Paper3 statement target
from Paper2 main theorem targets, with negative sensitivity discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedMoserStability24P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Lower-average / upper-data-gap component route -/

/-- Compatibility-named actual-linear-small Moser residuals for the former
lower-average / upper-data-gap route.

The direct threshold-plan route now only consumes regularity, integrated
dissipation, and relative interpolation; the lower-average / upper-data-gap
fields have been removed from this residual surface. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
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
  classicalContinuityRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalContinuityRegularityData u T p0
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals

/-- Convert the compatibility-named actual-linear-small lowerAverage/upperDataGap
residual surface to the existing integrated-step actual-linear residual surface.

The old route name is retained for compatibility; the lower-average and
upper-data-gap fields have been removed, and this conversion uses the direct
threshold-plan route from regularity, integrated dissipation, and relative
interpolation. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
      p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
      (intervalDomain_classicalRegularityData_of_continuityRegularityData
        (IsPaper2ClassicalSolution.T_pos hsol).le
        (h.classicalContinuityRegularity hsol hcross hboot))
      hsol
      (h.integratedDissipation hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals

/-- Sectorial mainline facts with the compatibility-named
lowerAverage/upperDataGap Moser residual surface. -/
structure
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
      p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts

def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts
        p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_integratedStepResiduals

def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts
        p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p :=
  h.to_integratedStepFacts.to_aprioriActualLinearSmallFacts ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts

/-- Compatibility-named lowerAverage/upperDataGap Moser mainline data with the
actual-linear-small stability package reduced to its non-vacuous Theorem 2.4
branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts
      p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the compatibility-named lowerAverage/upperDataGap mainline data to
the existing integrated-step Stability24 surface. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData.toIntegratedStepStability24
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K where
  core := h.core.to_integratedStepFacts
  compactness := h.compactness
  stability24 := h.stability24

/-- Mainline target from the compatibility-named lowerAverage/upperDataGap
Moser route and the Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    hData.toIntegratedStepStability24

/-- Instance-facing mainline target from the compatibility-named
lowerAverage/upperDataGap Moser route and the Stability24-only actual-linear
stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using the
compatibility-named lowerAverage/upperDataGap Moser route, Paper2 main theorem
targets for Proposition 1.3/1.4, and the Stability24-only actual-linear
stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
compatibility-named lowerAverage/upperDataGap Moser route, Paper2 main theorem
target inputs, and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
compatibility-named lowerAverage/upperDataGap Moser route, Paper2 main theorem
target inputs, and Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the compatibility-named
lowerAverage / upperDataGap Stability24 route, with the negative-sensitivity
residual discharged by `0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the compatibility-named lowerAverage / upperDataGap Stability24
Paper3 statement target from Paper2 main theorem targets, without a separate
negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing compatibility-named lowerAverage / upperDataGap Stability24
Paper3 statement target from Paper2 main theorem targets, with negative
sensitivity discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Lower-average / upper-gap split route

This route refines the integrated-step residual by splitting the supplied
first-crossing input into the lower-average and upper-gap frontiers exposed in
`P3MoserIntegratedClosure`. -/

/-- Actual-linear-small Moser residuals with the integrated first-crossing step
replaced by lower-average / upper-gap split frontiers. -/
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals
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
  lowerUpperFrontiers :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        Nonempty
          (IntegratedMoserFirstCrossingLowerUpperFrontiers
            intervalDomain u T rho p0)
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

namespace
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals

/-- Convert the Paper3 actual-linear-small lower/upper split residual surface
to the reusable PDE-level lower/upper mass/Lp/smoothing residual package. -/
def to_lowerUpperFrontierResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  lowerUpperFrontiers := fun hsol hcross hboot =>
    Classical.choice (h.lowerUpperFrontiers hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Convert the lower/upper split residual surface to the existing Paper3
integrated-step residual package. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals p) :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
      p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  integratedStep := fun hsol hcross hboot =>
    integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
      (Classical.choice (h.lowerUpperFrontiers hsol hcross hboot))
  quantitativeEndpoint := h.quantitativeEndpoint

def to_routeResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_lowerUpperFrontierResiduals ha hχ0).to_routeResiduals

end
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals

/-- Sectorial mainline facts with lower-average / upper-gap split Moser
frontiers. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals p

namespace
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts

def to_integratedStepFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts p) :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_integratedStepResiduals

def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h :
      IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing := h.massLpSmoothing.to_routeResiduals ha hχ0

end
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts

/-- Concrete interval-domain Paper3 mainline frontiers using lower-average /
upper-gap split Moser frontiers. -/
structure IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from lower-average /
upper-gap split Moser frontiers. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { core := hData.core.to_integratedStepFacts
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline from lower-average
/ upper-gap split Moser frontiers. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using lower-average /
upper-gap split Moser frontiers. -/
structure IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from
lower-average / upper-gap split Moser frontiers. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from
lower-average / upper-gap split Moser frontiers. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperFrontierData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using lower-average /
upper-gap split Moser frontiers, with Proposition 1.3/1.4 routed through
Paper2 main theorem targets. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from
lower-average / upper-gap split Moser frontiers and Paper2 main theorem target
inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from
lower-average / upper-gap split Moser frontiers and Paper2 main theorem target
inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the lower/upper split
Moser route, with the negative-sensitivity residual discharged by `0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
      p M0 uBar vLower K

/-- Assemble the lower/upper split Moser Paper3 statement target from Paper2
main theorem targets, without a separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing lower/upper split Moser Paper3 statement target from Paper2
main theorem targets, with negative sensitivity discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Lower/upper headline route with Stability24 input -/

/-- Lower-average / upper-gap Moser mainline data with the actual-linear-small
stability package reduced to its non-vacuous Theorem 2.4 branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the Stability24-thinned lower/upper Moser mainline data to the
current full lower/upper frontier surface. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData.toCurrent
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
        p M0 uBar vLower K)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
      p M0 uBar vLower K where
  core := h.core
  compactness := h.compactness
  stability := h.stability24.toStability23To25 ha hχ0

/-- Mainline target from lower/upper Moser frontiers and the Stability24-only
actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    (hData.toCurrent ha hχ0)

/-- Instance-facing mainline target from lower/upper Moser frontiers and the
Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using lower/upper Moser
frontiers, Paper2 main theorem targets for Proposition 1.3/1.4, and the
Stability24-only actual-linear stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from lower/upper
Moser frontiers, Paper2 main theorem target inputs, and Stability24-only
actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from
lower/upper Moser frontiers, Paper2 main theorem target inputs, and
Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the lower/upper
Stability24 route, with the negative-sensitivity residual discharged by
`0 < χ₀`. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the lower/upper Stability24 Paper3 statement target from Paper2
main theorem targets, without a separate negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainNoNegData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing lower/upper Stability24 Paper3 statement target from Paper2
main theorem targets, with negative sensitivity discharged. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainNoNegData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainNoNegData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-! ### Lower/upper headline route with thin compactness and stability inputs -/

/-- Thin lower-average / upper-gap mainline frontiers for the actual-linear
headline route.  This chooses the canonical sup-norm compactness package,
shares initial continuity once, uses `0 < a` to discharge the minimal-upper
branch, and carries only the non-vacuous Theorem 2.4 stability frontiers. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts p
  initialContinuity : IntervalDomainInitialContinuityRaw p
  compactness :
    IntervalDomainPaper3SupNormCompactnessAPosData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the thin
lower-average / upper-gap actual-linear headline route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperThinFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    ha hb hχ0 hm hβ hχ
    { core := hData.core
      compactness :=
        (hData.compactness.toSupNormData ha hData.initialContinuity).toConcrete
      stability := hData.stability24.toStability23To25 ha hχ0 }

/-- Instance-facing concrete interval-domain Paper3 mainline from the thin
lower-average / upper-gap actual-linear headline route. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperThinFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperThinFrontierData
        p M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperThinFrontierData
    p M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the thin lower-average /
upper-gap actual-linear headline route, with Proposition 1.3/1.4 routed through
Paper2 main theorem targets. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the full interval-domain Paper3 statement target from the thin
lower-average / upper-gap actual-linear headline route and Paper2 main theorem
target inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2MainData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound
      ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the thin
lower-average / upper-gap actual-linear headline route and Paper2 main theorem
target inputs. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2MainData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers for the thin lower-average /
upper-gap actual-linear headline route, with the negative-sensitivity
Proposition 1.2 residual discharged from `0 < χ₀` and Proposition 1.3/1.4
routed through supplied Paper2 main theorem targets. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the thin lower-average / upper-gap actual-linear Paper3 statement
target from Paper2 main theorem targets, without carrying a separate
negative-sensitivity residual. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2MainNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ
    { propositions :=
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          paper2Main := hData.paper2Main }
      mainline := hData.mainline }

/-- Instance-facing thin lower-average / upper-gap actual-linear Paper3
statement target from Paper2 main theorem targets, with the
negative-sensitivity residual discharged by `0 < χ₀`. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2MainNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainNoNegData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound
    ha hb hχ0 hm hβ hχ hData.out

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
  intervalDomain_paper3_coreStatementTargets_of_actualLinear22Data
#print axioms
  intervalDomain_paper3_mainlineTargets_of_actualLinear22FrontierData
#print axioms
  intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_actualLinear22FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_actualLinear22P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_actualLinear22P2MainNoNegData
#print axioms
  intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_actualLinear22ThinP2MainNoNegData
#print axioms
  intervalDomain_sectorialMainline_unconditionalTarget_of_aprioriActualLinearSmallFacts
#print axioms
  intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_aprioriActualLinearSmallP2MainNoNegData
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
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEGradFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCEGradFrontierData
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCERawGradFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCERawGradFrontierData
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainNoNegData
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals.to_routeResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals.to_regularEnergyCoeffGapResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapResiduals.to_routeResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals.to_regularEnergyCoeffGapResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataResiduals.to_routeResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals.to_FTCLocalDataResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals.to_regularEnergyCoeffGapResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowResiduals.to_routeResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals.to_derivativeWindowResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals.to_FTCLocalDataResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals.to_regularEnergyCoeffGapResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryResiduals.to_routeResiduals
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts.to_integratedStepFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFacts.to_aprioriActualLinearSmallFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts.to_regularEnergyCoeffGapFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts.to_integratedStepFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataFacts.to_aprioriActualLinearSmallFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts.to_FTCLocalDataFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts.to_regularEnergyCoeffGapFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts.to_integratedStepFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowFacts.to_aprioriActualLinearSmallFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts.to_derivativeWindowFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts.to_FTCLocalDataFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts.to_regularEnergyCoeffGapFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts.to_integratedStepFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryFacts.to_aprioriActualLinearSmallFacts
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepP2MainNoNegData
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData.toCurrent
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainNoNegData
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData.toIntegratedStepStability24
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapStability24P2MainNoNegData
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData.toRegularEnergyCoeffGapStability24
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapFTCLocalDataStability24P2MainNoNegData
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData.toFTCLocalDataStability24
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeWindowStability24P2MainNoNegData
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData.toRegularEnergyCoeffGapStability24
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallRegularEnergyCoeffGapDerivativeBoundaryStability24P2MainNoNegData
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepThinP2MainNoNegData
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals.to_integratedMoserResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedMoserResiduals.to_routeResiduals
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedMoserFacts.to_integratedStepFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedMoserFacts.to_aprioriActualLinearSmallFacts
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedMoserStability24FrontierData.toIntegratedStepStability24
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedMoserStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedMoserStability24P2MainNoNegData
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts.to_integratedStepFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallLowerAverageUpperDataGapFacts.to_aprioriActualLinearSmallFacts
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData.toIntegratedStepStability24
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals.to_lowerUpperFrontierResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals.to_routeResiduals
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts.to_integratedStepFacts
#print axioms
  IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts.to_aprioriActualLinearSmallFacts
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainNoNegData
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData.toCurrent
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainNoNegData
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperThinFrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperThinP2MainNoNegData

end ShenWork.Paper3
