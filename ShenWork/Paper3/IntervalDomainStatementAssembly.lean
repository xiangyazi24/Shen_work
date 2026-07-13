/-
  Paper3 interval-domain statement-target assembly.

  This file only packages proved bridges from the interval-domain StabilityChain
  and Sectorial files.  It adds no new analytic frontier: the remaining
  hypotheses are the canonical core existence package and the concrete
  initial-continuity frontier already exposed downstream.
-/
import ShenWork.Paper2.IntervalDomainStatementAssembly
import ShenWork.Paper3.StatementAssembly
import ShenWork.Paper3.IntervalDomainStabilityChain
import ShenWork.Paper3.IntervalDomainSectorialNonlinearBridges
import ShenWork.Paper3.IntervalDomainFaithfulTheorem22
import ShenWork.Paper3.IntervalDomainEventualConvergenceUpgrade

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-! ## Proposition 1.x targets -/

/-- Interval-domain Paper3 Proposition 1.2 and Proposition 1.4 targets. -/
def IntervalDomainPaper3Proposition1Targets (p : CM2Params) : Prop :=
  Proposition_1_2 intervalDomain p ∧ Proposition_1_4 intervalDomain p

/-- Interval-domain abbreviation for the independent Paper3 Proposition 1.2
negative-sensitivity residual.  This is not produced by Paper2 main targets. -/
abbrev IntervalDomainPaper3NegativeSensitivityResidual
    (p : CM2Params) : Prop :=
  NegativeSensitivityGlobalEventualBound intervalDomain p

/-- Atomic interval-domain frontiers for Paper3 Proposition 1.2 in the
negative-sensitivity regime.

This is still a residual package.  It separates global existence/initial trace
from the long-time sup-norm bound so future PDE work can discharge the two
analytic components independently. -/
structure IntervalDomainPaper3NegativeSensitivityFrontierData
    (p : CM2Params) : Prop where
  globalSolution :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
            InitialTrace intervalDomain u₀ u
  eventualSupBound :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomain p u v →
            InitialTrace intervalDomain u₀ u →
              ∃ T₀ M : ℝ,
                ∀ t : ℝ, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Pure packaging from the atomic negative-sensitivity frontiers to the
existing Paper3 Proposition 1.2 residual. -/
theorem intervalDomainPaper3_negativeSensitivityResidual_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper3NegativeSensitivityFrontierData p) :
    IntervalDomainPaper3NegativeSensitivityResidual p := by
  intro hχ hm u₀ hu₀
  rcases hData.globalSolution hχ hm u₀ hu₀ with
    ⟨u, v, hglobal, htrace⟩
  rcases hData.eventualSupBound hχ hm u₀ hu₀ u v hglobal htrace with
    ⟨T₀, M, hM⟩
  exact ⟨u, v, hglobal, htrace, M,
    Filter.eventually_atTop.mpr ⟨T₀, hM⟩⟩

/-- Instance-facing wrapper for the decomposed negative-sensitivity residual. -/
theorem intervalDomainPaper3_negativeSensitivityResidual_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper3NegativeSensitivityFrontierData p)] :
    IntervalDomainPaper3NegativeSensitivityResidual p :=
  intervalDomainPaper3_negativeSensitivityResidual_of_frontierData p hData.out

/-- Frontier data for the interval-domain Proposition 1.2 and Proposition 1.4
targets.  The `negativeBound` field can be supplied monolithically, or via
`intervalDomainPaper3_negativeSensitivityResidual_of_frontierData` from the
decomposed global-solution and eventual-sup frontiers above. -/
structure IntervalDomainPaper3Proposition1FrontierData
    (p : CM2Params) : Prop where
  negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p
  criticalExistence :
    p.m = 1 → 1 ≤ p.β →
      ((p.a = 0 ∧ p.b = 0) ∨ (0 ≤ p.a ∧ 0 < p.b)) →
        p.χ₀ < chiBeta p →
          ∀ u₀ : intervalDomain.Point → ℝ,
            PositiveInitialDatum intervalDomain u₀ →
              ∃ u v : ℝ → intervalDomain.Point → ℝ,
                IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
                InitialTrace intervalDomain u₀ u ∧
                IsPaper2Bounded intervalDomain u

/-- Interval-domain Proposition 1.2 and Proposition 1.4 from their frontier
data. -/
theorem intervalDomain_paper3_proposition1Targets_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper3Proposition1FrontierData p) :
    IntervalDomainPaper3Proposition1Targets p :=
  ⟨Proposition_1_2_of_negativeSensitivityGlobalEventualBound
      intervalDomain p hData.negativeBound,
    Proposition_1_4.of_assumed_existence_branch hData.criticalExistence⟩

/-- Instance-facing interval-domain Proposition 1.2/1.4 wrapper. -/
theorem intervalDomain_paper3_proposition1Targets_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper3Proposition1FrontierData p)] :
    IntervalDomainPaper3Proposition1Targets p :=
  intervalDomain_paper3_proposition1Targets_of_frontierData p hData.out

/-- Single-target wrapper for Paper3 Proposition 1.2. -/
theorem intervalDomain_paper3_Proposition_1_2_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper3Proposition1FrontierData p) :
    Proposition_1_2 intervalDomain p :=
  (intervalDomain_paper3_proposition1Targets_of_frontierData p hData).1

/-- Instance-facing wrapper for Paper3 Proposition 1.2. -/
theorem intervalDomain_paper3_Proposition_1_2_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper3Proposition1FrontierData p)] :
    Proposition_1_2 intervalDomain p :=
  intervalDomain_paper3_Proposition_1_2_of_frontierData p hData.out

/-- Single-target wrapper for Paper3 Proposition 1.4. -/
theorem intervalDomain_paper3_Proposition_1_4_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper3Proposition1FrontierData p) :
    Proposition_1_4 intervalDomain p :=
  (intervalDomain_paper3_proposition1Targets_of_frontierData p hData).2

/-- Instance-facing wrapper for Paper3 Proposition 1.4. -/
theorem intervalDomain_paper3_Proposition_1_4_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper3Proposition1FrontierData p)] :
    Proposition_1_4 intervalDomain p :=
  intervalDomain_paper3_Proposition_1_4_of_frontierData p hData.out

/-- Interval-domain Paper3 Proposition 1.x targets, with Proposition 1.3
supplied by Paper2 Theorem 1.3. -/
def IntervalDomainPaper3Proposition1WithTheorem13Targets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Paper3Proposition1Targets intervalDomain p C

/-- Frontier data for the interval-domain Proposition 1.x target package when
the Proposition 1.3 branch is supplied by Paper2 Theorem 1.3. -/
structure IntervalDomainPaper3Proposition1WithTheorem13FrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  proposition12And14 : IntervalDomainPaper3Proposition1FrontierData p
  theorem13 : Theorem_1_3 intervalDomain p C

/-- Assemble interval-domain Paper3 Propositions 1.2--1.4, routing
Proposition 1.3 through Paper2 Theorem 1.3. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hData :
      IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C) :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  paper3_proposition1Targets_of_paper2Theorem13Data
    { negativeBound := hData.proposition12And14.negativeBound
      theorem13 := hData.theorem13
      proposition14 := hData.proposition12And14.criticalExistence }

/-- Instance-facing interval-domain Paper3 Proposition 1.x wrapper using
Paper2 Theorem 1.3 for Proposition 1.3. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    [hData : Fact
      (IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C)] :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
    p C hData.out

/-- Interval-domain Paper3 Proposition 1.x data with Proposition 1.4 routed
through Paper2 Theorem 1.2 and Proposition 1.3 routed through Paper2 Theorem
1.3. -/
structure IntervalDomainPaper3Proposition1FromPaper2TheoremsData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p
  theorem12 : Theorem_1_2 intervalDomain p
  theorem13 : Theorem_1_3 intervalDomain p C

/-- Assemble interval-domain Paper3 Propositions 1.2--1.4 using Paper2
Theorems 1.2 and 1.3 for the existence branches. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData
    (p : CM2Params) (C : Paper2Constants p)
    (hData : IntervalDomainPaper3Proposition1FromPaper2TheoremsData p C) :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  paper3_proposition1Targets_of_paper2TheoremsData
    { negativeBound := hData.negativeBound
      theorem12 := hData.theorem12
      theorem13 := hData.theorem13 }

/-- Instance-facing interval-domain Paper3 Proposition 1.x wrapper using
Paper2 Theorems 1.2 and 1.3. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsDataFact
    (p : CM2Params) (C : Paper2Constants p)
    [hData :
      Fact (IntervalDomainPaper3Proposition1FromPaper2TheoremsData p C)] :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData
    p C hData.out

/-- Interval-domain Paper3 Proposition 1.x data with Proposition 1.4 and
Proposition 1.3 routed through the Paper2 main theorem target bundle.

The `negativeBound` field is still the independent Proposition 1.2 residual;
the Paper2 main bundle is used downstream only for the Theorem 1.2/1.3
components that imply Paper3 Propositions 1.4/1.3. -/
structure IntervalDomainPaper3Proposition1FromPaper2MainTargetsData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p
  paper2Main : IntervalDomainPaper2MainTheoremTargets p C

/-- Assemble interval-domain Paper3 Propositions 1.2--1.4 using Paper2 main
theorem targets for the Proposition 1.3/1.4 existence branches.  Proposition
1.2 is supplied by the separate `negativeBound` field. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
    (p : CM2Params) (C : Paper2Constants p)
    (hData : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C) :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  paper3_proposition1Targets_of_paper2MainTargetsData
    { negativeBound := hData.negativeBound
      main := hData.paper2Main }

/-- Instance-facing interval-domain Paper3 Proposition 1.x wrapper using
Paper2 main theorem targets. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsDataFact
    (p : CM2Params) (C : Paper2Constants p)
    [hData :
      Fact (IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C)] :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
    p C hData.out

/-! ## Theorem 2.x and compactness targets -/

/-- Concrete interval-domain Paper3 targets currently closed by the existing
StabilityChain/Sectorial infrastructure once the canonical core existence and
initial-continuity frontiers are supplied. -/
def IntervalDomainPaper3CoreStatementTargets
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop :=
  Lemma_3_1 intervalDomain p ∧
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms ∧
    UpperEnvelopeMonotonicityRaw intervalDomain p intervalDomain.supNorm ∧
    IntervalDomainStabilityChainTheorem21Target p M0 uBar vLower ∧
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower

/-- Core Paper3 interval-domain statement-target assembly.

The result records all concrete statement targets that are already connected by
existing branch theorems:
* `Lemma_3_1` is closed by the global classical-solution regularity field;
* concrete `Lemma_3_3` comes from `IntervalDomainInitialContinuityRaw`;
* upper-envelope monotonicity is the interval sup-norm max-principle bridge;
* the StabilityChain `Theorem_2_1` target uses the persistence part of the
  sectorial core existence package;
* the Sectorial `Theorem_2_1/2.2` target uses the full core existence package.
-/
theorem intervalDomain_paper3_coreStatementTargets_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower := by
  have hchain :
      IntervalDomainStabilityChainConcreteMainlineTarget
        p M0 uBar vLower :=
    intervalDomain_stabilityChainConcreteMainlineTarget_of_sectorialMainlineExistence
      p M0 uBar vLower hcont hcore.to_mainlineExistence
  exact ⟨Lemma_3_1_proved intervalDomain p,
    hchain.1,
    hchain.2.1,
    hchain.2.2,
    intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
      p M0 uBar vLower hcore⟩

/-- Instance-facing version of the core Paper3 interval-domain statement-target
assembly. -/
theorem intervalDomain_paper3_coreStatementTargets_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower :=
  intervalDomain_paper3_coreStatementTargets_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

/-- Core statement-frontier data with Theorem 2.2 supplied directly by the
two raw linear-stability branches.

Compared with `IntervalDomainSectorialMainlineCoreExistence`, this separates
the Theorem 2.1 persistence frontiers from the Theorem 2.2 local-exponential
branches.  It therefore does not require the spectral-orbit and small-data
existence fields when a direct `LinearStabilityInstability*Raw` producer is
available. -/
structure IntervalDomainPaper3CoreStatementLinear22Data
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  persistence : IntervalDomainSectorialTheorem21Persistence p uBar
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

/-- Assemble the core Paper3 statement targets from persistence plus the raw
linear Theorem 2.2 branches. -/
theorem intervalDomain_paper3_coreStatementTargets_of_linear22Data
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hData :
      IntervalDomainPaper3CoreStatementLinear22Data p M0 uBar vLower) :
    IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower := by
  have h22 :
      Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
    intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw
      p intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
      (intervalDomainSectorialPaper3Constants_usesCriticalSpectrum
        p M0 uBar vLower)
      hData.theorem22Nonminimal hData.theorem22Minimal
  have h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainPaper3Constants p M0 uBar vLower) :=
    intervalDomain_Theorem_2_1_for_concrete_constants_of_uniformPersistence_frontiers
      p M0 uBar vLower
      hData.persistence.part1 hData.persistence.part2
      hData.persistence.part3 hData.persistence.part4
  have h21_sectorial :
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
    intervalDomain_Theorem_2_1_sectorialMainline_of_persistence
      p M0 uBar vLower hData.persistence
  exact
    ⟨Lemma_3_1_proved intervalDomain p,
      intervalDomain_Lemma_3_3_for_concreteStabilityNorms_of_initialContinuityRaw
        p hData.initialContinuity,
      intervalDomain_upperEnvelopeMonotonicityRaw_supNorm p,
      h21,
      ⟨h22, h21_sectorial⟩⟩

/-- Instance-facing core statement wrapper for the raw-linear Theorem 2.2
route. -/
theorem intervalDomain_paper3_coreStatementTargets_of_linear22DataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hData : Fact
      (IntervalDomainPaper3CoreStatementLinear22Data p M0 uBar vLower)] :
    IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower :=
  intervalDomain_paper3_coreStatementTargets_of_linear22Data
    p M0 uBar vLower hData.out

/-- Single-target wrapper for Paper3 Lemma 3.1 from the core existence
bundle. -/
theorem intervalDomain_paper3_Lemma_3_1_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Lemma_3_1 intervalDomain p :=
  (intervalDomain_paper3_coreStatementTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).1

/-- Instance-facing single-target wrapper for Paper3 Lemma 3.1. -/
theorem intervalDomain_paper3_Lemma_3_1_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    Lemma_3_1 intervalDomain p :=
  intervalDomain_paper3_Lemma_3_1_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

/-- Single-target wrapper for Paper3 Lemma 3.3 from the core existence
bundle. -/
theorem intervalDomain_paper3_Lemma_3_3_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms :=
  (intervalDomain_paper3_coreStatementTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).2.1

/-- Instance-facing single-target wrapper for Paper3 Lemma 3.3. -/
theorem intervalDomain_paper3_Lemma_3_3_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms :=
  intervalDomain_paper3_Lemma_3_3_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

/-- Single-target wrapper for interval upper-envelope monotonicity from the
core existence bundle. -/
theorem intervalDomain_paper3_upperEnvelopeMonotonicity_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    UpperEnvelopeMonotonicityRaw intervalDomain p intervalDomain.supNorm :=
  (intervalDomain_paper3_coreStatementTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).2.2.1

/-- Instance-facing single-target wrapper for interval upper-envelope
monotonicity. -/
theorem intervalDomain_paper3_upperEnvelopeMonotonicity_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    UpperEnvelopeMonotonicityRaw intervalDomain p intervalDomain.supNorm :=
  intervalDomain_paper3_upperEnvelopeMonotonicity_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

/-- Single-target wrapper for the StabilityChain Theorem 2.1 target from the
core existence bundle. -/
theorem intervalDomain_paper3_stabilityChainTheorem21Target_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainStabilityChainTheorem21Target p M0 uBar vLower :=
  (intervalDomain_paper3_coreStatementTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).2.2.2.1

/-- Instance-facing single-target wrapper for the StabilityChain Theorem 2.1
target. -/
theorem
    intervalDomain_paper3_stabilityChainTheorem21Target_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    IntervalDomainStabilityChainTheorem21Target p M0 uBar vLower :=
  intervalDomain_paper3_stabilityChainTheorem21Target_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

/-- Single-target wrapper for the sectorial Theorem 2.1/2.2 target from the
core existence bundle. -/
theorem intervalDomain_paper3_sectorialTheorem21And22Target_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  (intervalDomain_paper3_coreStatementTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).2.2.2.2

/-- Instance-facing single-target wrapper for the sectorial Theorem 2.1/2.2
target. -/
theorem
    intervalDomain_paper3_sectorialTheorem21And22Target_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_paper3_sectorialTheorem21And22Target_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

/-- Concrete interval-domain Paper3 Theorem 2.1 target together with its four
part statements. -/
def IntervalDomainPaper3Theorem21PartTargets
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop :=
  Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) ∧
    Theorem_2_1_part1 intervalDomain p ∧
    Theorem_2_1_part2 intervalDomain p ∧
    Theorem_2_1_part3 intervalDomain p ∧
    Theorem_2_1_part4 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Single-target wrapper for concrete interval-domain Paper3 Theorem 2.1
from the persistence package alone.

This is the Theorem 2.1-specific entry point: it does not carry the sectorial
mainline existence package, and therefore does not require the local-stability
orbit comparison or small-data Cauchy existence fields used by Theorem 2.2. -/
theorem intervalDomain_paper3_Theorem_2_1_of_persistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hpersist : IntervalDomainSectorialTheorem21Persistence p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_for_concrete_constants_of_uniformPersistence_frontiers
    p M0 uBar vLower
    hpersist.part1 hpersist.part2 hpersist.part3 hpersist.part4

/-- Instance-facing concrete interval-domain Paper3 Theorem 2.1 wrapper from
the persistence package alone. -/
theorem intervalDomain_paper3_Theorem_2_1_of_persistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hpersist : Fact (IntervalDomainSectorialTheorem21Persistence p uBar)] :
    Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_1_of_persistence
    p M0 uBar vLower hpersist.out

/-- Assemble concrete interval-domain Paper3 Theorem 2.1 and all four part
statements from the persistence package alone. -/
theorem intervalDomain_paper3_Theorem_2_1_partTargets_of_persistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hpersist : IntervalDomainSectorialTheorem21Persistence p uBar) :
    IntervalDomainPaper3Theorem21PartTargets p M0 uBar vLower := by
  have h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainPaper3Constants p M0 uBar vLower) :=
    intervalDomain_paper3_Theorem_2_1_of_persistence
      p M0 uBar vLower hpersist
  exact ⟨h21, h21.1, h21.2.1, h21.2.2.1, h21.2.2.2⟩

/-- Instance-facing concrete interval-domain Paper3 Theorem 2.1 part-target
bundle from the persistence package alone. -/
theorem intervalDomain_paper3_Theorem_2_1_partTargets_of_persistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hpersist : Fact (IntervalDomainSectorialTheorem21Persistence p uBar)] :
    IntervalDomainPaper3Theorem21PartTargets p M0 uBar vLower :=
  intervalDomain_paper3_Theorem_2_1_partTargets_of_persistence
    p M0 uBar vLower hpersist.out

/-- Sectorial-constants interval-domain Paper3 Theorem 2.1 from the
persistence package alone. -/
theorem intervalDomain_paper3_Theorem_2_1_sectorial_of_persistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hpersist : IntervalDomainSectorialTheorem21Persistence p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_sectorialMainline_of_persistence
    p M0 uBar vLower hpersist

/-- Instance-facing sectorial-constants interval-domain Paper3 Theorem 2.1
from the persistence package alone. -/
theorem intervalDomain_paper3_Theorem_2_1_sectorial_of_persistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hpersist : Fact (IntervalDomainSectorialTheorem21Persistence p uBar)] :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_1_sectorial_of_persistence
    p M0 uBar vLower hpersist.out

/-- Single-target wrapper for the concrete interval-domain Paper3 Theorem
2.1 statement from the core existence bundle. -/
theorem intervalDomain_paper3_Theorem_2_1_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_stabilityChainTheorem21Target_of_coreExistence
    p M0 uBar vLower hcont hcore

/-- Instance-facing concrete interval-domain Paper3 Theorem 2.1 wrapper. -/
theorem intervalDomain_paper3_Theorem_2_1_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_1_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

/-- Assemble concrete interval-domain Paper3 Theorem 2.1 and all four part
statements from the core existence bundle. -/
theorem intervalDomain_paper3_Theorem_2_1_partTargets_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainPaper3Theorem21PartTargets p M0 uBar vLower := by
  have h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainPaper3Constants p M0 uBar vLower) :=
    intervalDomain_paper3_Theorem_2_1_of_coreExistence
      p M0 uBar vLower hcont hcore
  exact ⟨h21, h21.1, h21.2.1, h21.2.2.1, h21.2.2.2⟩

/-- Instance-facing concrete interval-domain Paper3 Theorem 2.1 part-target
bundle. -/
theorem intervalDomain_paper3_Theorem_2_1_partTargets_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcont : Fact (IntervalDomainInitialContinuityRaw p)]
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    IntervalDomainPaper3Theorem21PartTargets p M0 uBar vLower :=
  intervalDomain_paper3_Theorem_2_1_partTargets_of_coreExistence
    p M0 uBar vLower hcont.out hcore.out

/-- Single-target wrapper for Paper3 Theorem 2.1 part 1. -/
theorem intervalDomain_paper3_Theorem_2_1_part1_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_1_part1 intervalDomain p :=
  (intervalDomain_paper3_Theorem_2_1_partTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).2.1

/-- Single-target wrapper for Paper3 Theorem 2.1 part 2. -/
theorem intervalDomain_paper3_Theorem_2_1_part2_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_1_part2 intervalDomain p :=
  (intervalDomain_paper3_Theorem_2_1_partTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).2.2.1

/-- Single-target wrapper for Paper3 Theorem 2.1 part 3. -/
theorem intervalDomain_paper3_Theorem_2_1_part3_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_1_part3 intervalDomain p :=
  (intervalDomain_paper3_Theorem_2_1_partTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).2.2.2.1

/-- Single-target wrapper for Paper3 Theorem 2.1 part 4. -/
theorem intervalDomain_paper3_Theorem_2_1_part4_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_1_part4 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_paper3_Theorem_2_1_partTargets_of_coreExistence
    p M0 uBar vLower hcont hcore).2.2.2.2

/-- Single-target wrapper for the sectorial interval-domain Paper3 Theorem
2.2 statement from the core existence bundle. -/
theorem intervalDomain_paper3_Theorem_2_2_sectorial_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_paper3_sectorialTheorem21And22Target_of_coreExistence
    p M0 uBar vLower hcont hcore).1

/-- Single-target wrapper for the sectorial interval-domain Paper3 Theorem
2.1 statement from the core existence bundle. -/
theorem intervalDomain_paper3_Theorem_2_1_sectorial_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcont : IntervalDomainInitialContinuityRaw p)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_paper3_sectorialTheorem21And22Target_of_coreExistence
    p M0 uBar vLower hcont hcore).2

/-- Concrete interval-domain compactness/regularization targets closed by the
raw compactness, initial-continuity, minimal upper-bound, and Neumann-resolvent
frontiers. -/
def IntervalDomainPaper3CompactnessRegularizationTargets
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p) : Prop :=
  Lemma_3_1 intervalDomain p ∧
    Lemma_3_2 intervalDomain p K ∧
    Lemma_3_3 intervalDomain p N ∧
    Lemma_3_4 intervalDomain p K ∧
    Lemma_3_5 intervalDomain p C ∧
    Lemma_7_1 intervalDomain K

/-- Bundled raw frontiers for the interval-domain Paper3 compactness and
regularization targets.  The upper-envelope field is tied to the concrete
interval sup norm; the other fields remain the exposed analytic frontiers. -/
structure IntervalDomainPaper3CompactnessRegularizationData
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p) : Prop where
  upperEq :
    ∀ f : intervalDomain.Point → ℝ,
      K.upperEnvelope f = intervalDomain.supNorm f
  compact :
    TimeTranslateCompactnessRaw intervalDomain p K.locallyConverges
  initialContinuity :
    ∀ uStar > 0, InitialContinuityConclusion intervalDomain p N uStar
  minimalUpper :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            EventuallyUpperBoundMinimalConclusion intervalDomain p C u
  resolvent :
    NeumannResolventGradientBoundExistsRaw intervalDomain
      K.neumannResolventGradientBound

/-- Bundled compactness/regularization statement-target assembly on the
interval domain. -/
theorem intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hData :
      IntervalDomainPaper3CompactnessRegularizationData p K N C) :
    IntervalDomainPaper3CompactnessRegularizationTargets p K N C :=
  intervalDomain_compactness_regularization_support_of_frontiers
    p K N C hData.upperEq hData.compact hData.initialContinuity
    hData.minimalUpper hData.resolvent

/-- Instance-facing compactness/regularization statement-target assembly on
the interval domain. -/
theorem intervalDomain_paper3_compactnessRegularizationTargets_of_frontiersFact
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    [hData : Fact
      (IntervalDomainPaper3CompactnessRegularizationData p K N C)] :
    IntervalDomainPaper3CompactnessRegularizationTargets p K N C :=
  intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers
    p K N C hData.out

/-- Single-target wrapper for Paper3 Lemma 3.2 from the compactness bundle. -/
theorem intervalDomain_paper3_Lemma_3_2_of_compactnessRegularizationData
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3CompactnessRegularizationData p K N C) :
    Lemma_3_2 intervalDomain p K :=
  (intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers
    p K N C hData).2.1

/-- Instance-facing single-target wrapper for Paper3 Lemma 3.2. -/
theorem intervalDomain_paper3_Lemma_3_2_of_compactnessRegularizationDataFact
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    [hData : Fact
      (IntervalDomainPaper3CompactnessRegularizationData p K N C)] :
    Lemma_3_2 intervalDomain p K :=
  intervalDomain_paper3_Lemma_3_2_of_compactnessRegularizationData
    p K N C hData.out

/-- Single-target wrapper for Paper3 Lemma 3.3 from the compactness bundle. -/
theorem intervalDomain_paper3_Lemma_3_3_of_compactnessRegularizationData
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3CompactnessRegularizationData p K N C) :
    Lemma_3_3 intervalDomain p N :=
  (intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers
    p K N C hData).2.2.1

/-- Instance-facing single-target wrapper for Paper3 Lemma 3.3. -/
theorem intervalDomain_paper3_Lemma_3_3_of_compactnessRegularizationDataFact
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    [hData : Fact
      (IntervalDomainPaper3CompactnessRegularizationData p K N C)] :
    Lemma_3_3 intervalDomain p N :=
  intervalDomain_paper3_Lemma_3_3_of_compactnessRegularizationData
    p K N C hData.out

/-- Single-target wrapper for Paper3 Lemma 3.4 from the compactness bundle. -/
theorem intervalDomain_paper3_Lemma_3_4_of_compactnessRegularizationData
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3CompactnessRegularizationData p K N C) :
    Lemma_3_4 intervalDomain p K :=
  (intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers
    p K N C hData).2.2.2.1

/-- Instance-facing single-target wrapper for Paper3 Lemma 3.4. -/
theorem intervalDomain_paper3_Lemma_3_4_of_compactnessRegularizationDataFact
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    [hData : Fact
      (IntervalDomainPaper3CompactnessRegularizationData p K N C)] :
    Lemma_3_4 intervalDomain p K :=
  intervalDomain_paper3_Lemma_3_4_of_compactnessRegularizationData
    p K N C hData.out

/-- Single-target wrapper for Paper3 Lemma 3.5 from the compactness bundle. -/
theorem intervalDomain_paper3_Lemma_3_5_of_compactnessRegularizationData
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3CompactnessRegularizationData p K N C) :
    Lemma_3_5 intervalDomain p C :=
  (intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers
    p K N C hData).2.2.2.2.1

/-- Instance-facing single-target wrapper for Paper3 Lemma 3.5. -/
theorem intervalDomain_paper3_Lemma_3_5_of_compactnessRegularizationDataFact
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    [hData : Fact
      (IntervalDomainPaper3CompactnessRegularizationData p K N C)] :
    Lemma_3_5 intervalDomain p C :=
  intervalDomain_paper3_Lemma_3_5_of_compactnessRegularizationData
    p K N C hData.out

/-- Single-target wrapper for Paper3 Lemma 7.1 from the compactness bundle. -/
theorem intervalDomain_paper3_Lemma_7_1_of_compactnessRegularizationData
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3CompactnessRegularizationData p K N C) :
    Lemma_7_1 intervalDomain K :=
  (intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers
    p K N C hData).2.2.2.2.2

/-- Instance-facing single-target wrapper for Paper3 Lemma 7.1. -/
theorem intervalDomain_paper3_Lemma_7_1_of_compactnessRegularizationDataFact
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    [hData : Fact
      (IntervalDomainPaper3CompactnessRegularizationData p K N C)] :
    Lemma_7_1 intervalDomain K :=
  intervalDomain_paper3_Lemma_7_1_of_compactnessRegularizationData
    p K N C hData.out

/-- Bundled raw frontiers for the concrete interval constants and concrete
interval stability norms. -/
structure IntervalDomainPaper3ConcreteCompactnessRegularizationData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  upperEq :
    ∀ f : intervalDomain.Point → ℝ,
      K.upperEnvelope f = intervalDomain.supNorm f
  compact :
    TimeTranslateCompactnessRaw intervalDomain p K.locallyConverges
  initialContinuity : IntervalDomainInitialContinuityRaw p
  minimalUpper :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            EventuallyUpperBoundMinimalConclusion intervalDomain p
              (intervalDomainPaper3Constants p M0 uBar vLower) u
  resolvent :
    NeumannResolventGradientBoundExistsRaw intervalDomain
      K.neumannResolventGradientBound

/-- Compactness data on the interval with the upper envelope fixed to the
concrete interval sup norm.  The convergence relation and Neumann-resolvent
bound predicate remain parameters, so this only removes the structural
`upperEq` field from routes that choose this compactness package. -/
def intervalDomainSupNormCompactnessData
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) :
    CompactnessData intervalDomain where
  locallyConverges := locallyConverges
  upperEnvelope := intervalDomain.supNorm
  neumannResolventGradientBound := neumannResolventGradientBound

@[simp] theorem intervalDomainSupNormCompactnessData_upperEnvelope
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (f : intervalDomain.Point → ℝ) :
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound).upperEnvelope f =
      intervalDomain.supNorm f :=
  rfl

/-- Concrete-constants compactness/regularization data for the canonical
sup-envelope compactness package.  This omits only the structural `upperEq`
field; compactness, initial continuity, minimal upper bounds, and resolvent
estimates remain explicit analytic frontiers. -/
structure IntervalDomainPaper3SupNormCompactnessRegularizationData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop) : Prop where
  compact :
    TimeTranslateCompactnessRaw intervalDomain p locallyConverges
  initialContinuity : IntervalDomainInitialContinuityRaw p
  minimalUpper :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      0 < p.χ₀ → p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) →
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            EventuallyUpperBoundMinimalConclusion intervalDomain p
              (intervalDomainPaper3Constants p M0 uBar vLower) u
  resolvent :
    NeumannResolventGradientBoundExistsRaw intervalDomain
      neumannResolventGradientBound

/-- Convert the canonical sup-envelope compactness package to the existing
concrete compactness data by filling `upperEq` definitionally. -/
def IntervalDomainPaper3SupNormCompactnessRegularizationData.toConcrete
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop}
    {neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop}
    (h : IntervalDomainPaper3SupNormCompactnessRegularizationData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) where
  upperEq := by
    intro f
    rfl
  compact := h.compact
  initialContinuity := h.initialContinuity
  minimalUpper := h.minimalUpper
  resolvent := h.resolvent

/-- Concrete-constants compactness/regularization statement-target assembly on
the interval domain. -/
theorem
    intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K) :
    IntervalDomainPaper3CompactnessRegularizationTargets p K
      intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) := by
  refine
    intervalDomain_paper3_compactnessRegularizationTargets_of_frontiers
      p K intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower)
      ?_
  refine
    { upperEq := hData.upperEq
      compact := hData.compact
      initialContinuity := ?_
      minimalUpper := hData.minimalUpper
      resolvent := hData.resolvent }
  intro uStar huStar
  simpa [IntervalDomainInitialContinuityRaw, InitialContinuityRaw,
    InitialContinuityConclusion] using hData.initialContinuity uStar huStar

/-- Instance-facing concrete-constants compactness/regularization
statement-target assembly on the interval domain. -/
theorem
    intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiersFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3CompactnessRegularizationTargets p K
      intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    p M0 uBar vLower K hData.out

/-- Concrete-constants compactness/regularization targets for the canonical
sup-envelope compactness package.  This is a wrapper only; it does not produce
the analytic compactness, initial-continuity, minimal-upper, or resolvent
frontiers. -/
theorem
    intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_supNormData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (hData : IntervalDomainPaper3SupNormCompactnessRegularizationData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound) :
    IntervalDomainPaper3CompactnessRegularizationTargets p
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound)
      intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    p M0 uBar vLower
    (intervalDomainSupNormCompactnessData
      locallyConverges neumannResolventGradientBound)
    hData.toConcrete

/-- Instance-facing sup-envelope compactness/regularization wrapper. -/
theorem
    intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_supNormDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    [hData : Fact (IntervalDomainPaper3SupNormCompactnessRegularizationData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound)] :
    IntervalDomainPaper3CompactnessRegularizationTargets p
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound)
      intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_supNormData
    p M0 uBar vLower locallyConverges
    neumannResolventGradientBound hData.out

/-- Single-target wrapper for concrete Paper3 Lemma 3.2 from the concrete
compactness bundle. -/
theorem intervalDomain_paper3_Lemma_3_2_of_concreteCompactnessData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K) :
    Lemma_3_2 intervalDomain p K :=
  (intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    p M0 uBar vLower K hData).2.1

/-- Instance-facing single-target wrapper for concrete Paper3 Lemma 3.2. -/
theorem intervalDomain_paper3_Lemma_3_2_of_concreteCompactnessDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K)] :
    Lemma_3_2 intervalDomain p K :=
  intervalDomain_paper3_Lemma_3_2_of_concreteCompactnessData
    p M0 uBar vLower K hData.out

/-- Single-target wrapper for concrete Paper3 Lemma 3.3 from the concrete
compactness bundle. -/
theorem intervalDomain_paper3_Lemma_3_3_of_concreteCompactnessData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K) :
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms :=
  (intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    p M0 uBar vLower K hData).2.2.1

/-- Instance-facing single-target wrapper for concrete Paper3 Lemma 3.3. -/
theorem intervalDomain_paper3_Lemma_3_3_of_concreteCompactnessDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K)] :
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms :=
  intervalDomain_paper3_Lemma_3_3_of_concreteCompactnessData
    p M0 uBar vLower K hData.out

/-- Single-target wrapper for concrete Paper3 Lemma 3.4 from the concrete
compactness bundle. -/
theorem intervalDomain_paper3_Lemma_3_4_of_concreteCompactnessData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K) :
    Lemma_3_4 intervalDomain p K :=
  (intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    p M0 uBar vLower K hData).2.2.2.1

/-- Instance-facing single-target wrapper for concrete Paper3 Lemma 3.4. -/
theorem intervalDomain_paper3_Lemma_3_4_of_concreteCompactnessDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K)] :
    Lemma_3_4 intervalDomain p K :=
  intervalDomain_paper3_Lemma_3_4_of_concreteCompactnessData
    p M0 uBar vLower K hData.out

/-- Single-target wrapper for concrete Paper3 Lemma 3.5 from the concrete
compactness bundle. -/
theorem intervalDomain_paper3_Lemma_3_5_of_concreteCompactnessData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K) :
    Lemma_3_5 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    p M0 uBar vLower K hData).2.2.2.2.1

/-- Instance-facing single-target wrapper for concrete Paper3 Lemma 3.5. -/
theorem intervalDomain_paper3_Lemma_3_5_of_concreteCompactnessDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K)] :
    Lemma_3_5 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Lemma_3_5_of_concreteCompactnessData
    p M0 uBar vLower K hData.out

/-- Single-target wrapper for concrete Paper3 Lemma 7.1 from the concrete
compactness bundle. -/
theorem intervalDomain_paper3_Lemma_7_1_of_concreteCompactnessData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K) :
    Lemma_7_1 intervalDomain K :=
  (intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
    p M0 uBar vLower K hData).2.2.2.2.2

/-- Instance-facing single-target wrapper for concrete Paper3 Lemma 7.1. -/
theorem intervalDomain_paper3_Lemma_7_1_of_concreteCompactnessDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3ConcreteCompactnessRegularizationData
        p M0 uBar vLower K)] :
    Lemma_7_1 intervalDomain K :=
  intervalDomain_paper3_Lemma_7_1_of_concreteCompactnessData
    p M0 uBar vLower K hData.out

/-- Concrete-norm Paper3 stability targets currently closed by the
global-convergence and exponential-upgrade frontiers. -/
def IntervalDomainPaper3Stability23To25Targets
    (p : CM2Params) (C : Paper3Constants intervalDomain p) : Prop :=
  Theorem_2_3 intervalDomain p intervalDomainStabilityNorms ∧
    Theorem_2_4 intervalDomain p intervalDomainStabilityNorms C ∧
    Theorem_2_5 intervalDomain p intervalDomainStabilityNorms C

/-- Bundled frontiers for the concrete-norm Paper3 Theorem 2.3--2.5
stability package. -/
structure IntervalDomainPaper3Stability23To25FrontierData
    (p : CM2Params) (C : Paper3Constants intervalDomain p) : Prop where
  globalNonminimal23 :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        GloballyAsymptoticallyStableNonminimal intervalDomain p
          eq.1 eq.2
  globalMinimal23 :
    p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        GloballyAsymptoticallyStableMinimal intervalDomain p
          eq.1 eq.2
  expNonminimal23 :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        ∃ A > 0, ∃ rate > 0,
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
            UniformConvergesInSup intervalDomain u eq.1 →
              ExponentialC1ConvergenceWith intervalDomain
                intervalDomainStabilityNorms u v eq.1 eq.2 A rate
  expMinimal23 :
    p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        ∃ A > 0, ∃ rate > 0,
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
            HasInitialMass intervalDomain u uStar →
            UniformConvergesInSup intervalDomain u eq.1 →
              ExponentialC1ConvergenceWith intervalDomain
                intervalDomainStabilityNorms u v eq.1 eq.2 A rate
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
  global25 :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        MinimalGlobalStabilityCondition intervalDomain p C uStar →
          GloballyAsymptoticallyStableMinimal intervalDomain p
            eq.1 eq.2
  exp25 :
    p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
      ∀ uStar > 0,
        let eq := minimalEquilibrium p uStar
        MinimalGlobalStabilityCondition intervalDomain p C uStar →
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
              UniformConvergesInSup intervalDomain u eq.1 →
                ExponentialC1ConvergenceWith intervalDomain
                  intervalDomainStabilityNorms u v eq.1 eq.2 A rate

/-- Bundled concrete-norm Paper3 Theorem 2.3--2.5 assembly. -/
theorem intervalDomain_paper3_stability23To25Targets_of_frontiers
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3Stability23To25FrontierData p C) :
    IntervalDomainPaper3Stability23To25Targets p C :=
  intervalDomain_Theorem_2_3_to_2_5_for_concreteStabilityNorms_of_frontiers
    p C hData.globalNonminimal23 hData.globalMinimal23
    hData.expNonminimal23 hData.expMinimal23 hData.global24 hData.exp24
    hData.global25 hData.exp25

/-- Instance-facing bundled concrete-norm Paper3 Theorem 2.3--2.5 assembly. -/
theorem intervalDomain_paper3_stability23To25Targets_of_frontiersFact
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    [hData : Fact (IntervalDomainPaper3Stability23To25FrontierData p C)] :
    IntervalDomainPaper3Stability23To25Targets p C :=
  intervalDomain_paper3_stability23To25Targets_of_frontiers p C hData.out

/-- Single-target wrapper for Paper3 Theorem 2.3 from the stability bundle. -/
theorem intervalDomain_paper3_Theorem_2_3_of_stability23To25Data
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3Stability23To25FrontierData p C) :
    Theorem_2_3 intervalDomain p intervalDomainStabilityNorms :=
  (intervalDomain_paper3_stability23To25Targets_of_frontiers
    p C hData).1

/-- Instance-facing single-target wrapper for Paper3 Theorem 2.3. -/
theorem intervalDomain_paper3_Theorem_2_3_of_stability23To25DataFact
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    [hData : Fact (IntervalDomainPaper3Stability23To25FrontierData p C)] :
    Theorem_2_3 intervalDomain p intervalDomainStabilityNorms :=
  intervalDomain_paper3_Theorem_2_3_of_stability23To25Data
    p C hData.out

/-- Single-target wrapper for Paper3 Theorem 2.4 from the stability bundle. -/
theorem intervalDomain_paper3_Theorem_2_4_of_stability23To25Data
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3Stability23To25FrontierData p C) :
    Theorem_2_4 intervalDomain p intervalDomainStabilityNorms C :=
  (intervalDomain_paper3_stability23To25Targets_of_frontiers
    p C hData).2.1

/-- Instance-facing single-target wrapper for Paper3 Theorem 2.4. -/
theorem intervalDomain_paper3_Theorem_2_4_of_stability23To25DataFact
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    [hData : Fact (IntervalDomainPaper3Stability23To25FrontierData p C)] :
    Theorem_2_4 intervalDomain p intervalDomainStabilityNorms C :=
  intervalDomain_paper3_Theorem_2_4_of_stability23To25Data
    p C hData.out

/-- Single-target wrapper for Paper3 Theorem 2.5 from the stability bundle. -/
theorem intervalDomain_paper3_Theorem_2_5_of_stability23To25Data
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    (hData : IntervalDomainPaper3Stability23To25FrontierData p C) :
    Theorem_2_5 intervalDomain p intervalDomainStabilityNorms C :=
  (intervalDomain_paper3_stability23To25Targets_of_frontiers
    p C hData).2.2

/-- Instance-facing single-target wrapper for Paper3 Theorem 2.5. -/
theorem intervalDomain_paper3_Theorem_2_5_of_stability23To25DataFact
    (p : CM2Params) (C : Paper3Constants intervalDomain p)
    [hData : Fact (IntervalDomainPaper3Stability23To25FrontierData p C)] :
    Theorem_2_5 intervalDomain p intervalDomainStabilityNorms C :=
  intervalDomain_paper3_Theorem_2_5_of_stability23To25Data
    p C hData.out

/-- Concrete-constants Paper3 Theorem 2.3--2.5 target package. -/
def IntervalDomainPaper3ConcreteStability23To25Targets
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop :=
  IntervalDomainPaper3Stability23To25Targets p
    (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Concrete-constants bundled Paper3 Theorem 2.3--2.5 assembly. -/
theorem intervalDomain_paper3_concreteStability23To25Targets_of_frontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hData :
      IntervalDomainPaper3Stability23To25FrontierData p
        (intervalDomainPaper3Constants p M0 uBar vLower)) :
    IntervalDomainPaper3ConcreteStability23To25Targets
      p M0 uBar vLower :=
  intervalDomain_paper3_stability23To25Targets_of_frontiers
    p (intervalDomainPaper3Constants p M0 uBar vLower) hData

/-- Instance-facing concrete-constants Paper3 Theorem 2.3--2.5 assembly. -/
theorem intervalDomain_paper3_concreteStability23To25Targets_of_frontiersFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hData : Fact
      (IntervalDomainPaper3Stability23To25FrontierData p
        (intervalDomainPaper3Constants p M0 uBar vLower))] :
    IntervalDomainPaper3ConcreteStability23To25Targets
      p M0 uBar vLower :=
  intervalDomain_paper3_concreteStability23To25Targets_of_frontiers
    p M0 uBar vLower hData.out

/-- Single-target wrapper for concrete Paper3 Theorem 2.3 from the stability
bundle. -/
theorem intervalDomain_paper3_Theorem_2_3_of_concreteStabilityData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hData :
      IntervalDomainPaper3Stability23To25FrontierData p
        (intervalDomainPaper3Constants p M0 uBar vLower)) :
    Theorem_2_3 intervalDomain p intervalDomainStabilityNorms :=
  (intervalDomain_paper3_concreteStability23To25Targets_of_frontiers
    p M0 uBar vLower hData).1

/-- Instance-facing single-target wrapper for concrete Paper3 Theorem 2.3. -/
theorem intervalDomain_paper3_Theorem_2_3_of_concreteStabilityDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hData : Fact
      (IntervalDomainPaper3Stability23To25FrontierData p
        (intervalDomainPaper3Constants p M0 uBar vLower))] :
    Theorem_2_3 intervalDomain p intervalDomainStabilityNorms :=
  intervalDomain_paper3_Theorem_2_3_of_concreteStabilityData
    p M0 uBar vLower hData.out

/-- Single-target wrapper for concrete Paper3 Theorem 2.4 from the stability
bundle. -/
theorem intervalDomain_paper3_Theorem_2_4_of_concreteStabilityData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hData :
      IntervalDomainPaper3Stability23To25FrontierData p
        (intervalDomainPaper3Constants p M0 uBar vLower)) :
    Theorem_2_4 intervalDomain p intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_paper3_concreteStability23To25Targets_of_frontiers
    p M0 uBar vLower hData).2.1

/-- Instance-facing single-target wrapper for concrete Paper3 Theorem 2.4. -/
theorem intervalDomain_paper3_Theorem_2_4_of_concreteStabilityDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hData : Fact
      (IntervalDomainPaper3Stability23To25FrontierData p
        (intervalDomainPaper3Constants p M0 uBar vLower))] :
    Theorem_2_4 intervalDomain p intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_4_of_concreteStabilityData
    p M0 uBar vLower hData.out

/-- Single-target wrapper for concrete Paper3 Theorem 2.5 from the stability
bundle. -/
theorem intervalDomain_paper3_Theorem_2_5_of_concreteStabilityData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hData :
      IntervalDomainPaper3Stability23To25FrontierData p
        (intervalDomainPaper3Constants p M0 uBar vLower)) :
    Theorem_2_5 intervalDomain p intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_paper3_concreteStability23To25Targets_of_frontiers
    p M0 uBar vLower hData).2.2

/-- Instance-facing single-target wrapper for concrete Paper3 Theorem 2.5. -/
theorem intervalDomain_paper3_Theorem_2_5_of_concreteStabilityDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hData : Fact
      (IntervalDomainPaper3Stability23To25FrontierData p
        (intervalDomainPaper3Constants p M0 uBar vLower))] :
    Theorem_2_5 intervalDomain p intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_paper3_Theorem_2_5_of_concreteStabilityData
    p M0 uBar vLower hData.out

/-! ## Mainline umbrella targets -/

/-- Concrete interval-domain Paper3 mainline targets assembled from the
existing core-existence, compactness/regularization, and stability-frontier
packages. -/
def IntervalDomainPaper3MainlineTargets
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop :=
  IntervalDomainPaper3CoreStatementTargets p M0 uBar vLower ∧
    IntervalDomainPaper3Theorem21PartTargets p M0 uBar vLower ∧
      IntervalDomainPaper3CompactnessRegularizationTargets p K
        intervalDomainStabilityNorms
        (intervalDomainPaper3Constants p M0 uBar vLower) ∧
        IntervalDomainPaper3ConcreteStability23To25Targets
          p M0 uBar vLower

/-- Bundled frontiers for the concrete interval-domain Paper3 mainline
umbrella. -/
structure IntervalDomainPaper3MainlineFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainSectorialMainlineCoreExistence p uBar
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline umbrella from the
existing frontier records. -/
theorem intervalDomain_paper3_mainlineTargets_of_frontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3MainlineFrontierData p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  ⟨intervalDomain_paper3_coreStatementTargets_of_coreExistence
      p M0 uBar vLower hData.compactness.initialContinuity hData.core,
    intervalDomain_paper3_Theorem_2_1_partTargets_of_coreExistence
      p M0 uBar vLower hData.compactness.initialContinuity hData.core,
    intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
      p M0 uBar vLower K hData.compactness,
    intervalDomain_paper3_concreteStability23To25Targets_of_frontiers
      p M0 uBar vLower hData.stability⟩

/-- Instance-facing concrete interval-domain Paper3 mainline umbrella. -/
theorem intervalDomain_paper3_mainlineTargets_of_frontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3MainlineFrontierData p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_frontierData
    p M0 uBar vLower K hData.out

/-- Bundled interval-domain Paper3 mainline frontiers with Theorem 2.2 supplied
by direct raw linear-stability branches. -/
structure IntervalDomainPaper3MainlineLinear22FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainPaper3CoreStatementLinear22Data p M0 uBar vLower
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline umbrella from
direct raw linear Theorem 2.2 branches and the remaining frontier records. -/
theorem intervalDomain_paper3_mainlineTargets_of_linear22FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3MainlineLinear22FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  ⟨intervalDomain_paper3_coreStatementTargets_of_linear22Data
      p M0 uBar vLower hData.core,
    intervalDomain_paper3_Theorem_2_1_partTargets_of_persistence
      p M0 uBar vLower hData.core.persistence,
    intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers
      p M0 uBar vLower K hData.compactness,
    intervalDomain_paper3_concreteStability23To25Targets_of_frontiers
      p M0 uBar vLower hData.stability⟩

/-- Instance-facing concrete interval-domain Paper3 mainline umbrella from
direct raw linear Theorem 2.2 branches. -/
theorem intervalDomain_paper3_mainlineTargets_of_linear22FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3MainlineLinear22FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_linear22FrontierData
    p M0 uBar vLower K hData.out

/-- Thinner concrete interval-domain Paper3 mainline frontiers in which the
sectorial core package is supplied by reduced analytic facts.  The small-data
Cauchy fields stay explicit, while the four persistence fields are replaced by
pointwise lower-barrier facts. -/
structure IntervalDomainPaper3MainlineReducedAnalyticFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainSectorialMainlineReducedAnalyticFacts p uBar
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline umbrella from the
reduced analytic sectorial facts. -/
theorem intervalDomain_paper3_mainlineTargets_of_reducedAnalyticFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3MainlineReducedAnalyticFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_frontierData
    p M0 uBar vLower K
    { core := hData.core.to_coreExistence
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline umbrella from
the reduced analytic sectorial facts. -/
theorem intervalDomain_paper3_mainlineTargets_of_reducedAnalyticFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3MainlineReducedAnalyticFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_reducedAnalyticFrontierData
    p M0 uBar vLower K hData.out

/-- Thinner concrete interval-domain Paper3 mainline frontiers in which the
sectorial core package is supplied by the a-priori global-existence route.  The
small-data Cauchy fields are produced from continuation plus mass/Lp/smoothing
residuals; persistence is still supplied by pointwise lower-barrier facts. -/
structure IntervalDomainPaper3MainlineAprioriFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainSectorialMainlineAprioriFacts p uBar
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline umbrella from the
a-priori global-existence sectorial facts. -/
theorem intervalDomain_paper3_mainlineTargets_of_aprioriFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3MainlineAprioriFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_frontierData
    p M0 uBar vLower K
    { core := hData.core.to_coreExistence
      compactness := hData.compactness
      stability := hData.stability }

/-- Instance-facing concrete interval-domain Paper3 mainline umbrella from
the a-priori global-existence sectorial facts. -/
theorem intervalDomain_paper3_mainlineTargets_of_aprioriFrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3MainlineAprioriFrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_aprioriFrontierData
    p M0 uBar vLower K hData.out

/-! ## Full interval-domain statement targets -/

/-- Concrete interval-domain Paper3 statement targets combining the
Proposition 1.x package with the existing mainline umbrella. -/
def IntervalDomainPaper3StatementTargets
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop :=
  IntervalDomainPaper3Proposition1WithTheorem13Targets p C ∧
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K

/-- Bundled interval-domain Paper3 frontiers for the Proposition 1.x package
and the mainline umbrella. -/
structure IntervalDomainPaper3StatementFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline : IntervalDomainPaper3MainlineFrontierData p M0 uBar vLower K

/-- Assemble the concrete interval-domain Paper3 statement targets from the
existing Proposition 1.x and mainline frontier records. -/
theorem intervalDomain_paper3_statementTargets_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3StatementFrontierData p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_frontierData
      p M0 uBar vLower K hData.mainline⟩

/-- Instance-facing concrete interval-domain Paper3 statement-target wrapper. -/
theorem intervalDomain_paper3_statementTargets_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3StatementFrontierData p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_frontierData
    p C M0 uBar vLower K hData.out

/-- Bundled interval-domain Paper3 frontiers with the mainline Theorem 2.2
branch supplied by direct raw linear-stability data. -/
structure IntervalDomainPaper3StatementLinear22FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineLinear22FrontierData p M0 uBar vLower K

/-- Assemble the concrete interval-domain Paper3 statement targets using the
direct raw linear Theorem 2.2 mainline route. -/
theorem intervalDomain_paper3_statementTargets_of_linear22FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3StatementLinear22FrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_linear22FrontierData
      p M0 uBar vLower K hData.mainline⟩

/-- Instance-facing concrete interval-domain Paper3 statement-target wrapper
using the direct raw linear Theorem 2.2 mainline route. -/
theorem intervalDomain_paper3_statementTargets_of_linear22FrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3StatementLinear22FrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_linear22FrontierData
    p C M0 uBar vLower K hData.out

/-- Bundled interval-domain Paper3 frontiers with the mainline sectorial core
provided by reduced analytic facts. -/
structure IntervalDomainPaper3StatementReducedAnalyticFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineReducedAnalyticFrontierData
      p M0 uBar vLower K

/-- Assemble the concrete interval-domain Paper3 statement targets using the
reduced analytic sectorial mainline route. -/
theorem intervalDomain_paper3_statementTargets_of_reducedAnalyticFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3StatementReducedAnalyticFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_reducedAnalyticFrontierData
      p M0 uBar vLower K hData.mainline⟩

/-- Instance-facing concrete interval-domain Paper3 statement-target wrapper
using the reduced analytic sectorial mainline route. -/
theorem
    intervalDomain_paper3_statementTargets_of_reducedAnalyticFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3StatementReducedAnalyticFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_reducedAnalyticFrontierData
    p C M0 uBar vLower K hData.out

/-- Bundled interval-domain Paper3 frontiers with the mainline sectorial core
provided by the a-priori global-existence route. -/
structure IntervalDomainPaper3StatementAprioriFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineAprioriFrontierData p M0 uBar vLower K

/-- Assemble the concrete interval-domain Paper3 statement targets using the
a-priori global-existence sectorial mainline route. -/
theorem intervalDomain_paper3_statementTargets_of_aprioriFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (hData :
      IntervalDomainPaper3StatementAprioriFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_aprioriFrontierData
      p M0 uBar vLower K hData.mainline⟩

/-- Instance-facing concrete interval-domain Paper3 statement-target wrapper
using the a-priori global-existence sectorial mainline route. -/
theorem intervalDomain_paper3_statementTargets_of_aprioriFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    [hData : Fact
      (IntervalDomainPaper3StatementAprioriFrontierData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_aprioriFrontierData
    p C M0 uBar vLower K hData.out

section AxiomAudit

#print axioms intervalDomain_paper3_coreStatementTargets_of_linear22Data
#print axioms intervalDomain_paper3_mainlineTargets_of_linear22FrontierData
#print axioms intervalDomain_paper3_statementTargets_of_linear22FrontierData
#print axioms intervalDomain_paper3_mainlineTargets_of_reducedAnalyticFrontierData
#print axioms intervalDomain_paper3_statementTargets_of_reducedAnalyticFrontierData
#print axioms intervalDomain_paper3_mainlineTargets_of_aprioriFrontierData
#print axioms intervalDomain_paper3_statementTargets_of_aprioriFrontierData

end AxiomAudit

end

end ShenWork.Paper3
