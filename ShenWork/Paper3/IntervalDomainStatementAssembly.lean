/-
  Paper3 interval-domain statement-target assembly.

  This file only packages proved bridges from the interval-domain StabilityChain
  and Sectorial files.  It adds no new analytic frontier: the remaining
  hypotheses are the canonical core existence package and the concrete
  initial-continuity frontier already exposed downstream.
-/
import ShenWork.Paper3.IntervalDomainStabilityChain

open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

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

end

end ShenWork.Paper3
