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

end

end ShenWork.Paper3
