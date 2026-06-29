import ShenWork.Paper2.IntervalLemma31Closure
/-
  Paper2 interval-domain statement-target assembly.

  This file only packages already-proved interval-domain bridges and existing
  statement-layer branch-data wrappers.  It adds no analytic estimate.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
import ShenWork.Paper2.IntervalDomainTheorem12
import ShenWork.Paper2.IntervalDomainTheorem13

set_option linter.style.longLine false

open ShenWork.IntervalDomain

namespace ShenWork.Paper2

noncomputable section

/-! ## Section 2 statement targets -/

/-- Interval-domain Paper 2 section-2 targets covered by the existing bundled
bootstrap/estimate branch-data record. -/
def IntervalDomainPaper2BootstrapEstimateTargets (p : CM2Params) : Prop :=
  Lemma_2_6 intervalDomain ∧
    Lemma_2_7 intervalDomain ∧
      Proposition_2_2 intervalDomain p ∧
        Proposition_2_3 intervalDomain p ∧
          Proposition_2_4 intervalDomain p ∧
            Proposition_2_5 intervalDomain p

/-- Interval-domain wrapper for Lemmas 2.6--2.7 and Propositions 2.2--2.5
from the statement-layer branch-data package. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  lemma_2_6_2_7_and_propositions_2_2_to_2_5_of_branchData hData

/-- Instance-facing interval-domain wrapper for the section-2 target bundle. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Lemma 2.6. -/
theorem intervalDomainPaper2_Lemma_2_6_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Lemma_2_6 intervalDomain :=
  Lemma_2_6.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Lemma 2.6. -/
theorem intervalDomainPaper2_Lemma_2_6_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Lemma_2_6 intervalDomain :=
  intervalDomainPaper2_Lemma_2_6_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Lemma 2.7. -/
theorem intervalDomainPaper2_Lemma_2_7_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Lemma_2_7 intervalDomain :=
  Lemma_2_7.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Lemma 2.7. -/
theorem intervalDomainPaper2_Lemma_2_7_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Lemma_2_7 intervalDomain :=
  intervalDomainPaper2_Lemma_2_7_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Proposition 2.2. -/
theorem intervalDomainPaper2_Proposition_2_2_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_2 intervalDomain p :=
  Proposition_2_2.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Proposition
2.2. -/
theorem intervalDomainPaper2_Proposition_2_2_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Proposition_2_2 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_2_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Proposition 2.3. -/
theorem intervalDomainPaper2_Proposition_2_3_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_3 intervalDomain p :=
  Proposition_2_3.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Proposition
2.3. -/
theorem intervalDomainPaper2_Proposition_2_3_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Proposition_2_3 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_3_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Proposition 2.4. -/
theorem intervalDomainPaper2_Proposition_2_4_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_4 intervalDomain p :=
  Proposition_2_4.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Proposition
2.4. -/
theorem intervalDomainPaper2_Proposition_2_4_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Proposition_2_4 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_4_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_5 intervalDomain p :=
  Proposition_2_5.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Proposition
2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_branchData p hData.out

/-- Frontier data for interval-domain Corollary 2.1 assembled from the
statement-layer Moser branch and the PDE energy derivation. -/
structure IntervalDomainPaper2Corollary21FrontierData
    (p : CM2Params) : Prop where
  bootstrap : Paper2BootstrapEstimateBranchData intervalDomain p
  energyFromCrossDiffusion :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0

/-- Interval-domain Corollary 2.1 from the Moser branch and PDE energy
frontier. -/
theorem intervalDomainPaper2_Corollary_2_1_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Corollary21FrontierData p) :
    Corollary_2_1 intervalDomain p :=
  IntervalDomainCorollary21.Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
    p (Lemma_2_6.of_branchData hData.bootstrap)
    hData.energyFromCrossDiffusion

/-- Instance-facing interval-domain Corollary 2.1 wrapper. -/
theorem intervalDomainPaper2_Corollary_2_1_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Corollary21FrontierData p)] :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_frontierData p hData.out

/-- Bundle of interval-domain Corollary 2.1 with the section-2 targets already
available from the same bootstrap/estimate data. -/
def IntervalDomainPaper2Corollary21BootstrapTargets (p : CM2Params) : Prop :=
  Corollary_2_1 intervalDomain p ∧
    IntervalDomainPaper2BootstrapEstimateTargets p

/-- Combined interval-domain section-2 target wrapper including Corollary 2.1. -/
theorem intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Corollary21FrontierData p) :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  ⟨intervalDomainPaper2_Corollary_2_1_of_frontierData p hData,
    intervalDomainPaper2_bootstrapEstimateTargets_of_branchData
      p hData.bootstrap⟩

/-- Instance-facing combined section-2 target wrapper including Corollary 2.1. -/
theorem intervalDomainPaper2_corollary21BootstrapTargets_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Corollary21FrontierData p)] :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
    p hData.out

/-! ## Section 3 and 4 a priori statement targets -/

/-- Interval-domain Paper 2 a priori statement targets already available from
the maximum-principle branch and the interval GN frontier. -/
def IntervalDomainPaper2AprioriTargets (p : CM2Params) : Prop :=
  Lemma_3_1 intervalDomain p ∧ Lemma_4_1 intervalDomain p

/-- Single-target interval-domain wrapper for Lemma 3.1. -/
theorem intervalDomainPaper2_Lemma_3_1
    (p : CM2Params) :
    Lemma_3_1 intervalDomain p :=
  Lemma31Closure.Lemma_3_1_intervalDomain p

/-- Single-target interval-domain wrapper for Lemma 4.1 from the concrete GN
frontier. -/
theorem intervalDomainPaper2_Lemma_4_1_of_GN_frontier
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation) :
    Lemma_4_1 intervalDomain p :=
  IntervalDomainTheorem11Composite.Lemma_4_1_intervalDomain_of_GN_frontier
    p hGN

/-- Instance-facing interval-domain wrapper for Lemma 4.1. -/
theorem intervalDomainPaper2_Lemma_4_1_of_GN_frontierFact
    (p : CM2Params)
    [hGN : Fact IntervalDomainLemma41.IntervalDomainInterpolation] :
    Lemma_4_1 intervalDomain p :=
  intervalDomainPaper2_Lemma_4_1_of_GN_frontier p hGN.out

/-- Assemble the interval-domain Lemma 3.1 and Lemma 4.1 targets from the GN
frontier. -/
theorem intervalDomainPaper2_aprioriTargets_of_GN_frontier
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation) :
    IntervalDomainPaper2AprioriTargets p :=
  ⟨intervalDomainPaper2_Lemma_3_1 p,
    intervalDomainPaper2_Lemma_4_1_of_GN_frontier p hGN⟩

/-- Instance-facing assembly wrapper for interval-domain Lemma 3.1 and Lemma
4.1. -/
theorem intervalDomainPaper2_aprioriTargets_of_GN_frontierFact
    (p : CM2Params)
    [hGN : Fact IntervalDomainLemma41.IntervalDomainInterpolation] :
    IntervalDomainPaper2AprioriTargets p :=
  intervalDomainPaper2_aprioriTargets_of_GN_frontier p hGN.out

/-! ## Proposition 1.1 local-existence target -/

/-- Frontier data for interval-domain Paper 2 Proposition 1.1.  The first
field is the closed local-existence branch; the second is the genuine
maximal-time finite-horizon alternative. -/
structure IntervalDomainPaper2Proposition11FrontierData
    (p : CM2Params) : Prop where
  localExistence :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  finiteHorizonAlternative :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v →
      InitialTrace intervalDomain u₀ u →
        FiniteHorizonAlternative intervalDomain Tmax u ∧
        (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)

/-- Interval-domain Paper 2 Proposition 1.1 from local existence plus the
finite-horizon alternative frontier. -/
theorem intervalDomainPaper2_Proposition_1_1_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Proposition11FrontierData p) :
    Proposition_1_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.Proposition_1_1_intervalDomain_of_localExistence_and_finiteHorizonAlternative
    p hData.localExistence hData.finiteHorizonAlternative

/-- Instance-facing interval-domain Paper 2 Proposition 1.1 wrapper. -/
theorem intervalDomainPaper2_Proposition_1_1_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Proposition11FrontierData p)] :
    Proposition_1_1 intervalDomain p :=
  intervalDomainPaper2_Proposition_1_1_of_frontierData p hData.out

/-- Thinner interval-domain Paper 2 Proposition 1.1 frontier for the proved
`χ₀ = 0` route.  Local existence is produced internally by
`intervalDomain_localExistence_chiZero_unconditional`; only the independent
finite-horizon alternative remains. -/
structure IntervalDomainPaper2Proposition11ChiZeroFrontierData
    (p : CM2Params) : Prop where
  finiteHorizonAlternative :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v →
      InitialTrace intervalDomain u₀ u →
        FiniteHorizonAlternative intervalDomain Tmax u ∧
        (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)

/-- Interval-domain Paper 2 Proposition 1.1 in the proved `χ₀ = 0` route,
with local existence discharged internally. -/
theorem intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
    (p : CM2Params)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2Proposition11ChiZeroFrontierData p) :
    Proposition_1_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.Proposition_1_1_intervalDomain_of_localExistence_and_finiteHorizonAlternative
    p
    (fun _u₀ hu₀ =>
      intervalDomain_localExistence_chiZero_unconditional
        p hχ0 ha hb hα hγ hu₀)
    hData.finiteHorizonAlternative

/-- Instance-facing interval-domain Paper 2 Proposition 1.1 wrapper for the
proved `χ₀ = 0` route. -/
theorem intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierDataFact
    (p : CM2Params)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact (IntervalDomainPaper2Proposition11ChiZeroFrontierData p)] :
    Proposition_1_1 intervalDomain p :=
  intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
    p hχ0 ha hb hα hγ hData.out

/-! ## Theorem 1.1 statement targets -/

/-- Interval-domain Paper 2 Theorem 1.1 in the proved `χ₀ = 0` regime.

This entry point consumes no half-step frontier package; the local and uniform
existence inputs are produced internally by
`intervalDomain_theorem_1_1_chiZero_unconditional`. -/
theorem intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiZero_unconditional p hχ0 ha hb hα hγ

/-- Instance-facing interval-domain Paper 2 Theorem 1.1 in the proved
`χ₀ = 0` regime. -/
theorem intervalDomainPaper2_Theorem_1_1_chiZero_unconditionalFact
    (p : CM2Params) [hχ0 : Fact (p.χ₀ = 0)] [ha : Fact (0 < p.a)]
    [hb : Fact (0 < p.b)] [hα : Fact (1 ≤ p.α)] [hγ : Fact (1 ≤ p.γ)] :
    Theorem_1_1 intervalDomain p :=
  intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
    p hχ0.out ha.out hb.out hα.out hγ.out

/-- Paper 2 Theorem 1.1 from half-step H2-source Picard data, routed through
the existing gamma >= 1 interval-domain umbrella. -/
theorem intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
        p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepH2SourceFrontierCoreLocalData_bundled
    p hχ ha hb hγ_ge_one hData

/-- Instance-facing Theorem 1.1 wrapper from half-step H2-source Picard data. -/
theorem intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierDataFact
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
        p)] :
    Theorem_1_1 intervalDomain p :=
  intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierData
    p hχ ha hb hγ_ge_one hData.out

/-- Paper 2 Theorem 1.1 from half-step logistic-source Picard data, routed
through the existing gamma >= 1 interval-domain umbrella. -/
theorem intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
        p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepLogisticSourceFrontierCoreLocalData_bundled
    p hχ ha hb hγ_ge_one hData

/-- Instance-facing Theorem 1.1 wrapper from half-step logistic-source data. -/
theorem intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierDataFact
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
        p)] :
    Theorem_1_1 intervalDomain p :=
  intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierData
    p hχ ha hb hγ_ge_one hData.out

/-! ## Theorems 1.2 and 1.3 statement targets -/

/-- Joint frontier record for the interval-domain Theorem 1.2 and Theorem 1.3
statement targets. -/
structure IntervalDomainPaper2Theorem12And13FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  theorem12 : IntervalDomainTheorem12.IntervalDomainTheorem12FrontierData p S
  theorem13 : IntervalDomainTheorem13.IntervalDomainTheorem13FrontierData p C S

/-- Shared bootstrap conclusion used by the thinner Theorem 1.2/1.3
interpolation-frontier route. -/
abbrev IntervalDomainPaper2BootstrapOutput
    (p : CM2Params) (T : ℝ)
    (u v : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∃ rho > 0,
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
      ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
        LpPowerBoundedBefore intervalDomain p0 T u

/-- Dissipation-side input for the thinner interval-domain Theorem 1.2/1.3
route. -/
abbrev IntervalDomainPaper2DissipationFrontier : Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp, p0 ≤ pExp → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / pExp) * deriv
            (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤
        K * intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / pExp) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ pExp)

/-- Positivity of the gradient-conversion coefficient in the thinner
Theorem 1.2/1.3 route. -/
abbrev IntervalDomainPaper2GradientConstantPositive
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp, p0 ≤ pExp → 0 < cGrad u T rho p0 pExp

/-- Chain-rule gradient comparison in the thinner Theorem 1.2/1.3 route. -/
abbrev IntervalDomainPaper2GradientChainFrontier
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (pExp + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad u T rho p0 pExp * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)

/-- Mass-control input in the thinner Theorem 1.2/1.3 route. -/
abbrev IntervalDomainPaper2MassControlFrontier : Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp, p0 ≤ pExp → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
      Ceta * (intervalDomain.integral (u t)) ^ (pExp + rho) ≤ Cmass

/-- Power-integrability input in the thinner Theorem 1.2/1.3 route. -/
abbrev IntervalDomainPaper2PowerIntegrabilityFrontier : Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
        MeasureTheory.volume 0 1

/-- PDE bridge from cross-diffusion bootstrap to the Lp energy inequality. -/
abbrev IntervalDomainPaper2EnergyFromCrossDiffusionFrontier
    (p : CM2Params) : Prop :=
  ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
      LpBootstrapEnergyInequality intervalDomain u T rho p0

/-- Per-datum interval-domain local existence input. -/
abbrev IntervalDomainPaper2LocalExistenceFrontier
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u

/-- Continuation input turning bounded finite-time solutions into global
classical solutions. -/
abbrev IntervalDomainPaper2GlobalExtensionFrontier
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
  ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
    IsPaper2ClassicalSolution intervalDomain p Tmax u v →
    InitialTrace intervalDomain u₀ u →
      IsPaper2BoundedBefore intervalDomain Tmax u →
        1 ≤ p.m →
          IsPaper2GlobalClassicalSolution intervalDomain p u v

/-- Common interpolation/energy inputs shared by the thinner interval-domain
Theorem 1.2 and Theorem 1.3 route. -/
structure IntervalDomainPaper2InterpolationEnergyFrontierData
    (p : CM2Params)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  dissipation : IntervalDomainPaper2DissipationFrontier
  gradConstantPositive :
    IntervalDomainPaper2GradientConstantPositive cGrad
  gradientChain : IntervalDomainPaper2GradientChainFrontier cGrad
  massControl : IntervalDomainPaper2MassControlFrontier
  powerIntegrability : IntervalDomainPaper2PowerIntegrabilityFrontier
  energyFromCrossDiffusion :
    IntervalDomainPaper2EnergyFromCrossDiffusionFrontier p

/-- Thinner joint frontier for interval-domain Theorems 1.2 and 1.3.

Compared with `IntervalDomainPaper2Theorem12And13FrontierData`, this route no
longer carries `SemigroupEstimateData`, Lemma 2.1, Lemma 2.6, Lemma 4.1, or
Corollary 2.1 as theorem fields.  It exposes the interpolation/energy/positivity
route used by the existing Theorem 1.2/1.3 assemblies and replaces global
boundedness fields by eventual sup-norm frontiers. -/
structure IntervalDomainPaper2Theorem12And13InterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  common : IntervalDomainPaper2InterpolationEnergyFrontierData p cGrad
  prop25 : Proposition_2_5 intervalDomain p
  localExistence : IntervalDomainPaper2LocalExistenceFrontier p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Assemble the interval-domain Theorem 1.2 and Theorem 1.3 statement targets
from their existing frontier-data records. -/
theorem intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hData : IntervalDomainPaper2Theorem12And13FrontierData p C S) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  ⟨IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_frontierData
      p S hData.theorem12,
    IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_frontierData
      p C S hData.theorem13⟩

/-- Instance-facing joint wrapper for interval-domain Theorems 1.2 and 1.3. -/
theorem intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    [hData : Fact (IntervalDomainPaper2Theorem12And13FrontierData p C S)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
    p C S hData.out

/-- Assemble the interval-domain Theorem 1.2 and Theorem 1.3 statement targets
from the thinner interpolation/energy/positivity frontiers. -/
theorem intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13InterpolationFrontierData p C cGrad) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  ⟨IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_interpolation_frontier_solution_positivity
      p hData.common.interpolation cGrad
      hData.common.dissipation hData.common.gradConstantPositive
      hData.common.gradientChain hData.common.massControl
      hData.common.powerIntegrability
      hData.common.energyFromCrossDiffusion hData.prop25
      hData.localExistence hData.globalExtension
      hData.slowBootstrap hData.criticalBootstrap
      hData.criticalEventualSupBound,
    IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_interpolation_frontier_solution_positivity
      p C hData.common.interpolation cGrad
      hData.common.dissipation hData.common.gradConstantPositive
      hData.common.gradientChain hData.common.massControl
      hData.common.powerIntegrability
      hData.common.energyFromCrossDiffusion hData.prop25
      hData.localExistence hData.globalExtension
      hData.strongBootstrap hData.strongEventualSupBound⟩

/-- Instance-facing joint wrapper for interval-domain Theorems 1.2 and 1.3
from the thinner interpolation frontiers. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    [hData :
      Fact
        (IntervalDomainPaper2Theorem12And13InterpolationFrontierData
          p C cGrad)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
    p C cGrad hData.out

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.2. -/
theorem intervalDomainPaper2_Theorem_1_2_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hData : IntervalDomainPaper2Theorem12And13FrontierData p C S) :
    Theorem_1_2 intervalDomain p :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
    p C S hData).1

/-- Instance-facing interval-domain wrapper for Paper2 Theorem 1.2. -/
theorem intervalDomainPaper2_Theorem_1_2_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    [hData : Fact (IntervalDomainPaper2Theorem12And13FrontierData p C S)] :
    Theorem_1_2 intervalDomain p :=
  intervalDomainPaper2_Theorem_1_2_of_frontierData
    p C S hData.out

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.3. -/
theorem intervalDomainPaper2_Theorem_1_3_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hData : IntervalDomainPaper2Theorem12And13FrontierData p C S) :
    Theorem_1_3 intervalDomain p C :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
    p C S hData).2

/-- Instance-facing interval-domain wrapper for Paper2 Theorem 1.3. -/
theorem intervalDomainPaper2_Theorem_1_3_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    [hData : Fact (IntervalDomainPaper2Theorem12And13FrontierData p C S)] :
    Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorem_1_3_of_frontierData
    p C S hData.out

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.2 from the
thinner interpolation frontiers. -/
theorem intervalDomainPaper2_Theorem_1_2_of_interpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13InterpolationFrontierData p C cGrad) :
    Theorem_1_2 intervalDomain p :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
    p C cGrad hData).1

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.3 from the
thinner interpolation frontiers. -/
theorem intervalDomainPaper2_Theorem_1_3_of_interpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13InterpolationFrontierData p C cGrad) :
    Theorem_1_3 intervalDomain p C :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
    p C cGrad hData).2

/-! ## Main theorem bundles -/

/-- Concrete interval-domain Paper 2 main theorem targets. -/
def IntervalDomainPaper2MainTheoremTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Theorem_1_1 intervalDomain p ∧
    Theorem_1_2 intervalDomain p ∧
      Theorem_1_3 intervalDomain p C

/-- Main-theorem frontier record for the `χ₀ = 0` route.  Theorem 1.1 is
proved internally; only the independent Theorem 1.2/1.3 frontier remains. -/
structure IntervalDomainPaper2MainTheoremChiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13FrontierData p C S

/-- Main-theorem frontier record for the proved `χ₀ = 0` route using the
thinner interpolation-frontier Theorem 1.2/1.3 assembly.  This route carries
no `SemigroupEstimateData` package. -/
structure IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13InterpolationFrontierData p C cGrad

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 in the proved `χ₀ = 0`
route.  Compared with the H2/logistic-source routes, this carries no Theorem
1.1 local-existence frontier package. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2MainTheoremChiZeroFrontierData p C S) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
      p C S hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle in the proved
`χ₀ = 0` route. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact (IntervalDomainPaper2MainTheoremChiZeroFrontierData p C S)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 in the proved `χ₀ = 0`
route, with Theorems 1.2/1.3 supplied by the thinner interpolation-frontier
assembly. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
      p C cGrad hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle in the proved
`χ₀ = 0` route using the thinner interpolation-frontier Theorem 1.2/1.3
assembly. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Main-theorem frontier record using the half-step H2-source Theorem 1.1
route. -/
structure IntervalDomainPaper2MainTheoremH2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  theorem11 :
    IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
      p
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13FrontierData p C S

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 from the H2-source
local-existence route plus the existing Theorem 1.2/1.3 frontiers. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_H2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremH2SourceFrontierData p C S) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierData
      p hχ ha hb hγ_ge_one hData.theorem11,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
      p C S hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle from the H2-source
route. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_H2SourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremH2SourceFrontierData p C S)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_H2SourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Main-theorem frontier record using the half-step logistic-source Theorem
1.1 route. -/
structure IntervalDomainPaper2MainTheoremLogisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  theorem11 :
    IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
      p
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13FrontierData p C S

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 from the
logistic-source local-existence route plus the existing Theorem 1.2/1.3
frontiers. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_logisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremLogisticSourceFrontierData p C S) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierData
      p hχ ha hb hγ_ge_one hData.theorem11,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
      p C S hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle from the
logistic-source route. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_logisticSourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremLogisticSourceFrontierData p C S)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_logisticSourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Concrete interval-domain Paper 2 Proposition 1.1 together with the main
Theorems 1.1--1.3. -/
def IntervalDomainPaper2LocalAndMainTheoremTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Proposition_1_1 intervalDomain p ∧
    IntervalDomainPaper2MainTheoremTargets p C

/-- Local-plus-main frontier record for the proved `χ₀ = 0` Theorem 1.1
route. -/
structure IntervalDomainPaper2LocalAndMainChiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  proposition11 : IntervalDomainPaper2Proposition11FrontierData p
  main : IntervalDomainPaper2MainTheoremChiZeroFrontierData p C S

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
with Theorem 1.1 supplied by the proved `χ₀ = 0` route. -/
theorem intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2LocalAndMainChiZeroFrontierData p C S) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_frontierData
      p hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
      p C S hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper for the proved
`χ₀ = 0` Theorem 1.1 route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroFrontierData p C S)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Thinner local-plus-main frontier record for the proved `χ₀ = 0` route.
The Proposition 1.1 local-existence field is produced internally, so the local
side only carries the finite-horizon alternative. -/
structure IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  main : IntervalDomainPaper2MainTheoremChiZeroFrontierData p C S

/-- Local-plus-main frontier record for the proved `χ₀ = 0` route using the
thinner interpolation-frontier Theorem 1.2/1.3 assembly.  The Proposition 1.1
local-existence field is produced internally, and the main theorem route
carries no `SemigroupEstimateData`. -/
structure IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  main : IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData
    p C cGrad

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
in the proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData p C S) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
      p hχ0 ha hb hα hγ hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
      p C S hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper for the thinner
proved `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData p C S)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
in the proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally and Theorems 1.2/1.3 routed through the thinner interpolation
frontiers. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
      p hχ0 ha hb hα hγ hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper for the proved
`χ₀ = 0` route using the thinner interpolation-frontier Theorem 1.2/1.3
assembly. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Local-plus-main frontier record using the half-step H2-source Theorem 1.1
route. -/
structure IntervalDomainPaper2LocalAndMainH2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  proposition11 : IntervalDomainPaper2Proposition11FrontierData p
  main : IntervalDomainPaper2MainTheoremH2SourceFrontierData p C S

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
from the H2-source local-existence route. -/
theorem intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainH2SourceFrontierData p C S) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_frontierData
      p hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_H2SourceFrontierData
      p C S hχ ha hb hγ_ge_one hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper from the H2-source
route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainH2SourceFrontierData p C S)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Local-plus-main frontier record using the half-step logistic-source
Theorem 1.1 route. -/
structure IntervalDomainPaper2LocalAndMainLogisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  proposition11 : IntervalDomainPaper2Proposition11FrontierData p
  main : IntervalDomainPaper2MainTheoremLogisticSourceFrontierData p C S

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
from the logistic-source local-existence route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainLogisticSourceFrontierData p C S) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_frontierData
      p hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_logisticSourceFrontierData
      p C S hχ ha hb hγ_ge_one hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper from the
logistic-source route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainLogisticSourceFrontierData p C S)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-! ## Combined interval-domain statement targets -/

/-- Concrete interval-domain Paper 2 statement targets assembled from the
section-2 bootstrap/corollary package, the section-3/4 a priori package, and
the local-plus-main theorem package. -/
def IntervalDomainPaper2StatementTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2Corollary21BootstrapTargets p ∧
    IntervalDomainPaper2AprioriTargets p ∧
      IntervalDomainPaper2LocalAndMainTheoremTargets p C

/-- Interval-domain Paper 2 statement-frontier record for the proved
`χ₀ = 0` Theorem 1.1 route. -/
structure IntervalDomainPaper2StatementChiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain : IntervalDomainPaper2LocalAndMainChiZeroFrontierData p C S

/-- Assemble the concrete interval-domain Paper 2 statement targets with
Theorem 1.1 supplied by the proved `χ₀ = 0` route. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2StatementChiZeroFrontierData p C S) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroFrontierData
      p C S hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
proved `χ₀ = 0` Theorem 1.1 route. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact (IntervalDomainPaper2StatementChiZeroFrontierData p C S)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Thinner interval-domain Paper 2 statement-frontier record for the proved
`χ₀ = 0` route.  The Proposition 1.1 local-existence field is produced from
`intervalDomain_localExistence_chiZero_unconditional`. -/
structure IntervalDomainPaper2StatementChiZeroThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData p C S

/-- Thinner interval-domain Paper 2 statement-frontier record for the proved
`χ₀ = 0` route using the interpolation-frontier Theorem 1.2/1.3 assembly.
This removes the statement-level `SemigroupEstimateData` package from the
main theorem component. -/
structure IntervalDomainPaper2StatementChiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData
      p C cGrad

/-- Assemble the concrete interval-domain Paper 2 statement targets in the
proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2StatementChiZeroThinFrontierData p C S) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierData
      p C S hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
thinner proved `χ₀ = 0` route. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroThinFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact (IntervalDomainPaper2StatementChiZeroThinFrontierData p C S)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroThinFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets in the
proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally and Theorems 1.2/1.3 routed through the thinner interpolation
frontiers. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroInterpolationFrontierData p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
proved `χ₀ = 0` route using the thinner interpolation-frontier Theorem 1.2/1.3
assembly. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2StatementChiZeroInterpolationFrontierData
          p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Interval-domain Paper 2 statement-frontier record using the half-step
H2-source local-existence route. -/
structure IntervalDomainPaper2StatementH2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain : IntervalDomainPaper2LocalAndMainH2SourceFrontierData p C S

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
H2-source local-existence route. -/
theorem intervalDomainPaper2_statementTargets_of_H2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementH2SourceFrontierData p C S) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourceFrontierData
      p C S hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the H2-source local-existence route. -/
theorem intervalDomainPaper2_statementTargets_of_H2SourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementH2SourceFrontierData p C S)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_H2SourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Interval-domain Paper 2 statement-frontier record using the half-step
logistic-source local-existence route. -/
structure IntervalDomainPaper2StatementLogisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain :
    IntervalDomainPaper2LocalAndMainLogisticSourceFrontierData p C S

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
logistic-source local-existence route. -/
theorem intervalDomainPaper2_statementTargets_of_logisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementLogisticSourceFrontierData p C S) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourceFrontierData
      p C S hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the logistic-source local-existence route. -/
theorem intervalDomainPaper2_statementTargets_of_logisticSourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementLogisticSourceFrontierData p C S)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_logisticSourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

section AxiomAudit

#print axioms intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
#print axioms intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
#print axioms intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
#print axioms intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
#print axioms intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierData
#print axioms intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierData
#print axioms intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierData
#print axioms intervalDomainPaper2_statementTargets_of_chiZeroFrontierData
#print axioms intervalDomainPaper2_statementTargets_of_chiZeroThinFrontierData
#print axioms intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierData

end AxiomAudit

end

end ShenWork.Paper2
