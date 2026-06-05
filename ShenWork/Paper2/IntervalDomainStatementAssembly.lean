/-
  Paper2 interval-domain statement-target assembly.

  This file only packages already-proved interval-domain bridges and existing
  statement-layer branch-data wrappers.  It adds no analytic estimate.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
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

/-- Single-target interval-domain wrapper for Lemma 2.7. -/
theorem intervalDomainPaper2_Lemma_2_7_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Lemma_2_7 intervalDomain :=
  Lemma_2_7.of_branchData hData

/-- Single-target interval-domain wrapper for Proposition 2.2. -/
theorem intervalDomainPaper2_Proposition_2_2_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_2 intervalDomain p :=
  Proposition_2_2.of_branchData hData

/-- Single-target interval-domain wrapper for Proposition 2.3. -/
theorem intervalDomainPaper2_Proposition_2_3_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_3 intervalDomain p :=
  Proposition_2_3.of_branchData hData

/-- Single-target interval-domain wrapper for Proposition 2.4. -/
theorem intervalDomainPaper2_Proposition_2_4_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_4 intervalDomain p :=
  Proposition_2_4.of_branchData hData

/-- Single-target interval-domain wrapper for Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_5 intervalDomain p :=
  Proposition_2_5.of_branchData hData

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
  Lemma_3_1_intervalDomain p

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

/-! ## Theorem 1.1 statement targets -/

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

/-! ## Main theorem bundles -/

/-- Concrete interval-domain Paper 2 main theorem targets. -/
def IntervalDomainPaper2MainTheoremTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Theorem_1_1 intervalDomain p ∧
    Theorem_1_2 intervalDomain p ∧
      Theorem_1_3 intervalDomain p C

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

end

end ShenWork.Paper2
