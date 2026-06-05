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

end

end ShenWork.Paper2
