/-
  Paper2 generic statement-target assembly.

  This file packages statement-layer branch-data bridges from `Statements`.
  It adds no analytic estimates.
-/
import ShenWork.Paper2.Statements

namespace ShenWork.Paper2

noncomputable section

/-! ## Lemma 2.6--2.7 and Proposition 2.2--2.5 targets -/

/-- Paper2 section-2 estimate targets covered by the bootstrap branch-data
package. -/
def Paper2BootstrapEstimateTargets
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  Lemma_2_6 D ∧
    Lemma_2_7 D ∧
      Proposition_2_2 D p ∧
        Proposition_2_3 D p ∧
          Proposition_2_4 D p ∧
            Proposition_2_5 D p

/-- Assemble Lemmas 2.6--2.7 and Propositions 2.2--2.5 from the
statement-layer branch-data package. -/
theorem paper2_bootstrapEstimateTargets_of_branchData
    {D : BoundedDomainData} {p : CM2Params}
    (hData : Paper2BootstrapEstimateBranchData D p) :
    Paper2BootstrapEstimateTargets D p :=
  lemma_2_6_2_7_and_propositions_2_2_to_2_5_of_branchData hData

/-- Instance-facing wrapper for the section-2 estimate target bundle. -/
theorem paper2_bootstrapEstimateTargets_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData D p)] :
    Paper2BootstrapEstimateTargets D p :=
  paper2_bootstrapEstimateTargets_of_branchData hData.out

/-- Single-target wrapper for Paper2 Lemma 2.6. -/
theorem paper2_Lemma_2_6_of_branchData
    {D : BoundedDomainData} {p : CM2Params}
    (hData : Paper2BootstrapEstimateBranchData D p) :
    Lemma_2_6 D :=
  Lemma_2_6.of_branchData hData

/-- Instance-facing wrapper for Paper2 Lemma 2.6. -/
theorem paper2_Lemma_2_6_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData D p)] :
    Lemma_2_6 D :=
  paper2_Lemma_2_6_of_branchData hData.out

/-- Single-target wrapper for Paper2 Lemma 2.7. -/
theorem paper2_Lemma_2_7_of_branchData
    {D : BoundedDomainData} {p : CM2Params}
    (hData : Paper2BootstrapEstimateBranchData D p) :
    Lemma_2_7 D :=
  Lemma_2_7.of_branchData hData

/-- Instance-facing wrapper for Paper2 Lemma 2.7. -/
theorem paper2_Lemma_2_7_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData D p)] :
    Lemma_2_7 D :=
  paper2_Lemma_2_7_of_branchData hData.out

/-- Single-target wrapper for Paper2 Proposition 2.2. -/
theorem paper2_Proposition_2_2_of_branchData
    {D : BoundedDomainData} {p : CM2Params}
    (hData : Paper2BootstrapEstimateBranchData D p) :
    Proposition_2_2 D p :=
  Proposition_2_2.of_branchData hData

/-- Instance-facing wrapper for Paper2 Proposition 2.2. -/
theorem paper2_Proposition_2_2_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData D p)] :
    Proposition_2_2 D p :=
  paper2_Proposition_2_2_of_branchData hData.out

/-- Single-target wrapper for Paper2 Proposition 2.3. -/
theorem paper2_Proposition_2_3_of_branchData
    {D : BoundedDomainData} {p : CM2Params}
    (hData : Paper2BootstrapEstimateBranchData D p) :
    Proposition_2_3 D p :=
  Proposition_2_3.of_branchData hData

/-- Instance-facing wrapper for Paper2 Proposition 2.3. -/
theorem paper2_Proposition_2_3_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData D p)] :
    Proposition_2_3 D p :=
  paper2_Proposition_2_3_of_branchData hData.out

/-- Single-target wrapper for Paper2 Proposition 2.4. -/
theorem paper2_Proposition_2_4_of_branchData
    {D : BoundedDomainData} {p : CM2Params}
    (hData : Paper2BootstrapEstimateBranchData D p) :
    Proposition_2_4 D p :=
  Proposition_2_4.of_branchData hData

/-- Instance-facing wrapper for Paper2 Proposition 2.4. -/
theorem paper2_Proposition_2_4_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData D p)] :
    Proposition_2_4 D p :=
  paper2_Proposition_2_4_of_branchData hData.out

/-- Single-target wrapper for Paper2 Proposition 2.5. -/
theorem paper2_Proposition_2_5_of_branchData
    {D : BoundedDomainData} {p : CM2Params}
    (hData : Paper2BootstrapEstimateBranchData D p) :
    Proposition_2_5 D p :=
  Proposition_2_5.of_branchData hData

/-- Instance-facing wrapper for Paper2 Proposition 2.5. -/
theorem paper2_Proposition_2_5_of_branchDataFact
    (D : BoundedDomainData) (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData D p)] :
    Proposition_2_5 D p :=
  paper2_Proposition_2_5_of_branchData hData.out

/-! ## Proposition 1.1 local-existence target -/

/-- Paper2 Proposition 1.1 target. -/
def Paper2Proposition11Target
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  Proposition_1_1 D p

/-- Branch data for Paper2 Proposition 1.1.  This is the exact local
existence/blow-up alternative target shape exposed by `Statements`. -/
structure Paper2Proposition11ExistenceData
    (D : BoundedDomainData) (p : CM2Params) : Prop where
  existence :
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          FiniteHorizonAlternative D Tmax u ∧
          (1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u)

/-- Assemble Paper2 Proposition 1.1 from its statement-layer existence
branch. -/
theorem paper2_Proposition_1_1_of_existenceData
    {D : BoundedDomainData} {p : CM2Params}
    (hData : Paper2Proposition11ExistenceData D p) :
    Paper2Proposition11Target D p :=
  Proposition_1_1.of_assumed_existence_branch hData.existence

/-- Instance-facing wrapper for Paper2 Proposition 1.1. -/
theorem paper2_Proposition_1_1_of_existenceDataFact
    (D : BoundedDomainData) (p : CM2Params)
    [hData : Fact (Paper2Proposition11ExistenceData D p)] :
    Paper2Proposition11Target D p :=
  paper2_Proposition_1_1_of_existenceData hData.out

/-! ## Theorem 1.1--1.3 targets -/

/-- Paper2 main theorem targets covered by the solution-branch package. -/
def Paper2MainTheoremTargets
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper2Constants p) : Prop :=
  Theorem_1_1 D p ∧ Theorem_1_2 D p ∧ Theorem_1_3 D p C

/-- Assemble Paper2 Theorems 1.1--1.3 from the statement-layer solution
branch-data package. -/
theorem paper2_mainTheoremTargets_of_solutionBranchData
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (hData : Paper2MainSolutionBranchData D p C) :
    Paper2MainTheoremTargets D p C :=
  paper2_main_results_of_solutionBranchData hData

/-- Instance-facing wrapper for Paper2 Theorems 1.1--1.3. -/
theorem paper2_mainTheoremTargets_of_solutionBranchDataFact
    (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p)
    [hData : Fact (Paper2MainSolutionBranchData D p C)] :
    Paper2MainTheoremTargets D p C :=
  paper2_mainTheoremTargets_of_solutionBranchData hData.out

/-- Paper2 Proposition 1.1 together with Theorems 1.1--1.3. -/
def Paper2LocalAndMainTheoremTargets
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper2Constants p) : Prop :=
  Proposition_1_1 D p ∧ Paper2MainTheoremTargets D p C

/-- Bundled data for Paper2 Proposition 1.1 and Theorems 1.1--1.3. -/
structure Paper2LocalAndMainTheoremData
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper2Constants p) : Prop where
  localExistence : Paper2Proposition11ExistenceData D p
  main : Paper2MainSolutionBranchData D p C

/-- Assemble Paper2 Proposition 1.1 and Theorems 1.1--1.3 from their existing
statement-layer data records. -/
theorem paper2_localAndMainTheoremTargets_of_data
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (hData : Paper2LocalAndMainTheoremData D p C) :
    Paper2LocalAndMainTheoremTargets D p C :=
  ⟨paper2_Proposition_1_1_of_existenceData hData.localExistence,
    paper2_mainTheoremTargets_of_solutionBranchData hData.main⟩

/-- Instance-facing wrapper for Paper2 Proposition 1.1 and Theorems
1.1--1.3. -/
theorem paper2_localAndMainTheoremTargets_of_dataFact
    (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p)
    [hData : Fact (Paper2LocalAndMainTheoremData D p C)] :
    Paper2LocalAndMainTheoremTargets D p C :=
  paper2_localAndMainTheoremTargets_of_data hData.out

/-! ## Combined statement targets -/

/-- Generic Paper2 statement targets currently covered by the existing
statement-layer branch-data packages. -/
def Paper2StatementTargets
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper2Constants p) : Prop :=
  Paper2BootstrapEstimateTargets D p ∧
    Paper2LocalAndMainTheoremTargets D p C

/-- Bundled generic Paper2 statement-target data. -/
structure Paper2StatementData
    (D : BoundedDomainData) (p : CM2Params)
    (C : Paper2Constants p) : Prop where
  bootstrap : Paper2BootstrapEstimateBranchData D p
  localAndMain : Paper2LocalAndMainTheoremData D p C

/-- Assemble generic Paper2 statement targets from the existing branch-data
records. -/
theorem paper2_statementTargets_of_data
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (hData : Paper2StatementData D p C) :
    Paper2StatementTargets D p C :=
  ⟨paper2_bootstrapEstimateTargets_of_branchData hData.bootstrap,
    paper2_localAndMainTheoremTargets_of_data hData.localAndMain⟩

/-- Instance-facing wrapper for generic Paper2 statement targets. -/
theorem paper2_statementTargets_of_dataFact
    (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p)
    [hData : Fact (Paper2StatementData D p C)] :
    Paper2StatementTargets D p C :=
  paper2_statementTargets_of_data hData.out

end

end ShenWork.Paper2
