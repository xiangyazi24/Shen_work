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

end

end ShenWork.Paper2
