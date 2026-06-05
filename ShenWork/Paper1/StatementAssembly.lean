/-
  Paper1 statement-target assembly.

  This file packages the existing Paper1 statement-layer bridges from
  `Statements` and `Lemma25Helpers`.  It adds no new analytic frontier.
-/
import ShenWork.Paper1.Lemma25Helpers

namespace ShenWork.Paper1

noncomputable section

/-- The three main Paper1 statement targets. -/
def Paper1MainStatementTargets : Prop :=
  Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3

/-- Main Paper1 statement-target assembly from the existing main-results
frontier record. -/
theorem paper1_mainStatementTargets_of_mainResultsData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainResultsData cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_main_results_bundled cStarStarFn hData

/-- Instance-facing wrapper for the main Paper1 statement targets. -/
theorem paper1_mainStatementTargets_of_mainResultsDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainResultsData cStarStarFn)] :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_mainResultsData hData.out

/-- The B5 stability/uniqueness endpoints covered by the canonical mainline
existence package. -/
def Paper1MainlineStatementTargets : Prop :=
  Theorem_1_2 ∧ Theorem_1_3

/-- Mainline-existence assembly for Paper1 Theorems 1.2 and 1.3. -/
theorem paper1_mainlineStatementTargets_of_mainlineExistence
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hexist : Paper1MainlineExistence cStarStarFn) :
    Paper1MainlineStatementTargets :=
  Theorem_1_2_and_1_3.of_mainlineExistence hexist

/-- Instance-facing mainline-existence assembly for Paper1 Theorems 1.2 and
1.3. -/
theorem paper1_mainlineStatementTargets_of_mainlineExistenceFact
    {cStarStarFn : CMParams → ℝ → ℝ}
    [hexist : Fact (Paper1MainlineExistence cStarStarFn)] :
    Paper1MainlineStatementTargets :=
  paper1_mainlineStatementTargets_of_mainlineExistence hexist.out

/-- Single-target Paper1 Theorem 1.2 wrapper from the mainline existence
package. -/
theorem paper1_Theorem_1_2_of_mainlineExistence
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hexist : Paper1MainlineExistence cStarStarFn) :
    Theorem_1_2 :=
  (paper1_mainlineStatementTargets_of_mainlineExistence hexist).1

/-- Single-target Paper1 Theorem 1.3 wrapper from the mainline existence
package. -/
theorem paper1_Theorem_1_3_of_mainlineExistence
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hexist : Paper1MainlineExistence cStarStarFn) :
    Theorem_1_3 :=
  (paper1_mainlineStatementTargets_of_mainlineExistence hexist).2

end

end ShenWork.Paper1
