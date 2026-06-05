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

/-- Single-target Paper1 Theorem 1.1 wrapper from the main-results data
bundle. -/
theorem paper1_Theorem_1_1_of_mainResultsData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainResultsData cStarStarFn) :
    Theorem_1_1 :=
  Theorem_1_1.of_mainResultsData hData

/-- Instance-facing Paper1 Theorem 1.1 wrapper from the main-results data
bundle. -/
theorem paper1_Theorem_1_1_of_mainResultsDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainResultsData cStarStarFn)] :
    Theorem_1_1 :=
  paper1_Theorem_1_1_of_mainResultsData hData.out

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

/-! ## Proposition 1.x targets -/

/-- Paper1 Proposition 1.1 and Proposition 1.2 targets. -/
def Paper1PropositionTargets : Prop :=
  Proposition_1_1 ∧ Proposition_1_2

/-- Frontier record for the Paper1 Cauchy existence, bounds, and convergence
inputs that close Propositions 1.1 and 1.2. -/
structure Paper1PropositionFrontierData : Prop where
  existence :
    ∀ p : CMParams,
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
        ∃ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v
  max_neg :
    ∀ p : CMParams, p.χ ≤ 0 →
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
        (∀ M, (∀ x, u₀ x ≤ M) →
          ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
        UniformLimsupLe u 1
  bound_pos :
    ∀ p : CMParams,
      (0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
        (0 < p.χ ∧
          p.χ <
            min ((p.m + p.γ - 1) / (2 * p.m - 1))
              ((p.m + p.γ - 1) / (p.γ - 1)) ∧
          p.α = p.m + p.γ - 1) →
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
        UniformEventuallyBounded u ∧
        (0 < p.χ → p.χ < 1 →
          UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α)))
  conv_neg :
    ∀ p : CMParams, p.χ ≤ 0 →
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      UniformlyPositive u₀ →
      ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
        UniformConvergesToConstant u 1
  conv_pos :
    ∀ p : CMParams, 0 < p.χ → p.χ < (1 / 2 : ℝ) →
      p.m + p.γ - 1 ≤ p.α →
      ∀ u₀ : ℝ → ℝ, NonnegativeInitialDatum u₀ →
      UniformlyPositive u₀ →
      ∀ u v : ℝ → ℝ → ℝ, IsGlobalCauchySolutionFrom p u₀ u v →
        UniformConvergesToConstant u 1

/-- Assemble Paper1 Propositions 1.1 and 1.2 from their existing separated
Cauchy-frontier theorem wrappers. -/
theorem paper1_propositionTargets_of_frontierData
    (hData : Paper1PropositionFrontierData) :
    Paper1PropositionTargets :=
  ⟨Proposition_1_1.of_global_existence_and_bounds
      hData.existence hData.max_neg hData.bound_pos,
    Proposition_1_2.of_global_existence_and_convergence
      (fun p u₀ hu₀ _hu₀_pos => hData.existence p u₀ hu₀)
      hData.conv_neg hData.conv_pos⟩

/-- Instance-facing wrapper for Paper1 Propositions 1.1 and 1.2. -/
theorem paper1_propositionTargets_of_frontierDataFact
    [hData : Fact Paper1PropositionFrontierData] :
    Paper1PropositionTargets :=
  paper1_propositionTargets_of_frontierData hData.out

/-- Single-target wrapper for Paper1 Proposition 1.1. -/
theorem paper1_Proposition_1_1_of_frontierData
    (hData : Paper1PropositionFrontierData) :
    Proposition_1_1 :=
  (paper1_propositionTargets_of_frontierData hData).1

/-- Single-target wrapper for Paper1 Proposition 1.2. -/
theorem paper1_Proposition_1_2_of_frontierData
    (hData : Paper1PropositionFrontierData) :
    Proposition_1_2 :=
  (paper1_propositionTargets_of_frontierData hData).2

end

end ShenWork.Paper1
