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

/-! ## Lemma 2.5 targets -/

/-- Paper1 Lemma 2.5 together with its Jensen-step support target. -/
def Paper1Lemma25Targets : Prop :=
  Lemma_2_5 ∧ Lemma_2_5_JensenStep

/-- Single-target wrapper for Paper1 Lemma 2.5. -/
theorem paper1_Lemma_2_5 : Lemma_2_5 :=
  Lemma_2_5_proved

/-- Single-target wrapper for the Paper1 Lemma 2.5 Jensen step. -/
theorem paper1_Lemma_2_5_JensenStep : Lemma_2_5_JensenStep :=
  Lemma_2_5_JensenStep_proved

/-- Bundle wrapper for the closed Paper1 Lemma 2.5 targets. -/
theorem paper1_lemma25Targets : Paper1Lemma25Targets :=
  ⟨paper1_Lemma_2_5, paper1_Lemma_2_5_JensenStep⟩

/-! ## Lemma 5.1 and 5.2 targets -/

/-- Frontier record for the Paper1 Lemma 5.1 resolvent and derivative-bound
inputs. -/
structure Paper1Lemma51FrontierData : Prop where
  resolvent :
    ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → V = frozenElliptic p U
  continuous :
    ∀ p : CMParams, ∀ c : ℝ, ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V → Continuous U
  deriv_tends :
    ∀ p : CMParams, ∀ c : ℝ, 2 < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        WaveDerivativeTendsZero U
  deriv_bound :
    ∀ p : CMParams, ∀ c : ℝ, 2 < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        c > p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) →
          ∃ B > 0, ∀ x, |deriv U x| ≤ B
  deriv_exp :
    ∀ p : CMParams, ∀ c : ℝ, 2 < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        c > max (p.γ + p.γ⁻¹)
          (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
          ∃ B1 B2, ∀ x,
            |deriv U x| ≤
              B1 * Real.exp (-(kappa c) * x) +
                B2 * Real.exp (-(kappa c) * p.γ * x)

/-- Frontier record for the Paper1 Lemma 5.2 monotonicity input. -/
structure Paper1Lemma52FrontierData : Prop where
  monotone :
    ∀ p : CMParams, ∀ c : ℝ,
      c > max (p.γ + p.γ⁻¹)
        (p.m * |p.χ| * (MChi p) ^ (p.m + p.γ - 1)) →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasWaveUpperTailBound p c U →
        ∀ x, deriv U x ≤ 0

/-- Paper1 Lemma 5.1, Lemma 5.2 explicit, and Lemma 5.2 targets. -/
def Paper1Lemma51And52Targets : Prop :=
  Lemma_5_1 ∧ Lemma_5_2_explicit ∧ Lemma_5_2

/-- Single-target wrapper for Paper1 Lemma 5.1. -/
theorem paper1_Lemma_5_1_of_frontierData
    (hData : Paper1Lemma51FrontierData) :
    Lemma_5_1 :=
  Lemma_5_1.of_resolvent_derivative_bounds hData.resolvent
    hData.continuous hData.deriv_tends hData.deriv_bound hData.deriv_exp

/-- Single-target wrapper for Paper1 Lemma 5.2 explicit. -/
theorem paper1_Lemma_5_2_explicit_of_frontierData
    (hData : Paper1Lemma52FrontierData) :
    Lemma_5_2_explicit :=
  Lemma_5_2_explicit_under_monotone hData.monotone

/-- Single-target wrapper for Paper1 Lemma 5.2. -/
theorem paper1_Lemma_5_2_of_frontierData
    (hData : Paper1Lemma52FrontierData) :
    Lemma_5_2 :=
  Lemma_5_2_under_monotone hData.monotone

/-- Bundle wrapper for Paper1 Lemma 5.1 and Lemma 5.2 targets. -/
theorem paper1_lemma51And52Targets_of_frontierData
    (h51 : Paper1Lemma51FrontierData)
    (h52 : Paper1Lemma52FrontierData) :
    Paper1Lemma51And52Targets :=
  ⟨paper1_Lemma_5_1_of_frontierData h51,
    paper1_Lemma_5_2_explicit_of_frontierData h52,
    paper1_Lemma_5_2_of_frontierData h52⟩

/-- Instance-facing wrapper for Paper1 Lemma 5.1 and Lemma 5.2 targets. -/
theorem paper1_lemma51And52Targets_of_frontierDataFact
    [h51 : Fact Paper1Lemma51FrontierData]
    [h52 : Fact Paper1Lemma52FrontierData] :
    Paper1Lemma51And52Targets :=
  paper1_lemma51And52Targets_of_frontierData h51.out h52.out

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
