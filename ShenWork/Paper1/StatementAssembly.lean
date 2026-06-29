/-
  Paper1 statement-target assembly.

  This file packages the existing Paper1 statement-layer bridges from
  `Statements` and `Lemma25Helpers`.  It adds no new analytic frontier.
-/
import ShenWork.Paper1.Lemma25Helpers
import ShenWork.Paper1.StationaryUpperTail

namespace ShenWork.Paper1

noncomputable section

/-- The three main Paper1 statement targets. -/
def Paper1MainStatementTargets : Prop :=
  Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3

/-- Main Paper1 statement-target assembly from the existing main-results
frontier record.

Conditional interface: this theorem does not construct `Paper1MainResultsData`.
It only turns that package into `Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3`.
The closed no-frontier component in this file is `paper1_lemma25Targets`. -/
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

/-- Single-target Paper1 Theorem 1.1 wrapper using the weakened negative
construction provider.  The negative branch no longer carries
`ShenUpperBoundNegative` directly; it carries the scalar strictness `U 0 < 1`
through `ConstructionNegSMPProvider`.

Still conditional: both `hneg : ConstructionNegSMPProvider` and the positive
branch `hpos` are headline construction inputs. -/
theorem paper1_Theorem_1_1_of_constructionNegSMPProvider
    (hneg : ConstructionNegSMPProvider)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ < min ((1 + p.α) * kappa c)
                  (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 :=
  Theorem_1_1.of_constructionNeg_provider_smp hneg hpos

/-- Instance-facing Paper1 Theorem 1.1 wrapper from the weakened negative
construction provider. -/
theorem paper1_Theorem_1_1_of_constructionNegSMPProviderFact
    [hneg : Fact ConstructionNegSMPProvider]
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ < min ((1 + p.α) * kappa c)
                  (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 :=
  paper1_Theorem_1_1_of_constructionNegSMPProvider hneg.out hpos

/-- The B5 stability/uniqueness endpoints covered by the canonical mainline
existence package. -/
def Paper1MainlineStatementTargets : Prop :=
  Theorem_1_2 ∧ Theorem_1_3

/-- Mainline-existence assembly for Paper1 Theorems 1.2 and 1.3.

Conditional interface: `Paper1MainlineExistence` is the B5 mainline input
package.  This wrapper does not construct that package. -/
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

/-- Positive critical frozen-stationary branch used with
`ConstructionNegSMPProvider` to prove Paper1 Theorem 1.1.

This is the existing `hpos` argument of
`paper1_Theorem_1_1_of_constructionNegSMPProvider`, factored out so the
preferred bundled main wrapper exposes every remaining input explicitly.

This remains a genuine positive-construction frontier: the existing positive
Rothe/Schauder route produces lower-pinned frozen stationary profiles, but the
full `hpos` branch also requires `ShenUpperBoundPositive` and the sharp
right-tail asymptotic for the produced profile. -/
def Paper1PositiveCriticalFrozenStationaryBranch : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ U : ℝ → ℝ,
        FrozenStationaryWaveProfile p c U ∧
          ShenUpperBoundPositive p c U ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
            HasWaveRightTailAsymptotic c κ₁ U

/-- Strict comparison with the canonical `MChi` upper barrier implies the
paper-facing positive upper-bound statement.

This is pure normalization: `ShenUpperBoundPositive` stores the constant bound
as `(1 / (1 - p.χ)) ^ (1 / p.α)`, while the construction route naturally uses
`MChi p`. -/
theorem ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
    (hpos : ∀ x, 0 < U x)
    (hstrict : ∀ x, U x < upperBarrier (kappa c) (MChi p) x) :
    ShenUpperBoundPositive p c U := by
  intro x
  refine ⟨hpos x, ?_⟩
  rw [← MChi_eq_rpow_of_chi_nonneg_lt_one p hχ_nonneg hχ_lt]
  simpa [upperBarrier] using hstrict x

/-- Positive critical branch with the upper-bound residual exposed as a strict
barrier comparison rather than as the bundled `ShenUpperBoundPositive`.

Still conditional: this does not prove the strict comparison or the sharp
right-tail asymptotics.  It only separates the pure `MChi`/normalization wiring
from the analytic strict-comparison obligation. -/
def Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ U : ℝ → ℝ,
        FrozenStationaryWaveProfile p c U ∧
          (∀ x, U x < upperBarrier (kappa c) (MChi p) x) ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
            HasWaveRightTailAsymptotic c κ₁ U

/-- Pure conversion from the strict-barrier positive branch to the existing
positive branch required by the Paper1 Theorem 1.1 wrapper. -/
theorem paper1_positiveCriticalBranch_of_strictBarrier
    (hbranch : Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch) :
    Paper1PositiveCriticalFrozenStationaryBranch := by
  intro p hα hχ_nonneg hχ_small c hc
  rcases hbranch p hα hχ_nonneg hχ_small c hc with
    ⟨U, hprofile, hstrict, htail⟩
  have hχ_lt_half : p.χ < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hχ_small (min_le_left _ _)
  have hχ_lt_one : p.χ < 1 := by linarith
  exact
    ⟨U, hprofile,
      ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
        hχ_nonneg hχ_lt_one hprofile.U_pos hstrict,
      htail⟩

/-- Preferred Paper1 main-statement input package using the thinner current
routes instead of the old monolithic `Paper1MainResultsData`.

Still conditional: `constructionNeg` is the weakened negative construction
provider, `positiveCritical` is the positive frozen-stationary branch for
Theorem 1.1, and `mainline` is the B5 stability/uniqueness mainline package for
Theorems 1.2 and 1.3.  This package is not an unconditional Paper1 headline
producer. -/
structure Paper1MainStatementSMPMainlineData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveCritical : Paper1PositiveCriticalFrozenStationaryBranch
  mainline : Paper1MainlineExistence cStarStarFn

/-- Main-statement input package with the positive branch's upper-bound field
split down to the strict `MChi` upper-barrier comparison.

Still conditional: the strict comparison and sharp right-tail asymptotics remain
frontier inputs, and `Paper1MainlineExistence` is unchanged. -/
structure Paper1MainStatementStrictBarrierData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveStrictBarrier : Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch
  mainline : Paper1MainlineExistence cStarStarFn

/-- Preferred Paper1 main-statement wrapper from the current thinner input
packages.

This is pure wiring:
* Theorem 1.1 is obtained from
  `paper1_Theorem_1_1_of_constructionNegSMPProvider`.
* Theorems 1.2 and 1.3 are obtained from
  `paper1_mainlineStatementTargets_of_mainlineExistence`.

It does not construct `ConstructionNegSMPProvider`, the positive branch, or
`Paper1MainlineExistence`. -/
theorem paper1_mainStatementTargets_of_smpMainlineData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainStatementSMPMainlineData cStarStarFn) :
    Paper1MainStatementTargets := by
  have hmainline :=
    paper1_mainlineStatementTargets_of_mainlineExistence hData.mainline
  exact ⟨paper1_Theorem_1_1_of_constructionNegSMPProvider
      hData.constructionNeg hData.positiveCritical,
    hmainline.1,
    hmainline.2⟩

/-- Main-statement wrapper from the strict-barrier positive-branch package. -/
theorem paper1_mainStatementTargets_of_strictBarrierData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainStatementStrictBarrierData cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_smpMainlineData
    { constructionNeg := hData.constructionNeg
      positiveCritical :=
        paper1_positiveCriticalBranch_of_strictBarrier
          hData.positiveStrictBarrier
      mainline := hData.mainline }

/-- Instance-facing wrapper for the preferred conditional Paper1 main-statement
route. -/
theorem paper1_mainStatementTargets_of_smpMainlineDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainStatementSMPMainlineData cStarStarFn)] :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_smpMainlineData hData.out

/-- Instance-facing wrapper for the strict-barrier Paper1 main-statement
route. -/
theorem paper1_mainStatementTargets_of_strictBarrierDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainStatementStrictBarrierData cStarStarFn)] :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_strictBarrierData hData.out

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
inputs.  This record names the remaining analytic inputs; it does not produce
them. -/
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

/-- Frontier record for the Paper1 Lemma 5.2 monotonicity input.  This is a
carried frontier field, not a monotonicity producer. -/
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
inputs that close Propositions 1.1 and 1.2.  These fields are the remaining
whole-line Cauchy frontiers, not theorem producers. -/
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

/-! ## Combined statement targets -/

/-- Paper1 statement targets currently assembled by this file. -/
def Paper1CombinedStatementTargets : Prop :=
  Paper1MainStatementTargets ∧
    Paper1PropositionTargets ∧
      Paper1Lemma25Targets ∧
        Paper1Lemma51And52Targets

/-- Bundled data for the Paper1 combined statement-target assembly.

This is a frontier bundle: `main`, `propositions`, `lemma51`, and `lemma52`
are still supplied inputs.  Only the nested Lemma 2.5 targets are closed
inside `paper1_combinedStatementTargets_of_data`. -/
structure Paper1CombinedStatementData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  main : Paper1MainResultsData cStarStarFn
  propositions : Paper1PropositionFrontierData
  lemma51 : Paper1Lemma51FrontierData
  lemma52 : Paper1Lemma52FrontierData

/-- Assemble the Paper1 statement targets covered by existing data records. -/
theorem paper1_combinedStatementTargets_of_data
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1CombinedStatementData cStarStarFn) :
    Paper1CombinedStatementTargets :=
  ⟨paper1_mainStatementTargets_of_mainResultsData hData.main,
    paper1_propositionTargets_of_frontierData hData.propositions,
    paper1_lemma25Targets,
    paper1_lemma51And52Targets_of_frontierData
      hData.lemma51 hData.lemma52⟩

/-- Instance-facing wrapper for the combined Paper1 statement targets. -/
theorem paper1_combinedStatementTargets_of_dataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1CombinedStatementData cStarStarFn)] :
    Paper1CombinedStatementTargets :=
  paper1_combinedStatementTargets_of_data hData.out

end

end ShenWork.Paper1
