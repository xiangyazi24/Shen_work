import ShenWork.Paper1.WaveNegativeRotheParameters
import ShenWork.Paper1.NegativeRawRouteAAssembly

noncomputable section

namespace ShenWork.Paper1

/-- Canonical global Green-step constants supplied by the large-parameter
theorem. -/
noncomputable def paper1NegativeLocalStepScalars
    (p : CMParams) {c : ℝ}
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0)
    (hc : cStarLower p < c) :
    Paper1NegativeLocalStepScalarData p c :=
  Classical.choice (paper1NegativeLocalStepScalarData_exists p hα hχ hc)

/-- Canonical strict lower-barrier coefficient. -/
def paper1NegativeRotheD (p : CMParams) (c : ℝ) : ℝ :=
  max 1
    (paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
      p.m p.γ c + 1)

theorem paper1NegativeRotheD_one_le (p : CMParams) (c : ℝ) :
    1 ≤ paper1NegativeRotheD p c :=
  le_max_left _ _

theorem paper1NegativeRotheD_gt (p : CMParams) (c : ℝ) :
    paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
        p.m p.γ c < paper1NegativeRotheD p c := by
  unfold paper1NegativeRotheD
  exact lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)

/-- The single remaining negative-branch analytic theorem.

All global constants, the explicit elliptic source box, local source Schauder,
orbit compactness, adaptive moving-index Green closed graph, and outer
Schauder--Tychonoff theorem are already internal.  This statement now contains
exactly the cross-frozen parabolic comparison/Route-A step and L10
local-uniform stability for those canonical constants. -/
def Paper1NegativeRotheAnalyticCore : Type :=
  ∀ p : CMParams, ∀ hα : p.α ≤ p.m + p.γ - 1,
    ∀ hχ : p.χ ≤ 0, ∀ c : ℝ, ∀ hc : cStarLower p < c,
      let s := paper1NegativeLocalStepScalars p hα hχ hc
      let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
      PaperLowerRawParabolicFloorRouteAParamCoreNoBar
        p c s.lam 1 (kappa c) (negativeBranchTailCap p c)
          (paper1NegativeRotheD p c) s.Λ
          hcond.hκ0.le (le_trans zero_le_one hcond.hM)

/-- Exact per-step residual after source Schauder, the frozen source box, and
the raw lower comparison have all been discharged. -/
def Paper1NegativeLocalStepRestCore : Prop :=
  ∀ p : CMParams, ∀ hα : p.α ≤ p.m + p.γ - 1,
    ∀ hχ : p.χ ≤ 0, ∀ c : ℝ, ∀ hc : cStarLower p < c,
      let s := paper1NegativeLocalStepScalars p hα hχ hc
      ∀ u, InMonotoneWaveTrapSet (kappa c) 1 u →
        PaperLocalFixedStepRestProvider
          p c s.lam 1 (kappa c) s.Λ s.B u

/-- Canonical lower-raw producer induced by the exact local step residual. -/
noncomputable def paper1NegativeParamProducer
    (hstep : Paper1NegativeLocalStepRestCore)
    (p : CMParams) (hα : p.α ≤ p.m + p.γ - 1)
    (hχ : p.χ ≤ 0) (c : ℝ) (hc : cStarLower p < c) :
    let s := paper1NegativeLocalStepScalars p hα hχ hc
    let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
    ∀ u, InMonotoneWaveTrapSet (kappa c) 1 u →
      PaperLowerRawStepProducerRouteAParamCore
        p c s.lam 1 (kappa c) (negativeBranchTailCap p c)
          (paper1NegativeRotheD p c) s.Λ
          hcond.hκ0.le (le_trans zero_le_one hcond.hM) u := by
  dsimp only
  intro u hu
  let s := paper1NegativeLocalStepScalars p hα hχ hc
  exact s.toLowerRawStepProducer hu (hstep p hα hχ c hc u hu)

/-- The exact L10 double-limit datum for the canonical producer.  All
compactness and adaptive Green closed-graph statements used after this field
are theorems. -/
def Paper1NegativeRotheL10
    (hstep : Paper1NegativeLocalStepRestCore) : Prop :=
  ∀ p : CMParams, ∀ hα : p.α ≤ p.m + p.γ - 1,
    ∀ hχ : p.χ ≤ 0, ∀ c : ℝ, ∀ hc : cStarLower p < c,
      LocalUniformContinuousOn
        (InLowerPinnedMonotoneTrap (kappa c) 1
          (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c)
            (paper1NegativeRotheD p c)))
        (fun u => rotheLimit
          (paperLowerRawParamRotheSeq
            (paper1NegativeParamProducer hstep p hα hχ c hc) u))

/-- Reassemble the legacy one-record residual from exactly the per-step order
theorem and L10. -/
noncomputable def paper1NegativeRotheAnalyticCore_of_rest_l10
    (hstep : Paper1NegativeLocalStepRestCore)
    (hL10 : Paper1NegativeRotheL10 hstep) :
    Paper1NegativeRotheAnalyticCore := by
  intro p hα hχ c hc
  let s := paper1NegativeLocalStepScalars p hα hχ hc
  let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
  exact
    { producer := paper1NegativeParamProducer hstep p hα hχ c hc
      limitContinuous := hL10 p hα hχ c hc }

/-- Mechanical headline adapter after the single analytic core. -/
theorem paper1NegativeLowerRawCapRouteAParamData_of_analyticCore
    (hcore : Paper1NegativeRotheAnalyticCore) :
    Paper1NegativeLowerRawCapRouteAParamData := by
  refine ⟨?_⟩
  intro p hα hχ c hc
  let s := paper1NegativeLocalStepScalars p hα hχ hc
  let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
  let D := paper1NegativeRotheD p c
  refine ⟨s.lam, D, s.Λ, ?_, ?_, ?_, s.hΛ0⟩
  · exact hcore p hα hχ c hc
  · exact paper1NegativeRotheD_one_le p c
  · exact paper1NegativeRotheD_gt p c

/-- The complete negative headline branch, conditional only on the exact
analytic core named above. -/
theorem paper1_negativeConstruction_of_analyticCore
    (hcore : Paper1NegativeRotheAnalyticCore) :
    ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
      ∀ c : ℝ, cStarLower p < c →
        ∃ U : ℝ → ℝ,
          FrozenStationaryWaveProfile p c U ∧
          (∀ x, deriv U x ≤ 0) ∧
          (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
          ShenUpperBoundNegative c U ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < negativeBranchTailCap p c →
              HasWaveRightTailAsymptotic c κ₁ U :=
  paper1_negativeConstruction_of_routeAParamData
    (paper1NegativeLowerRawCapRouteAParamData_of_analyticCore hcore)

section AxiomAudit

#print axioms paper1NegativeRotheD_one_le
#print axioms paper1NegativeRotheD_gt
#print axioms paper1NegativeParamProducer
#print axioms paper1NegativeRotheAnalyticCore_of_rest_l10
#print axioms paper1NegativeLowerRawCapRouteAParamData_of_analyticCore
#print axioms paper1_negativeConstruction_of_analyticCore

end AxiomAudit

end ShenWork.Paper1
