import ShenWork.Paper1.WaveNegativeRotheParameters
import ShenWork.Paper1.WaveNegativePinnedSchauder
import ShenWork.Paper1.NegativeRawRouteAAssembly

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

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

/-- Canonical global Green-step constants supplied by the large-parameter
theorem, including the lower-pinned successor comparison gap. -/
noncomputable def paper1NegativeLocalStepScalars
    (p : CMParams) {c : ℝ}
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0)
    (hc : cStarLower p < c) :
    Paper1NegativeLocalStepScalarData p c (paper1NegativeRotheD p c) :=
  Classical.choice
    (paper1NegativeLocalStepScalarData_exists p (paper1NegativeRotheD p c)
      hα hχ hc)

/-- The sole residual of the genuine negative construction: L10 stability of
the explicitly constructed lower-pinned Rothe long-time map on its compact
uniform-modulus trap.  Source-box existence, every local Green step, orbit
compactness, Schauder--Tychonoff, and the whole-line Green closed graph are
theorems rather than fields of this predicate. -/
def Paper1NegativePinnedRotheL10Core : Prop :=
  ∀ p : CMParams, ∀ hα : p.α ≤ p.m + p.γ - 1,
    ∀ hχ : p.χ ≤ 0, ∀ c : ℝ, ∀ hc : cStarLower p < c,
      let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
      let D := paper1NegativeRotheD p c
      let s := paper1NegativeLocalStepScalars p hα hχ hc
      PaperNegativePinnedRotheL10 hcond
        (paper1NegativeRotheD_gt p c) (paper1NegativeRotheD_one_le p c) s

/-- Canonical form of the single irreducible negative-branch residual after
adaptive Green closure: uniqueness of the normalized lower-pinned stationary
selection for each frozen profile. -/
def Paper1NegativePinnedStationaryIdentificationCore : Prop :=
  ∀ p : CMParams, ∀ hα : p.α ≤ p.m + p.γ - 1,
    ∀ hχ : p.χ ≤ 0, ∀ c : ℝ, ∀ hc : cStarLower p < c,
      let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
      let D := paper1NegativeRotheD p c
      let s := paper1NegativeLocalStepScalars p hα hχ hc
      PaperNegativePinnedStationaryIdentification hcond
        (paper1NegativeRotheD_gt p c) (paper1NegativeRotheD_one_le p c) s

/-- Exact one-sided residual after the proved stationary maximality theorem.
For an adaptive stationary cluster `W`, only the inequality saying that the
upper-start selection does not drop strictly above `W` remains open. -/
def Paper1NegativePinnedStationaryNoDropCore : Prop :=
  ∀ p : CMParams, ∀ hα : p.α ≤ p.m + p.γ - 1,
    ∀ hχ : p.χ ≤ 0, ∀ c : ℝ, ∀ hc : cStarLower p < c,
      let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
      let D := paper1NegativeRotheD p c
      let s := paper1NegativeLocalStepScalars p hα hχ hc
      PaperNegativePinnedStationaryNoDrop hcond
        (paper1NegativeRotheD_gt p c) (paper1NegativeRotheD_one_le p c) s

/-- The adaptive moving-index closed graph and compact range turn the exact
stationary-identification core into L10. -/
theorem paper1NegativePinnedRotheL10Core_of_stationaryIdentification
    (hidentify : Paper1NegativePinnedStationaryIdentificationCore) :
    Paper1NegativePinnedRotheL10Core := by
  intro p hα hχ c hc
  exact paperNegativePinnedRotheL10_of_stationaryIdentification
    (negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc)
    (paper1NegativeRotheD_gt p c) (paper1NegativeRotheD_one_le p c)
    (paper1NegativeLocalStepScalars p hα hχ hc)
    (hidentify p hα hχ c hc)

/-- The adaptive Green graph, the proved maximality direction, and compact
range reduce L10 to the exact no-drop core. -/
theorem paper1NegativePinnedRotheL10Core_of_stationaryNoDrop
    (hnoDrop : Paper1NegativePinnedStationaryNoDropCore) :
    Paper1NegativePinnedRotheL10Core := by
  intro p hα hχ c hc
  exact paperNegativePinnedRotheL10_of_stationaryNoDrop
    (negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc)
    (paper1NegativeRotheD_gt p c) (paper1NegativeRotheD_one_le p c)
    (paper1NegativeLocalStepScalars p hα hχ hc)
    (hnoDrop p hα hχ c hc)

/-- Full negative headline branch from the genuine pinned Rothe construction,
conditional only on its exact L10 stability theorem. -/
theorem paper1_negativeConstruction_of_pinnedRotheL10
    (hL10 : Paper1NegativePinnedRotheL10Core) :
    ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
      ∀ c : ℝ, cStarLower p < c →
        ∃ U : ℝ → ℝ,
          FrozenStationaryWaveProfile p c U ∧
          (∀ x, deriv U x ≤ 0) ∧
          (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
          ShenUpperBoundNegative c U ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < negativeBranchTailCap p c →
              HasWaveRightTailAsymptotic c κ₁ U := by
  intro p hα hχ c hc
  let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
  let D := paper1NegativeRotheD p c
  let s := paper1NegativeLocalStepScalars p hα hχ hc
  obtain ⟨U, hU, _hfix, hstat, hUdiff, hUderivDiff, hsourceTail⟩ :=
    paperNegativePinned_fixed_stationary_of_L10
      hcond (paper1NegativeRotheD_gt p c)
      (paper1NegativeRotheD_one_le p c) s (hL10 p hα hχ c hc)
  have hUpin : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) U :=
    hU.toLowerPinned
  have hgap : 0 < negativeBranchTailCap p c - kappa c :=
    sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond
    (paper1NegativeRotheD_gt p c)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond
      (paper1NegativeRotheD_gt p c) (fun x _hx => hUpin.lower x)
  have hpos : ∀ x, 0 < U x :=
    stationaryProfile_strictlyPositive_of_trap_regularity
      one_pos hUpin.bare hstat hUdiff hUderivDiff hnontriv
  have hsource : FrozenStationaryGreenSourceTail c s.lam U := by
    simpa [PaperGreenSourceTailData, FrozenStationaryGreenSourceTail] using
      hsourceTail
  have hflat : FrozenStationaryFlatAtLeft p U :=
    frozenStationaryFlatAtLeft_of_green_source_tail
      s.hlam one_pos hUpin hUdiff hsource
  have hleft : Tendsto U atBot (nhds 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
      hcond.hκ0 hgap hDpos hUpin.bare hUpin.lower hflat hstat
  have hright : Tendsto U atTop (nhds 0) :=
    hUpin.bare.tendsto_atTop_zero hcond.hκ0
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < (kappa c)⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  let hprofile : FrozenStationaryWaveProfile p c U :=
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hUpin.bare.trap.cunif_bdd hstat hleft hright
  have hstrict0 : U 0 < 1 := by
    refine lt_of_le_of_ne (hUpin.bare.le_M 0) ?_
    intro hU0
    exact upperBarrier_interfaceNoContact_of_profile_differentiable
      hcond.hκ0 one_pos hUpin.bare hUdiff 0 (by simp) hU0
  have hupper : ShenUpperBoundNegative c U :=
    ShenUpperBoundNegative_of_strictAtZero hcond.hκ0 hUpin.bare
      hprofile.U_pos hstrict0
  have htail : ∀ κ₁, kappa c < κ₁ →
      κ₁ < negativeBranchTailCap p c →
        HasWaveRightTailAsymptotic c κ₁ U :=
    lowerPinnedRawMonotoneTrap_tail_family_for_branch
      (le_trans zero_le_one (paper1NegativeRotheD_one_le p c))
      (by simp [negativeBranchTailCap]) hUpin
  exact ⟨U, hprofile, hUpin.bare.deriv_nonpos,
    frozenElliptic_deriv_nonpos_of_monotone_trap
      p (kappa c) 1 U hUpin.bare,
    hupper, htail⟩

/-- Negative construction with every Rothe/Schauder/Green hypothesis
discharged except the exact stationary-identification theorem. -/
theorem paper1_negativeConstruction_of_stationaryIdentification
    (hidentify : Paper1NegativePinnedStationaryIdentificationCore) :
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
  paper1_negativeConstruction_of_pinnedRotheL10
    (paper1NegativePinnedRotheL10Core_of_stationaryIdentification hidentify)

/-- Negative construction with every local Green, comparison, compactness and
Schauder theorem discharged except the single stationary no-drop inequality. -/
theorem paper1_negativeConstruction_of_stationaryNoDrop
    (hnoDrop : Paper1NegativePinnedStationaryNoDropCore) :
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
  paper1_negativeConstruction_of_pinnedRotheL10
    (paper1NegativePinnedRotheL10Core_of_stationaryNoDrop hnoDrop)

/-- Headline adapter after the genuine negative Rothe construction.  The
positive-attraction construction remains a separate input; in particular this
theorem does not mention the inconsistent Route-A positive ParamData package. -/
theorem Theorem_1_1.of_negativePinnedRotheL10
    (hL10 : Paper1NegativePinnedRotheL10Core)
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
  Theorem_1_1.of_assumed_frozenStationaryProfile_branches
    (by simpa [negativeBranchTailCap] using
      paper1_negativeConstruction_of_pinnedRotheL10 hL10)
    hpos

/-- Headline adapter exposing the exact remaining negative stationary
identification theorem and the genuinely separate positive construction. -/
theorem Theorem_1_1.of_negativeStationaryIdentification
    (hidentify : Paper1NegativePinnedStationaryIdentificationCore)
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
  Theorem_1_1.of_negativePinnedRotheL10
    (paper1NegativePinnedRotheL10Core_of_stationaryIdentification hidentify)
    hpos

/-- Headline adapter exposing the one-sided negative no-drop theorem and the
genuinely separate positive-attraction construction. -/
theorem Theorem_1_1.of_negativeStationaryNoDrop
    (hnoDrop : Paper1NegativePinnedStationaryNoDropCore)
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
  Theorem_1_1.of_negativePinnedRotheL10
    (paper1NegativePinnedRotheL10Core_of_stationaryNoDrop hnoDrop) hpos

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
#print axioms paper1NegativePinnedRotheL10Core_of_stationaryIdentification
#print axioms paper1NegativePinnedRotheL10Core_of_stationaryNoDrop
#print axioms paper1_negativeConstruction_of_pinnedRotheL10
#print axioms paper1_negativeConstruction_of_stationaryIdentification
#print axioms paper1_negativeConstruction_of_stationaryNoDrop
#print axioms Theorem_1_1.of_negativePinnedRotheL10
#print axioms Theorem_1_1.of_negativeStationaryIdentification
#print axioms Theorem_1_1.of_negativeStationaryNoDrop
#print axioms paper1NegativeParamProducer
#print axioms paper1NegativeRotheAnalyticCore_of_rest_l10
#print axioms paper1NegativeLowerRawCapRouteAParamData_of_analyticCore
#print axioms paper1_negativeConstruction_of_analyticCore

end AxiomAudit

end ShenWork.Paper1
