/-
  Paper1 positive Route-A assembly at the branch cap.

  The current positive Route-A producers preserve a raw lower-barrier pin.  This
  file specializes their parameter package to `positiveBranchTailCap` and wires
  the result into the raw lower-pinned statement interfaces.
-/
import ShenWork.Paper1.UpperBarrierContact
import ShenWork.Paper1.WaveLemma42ParamCore
import ShenWork.Paper1.NegativeRawRouteAAssembly

namespace ShenWork.Paper1

noncomputable section

/-- Positive Lemma 4.2 exact conditions specialized to the branch tail cap. -/
theorem positivePaperLemma42ExactConditions_of_branchCap
    (p : CMParams) {c : ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c) :
    PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p) := by
  have hχ_half : p.χ < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hχ_small (min_le_left _ _)
  have hχ_one : p.χ < 1 :=
    lt_trans hχ_half (by norm_num)
  exact
    { hκ0 := kappa_pos_of_two_lt hc
      hκ1 := kappa_lt_one_of_two_lt hc
      hgap := kappa_lt_positiveBranchTailCap p hc
      hrange := by
        simp [positiveBranchTailCap]
      hM := one_le_MChi_of_chi_nonneg_lt_one p hχ_nonneg hχ_one
      hc := (kappa_add_inv_eq_of_two_lt hc).symm
      hχ_nonneg := hχ_nonneg
      hχ_small := hχ_small
      hα_eq := hα }

/-- Route-A param-core data at the positive branch cap after all upper-barrier
contact cases have become internal.  The remaining input is precisely the
frozen parabolic/Rothe floor package. -/
structure Paper1PositiveLowerRawCapRouteAParamData : Prop where
  produce :
    ∀ p : CMParams, ∀ hα : p.α = p.m + p.γ - 1,
      ∀ hχ_nonneg : 0 ≤ p.χ,
        ∀ hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p),
          ∀ c : ℝ, ∀ hc : 2 < c,
            ∃ lam D Λ : ℝ,
              let hcond :
                  PositivePaperLemma42ExactConditions p c (kappa c)
                    (positiveBranchTailCap p c) (MChi p) :=
                positivePaperLemma42ExactConditions_of_branchCap
                  p hα hχ_nonneg hχ_small hc
              ∃ _hpar :
                PaperLowerRawParabolicFloorRouteAParamCoreNoBar
                  p c lam (MChi p) (kappa c)
                  (positiveBranchTailCap p c) D Λ
                  hcond.hκ0.le (le_trans zero_le_one hcond.hM),
                  1 ≤ D ∧
                  paperDMin p.χ (MChi p) (kappa c)
                    (positiveBranchTailCap p c) p.m p.γ c < D ∧
                  0 ≤ Λ ∧ Λ ≤ MChi p

/-- Route-A param-core data produces the raw lower-pinned contact package. -/
theorem paper1_positiveRawContactData_of_routeAParamData
    (hData : Paper1PositiveLowerRawCapRouteAParamData) :
    Paper1PositiveLowerPinnedRawContactBranchData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  let hcond :
      PositivePaperLemma42ExactConditions p c (kappa c)
        (positiveBranchTailCap p c) (MChi p) :=
    positivePaperLemma42ExactConditions_of_branchCap
      p hα hχ_nonneg hχ_small hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨lam, D, Λ, hpar, hD_ge_one, hD_gt, hΛ0, hΛM⟩
  obtain ⟨U, hpin, hprofile, hUdiff, hUderivDiff⟩ :=
    b1_chiPos_existence_paper_routeA_paramCore_noBar
      p c lam (MChi p) (kappa c) (positiveBranchTailCap p c) D Λ
      hcond hD_gt hD_ge_one hΛ0 hΛM hpar
  exact
    ⟨positiveBranchTailCap p c, D, U,
      le_trans zero_le_one hD_ge_one,
      le_rfl,
      hprofile,
      hpin,
      PositiveUpperBarrierContactContradictions.of_profile_chi_nonneg
        hα hχ_nonneg hχ_small hc hpin.bare hprofile
        hUdiff hUderivDiff⟩

/-- Positive contact branch from Route-A param-core cap data. -/
theorem paper1_positiveContactBranch_of_routeAParamData
    (hData : Paper1PositiveLowerRawCapRouteAParamData) :
    Paper1PositiveCriticalFrozenStationaryContactBranch :=
  paper1_positiveContactBranch_of_lowerPinnedRawContactData
    (paper1_positiveRawContactData_of_routeAParamData hData)

/-- Strict-barrier branch from Route-A param-core cap data. -/
theorem paper1_positiveStrictBarrierBranch_of_routeAParamData
    (hData : Paper1PositiveLowerRawCapRouteAParamData) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_lowerPinnedRawContactData
    (paper1_positiveRawContactData_of_routeAParamData hData)

/-- Route-A param-core data at the positive branch cap, carrying only the
smooth-branch upper-contact residual plus regularity for the interface. -/
structure Paper1PositiveLowerRawCapRouteASmoothParamData : Prop where
  produce :
    ∀ p : CMParams, ∀ hα : p.α = p.m + p.γ - 1,
      ∀ hχ_nonneg : 0 ≤ p.χ,
        ∀ hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p),
          ∀ c : ℝ, ∀ hc : 2 < c,
            ∃ lam D Λ : ℝ,
              let hcond :
                  PositivePaperLemma42ExactConditions p c (kappa c)
                    (positiveBranchTailCap p c) (MChi p) :=
                positivePaperLemma42ExactConditions_of_branchCap
                  p hα hχ_nonneg hχ_small hc
              ∃ _hpar :
                PaperLowerRawParabolicFloorRouteAParamCoreNoBar
                  p c lam (MChi p) (kappa c)
                  (positiveBranchTailCap p c) D Λ
                  hcond.hκ0.le (le_trans zero_le_one hcond.hM),
                  1 ≤ D ∧
                  paperDMin p.χ (MChi p) (kappa c)
                    (positiveBranchTailCap p c) p.m p.γ c < D ∧
                  0 ≤ Λ ∧ Λ ≤ MChi p ∧
                  (∀ U : ℝ → ℝ,
                    InLowerPinnedMonotoneTrap (kappa c) (MChi p)
                      (lowerBarrierRaw (kappa c)
                        (positiveBranchTailCap p c) D) U →
                    FrozenStationaryWaveProfile p c U →
                    PositiveUpperBarrierSmoothBranchNoContact p c U)

/-- Route-A param-core data with smooth-branch residuals produces the raw
smooth-contact package. -/
theorem paper1_positiveRawSmoothContactData_of_routeAParamData
    (hData : Paper1PositiveLowerRawCapRouteASmoothParamData) :
    Paper1PositiveLowerPinnedRawSmoothContactBranchData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  let hcond :
      PositivePaperLemma42ExactConditions p c (kappa c)
        (positiveBranchTailCap p c) (MChi p) :=
    positivePaperLemma42ExactConditions_of_branchCap
      p hα hχ_nonneg hχ_small hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨lam, D, Λ, hpar, hD_ge_one, hD_gt, hΛ0, hΛM, hsmooth⟩
  obtain ⟨U, hpin, hprofile, hUdiff, hUderivDiff⟩ :=
    b1_chiPos_existence_paper_routeA_paramCore_noBar
      p c lam (MChi p) (kappa c) (positiveBranchTailCap p c) D Λ
      hcond hD_gt hD_ge_one hΛ0 hΛM hpar
  exact
    ⟨positiveBranchTailCap p c, D, U,
      le_trans zero_le_one hD_ge_one,
      le_rfl,
      hprofile,
      hpin,
      hsmooth U hpin hprofile,
      hUdiff, hUderivDiff⟩

/-- Positive contact branch from Route-A param-core data with smooth-branch
upper-contact residuals. -/
theorem paper1_positiveContactBranch_of_routeASmoothParamData
    (hData : Paper1PositiveLowerRawCapRouteASmoothParamData) :
    Paper1PositiveCriticalFrozenStationaryContactBranch :=
  paper1_positiveContactBranch_of_lowerPinnedRawSmoothContactData
    (paper1_positiveRawSmoothContactData_of_routeAParamData hData)

/-- Strict-barrier branch from Route-A param-core data with smooth-branch
upper-contact residuals. -/
theorem paper1_positiveStrictBarrierBranch_of_routeASmoothParamData
    (hData : Paper1PositiveLowerRawCapRouteASmoothParamData) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_lowerPinnedRawSmoothContactData
    (paper1_positiveRawSmoothContactData_of_routeAParamData hData)

/-- Route-A param-core data at the positive branch cap, carrying only the
remaining smooth-contact residual.  The exponential operator comparison is
closed from the stationary regularity field. -/
structure Paper1PositiveLowerRawCapRouteARemainingParamData : Prop where
  produce :
    ∀ p : CMParams, ∀ hα : p.α = p.m + p.γ - 1,
      ∀ hχ_nonneg : 0 ≤ p.χ,
        ∀ hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p),
          ∀ c : ℝ, ∀ hc : 2 < c,
            ∃ lam D Λ : ℝ,
              let hcond :
                  PositivePaperLemma42ExactConditions p c (kappa c)
                    (positiveBranchTailCap p c) (MChi p) :=
                positivePaperLemma42ExactConditions_of_branchCap
                  p hα hχ_nonneg hχ_small hc
              ∃ _hpar :
                PaperLowerRawParabolicFloorRouteAParamCoreNoBar
                  p c lam (MChi p) (kappa c)
                  (positiveBranchTailCap p c) D Λ
                  hcond.hκ0.le (le_trans zero_le_one hcond.hM),
                  1 ≤ D ∧
                  paperDMin p.χ (MChi p) (kappa c)
                    (positiveBranchTailCap p c) p.m p.γ c < D ∧
                  0 ≤ Λ ∧ Λ ≤ MChi p ∧
                  (∀ U : ℝ → ℝ,
                    InLowerPinnedMonotoneTrap (kappa c) (MChi p)
                      (lowerBarrierRaw (kappa c)
                        (positiveBranchTailCap p c) D) U →
                    FrozenStationaryWaveProfile p c U →
                    PositiveUpperBarrierRemainingContactResidual p c U)

/-- Route-A param-core data on the `hmκ` subregime carrying only the
constant-branch upper-contact residual.  The strict exponential residual is
produced from the positive-region operator estimate. -/
structure Paper1PositiveLowerRawCapRouteAHmkConstParamData : Prop where
  produce :
    ∀ p : CMParams, ∀ hα : p.α = p.m + p.γ - 1,
      ∀ hχ_nonneg : 0 ≤ p.χ,
        ∀ hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p),
          ∀ c : ℝ, ∀ hc : 2 < c,
            p.m * kappa c ≤ 1 ∧
            ∃ lam D Λ : ℝ,
              let hcond :
                  PositivePaperLemma42ExactConditions p c (kappa c)
                    (positiveBranchTailCap p c) (MChi p) :=
                positivePaperLemma42ExactConditions_of_branchCap
                  p hα hχ_nonneg hχ_small hc
              ∃ _hpar :
                PaperLowerRawParabolicFloorRouteAParamCoreNoBar
                  p c lam (MChi p) (kappa c)
                  (positiveBranchTailCap p c) D Λ
                  hcond.hκ0.le (le_trans zero_le_one hcond.hM),
                  1 ≤ D ∧
                  paperDMin p.χ (MChi p) (kappa c)
                    (positiveBranchTailCap p c) p.m p.γ c < D ∧
                  0 ≤ Λ ∧ Λ ≤ MChi p ∧
                  (∀ U : ℝ → ℝ,
                    InLowerPinnedMonotoneTrap (kappa c) (MChi p)
                      (lowerBarrierRaw (kappa c)
                        (positiveBranchTailCap p c) D) U →
                    FrozenStationaryWaveProfile p c U →
                    PositiveUpperBarrierConstLeftPlateauResidual p c U)

/-- The hmk-aware constant-branch package produces the existing remaining
Route-A package. -/
theorem paper1_routeARemainingParamData_of_routeAHmkConstParamData
    (hData : Paper1PositiveLowerRawCapRouteAHmkConstParamData) :
    Paper1PositiveLowerRawCapRouteARemainingParamData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨hmκ, lam, D, Λ, hpar, hD_ge_one, hD_gt, hΛ0, hΛM, hconst⟩
  exact
    ⟨lam, D, Λ, hpar, hD_ge_one, hD_gt, hΛ0, hΛM,
      fun U hpin hprofile =>
        PositiveUpperBarrierRemainingContactResidual.of_constLeftPlateau_positiveRegion
          (p := p) (c := c) (U := U)
          hα hχ_nonneg hχ_small hc hmκ hpin.bare
          (hconst U hpin hprofile)⟩

/-- Route-A remaining-contact param data produces the raw lower-pinned
remaining-contact package directly. -/
theorem paper1_positiveRawRemainingContactData_of_routeARemainingParamData
    (hData : Paper1PositiveLowerRawCapRouteARemainingParamData) :
    Paper1PositiveLowerPinnedRawRemainingContactBranchData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  let hcond :
      PositivePaperLemma42ExactConditions p c (kappa c)
        (positiveBranchTailCap p c) (MChi p) :=
    positivePaperLemma42ExactConditions_of_branchCap
      p hα hχ_nonneg hχ_small hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨lam, D, Λ, hpar, hD_ge_one, hD_gt, hΛ0, hΛM, hres⟩
  obtain ⟨U, hpin, hprofile, hUdiff, hUderivDiff⟩ :=
    b1_chiPos_existence_paper_routeA_paramCore_noBar
      p c lam (MChi p) (kappa c) (positiveBranchTailCap p c) D Λ
      hcond hD_gt hD_ge_one hΛ0 hΛM hpar
  exact
    ⟨positiveBranchTailCap p c, D, U,
      le_trans zero_le_one hD_ge_one,
      le_rfl,
      hprofile,
      hpin,
      hres U hpin hprofile,
      hUdiff, hUderivDiff⟩

/-- Route-A remaining-contact param data produces the raw smooth-contact
package. -/
theorem paper1_positiveRawSmoothContactData_of_routeARemainingParamData
    (hData : Paper1PositiveLowerRawCapRouteARemainingParamData) :
    Paper1PositiveLowerPinnedRawSmoothContactBranchData :=
  paper1_positiveLowerPinnedRawSmoothContactData_of_remainingContactData
    (paper1_positiveRawRemainingContactData_of_routeARemainingParamData hData)

/-- Raw remaining-contact package from hmk-aware constant-branch Route-A data. -/
theorem paper1_positiveRawRemainingContactData_of_routeAHmkConstParamData
    (hData : Paper1PositiveLowerRawCapRouteAHmkConstParamData) :
    Paper1PositiveLowerPinnedRawRemainingContactBranchData :=
  paper1_positiveRawRemainingContactData_of_routeARemainingParamData
    (paper1_routeARemainingParamData_of_routeAHmkConstParamData hData)

/-- Main Paper1 statement targets from Route-A remaining-contact cap data. -/
theorem paper1_mainStatementTargets_of_routeARemainingParamData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hneg : ConstructionNegSMPProvider)
    (hpos : Paper1PositiveLowerRawCapRouteARemainingParamData)
    (hmainline : Paper1MainlineExistence cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawRemainingContactData
    { constructionNeg := hneg
      positiveLowerPinnedRawRemainingContact :=
        paper1_positiveRawRemainingContactData_of_routeARemainingParamData hpos
      mainline := hmainline }

/-- Main Paper1 statement targets from hmk-aware Route-A constant-branch cap
data. -/
theorem paper1_mainStatementTargets_of_routeAHmkConstParamData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hneg : ConstructionNegSMPProvider)
    (hpos : Paper1PositiveLowerRawCapRouteAHmkConstParamData)
    (hmainline : Paper1MainlineExistence cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_routeARemainingParamData
    hneg
    (paper1_routeARemainingParamData_of_routeAHmkConstParamData hpos)
    hmainline

/-- Combined Paper1 statement targets from Route-A remaining-contact cap data. -/
theorem paper1_combinedStatementTargets_of_routeARemainingParamData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hneg : ConstructionNegSMPProvider)
    (hpos : Paper1PositiveLowerRawCapRouteARemainingParamData)
    (hmainline : Paper1MainlineExistence cStarStarFn)
    (hprops : Paper1PropositionFrontierData)
    (h51 : Paper1Lemma51FrontierData)
    (h52 : Paper1Lemma52FrontierData) :
    Paper1CombinedStatementTargets :=
  paper1_combinedStatementTargets_of_lowerPinnedRawRemainingContactData
    { main :=
        { constructionNeg := hneg
          positiveLowerPinnedRawRemainingContact :=
            paper1_positiveRawRemainingContactData_of_routeARemainingParamData
              hpos
          mainline := hmainline }
      propositions := hprops
      lemma51 := h51
      lemma52 := h52 }

/-- Combined Paper1 statement targets from hmk-aware Route-A constant-branch
cap data. -/
theorem paper1_combinedStatementTargets_of_routeAHmkConstParamData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hneg : ConstructionNegSMPProvider)
    (hpos : Paper1PositiveLowerRawCapRouteAHmkConstParamData)
    (hmainline : Paper1MainlineExistence cStarStarFn)
    (hprops : Paper1PropositionFrontierData)
    (h51 : Paper1Lemma51FrontierData)
    (h52 : Paper1Lemma52FrontierData) :
    Paper1CombinedStatementTargets :=
  paper1_combinedStatementTargets_of_routeARemainingParamData
    hneg
    (paper1_routeARemainingParamData_of_routeAHmkConstParamData hpos)
    hmainline hprops h51 h52

/-- Positive contact branch from Route-A param-core data with only the remaining
upper-contact residual. -/
theorem paper1_positiveContactBranch_of_routeARemainingParamData
    (hData : Paper1PositiveLowerRawCapRouteARemainingParamData) :
    Paper1PositiveCriticalFrozenStationaryContactBranch :=
  paper1_positiveContactBranch_of_lowerPinnedRawRemainingContactData
    (paper1_positiveRawRemainingContactData_of_routeARemainingParamData hData)

/-- Strict-barrier branch from Route-A param-core data with only the remaining
upper-contact residual. -/
theorem paper1_positiveStrictBarrierBranch_of_routeARemainingParamData
    (hData : Paper1PositiveLowerRawCapRouteARemainingParamData) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_lowerPinnedRawRemainingContactData
    (paper1_positiveRawRemainingContactData_of_routeARemainingParamData hData)

/-- Raw smooth-contact package from hmk-aware constant-branch Route-A data. -/
theorem paper1_positiveRawSmoothContactData_of_routeAHmkConstParamData
    (hData : Paper1PositiveLowerRawCapRouteAHmkConstParamData) :
    Paper1PositiveLowerPinnedRawSmoothContactBranchData :=
  paper1_positiveRawSmoothContactData_of_routeARemainingParamData
    (paper1_routeARemainingParamData_of_routeAHmkConstParamData hData)

/-- Positive contact branch from hmk-aware constant-branch Route-A data. -/
theorem paper1_positiveContactBranch_of_routeAHmkConstParamData
    (hData : Paper1PositiveLowerRawCapRouteAHmkConstParamData) :
    Paper1PositiveCriticalFrozenStationaryContactBranch :=
  paper1_positiveContactBranch_of_routeARemainingParamData
    (paper1_routeARemainingParamData_of_routeAHmkConstParamData hData)

/-- Strict-barrier branch from hmk-aware constant-branch Route-A data. -/
theorem paper1_positiveStrictBarrierBranch_of_routeAHmkConstParamData
    (hData : Paper1PositiveLowerRawCapRouteAHmkConstParamData) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_routeARemainingParamData
    (paper1_routeARemainingParamData_of_routeAHmkConstParamData hData)

/-- The Paper 1 existence headline from the orbit-faithful negative and
positive Route-A parameter packages. -/
theorem Theorem_1_1.of_routeAParamData
    (hneg : Paper1NegativeLowerRawCapRouteAParamData)
    (hpos : Paper1PositiveLowerRawCapRouteAParamData) :
    Theorem_1_1 :=
  Theorem_1_1.of_negativeRouteAParamData hneg
    (paper1_positiveCriticalBranch_of_strictBarrier
      (paper1_positiveStrictBarrierBranch_of_routeAParamData hpos))

section AxiomAudit
#print axioms paper1_positiveRawContactData_of_routeAParamData
#print axioms paper1_positiveRawSmoothContactData_of_routeAParamData
#print axioms paper1_positiveRawRemainingContactData_of_routeARemainingParamData
#print axioms Theorem_1_1.of_routeAParamData
end AxiomAudit

end

end ShenWork.Paper1
