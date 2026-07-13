/-
  Negative Paper 1 Route-A assembly at the sharp right-tail cap.
-/
import ShenWork.Paper1.StationaryUpperTail
import ShenWork.Paper1.WaveLemma42ParamCore
import ShenWork.Paper1.UpperBarrierContact

namespace ShenWork.Paper1

noncomputable section

/-- The sharp branch endpoint, used as the raw lower-barrier exponent. -/
def negativeBranchTailCap (p : CMParams) (c : ℝ) : ℝ :=
  min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)

theorem kappa_lt_negativeBranchTailCap
    (p : CMParams) {c : ℝ} (hc : cStarLower p < c) :
    kappa c < negativeBranchTailCap p c := by
  have hc2 : 2 < c := two_lt_of_cStarLower_lt hc
  have hκpos : 0 < kappa c := kappa_pos_of_cStarLower_lt hc
  have hκlt1 : kappa c < 1 := kappa_lt_one_of_two_lt hc2
  have hcoeff : (1 : ℝ) < 1 + p.α := by linarith [p.hα]
  have hleft : kappa c < (1 + p.α) * kappa c := by
    calc
      kappa c = (1 : ℝ) * kappa c := by ring
      _ < (1 + p.α) * kappa c :=
        mul_lt_mul_of_pos_right hcoeff hκpos
  have hmk : kappa c ≤ p.m * kappa c := by
    calc
      kappa c = (1 : ℝ) * kappa c := by ring
      _ ≤ p.m * kappa c :=
        mul_le_mul_of_nonneg_right p.hm hκpos.le
  have hmid : kappa c < p.m * kappa c + 1 / 2 := by linarith
  simpa [negativeBranchTailCap] using lt_min hleft (lt_min hmid hκlt1)

/-- Negative Lemma 4.2 conditions at the exact headline tail endpoint. -/
theorem negativePaperLemma42ExactConditions_of_branchCap
    (p : CMParams) {c : ℝ}
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0)
    (hc : cStarLower p < c) :
    PaperLemma42ExactConditions p c (kappa c)
      (negativeBranchTailCap p c) 1 :=
  { hκ0 := kappa_pos_of_cStarLower_lt hc
    hκ1 := kappa_lt_one_of_two_lt (two_lt_of_cStarLower_lt hc)
    hgap := kappa_lt_negativeBranchTailCap p hc
    hrange := by simp [negativeBranchTailCap]
    hM := le_rfl
    hc := (kappa_add_inv_eq_of_two_lt (two_lt_of_cStarLower_lt hc)).symm
    hχ := hχ
    hα_le := hα }

/-- Route-A construction data for the negative branch after source compactness,
finite-cube Schauder, adaptive stationarity, `C²`, strict positivity, left
flatness, the right-tail family, and strict non-contact at the saturated point
`x = 0` have all become internal.  The remaining analytic input is precisely
the frozen parabolic/Rothe floor package. -/
structure Paper1NegativeLowerRawCapRouteAParamData : Prop where
  produce :
    ∀ p : CMParams, ∀ hα : p.α ≤ p.m + p.γ - 1,
      ∀ hχ : p.χ ≤ 0, ∀ c : ℝ, ∀ hc : cStarLower p < c,
        ∃ lam D Λ : ℝ,
          let hcond : PaperLemma42ExactConditions p c (kappa c)
              (negativeBranchTailCap p c) 1 :=
            negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
          ∃ _hpar : PaperLowerRawParabolicFloorRouteAParamCoreNoBar
              p c lam 1 (kappa c) (negativeBranchTailCap p c) D Λ
              hcond.hκ0.le (le_trans zero_le_one hcond.hM),
            1 ≤ D ∧
            paperDMin p.χ 1 (kappa c) (negativeBranchTailCap p c)
              p.m p.γ c < D ∧
            0 ≤ Λ ∧ Λ ≤ 1

/-- The current negative headline package is also empty: it asks the
per-profile source box to work on every member of the bare monotone trap, which
contains `slowLeftTrapProfile`, while the source box requires a positive
exponential left-rate witness. -/
theorem not_Paper1NegativeLowerRawCapRouteAParamData :
    ¬ Paper1NegativeLowerRawCapRouteAParamData := by
  intro hData
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 0
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hα : p.α ≤ p.m + p.γ - 1 := by norm_num [p]
  have hχ : p.χ ≤ 0 := by norm_num [p]
  have hc : cStarLower p < 3 := by
    norm_num [p, cStarLower]
  rcases hData.produce p hα hχ 3 hc with
    ⟨lam, D, Λ, hpar, _hD_ge_one, _hD_gt, _hΛ0, _hΛM⟩
  exact
    not_PaperLowerRawParabolicFloorRouteAParamCoreNoBar_of_one_le_M
      (p := p) (c := 3) (lam := lam) (M := 1)
      (κ := kappa 3) (κtilde := negativeBranchTailCap p 3)
      (D := D) (Λ := Λ) le_rfl hpar

/-- Full negative branch from the orbit-faithful Route-A parameter data. -/
theorem paper1_negativeConstruction_of_routeAParamData
    (hData : Paper1NegativeLowerRawCapRouteAParamData) :
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
  let hcond : PaperLemma42ExactConditions p c (kappa c)
      (negativeBranchTailCap p c) 1 :=
    negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
  rcases hData.produce p hα hχ c hc with
    ⟨lam, D, Λ, hpar, hD1, hD, hΛ0, hΛ1⟩
  obtain ⟨U, hU, hprofile, hUdiff, _hUderivDiff⟩ :=
    b1_chiNeg_existence_paper_routeA_paramCore_noBar
      p c lam 1 (kappa c) (negativeBranchTailCap p c) D Λ
      hcond hD hD1 hΛ0 hΛ1 hpar
  have hstrict0 : U 0 < 1 := by
    refine lt_of_le_of_ne (hU.bare.le_M 0) ?_
    intro hU0
    exact upperBarrier_interfaceNoContact_of_profile_differentiable
      hcond.hκ0 one_pos hU.bare hUdiff 0 (by simp) hU0
  have hupper : ShenUpperBoundNegative c U :=
    ShenUpperBoundNegative_of_strictAtZero hcond.hκ0 hU.bare
      hprofile.U_pos hstrict0
  have htail : ∀ κ₁, kappa c < κ₁ →
      κ₁ < negativeBranchTailCap p c →
        HasWaveRightTailAsymptotic c κ₁ U :=
    lowerPinnedRawMonotoneTrap_tail_family_for_branch
      (le_trans zero_le_one hD1) (by simp [negativeBranchTailCap]) hU
  exact ⟨U, hprofile, hU.bare.deriv_nonpos,
    frozenElliptic_deriv_nonpos_of_monotone_trap
      p (kappa c) 1 U hU.bare,
    hupper, htail⟩

/-- Theorem 1.1 once the positive construction branch is supplied. -/
theorem Theorem_1_1.of_negativeRouteAParamData
    (hneg : Paper1NegativeLowerRawCapRouteAParamData)
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
      paper1_negativeConstruction_of_routeAParamData hneg)
    hpos

section AxiomAudit
#print axioms negativePaperLemma42ExactConditions_of_branchCap
#print axioms not_Paper1NegativeLowerRawCapRouteAParamData
#print axioms paper1_negativeConstruction_of_routeAParamData
#print axioms Theorem_1_1.of_negativeRouteAParamData
end AxiomAudit

end

end ShenWork.Paper1
