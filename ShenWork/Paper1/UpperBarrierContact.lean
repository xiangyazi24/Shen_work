/-
  Paper1 positive upper-barrier contact refinements.

  This file keeps the statement assembly lean: it imports the existing
  kink-avoidance lemma only here, then exposes a narrower no-contact frontier for
  the two smooth branches of the positive upper barrier.
-/
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheResidualClose

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- The remaining analytic atom for the positive branch after the interface kink
is discharged by differentiability. -/
def PositiveUpperBarrierSmoothBranchNoContact
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  (∀ x, MChi p < Real.exp (-(kappa c) * x) →
      U x = MChi p → False) ∧
  (∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) → False)

/-- Assemble the full contact-contradiction record from smooth-branch
no-contact plus an interface no-contact proof. -/
theorem PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hsmooth : PositiveUpperBarrierSmoothBranchNoContact p c U)
    (hinterface :
      ∀ x, Real.exp (-(kappa c) * x) = MChi p →
        U x = MChi p → False) :
    PositiveUpperBarrierContactContradictions p c U :=
  { const_branch := hsmooth.1
    exp_branch := hsmooth.2
    interface := hinterface }

/-- A differentiable trapped profile cannot touch the positive upper barrier at
the nonsmooth interface.  This reuses the existing kink-avoidance lemma for
local maxima of `U - upperBarrier`. -/
theorem positiveUpperBarrier_interfaceNoContact_of_regular_stationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hM : 0 < MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    ∀ x, Real.exp (-(kappa c) * x) = MChi p →
      U x = MChi p → False := by
  intro x hx hUx
  have hdiff : Differentiable ℝ U := (hreg U htrap hstat).1
  have hbarrier_x :
      upperBarrier (kappa c) (MChi p) x = MChi p :=
    upperBarrier_eq_M_of_le_exp hx.ge
  have hmax :
      IsLocalMax
        (fun y => U y - upperBarrier (kappa c) (MChi p) y) x := by
    dsimp [IsLocalMax, IsMaxFilter]
    refine Filter.Eventually.of_forall fun y => ?_
    have hy : U y - upperBarrier (kappa c) (MChi p) y ≤ 0 :=
      sub_nonpos.mpr (htrap.le_upperBarrier y)
    have hx0 :
        U x - upperBarrier (kappa c) (MChi p) x = 0 := by
      rw [hUx, hbarrier_x, sub_self]
    simpa [hx0] using hy
  exact
    maxSub_upperBarrier_ne_interface
      (κ := kappa c) (M := MChi p) (W := U) (x := x)
      hκ hM (hdiff x) hmax hx

/-- Regular stationary data discharges the interface field, so only the two
smooth-branch no-contact facts remain. -/
theorem PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_regularStationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hsmooth : PositiveUpperBarrierSmoothBranchNoContact p c U)
    (hκ : 0 < kappa c) (hM : 0 < MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    PositiveUpperBarrierContactContradictions p c U :=
  PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact hsmooth
    (positiveUpperBarrier_interfaceNoContact_of_regular_stationary
      hκ hM htrap hstat hreg)

/-- Constant-branch contact with the upper trap level forces a full left
plateau by monotonicity. -/
theorem constBranch_contact_forces_left_plateau
    {κ M : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet κ M U)
    {x : ℝ} (hUx : U x = M) :
    ∀ y, y ≤ x → U y = M := by
  intro y hy
  exact le_antisymm
    (htrap.le_M y)
    (by
      have hmono : U x ≤ U y := htrap.antitone hy
      simpa [hUx] using hmono)

/-- A profile tending to `1` at `-∞` cannot have a left plateau at a distinct
level `MChi p`. -/
theorem no_const_left_plateau_of_tendsto_atBot_one
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hlim : Tendsto U atBot (𝓝 (1 : ℝ)))
    (hMne : MChi p ≠ 1) :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False := by
  intro x _hx hplateau
  have hev : U =ᶠ[atBot] fun _ : ℝ => MChi p := by
    exact eventually_atBot.2 ⟨x, fun y hy => hplateau y hy⟩
  have hlimM : Tendsto U atBot (𝓝 (MChi p)) :=
    tendsto_const_nhds.congr' (hev.mono fun _ hy => hy.symm)
  have hEq : (1 : ℝ) = MChi p := tendsto_nhds_unique hlim hlimM
  exact hMne hEq.symm

/-- Finer smooth-branch frontier for the positive upper barrier.

The constant branch is reduced to a no-left-plateau statement.  The exponential
branch is reduced to an operator comparison at contact plus strict upper
super-barrier residual at contact. -/
structure PositiveUpperBarrierSmoothBranchResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  no_const_left_plateau :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      (∀ y, y ≤ x → U y = MChi p) → False
  exp_operator_compare_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U U x ≤
          frozenWaveOperator p c U
            (upperBarrier (kappa c) (MChi p)) x
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) →
        frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x < 0

/-- The finer smooth-branch residual assembles the original smooth no-contact
pair. -/
theorem positiveUpperBarrierSmoothBranchNoContact_of_residual
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hres : PositiveUpperBarrierSmoothBranchResidual p c U) :
    PositiveUpperBarrierSmoothBranchNoContact p c U := by
  constructor
  · intro x hx hUx
    exact hres.no_const_left_plateau x hx
      (constBranch_contact_forces_left_plateau htrap hUx)
  · intro x hx hUx
    have hcmp := hres.exp_operator_compare_at_contact x hx hUx
    have hstrict := hres.exp_strict_super_at_contact x hx hUx
    have hnonneg :
        0 ≤ frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x := by
      simpa [hstat x] using hcmp
    exact (not_lt_of_ge hnonneg) hstrict

/-- Positive critical branch data that preserves the current raw lower pin and
carries only smooth-branch no-contact; the interface is discharged from
regularity. -/
structure Paper1PositiveLowerPinnedRawSmoothContactBranchData : Prop where
  produce :
    ∀ p : CMParams, p.α = p.m + p.γ - 1 →
      0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
      ∀ c : ℝ, 2 < c →
        ∃ κtilde D : ℝ, ∃ U : ℝ → ℝ,
          0 ≤ D ∧
          positiveBranchTailCap p c ≤ κtilde ∧
          FrozenStationaryWaveProfile p c U ∧
          InLowerPinnedMonotoneTrap (kappa c) (MChi p)
            (lowerBarrierRaw (kappa c) κtilde D) U ∧
          PositiveUpperBarrierSmoothBranchNoContact p c U ∧
          StationaryC2RegularityFromEquation p c (kappa c) (MChi p)

/-- Raw lower-pinned smooth-branch contact data produces the full raw-contact
package by closing the interface from regularity. -/
theorem paper1_positiveLowerPinnedRawContactData_of_smoothContactData
    (hData : Paper1PositiveLowerPinnedRawSmoothContactBranchData) :
    Paper1PositiveLowerPinnedRawContactBranchData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨κtilde, D, U, hD, hcover, hprofile, hpin, hsmooth, hreg⟩
  have hχ_star : p.χ < chiStar p :=
    lt_of_lt_of_le hχ_small (min_le_right _ _)
  exact
    ⟨κtilde, D, U, hD, hcover, hprofile, hpin,
      PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact_regularStationary
        hsmooth (kappa_pos_of_two_lt hc)
        (MChi_pos_of_chi_lt_chiStar p hχ_star)
        hpin.bare hprofile.stationary_eq hreg⟩

/-- Positive branch wrapper through raw lower-pinned smooth-contact data. -/
theorem paper1_positiveContactBranch_of_lowerPinnedRawSmoothContactData
    (hData : Paper1PositiveLowerPinnedRawSmoothContactBranchData) :
    Paper1PositiveCriticalFrozenStationaryContactBranch :=
  paper1_positiveContactBranch_of_lowerPinnedRawContactData
    (paper1_positiveLowerPinnedRawContactData_of_smoothContactData hData)

/-- Strict-barrier branch wrapper through raw lower-pinned smooth-contact data. -/
theorem paper1_positiveStrictBarrierBranch_of_lowerPinnedRawSmoothContactData
    (hData : Paper1PositiveLowerPinnedRawSmoothContactBranchData) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_lowerPinnedRawContactData
    (paper1_positiveLowerPinnedRawContactData_of_smoothContactData hData)

/-- Main-statement input package with the positive branch routed through raw
lower-pinned smooth-branch no-contact data. -/
structure Paper1MainStatementLowerPinnedRawSmoothContactData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveLowerPinnedRawSmoothContact :
    Paper1PositiveLowerPinnedRawSmoothContactBranchData
  mainline : Paper1MainlineExistence cStarStarFn

/-- Main-statement wrapper through raw lower-pinned smooth-contact data. -/
theorem paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainStatementLowerPinnedRawSmoothContactData cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawContactData
    { constructionNeg := hData.constructionNeg
      positiveLowerPinnedRawContact :=
        paper1_positiveLowerPinnedRawContactData_of_smoothContactData
          hData.positiveLowerPinnedRawSmoothContact
      mainline := hData.mainline }

/-- Instance-facing wrapper for the raw lower-pinned smooth-contact
main-statement route. -/
theorem paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData :
      Fact (Paper1MainStatementLowerPinnedRawSmoothContactData cStarStarFn)] :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactData hData.out

/-- Bundled data for Paper1 combined statement targets using the raw
lower-pinned smooth-contact positive branch. -/
structure Paper1CombinedLowerPinnedRawSmoothContactStatementData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  main : Paper1MainStatementLowerPinnedRawSmoothContactData cStarStarFn
  propositions : Paper1PropositionFrontierData
  lemma51 : Paper1Lemma51FrontierData
  lemma52 : Paper1Lemma52FrontierData

/-- Assemble the Paper1 combined statement targets through the raw
lower-pinned smooth-contact route. -/
theorem paper1_combinedStatementTargets_of_lowerPinnedRawSmoothContactData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData :
      Paper1CombinedLowerPinnedRawSmoothContactStatementData cStarStarFn) :
    Paper1CombinedStatementTargets :=
  ⟨paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactData hData.main,
    paper1_propositionTargets_of_frontierData hData.propositions,
    paper1_lemma25Targets,
    paper1_lemma51And52Targets_of_frontierData
      hData.lemma51 hData.lemma52⟩

/-- Instance-facing wrapper for the combined raw lower-pinned smooth-contact
Paper1 statement route. -/
theorem paper1_combinedStatementTargets_of_lowerPinnedRawSmoothContactDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData :
      Fact (Paper1CombinedLowerPinnedRawSmoothContactStatementData
        cStarStarFn)] :
    Paper1CombinedStatementTargets :=
  paper1_combinedStatementTargets_of_lowerPinnedRawSmoothContactData hData.out

end

end ShenWork.Paper1
