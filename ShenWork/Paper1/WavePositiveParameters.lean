/- Uniform scalar choices for the genuine positive-attraction self step. -/
import ShenWork.Paper1.WavePositiveStepComparison
import ShenWork.Paper1.WavePositiveLocalStep

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Route-independent positive Lemma 4.2 conditions at the headline tail cap.
This is the parameter constructor used by the genuine nonmonotone self-step;
it deliberately does not pass through the inconsistent Route-A package. -/
theorem positiveSelfStepExactConditions_of_branchCap
    (p : CMParams) {c : ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ0 : 0 ≤ p.χ)
    (hχsmall : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c) :
    PositivePaperLemma42ExactConditions p c (kappa c)
      (positiveBranchTailCap p c) (MChi p) := by
  have hχhalf : p.χ < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hχsmall (min_le_left _ _)
  have hχ1 : p.χ < 1 := lt_trans hχhalf (by norm_num)
  exact
    { hκ0 := kappa_pos_of_two_lt hc
      hκ1 := kappa_lt_one_of_two_lt hc
      hgap := kappa_lt_positiveBranchTailCap p hc
      hrange := by simp [positiveBranchTailCap]
      hM := one_le_MChi_of_chi_nonneg_lt_one p hχ0 hχ1
      hc := (kappa_add_inv_eq_of_two_lt hc).symm
      hχ_nonneg := hχ0
      hχ_small := hχsmall
      hα_eq := hα }

structure Paper1PositiveLocalStepScalarData
    (p : CMParams) (c D : ℝ) : Type where
  lam : ℝ
  B : ℝ
  Λ : ℝ
  hlam : 0 < lam
  hrpκ : kappa c < greenRootPlus c lam
  hrmκ : kappa c < -greenRootMinus c lam
  hB : 0 ≤ B
  hΛ : Λ = 2 * (greenDelta c lam)⁻¹ * (B * MChi p)
  hΛ0 : 0 ≤ Λ
  pinnedStep_small :
    (1 / lam) * paperPositivePinnedStepCmono p (MChi p)
      (paperLowerPinnedStepLogSlopeCoeff c lam (kappa c)
        (positiveBranchTailCap p c) D (MChi p) B) < 1
  plateauStep_small :
    (1 / lam) * paperPositivePlateauStepCmono p (MChi p)
      (paperLowerPinnedStepLogSlopeCoeff c lam (kappa c)
        (positiveBranchTailCap p c) D (MChi p) B) < 1
  sourceScalar :
    |(-p.χ * p.m)| * (MChi p) ^ (p.m - 1) * (MChi p) ^ p.γ *
          greenWeightedMass1 c lam (kappa c) * B
      + (1 + |p.χ| * (MChi p) ^ (p.m - 1) * (MChi p) ^ p.γ
          + (MChi p) ^ p.α
          + |p.χ| * (MChi p) ^ (p.m + p.γ - 1))
      + lam ≤ B

/-- One sufficiently large whole-line resolvent parameter closes all scalar
budgets of the positive self step. -/
theorem paper1PositiveLocalStepScalarData_exists
    (p : CMParams) {c : ℝ} (D : ℝ)
    (hM : 0 < MChi p) :
    Nonempty (Paper1PositiveLocalStepScalarData p c D) := by
  let M : ℝ := MChi p
  let A : ℝ := |(-p.χ * p.m)| * M ^ (p.m - 1) * M ^ p.γ
  let C : ℝ :=
    1 + |p.χ| * M ^ (p.m - 1) * M ^ p.γ
      + M ^ p.α + |p.χ| * M ^ (p.m + p.γ - 1)
  have hmassT : Tendsto
      (fun lam : ℝ => A * greenWeightedMass1 c lam (kappa c))
      atTop (nhds 0) := by
    simpa [A] using
      (greenWeightedMass1_tendsto_zero c (kappa c)).const_mul A
  have hmass : ∀ᶠ lam in atTop,
      A * greenWeightedMass1 c lam (kappa c) < 1 / 2 :=
    hmassT.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hrp : ∀ᶠ lam in atTop, kappa c < greenRootPlus c lam :=
    (greenRootPlus_tendsto_atTop c).eventually_gt_atTop (kappa c)
  have hrm : ∀ᶠ lam in atTop, kappa c < -greenRootMinus c lam :=
    (neg_greenRootMinus_tendsto_atTop c).eventually_gt_atTop (kappa c)
  have hlamLarge : ∀ᶠ lam : ℝ in atTop, 0 < lam := eventually_gt_atTop 0
  have hpinned : ∀ᶠ lam : ℝ in atTop,
      (1 / lam) * paperPositivePinnedStepCmono p M
        (paperLowerPinnedStepLogSlopeCoeff c lam (kappa c)
          (positiveBranchTailCap p c) D M (2 * (C + lam))) < 1 :=
    (paperPositivePinnedStepCmono_large_source_tendsto_zero
      p c M (kappa c) (positiveBranchTailCap p c) D C).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hplateau : ∀ᶠ lam : ℝ in atTop,
      (1 / lam) * paperPositivePlateauStepCmono p M
        (paperLowerPinnedStepLogSlopeCoeff c lam (kappa c)
          (positiveBranchTailCap p c) D M (2 * (C + lam))) < 1 :=
    (paperPositivePlateauStepCmono_large_source_tendsto_zero
      p c M (kappa c) (positiveBranchTailCap p c) D C).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨lam, hmassLam, hrpLam, hrmLam, hlam, hpinnedLam, hplateauLam⟩ :=
    (hmass.and
      (hrp.and (hrm.and (hlamLarge.and (hpinned.and hplateau))))).exists
  let B : ℝ := 2 * (C + lam)
  have hC0 : 0 ≤ C := by
    dsimp [C, M]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsource :
      A * greenWeightedMass1 c lam (kappa c) * B + C + lam ≤ B := by
    have hmul :
        A * greenWeightedMass1 c lam (kappa c) * B ≤ (1 / 2 : ℝ) * B :=
      mul_le_mul_of_nonneg_right hmassLam.le hB
    dsimp [B]
    nlinarith
  let Λ : ℝ := 2 * (greenDelta c lam)⁻¹ * (B * M)
  have hΛ0 : 0 ≤ Λ := by
    dsimp [Λ]
    exact mul_nonneg
      (mul_nonneg zero_le_two
        (inv_nonneg.mpr (greenDelta_pos (c := c) hlam).le))
      (mul_nonneg hB hM.le)
  refine ⟨{
    lam := lam
    B := B
    Λ := Λ
    hlam := hlam
    hrpκ := hrpLam
    hrmκ := hrmLam
    hB := hB
    hΛ := rfl
    hΛ0 := hΛ0
    pinnedStep_small := by simpa [M, B] using hpinnedLam
    plateauStep_small := by simpa [M, B] using hplateauLam
    sourceScalar := ?_ }⟩
  change A * greenWeightedMass1 c lam (kappa c) * B + C + lam ≤ B
  exact hsource

section AxiomAudit

#print axioms paper1PositiveLocalStepScalarData_exists
#print axioms positiveSelfStepExactConditions_of_branchCap

end AxiomAudit

end ShenWork.Paper1
