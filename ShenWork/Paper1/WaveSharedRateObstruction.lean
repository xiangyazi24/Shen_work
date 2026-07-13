import ShenWork.Paper1.WaveSharedRateOrbit

open MeasureTheory

noncomputable section

namespace ShenWork.Paper1

theorem greenKernelExpMoment_nonneg (c lam sigma : ℝ) :
    0 ≤ greenKernelExpMoment c lam sigma := by
  unfold greenKernelExpMoment
  exact integral_nonneg fun z =>
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem greenKernelDerivExpMoment_nonneg (c lam sigma : ℝ) :
    0 ≤ greenKernelDerivExpMoment c lam sigma := by
  unfold greenKernelDerivExpMoment
  exact integral_nonneg fun z =>
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem paperTruncatedNonlinearityRateClam_nonneg
    (p : CMParams) {c lam M B sigma C_u : ℝ} (hM : 0 ≤ M) :
    0 ≤ paperTruncatedNonlinearityRateClam p c lam M B sigma C_u := by
  have hG0 := greenKernelExpMoment_nonneg c lam sigma
  have hG1 := greenKernelDerivExpMoment_nonneg c lam sigma
  have hLm : 0 ≤ rpowLip p.m M := rpowLip_nonneg p.hm hM
  have hLa : 0 ≤ rpowLip (p.α + 1) M :=
    rpowLip_nonneg (by linarith [p.hα]) hM
  have hLmg : 0 ≤ rpowLip (p.m + p.γ) M :=
    rpowLip_nonneg (by linarith [p.hm, p.hγ]) hM
  unfold paperTruncatedNonlinearityRateClam
  dsimp only
  positivity

/-- Exact exponential resolvent mass.  The denominator is the characteristic
polynomial evaluated at the positive weight `sigma`. -/
theorem greenKernelExpMoment_eq_inv_characteristic
    {c lam sigma : ℝ} (hlam : 0 < lam) (hsigma0 : 0 ≤ sigma)
    (hsigma : sigma < greenRootPlus c lam) :
    greenKernelExpMoment c lam sigma =
      (lam - c * sigma - sigma ^ 2)⁻¹ := by
  rw [greenKernelExpMoment_eq (c := c) (lam := lam) hlam hsigma0 hsigma]
  have hp : 0 < greenRootPlus c lam - sigma := sub_pos.mpr hsigma
  have hm : greenRootMinus c lam - sigma < 0 := by
    linarith [greenRootMinus_neg (c := c) hlam]
  have hδ : 0 < greenDelta c lam := greenDelta_pos (c := c) hlam
  have hadd := greenRoots_add (c := c) (lam := lam)
  have hmul := greenRoots_mul (c := c) (lam := lam) hlam
  have hdiff := greenRoots_sub (c := c) (lam := lam) hlam
  have hprod :
      (greenRootPlus c lam - sigma) *
          (greenRootMinus c lam - sigma) =
        -(lam - c * sigma - sigma ^ 2) := by
    calc
      (greenRootPlus c lam - sigma) *
          (greenRootMinus c lam - sigma) =
          greenRootPlus c lam * greenRootMinus c lam -
            sigma * (greenRootPlus c lam + greenRootMinus c lam) +
            sigma ^ 2 := by ring
      _ = -(lam - c * sigma - sigma ^ 2) := by
        rw [hmul, hadd]
        ring
  have hden : 0 < lam - c * sigma - sigma ^ 2 := by
    have hneg := mul_neg_of_pos_of_neg hp hm
    rw [hprod] at hneg
    linarith
  have hinner :
      (greenRootPlus c lam - sigma)⁻¹ -
          (greenRootMinus c lam - sigma)⁻¹ =
        greenDelta c lam / (lam - c * sigma - sigma ^ 2) := by
    rw [inv_sub_inv hp.ne' (ne_of_lt hm), hprod]
    have hnum :
        (greenRootMinus c lam - sigma) -
            (greenRootPlus c lam - sigma) = -greenDelta c lam := by
      linarith
    rw [hnum]
    rw [div_neg, neg_div]
    simp
  rw [hinner]
  field_simp [hδ.ne', hden.ne']

theorem inv_lam_le_greenKernelExpMoment
    {c lam sigma : ℝ} (hc : 0 ≤ c) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hroot : sigma < greenRootPlus c lam) :
    lam⁻¹ ≤ greenKernelExpMoment c lam sigma := by
  rw [greenKernelExpMoment_eq_inv_characteristic
    hlam hsigma.le hroot]
  have hden : 0 < lam - c * sigma - sigma ^ 2 := by
    have hp : 0 < greenRootPlus c lam - sigma := sub_pos.mpr hroot
    have hm : greenRootMinus c lam - sigma < 0 := by
      linarith [greenRootMinus_neg (c := c) hlam]
    have hadd := greenRoots_add (c := c) (lam := lam)
    have hmul := greenRoots_mul (c := c) (lam := lam) hlam
    have hprod :
        (greenRootPlus c lam - sigma) *
            (greenRootMinus c lam - sigma) =
          -(lam - c * sigma - sigma ^ 2) := by
      calc
        (greenRootPlus c lam - sigma) *
            (greenRootMinus c lam - sigma) =
            greenRootPlus c lam * greenRootMinus c lam -
              sigma * (greenRootPlus c lam + greenRootMinus c lam) +
              sigma ^ 2 := by ring
        _ = -(lam - c * sigma - sigma ^ 2) := by
          rw [hmul, hadd]
          ring
    have hneg := mul_neg_of_pos_of_neg hp hm
    rw [hprod] at hneg
    linarith
  have hden_le : lam - c * sigma - sigma ^ 2 ≤ lam := by
    nlinarith [mul_nonneg hc hsigma.le, sq_nonneg sigma]
  have hone := one_div_le_one_div_of_le hden hden_le
  simpa [one_div] using hone

/-- The old two-radius invariant is inconsistent in the headline regime.  The
source contraction forces `lam*m_sigma < 1`, whereas absorbing even the linear
Green successor forces `lam*m_sigma ≥ 2`. -/
theorem not_twoRadius_absorbs_controlledStepRate
    {p : CMParams}
    {c lam M B sigma C_u C_R m_sigma : ℝ}
    (hc : 0 ≤ c) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hB : 0 ≤ B) (hsigma : 0 < sigma)
    (hroot : sigma < greenRootPlus c lam) (hCR : 0 < C_R)
    (hcontract :
      paperTruncatedNonlinearityRateClam p c lam M B sigma C_u +
        paperFixedSourceMapAZ lam * m_sigma < 1) :
    ¬ paperControlledStepRateConst c lam sigma B M C_R ≤
        paperFixedSourceMapTwoRadiusCZ m_sigma C_R := by
  intro habsorb
  have hClam : 0 ≤
      paperTruncatedNonlinearityRateClam p c lam M B sigma C_u :=
    paperTruncatedNonlinearityRateClam_nonneg p hM
  have hG : lam⁻¹ ≤ greenKernelExpMoment c lam sigma :=
    inv_lam_le_greenKernelExpMoment hc hlam hsigma hroot
  have hG0 : 0 ≤ greenKernelExpMoment c lam sigma :=
    greenKernelExpMoment_nonneg c lam sigma
  have hBM : 0 ≤ B * M := mul_nonneg hB hM
  have htwoG :
      2 * greenKernelExpMoment c lam sigma ≤ m_sigma := by
    dsimp [paperControlledStepRateConst,
      paperFixedSourceMapTwoRadiusCZ] at habsorb
    have hweak :
        greenKernelExpMoment c lam sigma * (2 * C_R) ≤
          m_sigma * C_R := by
      calc
        greenKernelExpMoment c lam sigma * (2 * C_R)
            ≤ greenKernelExpMoment c lam sigma *
                (2 * C_R + 2 * (B * M)) := by
              exact mul_le_mul_of_nonneg_left
                (by nlinarith : 2 * C_R ≤ 2 * C_R + 2 * (B * M)) hG0
        _ ≤ m_sigma * C_R := habsorb
    nlinarith
  have hlamG : 1 ≤ lam * greenKernelExpMoment c lam sigma := by
    have hmul := mul_le_mul_of_nonneg_left hG hlam.le
    simpa [hlam.ne'] using hmul
  have hlarge : 2 ≤ lam * m_sigma := by
    nlinarith
  have hsmall : lam * m_sigma < 1 := by
    rw [paperFixedSourceMapAZ, abs_of_pos hlam] at hcontract
    linarith
  linarith

/-- In particular, no positive-radius `PerStepBoxParams` can satisfy the extra
shared-successor absorption used by the first controlled-orbit prototype. -/
theorem PerStepBoxParams.not_sharedRate_absorption
    {p : CMParams}
    {c lam M κ Λ B sigma aL C_u L_u C_R m_sigma : ℝ}
    {u : ℝ → ℝ}
    (params :
      PerStepBoxParams p c lam M κ Λ B sigma aL C_u L_u C_R m_sigma u)
    (hc : 0 ≤ c) :
    ¬ paperControlledStepRateConst c lam sigma B M C_R ≤
        paperFixedSourceMapTwoRadiusCZ m_sigma C_R := by
  have hCRpos : 0 < C_R := by
    have hBM : 0 < B * M := mul_pos params.hBpos params.hM
    nlinarith [params.hObsRight]
  exact not_twoRadius_absorbs_controlledStepRate
    hc params.hlam params.hM.le params.hBnn params.hsigma
    params.hsigma_root hCRpos params.hcontract

section AxiomAudit

#print axioms greenKernelExpMoment_eq_inv_characteristic
#print axioms inv_lam_le_greenKernelExpMoment
#print axioms not_twoRadius_absorbs_controlledStepRate
#print axioms PerStepBoxParams.not_sharedRate_absorption

end AxiomAudit

end ShenWork.Paper1
