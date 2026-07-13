import ShenWork.Paper1.WaveLocalStepConstruction
import ShenWork.Paper1.WaveLemma42G1Discharge

open Filter Topology Set Real

noncomputable section

namespace ShenWork.Paper1

/-- Uniform ratio comparing the exponential upper barrier with the positive
plateau of the raw lower barrier. -/
def lowerPinnedBarrierRatio (κ κtilde D M : ℝ) : ℝ :=
  max
    (M / lowerBarrierRaw κ κtilde D
      (lowerBarrierXPlus κ κtilde D))
    (κtilde / (κtilde - κ))

/-- Uniform logarithmic-slope coefficient for every lower-pinned local Green
step built with the same source weight. -/
def paperLowerPinnedStepLogSlopeCoeff
    (c lam κ κtilde D M B : ℝ) : ℝ :=
  PaperLocalFixedStepData.paperStepWeightedDerivCoeff c lam κ B *
    lowerPinnedBarrierRatio κ κtilde D M

theorem lowerPinnedBarrierRatio_nonneg
    {κ κtilde D M : ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (_hD : 0 < D) (_hM : 0 ≤ M) :
    0 ≤ lowerPinnedBarrierRatio κ κtilde D M := by
  unfold lowerPinnedBarrierRatio
  apply le_trans (show 0 ≤ κtilde / (κtilde - κ) by
    have hκtilde : 0 < κtilde := by linarith
    positivity)
  exact le_max_right _ _

/-- The lower plateau controls the upper exponential barrier by a uniform
constant.  On the left this is the positive plateau value; on the right the
two-exponential factor is bounded below by `1 - κ/κtilde`. -/
theorem upperBarrier_le_lowerPinnedBarrierRatio_mul_plateau
    {κ κtilde D M : ℝ}
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (_hM : 0 ≤ M) :
    ∀ x, upperBarrier κ M x ≤
      lowerPinnedBarrierRatio κ κtilde D M *
        lowerBarrierPlateau κ κtilde D x := by
  intro x
  let X := lowerBarrierXPlus κ κtilde D
  let P := lowerBarrierRaw κ κtilde D X
  have hκtilde : 0 < κtilde := by linarith
  have hP : 0 < P := by
    exact lowerBarrierRaw_pos_at_xplus hκ hgap hD
  by_cases hx : x ≤ X
  · have hplat : lowerBarrierPlateau κ κtilde D x = P := by
      exact lowerBarrierPlateau_eq_const_of_le hx
    have hratio : M / P ≤ lowerPinnedBarrierRatio κ κtilde D M :=
      le_max_left _ _
    have hmul := mul_le_mul_of_nonneg_right hratio hP.le
    rw [hplat]
    calc
      upperBarrier κ M x ≤ M := upperBarrier_le_M κ M x
      _ = (M / P) * P := by field_simp [ne_of_gt hP]
      _ ≤ lowerPinnedBarrierRatio κ κtilde D M * P := hmul
  · have hx' : X < x := lt_of_not_ge hx
    have hplat : lowerBarrierPlateau κ κtilde D x =
        lowerBarrierRaw κ κtilde D x :=
      lowerBarrierPlateau_eq_raw_of_xplus_lt hx'
    have hXeq :
        (κtilde - κ) * X = Real.log (κtilde * D / κ) := by
      dsimp [X]
      unfold lowerBarrierXPlus
      field_simp [ne_of_gt hgap]
    have harg : 0 < κtilde * D / κ := by positivity
    have hcrit :
        D * Real.exp (-(κtilde - κ) * X) = κ / κtilde := by
      have hnegX :
          -(κtilde - κ) * X = -Real.log (κtilde * D / κ) := by
        linarith [hXeq]
      have hexp :
          Real.exp (-(κtilde - κ) * X) =
            (κtilde * D / κ)⁻¹ := by
        rw [hnegX, Real.exp_neg, Real.exp_log harg]
      rw [hexp]
      field_simp [ne_of_gt hκ, ne_of_gt hκtilde, ne_of_gt hD]
    have hexpmono :
        Real.exp (-(κtilde - κ) * x) ≤
          Real.exp (-(κtilde - κ) * X) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hfactor :
        D * Real.exp (-(κtilde - κ) * x) ≤ κ / κtilde := by
      calc
        D * Real.exp (-(κtilde - κ) * x) ≤
            D * Real.exp (-(κtilde - κ) * X) :=
          mul_le_mul_of_nonneg_left hexpmono hD.le
        _ = κ / κtilde := hcrit
    have hrawfactor :
        Real.exp (-κ * x) ≤
          (κtilde / (κtilde - κ)) *
            lowerBarrierRaw κ κtilde D x := by
      rw [lowerBarrierRaw_eq_exp_mul]
      have hE : 0 < Real.exp (-κ * x) := Real.exp_pos _
      have hden : 0 < κtilde - κ := hgap
      have hκt : κtilde ≠ 0 := ne_of_gt hκtilde
      have hDexp_mul :
          κtilde * (D * Real.exp (-(κtilde - κ) * x)) ≤ κ := by
        calc
          κtilde * (D * Real.exp (-(κtilde - κ) * x)) ≤
              κtilde * (κ / κtilde) :=
            mul_le_mul_of_nonneg_left hfactor hκtilde.le
          _ = κ := by field_simp [hκt]
      have hgapfac :
          κtilde - κ ≤
            κtilde * (1 - D * Real.exp (-(κtilde - κ) * x)) := by
        nlinarith
      have hqfac :
          1 ≤ (κtilde / (κtilde - κ)) *
            (1 - D * Real.exp (-(κtilde - κ) * x)) := by
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀ hden).2 (by simpa using hgapfac)
      calc
        Real.exp (-κ * x) = Real.exp (-κ * x) * 1 := by ring
        _ ≤ Real.exp (-κ * x) *
            ((κtilde / (κtilde - κ)) *
              (1 - D * Real.exp (-(κtilde - κ) * x))) :=
          mul_le_mul_of_nonneg_left hqfac hE.le
        _ = (κtilde / (κtilde - κ)) *
            (Real.exp (-κ * x) *
              (1 - D * Real.exp (-(κtilde - κ) * x))) := by ring
    have hratio :
        κtilde / (κtilde - κ) ≤
          lowerPinnedBarrierRatio κ κtilde D M := le_max_right _ _
    have hraw0 : 0 ≤ lowerBarrierRaw κ κtilde D x :=
      (lowerBarrierRaw_pos_of_xminus_lt hgap hD
        (lt_trans (lowerBarrierXMinus_lt_xplus hκ hgap hD) hx')).le
    rw [hplat]
    calc
      upperBarrier κ M x ≤ Real.exp (-κ * x) := upperBarrier_le_exp κ M x
      _ ≤ (κtilde / (κtilde - κ)) *
          lowerBarrierRaw κ κtilde D x := hrawfactor
      _ ≤ lowerPinnedBarrierRatio κ κtilde D M *
          lowerBarrierRaw κ κtilde D x :=
        mul_le_mul_of_nonneg_right hratio hraw0

/-- A locally constructed Green step above the pinned plateau has a uniform
logarithmic slope bound.  Spatial antitonicity is not used: the weighted source
box and the pointwise lower pin are sufficient. -/
theorem PaperLocalFixedStepData.deriv_abs_le_mul_self_of_lowerBound
    {p : CMParams} {c lam M κ κtilde D Λ B : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (d : PaperLocalFixedStepData p c lam M κ Λ B u Z)
    (hW : ∀ x, lowerBarrierPlateau κ κtilde D x ≤ d.fixed.W x) :
    ∀ x, |deriv d.fixed.W x| ≤
      paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M B *
        d.fixed.W x := by
  intro x
  have hderiv := d.deriv_abs_le_weighted_barrier
    hlam hrpκ hrmκ hκ.le hM hB x
  have hratio :=
    upperBarrier_le_lowerPinnedBarrierRatio_mul_plateau
      hκ hgap hD hM x
  have hplateau := hW x
  have hcoeff0 := d.weightedDerivCoeff_nonneg hlam hrpκ hrmκ hB
  have hratio0 := lowerPinnedBarrierRatio_nonneg hκ hgap hD hM
  calc
    |deriv d.fixed.W x| ≤
        d.weightedDerivCoeff c lam κ * upperBarrier κ M x := hderiv
    _ ≤ d.weightedDerivCoeff c lam κ *
        (lowerPinnedBarrierRatio κ κtilde D M *
          lowerBarrierPlateau κ κtilde D x) :=
      mul_le_mul_of_nonneg_left hratio hcoeff0
    _ ≤ d.weightedDerivCoeff c lam κ *
        (lowerPinnedBarrierRatio κ κtilde D M * d.fixed.W x) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hplateau hratio0) hcoeff0
    _ = paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M B *
        d.fixed.W x := by
      unfold paperLowerPinnedStepLogSlopeCoeff
        PaperLocalFixedStepData.weightedDerivCoeff
      ring

/-- Lower-pinned trap wrapper for the pointwise lower-bound theorem. -/
theorem PaperLocalFixedStepData.deriv_abs_le_mul_self_of_lowerPinned
    {p : CMParams} {c lam M κ κtilde D Λ B : ℝ} {u Z : ℝ → ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (d : PaperLocalFixedStepData p c lam M κ Λ B u Z)
    (hW : InLowerPinnedMonotoneTrap κ M
      (lowerBarrierRaw κ κtilde D) d.fixed.W) :
    ∀ x, |deriv d.fixed.W x| ≤
      paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M B *
        d.fixed.W x :=
  d.deriv_abs_le_mul_self_of_lowerBound
    hlam hrpκ hrmκ hκ hgap hD hM hB
      (fun x => plateau_le_of_lowerPinnedRaw hW x)

theorem paperLowerPinnedStepLogSlopeCoeff_nonneg
    {c lam κ κtilde D M B : ℝ}
    (hlam : 0 < lam)
    (hrpκ : κ < greenRootPlus c lam)
    (hrmκ : κ < -greenRootMinus c lam)
    (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    0 ≤ paperLowerPinnedStepLogSlopeCoeff c lam κ κtilde D M B := by
  unfold paperLowerPinnedStepLogSlopeCoeff
  have hcoeff : 0 ≤
      PaperLocalFixedStepData.paperStepWeightedDerivCoeff c lam κ B := by
    unfold PaperLocalFixedStepData.paperStepWeightedDerivCoeff
    have hδ : 0 < greenDelta c lam := greenDelta_pos hlam
    have hrp : 0 < greenRootPlus c lam := greenRootPlus_pos hlam
    have hrm : greenRootMinus c lam < 0 := greenRootMinus_neg hlam
    have hdenp : 0 < greenRootPlus c lam - κ := by linarith
    have hdenm : 0 < -(greenRootMinus c lam + κ) := by linarith
    exact mul_nonneg (inv_nonneg.mpr hδ.le)
      (add_nonneg
        (mul_nonneg hrp.le (div_nonneg hB hdenp.le))
        (mul_nonneg (neg_nonneg.mpr hrm.le)
          (div_nonneg hB hdenm.le)))
  exact mul_nonneg hcoeff
    (lowerPinnedBarrierRatio_nonneg hκ hgap hD hM)

section AxiomAudit

#print axioms upperBarrier_le_lowerPinnedBarrierRatio_mul_plateau
#print axioms PaperLocalFixedStepData.deriv_abs_le_mul_self_of_lowerBound
#print axioms PaperLocalFixedStepData.deriv_abs_le_mul_self_of_lowerPinned
#print axioms paperLowerPinnedStepLogSlopeCoeff_nonneg

end AxiomAudit

end ShenWork.Paper1
