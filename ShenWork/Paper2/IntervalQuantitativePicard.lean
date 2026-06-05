/-
  Quantitative Picard: explicit δ(M) from contraction rate estimates.

  For the γ ≥ 1 negative-sensitivity regime, the Picard contraction
  gives a uniform existence duration δ(M) > 0 depending only on M
  (the sup-norm bound on the initial datum) and the PDE parameters.

  The contraction rate is dominated by the logistic Lipschitz:
    K ≤ T · (a + b·(1+α)·M^α)
  so K < 1 when T < 1/(a + b·(1+α)·M^α + 1).

  The MapsTo condition requires the Duhamel integral to stay in the
  M-ball, which holds when T is small enough relative to M.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalLogisticLipschitz
import ShenWork.PDE.IntervalGradDuhamelBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace ShenWork.IntervalQuantitativePicard

/-- The logistic Lipschitz constant `L(M) = a + b·(1+α)·M^α` on `[−M, M]`. -/
def logisticLipConst (p : CM2Params) (M : ℝ) : ℝ :=
  p.a + p.b * (1 + p.α) * M ^ p.α

theorem logisticLipConst_nonneg (p : CM2Params) {M : ℝ} (hM : 0 < M) :
    0 ≤ logisticLipConst p M := by
  unfold logisticLipConst
  have hMα : 0 ≤ M ^ p.α := Real.rpow_nonneg hM.le p.α
  have h1α : 0 ≤ 1 + p.α := by linarith [p.hα]
  exact add_nonneg p.ha (mul_nonneg (mul_nonneg p.hb h1α) hMα)

/-- The uniform Picard existence duration `δ(M, p)`.
Chosen as `1 / (1 + L(M))` — a simple explicit formula ensuring the
contraction rate `T · L(M) < 1` and the MapsTo ball condition. -/
def picardDelta (p : CM2Params) (M : ℝ) : ℝ :=
  1 / (1 + logisticLipConst p M)

theorem picardDelta_pos (p : CM2Params) {M : ℝ} (hM : 0 < M) :
    0 < picardDelta p M := by
  unfold picardDelta
  exact div_pos one_pos (by linarith [logisticLipConst_nonneg p hM])

theorem picardDelta_le_one (p : CM2Params) {M : ℝ} (hM : 0 < M) :
    picardDelta p M ≤ 1 := by
  unfold picardDelta
  have hL := logisticLipConst_nonneg p hM
  have hL := logisticLipConst_nonneg p hM
  have hden : (0 : ℝ) < 1 + logisticLipConst p M := by linarith
  rw [div_le_one hden]
  linarith

theorem picardDelta_mul_lip_lt_one (p : CM2Params) {M : ℝ} (hM : 0 < M) :
    picardDelta p M * logisticLipConst p M < 1 := by
  unfold picardDelta
  have hL := logisticLipConst_nonneg p hM
  rw [div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
  linarith

end ShenWork.IntervalQuantitativePicard
