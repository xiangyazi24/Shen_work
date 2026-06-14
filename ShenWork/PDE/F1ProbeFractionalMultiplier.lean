import ShenWork.PDE.AnalyticSemigroupGen

/-!
# F1 probe: fractional heat multiplier bound `λ^σ e^{-λt} ≤ C_σ t^{-σ}`

This file closes the **scalar engine** of the H1.1 fractional-power Neumann
smoothing estimate

`‖A^σ e^{-tA} a‖₂ ≤ C_σ t^{-σ} ‖a‖₂`,

i.e. the elementary calculus maximization

`λ^σ · e^{-λ t} ≤ (σ / e)^σ · t^{-σ}`   (`0 ≤ σ`, `0 ≤ λ`, `0 < t`),

together with its diagonal coefficient-`ℓ²` corollary for the shifted interval
Neumann generator.  The `σ = 1` case is exactly
`AnalyticSemigroupGen.real_mul_exp_neg_mul_le_inv`
(`λ e^{-λt} ≤ 1/t`, with `(1/e)^1 < 1`); this file proves the general-`σ`
multiplier bound that the abstract `SemigroupEstimateData.fractionalNorm`
smoothing field (Paper2 Lemma 2.1, second clause) requires for `0 < σ < 1`.

These are real bounded analytic estimates discharged from Mathlib calculus
(`Real.log_le_sub_one_of_pos`) and `rpow` arithmetic.  No new operator theory
is used: the missing infrastructure flagged elsewhere is the unbounded
closed-operator / fractional-domain transport, not this scalar multiplier.
-/

noncomputable section

namespace ShenWork.PDE.F1ProbeFractionalMultiplier

open ShenWork.PDE.AnalyticSemigroupGen
open ShenWork.PDE.ResolventEstimate

/-- Base maximization: `y^σ · e^{-y} ≤ (σ / e)^σ` for `0 ≤ y`, `0 ≤ σ`.

The maximum of `y ↦ y^σ e^{-y}` over `y ≥ 0` is attained at `y = σ` with value
`(σ/e)^σ`.  Proved from `Real.log_le_sub_one_of_pos` applied to `y / σ`. -/
theorem rpow_mul_exp_neg_le {σ : ℝ} (hσ : 0 ≤ σ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ σ * Real.exp (-y) ≤ (σ / Real.exp 1) ^ σ := by
  rcases eq_or_lt_of_le hσ with hσ0 | hσpos
  · -- σ = 0: both sides reduce to `e^{-y} ≤ 1`.
    subst hσ0
    simp only [Real.rpow_zero, one_mul]
    exact (Real.exp_le_one_iff).2 (by linarith)
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · -- y = 0: `0 ≤ (σ/e)^σ`.
    have h0 : (0 : ℝ) ^ σ = 0 := Real.zero_rpow (ne_of_gt hσpos)
    rw [← hy0, h0, zero_mul]
    exact Real.rpow_nonneg (div_nonneg hσpos.le (Real.exp_nonneg 1)) σ
  -- Main case: `0 < σ`, `0 < y`.
  have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hquot_pos : 0 < y / σ := div_pos hypos hσpos
  -- `log(y/σ) ≤ y/σ - 1`.
  have hlog : Real.log (y / σ) ≤ y / σ - 1 :=
    Real.log_le_sub_one_of_pos hquot_pos
  -- Multiply by `σ > 0`: `σ·log(y/σ) ≤ y - σ`.
  have hmul : σ * Real.log (y / σ) ≤ y - σ := by
    have := mul_le_mul_of_nonneg_left hlog hσpos.le
    have hexpand : σ * (y / σ - 1) = y - σ := by
      field_simp
    linarith [this, hexpand.le, hexpand.ge]
  -- Both sides are `exp` of comparable logs.
  -- LHS log: `log (y^σ · e^{-y}) = σ·log y - y`.
  -- RHS log: `log ((σ/e)^σ) = σ·(log σ - 1)`.
  -- Difference: `σ log(y/σ) - (y - σ) ≤ 0` by `hmul`.
  have hLHS_pos : 0 < y ^ σ * Real.exp (-y) :=
    mul_pos (Real.rpow_pos_of_pos hypos σ) (Real.exp_pos _)
  have hRHS_pos : 0 < (σ / Real.exp 1) ^ σ :=
    Real.rpow_pos_of_pos (div_pos hσpos he1) σ
  rw [← Real.exp_log hLHS_pos, ← Real.exp_log hRHS_pos]
  apply Real.exp_le_exp.2
  -- Compute the two logs explicitly.
  have hlogL : Real.log (y ^ σ * Real.exp (-y)) = σ * Real.log y - y := by
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hypos σ))
        (ne_of_gt (Real.exp_pos _)),
      Real.log_rpow hypos, Real.log_exp]
    ring
  have hlogR : Real.log ((σ / Real.exp 1) ^ σ) = σ * (Real.log σ - 1) := by
    rw [Real.log_rpow (div_pos hσpos he1),
      Real.log_div (ne_of_gt hσpos) (ne_of_gt he1), Real.log_exp]
  rw [hlogL, hlogR]
  -- Goal: `σ log y - y ≤ σ(log σ - 1)`, i.e. `σ log(y/σ) ≤ y - σ` = `hmul`.
  have hsplit : Real.log (y / σ) = Real.log y - Real.log σ :=
    Real.log_div (ne_of_gt hypos) (ne_of_gt hσpos)
  rw [hsplit] at hmul
  nlinarith [hmul]

/-- Rescaled fractional multiplier bound:
`λ^σ · e^{-(λ t)} ≤ (σ / e)^σ · t^{-σ}` for `0 ≤ σ`, `0 ≤ λ`, `0 < t`.

This is the scalar smoothing engine for `A^σ e^{-tA}`. The `σ = 1` case
recovers `λ e^{-λt} ≤ 1/t` (`(1/e)^1 < 1`). -/
theorem rpow_mul_exp_neg_mul_le {σ : ℝ} (hσ : 0 ≤ σ) {lam t : ℝ}
    (hlam : 0 ≤ lam) (ht : 0 < t) :
    lam ^ σ * Real.exp (-(lam * t)) ≤ (σ / Real.exp 1) ^ σ * t ^ (-σ) := by
  -- Apply the base bound at `y = lam * t`, then peel off `t^σ`.
  have hbase := rpow_mul_exp_neg_le hσ (mul_nonneg hlam ht.le)
  -- `(lam*t)^σ = lam^σ * t^σ`.
  have hsplit : (lam * t) ^ σ = lam ^ σ * t ^ σ :=
    Real.mul_rpow hlam ht.le
  rw [hsplit, show -(lam * t) = -(lam * t) from rfl] at hbase
  -- Now `lam^σ t^σ · e^{-(lam t)} ≤ (σ/e)^σ`. Divide by `t^σ > 0`.
  have htpos : 0 < t ^ σ := Real.rpow_pos_of_pos ht σ
  have htinv : t ^ (-σ) = (t ^ σ)⁻¹ := by
    rw [Real.rpow_neg ht.le]
  have hineq : lam ^ σ * Real.exp (-(lam * t)) * t ^ σ ≤ (σ / Real.exp 1) ^ σ := by
    calc
      lam ^ σ * Real.exp (-(lam * t)) * t ^ σ
          = lam ^ σ * t ^ σ * Real.exp (-(lam * t)) := by ring
      _ ≤ (σ / Real.exp 1) ^ σ := hbase
  -- Multiply both sides of `hineq` by `(t^σ)⁻¹`.
  have hfinal := mul_le_mul_of_nonneg_right hineq (le_of_lt (inv_pos.2 htpos))
  calc
    lam ^ σ * Real.exp (-(lam * t))
        = lam ^ σ * Real.exp (-(lam * t)) * t ^ σ * (t ^ σ)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), mul_one]
    _ ≤ (σ / Real.exp 1) ^ σ * (t ^ σ)⁻¹ := hfinal
    _ = (σ / Real.exp 1) ^ σ * t ^ (-σ) := by rw [htinv]

/-! ### Diagonal coefficient corollary for the shifted Neumann generator -/

/-- Fractional-power generator coefficient `A^σ e^{-tA}` for `A = -Δ_N + ω`. -/
def shiftedNeumannFractionalGeneratorHeatCoeff (ω : ℝ) (σ t : ℝ)
    (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((shiftedNeumannEigenvalue ω n : ℝ) ^ σ : ℝ) *
    shiftedNeumannHeatCoeff ω t a n

/-- Per-coefficient squared fractional smoothing bound:
`‖A^σ e^{-tA} a n‖² ≤ ((σ/e)^σ · t^{-σ})² · ‖a n‖²`.

This is the genuine general-`σ` analogue of
`AnalyticSemigroupGen.shiftedNeumannGeneratorHeatCoeff_sq_le` (the `σ = 1`,
constant `1/t` case); it is the diagonal scalar core of the
`SemigroupEstimateData.fractionalNorm` smoothing estimate. -/
theorem shiftedNeumannFractionalGeneratorHeatCoeff_sq_le
    {ω σ t : ℝ} (hω : 0 ≤ ω) (hσ : 0 ≤ σ) (ht : 0 < t)
    (a : ℕ → ℂ) (n : ℕ) :
    ‖shiftedNeumannFractionalGeneratorHeatCoeff ω σ t a n‖ ^ 2 ≤
      ((σ / Real.exp 1) ^ σ * t ^ (-σ)) ^ 2 * ‖a n‖ ^ 2 := by
  set r := shiftedNeumannEigenvalue ω n with hrdef
  have hr : 0 ≤ r := by
    simpa [hrdef] using shiftedNeumannEigenvalue_nonneg hω n
  -- Scalar multiplier bound at `λ = r`.
  have hcoef : r ^ σ * Real.exp (-(r * t)) ≤ (σ / Real.exp 1) ^ σ * t ^ (-σ) :=
    rpow_mul_exp_neg_mul_le hσ hr ht
  have hcoef_nonneg : 0 ≤ r ^ σ * Real.exp (-(r * t)) :=
    mul_nonneg (Real.rpow_nonneg hr σ) (Real.exp_nonneg _)
  have hC_nonneg : 0 ≤ (σ / Real.exp 1) ^ σ * t ^ (-σ) :=
    mul_nonneg
      (Real.rpow_nonneg (div_nonneg hσ (Real.exp_nonneg 1)) σ)
      (Real.rpow_nonneg ht.le (-σ))
  have hmul :
      r ^ σ * Real.exp (-(r * t)) * ‖a n‖ ≤
        ((σ / Real.exp 1) ^ σ * t ^ (-σ)) * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hcoef (norm_nonneg (a n))
  calc
    ‖shiftedNeumannFractionalGeneratorHeatCoeff ω σ t a n‖ ^ 2
        =
          (‖((r ^ σ : ℝ) : ℂ)‖ *
            (‖(Real.exp (-(r * t)) : ℂ)‖ * ‖a n‖)) ^ 2 := by
          rw [shiftedNeumannFractionalGeneratorHeatCoeff, shiftedNeumannHeatCoeff,
            ← hrdef, norm_mul, norm_mul]
    _ =
          (r ^ σ * Real.exp (-(r * t)) * ‖a n‖) ^ 2 := by
          rw [Complex.norm_of_nonneg (Real.rpow_nonneg hr σ),
            Complex.norm_of_nonneg (Real.exp_nonneg (-(r * t)))]
          ring
    _ ≤ (((σ / Real.exp 1) ^ σ * t ^ (-σ)) * ‖a n‖) ^ 2 := by
          exact
            (sq_le_sq₀
              (mul_nonneg hcoef_nonneg (norm_nonneg _))
              (mul_nonneg hC_nonneg (norm_nonneg _))).mpr hmul
    _ = ((σ / Real.exp 1) ^ σ * t ^ (-σ)) ^ 2 * ‖a n‖ ^ 2 := by ring

end ShenWork.PDE.F1ProbeFractionalMultiplier
