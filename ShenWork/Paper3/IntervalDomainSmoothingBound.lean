/-
  ShenWork/Paper3/IntervalDomainSmoothingBound.lean

  **Fable roadmap L2 (scalar core) — the analytic-smoothing bound that REPLACES
  Henry's fractional-power sectorial theory.**

  The diagonal semigroup `e^{tL}` on the Neumann cosine modes has, per mode,
  factor `e^{-λ_k t}`.  The `X^s → X^{s+θ}` smoothing estimate reduces to the
  single scalar fact
    sup_{x ≥ 0}  x^{p} · e^{-x t}  ≤  (p/(e t))^{p}     (p = θ/2, t > 0),
  the maximum being attained at `x = p/t`.  This is one line of calculus (the
  standard `log z ≤ z − 1`), NOT an abstract sectorial/fractional-power theory.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace ShenWork.Paper3.SmoothingBound

open Real

/-- **Scalar smoothing core (dimensionless form):** `y^p · e^{-y} ≤ (p/e)^p` for
`y ≥ 0`, `p > 0`.  Maximum at `y = p`.  Pure calculus via `log z ≤ z − 1`. -/
theorem rpow_mul_exp_neg_le {y p : ℝ} (hy : 0 ≤ y) (hp : 0 < p) :
    y ^ p * Real.exp (-y) ≤ (p / Real.exp 1) ^ p := by
  have hpe : 0 < p / Real.exp 1 := by positivity
  rcases eq_or_lt_of_le hy with h0 | hy0
  · -- y = 0
    rw [← h0, Real.zero_rpow (ne_of_gt hp), zero_mul]
    positivity
  · -- y > 0 : compare logs
    have hLHSpos : 0 < y ^ p * Real.exp (-y) := by positivity
    have hRHSpos : 0 < (p / Real.exp 1) ^ p := by positivity
    have hloglhs : Real.log (y ^ p * Real.exp (-y)) = p * Real.log y - y := by
      rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hy0 p))
            (ne_of_gt (Real.exp_pos _)),
        Real.log_rpow hy0, Real.log_exp]; ring
    have hlogrhs : Real.log ((p / Real.exp 1) ^ p) = p * Real.log p - p := by
      rw [Real.log_rpow hpe,
        Real.log_div (ne_of_gt hp) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]; ring
    have hkey : p * Real.log y - y ≤ p * Real.log p - p := by
      have hz : 0 < y / p := by positivity
      have hlog := Real.log_le_sub_one_of_pos hz         -- log(y/p) ≤ y/p − 1
      rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hp)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hp.le
      have hfs : p * (y / p - 1) = y - p := by field_simp
      nlinarith [hmul, hfs]
    have hlogle : Real.log (y ^ p * Real.exp (-y))
        ≤ Real.log ((p / Real.exp 1) ^ p) := by
      rw [hloglhs, hlogrhs]; linarith
    calc
      y ^ p * Real.exp (-y)
          = Real.exp (Real.log (y ^ p * Real.exp (-y))) := (Real.exp_log hLHSpos).symm
      _ ≤ Real.exp (Real.log ((p / Real.exp 1) ^ p)) := Real.exp_le_exp.mpr hlogle
      _ = (p / Real.exp 1) ^ p := Real.exp_log hRHSpos

/-- **Scalar smoothing core (semigroup form):** `x^p · e^{-x t} ≤ (p/(e t))^p`
for `x ≥ 0`, `p > 0`, `t > 0` — the per-mode smoothing factor that gives the
`X^s → X^{s+θ}` estimate with `p = θ/2`.  Substitute `y = x t` into the
dimensionless bound. -/
theorem rpow_mul_exp_neg_mul_le {x p t : ℝ} (hx : 0 ≤ x) (hp : 0 < p) (ht : 0 < t) :
    x ^ p * Real.exp (-(x * t)) ≤ (p / (Real.exp 1 * t)) ^ p := by
  have hxt : 0 ≤ x * t := mul_nonneg hx ht.le
  have hbase := rpow_mul_exp_neg_le hxt hp             -- (xt)^p e^{-xt} ≤ (p/e)^p
  have hxtp : (x * t) ^ p = x ^ p * t ^ p :=
    Real.mul_rpow hx ht.le
  rw [hxtp] at hbase
  -- divide by t^p > 0
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hstep : x ^ p * Real.exp (-(x * t)) ≤ (p / Real.exp 1) ^ p / t ^ p := by
    rw [le_div_iff₀ htp]
    calc x ^ p * Real.exp (-(x * t)) * t ^ p
        = x ^ p * t ^ p * Real.exp (-(x * t)) := by ring
      _ ≤ (p / Real.exp 1) ^ p := hbase
  have hrw : (p / Real.exp 1) ^ p / t ^ p = (p / (Real.exp 1 * t)) ^ p := by
    rw [← Real.div_rpow (by positivity) ht.le]
    congr 1
    field_simp
  rwa [hrw] at hstep

/-- **Fable L1 per-mode decay core:** if a modal rate `s ≤ −δ` then its semigroup
factor decays at rate `δ`: `exp(s·t) ≤ exp(−δ·t)` for `t ≥ 0`.  Applied to
`s = σ_k ≤ −δ` (from the spectral gap) this gives the diagonal decay
`‖e^{tL}φ‖_s ≤ e^{−δt}‖φ‖_s` mode by mode. -/
theorem exp_mul_le_of_rate_le {s delta t : ℝ} (hs : s ≤ -delta) (ht : 0 ≤ t) :
    Real.exp (s * t) ≤ Real.exp (-delta * t) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right hs ht

end ShenWork.Paper3.SmoothingBound
