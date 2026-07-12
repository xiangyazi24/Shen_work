/-
  ShenWork/Paper3/IntervalDomainRelativeEntropy.lean

  **Fable roadmap D / L6 — pointwise nonnegativity of the relative-entropy
  Lyapunov integrand.**

  The global-stability half of Paper 3 (Thm 2.3–2.5) uses the entropy functional
    H(u) = ∫_Ω [ u ln(u/u*) − (u − u*) ] dx ≥ 0,   (= 0 iff u ≡ u*)
  as the Lyapunov functional.  Its nonnegativity is pointwise convexity: the
  integrand `s ↦ s ln(s/u*) − (s − u*)` is ≥ 0 for `s, u* > 0`, with a strict
  minimum 0 at `s = u*`.  This reduces to Gibbs' inequality `z ln z ≥ z − 1`
  (`z = s/u*`), itself the standard `log z ≤ z − 1` applied at `z⁻¹`.

  No `sorry`/`admit`/custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace ShenWork.Paper3.RelativeEntropy

open Real

/-- **Gibbs' inequality core:** `z − 1 ≤ z · log z` for `z > 0`. -/
theorem z_mul_log_ge {z : ℝ} (hz : 0 < z) : z - 1 ≤ z * Real.log z := by
  have hinv : (0 : ℝ) < z⁻¹ := by positivity
  have h := Real.log_le_sub_one_of_pos hinv          -- log z⁻¹ ≤ z⁻¹ − 1
  rw [Real.log_inv] at h                             -- −log z ≤ z⁻¹ − 1
  have h2 : (1 : ℝ) - z⁻¹ ≤ Real.log z := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hz.le       -- z·(1 − z⁻¹) ≤ z·log z
  have hzz : z * (1 - z⁻¹) = z - 1 := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (ne_of_gt hz)]
  rw [hzz] at h3
  exact h3

/-- **Relative-entropy integrand is nonnegative (Fable D/L6):**
`0 ≤ s · log(s/u*) − (s − u*)` for `s, u* > 0`.  Zero iff `s = u*`. -/
theorem relEntropy_integrand_nonneg {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    0 ≤ s * Real.log (s / u) - (s - u) := by
  have hz : 0 < s / u := by positivity
  have hcore := z_mul_log_ge hz                       -- s/u − 1 ≤ (s/u)·log(s/u)
  have key : s * Real.log (s / u) = u * ((s / u) * Real.log (s / u)) := by
    field_simp
  have key2 : s - u = u * (s / u - 1) := by field_simp
  rw [key, key2]
  have hmul := mul_le_mul_of_nonneg_left hcore hu.le   -- u·(s/u−1) ≤ u·((s/u)·log(s/u))
  linarith

/-- **Entropy dissipation reaction-term sign (Fable D):**
`0 ≤ log(s/u*) · (s^α − u*^α)` for `s, u*, α > 0` — the two factors share the sign
of `(s − u*)`, so the logistic reaction term `−b∫ u·log(u/u*)·(u^α−u*^α)` in `dH/dt`
is dissipative (≤ 0). -/
theorem log_mul_rpow_diff_nonneg {s u alpha : ℝ}
    (hs : 0 < s) (hu : 0 < u) (ha : 0 < alpha) :
    0 ≤ Real.log (s / u) * (s ^ alpha - u ^ alpha) := by
  have hlogeq : Real.log (s / u) = Real.log s - Real.log u :=
    Real.log_div (ne_of_gt hs) (ne_of_gt hu)
  rw [hlogeq]
  rcases le_total s u with h | h
  · have hlog : Real.log s - Real.log u ≤ 0 := by
      have : Real.log s ≤ Real.log u := by gcongr
      linarith
    have hrpow : s ^ alpha - u ^ alpha ≤ 0 := by
      have : s ^ alpha ≤ u ^ alpha := by gcongr
      linarith
    have := mul_nonneg (neg_nonneg.mpr hlog) (neg_nonneg.mpr hrpow)
    rwa [neg_mul_neg] at this
  · have hlog : 0 ≤ Real.log s - Real.log u := by
      have : Real.log u ≤ Real.log s := by gcongr
      linarith
    have hrpow : 0 ≤ s ^ alpha - u ^ alpha := by
      have : u ^ alpha ≤ s ^ alpha := by gcongr
      linarith
    exact mul_nonneg hlog hrpow

end ShenWork.Paper3.RelativeEntropy
