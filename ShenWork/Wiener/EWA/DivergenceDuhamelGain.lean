import ShenWork.PDE.HeatSemigroup
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Divergence–Duhamel gain (χ₀<0 positive-time A³ weighted-Wiener bootstrap base)

This file is the cleanly-scoped analytic *base* of the χ₀<0 positive-time A³
weighted-Wiener bootstrap ladder.  It is **pure analysis** — no EWA structure,
no `whnf` risk — stated abstractly over a per-mode coefficient sequence
`Ŝ : ℕ → ℝ → ℝ` and a pointwise bound.

The three building blocks:

1. `duhamel_sqrt_decay_bound` — the scalar `√λ`-contraction of the heat
   time-integral:
   `√λ · ∫_a^t e^{−(t−s)λ} ds ≤ 1/√λ` for `λ > 0`, `a ≤ t`.
   (FTC gives `∫_a^t e^{−(t−s)λ} ds = (1−e^{−(t−a)λ})/λ`, and
   `√λ · (1−e^{−(t−a)λ})/λ = (1−e^{−(t−a)λ})/√λ ≤ 1/√λ`.)

2. `divGain_const` — the spectral weight-gain constant
   `Cdiv := √(1+π²)/π`, with `0 < Cdiv` and the per-mode bound
   `√(1+λ_k)/√λ_k ≤ Cdiv` for `k ≥ 1`, where `λ_k = (kπ)²`.  The ratio
   `√(1+λ_k)/√λ_k = √(1+1/(kπ)²)` is decreasing in `k`, with sup at `k = 1`.

3. `divergence_duhamel_gain_per_mode` — the weighted per-mode bound combining
   1 + 2:
   `(1+λ_k)^{(r+1)/2} · (√λ_k · ∫_a^t e^{−(t−s)λ_k} |Ŝ_k(s)| ds)
     ≤ Cdiv · (1+λ_k)^{r/2} · Esrc_k`,
   for `k ≥ 1`, `r ≥ 0`, given `|Ŝ_k(s)| ≤ Esrc_k` on `[a,t]`.
-/

open Set Real MeasureTheory intervalIntegral

namespace ShenWork.EWA

/-- Spectral eigenvalue `λ_k = (kπ)²` (the project's `unitIntervalCosineEigenvalue`). -/
local notation "lam" => unitIntervalCosineEigenvalue

/-! ### 1. The scalar `√λ`-decay bound of the heat time-integral. -/

/-- The heat time-integral identity on `[a,t]`:
`∫_a^t e^{−(t−s)λ} ds = (1 − e^{−(t−a)λ})/λ` for `λ > 0`.
Proved by factoring `e^{−(t−s)λ} = e^{−tλ}·e^{sλ}` and `∫ e^{sλ}`. -/
theorem heat_kernel_interval_integral (lam' t a : ℝ) (hlam : 0 < lam') :
    (∫ s in a..t, Real.exp (-((t - s) * lam')))
      = (1 - Real.exp (-((t - a) * lam'))) / lam' := by
  have hcongr : (∫ s in a..t, Real.exp (-((t - s) * lam')))
      = ∫ s in a..t, Real.exp (-(t * lam')) * Real.exp (s * lam') := by
    apply intervalIntegral.integral_congr; intro s _
    change Real.exp (-((t - s) * lam')) = Real.exp (-(t * lam')) * Real.exp (s * lam')
    rw [← Real.exp_add]; congr 1; ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hexp : (∫ s in a..t, Real.exp (s * lam'))
      = (Real.exp (t * lam') - Real.exp (a * lam')) / lam' := by
    rw [integral_comp_mul_right (fun x => Real.exp x) (ne_of_gt hlam), integral_exp]
    simp [div_eq_inv_mul, mul_comm]
  rw [hexp]
  have he1 : Real.exp (-(t * lam')) * Real.exp (t * lam') = 1 := by
    rw [← Real.exp_add, show -(t * lam') + t * lam' = 0 by ring, Real.exp_zero]
  have he2 : Real.exp (-(t * lam')) * Real.exp (a * lam') = Real.exp (-((t - a) * lam')) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [mul_div_assoc', mul_sub, he1, he2]

/-- **The scalar `√λ`-decay bound.** For `λ > 0` and `a ≤ t`:
`√λ · ∫_a^t e^{−(t−s)λ} ds ≤ 1/√λ`.  Since the integral is
`(1−e^{−(t−a)λ})/λ` with `0 ≤ 1−e^{−(t−a)λ} ≤ 1`. -/
theorem duhamel_sqrt_decay_bound (lam' t a : ℝ) (hlam : 0 < lam') (hat : a ≤ t) :
    Real.sqrt lam' * (∫ s in a..t, Real.exp (-((t - s) * lam'))) ≤ 1 / Real.sqrt lam' := by
  rw [heat_kernel_interval_integral lam' t a hlam]
  have hsqrt_pos : 0 < Real.sqrt lam' := Real.sqrt_pos.mpr hlam
  have hsq : Real.sqrt lam' * Real.sqrt lam' = lam' := Real.mul_self_sqrt hlam.le
  have hexp_le_one : Real.exp (-((t - a) * lam')) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (t - a) * lam' := mul_nonneg (by linarith) hlam.le
    linarith
  have hexp_nonneg : 0 ≤ Real.exp (-((t - a) * lam')) := Real.exp_nonneg _
  have hnum_le : 1 - Real.exp (-((t - a) * lam')) ≤ 1 := by linarith
  have hnum_nonneg : 0 ≤ 1 - Real.exp (-((t - a) * lam')) := by linarith
  calc Real.sqrt lam' * ((1 - Real.exp (-((t - a) * lam'))) / lam')
      ≤ Real.sqrt lam' * (1 / lam') := by
        gcongr
    _ = 1 / Real.sqrt lam' := by
        rw [mul_one_div, div_eq_div_iff hlam.ne' hsqrt_pos.ne', one_mul]; exact hsq

/-! ### 2. The spectral weight-gain constant `Cdiv = √(1+π²)/π`. -/

/-- The divergence weight-gain constant `Cdiv := √(1+π²)/π`.  This is the value of
the decreasing-in-`k` ratio `√(1+λ_k)/√λ_k = √(1+1/(kπ)²)` at its supremum `k=1`. -/
noncomputable def Cdiv : ℝ := Real.sqrt (1 + Real.pi ^ 2) / Real.pi

theorem Cdiv_pos : 0 < Cdiv := by
  unfold Cdiv
  apply div_pos
  · apply Real.sqrt_pos.mpr; positivity
  · exact Real.pi_pos

/-- The spectral weight `√(λ_k) = kπ` for the eigenvalue `λ_k = (kπ)²`. -/
theorem sqrt_lam (k : ℕ) : Real.sqrt (lam k) = (k : ℝ) * Real.pi := by
  unfold unitIntervalCosineEigenvalue
  rw [Real.sqrt_sq (by positivity)]

/-- **The per-mode weight-gain bound.** `√(1+λ_k)/√λ_k ≤ Cdiv` for `k ≥ 1`.
Equivalently `√(1+(kπ)²) ≤ k·√(1+π²)`, by squaring (`1 ≤ k²`). -/
theorem divGain_const (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt (1 + lam k) / Real.sqrt (lam k) ≤ Cdiv := by
  unfold Cdiv
  rw [sqrt_lam k]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpi_pos : 0 < (k : ℝ) * Real.pi := by positivity
  rw [div_le_div_iff₀ hkpi_pos Real.pi_pos]
  -- want: √(1+λ_k)·π ≤ √(1+π²)·(kπ)
  have hkey : Real.sqrt (1 + lam k) ≤ (k : ℝ) * Real.sqrt (1 + Real.pi ^ 2) := by
    rw [show (k : ℝ) * Real.sqrt (1 + Real.pi ^ 2)
          = Real.sqrt ((k : ℝ) ^ 2 * (1 + Real.pi ^ 2)) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    unfold unitIntervalCosineEigenvalue
    nlinarith [hk1, Real.pi_pos, sq_nonneg ((k : ℝ) * Real.pi)]
  calc Real.sqrt (1 + lam k) * Real.pi
      ≤ ((k : ℝ) * Real.sqrt (1 + Real.pi ^ 2)) * Real.pi := by
        apply mul_le_mul_of_nonneg_right hkey Real.pi_pos.le
    _ = Real.sqrt (1 + Real.pi ^ 2) * ((k : ℝ) * Real.pi) := by ring

/-! ### 3. The weighted per-mode divergence–Duhamel gain. -/

/-- **The weighted per-mode divergence–Duhamel gain.**  For `k ≥ 1`, `r ≥ 0`,
`a ≤ t`, a coefficient sequence `Ŝ : ℕ → ℝ → ℝ`, and a pointwise bound
`|Ŝ_k(s)| ≤ Esrc_k` on `[a,t]`:
`(1+λ_k)^{(r+1)/2} · (√λ_k · ∫_a^t e^{−(t−s)λ_k} |Ŝ_k(s)| ds)
  ≤ Cdiv · (1+λ_k)^{r/2} · Esrc_k`.

Proof: bound the integrand `e·|Ŝ| ≤ e·Esrc`, factor out `Esrc`, apply the scalar
`√λ`-decay bound (1) and split `(1+λ)^{(r+1)/2} = (1+λ)^{r/2}·√(1+λ)`, then the
weight-gain bound (2) `√(1+λ_k)/√λ_k ≤ Cdiv`. -/
theorem divergence_duhamel_gain_per_mode
    (Ŝ : ℕ → ℝ → ℝ) (Esrc : ℕ → ℝ) (k : ℕ) (r t a : ℝ)
    (hk : 1 ≤ k) (_hr : 0 ≤ r) (hat : a ≤ t)
    (hŜcont : Continuous (Ŝ k))
    (hbound : ∀ s ∈ Set.uIcc a t, |Ŝ k s| ≤ Esrc k) :
    (1 + lam k) ^ ((r + 1) / 2)
        * (Real.sqrt (lam k)
            * ∫ s in a..t, Real.exp (-((t - s) * lam k)) * |Ŝ k s|)
      ≤ Cdiv * (1 + lam k) ^ (r / 2) * Esrc k := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlam_pos : 0 < lam k := by
    unfold unitIntervalCosineEigenvalue; positivity
  have hone_lam_pos : 0 < 1 + lam k := by linarith
  have hsqrt_lam_pos : 0 < Real.sqrt (lam k) := Real.sqrt_pos.mpr hlam_pos
  -- `Esrc k ≥ 0` from the pointwise bound at `s = a` (`a ∈ uIcc a t`).
  have hEsrc_nonneg : 0 ≤ Esrc k :=
    le_trans (abs_nonneg _) (hbound a (Set.left_mem_uIcc))
  -- Integrand bound: `e^{−(t−s)λ}·|Ŝ| ≤ Esrc · e^{−(t−s)λ}` on `[a,t]`.
  have hint_le :
      (∫ s in a..t, Real.exp (-((t - s) * lam k)) * |Ŝ k s|)
        ≤ Esrc k * ∫ s in a..t, Real.exp (-((t - s) * lam k)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hat
    · apply Continuous.intervalIntegrable
      exact (Real.continuous_exp.comp (by fun_prop)).mul hŜcont.abs
    · apply Continuous.intervalIntegrable; fun_prop
    · intro s hs
      have hs' : s ∈ Set.uIcc a t := by
        rw [Set.uIcc_of_le hat]; exact hs
      have hexp_nonneg : 0 ≤ Real.exp (-((t - s) * lam k)) := Real.exp_nonneg _
      calc Real.exp (-((t - s) * lam k)) * |Ŝ k s|
          ≤ Real.exp (-((t - s) * lam k)) * Esrc k := by
            apply mul_le_mul_of_nonneg_left (hbound s hs') hexp_nonneg
        _ = Esrc k * Real.exp (-((t - s) * lam k)) := by ring
  -- Combine: `√λ · ∫ e·|Ŝ| ≤ Esrc · (√λ · ∫ e) ≤ Esrc · (1/√λ)`.
  have hsqrt_int_le :
      Real.sqrt (lam k) * (∫ s in a..t, Real.exp (-((t - s) * lam k)) * |Ŝ k s|)
        ≤ Esrc k * (1 / Real.sqrt (lam k)) := by
    calc Real.sqrt (lam k)
            * (∫ s in a..t, Real.exp (-((t - s) * lam k)) * |Ŝ k s|)
        ≤ Real.sqrt (lam k) * (Esrc k * ∫ s in a..t, Real.exp (-((t - s) * lam k))) := by
          apply mul_le_mul_of_nonneg_left hint_le hsqrt_lam_pos.le
      _ = Esrc k * (Real.sqrt (lam k) * ∫ s in a..t, Real.exp (-((t - s) * lam k))) := by
          ring
      _ ≤ Esrc k * (1 / Real.sqrt (lam k)) := by
          apply mul_le_mul_of_nonneg_left
            (duhamel_sqrt_decay_bound (lam k) t a hlam_pos hat) hEsrc_nonneg
  -- Split the weight `(1+λ)^{(r+1)/2} = (1+λ)^{r/2} · √(1+λ)`.
  have hsplit : (1 + lam k) ^ ((r + 1) / 2)
      = (1 + lam k) ^ (r / 2) * Real.sqrt (1 + lam k) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hone_lam_pos]
    congr 1; ring
  -- Assemble.
  rw [hsplit]
  have hweight_nonneg : 0 ≤ (1 + lam k) ^ (r / 2) :=
    Real.rpow_nonneg hone_lam_pos.le _
  have hsqrt_one_lam_nonneg : 0 ≤ Real.sqrt (1 + lam k) := Real.sqrt_nonneg _
  calc (1 + lam k) ^ (r / 2) * Real.sqrt (1 + lam k)
          * (Real.sqrt (lam k)
              * ∫ s in a..t, Real.exp (-((t - s) * lam k)) * |Ŝ k s|)
      ≤ (1 + lam k) ^ (r / 2) * Real.sqrt (1 + lam k) * (Esrc k * (1 / Real.sqrt (lam k))) := by
        apply mul_le_mul_of_nonneg_left hsqrt_int_le
        exact mul_nonneg hweight_nonneg hsqrt_one_lam_nonneg
    _ = (1 + lam k) ^ (r / 2) * Esrc k
          * (Real.sqrt (1 + lam k) / Real.sqrt (lam k)) := by
        rw [div_eq_mul_inv, one_div]; ring
    _ ≤ (1 + lam k) ^ (r / 2) * Esrc k * Cdiv := by
        apply mul_le_mul_of_nonneg_left (divGain_const k hk)
        exact mul_nonneg hweight_nonneg hEsrc_nonneg
    _ = Cdiv * (1 + lam k) ^ (r / 2) * Esrc k := by ring

end ShenWork.EWA
