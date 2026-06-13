/-
# Parabolic ∂ₓₓ-Duhamel L∞ estimate — the DIRECT multiplier bound (per-mode)

This file formalizes the SHARPER, CLEANER per-mode bound for the second-spatial-
derivative Neumann-heat Duhamel term.  Where the committed IBP route
(`parabolicDuhamel_perMode_bound`) gives `|D_k| ≤ 2·Bv + (1/λ)·Bv'` and needs a
`C¹`-in-time coefficient, the direct multiplier estimate needs ONLY continuity
and `λ > 0`, with NO time-derivative hypothesis:

  `|D_k(t)| = λ·|∫₀ᵗ e^{-λ(t−s)} fhat(s) ds|`
    `≤ λ·∫₀ᵗ e^{-λ(t−s)} |fhat(s)| ds`
    `≤ λ·Bv·∫₀ᵗ e^{-λ(t−s)} ds`
    `= λ·Bv·(1 − e^{-λt})/λ = Bv·(1 − e^{-λt}) ≤ Bv`.

The crux is the committed `parabolic_weight_integral_eq`:
`∫₀ᵗ e^{-λ(t−s)} ds = (1 − e^{-λt})/λ`, so `λ·that = 1 − e^{-λt} ≤ 1`.

## What is proved (0 sorry, 0 admit, 0 custom axiom, 0 native_decide)

* `parabolicDuhamel_perMode_bound_direct` — `|D_k(t)| ≤ Bv` from continuity + `λ>0`.
* `parabolicDuhamel_sndDeriv_summable_direct` — `Summable (fun k => |D_k|)` from
  PURE source-ℓ¹ `Summable Bv` (no `Bv'`, no `1/λ` term).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ShenWork.PDE.IntervalParabolicDuhamelSecondDerivBoundedWeight

open MeasureTheory intervalIntegral
open scoped Topology BigOperators
open ShenWork.IntervalParabolicDuhamelSecondDerivBoundedWeight

namespace ShenWork.IntervalParabolicDuhamelDirectBound

noncomputable section

/-- **The DIRECT per-mode multiplier bound.**
With `λ > 0`, `0 ≤ t`, continuity of `fhat`, and a sup bound `|fhat s| ≤ Bv` on
`[0,t]`, the second-spatial-derivative Duhamel quantity satisfies `|D_k(t)| ≤ Bv`.
NO time-derivative hypothesis: the unbounded `λ` is canceled directly by the
time-integral of the parabolic weight, `λ·∫₀ᵗ e^{-λ(t−s)} ds = 1 − e^{-λt} ≤ 1`. -/
theorem parabolicDuhamel_perMode_bound_direct {lam t Bv : ℝ} {fhat : ℝ → ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t)
    (hfc : Continuous fhat)
    (hBv : ∀ s ∈ Set.Icc (0 : ℝ) t, |fhat s| ≤ Bv) :
    |duhamelSecondMode lam t fhat| ≤ Bv := by
  have hBv_nonneg : 0 ≤ Bv := le_trans (abs_nonneg _) (hBv 0 ⟨le_refl _, ht⟩)
  unfold duhamelSecondMode
  rw [abs_neg, abs_mul, abs_of_pos hlam]
  -- pointwise bound: |parabolicWeight · fhat| ≤ parabolicWeight · Bv on [0,t]
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t,
      |parabolicWeight lam t s * fhat s| ≤ parabolicWeight lam t s * Bv := by
    intro s hs
    rw [abs_mul, abs_of_nonneg (parabolicWeight_nonneg lam t s)]
    exact mul_le_mul_of_nonneg_left (hBv s hs) (parabolicWeight_nonneg lam t s)
  have hwc : Continuous (parabolicWeight lam t) := parabolicWeight_continuous lam t
  have hintbound : |∫ s in (0 : ℝ)..t, parabolicWeight lam t s * fhat s|
      ≤ Bv * ((1 - Real.exp (-(lam * t))) / lam) := by
    calc |∫ s in (0 : ℝ)..t, parabolicWeight lam t s * fhat s|
        ≤ ∫ s in (0 : ℝ)..t, |parabolicWeight lam t s * fhat s| :=
          intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ s in (0 : ℝ)..t, parabolicWeight lam t s * Bv :=
          intervalIntegral.integral_mono_on ht
            ((Continuous.intervalIntegrable (hwc.mul hfc) 0 t).abs)
            ((hwc.mul_const Bv).intervalIntegrable 0 t)
            hpt
      _ = Bv * ((1 - Real.exp (-(lam * t))) / lam) := by
          rw [show (fun s => parabolicWeight lam t s * Bv)
                = (fun s => Bv * parabolicWeight lam t s) from by funext s; ring,
            intervalIntegral.integral_const_mul,
            parabolic_weight_integral_eq hlam.ne']
  -- multiply through by lam and cancel
  have hkey : lam * |∫ s in (0 : ℝ)..t, parabolicWeight lam t s * fhat s|
      ≤ Bv * (1 - Real.exp (-(lam * t))) := by
    calc lam * |∫ s in (0 : ℝ)..t, parabolicWeight lam t s * fhat s|
        ≤ lam * (Bv * ((1 - Real.exp (-(lam * t))) / lam)) :=
          mul_le_mul_of_nonneg_left hintbound hlam.le
      _ = Bv * (1 - Real.exp (-(lam * t))) := by
          have hne := hlam.ne'
          field_simp
  have hle1 : Bv * (1 - Real.exp (-(lam * t))) ≤ Bv := by
    have hfac : (1 : ℝ) - Real.exp (-(lam * t)) ≤ 1 := by
      have := Real.exp_pos (-(lam * t)); linarith
    calc Bv * (1 - Real.exp (-(lam * t)))
        ≤ Bv * 1 := mul_le_mul_of_nonneg_left hfac hBv_nonneg
      _ = Bv := mul_one _
  linarith

/-- **L∞ summation majorant from PURE source-ℓ¹.**
Given per-mode `lam k > 0`, continuous coefficients `fhat k`, sup bounds `Bv k`,
and the single honest ℓ¹ input `Summable Bv`, the second-spatial-derivative
Duhamel coefficients are absolutely summable.  No `Bv'`, no `1/λ` term: comparison
against `Bv k` directly via the direct per-mode bound. -/
theorem parabolicDuhamel_sndDeriv_summable_direct
    {lam : ℕ → ℝ} {fhat : ℕ → ℝ → ℝ} {Bv : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hlam : ∀ k, 0 < lam k) (hfc : ∀ k, Continuous (fhat k))
    (hBv : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) t, |fhat k s| ≤ Bv k)
    (hsumBv : Summable Bv) :
    Summable (fun k => |duhamelSecondMode (lam k) t (fhat k)|) := by
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hsumBv
  exact parabolicDuhamel_perMode_bound_direct (hlam k) ht (hfc k) (hBv k)

end

end ShenWork.IntervalParabolicDuhamelDirectBound
