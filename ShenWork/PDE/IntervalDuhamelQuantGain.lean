/-
# Phase-0 / M-gate-1: quantitative parabolic gains for the Duhamel coefficient sums

This module supplies three explicit, existential-free estimates for the spectral
Duhamel coefficient `duhamelSpectralCoeff a τ k = ∫₀^τ e^{−(τ−s)λₖ} a s k ds`
(`λₖ = unitIntervalCosineEigenvalue k = ((k:ℝ)·π)²`), under a `1/k²`-type decay
hypothesis on the source coefficients:

  `hdecay : ∀ σ, 0 ≤ σ → ∀ k, 1 ≤ k → |a σ k| ≤ 2*B/((k:ℝ)*π)²`.

1. **Per-mode bound** (`duhamelSpectralCoeff_min_bound`, `k ≥ 1`):
     `|bₖ| ≤ (2B/(kπ)²) · min τ (1/(kπ)²)`.

2. **λ-weighted sum with `τ^{1/4}` gain** (the G2 estimate,
   `duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound`):
     `∑'ₖ λₖ·|bₖ| ≤ (2·(∑'ₖ 1/((k:ℝ)+1)^{3/2})/π^{3/2}) · τ^{1/4} · B`.

3. **√λ-weighted sum, τ-free** (the G1 estimate,
   `duhamelSpectralCoeff_sqrtEigenvalue_tsum_bound`):
     `∑'ₖ √λₖ·|bₖ| ≤ (2·(∑'ₖ 1/((k:ℝ)+1)³)/π³) · B`.

The integral idioms (`∫₀^τ e^{−(τ−s)λ} ds = (1−e^{−τλ})/λ ≤ min τ (1/λ)`) reuse
`parabolicGain_le_one` of `IntervalDuhamelRegularity`.
-/
import ShenWork.PDE.IntervalDuhamelClosedC2

open MeasureTheory
open scoped Real

namespace ShenWork.IntervalDuhamelQuantGain

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)

/-! ## Elementary `min ≤ x^θ · y^{1−θ}` interpolation for `θ ∈ {1/4}` -/

/-- **Interpolation inequality.**  For `x, y ≥ 0` and `θ ∈ [0,1]`,
`min x y ≤ x^θ · y^{1−θ}`.  Proof: `min = min^θ · min^{1−θ} ≤ x^θ · y^{1−θ}` by
`rpow` monotonicity (`min ≤ x`, `min ≤ y`, all nonneg). -/
theorem min_le_rpow_mul_rpow {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min x y ≤ x ^ θ * y ^ (1 - θ) := by
  have hmnn : 0 ≤ min x y := le_min hx hy
  have hmx : min x y ≤ x := min_le_left _ _
  have hmy : min x y ≤ y := min_le_right _ _
  have hsplit : min x y = (min x y) ^ θ * (min x y) ^ (1 - θ) := by
    rw [← Real.rpow_add_of_nonneg hmnn hθ0 (by linarith)]
    rw [add_sub_cancel, Real.rpow_one]
  rw [hsplit]
  refine mul_le_mul ?_ ?_ (Real.rpow_nonneg hmnn _) (Real.rpow_nonneg hx _)
  · exact Real.rpow_le_rpow hmnn hmx hθ0
  · exact Real.rpow_le_rpow hmnn hmy (by linarith)

/-! ## The gain integral identity and per-mode bound -/

/-- `∫₀^τ e^{−(τ−s)λ} ds ≤ min τ (1/λ)` for `λ > 0, τ > 0`.  The two bounds:
`∫ = (1−e^{−τλ})/λ ≤ τ` (since `1−e^{−x} ≤ x`) and `≤ 1/λ` (since `1−e^{−τλ} ≤ 1`). -/
theorem gainIntegral_le_min {τ lam : ℝ} (hτ : 0 < τ) (hlam : 0 < lam) :
    (∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * lam)) ≤ min τ (1 / lam) := by
  have hpos : 0 ≤ ∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * lam) := by
    apply intervalIntegral.integral_nonneg hτ.le
    intro s _; exact Real.exp_nonneg _
  -- `λ · ∫ ≤ 1` ⇒ `∫ ≤ 1/λ`.
  have hgain := ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one
    (lam := lam) (t := τ) hlam.le hτ.le
  have hle_inv : (∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * lam)) ≤ 1 / lam := by
    rw [le_div_iff₀ hlam]
    calc (∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * lam)) * lam
        = lam * ∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * lam) := by ring
      _ ≤ 1 := hgain
  -- `∫ e^{−(τ−s)λ} ds ≤ ∫ 1 ds = τ` since `e^{−(τ−s)λ} ≤ 1` on `[0,τ]`.
  have hle_tau : (∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * lam)) ≤ τ := by
    have hbound : (∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * lam))
        ≤ ∫ _s in (0:ℝ)..τ, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hτ.le
      · apply Continuous.intervalIntegrable; fun_prop
      · apply Continuous.intervalIntegrable; fun_prop
      · intro s hs
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hsle : s ≤ τ := hs.2
        have : 0 ≤ (τ - s) * lam := mul_nonneg (by linarith) hlam.le
        nlinarith [this]
    simpa using hbound
  exact le_min hle_tau hle_inv

/-- **(i) Per-mode bound.**  For `k ≥ 1`,
`|duhamelSpectralCoeff a τ k| ≤ (2B/(kπ)²) · min τ (1/(kπ)²)`. -/
theorem duhamelSpectralCoeff_min_bound {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k → |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun σ => a σ k))
    {k : ℕ} (hk : 1 ≤ k) :
    |duhamelSpectralCoeff a τ k|
      ≤ (2 * B / ((k : ℝ) * Real.pi) ^ 2) * min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hlampos : (0 : ℝ) < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hCnn : (0 : ℝ) ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hlam_eq : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := rfl
  -- `|∫| ≤ ∫ |kernel|·|a| ≤ C · ∫ kernel`.
  have hkernel : Continuous
      (fun s : ℝ => Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k)) := by fun_prop
  have hII : IntervalIntegrable
      (fun s => Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k)
      volume 0 τ := (hkernel.mul (hcont k)).intervalIntegrable 0 τ
  have hstep : |duhamelSpectralCoeff a τ k|
      ≤ (2 * B / ((k : ℝ) * Real.pi) ^ 2)
          * ∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) := by
    unfold duhamelSpectralCoeff
    calc |∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k|
        = ‖∫ s in (0:ℝ)..τ,
            Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in (0:ℝ)..τ,
            ‖Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) * a s k‖ :=
          intervalIntegral.norm_integral_le_integral_norm hτ.le
      _ ≤ ∫ s in (0:ℝ)..τ,
            (2 * B / ((k : ℝ) * Real.pi) ^ 2)
              * Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) := by
          apply intervalIntegral.integral_mono_on hτ.le hII.norm
            (by apply Continuous.intervalIntegrable; fun_prop)
          intro s hs
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
            mul_comm (2 * B / ((k : ℝ) * Real.pi) ^ 2)]
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          exact hdecay s hs.1 k hk
      _ = (2 * B / ((k : ℝ) * Real.pi) ^ 2)
            * ∫ s in (0:ℝ)..τ, Real.exp (-(τ - s) * unitIntervalCosineEigenvalue k) := by
          rw [intervalIntegral.integral_const_mul]
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hCnn
  rw [hlam_eq]
  exact gainIntegral_le_min hτ hlampos

/-! ## (ii) λ-weighted sum with `τ^{1/4}` gain (the G2 estimate) -/

/-- **Per-mode `τ^{1/4}` bound** for the eigenvalue-weighted coefficient (`k ≥ 1`):
`λₖ·|bₖ| ≤ 2B·τ^{1/4}/((k:ℝ)·π)^{3/2}`. -/
theorem eigenvalue_mul_coeff_tauQuarter_bound {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k → |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun σ => a σ k))
    {k : ℕ} (hk : 1 ≤ k) :
    unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
      ≤ 2 * B * τ ^ ((1 : ℝ) / 4) / ((k : ℝ) * Real.pi) ^ ((3 : ℝ) / 2) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hkπpos : (0 : ℝ) < (k : ℝ) * Real.pi := by positivity
  have hlampos : (0 : ℝ) < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hlam_eq : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := rfl
  have hlamnn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := by rw [hlam_eq]; positivity
  have hinvnn : (0 : ℝ) ≤ 1 / ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hmin := duhamelSpectralCoeff_min_bound hτ hB hdecay hcont hk
  -- `λₖ·|bₖ| ≤ λₖ·(2B/(kπ)²)·min τ (1/(kπ)²) = 2B·min τ (1/(kπ)²)`  (since λₖ = (kπ)²).
  have hstep1 : unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
      ≤ 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
    calc unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
        ≤ unitIntervalCosineEigenvalue k
            * ((2 * B / ((k : ℝ) * Real.pi) ^ 2) * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)) :=
          mul_le_mul_of_nonneg_left hmin hlamnn
      _ = 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2) := by
          rw [hlam_eq]
          rw [show ((k : ℝ) * Real.pi) ^ 2
              * (2 * B / ((k : ℝ) * Real.pi) ^ 2 * min τ (1 / ((k : ℝ) * Real.pi) ^ 2))
              = (((k : ℝ) * Real.pi) ^ 2 / ((k : ℝ) * Real.pi) ^ 2)
                  * (2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)) by ring,
            div_self (by positivity : ((k : ℝ) * Real.pi) ^ 2 ≠ 0), one_mul]
  -- `min τ (1/(kπ)²) ≤ τ^{1/4}·(1/(kπ)²)^{3/4}`, and `(1/(kπ)²)^{3/4} = (kπ)^{-3/2}`.
  have hinterp := min_le_rpow_mul_rpow (x := τ) (y := 1 / ((k : ℝ) * Real.pi) ^ 2)
    hτ.le hinvnn (by norm_num : (0:ℝ) ≤ (1:ℝ)/4) (by norm_num : (1:ℝ)/4 ≤ 1)
  -- `(1/(kπ)²)^{3/4} = ((kπ)²)^{−3/4} = (kπ)^{−3/2} = 1/(kπ)^{3/2}`.
  have hrpow_inv : (1 / ((k : ℝ) * Real.pi) ^ 2) ^ (1 - (1:ℝ)/4)
      = 1 / ((k : ℝ) * Real.pi) ^ ((3:ℝ)/2) := by
    rw [show (1 : ℝ) - 1/4 = 3/4 by norm_num]
    rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow]
    congr 1
    rw [← Real.rpow_natCast ((k : ℝ) * Real.pi) 2, ← Real.rpow_mul hkπpos.le]
    norm_num
  rw [hrpow_inv] at hinterp
  have hstep2 : 2 * B * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)
      ≤ 2 * B * (τ ^ ((1:ℝ)/4) * (1 / ((k : ℝ) * Real.pi) ^ ((3:ℝ)/2))) :=
    mul_le_mul_of_nonneg_left hinterp (by positivity)
  refine (hstep1.trans hstep2).trans (le_of_eq ?_)
  rw [mul_one_div, mul_div_assoc]

/-- Summability of the `p = 3/2` shifted `p`-series `∑'ₖ 1/((k:ℝ)+1)^{3/2}`. -/
theorem summable_one_div_natShift_rpow_threeHalves :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    (Real.summable_one_div_nat_rpow).mpr (by norm_num)
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ ((3 : ℝ) / 2)) 1).2 hbase
  refine hshift.congr (fun n => ?_)
  push_cast
  ring_nf

/-- **(ii) The `τ^{1/4}` G2 estimate.**
`∑'ₖ λₖ·|bₖ| ≤ (2·(∑'ₖ 1/((k:ℝ)+1)^{3/2})/π^{3/2}) · τ^{1/4} · B`. -/
theorem duhamelSpectralCoeff_eigenvalue_tsum_tauQuarter_bound {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k → |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun σ => a σ k)) :
    (∑' k : ℕ, unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|)
      ≤ (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) / Real.pi ^ ((3 : ℝ) / 2))
          * τ ^ ((1 : ℝ) / 4) * B := by
  set C : ℝ := 2 * B * τ ^ ((1 : ℝ) / 4) / Real.pi ^ ((3 : ℝ) / 2) with hC_def
  have hCnn : 0 ≤ C := by rw [hC_def]; positivity
  -- The full series `f` and its `k ↦ k+1` shift (the `k = 0` term vanishes since `λ₀ = 0`).
  set f : ℕ → ℝ := fun k => unitIntervalCosineEigenvalue k * |duhamelSpectralCoeff a τ k|
    with hf_def
  have hfnn : ∀ k, 0 ≤ f k := by
    intro k
    refine mul_nonneg ?_ (abs_nonneg _)
    simp only [unitIntervalCosineEigenvalue]; positivity
  -- Majorant on the shifted index: `g k = C · 1/((k:ℝ)+1)^{3/2}`.
  set g : ℕ → ℝ := fun k => C * (1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) with hg_def
  have hg_summable : Summable g :=
    summable_one_div_natShift_rpow_threeHalves.mul_left C
  -- Per-mode shifted bound `f (k+1) ≤ g k`.
  have hshift_le : ∀ k : ℕ, f (k + 1) ≤ g k := by
    intro k
    have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hbound := eigenvalue_mul_coeff_tauQuarter_bound hτ hB hdecay hcont hk
    refine hbound.trans (le_of_eq ?_)
    have hkπpos : (0 : ℝ) < ((k : ℝ) + 1) * Real.pi := by positivity
    -- `2B·τ^{1/4}/(((k+1)π)^{3/2}) = C · 1/((k:ℝ)+1)^{3/2}`.
    rw [hg_def, hC_def]
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    rw [Real.mul_rpow (by positivity) Real.pi_nonneg]
    field_simp
  -- The shifted series is summable, hence so is `f`, and the sums agree.
  have hf_shift_summable : Summable (fun k => f (k + 1)) :=
    hg_summable.of_nonneg_of_le (fun k => hfnn (k + 1)) hshift_le
  have hf_summable : Summable f :=
    (summable_nat_add_iff (f := f) 1).1 hf_shift_summable
  have hf0 : f 0 = 0 := by
    rw [hf_def]; simp only [unitIntervalCosineEigenvalue]
    norm_num
  have hsum_shift : (∑' k, f k) = ∑' k, f (k + 1) := by
    rw [hf_summable.tsum_eq_zero_add, hf0, zero_add]
  rw [hsum_shift]
  -- `∑' f(k+1) ≤ ∑' g = C · ∑' 1/((k:ℝ)+1)^{3/2}`, then rearrange to the spec constant.
  refine (hf_shift_summable.tsum_le_tsum hshift_le hg_summable).trans (le_of_eq ?_)
  rw [hg_def, tsum_mul_left, hC_def]
  ring

/-! ## (iii) √λ-weighted sum, τ-free (the G1 estimate) -/

/-- **Per-mode τ-free bound** for the `√λ`-weighted coefficient (`k ≥ 1`):
`√λₖ·|bₖ| ≤ 2B/((k:ℝ)·π)³`.  Uses `√λₖ·min(τ,1/λₖ) ≤ √λₖ·(1/λₖ) = 1/√λₖ = 1/(kπ)`. -/
theorem sqrtEigenvalue_mul_coeff_bound {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k → |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun σ => a σ k))
    {k : ℕ} (hk : 1 ≤ k) :
    Real.sqrt (unitIntervalCosineEigenvalue k) * |duhamelSpectralCoeff a τ k|
      ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 3 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hkπpos : (0 : ℝ) < (k : ℝ) * Real.pi := by positivity
  have hlampos : (0 : ℝ) < ((k : ℝ) * Real.pi) ^ 2 := by positivity
  have hlam_eq : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := rfl
  have hsqrt_eq : Real.sqrt (unitIntervalCosineEigenvalue k) = (k : ℝ) * Real.pi := by
    rw [hlam_eq, Real.sqrt_sq hkπpos.le]
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (unitIntervalCosineEigenvalue k) := Real.sqrt_nonneg _
  have hmin := duhamelSpectralCoeff_min_bound hτ hB hdecay hcont hk
  -- `√λₖ·|bₖ| ≤ √λₖ·(2B/(kπ)²)·min τ (1/(kπ)²) ≤ √λₖ·(2B/(kπ)²)·(1/(kπ)²)`.
  have hmin_le : min τ (1 / ((k : ℝ) * Real.pi) ^ 2) ≤ 1 / ((k : ℝ) * Real.pi) ^ 2 :=
    min_le_right _ _
  calc Real.sqrt (unitIntervalCosineEigenvalue k) * |duhamelSpectralCoeff a τ k|
      ≤ Real.sqrt (unitIntervalCosineEigenvalue k)
          * ((2 * B / ((k : ℝ) * Real.pi) ^ 2) * min τ (1 / ((k : ℝ) * Real.pi) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmin hsqrtnn
    _ ≤ Real.sqrt (unitIntervalCosineEigenvalue k)
          * ((2 * B / ((k : ℝ) * Real.pi) ^ 2) * (1 / ((k : ℝ) * Real.pi) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hsqrtnn
        exact mul_le_mul_of_nonneg_left hmin_le (by positivity)
    _ = 2 * B / ((k : ℝ) * Real.pi) ^ 3 := by
        rw [hsqrt_eq]; field_simp

/-- Summability of the `p = 3` shifted `p`-series `∑'ₖ 1/((k:ℝ)+1)³`. -/
theorem summable_one_div_natShift_cube :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (3 : ℕ)) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 : ℕ)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (3 : ℕ)) 1).2 hbase
  refine hshift.congr (fun n => ?_)
  push_cast
  ring_nf

/-- **(iii) The τ-free G1 estimate.**
`∑'ₖ √λₖ·|bₖ| ≤ (2·(∑'ₖ 1/((k:ℝ)+1)³)/π³) · B`. -/
theorem duhamelSpectralCoeff_sqrtEigenvalue_tsum_bound {a : ℝ → ℕ → ℝ} {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B)
    (hdecay : ∀ σ, 0 ≤ σ → ∀ k : ℕ, 1 ≤ k → |a σ k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2)
    (hcont : ∀ k, Continuous (fun σ => a σ k)) :
    (∑' k : ℕ, Real.sqrt (unitIntervalCosineEigenvalue k) * |duhamelSpectralCoeff a τ k|)
      ≤ (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (3 : ℕ)) / Real.pi ^ 3) * B := by
  set C : ℝ := 2 * B / Real.pi ^ 3 with hC_def
  have hCnn : 0 ≤ C := by rw [hC_def]; positivity
  set f : ℕ → ℝ :=
    fun k => Real.sqrt (unitIntervalCosineEigenvalue k) * |duhamelSpectralCoeff a τ k|
    with hf_def
  have hfnn : ∀ k, 0 ≤ f k := fun k => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  set g : ℕ → ℝ := fun k => C * (1 / ((k : ℝ) + 1) ^ (3 : ℕ)) with hg_def
  have hg_summable : Summable g := summable_one_div_natShift_cube.mul_left C
  have hshift_le : ∀ k : ℕ, f (k + 1) ≤ g k := by
    intro k
    have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hbound := sqrtEigenvalue_mul_coeff_bound hτ hB hdecay hcont hk
    refine hbound.trans (le_of_eq ?_)
    rw [hg_def, hC_def]
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    rw [mul_pow]
    field_simp
  have hf_shift_summable : Summable (fun k => f (k + 1)) :=
    hg_summable.of_nonneg_of_le (fun k => hfnn (k + 1)) hshift_le
  have hf_summable : Summable f := (summable_nat_add_iff (f := f) 1).1 hf_shift_summable
  have hf0 : f 0 = 0 := by
    rw [hf_def]; simp only [unitIntervalCosineEigenvalue]
    norm_num
  have hsum_shift : (∑' k, f k) = ∑' k, f (k + 1) := by
    rw [hf_summable.tsum_eq_zero_add, hf0, zero_add]
  rw [hsum_shift]
  refine (hf_shift_summable.tsum_le_tsum hshift_le hg_summable).trans (le_of_eq ?_)
  rw [hg_def, tsum_mul_left, hC_def]
  ring

end ShenWork.IntervalDuhamelQuantGain
