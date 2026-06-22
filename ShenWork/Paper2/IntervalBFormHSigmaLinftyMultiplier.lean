import ShenWork.Paper2.IntervalSpectralMultiplierBound
import ShenWork.Paper2.IntervalHSigmaScale
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  Brick 3 — per-mode `L∞_t L²_x → H^σ_x` multiplier (the CORRECT smoothing route).

  The originally-planned `L²_t L²_x → H^σ` estimate is false (see
  `IntervalBFormHSigmaKernelL2`).  The viable fractional smoothing brick takes an
  `L∞`-in-time `L²`-in-space source and gains a half spatial derivative with rate
  `s^{1−σ}` (for the squared `H^σ` energy).  It is proved by the Minkowski
  (integral-triangle) route, which reduces to a single genuinely-new per-mode
  multiplier bound, UNIFORM in the mode index `k` for each fixed `r > 0`:

      (1 + λ)^{σ/2} · √λ · exp(−d λ r) ≤ C_σ · r^{−(σ+1)/2},    0 ≤ σ < 1, r ∈ (0,1].

  Note this is NOT in tension with the kernel-`L²` impossibility: there the
  weighted quantity was the *time integral of the squared kernel*
  `∫₀ˢ λ e^{−2dλr} dr`, which carries an irreducible `(1+λ)^σ` weight.  Here, for a
  *fixed* `r`, the function `λ ↦ (1+λ)^{σ/2} λ^{1/2} e^{−dλr}` is bounded (the
  exponential beats every polynomial), with maximum of order `r^{−(σ+1)/2}`.

  The bound is assembled from the landed pieces:
    * `√λ ≤ √(1+λ)`, so `(1+λ)^{σ/2}·λ^{1/2} ≤ (1+λ)^{(σ+1)/2}`;
    * `(1+λ)^{(σ+1)/2} ≤ 2^{(σ+1)/2}·(1 + λ^{(σ+1)/2})`;
    * `spectral_multiplier_bound` at `θ = (σ+1)/2` for the `λ^{(σ+1)/2} e^{−dλr}` term;
    * `exp(−dλr) ≤ 1` and `1 ≤ r^{−(σ+1)/2}` (for `r ≤ 1`, exponent `≥ 0`) for the
      remaining constant term.
-/

noncomputable section

namespace ShenWork.Paper2.BFormHSigmaLinftyMultiplier

open ShenWork.Paper2.SpectralMultiplierBound
open ShenWork.Paper2.HSigmaScale
open Real

/-- `√λ · (1+λ)^{σ/2} ≤ (1+λ)^{(σ+1)/2}` for `σ ≥ 0`, `λ ≥ 0`. -/
theorem weight_sqrt_le {σ lam : ℝ} (_hσ0 : 0 ≤ σ) (hlam : 0 ≤ lam) :
    lam ^ (1/2 : ℝ) * (1 + lam) ^ (σ/2) ≤ (1 + lam) ^ ((σ + 1)/2) := by
  have h1l : (0:ℝ) ≤ 1 + lam := by linarith
  have hsqrt : lam ^ (1/2 : ℝ) ≤ (1 + lam) ^ (1/2 : ℝ) :=
    Real.rpow_le_rpow hlam (by linarith) (by norm_num)
  calc lam ^ (1/2 : ℝ) * (1 + lam) ^ (σ/2)
      ≤ (1 + lam) ^ (1/2 : ℝ) * (1 + lam) ^ (σ/2) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg h1l _)
    _ = (1 + lam) ^ ((1:ℝ)/2 + σ/2) := by rw [← Real.rpow_add (by linarith)]
    _ = (1 + lam) ^ ((σ + 1)/2) := by ring_nf

/-- `(1+λ)^θ ≤ 2^θ · (1 + λ^θ)` for `θ ≥ 0`, `λ ≥ 0`.  (Subadditivity of `x^θ`
on `[0,1]` scaled, or `(1+λ) ≤ 2·max 1 λ` then `rpow_le_rpow`.) -/
theorem one_add_rpow_le {θ lam : ℝ} (hθ : 0 ≤ θ) (hlam : 0 ≤ lam) :
    (1 + lam) ^ θ ≤ 2 ^ θ * (1 + lam ^ θ) := by
  have h1l : (0:ℝ) ≤ 1 + lam := by linarith
  rcases le_or_gt lam 1 with hle | hgt
  · -- λ ≤ 1: (1+λ) ≤ 2, and 1 ≤ 1 + λ^θ.
    have hbase : (1 + lam) ^ θ ≤ (2:ℝ) ^ θ :=
      Real.rpow_le_rpow h1l (by linarith) hθ
    have hr : (1:ℝ) ≤ 1 + lam ^ θ := by
      have := Real.rpow_nonneg hlam θ; linarith
    calc (1 + lam) ^ θ ≤ 2 ^ θ := hbase
      _ = 2 ^ θ * 1 := by ring
      _ ≤ 2 ^ θ * (1 + lam ^ θ) :=
        mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg (by norm_num) θ)
  · -- λ > 1: (1+λ) ≤ 2λ, so (1+λ)^θ ≤ 2^θ λ^θ ≤ 2^θ(1+λ^θ).
    have hbase : (1 + lam) ^ θ ≤ (2 * lam) ^ θ :=
      Real.rpow_le_rpow h1l (by linarith) hθ
    have hsplit : (2 * lam) ^ θ = 2 ^ θ * lam ^ θ :=
      Real.mul_rpow (by norm_num) hlam
    have hr : lam ^ θ ≤ 1 + lam ^ θ := by linarith [Real.rpow_nonneg hlam θ]
    calc (1 + lam) ^ θ ≤ (2 * lam) ^ θ := hbase
      _ = 2 ^ θ * lam ^ θ := hsplit
      _ ≤ 2 ^ θ * (1 + lam ^ θ) :=
        mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg (by norm_num) θ)

/-- **Per-mode `L∞→H^σ` multiplier bound.**  For `0 ≤ σ < 1`, `d > 0`,
`0 < r ≤ 1`, `λ ≥ 0`:
`(1+λ)^{σ/2} · λ^{1/2} · exp(−d λ r) ≤ C_σ · r^{−(σ+1)/2}`,
with `C_σ` depending only on `σ` (and `d`).  This is the single genuinely-new
ingredient of the `L∞_t L²_x → H^σ_x` Minkowski smoothing estimate; everything
else (terminal singularity integral, `s^{(1−σ)/2}` rate) is already landed. -/
theorem linfty_multiplier_bound {σ : ℝ} (hσ0 : 0 ≤ σ) (_hσ1 : σ < 1) (d : ℝ)
    (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r lam : ℝ, 0 < r → r ≤ 1 → 0 ≤ lam →
        (1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ) * Real.exp (-(d * r * lam)) ≤
          C * r ^ (-((σ + 1)/2)) := by
  have hθ : 0 < (σ + 1) / 2 := by linarith
  obtain ⟨C₀, hC₀pos, hC₀⟩ := spectral_multiplier_bound ((σ + 1)/2) hθ
  -- final constant
  refine ⟨2 ^ ((σ + 1)/2) * (1 + C₀ * d ^ (-((σ + 1)/2))) , ?_, ?_⟩
  · have : 0 < (2:ℝ) ^ ((σ + 1)/2) := Real.rpow_pos_of_pos (by norm_num) _
    have hd1 : 0 < d ^ (-((σ + 1)/2)) := Real.rpow_pos_of_pos hd _
    positivity
  · intro r lam hr hr1 hlam
    have h1l : (0:ℝ) ≤ 1 + lam := by linarith
    have hexp_le_one : Real.exp (-(d * r * lam)) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have : 0 ≤ d * r * lam := by positivity
      linarith
    have hexp_nonneg : (0:ℝ) ≤ Real.exp (-(d * r * lam)) := (Real.exp_pos _).le
    -- Step 1: (1+λ)^{σ/2} λ^{1/2} ≤ (1+λ)^{(σ+1)/2}.
    have hstep1 : (1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ)
        ≤ (1 + lam) ^ ((σ + 1)/2) := by
      rw [mul_comm]; exact weight_sqrt_le hσ0 hlam
    -- Step 2: (1+λ)^{(σ+1)/2} ≤ 2^{(σ+1)/2}(1 + λ^{(σ+1)/2}).
    have hstep2 := one_add_rpow_le (θ := (σ + 1)/2) (lam := lam) hθ.le hlam
    -- Combine the LHS pointwise.
    have hLHS : (1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ) * Real.exp (-(d * r * lam))
        ≤ 2 ^ ((σ + 1)/2) * (Real.exp (-(d * r * lam))
            + lam ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))) := by
      have hA : (1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ) * Real.exp (-(d * r * lam))
          ≤ (1 + lam) ^ ((σ + 1)/2) * Real.exp (-(d * r * lam)) :=
        mul_le_mul_of_nonneg_right hstep1 hexp_nonneg
      have hB : (1 + lam) ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))
          ≤ 2 ^ ((σ + 1)/2) * (1 + lam ^ ((σ + 1)/2)) * Real.exp (-(d * r * lam)) :=
        mul_le_mul_of_nonneg_right hstep2 hexp_nonneg
      calc (1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ) * Real.exp (-(d * r * lam))
          ≤ 2 ^ ((σ + 1)/2) * (1 + lam ^ ((σ + 1)/2)) * Real.exp (-(d * r * lam)) :=
            le_trans hA hB
        _ = 2 ^ ((σ + 1)/2) * (Real.exp (-(d * r * lam))
              + lam ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))) := by ring
    -- The two inner terms, each ≤ r^{−(σ+1)/2}·(const).
    have hone_le : (1:ℝ) ≤ r ^ (-((σ + 1)/2)) := by
      rw [Real.rpow_neg hr.le]
      have hrp : r ^ ((σ + 1)/2) ≤ 1 := by
        calc r ^ ((σ + 1)/2) ≤ (1:ℝ) ^ ((σ + 1)/2) :=
              Real.rpow_le_rpow hr.le hr1 hθ.le
          _ = 1 := Real.one_rpow _
      have hrp_pos : 0 < r ^ ((σ + 1)/2) := Real.rpow_pos_of_pos hr _
      rw [le_inv_comm₀ (by norm_num) hrp_pos]; simpa using hrp
    have hterm1 : Real.exp (-(d * r * lam))
        ≤ r ^ (-((σ + 1)/2)) := le_trans hexp_le_one hone_le
    have hterm2 : lam ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))
        ≤ C₀ * d ^ (-((σ + 1)/2)) * r ^ (-((σ + 1)/2)) :=
      hC₀ d r lam hd hr hlam
    -- assemble
    have hrpow_nonneg : (0:ℝ) ≤ r ^ (-((σ + 1)/2)) := Real.rpow_nonneg hr.le _
    have hsum : Real.exp (-(d * r * lam))
          + lam ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))
        ≤ (1 + C₀ * d ^ (-((σ + 1)/2))) * r ^ (-((σ + 1)/2)) := by
      have h2 : lam ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))
          ≤ (C₀ * d ^ (-((σ + 1)/2))) * r ^ (-((σ + 1)/2)) := by
        calc lam ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))
            ≤ C₀ * d ^ (-((σ + 1)/2)) * r ^ (-((σ + 1)/2)) := hterm2
          _ = (C₀ * d ^ (-((σ + 1)/2))) * r ^ (-((σ + 1)/2)) := by ring
      calc Real.exp (-(d * r * lam))
            + lam ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))
          ≤ r ^ (-((σ + 1)/2)) + (C₀ * d ^ (-((σ + 1)/2))) * r ^ (-((σ + 1)/2)) :=
            add_le_add hterm1 h2
        _ = (1 + C₀ * d ^ (-((σ + 1)/2))) * r ^ (-((σ + 1)/2)) := by ring
    calc (1 + lam) ^ (σ/2) * lam ^ (1/2 : ℝ) * Real.exp (-(d * r * lam))
        ≤ 2 ^ ((σ + 1)/2) * (Real.exp (-(d * r * lam))
            + lam ^ ((σ + 1)/2) * Real.exp (-(d * r * lam))) := hLHS
      _ ≤ 2 ^ ((σ + 1)/2)
            * ((1 + C₀ * d ^ (-((σ + 1)/2))) * r ^ (-((σ + 1)/2))) :=
          mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num) _)
      _ = 2 ^ ((σ + 1)/2) * (1 + C₀ * d ^ (-((σ + 1)/2)))
            * r ^ (-((σ + 1)/2)) := by ring

#print axioms linfty_multiplier_bound

end ShenWork.Paper2.BFormHSigmaLinftyMultiplier
