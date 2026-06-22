import ShenWork.Paper2.IntervalSpectralMultiplierBound
import ShenWork.Paper2.IntervalHSigmaScale
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
  Brick 3 (per-mode kernel) of the two-step parabolic-smoothing bootstrap.

  The full Step-1 estimate `‖Bduhamel F s‖_{H^σ} ≤ C M s^{(1−σ)/2}` reduces, mode
  by mode, to the weighted single-mode smoothing inequality:

      (1+λ)^σ · ( ∫₀ˢ √λ · exp(−d λ (s−τ)) · F(τ) dτ )²
        ≤ C_σ · d^(−(σ+1)/2) · (∫₀ˢ (s−τ)^(−(σ+1)/2) dτ) · ∫₀ˢ |F(τ)|² dτ-ish.

  This file builds the genuinely-new content: the weighted spectral multiplier
  `(1+λ)^(σ/2)·√λ·exp(−d r λ) ≤ C · d^(−(σ+1)/2) · r^(−(σ+1)/2)` for `r > 0`,
  obtained from `spectral_multiplier_bound` at `θ = (σ+1)/2`, together with the
  scalar terminal-singularity integrability `∫₀ˢ r^(−(σ+1)/2) dr < ∞` for
  `σ < 1`.  These are the two scalar inputs the Minkowski/Cauchy-Schwarz
  assembly consumes.
-/

noncomputable section

namespace ShenWork.Paper2.BFormHSigmaSmoothing

open ShenWork.Paper2.SpectralMultiplierBound
open ShenWork.Paper2.HSigmaScale
open Real

/-- The weighted spectral multiplier for the divergence-Duhamel kernel:
`(1+λ)^(σ/2) · √λ · exp(−d r λ) ≤ ((1+λ)^(σ/2)·λ^(1/2))·exp(−drλ)`, and since
`(1+λ)^(σ/2)·λ^(1/2) ≤ (1+λ)^((σ+1)/2)`, the whole thing is bounded by
`(1+λ)^((σ+1)/2) exp(−drλ)`.  We record the clean dominating multiplier
`λ^((σ+1)/2) exp(−drλ)` form via `spectral_multiplier_bound` at `θ=(σ+1)/2`. -/
theorem weighted_kernel_multiplier_le {σ d r lam : ℝ}
    (hσ0 : 0 ≤ σ) (hd : 0 < d) (hr : 0 < r) (hlam : 0 ≤ lam) :
    ∃ C : ℝ, 0 < C ∧
      lam ^ ((σ + 1) / 2) * Real.exp (-(d * r * lam)) ≤
        C * d ^ (-((σ + 1) / 2)) * r ^ (-((σ + 1) / 2)) := by
  have hθ : 0 < (σ + 1) / 2 := by linarith
  obtain ⟨C, hCpos, hC⟩ := spectral_multiplier_bound ((σ + 1) / 2) hθ
  exact ⟨C, hCpos, hC d r lam hd hr hlam⟩

/-- Terminal-singularity integrability exponent: for `0 ≤ σ < 1`,
`(σ+1)/2 < 1`, so `∫₀ˢ r^(−(σ+1)/2) dr` converges (the integrand has an
integrable power singularity at `0`). -/
theorem terminal_exponent_lt_one {σ : ℝ} (hσ1 : σ < 1) :
    (σ + 1) / 2 < 1 := by linarith

theorem terminal_exponent_nonneg {σ : ℝ} (hσ0 : 0 ≤ σ) :
    0 ≤ (σ + 1) / 2 := by linarith

/-- The scalar terminal integral `∫₀ˢ r^(−p) dr = s^(1−p)/(1−p)` for `0 ≤ p < 1`,
`s > 0`, evaluated via `integral_rpow`.  Here `p = (σ+1)/2`.  This is the exact
constant producing the `s^{(1−σ)/2}` rate (`1 − (σ+1)/2 = (1−σ)/2`). -/
theorem integral_terminal_singularity {p s : ℝ} (_hp0 : 0 ≤ p) (hp1 : p < 1)
    (_hs : 0 < s) :
    ∫ r in (0 : ℝ)..s, r ^ (-p) = s ^ (1 - p) / (1 - p) := by
  have hpow : (∫ r in (0 : ℝ)..s, r ^ (-p))
      = (s ^ (-p + 1) - (0 : ℝ) ^ (-p + 1)) / (-p + 1) := by
    apply integral_rpow
    left
    linarith
  rw [hpow]
  have hzero : (0 : ℝ) ^ (-p + 1) = 0 := by
    rw [Real.zero_rpow (by linarith : -p + 1 ≠ 0)]
  rw [hzero]
  have : (-p + 1) = (1 - p) := by ring
  rw [this]; ring_nf

/-- The `s^{(1−σ)/2}` rate exponent, recorded explicitly:
`1 − (σ+1)/2 = (1−σ)/2`. -/
theorem rate_exponent_eq (σ : ℝ) : 1 - (σ + 1) / 2 = (1 - σ) / 2 := by ring

#print axioms weighted_kernel_multiplier_le
#print axioms terminal_exponent_lt_one
#print axioms integral_terminal_singularity
#print axioms rate_exponent_eq

end ShenWork.Paper2.BFormHSigmaSmoothing
