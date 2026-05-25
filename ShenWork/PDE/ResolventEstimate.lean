import ShenWork.PDE.CosineSpectrum

/-!
# Unit-interval Neumann resolvent estimate

This file proves the spectral-diagonal core of the H3.1 sectorial estimate for
the interval domain.  For the shifted Neumann Laplacian
`A = -Δ_N + ω`, with spectrum
`unitIntervalNeumannSpectrum.eigenvalue n + ω = n^2 π^2 + ω`, the coefficient
resolvent multiplier is

`(λ + unitIntervalNeumannSpectrum.eigenvalue n + ω)^{-1}`.

On the right-half-plane sector `λ ≠ 0`, `0 ≤ λ.re`, and for `0 ≤ ω`, this gives
the `ℓ²` resolvent bound

`‖(λ + A)^{-1} a‖₂² ≤ (1 / ‖λ‖)^2 ‖a‖₂²`.

This is an honest spectral subblock.  It does not assert the full nonlinear
`SectorialLocalExponentialRaw` H3.1 statement, nor does it construct the
unbounded Neumann Laplacian as a closed operator on the physical function
space; those remain separate analytic/operator-theoretic bridges.
-/

noncomputable section

namespace ShenWork.PDE.ResolventEstimate

open ShenWork.Paper3

/-- Coefficient `ℓ²` energy for Neumann-cosine coefficients. -/
def coeffL2Energy (a : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ ^ 2

/-- Coefficient `ℓ²` norm induced by `coeffL2Energy`. -/
def coeffL2Norm (a : ℕ → ℂ) : ℝ :=
  Real.sqrt (coeffL2Energy a)

/-- The shifted Neumann eigenvalue for `-Δ_N + ω` on the unit interval. -/
def shiftedNeumannEigenvalue (ω : ℝ) (n : ℕ) : ℝ :=
  unitIntervalNeumannSpectrum.eigenvalue n + ω

/-- The diagonal coefficient resolvent for `λ + (-Δ_N + ω)`. -/
def shiftedNeumannResolventCoeff (ω : ℝ) (z : ℂ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹ * a n

lemma unitIntervalNeumannSpectrum_eigenvalue_nonneg (n : ℕ) :
    0 ≤ unitIntervalNeumannSpectrum.eigenvalue n :=
  unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n

lemma shiftedNeumannEigenvalue_nonneg {ω : ℝ} (hω : 0 ≤ ω) (n : ℕ) :
    0 ≤ shiftedNeumannEigenvalue ω n := by
  unfold shiftedNeumannEigenvalue
  exact add_nonneg (unitIntervalNeumannSpectrum_eigenvalue_nonneg n) hω

lemma norm_le_norm_add_nonneg_real {z : ℂ} {r : ℝ}
    (hzre : 0 ≤ z.re) (hr : 0 ≤ r) :
    ‖z‖ ≤ ‖z + (r : ℂ)‖ := by
  have hsquares : ‖z‖ ^ 2 ≤ ‖z + (r : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
    nlinarith [mul_nonneg hzre hr, sq_nonneg r]
  exact (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (z + (r : ℂ)))).mp hsquares

lemma shiftedNeumann_resolvent_denominator_norm_ge {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hzre : 0 ≤ z.re) (n : ℕ) :
    ‖z‖ ≤ ‖z + (shiftedNeumannEigenvalue ω n : ℂ)‖ :=
  norm_le_norm_add_nonneg_real hzre (shiftedNeumannEigenvalue_nonneg hω n)

/-- Pointwise multiplier estimate in the right-half-plane sector. -/
theorem shiftedNeumann_resolvent_multiplier_norm_le {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : z ≠ 0) (n : ℕ) :
    ‖(z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹‖ ≤ (‖z‖)⁻¹ := by
  have hden_ge :
      ‖z‖ ≤ ‖z + (shiftedNeumannEigenvalue ω n : ℂ)‖ :=
    shiftedNeumann_resolvent_denominator_norm_ge hω hzre n
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hdenpos : 0 < ‖z + (shiftedNeumannEigenvalue ω n : ℂ)‖ :=
    hzpos.trans_le hden_ge
  rw [norm_inv]
  exact (inv_le_inv₀ hdenpos hzpos).mpr hden_ge

/-- Pointwise squared coefficient estimate for the diagonal resolvent. -/
theorem shiftedNeumannResolventCoeff_sq_le {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : z ≠ 0)
    (a : ℕ → ℂ) (n : ℕ) :
    ‖shiftedNeumannResolventCoeff ω z a n‖ ^ 2 ≤
      ((‖z‖)⁻¹) ^ 2 * ‖a n‖ ^ 2 := by
  have hmult :
      ‖(z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹‖ ≤ (‖z‖)⁻¹ :=
    shiftedNeumann_resolvent_multiplier_norm_le hω hzre hz n
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hinv_nonneg : 0 ≤ (‖z‖)⁻¹ := inv_nonneg.mpr hzpos.le
  have hmul :
      ‖(z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹‖ * ‖a n‖ ≤
        (‖z‖)⁻¹ * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hmult (norm_nonneg (a n))
  calc
    ‖shiftedNeumannResolventCoeff ω z a n‖ ^ 2
        = (‖(z + (shiftedNeumannEigenvalue ω n : ℂ))⁻¹‖ * ‖a n‖) ^ 2 := by
          rw [shiftedNeumannResolventCoeff, norm_mul]
    _ ≤ ((‖z‖)⁻¹ * ‖a n‖) ^ 2 := by
          exact
            (sq_le_sq₀
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (mul_nonneg hinv_nonneg (norm_nonneg _))).mpr hmul
    _ = ((‖z‖)⁻¹) ^ 2 * ‖a n‖ ^ 2 := by
          ring

/-- The diagonal resolvent preserves square-summability in the sector. -/
theorem shiftedNeumannResolventCoeff_l2_summable {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : z ≠ 0)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ => ‖shiftedNeumannResolventCoeff ω z a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left (((‖z‖)⁻¹) ^ 2))
  intro n
  exact shiftedNeumannResolventCoeff_sq_le hω hzre hz a n

/-- Coefficient-energy form of the resolvent estimate:
`‖(λ + (-Δ_N + ω))^{-1} a‖₂² ≤ |λ|^{-2} ‖a‖₂²`.
-/
theorem shiftedNeumannResolventCoeff_l2_energy_le {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : z ≠ 0)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy (shiftedNeumannResolventCoeff ω z a) ≤
      ((‖z‖)⁻¹) ^ 2 * coeffL2Energy a := by
  have hs :
      Summable fun n : ℕ => ‖shiftedNeumannResolventCoeff ω z a n‖ ^ 2 :=
    shiftedNeumannResolventCoeff_l2_summable hω hzre hz ha
  have hmajor :
      Summable fun n : ℕ => ((‖z‖)⁻¹) ^ 2 * ‖a n‖ ^ 2 :=
    ha.mul_left (((‖z‖)⁻¹) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖shiftedNeumannResolventCoeff ω z a n‖ ^ 2 ≤
          ((‖z‖)⁻¹) ^ 2 * ‖a n‖ ^ 2 :=
    shiftedNeumannResolventCoeff_sq_le hω hzre hz a
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- Norm form of the diagonal resolvent estimate. -/
theorem shiftedNeumannResolventCoeff_l2_norm_le {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hzre : 0 ≤ z.re) (hz : z ≠ 0)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm (shiftedNeumannResolventCoeff ω z a) ≤
      ((1 : ℝ) / ‖z‖) * coeffL2Norm a := by
  have henergy := shiftedNeumannResolventCoeff_l2_energy_le hω hzre hz ha
  have henergy' :
      coeffL2Energy (shiftedNeumannResolventCoeff ω z a) ≤
        ((1 : ℝ) / ‖z‖) ^ 2 * coeffL2Energy a := by
    simpa [one_div] using henergy
  have hsqrt := Real.sqrt_le_sqrt henergy'
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hfactor_nonneg : 0 ≤ (1 : ℝ) / ‖z‖ :=
    div_nonneg zero_le_one hzpos.le
  calc
    coeffL2Norm (shiftedNeumannResolventCoeff ω z a)
        = Real.sqrt (coeffL2Energy (shiftedNeumannResolventCoeff ω z a)) := rfl
    _ ≤ Real.sqrt (((1 : ℝ) / ‖z‖) ^ 2 * coeffL2Energy a) := hsqrt
    _ = ((1 : ℝ) / ‖z‖) * coeffL2Norm a := by
          rw [Real.sqrt_mul (sq_nonneg ((1 : ℝ) / ‖z‖))]
          rw [Real.sqrt_sq hfactor_nonneg]
          rfl

/-- H3.1 spectral subblock for the concrete interval-domain Neumann spectrum.

The constant is `C = 1` on the right-half-plane sector.  This is the squared
`ℓ²` form of `‖(λ + A)^{-1}‖ ≤ C / |λ|` for
`A = -Δ_N + ω`, diagonalized by the unit-interval Neumann spectrum.
-/
theorem intervalDomain_shiftedNeumannResolvent_estimate {ω : ℝ} (hω : 0 ≤ ω) :
    ∀ z : ℂ, z ≠ 0 → 0 ≤ z.re →
      ∀ a : ℕ → ℂ, Summable (fun n : ℕ => ‖a n‖ ^ 2) →
        coeffL2Energy (shiftedNeumannResolventCoeff ω z a) ≤
          ((1 : ℝ) / ‖z‖) ^ 2 * coeffL2Energy a := by
  intro z hz hzre a ha
  have h := shiftedNeumannResolventCoeff_l2_energy_le hω hzre hz ha
  simpa [one_div] using h

/-- H3.1 spectral subblock in norm form: `C = 1` on the right-half-plane sector. -/
theorem intervalDomain_shiftedNeumannResolvent_l2_norm_estimate {ω : ℝ} (hω : 0 ≤ ω) :
    ∀ z : ℂ, z ≠ 0 → 0 ≤ z.re →
      ∀ a : ℕ → ℂ, Summable (fun n : ℕ => ‖a n‖ ^ 2) →
        coeffL2Norm (shiftedNeumannResolventCoeff ω z a) ≤
          ((1 : ℝ) / ‖z‖) * coeffL2Norm a := by
  intro z hz hzre a ha
  exact shiftedNeumannResolventCoeff_l2_norm_le hω hzre hz ha

end ShenWork.PDE.ResolventEstimate
