import ShenWork.PDE.AnalyticSemigroupGen

/-!
# Exponential decay for the coefficient analytic Neumann semigroup

This file adds the spectral-bound decay part of the H3.1 coefficient
sectorial subblock.  For the shifted operator `A = -Δ_N + ω`, the diagonal
semigroup satisfies

`‖e^{-tA} a‖₂ ≤ exp (-ω t) ‖a‖₂`.

For the unshifted operator on zero-mode-free data, the first nonzero Neumann
eigenvalue gives

`‖e^{tΔ_N} a‖₂ ≤ exp (-λ₁ t) ‖a‖₂`.

These are coefficient `ℓ²` theorems; they do not assert the nonlinear
`SectorialLocalExponentialRaw` statement.
-/

noncomputable section

namespace ShenWork.PDE.AnalyticSemigroupDecay

open ShenWork.Paper3
open ShenWork.PDE.ResolventEstimate
open ShenWork.PDE.AnalyticSemigroupGen

/-! ### Shifted spectral-bound decay -/

lemma shiftedNeumannEigenvalue_ge_shift (ω : ℝ) (n : ℕ) :
    ω ≤ shiftedNeumannEigenvalue ω n := by
  unfold shiftedNeumannEigenvalue
  simpa [zero_add] using
    add_le_add_right (unitIntervalNeumannSpectrum_eigenvalue_nonneg n) ω

/-- Pointwise shifted heat coefficient decay from the spectral bound `ω`. -/
theorem shiftedNeumannHeatCoeff_sq_le_exp_shift
    {ω t : ℝ} (ht : 0 ≤ t) (a : ℕ → ℂ) (n : ℕ) :
    ‖shiftedNeumannHeatCoeff ω t a n‖ ^ 2 ≤
      (Real.exp (-(ω * t))) ^ 2 * ‖a n‖ ^ 2 := by
  set r := shiftedNeumannEigenvalue ω n with hrdef
  have hge : ω ≤ r := by
    simpa [hrdef] using shiftedNeumannEigenvalue_ge_shift ω n
  have hmul : -(r * t) ≤ -(ω * t) := by
    have hrt : ω * t ≤ r * t := mul_le_mul_of_nonneg_right hge ht
    linarith
  have hexp_le : Real.exp (-(r * t)) ≤ Real.exp (-(ω * t)) :=
    Real.exp_le_exp.mpr hmul
  have hexp_nonneg : 0 ≤ Real.exp (-(r * t)) := Real.exp_nonneg _
  have homega_nonneg : 0 ≤ Real.exp (-(ω * t)) := Real.exp_nonneg _
  have hnorm_nonneg : 0 ≤ ‖a n‖ := norm_nonneg _
  have hle :
      Real.exp (-(r * t)) * ‖a n‖ ≤
        Real.exp (-(ω * t)) * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hexp_le hnorm_nonneg
  calc
    ‖shiftedNeumannHeatCoeff ω t a n‖ ^ 2
        =
          (Real.exp (-(r * t)) * ‖a n‖) ^ 2 := by
            rw [shiftedNeumannHeatCoeff, ← hrdef, norm_mul,
              Complex.norm_of_nonneg hexp_nonneg]
    _ ≤ (Real.exp (-(ω * t)) * ‖a n‖) ^ 2 := by
            exact
              (sq_le_sq₀
                (mul_nonneg hexp_nonneg hnorm_nonneg)
                (mul_nonneg homega_nonneg hnorm_nonneg)).mpr hle
    _ = (Real.exp (-(ω * t))) ^ 2 * ‖a n‖ ^ 2 := by
            ring

/-- Shifted heat preserves square-summability under the spectral-bound
decay estimate. -/
theorem shiftedNeumannHeatCoeff_l2_summable_of_exp_shift
    {ω t : ℝ} (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ => ‖shiftedNeumannHeatCoeff ω t a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left ((Real.exp (-(ω * t))) ^ 2))
  intro n
  exact shiftedNeumannHeatCoeff_sq_le_exp_shift ht a n

/-- Coefficient `ℓ²` energy decay for the shifted Neumann heat semigroup. -/
theorem shiftedNeumannHeatCoeff_l2_energy_decay
    {ω t : ℝ} (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy (shiftedNeumannHeatCoeff ω t a) ≤
      (Real.exp (-(ω * t))) ^ 2 * coeffL2Energy a := by
  have hs :=
    shiftedNeumannHeatCoeff_l2_summable_of_exp_shift
      (ω := ω) (t := t) ht ha
  have hmajor :
      Summable fun n : ℕ =>
        (Real.exp (-(ω * t))) ^ 2 * ‖a n‖ ^ 2 :=
    ha.mul_left ((Real.exp (-(ω * t))) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖shiftedNeumannHeatCoeff ω t a n‖ ^ 2 ≤
          (Real.exp (-(ω * t))) ^ 2 * ‖a n‖ ^ 2 :=
    shiftedNeumannHeatCoeff_sq_le_exp_shift ht a
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- Coefficient `ℓ²` norm decay for the shifted Neumann heat semigroup. -/
theorem shiftedNeumannHeatCoeff_l2_norm_decay
    {ω t : ℝ} (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm (shiftedNeumannHeatCoeff ω t a) ≤
      Real.exp (-(ω * t)) * coeffL2Norm a := by
  have henergy :=
    shiftedNeumannHeatCoeff_l2_energy_decay (ω := ω) (t := t) ht ha
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hfactor_nonneg : 0 ≤ Real.exp (-(ω * t)) := Real.exp_nonneg _
  calc
    coeffL2Norm (shiftedNeumannHeatCoeff ω t a)
        = Real.sqrt (coeffL2Energy (shiftedNeumannHeatCoeff ω t a)) := rfl
    _ ≤ Real.sqrt
          ((Real.exp (-(ω * t))) ^ 2 * coeffL2Energy a) := hsqrt
    _ = Real.exp (-(ω * t)) * coeffL2Norm a := by
          rw [Real.sqrt_mul (sq_nonneg (Real.exp (-(ω * t))))]
          rw [Real.sqrt_sq hfactor_nonneg]
          rfl

/-! ### First-mode decay for zero-mode-free unshifted heat -/

/-- Pointwise first-mode decay for zero-mode-free coefficients under the
unshifted Neumann heat semigroup. -/
theorem unshiftedNeumannHeatCoeff_sq_le_firstNonzero_of_zeroMode
    {t : ℝ} (ht : 0 ≤ t) {a : ℕ → ℂ} (ha0 : a 0 = 0) (n : ℕ) :
    ‖shiftedNeumannHeatCoeff 0 t a n‖ ^ 2 ≤
      (Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))) ^ 2 *
        ‖a n‖ ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [shiftedNeumannHeatCoeff, ha0]
  · set r := shiftedNeumannEigenvalue 0 n with hrdef
    have hge : unitIntervalNeumannSpectrum.firstNonzero ≤ r := by
      have H := unitIntervalNeumannSpectrum_hasNeumannSpectrum
      have hle := H.firstNonzero_le_eigenvalue n hn
      simpa [hrdef, shiftedNeumannEigenvalue] using hle
    have hmul :
        -(r * t) ≤ -(unitIntervalNeumannSpectrum.firstNonzero * t) := by
      have hrt :
          unitIntervalNeumannSpectrum.firstNonzero * t ≤ r * t :=
        mul_le_mul_of_nonneg_right hge ht
      linarith
    have hexp_le :
        Real.exp (-(r * t)) ≤
          Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t)) :=
      Real.exp_le_exp.mpr hmul
    have hexp_nonneg : 0 ≤ Real.exp (-(r * t)) := Real.exp_nonneg _
    have hfirst_nonneg :
        0 ≤ Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t)) :=
      Real.exp_nonneg _
    have hnorm_nonneg : 0 ≤ ‖a n‖ := norm_nonneg _
    have hle :
        Real.exp (-(r * t)) * ‖a n‖ ≤
          Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t)) *
            ‖a n‖ :=
      mul_le_mul_of_nonneg_right hexp_le hnorm_nonneg
    calc
      ‖shiftedNeumannHeatCoeff 0 t a n‖ ^ 2
          =
            (Real.exp (-(r * t)) * ‖a n‖) ^ 2 := by
              rw [shiftedNeumannHeatCoeff, ← hrdef, norm_mul,
                Complex.norm_of_nonneg hexp_nonneg]
      _ ≤
            (Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t)) *
              ‖a n‖) ^ 2 := by
              exact
                (sq_le_sq₀
                  (mul_nonneg hexp_nonneg hnorm_nonneg)
                  (mul_nonneg hfirst_nonneg hnorm_nonneg)).mpr hle
      _ =
            (Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))) ^ 2 *
              ‖a n‖ ^ 2 := by
              ring

/-- Zero-mode-free unshifted heat preserves square-summability with
first-mode decay. -/
theorem unshiftedNeumannHeatCoeff_l2_summable_firstNonzero_of_zeroMode
    {t : ℝ} (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    Summable fun n : ℕ => ‖shiftedNeumannHeatCoeff 0 t a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left
      ((Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))) ^ 2))
  intro n
  exact unshiftedNeumannHeatCoeff_sq_le_firstNonzero_of_zeroMode ht ha0 n

/-- Coefficient `ℓ²` energy first-mode decay for zero-mode-free unshifted
Neumann heat. -/
theorem unshiftedNeumannHeatCoeff_l2_energy_firstNonzero_of_zeroMode
    {t : ℝ} (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Energy (shiftedNeumannHeatCoeff 0 t a) ≤
      (Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))) ^ 2 *
        coeffL2Energy a := by
  have hs :=
    unshiftedNeumannHeatCoeff_l2_summable_firstNonzero_of_zeroMode
      ht ha ha0
  have hmajor :
      Summable fun n : ℕ =>
        (Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))) ^ 2 *
          ‖a n‖ ^ 2 :=
    ha.mul_left
      ((Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖shiftedNeumannHeatCoeff 0 t a n‖ ^ 2 ≤
          (Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))) ^ 2 *
            ‖a n‖ ^ 2 :=
    unshiftedNeumannHeatCoeff_sq_le_firstNonzero_of_zeroMode ht ha0
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- Coefficient `ℓ²` norm first-mode decay for zero-mode-free unshifted
Neumann heat. -/
theorem unshiftedNeumannHeatCoeff_l2_norm_firstNonzero_of_zeroMode
    {t : ℝ} (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Norm (shiftedNeumannHeatCoeff 0 t a) ≤
      Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t)) *
        coeffL2Norm a := by
  have henergy :=
    unshiftedNeumannHeatCoeff_l2_energy_firstNonzero_of_zeroMode
      ht ha ha0
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hfactor_nonneg :
      0 ≤ Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t)) :=
    Real.exp_nonneg _
  calc
    coeffL2Norm (shiftedNeumannHeatCoeff 0 t a)
        = Real.sqrt (coeffL2Energy (shiftedNeumannHeatCoeff 0 t a)) := rfl
    _ ≤ Real.sqrt
          ((Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))) ^ 2 *
            coeffL2Energy a) := hsqrt
    _ =
          Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t)) *
            coeffL2Norm a := by
          rw [Real.sqrt_mul
            (sq_nonneg
              (Real.exp (-(unitIntervalNeumannSpectrum.firstNonzero * t))))]
          rw [Real.sqrt_sq hfactor_nonneg]
          rfl

end ShenWork.PDE.AnalyticSemigroupDecay
