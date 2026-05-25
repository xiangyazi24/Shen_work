/-
  ShenWork/PDE/SectorialOperator.lean

  Spectral diagonal sectorial infrastructure for the unit-interval Neumann
  cosine basis.

  This file proves the Hilbert-space part of the H3.1 sectorial story: a
  diagonal generator on the complete cosine Hilbert basis has the expected
  semigroup law, real resolvent bound, spectral-bound semigroup estimate, and
  spectral-gap exponential decay in `L²`.

  It deliberately does not claim `SectorialLocalExponentialRaw`: that Paper3
  raw statement is a nonlinear small-data stability assertion for global
  classical solutions and still needs Duhamel/fixed-point estimates plus local
  Cauchy theory.
-/
import ShenWork.PDE.CosineSpectrum
import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.Paper3.Statements
import Mathlib.Analysis.Complex.RealDeriv

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.PDE.SectorialOperator

open ShenWork.IntervalDomain
open ShenWork.HeatKernelGradientEstimates
open ShenWork.Paper3

/-! ### Coefficient and cosine-Hilbert reconstruction model -/

/-- Unweighted coefficient `ℓ²` energy. -/
def coeffL2Energy (a : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ ^ 2

/-- Coefficient energy is nonnegative. -/
theorem coeffL2Energy_nonneg (a : ℕ → ℂ) :
    0 ≤ coeffL2Energy a := by
  exact tsum_nonneg fun n => sq_nonneg _

/-- Coefficient `ℓ²` norm induced by `coeffL2Energy`. -/
def coeffL2Norm (a : ℕ → ℂ) : ℝ :=
  Real.sqrt (coeffL2Energy a)

/-- Coefficient `ℓ²` norm is nonnegative. -/
theorem coeffL2Norm_nonneg (a : ℕ → ℂ) :
    0 ≤ coeffL2Norm a := by
  exact Real.sqrt_nonneg _

/-- Package square-summable coefficients as an `ℓ²` vector. -/
def coeffLp2 (a : ℕ → ℂ)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) : ℓ²(ℕ, ℂ) := by
  refine ⟨a, ?_⟩
  change Memℓp (a : PreLp (fun _ : ℕ => ℂ)) (2 : ℝ≥0∞)
  simpa [Memℓp] using ha

/-- Reconstruct an interval `L²` vector from normalized cosine coefficients. -/
def cosineLpFromCoeffs
    (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Lp ℂ 2 (intervalMeasure 1) :=
  unitIntervalCosineHilbertBasis.repr.symm (coeffLp2 a ha)

/-- The reconstructed interval `L²` vector has the prescribed normalized
cosine coefficients. -/
theorem cosineLpFromCoeffs_repr
    (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (n : ℕ) :
    unitIntervalCosineHilbertBasis.repr
        (cosineLpFromCoeffs a ha) n = a n := by
  simp [cosineLpFromCoeffs, coeffLp2]

/-- The reconstructed interval `L²` norm is exactly the coefficient energy. -/
theorem cosineLpFromCoeffs_norm_sq
    (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖cosineLpFromCoeffs a ha‖ ^ 2 = coeffL2Energy a := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h :=
    lp.norm_rpow_eq_tsum (E := fun _ : ℕ => ℂ)
      (p := (2 : ℝ≥0∞)) hp (coeffLp2 a ha)
  simpa [cosineLpFromCoeffs, coeffL2Energy] using h

/-! ### Diagonal semigroup and resolvent on coefficients -/

/-- Diagonal generator multiplier on coefficients. -/
def diagonalGeneratorCoeff
    (growth : ℕ → ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (growth n : ℂ) * a n

/-- Coefficient form of `(z - A) a` for the diagonal generator `A`. -/
def diagonalShiftMinusGeneratorCoeff
    (growth : ℕ → ℝ) (z : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((z - growth n : ℝ) : ℂ) * a n

/-- Diagonal semigroup multiplier `exp(t g_n)` on coefficients. -/
def diagonalSemigroupCoeff
    (growth : ℕ → ℝ) (t : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.exp (t * growth n) : ℂ) * a n

/-- Real resolvent multiplier `(z - g_n)^{-1}` on coefficients. -/
def diagonalResolventCoeff
    (growth : ℕ → ℝ) (z : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (((z - growth n)⁻¹ : ℝ) : ℂ) * a n

/-- The diagonal multipliers form a semigroup on coefficients. -/
theorem diagonalSemigroupCoeff_add
    (growth : ℕ → ℝ) (t s : ℝ) (a : ℕ → ℂ) :
    diagonalSemigroupCoeff growth (t + s) a =
      diagonalSemigroupCoeff growth t
        (diagonalSemigroupCoeff growth s a) := by
  funext n
  unfold diagonalSemigroupCoeff
  rw [show (t + s) * growth n = t * growth n + s * growth n by ring,
    Real.exp_add]
  norm_num [Complex.ofReal_mul]
  ring

/-- The diagonal semigroup at time zero is the identity on coefficients. -/
theorem diagonalSemigroupCoeff_zero
    (growth : ℕ → ℝ) (a : ℕ → ℂ) :
    diagonalSemigroupCoeff growth 0 a = a := by
  funext n
  simp [diagonalSemigroupCoeff]

/-- Coefficientwise derivative of the diagonal semigroup orbit. -/
theorem diagonalSemigroupCoeff_hasDerivAt
    (growth : ℕ → ℝ) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => diagonalSemigroupCoeff growth s a n)
      (diagonalGeneratorCoeff growth
        (diagonalSemigroupCoeff growth t a) n) t := by
  unfold diagonalSemigroupCoeff diagonalGeneratorCoeff
  have hreal : HasDerivAt (fun s : ℝ => Real.exp (s * growth n))
      (Real.exp (t * growth n) * growth n) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id t).mul_const (growth n)).exp)
  have hc : HasDerivAt
      (fun s : ℝ => ((Real.exp (s * growth n) : ℝ) : ℂ))
      ((Real.exp (t * growth n) * growth n : ℝ) : ℂ) t :=
    hreal.ofReal_comp
  simpa [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc] using
    hc.const_mul (a n)

/-- Pointwise coefficient bound from a spectral upper bound `growth_n ≤ ω`. -/
theorem diagonalSemigroupCoeff_sq_le_of_growth_le
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, growth n ≤ omega) (a : ℕ → ℂ) (n : ℕ) :
    ‖diagonalSemigroupCoeff growth t a n‖ ^ 2 ≤
      (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 := by
  have hmul : t * growth n ≤ t * omega :=
    mul_le_mul_of_nonneg_left (hgrowth n) ht
  have hexp_le : Real.exp (t * growth n) ≤ Real.exp (t * omega) :=
    Real.exp_le_exp.mpr hmul
  have hexp_nonneg : 0 ≤ Real.exp (t * growth n) := Real.exp_nonneg _
  have homega_nonneg : 0 ≤ Real.exp (t * omega) := Real.exp_nonneg _
  have hnorm_nonneg : 0 ≤ ‖a n‖ := norm_nonneg _
  have hle :
      Real.exp (t * growth n) * ‖a n‖ ≤
        Real.exp (t * omega) * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hexp_le hnorm_nonneg
  calc
    ‖diagonalSemigroupCoeff growth t a n‖ ^ 2
        =
          (Real.exp (t * growth n) * ‖a n‖) ^ 2 := by
            rw [diagonalSemigroupCoeff, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
    _ ≤ (Real.exp (t * omega) * ‖a n‖) ^ 2 := by
            exact
              (sq_le_sq₀
                (mul_nonneg hexp_nonneg hnorm_nonneg)
                (mul_nonneg homega_nonneg hnorm_nonneg)).mpr hle
    _ = (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 := by
            ring

/-- Pointwise coefficient bound from a single-mode spectral upper bound. -/
theorem diagonalSemigroupCoeff_sq_le_of_growth_le_at
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    {a : ℕ → ℂ} {n : ℕ} (hgrowth : growth n ≤ omega) :
    ‖diagonalSemigroupCoeff growth t a n‖ ^ 2 ≤
      (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 := by
  have hmul : t * growth n ≤ t * omega :=
    mul_le_mul_of_nonneg_left hgrowth ht
  have hexp_le : Real.exp (t * growth n) ≤ Real.exp (t * omega) :=
    Real.exp_le_exp.mpr hmul
  have hexp_nonneg : 0 ≤ Real.exp (t * growth n) := Real.exp_nonneg _
  have homega_nonneg : 0 ≤ Real.exp (t * omega) := Real.exp_nonneg _
  have hnorm_nonneg : 0 ≤ ‖a n‖ := norm_nonneg _
  have hle :
      Real.exp (t * growth n) * ‖a n‖ ≤
        Real.exp (t * omega) * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hexp_le hnorm_nonneg
  calc
    ‖diagonalSemigroupCoeff growth t a n‖ ^ 2
        =
          (Real.exp (t * growth n) * ‖a n‖) ^ 2 := by
            rw [diagonalSemigroupCoeff, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
    _ ≤ (Real.exp (t * omega) * ‖a n‖) ^ 2 := by
            exact
              (sq_le_sq₀
                (mul_nonneg hexp_nonneg hnorm_nonneg)
                (mul_nonneg homega_nonneg hnorm_nonneg)).mpr hle
    _ = (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 := by
            ring

/-- Pointwise semigroup bound from a nonzero-mode spectral upper bound and a
vanishing zero coefficient. -/
theorem diagonalSemigroupCoeff_sq_le_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega)
    {a : ℕ → ℂ} (ha0 : a 0 = 0) (n : ℕ) :
    ‖diagonalSemigroupCoeff growth t a n‖ ^ 2 ≤
      (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [diagonalSemigroupCoeff, ha0]
  · exact diagonalSemigroupCoeff_sq_le_of_growth_le_at
      (growth := growth) (omega := omega) ht (a := a)
      (n := n) (hgrowth n hn)

/-- The diagonal semigroup preserves `ℓ²` under a spectral upper bound. -/
theorem diagonalSemigroupCoeff_l2_summable_of_growth_le
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖diagonalSemigroupCoeff growth t a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left ((Real.exp (t * omega)) ^ 2))
  intro n
  exact diagonalSemigroupCoeff_sq_le_of_growth_le ht hgrowth a n

/-- The diagonal semigroup preserves `ℓ²` under a nonzero-mode spectral upper
bound, provided the zero coefficient vanishes. -/
theorem diagonalSemigroupCoeff_l2_summable_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    Summable fun n : ℕ =>
      ‖diagonalSemigroupCoeff growth t a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left ((Real.exp (t * omega)) ^ 2))
  intro n
  exact diagonalSemigroupCoeff_sq_le_of_growth_le_on_nonzero
    ht hgrowth ha0 n

/-- `L²` coefficient-energy semigroup bound from a spectral upper bound. -/
theorem diagonalSemigroupCoeff_l2_energy_le_of_growth_le
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy (diagonalSemigroupCoeff growth t a) ≤
      (Real.exp (t * omega)) ^ 2 * coeffL2Energy a := by
  have hs :=
    diagonalSemigroupCoeff_l2_summable_of_growth_le
      (growth := growth) (omega := omega) ht hgrowth ha
  have hmajor :
      Summable fun n : ℕ =>
        (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 :=
    ha.mul_left ((Real.exp (t * omega)) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖diagonalSemigroupCoeff growth t a n‖ ^ 2 ≤
          (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 :=
    diagonalSemigroupCoeff_sq_le_of_growth_le ht hgrowth a
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- `L²` coefficient-norm semigroup bound from a spectral upper bound. -/
theorem diagonalSemigroupCoeff_l2_norm_le_of_growth_le
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm (diagonalSemigroupCoeff growth t a) ≤
      Real.exp (t * omega) * coeffL2Norm a := by
  have henergy :=
    diagonalSemigroupCoeff_l2_energy_le_of_growth_le
      (growth := growth) (omega := omega) ht hgrowth ha
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hfactor_nonneg : 0 ≤ Real.exp (t * omega) := Real.exp_nonneg _
  calc
    coeffL2Norm (diagonalSemigroupCoeff growth t a)
        = Real.sqrt (coeffL2Energy
            (diagonalSemigroupCoeff growth t a)) := rfl
    _ ≤ Real.sqrt
          ((Real.exp (t * omega)) ^ 2 * coeffL2Energy a) := hsqrt
    _ = Real.exp (t * omega) * coeffL2Norm a := by
          rw [Real.sqrt_mul (sq_nonneg (Real.exp (t * omega)))]
          rw [Real.sqrt_sq hfactor_nonneg]
          rfl

/-- `L²` coefficient-energy semigroup bound from a nonzero-mode spectral upper
bound and a vanishing zero coefficient. -/
theorem diagonalSemigroupCoeff_l2_energy_le_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Energy (diagonalSemigroupCoeff growth t a) ≤
      (Real.exp (t * omega)) ^ 2 * coeffL2Energy a := by
  have hs :=
    diagonalSemigroupCoeff_l2_summable_of_growth_le_on_nonzero
      (growth := growth) (omega := omega) ht hgrowth ha ha0
  have hmajor :
      Summable fun n : ℕ =>
        (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 :=
    ha.mul_left ((Real.exp (t * omega)) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖diagonalSemigroupCoeff growth t a n‖ ^ 2 ≤
          (Real.exp (t * omega)) ^ 2 * ‖a n‖ ^ 2 :=
    diagonalSemigroupCoeff_sq_le_of_growth_le_on_nonzero
      ht hgrowth ha0
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- `L²` coefficient-norm semigroup bound from a nonzero-mode spectral upper
bound and a vanishing zero coefficient. -/
theorem diagonalSemigroupCoeff_l2_norm_le_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Norm (diagonalSemigroupCoeff growth t a) ≤
      Real.exp (t * omega) * coeffL2Norm a := by
  have henergy :=
    diagonalSemigroupCoeff_l2_energy_le_of_growth_le_on_nonzero
      (growth := growth) (omega := omega) ht hgrowth ha ha0
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hfactor_nonneg : 0 ≤ Real.exp (t * omega) := Real.exp_nonneg _
  calc
    coeffL2Norm (diagonalSemigroupCoeff growth t a)
        = Real.sqrt (coeffL2Energy
            (diagonalSemigroupCoeff growth t a)) := rfl
    _ ≤ Real.sqrt
          ((Real.exp (t * omega)) ^ 2 * coeffL2Energy a) := hsqrt
    _ = Real.exp (t * omega) * coeffL2Norm a := by
          rw [Real.sqrt_mul (sq_nonneg (Real.exp (t * omega)))]
          rw [Real.sqrt_sq hfactor_nonneg]
          rfl

/-- Reconstructed interval `L²` semigroup bound from a spectral upper bound. -/
theorem diagonalSemigroupLp_norm_sq_le_of_growth_le
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖cosineLpFromCoeffs
        (diagonalSemigroupCoeff growth t a)
        (diagonalSemigroupCoeff_l2_summable_of_growth_le
          (growth := growth) (omega := omega) ht hgrowth ha)‖ ^ 2 ≤
      (Real.exp (t * omega)) ^ 2 * coeffL2Energy a := by
  rw [cosineLpFromCoeffs_norm_sq]
  exact diagonalSemigroupCoeff_l2_energy_le_of_growth_le
    (growth := growth) (omega := omega) ht hgrowth ha

/-- Reconstructed interval `L²` semigroup norm bound from a spectral upper
bound. -/
theorem diagonalSemigroupLp_norm_le_of_growth_le
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖cosineLpFromCoeffs
        (diagonalSemigroupCoeff growth t a)
        (diagonalSemigroupCoeff_l2_summable_of_growth_le
          (growth := growth) (omega := omega) ht hgrowth ha)‖ ≤
      Real.exp (t * omega) * coeffL2Norm a := by
  have hsq :=
    diagonalSemigroupLp_norm_sq_le_of_growth_le
      (growth := growth) (omega := omega) ht hgrowth ha
  have hright :
      (Real.exp (t * omega) * coeffL2Norm a) ^ 2 =
        (Real.exp (t * omega)) ^ 2 * coeffL2Energy a := by
    simp [coeffL2Norm, mul_pow, Real.sq_sqrt (coeffL2Energy_nonneg a)]
  exact
    (sq_le_sq₀
      (norm_nonneg _)
      (mul_nonneg (Real.exp_nonneg _) (coeffL2Norm_nonneg a))).mp
      (by simpa [hright] using hsq)

/-- Reconstructed interval `L²` semigroup bound from a nonzero-mode spectral
upper bound and a vanishing zero coefficient. -/
theorem diagonalSemigroupLp_norm_sq_le_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    ‖cosineLpFromCoeffs
        (diagonalSemigroupCoeff growth t a)
        (diagonalSemigroupCoeff_l2_summable_of_growth_le_on_nonzero
          (growth := growth) (omega := omega) ht hgrowth ha ha0)‖ ^ 2 ≤
      (Real.exp (t * omega)) ^ 2 * coeffL2Energy a := by
  rw [cosineLpFromCoeffs_norm_sq]
  exact diagonalSemigroupCoeff_l2_energy_le_of_growth_le_on_nonzero
    (growth := growth) (omega := omega) ht hgrowth ha ha0

/-- Reconstructed interval `L²` semigroup norm bound from a nonzero-mode
spectral upper bound and a vanishing zero coefficient. -/
theorem diagonalSemigroupLp_norm_le_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega t : ℝ} (ht : 0 ≤ t)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    ‖cosineLpFromCoeffs
        (diagonalSemigroupCoeff growth t a)
        (diagonalSemigroupCoeff_l2_summable_of_growth_le_on_nonzero
          (growth := growth) (omega := omega) ht hgrowth ha ha0)‖ ≤
      Real.exp (t * omega) * coeffL2Norm a := by
  have hsq :=
    diagonalSemigroupLp_norm_sq_le_of_growth_le_on_nonzero
      (growth := growth) (omega := omega) ht hgrowth ha ha0
  have hright :
      (Real.exp (t * omega) * coeffL2Norm a) ^ 2 =
        (Real.exp (t * omega)) ^ 2 * coeffL2Energy a := by
    simp [coeffL2Norm, mul_pow, Real.sq_sqrt (coeffL2Energy_nonneg a)]
  exact
    (sq_le_sq₀
      (norm_nonneg _)
      (mul_nonneg (Real.exp_nonneg _) (coeffL2Norm_nonneg a))).mp
      (by simpa [hright] using hsq)

/-- Pointwise real resolvent coefficient bound outside the spectral half-line. -/
theorem diagonalResolventCoeff_sq_le_of_growth_le
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    (hgrowth : ∀ n, growth n ≤ omega) (a : ℕ → ℂ) (n : ℕ) :
    ‖diagonalResolventCoeff growth z a n‖ ^ 2 ≤
      ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 := by
  have hden_pos : 0 < z - growth n := by linarith [hgrowth n]
  have homega_pos : 0 < z - omega := by linarith
  have hden_ge : z - omega ≤ z - growth n := by linarith [hgrowth n]
  have hinv_le : (z - growth n)⁻¹ ≤ (z - omega)⁻¹ :=
    (inv_le_inv₀ hden_pos homega_pos).mpr hden_ge
  have hinv_nonneg : 0 ≤ (z - growth n)⁻¹ :=
    inv_nonneg.mpr hden_pos.le
  have homega_inv_nonneg : 0 ≤ (z - omega)⁻¹ :=
    inv_nonneg.mpr homega_pos.le
  have hnorm_nonneg : 0 ≤ ‖a n‖ := norm_nonneg _
  have hle :
      (z - growth n)⁻¹ * ‖a n‖ ≤
        (z - omega)⁻¹ * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hinv_le hnorm_nonneg
  calc
    ‖diagonalResolventCoeff growth z a n‖ ^ 2
        = ((z - growth n)⁻¹ * ‖a n‖) ^ 2 := by
            rw [diagonalResolventCoeff, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
    _ ≤ ((z - omega)⁻¹ * ‖a n‖) ^ 2 := by
            exact
              (sq_le_sq₀
                (mul_nonneg hinv_nonneg hnorm_nonneg)
                (mul_nonneg homega_inv_nonneg hnorm_nonneg)).mpr hle
    _ = ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 := by
            ring

/-- Pointwise real resolvent coefficient bound from a single-mode spectral
upper bound. -/
theorem diagonalResolventCoeff_sq_le_of_growth_le_at
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    {a : ℕ → ℂ} {n : ℕ} (hgrowth : growth n ≤ omega) :
    ‖diagonalResolventCoeff growth z a n‖ ^ 2 ≤
      ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 := by
  have hden_pos : 0 < z - growth n := by linarith [hgrowth]
  have homega_pos : 0 < z - omega := by linarith
  have hden_ge : z - omega ≤ z - growth n := by linarith [hgrowth]
  have hinv_le : (z - growth n)⁻¹ ≤ (z - omega)⁻¹ :=
    (inv_le_inv₀ hden_pos homega_pos).mpr hden_ge
  have hinv_nonneg : 0 ≤ (z - growth n)⁻¹ :=
    inv_nonneg.mpr hden_pos.le
  have homega_inv_nonneg : 0 ≤ (z - omega)⁻¹ :=
    inv_nonneg.mpr homega_pos.le
  have hnorm_nonneg : 0 ≤ ‖a n‖ := norm_nonneg _
  have hle :
      (z - growth n)⁻¹ * ‖a n‖ ≤
        (z - omega)⁻¹ * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hinv_le hnorm_nonneg
  calc
    ‖diagonalResolventCoeff growth z a n‖ ^ 2
        = ((z - growth n)⁻¹ * ‖a n‖) ^ 2 := by
            rw [diagonalResolventCoeff, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
    _ ≤ ((z - omega)⁻¹ * ‖a n‖) ^ 2 := by
            exact
              (sq_le_sq₀
                (mul_nonneg hinv_nonneg hnorm_nonneg)
                (mul_nonneg homega_inv_nonneg hnorm_nonneg)).mpr hle
    _ = ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 := by
            ring

/-- Pointwise resolvent bound from a nonzero-mode spectral upper bound and a
vanishing zero coefficient. -/
theorem diagonalResolventCoeff_sq_le_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega)
    {a : ℕ → ℂ} (ha0 : a 0 = 0) (n : ℕ) :
    ‖diagonalResolventCoeff growth z a n‖ ^ 2 ≤
      ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [diagonalResolventCoeff, ha0]
  · exact diagonalResolventCoeff_sq_le_of_growth_le_at
      (growth := growth) (omega := omega) hz (a := a)
      (n := n) (hgrowth n hn)

/-- The real resolvent preserves `ℓ²` outside the spectral upper bound. -/
theorem diagonalResolventCoeff_l2_summable_of_growth_le
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    (hgrowth : ∀ n, growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖diagonalResolventCoeff growth z a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left (((z - omega)⁻¹) ^ 2))
  intro n
  exact diagonalResolventCoeff_sq_le_of_growth_le hz hgrowth a n

/-- The real resolvent preserves `ℓ²` under a nonzero-mode spectral upper
bound, provided the zero coefficient vanishes. -/
theorem diagonalResolventCoeff_l2_summable_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    Summable fun n : ℕ =>
      ‖diagonalResolventCoeff growth z a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    ?_
    (ha.mul_left (((z - omega)⁻¹) ^ 2))
  intro n
  exact diagonalResolventCoeff_sq_le_of_growth_le_on_nonzero
    hz hgrowth ha0 n

/-- `L²` coefficient-energy real resolvent bound. -/
theorem diagonalResolventCoeff_l2_energy_le_of_growth_le
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    (hgrowth : ∀ n, growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy (diagonalResolventCoeff growth z a) ≤
      ((z - omega)⁻¹) ^ 2 * coeffL2Energy a := by
  have hs :=
    diagonalResolventCoeff_l2_summable_of_growth_le
      (growth := growth) (omega := omega) hz hgrowth ha
  have hmajor :
      Summable fun n : ℕ => ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 :=
    ha.mul_left (((z - omega)⁻¹) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖diagonalResolventCoeff growth z a n‖ ^ 2 ≤
          ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 :=
    diagonalResolventCoeff_sq_le_of_growth_le hz hgrowth a
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- `L²` coefficient-norm real resolvent bound. -/
theorem diagonalResolventCoeff_l2_norm_le_of_growth_le
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    (hgrowth : ∀ n, growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm (diagonalResolventCoeff growth z a) ≤
      (z - omega)⁻¹ * coeffL2Norm a := by
  have henergy :=
    diagonalResolventCoeff_l2_energy_le_of_growth_le
      (growth := growth) (omega := omega) hz hgrowth ha
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hfactor_nonneg : 0 ≤ (z - omega)⁻¹ := by
    exact inv_nonneg.mpr (by linarith : 0 ≤ z - omega)
  calc
    coeffL2Norm (diagonalResolventCoeff growth z a)
        = Real.sqrt (coeffL2Energy
            (diagonalResolventCoeff growth z a)) := rfl
    _ ≤ Real.sqrt (((z - omega)⁻¹) ^ 2 * coeffL2Energy a) := hsqrt
    _ = (z - omega)⁻¹ * coeffL2Norm a := by
          rw [Real.sqrt_mul (sq_nonneg ((z - omega)⁻¹))]
          rw [Real.sqrt_sq hfactor_nonneg]
          rfl

/-- `L²` coefficient-energy real resolvent bound from a nonzero-mode spectral
upper bound and a vanishing zero coefficient. -/
theorem diagonalResolventCoeff_l2_energy_le_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Energy (diagonalResolventCoeff growth z a) ≤
      ((z - omega)⁻¹) ^ 2 * coeffL2Energy a := by
  have hs :=
    diagonalResolventCoeff_l2_summable_of_growth_le_on_nonzero
      (growth := growth) (omega := omega) hz hgrowth ha ha0
  have hmajor :
      Summable fun n : ℕ => ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 :=
    ha.mul_left (((z - omega)⁻¹) ^ 2)
  have hle :
      ∀ n : ℕ,
        ‖diagonalResolventCoeff growth z a n‖ ^ 2 ≤
          ((z - omega)⁻¹) ^ 2 * ‖a n‖ ^ 2 :=
    diagonalResolventCoeff_sq_le_of_growth_le_on_nonzero
      hz hgrowth ha0
  have htsum := hs.tsum_le_tsum hle hmajor
  simpa [coeffL2Energy, ha.tsum_mul_left] using htsum

/-- `L²` coefficient-norm real resolvent bound from a nonzero-mode spectral
upper bound and a vanishing zero coefficient. -/
theorem diagonalResolventCoeff_l2_norm_le_of_growth_le_on_nonzero
    {growth : ℕ → ℝ} {omega z : ℝ} (hz : omega < z)
    (hgrowth : ∀ n, n ≠ 0 → growth n ≤ omega) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Norm (diagonalResolventCoeff growth z a) ≤
      (z - omega)⁻¹ * coeffL2Norm a := by
  have henergy :=
    diagonalResolventCoeff_l2_energy_le_of_growth_le_on_nonzero
      (growth := growth) (omega := omega) hz hgrowth ha ha0
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hfactor_nonneg : 0 ≤ (z - omega)⁻¹ := by
    exact inv_nonneg.mpr (by linarith : 0 ≤ z - omega)
  calc
    coeffL2Norm (diagonalResolventCoeff growth z a)
        = Real.sqrt (coeffL2Energy
            (diagonalResolventCoeff growth z a)) := rfl
    _ ≤ Real.sqrt (((z - omega)⁻¹) ^ 2 * coeffL2Energy a) := hsqrt
    _ = (z - omega)⁻¹ * coeffL2Norm a := by
          rw [Real.sqrt_mul (sq_nonneg ((z - omega)⁻¹))]
          rw [Real.sqrt_sq hfactor_nonneg]
          rfl

/-- `(z - A) R(z,A) = I` at the coefficient level, outside the real spectral
half-line. -/
theorem diagonalShiftMinusGeneratorCoeff_resolvent
    {growth : ℕ → ℝ} {omega z : ℝ}
    (hz : omega < z) (hgrowth : ∀ n, growth n ≤ omega)
    (a : ℕ → ℂ) :
    diagonalShiftMinusGeneratorCoeff growth z
        (diagonalResolventCoeff growth z a) = a := by
  funext n
  have hzg : z ≠ growth n := by
    linarith [hgrowth n, hz]
  have hden_ne : (z - growth n : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hzg
  have hprod :
      ((z - growth n : ℝ) : ℂ) *
          (((z - growth n)⁻¹ : ℝ) : ℂ) = 1 := by
    have hprod_real : (z - growth n : ℝ) * (z - growth n)⁻¹ = 1 :=
      mul_inv_cancel₀ hden_ne
    exact_mod_cast hprod_real
  calc
    diagonalShiftMinusGeneratorCoeff growth z
        (diagonalResolventCoeff growth z a) n
        =
          ((z - growth n : ℝ) : ℂ) *
            ((((z - growth n)⁻¹ : ℝ) : ℂ) * a n) := by
            rfl
    _ = (((z - growth n : ℝ) : ℂ) *
          (((z - growth n)⁻¹ : ℝ) : ℂ)) * a n := by
            ring
    _ = a n := by
            simpa using congrArg (fun c : ℂ => c * a n) hprod

/-- `R(z,A) (z - A) = I` at the coefficient level, outside the real spectral
half-line. -/
theorem diagonalResolventCoeff_shiftMinusGenerator
    {growth : ℕ → ℝ} {omega z : ℝ}
    (hz : omega < z) (hgrowth : ∀ n, growth n ≤ omega)
    (a : ℕ → ℂ) :
    diagonalResolventCoeff growth z
        (diagonalShiftMinusGeneratorCoeff growth z a) = a := by
  funext n
  have hzg : z ≠ growth n := by
    linarith [hgrowth n, hz]
  have hden_ne : (z - growth n : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hzg
  have hprod :
      (((z - growth n)⁻¹ : ℝ) : ℂ) *
          ((z - growth n : ℝ) : ℂ) = 1 := by
    have hprod_real : (z - growth n)⁻¹ * (z - growth n : ℝ) = 1 :=
      inv_mul_cancel₀ hden_ne
    exact_mod_cast hprod_real
  calc
    diagonalResolventCoeff growth z
        (diagonalShiftMinusGeneratorCoeff growth z a) n
        =
          (((z - growth n)⁻¹ : ℝ) : ℂ) *
            (((z - growth n : ℝ) : ℂ) * a n) := by
            rfl
    _ = ((((z - growth n)⁻¹ : ℝ) : ℂ) *
          ((z - growth n : ℝ) : ℂ)) * a n := by
            ring
    _ = a n := by
            simpa using congrArg (fun c : ℂ => c * a n) hprod

/-! ### Unit-interval Paper3 linearized growth rates -/

/-- The scalar growth rate of the Paper3 linearized Neumann mode. -/
def unitIntervalLinearizedGrowth
    (p : CM2Params) (uStar vStar : ℝ) (n : ℕ) : ℝ :=
  sigma p uStar vStar (unitIntervalNeumannSpectrum.eigenvalue n)

/-- Full spectral upper bound for the unit-interval linearized operator. -/
def UnitIntervalLinearSpectralBound
    (p : CM2Params) (uStar vStar omega : ℝ) : Prop :=
  ∀ n : ℕ, unitIntervalLinearizedGrowth p uStar vStar n ≤ omega

/-- Full spectral gap for the unit-interval linearized operator. -/
def UnitIntervalLinearSpectralGap
    (p : CM2Params) (uStar vStar rate : ℝ) : Prop :=
  0 < rate ∧ UnitIntervalLinearSpectralBound p uStar vStar (-rate)

/-- Nonzero-mode spectral upper bound for the mass-constrained interval
linearization.  This is the right linear package for the minimal branch, where
the constant mode is neutral. -/
def UnitIntervalLinearMassSpectralBound
    (p : CM2Params) (uStar vStar omega : ℝ) : Prop :=
  ∀ n : ℕ, n ≠ 0 → unitIntervalLinearizedGrowth p uStar vStar n ≤ omega

/-- Nonzero-mode spectral gap for the mass-constrained interval linearization. -/
def UnitIntervalLinearMassSpectralGap
    (p : CM2Params) (uStar vStar rate : ℝ) : Prop :=
  0 < rate ∧ UnitIntervalLinearMassSpectralBound p uStar vStar (-rate)

/-- A uniform spectral gap is stronger than Paper3's modewise linear
stability predicate. -/
theorem UnitIntervalLinearSpectralGap.linearlyStable
    {p : CM2Params} {uStar vStar rate : ℝ}
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate) :
    LinearlyStable unitIntervalNeumannSpectrum p uStar vStar := by
  intro n hn
  have hmode :
      sigma p uStar vStar (unitIntervalNeumannSpectrum.eigenvalue n) ≤
        -rate :=
    hgap.2 n
  exact lt_of_le_of_lt hmode (by linarith [hgap.1])

/-- A nonzero-mode spectral gap is exactly the linear input required by
Paper3's modewise stability predicate. -/
theorem UnitIntervalLinearMassSpectralGap.linearlyStable
    {p : CM2Params} {uStar vStar rate : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar rate) :
    LinearlyStable unitIntervalNeumannSpectrum p uStar vStar := by
  intro n hn
  have hmode :
      sigma p uStar vStar (unitIntervalNeumannSpectrum.eigenvalue n) ≤
        -rate :=
    hgap.2 n hn
  exact lt_of_le_of_lt hmode (by linarith [hgap.1])

/-- For nonpositive sensitivity, the linearized Paper3 growth rate is bounded
above by the logistic damping rate. -/
theorem sigma_le_neg_logisticDamping_of_chi_nonpos
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hχ : p.χ₀ ≤ 0) (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar)
    (hlambda : 0 ≤ lambdaN) :
    sigma p uStar vStar lambdaN ≤ -p.a * p.α := by
  have hden_pos :
      0 < (1 + vStar) ^ p.β * (p.μ + lambdaN) := by
    exact mul_pos
      (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
      (by linarith [p.hμ])
  have hfrac_nonneg :
      0 ≤
        (uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN)) := by
    exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg huStar _) hlambda)
      hden_pos.le
  have hchem_nonpos :
      p.χ₀ * p.ν * p.γ *
        ((uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN))) ≤ 0 := by
    have hcoef_nonneg :
        0 ≤ p.ν * p.γ *
          ((uStar ^ (p.m + p.γ - 1) * lambdaN) /
            ((1 + vStar) ^ p.β * (p.μ + lambdaN))) := by
      exact mul_nonneg (mul_pos p.hν p.hγ).le hfrac_nonneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hχ hcoef_nonneg]
  have hchem_nonpos' :
      p.χ₀ * p.ν * p.γ * (uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN)) ≤ 0 := by
    convert hchem_nonpos using 1
    ring
  unfold sigma
  nlinarith [hlambda, hchem_nonpos']

/-- If the logistic damping coefficient is zero and the sensitivity is
nonpositive, the linearized growth is bounded above by the Neumann diffusion
rate. -/
theorem sigma_le_neg_lambda_of_chi_nonpos_a_eq_zero
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0)
    (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar)
    (hlambda : 0 ≤ lambdaN) :
    sigma p uStar vStar lambdaN ≤ -lambdaN := by
  have hden_pos :
      0 < (1 + vStar) ^ p.β * (p.μ + lambdaN) := by
    exact mul_pos
      (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
      (by linarith [p.hμ])
  have hfrac_nonneg :
      0 ≤
        (uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN)) := by
    exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg huStar _) hlambda)
      hden_pos.le
  have hchem_nonpos :
      p.χ₀ * p.ν * p.γ *
        ((uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN))) ≤ 0 := by
    have hcoef_nonneg :
        0 ≤ p.ν * p.γ *
          ((uStar ^ (p.m + p.γ - 1) * lambdaN) /
            ((1 + vStar) ^ p.β * (p.μ + lambdaN))) := by
      exact mul_nonneg (mul_pos p.hν p.hγ).le hfrac_nonneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hχ hcoef_nonneg]
  have hchem_nonpos' :
      p.χ₀ * p.ν * p.γ * (uStar ^ (p.m + p.γ - 1) * lambdaN) /
          ((1 + vStar) ^ p.β * (p.μ + lambdaN)) ≤ 0 := by
    convert hchem_nonpos using 1
    ring
  unfold sigma
  rw [ha]
  nlinarith [hchem_nonpos']

/-- Nonpositive sensitivity with positive logistic damping gives a uniform
spectral gap for all unit-interval Neumann modes. -/
theorem UnitIntervalLinearSpectralGap.of_chi_nonpos_a_pos
    (p : CM2Params) {uStar vStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a)
    (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar) :
    UnitIntervalLinearSpectralGap p uStar vStar (p.a * p.α) := by
  refine ⟨mul_pos ha p.hα, ?_⟩
  intro n
  calc
    unitIntervalLinearizedGrowth p uStar vStar n
        =
          sigma p uStar vStar
            (unitIntervalNeumannSpectrum.eigenvalue n) := rfl
    _ ≤ -p.a * p.α :=
          sigma_le_neg_logisticDamping_of_chi_nonpos
            p hχ huStar hvStar
            (unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n)
    _ = -(p.a * p.α) := by ring

/-- Positive-equilibrium nonpositive-sensitivity branch: the uniform spectral
gap is the logistic damping rate. -/
theorem positiveEquilibrium_UnitIntervalLinearSpectralGap_of_chi_nonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    UnitIntervalLinearSpectralGap p eq.1 eq.2 (p.a * p.α) := by
  dsimp
  exact UnitIntervalLinearSpectralGap.of_chi_nonpos_a_pos
    p hχ ha
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le

/-- Nonpositive-sensitivity minimal branch: after removing the neutral
constant mode, the unit-interval linearization has the Neumann first-mode gap. -/
theorem UnitIntervalLinearMassSpectralGap.of_chi_nonpos_a_eq_zero
    (p : CM2Params) {uStar vStar : ℝ}
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0)
    (huStar : 0 ≤ uStar) (hvStar : 0 ≤ vStar) :
    UnitIntervalLinearMassSpectralGap p uStar vStar
      unitIntervalNeumannSpectrum.firstNonzero := by
  refine ⟨unitIntervalNeumannSpectrum_hasNeumannSpectrum.firstNonzero_pos, ?_⟩
  intro n hn
  calc
    unitIntervalLinearizedGrowth p uStar vStar n
        =
          sigma p uStar vStar
            (unitIntervalNeumannSpectrum.eigenvalue n) := rfl
    _ ≤ -unitIntervalNeumannSpectrum.eigenvalue n :=
          sigma_le_neg_lambda_of_chi_nonpos_a_eq_zero
            p hχ ha huStar hvStar
            (unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n)
    _ ≤ -unitIntervalNeumannSpectrum.firstNonzero := by
          have H := unitIntervalNeumannSpectrum_hasNeumannSpectrum
          have hle := H.firstNonzero_le_eigenvalue n hn
          linarith

/-- Minimal-equilibrium nonpositive-sensitivity branch: the nonzero modes have
the first Neumann spectral gap. -/
theorem minimalEquilibrium_UnitIntervalLinearMassSpectralGap_of_chi_nonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : p.a = 0)
    {uStar : ℝ} (huStar : 0 < uStar) :
    let eq := minimalEquilibrium p uStar
    UnitIntervalLinearMassSpectralGap p eq.1 eq.2
      unitIntervalNeumannSpectrum.firstNonzero := by
  dsimp
  exact UnitIntervalLinearMassSpectralGap.of_chi_nonpos_a_eq_zero
    p hχ ha huStar.le
    (minimalEquilibrium_snd_pos p huStar).le

/-- A spectral gap gives coefficient-energy exponential decay. -/
theorem unitIntervalLinearizedSemigroup_l2_energy_decay
    {p : CM2Params} {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a) ≤
      (Real.exp (-(rate * t))) ^ 2 * coeffL2Energy a := by
  have hgrowth :
      ∀ n : ℕ,
        unitIntervalLinearizedGrowth p uStar vStar n ≤ -rate :=
    hgap.2
  have h :=
    diagonalSemigroupCoeff_l2_energy_le_of_growth_le
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgrowth ha
  simpa [mul_comm] using h

/-- A spectral gap gives coefficient-norm exponential decay. -/
theorem unitIntervalLinearizedSemigroup_l2_norm_decay
    {p : CM2Params} {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a) ≤
      Real.exp (-(rate * t)) * coeffL2Norm a := by
  have hgrowth :
      ∀ n : ℕ,
        unitIntervalLinearizedGrowth p uStar vStar n ≤ -rate :=
    hgap.2
  have h :=
    diagonalSemigroupCoeff_l2_norm_le_of_growth_le
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgrowth ha
  simpa [mul_comm] using h

/-- A spectral gap gives reconstructed interval `L²` exponential decay. -/
theorem unitIntervalLinearizedSemigroupLp_norm_sq_decay
    {p : CM2Params} {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖cosineLpFromCoeffs
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a)
        (diagonalSemigroupCoeff_l2_summable_of_growth_le
          (growth := unitIntervalLinearizedGrowth p uStar vStar)
          (omega := -rate) ht hgap.2 ha)‖ ^ 2 ≤
      (Real.exp (-(rate * t))) ^ 2 * coeffL2Energy a := by
  have h :=
    diagonalSemigroupLp_norm_sq_le_of_growth_le
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgap.2 ha
  simpa [mul_comm] using h

/-- A spectral gap gives reconstructed interval `L²` norm exponential decay. -/
theorem unitIntervalLinearizedSemigroupLp_norm_decay
    {p : CM2Params} {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    ‖cosineLpFromCoeffs
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a)
        (diagonalSemigroupCoeff_l2_summable_of_growth_le
          (growth := unitIntervalLinearizedGrowth p uStar vStar)
          (omega := -rate) ht hgap.2 ha)‖ ≤
      Real.exp (-(rate * t)) * coeffL2Norm a := by
  have h :=
    diagonalSemigroupLp_norm_le_of_growth_le
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgap.2 ha
  simpa [mul_comm] using h

/-- A nonzero-mode spectral gap gives coefficient-energy exponential decay
for zero-mode-free coefficient data. -/
theorem unitIntervalLinearizedMassSemigroup_l2_energy_decay
    {p : CM2Params} {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Energy
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a) ≤
      (Real.exp (-(rate * t))) ^ 2 * coeffL2Energy a := by
  have hgrowth :
      ∀ n : ℕ, n ≠ 0 →
        unitIntervalLinearizedGrowth p uStar vStar n ≤ -rate :=
    hgap.2
  have h :=
    diagonalSemigroupCoeff_l2_energy_le_of_growth_le_on_nonzero
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgrowth ha ha0
  simpa [mul_comm] using h

/-- A nonzero-mode spectral gap gives coefficient-norm exponential decay for
zero-mode-free coefficient data. -/
theorem unitIntervalLinearizedMassSemigroup_l2_norm_decay
    {p : CM2Params} {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Norm
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a) ≤
      Real.exp (-(rate * t)) * coeffL2Norm a := by
  have hgrowth :
      ∀ n : ℕ, n ≠ 0 →
        unitIntervalLinearizedGrowth p uStar vStar n ≤ -rate :=
    hgap.2
  have h :=
    diagonalSemigroupCoeff_l2_norm_le_of_growth_le_on_nonzero
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgrowth ha ha0
  simpa [mul_comm] using h

/-- A nonzero-mode spectral gap gives reconstructed interval `L²` exponential
decay for zero-mode-free coefficient data. -/
theorem unitIntervalLinearizedMassSemigroupLp_norm_sq_decay
    {p : CM2Params} {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    ‖cosineLpFromCoeffs
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a)
        (diagonalSemigroupCoeff_l2_summable_of_growth_le_on_nonzero
          (growth := unitIntervalLinearizedGrowth p uStar vStar)
          (omega := -rate) ht hgap.2 ha ha0)‖ ^ 2 ≤
      (Real.exp (-(rate * t))) ^ 2 * coeffL2Energy a := by
  have h :=
    diagonalSemigroupLp_norm_sq_le_of_growth_le_on_nonzero
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgap.2 ha ha0
  simpa [mul_comm] using h

/-- A nonzero-mode spectral gap gives reconstructed interval `L²` norm
exponential decay for zero-mode-free coefficient data. -/
theorem unitIntervalLinearizedMassSemigroupLp_norm_decay
    {p : CM2Params} {uStar vStar rate t : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar rate)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    ‖cosineLpFromCoeffs
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a)
        (diagonalSemigroupCoeff_l2_summable_of_growth_le_on_nonzero
          (growth := unitIntervalLinearizedGrowth p uStar vStar)
          (omega := -rate) ht hgap.2 ha ha0)‖ ≤
      Real.exp (-(rate * t)) * coeffL2Norm a := by
  have h :=
    diagonalSemigroupLp_norm_le_of_growth_le_on_nonzero
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (omega := -rate) ht hgap.2 ha ha0
  simpa [mul_comm] using h

/-- A spectral bound gives the real resolvent estimate for the unit-interval
linearized operator. -/
theorem unitIntervalLinearizedResolvent_l2_energy_le
    {p : CM2Params} {uStar vStar omega z : ℝ}
    (hbound : UnitIntervalLinearSpectralBound p uStar vStar omega)
    (hz : omega < z) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Energy
        (diagonalResolventCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) z a) ≤
      ((z - omega)⁻¹) ^ 2 * coeffL2Energy a :=
  diagonalResolventCoeff_l2_energy_le_of_growth_le
    (growth := unitIntervalLinearizedGrowth p uStar vStar)
    (omega := omega) hz hbound ha

/-- A spectral bound gives the real resolvent norm estimate for the
unit-interval linearized operator. -/
theorem unitIntervalLinearizedResolvent_l2_norm_le
    {p : CM2Params} {uStar vStar omega z : ℝ}
    (hbound : UnitIntervalLinearSpectralBound p uStar vStar omega)
    (hz : omega < z) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm
        (diagonalResolventCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) z a) ≤
      (z - omega)⁻¹ * coeffL2Norm a :=
  diagonalResolventCoeff_l2_norm_le_of_growth_le
    (growth := unitIntervalLinearizedGrowth p uStar vStar)
    (omega := omega) hz hbound ha

/-- A nonzero-mode spectral bound gives the real resolvent estimate for
zero-mode-free coefficient data. -/
theorem unitIntervalLinearizedMassResolvent_l2_energy_le
    {p : CM2Params} {uStar vStar omega z : ℝ}
    (hbound : UnitIntervalLinearMassSpectralBound p uStar vStar omega)
    (hz : omega < z) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Energy
        (diagonalResolventCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) z a) ≤
      ((z - omega)⁻¹) ^ 2 * coeffL2Energy a :=
  diagonalResolventCoeff_l2_energy_le_of_growth_le_on_nonzero
    (growth := unitIntervalLinearizedGrowth p uStar vStar)
    (omega := omega) hz hbound ha ha0

/-- A nonzero-mode spectral bound gives the real resolvent norm estimate for
zero-mode-free coefficient data. -/
theorem unitIntervalLinearizedMassResolvent_l2_norm_le
    {p : CM2Params} {uStar vStar omega z : ℝ}
    (hbound : UnitIntervalLinearMassSpectralBound p uStar vStar omega)
    (hz : omega < z) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) (ha0 : a 0 = 0) :
    coeffL2Norm
        (diagonalResolventCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) z a) ≤
      (z - omega)⁻¹ * coeffL2Norm a :=
  diagonalResolventCoeff_l2_norm_le_of_growth_le_on_nonzero
    (growth := unitIntervalLinearizedGrowth p uStar vStar)
    (omega := omega) hz hbound ha ha0

end ShenWork.PDE.SectorialOperator

end
