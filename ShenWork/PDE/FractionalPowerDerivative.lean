import ShenWork.PDE.FractionalPowerSpace

/-!
  One-derivative coefficient estimates for the spectral fractional-power
  space on an interval.

  This file keeps the derivative side of the H3.1 `X^σ -> C¹` bridge separate
  from `FractionalPowerSpace.lean`, which also carries Paper3 target wrappers.
-/

noncomputable section

namespace ShenWork.PDE.FractionalPower

/-- Neumann frequency `nπ/L`; its square is `neumannEigenvalue`. -/
def neumannFrequency (L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.pi / L

/-- Absolute coefficient weight for one spatial derivative. -/
def derivativeCoeffNorm (L : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  |neumannFrequency L n| * ‖a n‖

theorem neumannEigenvalue_eq_neumannFrequency_sq (L : ℝ) (n : ℕ) :
    neumannEigenvalue L n = neumannFrequency L n ^ 2 := by
  rfl

theorem derivativeCoeffNorm_nonneg (L : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    0 ≤ derivativeCoeffNorm L a n := by
  exact mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem sqrt_fractionalPowerEnergy_mul_sqrt_derivativeReciprocal_eq_derivativeCoeffNorm
    (L sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    Real.sqrt (fractionalPowerEnergyTerm L sigma a n) *
        Real.sqrt (derivativeReciprocalFractionalPowerWeight L sigma n) =
      derivativeCoeffNorm L a n := by
  have henergy_nonneg :
      0 ≤ fractionalPowerEnergyTerm L sigma a n :=
    fractionalPowerEnergyTerm_nonneg L sigma a n
  rw [← Real.sqrt_mul henergy_nonneg]
  have hprod :
      fractionalPowerEnergyTerm L sigma a n *
          derivativeReciprocalFractionalPowerWeight L sigma n =
        (neumannFrequency L n * ‖a n‖) ^ 2 := by
    have hwpos : 0 < fractionalPowerWeight L sigma n :=
      fractionalPowerWeight_pos L sigma n
    dsimp [fractionalPowerEnergyTerm,
      derivativeReciprocalFractionalPowerWeight,
      reciprocalFractionalPowerWeight, neumannFrequency, neumannEigenvalue]
    field_simp [hwpos.ne']
  rw [hprod, Real.sqrt_sq_eq_abs, derivativeCoeffNorm]
  rw [abs_mul, abs_of_nonneg (norm_nonneg (a n))]

/-- Cauchy-Schwarz derivative version: weighted `ℓ²` coefficients and the
one-derivative reciprocal trace control absolute derivative coefficients. -/
theorem summable_and_tsum_derivativeCoeffNorm_le_energy_mul_derivativeTrace
    {L sigma : ℝ} (a : ℕ → ℂ)
    (henergy : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n)
    (htrace :
      Summable fun n : ℕ =>
        derivativeReciprocalFractionalPowerWeight L sigma n) :
    (Summable fun n : ℕ => derivativeCoeffNorm L a n) ∧
      (∑' n : ℕ, derivativeCoeffNorm L a n) ≤
        (∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n) ^
            (1 / (2 : ℝ)) *
          (∑' n : ℕ,
              derivativeReciprocalFractionalPowerWeight L sigma n) ^
            (1 / (2 : ℝ)) := by
  let f : ℕ → ℝ := fun n =>
    Real.sqrt (fractionalPowerEnergyTerm L sigma a n)
  let g : ℕ → ℝ := fun n =>
    Real.sqrt (derivativeReciprocalFractionalPowerWeight L sigma n)
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => Real.sqrt_nonneg _
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => Real.sqrt_nonneg _
  have hf_sum : Summable fun n : ℕ => f n ^ (2 : ℝ) := by
    dsimp [f]
    convert henergy using 1
    ext n
    rw [Real.rpow_two,
      Real.sq_sqrt (fractionalPowerEnergyTerm_nonneg L sigma a n)]
  have hg_sum : Summable fun n : ℕ => g n ^ (2 : ℝ) := by
    dsimp [g]
    convert htrace using 1
    ext n
    rw [Real.rpow_two,
      Real.sq_sqrt
        (derivativeReciprocalFractionalPowerWeight_nonneg L sigma n)]
  have hholder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hf_nonneg hg_nonneg hf_sum hg_sum
  constructor
  · dsimp [f, g] at hholder
    simpa
      [sqrt_fractionalPowerEnergy_mul_sqrt_derivativeReciprocal_eq_derivativeCoeffNorm]
      using hholder.1
  · dsimp [f, g] at hholder
    simpa
      [sqrt_fractionalPowerEnergy_mul_sqrt_derivativeReciprocal_eq_derivativeCoeffNorm,
        Real.rpow_two, Real.sq_sqrt, fractionalPowerEnergyTerm_nonneg,
        derivativeReciprocalFractionalPowerWeight_nonneg]
      using hholder.2

theorem derivativeCoeffNorm_summable_of_derivative_trace
    {L sigma : ℝ} (a : ℕ → ℂ)
    (henergy : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n)
    (htrace :
      Summable fun n : ℕ =>
        derivativeReciprocalFractionalPowerWeight L sigma n) :
    Summable fun n : ℕ => derivativeCoeffNorm L a n :=
  (summable_and_tsum_derivativeCoeffNorm_le_energy_mul_derivativeTrace
    (L := L) (sigma := sigma) a henergy htrace).1

theorem tsum_derivativeCoeffNorm_le_energy_mul_derivativeTrace
    {L sigma : ℝ} (a : ℕ → ℂ)
    (henergy : Summable fun n : ℕ => fractionalPowerEnergyTerm L sigma a n)
    (htrace :
      Summable fun n : ℕ =>
        derivativeReciprocalFractionalPowerWeight L sigma n) :
    (∑' n : ℕ, derivativeCoeffNorm L a n) ≤
      (∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n) ^
          (1 / (2 : ℝ)) *
        (∑' n : ℕ,
            derivativeReciprocalFractionalPowerWeight L sigma n) ^
          (1 / (2 : ℝ)) :=
  (summable_and_tsum_derivativeCoeffNorm_le_energy_mul_derivativeTrace
    (L := L) (sigma := sigma) a henergy htrace).2

theorem FractionalPowerSpace.derivativeCoeffNorm_summable_of_derivative_trace
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (htrace :
      Summable fun n : ℕ =>
        derivativeReciprocalFractionalPowerWeight L sigma n) :
    Summable fun n : ℕ => derivativeCoeffNorm L (u : ℕ → ℂ) n :=
  _root_.ShenWork.PDE.FractionalPower.derivativeCoeffNorm_summable_of_derivative_trace
    (L := L) (sigma := sigma) (u : ℕ → ℂ) u.property htrace

theorem FractionalPowerSpace.derivativeCoeffNorm_summable_of_sigma_gt_three_quarters
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (hL : 0 < L) (hsigma : 3 / 4 < sigma) :
    Summable fun n : ℕ => derivativeCoeffNorm L (u : ℕ → ℂ) n :=
  u.derivativeCoeffNorm_summable_of_derivative_trace
    (derivativeReciprocalFractionalPowerWeight_summable_of_sigma_gt_three_quarters
      (L := L) (sigma := sigma) hL hsigma)

theorem FractionalPowerSpace.tsum_derivativeCoeffNorm_le_energy_derivativeTrace
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (htrace :
      Summable fun n : ℕ =>
        derivativeReciprocalFractionalPowerWeight L sigma n) :
    (∑' n : ℕ, derivativeCoeffNorm L (u : ℕ → ℂ) n) ≤
      (∑' n : ℕ,
          fractionalPowerEnergyTerm L sigma (u : ℕ → ℂ) n) ^
          (1 / (2 : ℝ)) *
        (∑' n : ℕ,
            derivativeReciprocalFractionalPowerWeight L sigma n) ^
          (1 / (2 : ℝ)) :=
  tsum_derivativeCoeffNorm_le_energy_mul_derivativeTrace
    (L := L) (sigma := sigma) (u : ℕ → ℂ) u.property htrace

theorem FractionalPowerSpace.tsum_derivativeCoeffNorm_le_energy_trace_of_sigma_gt_three_quarters
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (hL : 0 < L) (hsigma : 3 / 4 < sigma) :
    (∑' n : ℕ, derivativeCoeffNorm L (u : ℕ → ℂ) n) ≤
      (∑' n : ℕ,
          fractionalPowerEnergyTerm L sigma (u : ℕ → ℂ) n) ^
          (1 / (2 : ℝ)) *
        (∑' n : ℕ,
            derivativeReciprocalFractionalPowerWeight L sigma n) ^
          (1 / (2 : ℝ)) :=
  u.tsum_derivativeCoeffNorm_le_energy_derivativeTrace
    (derivativeReciprocalFractionalPowerWeight_summable_of_sigma_gt_three_quarters
      (L := L) (sigma := sigma) hL hsigma)

/-- Formal derivative of the `n`-th cosine-series term. -/
def cosineSeriesDerivativeTerm
    (L : ℝ) (a : ℕ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  a n *
    (((-(neumannFrequency L n * Real.sin (neumannFrequency L n * x))) : ℝ) : ℂ)

/-- Candidate derivative series for a cosine-series representative. -/
def cosineSeriesDerivative (L : ℝ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, cosineSeriesDerivativeTerm L a n x

theorem norm_cosineSeriesDerivativeTerm_le_derivativeCoeffNorm
    (L : ℝ) (a : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    ‖cosineSeriesDerivativeTerm L a n x‖ ≤ derivativeCoeffNorm L a n := by
  let k : ℝ := neumannFrequency L n
  calc
    ‖cosineSeriesDerivativeTerm L a n x‖
        = ‖a n‖ * (|k| * |Real.sin (k * x)|) := by
          dsimp [cosineSeriesDerivativeTerm, k]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul]
    _ ≤ ‖a n‖ * (|k| * 1) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (k * x))
              (abs_nonneg k))
            (norm_nonneg (a n))
    _ = derivativeCoeffNorm L a n := by
          dsimp [derivativeCoeffNorm, k]
          ring

theorem cosineSeriesDerivativeTerm_summable_of_derivativeCoeffNorm_summable
    {L : ℝ} {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => derivativeCoeffNorm L a n) (x : ℝ) :
    Summable fun n : ℕ => cosineSeriesDerivativeTerm L a n x :=
  Summable.of_norm_bounded ha fun n =>
    norm_cosineSeriesDerivativeTerm_le_derivativeCoeffNorm L a n x

theorem norm_cosineSeriesDerivative_le_tsum_derivativeCoeffNorm_of_summable
    {L : ℝ} {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => derivativeCoeffNorm L a n) (x : ℝ) :
    ‖cosineSeriesDerivative L a x‖ ≤
      ∑' n : ℕ, derivativeCoeffNorm L a n := by
  have hsum := cosineSeriesDerivativeTerm_summable_of_derivativeCoeffNorm_summable
    (L := L) (a := a) ha x
  exact hsum.hasSum.norm_le_of_bounded ha.hasSum
    (fun n => norm_cosineSeriesDerivativeTerm_le_derivativeCoeffNorm L a n x)

theorem continuous_cosineSeriesDerivativeTerm
    (L : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    Continuous fun x : ℝ => cosineSeriesDerivativeTerm L a n x := by
  unfold cosineSeriesDerivativeTerm
  fun_prop

theorem cosineSeriesDerivative_continuous_of_derivativeCoeffNorm_summable
    {L : ℝ} {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => derivativeCoeffNorm L a n) :
    Continuous fun x : ℝ => cosineSeriesDerivative L a x := by
  unfold cosineSeriesDerivative
  exact continuous_tsum
    (fun n => continuous_cosineSeriesDerivativeTerm L a n)
    ha
    (fun n x => norm_cosineSeriesDerivativeTerm_le_derivativeCoeffNorm L a n x)

theorem FractionalPowerSpace.continuous_cosineSeriesDerivative_of_sigma_gt_three_quarters
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (hL : 0 < L) (hsigma : 3 / 4 < sigma) :
    Continuous fun x : ℝ => cosineSeriesDerivative L (u : ℕ → ℂ) x :=
  cosineSeriesDerivative_continuous_of_derivativeCoeffNorm_summable
    (u.derivativeCoeffNorm_summable_of_sigma_gt_three_quarters hL hsigma)

theorem FractionalPowerSpace.norm_cosineSeriesDerivative_le_energy_trace_of_sigma_gt_three_quarters
    {L sigma : ℝ} (u : FractionalPowerSpace L sigma)
    (hL : 0 < L) (hsigma : 3 / 4 < sigma) (x : ℝ) :
    ‖cosineSeriesDerivative L (u : ℕ → ℂ) x‖ ≤
      (∑' n : ℕ,
          fractionalPowerEnergyTerm L sigma (u : ℕ → ℂ) n) ^
          (1 / (2 : ℝ)) *
        (∑' n : ℕ,
            derivativeReciprocalFractionalPowerWeight L sigma n) ^
          (1 / (2 : ℝ)) := by
  have htrace :=
    derivativeReciprocalFractionalPowerWeight_summable_of_sigma_gt_three_quarters
      (L := L) (sigma := sigma) hL hsigma
  exact
    (norm_cosineSeriesDerivative_le_tsum_derivativeCoeffNorm_of_summable
      (u.derivativeCoeffNorm_summable_of_derivative_trace htrace) x).trans
      (u.tsum_derivativeCoeffNorm_le_energy_derivativeTrace htrace)

end ShenWork.PDE.FractionalPower
