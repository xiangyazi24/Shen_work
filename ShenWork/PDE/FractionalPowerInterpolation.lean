/- Interpolation in the weighted Neumann coefficient realization. -/
import ShenWork.PDE.WeightedCoefficientSpace
import ShenWork.PDE.SectorialOperator
import Mathlib.Analysis.MeanInequalities

namespace ShenWork.PDE

open FractionalPower
open SectorialOperator

noncomputable section

/-- Pointwise factorization behind interpolation between the unweighted
coefficient norm and `X^rho`. -/
theorem fractionalPowerEnergyTerm_interpolation_factorization
    {L sigma rho : ℝ} (hsigma : 0 < sigma) (hsigmaRho : sigma < rho)
    (a : ℕ → ℂ) (n : ℕ) :
    fractionalPowerEnergyTerm L sigma a n =
      (‖a n‖ ^ 2) ^ (1 - sigma / rho) *
        (fractionalPowerEnergyTerm L rho a n) ^ (sigma / rho) := by
  have hrho : 0 < rho := lt_trans hsigma hsigmaRho
  let theta : ℝ := sigma / rho
  have htheta0 : 0 < theta := div_pos hsigma hrho
  have htheta1 : theta < 1 := (div_lt_one hrho).2 hsigmaRho
  have hthetaLe : theta ≤ 1 := htheta1.le
  have honeTheta : 0 ≤ 1 - theta := sub_nonneg.mpr hthetaLe
  let base : ℝ := 1 + neumannEigenvalue L n
  let w : ℝ := ‖a n‖ ^ 2
  have hbase : 0 < base := by
    simpa [base] using one_add_neumannEigenvalue_pos L n
  have hw : 0 ≤ w := sq_nonneg _
  have hweight : 0 ≤ base ^ (2 * rho) := Real.rpow_nonneg hbase.le _
  have hthetaEq : 2 * rho * theta = 2 * sigma := by
    dsimp [theta]
    field_simp [hrho.ne']
  have hwSplit : w = w ^ (1 - theta) * w ^ theta := by
    rw [← Real.rpow_add_of_nonneg hw honeTheta htheta0.le]
    norm_num
  unfold fractionalPowerEnergyTerm fractionalPowerWeight
  change base ^ (2 * sigma) * w =
    w ^ (1 - theta) * (base ^ (2 * rho) * w) ^ theta
  rw [Real.mul_rpow hweight hw]
  rw [← Real.rpow_mul hbase.le]
  rw [hthetaEq]
  calc
    base ^ (2 * sigma) * w =
        base ^ (2 * sigma) * (w ^ (1 - theta) * w ^ theta) := by
      rw [← hwSplit]
    _ = w ^ (1 - theta) * (base ^ (2 * sigma) * w ^ theta) := by ring

/-- Hilbert-scale interpolation in energy form.  Both membership and the
quantitative estimate are included so a finite-looking `tsum` cannot hide a
non-summable target family. -/
theorem fractionalPowerEnergy_interpolation
    {L sigma rho : ℝ} (hsigma : 0 < sigma) (hsigmaRho : sigma < rho)
    {a : ℕ → ℂ}
    (ha0 : Summable fun n : ℕ => ‖a n‖ ^ 2)
    (haRho : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L rho a n) :
    Summable (fun n : ℕ => fractionalPowerEnergyTerm L sigma a n) ∧
      (∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n) ≤
        coeffL2Energy a ^ (1 - sigma / rho) *
          (∑' n : ℕ, fractionalPowerEnergyTerm L rho a n) ^
            (sigma / rho) := by
  have hrho : 0 < rho := lt_trans hsigma hsigmaRho
  let theta : ℝ := sigma / rho
  have htheta0 : 0 < theta := div_pos hsigma hrho
  have htheta1 : theta < 1 := (div_lt_one hrho).2 hsigmaRho
  have honeTheta : 0 < 1 - theta := sub_pos.mpr htheta1
  let f : ℕ → ℝ := fun n => (‖a n‖ ^ 2) ^ (1 - theta)
  let g : ℕ → ℝ := fun n =>
    (fractionalPowerEnergyTerm L rho a n) ^ theta
  have hf0 : ∀ n, 0 ≤ f n := fun n => Real.rpow_nonneg (sq_nonneg _) _
  have hg0 : ∀ n, 0 ≤ g n := fun n =>
    Real.rpow_nonneg (fractionalPowerEnergyTerm_nonneg L rho a n) _
  have hpq : (1 - theta)⁻¹.HolderConjugate theta⁻¹ :=
    Real.HolderConjugate.one_sub_inv_inv htheta0 htheta1
  have hfPow : (fun n => f n ^ (1 - theta)⁻¹) =
      fun n => ‖a n‖ ^ 2 := by
    funext n
    dsimp [f]
    rw [← Real.rpow_mul (sq_nonneg _)]
    have hprod : (1 - theta) * (1 - theta)⁻¹ = 1 :=
      mul_inv_cancel₀ honeTheta.ne'
    rw [hprod, Real.rpow_one]
  have hgPow : (fun n => g n ^ theta⁻¹) =
      fun n => fractionalPowerEnergyTerm L rho a n := by
    funext n
    dsimp [g]
    rw [← Real.rpow_mul (fractionalPowerEnergyTerm_nonneg L rho a n)]
    rw [mul_inv_cancel₀ htheta0.ne', Real.rpow_one]
  have hfSum : Summable fun n => f n ^ (1 - theta)⁻¹ := by
    rw [hfPow]
    exact ha0
  have hgSum : Summable fun n => g n ^ theta⁻¹ := by
    rw [hgPow]
    exact haRho
  have hholder :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
      hpq hf0 hg0 hfSum hgSum
  have hfg : (fun n => f n * g n) =
      fun n => fractionalPowerEnergyTerm L sigma a n := by
    funext n
    dsimp [f, g, theta]
    exact (fractionalPowerEnergyTerm_interpolation_factorization
      hsigma hsigmaRho a n).symm
  constructor
  · rw [← hfg]
    exact hholder.1
  · rw [← hfg]
    calc
      (∑' n : ℕ, f n * g n) ≤
          (∑' n : ℕ, f n ^ (1 - theta)⁻¹) ^
              (1 / (1 - theta)⁻¹) *
            (∑' n : ℕ, g n ^ theta⁻¹) ^ (1 / theta⁻¹) := hholder.2
      _ = coeffL2Energy a ^ (1 - sigma / rho) *
          (∑' n : ℕ, fractionalPowerEnergyTerm L rho a n) ^
            (sigma / rho) := by
        rw [hfPow, hgPow]
        simp only [one_div, inv_inv]
        rfl

/-- Norm form of fractional-power interpolation. -/
theorem fractionalPowerNorm_interpolation
    {L sigma rho : ℝ} (hsigma : 0 < sigma) (hsigmaRho : sigma < rho)
    {a : ℕ → ℂ}
    (ha0 : Summable fun n : ℕ => ‖a n‖ ^ 2)
    (haRho : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm L rho a n) :
    Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n) ≤
      coeffL2Norm a ^ (1 - sigma / rho) *
        (Real.sqrt (∑' n : ℕ,
          fractionalPowerEnergyTerm L rho a n)) ^ (sigma / rho) := by
  have henergy :=
    (fractionalPowerEnergy_interpolation hsigma hsigmaRho ha0 haRho).2
  have hzero : 0 ≤ coeffL2Energy a := coeffL2Energy_nonneg a
  have hrhoZero : 0 ≤ ∑' n : ℕ, fractionalPowerEnergyTerm L rho a n :=
    tsum_nonneg fun n => fractionalPowerEnergyTerm_nonneg L rho a n
  have hrhs : 0 ≤ coeffL2Energy a ^ (1 - sigma / rho) *
      (∑' n : ℕ, fractionalPowerEnergyTerm L rho a n) ^
        (sigma / rho) := mul_nonneg (Real.rpow_nonneg hzero _)
          (Real.rpow_nonneg hrhoZero _)
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hsqrt_rpow : ∀ x r : ℝ, 0 ≤ x →
      Real.sqrt (x ^ r) = (Real.sqrt x) ^ r := by
    intro x r hx
    calc
      Real.sqrt (x ^ r) = (x ^ r) ^ (1 / (2 : ℝ)) :=
        Real.sqrt_eq_rpow _
      _ = x ^ (r * (1 / (2 : ℝ))) :=
        (Real.rpow_mul hx r (1 / (2 : ℝ))).symm
      _ = x ^ (r / 2) := by congr 1; ring
      _ = (Real.sqrt x) ^ r := Real.rpow_div_two_eq_sqrt r hx
  calc
    Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm L sigma a n) ≤
        Real.sqrt (coeffL2Energy a ^ (1 - sigma / rho) *
          (∑' n : ℕ, fractionalPowerEnergyTerm L rho a n) ^
            (sigma / rho)) := hsqrt
    _ = coeffL2Norm a ^ (1 - sigma / rho) *
        (Real.sqrt (∑' n : ℕ,
          fractionalPowerEnergyTerm L rho a n)) ^ (sigma / rho) := by
      rw [Real.sqrt_mul (Real.rpow_nonneg hzero _)]
      unfold coeffL2Norm
      rw [hsqrt_rpow _ _ hzero, hsqrt_rpow _ _ hrhoZero]

#print axioms fractionalPowerEnergyTerm_interpolation_factorization
#print axioms fractionalPowerEnergy_interpolation
#print axioms fractionalPowerNorm_interpolation

end

end ShenWork.PDE
