/- Strong-norm form of the full diagonal smoothing estimate. -/
import ShenWork.Paper3.IntervalDomainLinearizedEnergy

namespace ShenWork.Paper3

open ShenWork.PDE.SectorialOperator
open ShenWork.PDE.FractionalPower

noncomputable section

/-- The base fractional energy is exactly the unweighted coefficient energy. -/
theorem unitInterval_fractionalPowerEnergy_zero_eq_coeffL2Energy
    (a : ℕ → ℂ) :
    (∑' n : ℕ, fractionalPowerEnergyTerm 1 0 a n) =
      coeffL2Energy a := by
  unfold coeffL2Energy
  apply tsum_congr
  intro n
  simp [fractionalPowerEnergyTerm, fractionalPowerWeight]

/-- The explicit constant left after separating the singular time power from
the full-mode semigroup estimate. -/
def unitIntervalLinearizedStrongSmoothingConstant
    (p : CM2Params) (uStar vStar gap sigma : ℝ) : ℝ :=
  let B := |p.χ₀ * p.ν * p.γ *
      uStar ^ (p.m + p.γ - 1) / (1 + vStar) ^ p.β| + 1
  (sigma / (Real.exp 1 * (gap / (2 * (gap + B))))) ^ sigma

theorem unitIntervalLinearizedStrongSmoothingConstant_pos
    (p : CM2Params) {uStar vStar gap sigma : ℝ}
    (hgap : 0 < gap) (hsigma : 0 < sigma) :
    0 < unitIntervalLinearizedStrongSmoothingConstant
      p uStar vStar gap sigma := by
  let B := |p.χ₀ * p.ν * p.γ *
      uStar ^ (p.m + p.γ - 1) / (1 + vStar) ^ p.β| + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have heta : 0 < gap / (2 * (gap + B)) := by positivity
  unfold unitIntervalLinearizedStrongSmoothingConstant
  dsimp only
  exact Real.rpow_pos_of_pos (div_pos hsigma (mul_pos (Real.exp_pos _) heta)) _

theorem unitIntervalLinearized_smoothing_factor_eq
    (p : CM2Params) {uStar vStar gap sigma t : ℝ}
    (hgap : 0 < gap) (hsigma : 0 < sigma) (ht : 0 < t) :
    (sigma /
        (Real.exp 1 *
          ((gap /
            (2 *
              (gap +
                (|p.χ₀ * p.ν * p.γ *
                    uStar ^ (p.m + p.γ - 1) /
                  (1 + vStar) ^ p.β| + 1)))) * t))) ^ sigma =
      unitIntervalLinearizedStrongSmoothingConstant
          p uStar vStar gap sigma * t ^ (-sigma) := by
  let B := |p.χ₀ * p.ν * p.γ *
      uStar ^ (p.m + p.γ - 1) / (1 + vStar) ^ p.β| + 1
  let eta := gap / (2 * (gap + B))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hden : 0 < Real.exp 1 * eta := mul_pos (Real.exp_pos _) heta
  have hbase : 0 < sigma / (Real.exp 1 * eta) := div_pos hsigma hden
  unfold unitIntervalLinearizedStrongSmoothingConstant
  dsimp only
  change (sigma / (Real.exp 1 * (eta * t))) ^ sigma =
    (sigma / (Real.exp 1 * eta)) ^ sigma * t ^ (-sigma)
  rw [show Real.exp 1 * (eta * t) = (Real.exp 1 * eta) * t by ring]
  rw [show sigma / ((Real.exp 1 * eta) * t) =
      (sigma / (Real.exp 1 * eta)) * t⁻¹ by field_simp]
  rw [Real.mul_rpow hbase.le (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le]
  rw [Real.rpow_neg ht.le]

/-- Full-mode `L² -> X_2^sigma` smoothing in norm form.  In particular the
zero mode is propagated by the logistic multiplier; no projection occurs. -/
theorem unitIntervalLinearized_fractionalPowerNorm_le_full
    (p : CM2Params) {uStar vStar gap sigma t : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (ht : 0 < t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n) ≤
      unitIntervalLinearizedStrongSmoothingConstant
          p uStar vStar gap sigma * t ^ (-sigma) *
        Real.exp (-(gap / 2) * t) * coeffL2Norm a := by
  have ha0 : Summable fun n : ℕ => fractionalPowerEnergyTerm 1 0 a n := by
    simpa [fractionalPowerEnergyTerm, fractionalPowerWeight] using ha
  have henergy := unitIntervalLinearized_fractionalPowerEnergy_le_full
    p heq hgap hsigma ht ha0
  rw [unitInterval_fractionalPowerEnergy_zero_eq_coeffL2Energy] at henergy
  let K := unitIntervalLinearizedStrongSmoothingConstant
      p uStar vStar gap sigma * t ^ (-sigma) *
        Real.exp (-(gap / 2) * t)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (unitIntervalLinearizedStrongSmoothingConstant_pos
          p hgap.1 hsigma).le
        (Real.rpow_nonneg ht.le _))
      (Real.exp_nonneg _)
  have hfactor :
      (sigma /
          (Real.exp 1 *
            ((gap /
              (2 *
                (gap +
                  (|p.χ₀ * p.ν * p.γ *
                      uStar ^ (p.m + p.γ - 1) /
                    (1 + vStar) ^ p.β| + 1)))) * t))) ^ sigma *
          Real.exp (-(gap / 2) * t) = K := by
    rw [unitIntervalLinearized_smoothing_factor_eq p hgap.1 hsigma ht]
  rw [hfactor] at henergy
  have hroot := Real.sqrt_le_sqrt henergy
  have hbase : 0 ≤ coeffL2Energy a := coeffL2Energy_nonneg a
  unfold coeffL2Norm
  calc
    Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n) ≤
        Real.sqrt (K ^ 2 * coeffL2Energy a) := by simpa using hroot
    _ = K * Real.sqrt (coeffL2Energy a) := by
      rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
    _ = _ := rfl

/-- Same-order full-mode decay in the strong norm. -/
theorem unitIntervalLinearized_fractionalPowerNorm_le_exp
    (p : CM2Params) {uStar vStar gap sigma t : ℝ}
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar gap)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm 1 sigma a n) :
    Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n) ≤
      Real.exp (-gap * t) *
        Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n) := by
  have henergy := unitIntervalLinearized_fractionalPowerEnergy_le_exp
    p hgap ht ha
  have hroot := Real.sqrt_le_sqrt henergy
  have hexp : 0 ≤ Real.exp (-gap * t) := Real.exp_nonneg _
  have hbase : 0 ≤ ∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n :=
    tsum_nonneg fun n => fractionalPowerEnergyTerm_nonneg 1 sigma a n
  calc
    Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n) ≤
        Real.sqrt (Real.exp (-gap * t) ^ 2 *
          (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n)) := hroot
    _ = Real.exp (-gap * t) *
        Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hexp]

#print axioms unitInterval_fractionalPowerEnergy_zero_eq_coeffL2Energy
#print axioms unitIntervalLinearized_fractionalPowerNorm_le_full
#print axioms unitIntervalLinearized_fractionalPowerNorm_le_exp

end

end ShenWork.Paper3
