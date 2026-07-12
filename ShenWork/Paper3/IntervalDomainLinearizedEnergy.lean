/-
  Fractional-power energy estimates for the stable Paper3 diagonal semigroup.

  This lifts the scalar modal smoothing estimate to the weighted coefficient
  space used by `FractionalPowerSpace`.  The mass-constrained theorem keeps
  the zero coefficient separate, exactly as required in the `a = b = 0`
  branch of Theorem 2.2.
-/
import ShenWork.Paper3.IntervalDomainLinearizedSmoothing
import ShenWork.PDE.FractionalPowerSpace

namespace ShenWork.Paper3

open ShenWork.PDE.SectorialOperator
open ShenWork.PDE.FractionalPower

noncomputable section

/-- The two unit-interval Neumann eigenvalue conventions in the spectral and
fractional-power files agree. -/
theorem neumannEigenvalue_one_eq_unitInterval (n : ℕ) :
    neumannEigenvalue 1 n = unitIntervalNeumannSpectrum.eigenvalue n := by
  simp [neumannEigenvalue, unitIntervalNeumannSpectrum]
  ring

/-- Pointwise weighted-energy smoothing on the mass-constrained subspace. -/
theorem unitIntervalLinearized_fractionalPowerEnergyTerm_le_on_nonzero
    (p : CM2Params) {uStar vStar gap sigma theta t : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (htheta : 0 < theta) (ht : 0 < t)
    {a : ℕ → ℂ} (ha0 : a 0 = 0) (n : ℕ) :
    fractionalPowerEnergyTerm 1 (sigma + theta)
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a) n ≤
      ((theta /
          (Real.exp 1 *
            ((gap /
              (2 *
                (gap +
                  (|p.χ₀ * p.ν * p.γ *
                      uStar ^ (p.m + p.γ - 1) /
                    (1 + vStar) ^ p.β| + 1)))) * t))) ^ theta *
        Real.exp (-(gap / 2) * t)) ^ 2 *
        fractionalPowerEnergyTerm 1 sigma a n := by
  by_cases hn : n = 0
  · subst n
    simp [fractionalPowerEnergyTerm, fractionalPowerWeight,
      diagonalSemigroupCoeff, ha0]
  · let lambda : ℝ := unitIntervalNeumannSpectrum.eigenvalue n
    let K : ℝ :=
      (theta /
          (Real.exp 1 *
            ((gap /
              (2 *
                (gap +
                  (|p.χ₀ * p.ν * p.γ *
                      uStar ^ (p.m + p.γ - 1) /
                    (1 + vStar) ^ p.β| + 1)))) * t))) ^ theta *
        Real.exp (-(gap / 2) * t)
    have hmode :
        (1 + lambda) ^ theta *
            Real.exp
              (t * unitIntervalLinearizedGrowth p uStar vStar n) ≤ K := by
      simpa [lambda, K] using
        (unitIntervalLinearizedGrowth_weighted_smoothing p heq hgap
          htheta ht hn)
    have hbase : 0 < 1 + lambda := by
      dsimp [lambda]
      linarith
        [unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n]
    have hleft :
        0 ≤ (1 + lambda) ^ theta *
          Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n) :=
      mul_nonneg (Real.rpow_nonneg hbase.le _) (Real.exp_nonneg _)
    have hK : 0 ≤ K := hleft.trans hmode
    have hsq :
        ((1 + lambda) ^ theta *
          Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n)) ^ 2 ≤
            K ^ 2 :=
      (sq_le_sq₀ hleft hK).2 hmode
    have hcoeff : 0 ≤ (1 + lambda) ^ (2 * sigma) * ‖a n‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hbase.le _) (sq_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hsq hcoeff
    change
      (1 + neumannEigenvalue 1 n) ^ (2 * (sigma + theta)) *
          ‖(Real.exp
              (t * unitIntervalLinearizedGrowth p uStar vStar n) : ℂ) *
            a n‖ ^ 2 ≤
        K ^ 2 *
          ((1 + neumannEigenvalue 1 n) ^ (2 * sigma) * ‖a n‖ ^ 2)
    rw [neumannEigenvalue_one_eq_unitInterval]
    change
      (1 + lambda) ^ (2 * (sigma + theta)) *
          ‖(Real.exp
              (t * unitIntervalLinearizedGrowth p uStar vStar n) : ℂ) *
            a n‖ ^ 2 ≤
        K ^ 2 * ((1 + lambda) ^ (2 * sigma) * ‖a n‖ ^ 2)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hweight_split :
        (1 + lambda) ^ (2 * (sigma + theta)) =
          (1 + lambda) ^ (2 * sigma) * ((1 + lambda) ^ theta) ^ 2 := by
      rw [show 2 * (sigma + theta) = 2 * sigma + 2 * theta by ring,
        Real.rpow_add hbase]
      congr 1
      rw [show 2 * theta = theta * 2 by ring,
        Real.rpow_mul hbase.le]
      simp [pow_two]
    rw [hweight_split]
    nlinarith

/-- Positive-time smoothing in total fractional-power energy on the
mass-constrained subspace. -/
theorem unitIntervalLinearized_fractionalPowerEnergy_le_on_nonzero
    (p : CM2Params) {uStar vStar gap sigma theta t : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (htheta : 0 < theta) (ht : 0 < t)
    {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm 1 sigma a n)
    (ha0 : a 0 = 0) :
    (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 (sigma + theta)
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n) ≤
      ((theta /
          (Real.exp 1 *
            ((gap /
              (2 *
                (gap +
                  (|p.χ₀ * p.ν * p.γ *
                      uStar ^ (p.m + p.γ - 1) /
                    (1 + vStar) ^ p.β| + 1)))) * t))) ^ theta *
        Real.exp (-(gap / 2) * t)) ^ 2 *
        (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n) := by
  let K : ℝ :=
    ((theta /
        (Real.exp 1 *
          ((gap /
            (2 *
              (gap +
                (|p.χ₀ * p.ν * p.γ *
                    uStar ^ (p.m + p.γ - 1) /
                  (1 + vStar) ^ p.β| + 1)))) * t))) ^ theta *
      Real.exp (-(gap / 2) * t)) ^ 2
  have hK : 0 ≤ K := sq_nonneg _
  have hmajor : Summable fun n : ℕ =>
      K * fractionalPowerEnergyTerm 1 sigma a n := ha.mul_left K
  have hsum :
      Summable fun n : ℕ =>
        fractionalPowerEnergyTerm 1 (sigma + theta)
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n := by
    apply Summable.of_nonneg_of_le
      (fun n => fractionalPowerEnergyTerm_nonneg 1 (sigma + theta) _ n)
      (fun n => ?_) hmajor
    simpa [K] using
      unitIntervalLinearized_fractionalPowerEnergyTerm_le_on_nonzero
        p heq hgap htheta ht ha0 n
  have hle := hsum.tsum_le_tsum
    (fun n => by
      simpa [K] using
        unitIntervalLinearized_fractionalPowerEnergyTerm_le_on_nonzero
          p heq hgap htheta ht ha0 n)
    hmajor
  simpa [K, ha.tsum_mul_left] using hle

#print axioms neumannEigenvalue_one_eq_unitInterval
#print axioms unitIntervalLinearized_fractionalPowerEnergyTerm_le_on_nonzero
#print axioms unitIntervalLinearized_fractionalPowerEnergy_le_on_nonzero

end

end ShenWork.Paper3
