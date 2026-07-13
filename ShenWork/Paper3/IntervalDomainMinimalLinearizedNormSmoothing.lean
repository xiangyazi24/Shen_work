import ShenWork.Paper3.IntervalDomainLinearizedNormSmoothing

/-!
# Strong smoothing on the mass-constrained linearized subspace

The minimal model has a neutral zeroth mode.  These are the norm-level
counterparts of the existing nonzero-mode energy estimates; every theorem
requires the coefficient sequence to have zero mean.
-/

namespace ShenWork.Paper3

open ShenWork.PDE.SectorialOperator
open ShenWork.PDE.FractionalPower

noncomputable section

/-- Mass-constrained `L² -> X_2^sigma` smoothing. -/
theorem unitIntervalLinearizedMass_fractionalPowerNorm_le
    (p : CM2Params) {uStar vStar gap sigma t : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (ht : 0 < t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2)
    (ha0 : a 0 = 0) :
    Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n) ≤
      unitIntervalLinearizedStrongSmoothingConstant
          p uStar vStar gap sigma * t ^ (-sigma) *
        Real.exp (-(gap / 2) * t) * coeffL2Norm a := by
  have haEnergy : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 0 a n := by
    simpa [fractionalPowerEnergyTerm, fractionalPowerWeight] using ha
  have henergy := unitIntervalLinearized_fractionalPowerEnergy_le_on_nonzero
    p heq hgap hsigma ht haEnergy ha0
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

/-- Positive time maps a zero-mean `L²` sequence into the strong space. -/
theorem unitIntervalLinearizedMass_fractionalPower_summable
    (p : CM2Params) {uStar vStar gap sigma t : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (ht : 0 < t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2)
    (ha0 : a 0 = 0) :
    Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a) n := by
  have haEnergy : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 0 a n := by
    simpa [fractionalPowerEnergyTerm, fractionalPowerWeight] using ha
  let K : ℝ :=
    ((sigma /
        (Real.exp 1 *
          ((gap /
            (2 *
              (gap +
                (|p.χ₀ * p.ν * p.γ *
                    uStar ^ (p.m + p.γ - 1) /
                  (1 + vStar) ^ p.β| + 1)))) * t))) ^ sigma *
      Real.exp (-(gap / 2) * t)) ^ 2
  have hmajor : Summable fun n : ℕ =>
      K * fractionalPowerEnergyTerm 1 0 a n := haEnergy.mul_left K
  apply Summable.of_nonneg_of_le
    (fun n => fractionalPowerEnergyTerm_nonneg 1 sigma _ n)
    (fun n => ?_) hmajor
  simpa [K] using
    unitIntervalLinearized_fractionalPowerEnergyTerm_le_on_nonzero
      p heq hgap hsigma ht (sigma := 0) ha0 n

/-- Same-order energy decay on the zero-mean strong space. -/
theorem unitIntervalLinearizedMass_fractionalPowerEnergy_le_exp
    (p : CM2Params) {uStar vStar gap sigma t : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm 1 sigma a n)
    (ha0 : a 0 = 0) :
    (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n) ≤
      Real.exp (-gap * t) ^ 2 *
        (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n) := by
  have hpoint : ∀ n : ℕ,
      fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n ≤
        Real.exp (-gap * t) ^ 2 *
          fractionalPowerEnergyTerm 1 sigma a n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [fractionalPowerEnergyTerm, diagonalSemigroupCoeff, ha0]
    · have hg := hgap.2 n hn
      have hexp :
          Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n) ≤
            Real.exp (-gap * t) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hmode :
          (1 + unitIntervalNeumannSpectrum.eigenvalue n) ^ (0 : ℝ) *
              Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n) ≤
            Real.exp (-gap * t) := by simpa using hexp
      have hleft : 0 ≤
          (1 + unitIntervalNeumannSpectrum.eigenvalue n) ^ (0 : ℝ) *
            Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n) := by
        positivity
      simpa using
        unitIntervalLinearized_fractionalPowerEnergyTerm_le_of_mode
          p (sigma := sigma) (theta := 0) (t := t)
            (K := Real.exp (-gap * t)) n hmode hleft
  have hmajor : Summable fun n : ℕ =>
      Real.exp (-gap * t) ^ 2 * fractionalPowerEnergyTerm 1 sigma a n :=
    ha.mul_left _
  have hsum : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a) n :=
    Summable.of_nonneg_of_le
      (fun n => fractionalPowerEnergyTerm_nonneg 1 sigma _ n)
      hpoint hmajor
  exact hsum.tsum_le_tsum hpoint hmajor |>.trans_eq (ha.tsum_mul_left _)

/-- Same-order norm decay on the zero-mean strong space. -/
theorem unitIntervalLinearizedMass_fractionalPowerNorm_le_exp
    (p : CM2Params) {uStar vStar gap sigma t : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm 1 sigma a n)
    (ha0 : a 0 = 0) :
    Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) t a) n) ≤
      Real.exp (-gap * t) *
        Real.sqrt (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n) := by
  have henergy := unitIntervalLinearizedMass_fractionalPowerEnergy_le_exp
    p hgap ht ha ha0
  have hroot := Real.sqrt_le_sqrt henergy
  have hexp : 0 ≤ Real.exp (-gap * t) := Real.exp_nonneg _
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

/-- Same-order mass-constrained propagation preserves strong membership. -/
theorem unitIntervalLinearizedMass_fractionalPower_summable_exp
    (p : CM2Params) {uStar vStar gap sigma t : ℝ}
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (ht : 0 ≤ t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => fractionalPowerEnergyTerm 1 sigma a n)
    (ha0 : a 0 = 0) :
    Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) t a) n := by
  have hmajor : Summable fun n : ℕ =>
      Real.exp (-gap * t) ^ 2 * fractionalPowerEnergyTerm 1 sigma a n :=
    ha.mul_left _
  apply Summable.of_nonneg_of_le
    (fun n => fractionalPowerEnergyTerm_nonneg 1 sigma _ n)
    (fun n => ?_) hmajor
  by_cases hn : n = 0
  · subst n
    simp [fractionalPowerEnergyTerm, diagonalSemigroupCoeff, ha0]
  · have hg := hgap.2 n hn
    have hexp :
        Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n) ≤
          Real.exp (-gap * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hmode :
        (1 + unitIntervalNeumannSpectrum.eigenvalue n) ^ (0 : ℝ) *
            Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n) ≤
          Real.exp (-gap * t) := by simpa using hexp
    have hleft : 0 ≤
        (1 + unitIntervalNeumannSpectrum.eigenvalue n) ^ (0 : ℝ) *
          Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n) := by
      positivity
    simpa using
      unitIntervalLinearized_fractionalPowerEnergyTerm_le_of_mode
        p (sigma := sigma) (theta := 0) (t := t)
          (K := Real.exp (-gap * t)) n hmode hleft

#print axioms unitIntervalLinearizedMass_fractionalPowerNorm_le
#print axioms unitIntervalLinearizedMass_fractionalPower_summable
#print axioms unitIntervalLinearizedMass_fractionalPowerEnergy_le_exp
#print axioms unitIntervalLinearizedMass_fractionalPowerNorm_le_exp
#print axioms unitIntervalLinearizedMass_fractionalPower_summable_exp

end

end ShenWork.Paper3
