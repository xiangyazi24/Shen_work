/-
  Weighted smoothing for the stable diagonal Paper3 semigroup.

  The proof combines two independent bounds on each modal growth rate:
  a uniform spectral gap and the high-frequency estimate `growth <= -lambda+B`.
  A small fraction of the elapsed time supplies parabolic smoothing; the
  remaining fraction supplies exponential decay.
-/
import ShenWork.Paper3.IntervalDomainUniformSpectralGap
import ShenWork.Paper3.IntervalDomainSmoothingBound

namespace ShenWork.Paper3

open ShenWork.PDE.SectorialOperator
open ShenWork.Paper3.SmoothingBound

noncomputable section

/-- Scalar time-splitting estimate behind stable-semigroup smoothing. -/
theorem stable_growth_weighted_smoothing
    {growth lambda gap B theta t : ℝ}
    (hlambda : 0 ≤ lambda) (hgap : 0 < gap) (hB : 0 ≤ B)
    (hgGap : growth ≤ -gap)
    (hgTail : growth ≤ -(1 + lambda) + B)
    (htheta : 0 < theta) (ht : 0 < t) :
    (1 + lambda) ^ theta * Real.exp (t * growth) ≤
      (theta /
          (Real.exp 1 * ((gap / (2 * (gap + B))) * t))) ^ theta *
        Real.exp (-(gap / 2) * t) := by
  let eta : ℝ := gap / (2 * (gap + B))
  have hgapB : 0 < gap + B := add_pos_of_pos_of_nonneg hgap hB
  have heta : 0 < eta := div_pos hgap (mul_pos two_pos hgapB)
  have heta_le_one : eta ≤ 1 := by
    dsimp [eta]
    rw [div_le_one (mul_pos two_pos hgapB)]
    linarith
  have hone_eta : 0 ≤ 1 - eta := sub_nonneg.mpr heta_le_one
  have hsplit :
      t * growth = (eta * t) * growth + ((1 - eta) * t) * growth := by
    ring
  have hsmooth_part :
      (eta * t) * growth ≤ (eta * t) * (-(1 + lambda) + B) :=
    mul_le_mul_of_nonneg_left hgTail (mul_nonneg heta.le ht.le)
  have hdecay_part :
      ((1 - eta) * t) * growth ≤ ((1 - eta) * t) * (-gap) :=
    mul_le_mul_of_nonneg_left hgGap (mul_nonneg hone_eta ht.le)
  have heta_balance : (1 - eta) * gap - eta * B = gap / 2 := by
    dsimp [eta]
    field_simp [ne_of_gt hgapB]
    ring
  have hexponent :
      t * growth ≤ -((1 + lambda) * (eta * t)) - (gap / 2) * t := by
    rw [hsplit]
    calc
      (eta * t) * growth + ((1 - eta) * t) * growth
          ≤ (eta * t) * (-(1 + lambda) + B) +
              ((1 - eta) * t) * (-gap) := add_le_add hsmooth_part hdecay_part
      _ = -((1 + lambda) * (eta * t)) - (gap / 2) * t := by
        rw [← heta_balance]
        ring
  have hexp :
      Real.exp (t * growth) ≤
        Real.exp (-((1 + lambda) * (eta * t))) *
          Real.exp (-(gap / 2) * t) := by
    calc
      Real.exp (t * growth)
          ≤ Real.exp
              (-((1 + lambda) * (eta * t)) - (gap / 2) * t) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp (-((1 + lambda) * (eta * t))) *
            Real.exp (-(gap / 2) * t) := by
        rw [show -((1 + lambda) * (eta * t)) - (gap / 2) * t =
          -((1 + lambda) * (eta * t)) + (-(gap / 2) * t) by ring,
          Real.exp_add]
  have hweight : 0 ≤ (1 + lambda) ^ theta :=
    Real.rpow_nonneg (by linarith) _
  have hsm :=
    rpow_mul_exp_neg_mul_le (x := 1 + lambda) (p := theta)
      (by linarith) htheta (mul_pos heta ht)
  calc
    (1 + lambda) ^ theta * Real.exp (t * growth)
        ≤ (1 + lambda) ^ theta *
            (Real.exp (-((1 + lambda) * (eta * t))) *
              Real.exp (-(gap / 2) * t)) :=
          mul_le_mul_of_nonneg_left hexp hweight
    _ = ((1 + lambda) ^ theta *
          Real.exp (-((1 + lambda) * (eta * t)))) *
            Real.exp (-(gap / 2) * t) := by ring
    _ ≤ (theta / (Real.exp 1 * (eta * t))) ^ theta *
            Real.exp (-(gap / 2) * t) :=
          mul_le_mul_of_nonneg_right hsm (Real.exp_nonneg _)
    _ = (theta /
          (Real.exp 1 * ((gap / (2 * (gap + B))) * t))) ^ theta *
            Real.exp (-(gap / 2) * t) := by rfl

/-- Per-mode stable smoothing for the concrete Paper3 linearized growth. -/
theorem unitIntervalLinearizedGrowth_weighted_smoothing
    (p : CM2Params) {uStar vStar gap theta t : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (htheta : 0 < theta) (ht : 0 < t)
    {n : ℕ} (hn : n ≠ 0) :
    (1 + unitIntervalNeumannSpectrum.eigenvalue n) ^ theta *
        Real.exp (t * unitIntervalLinearizedGrowth p uStar vStar n) ≤
      (theta /
          (Real.exp 1 *
            ((gap /
              (2 *
                (gap +
                  (|p.χ₀ * p.ν * p.γ *
                      uStar ^ (p.m + p.γ - 1) /
                    (1 + vStar) ^ p.β| + 1)))) * t))) ^ theta *
        Real.exp (-(gap / 2) * t) := by
  let B : ℝ :=
    |p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) /
      (1 + vStar) ^ p.β| + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgGap : unitIntervalLinearizedGrowth p uStar vStar n ≤ -gap :=
    hgap.2 n hn
  have hsigma :=
    sigma_le_neg_lambda_add_abs_chemMultiplier p (uStar := uStar)
      heq.v_nonneg
      (unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n)
  have hgTail :
      unitIntervalLinearizedGrowth p uStar vStar n ≤
        -(1 + unitIntervalNeumannSpectrum.eigenvalue n) + B := by
    change sigma p uStar vStar (unitIntervalNeumannSpectrum.eigenvalue n) ≤
      -(1 + unitIntervalNeumannSpectrum.eigenvalue n) + B
    change sigma p uStar vStar (unitIntervalNeumannSpectrum.eigenvalue n) ≤
      -unitIntervalNeumannSpectrum.eigenvalue n +
        |p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) /
          (1 + vStar) ^ p.β| at hsigma
    dsimp [B]
    linarith
  simpa [B] using
    (stable_growth_weighted_smoothing
      (lambda := unitIntervalNeumannSpectrum.eigenvalue n)
      (gap := gap) (B := B) (theta := theta) (t := t)
      (unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n)
      hgap.1 hB hgGap hgTail htheta ht)

#print axioms stable_growth_weighted_smoothing
#print axioms unitIntervalLinearizedGrowth_weighted_smoothing

end

end ShenWork.Paper3
