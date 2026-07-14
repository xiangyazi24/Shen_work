import ShenWork.Paper3.IntervalClassicalClampField
import ShenWork.Paper2.IntervalDomainMChemDivBoundaryLimit
import ShenWork.Paper2.IntervalBFormLinearDriftComparisonRegular

open Set

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The physical resolver factor `vₓ (1+v)⁻ᵝ`. -/
def intervalDomainMFluxFactor
    (p : CM2Params) (v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  deriv (intervalDomainLift (v t)) x *
    (1 + intervalDomainLift (v t) x) ^ (-p.β)

/-- The physical derivative of the resolver factor, with `vₓₓ` replaced by
the elliptic equation. -/
def intervalDomainMFluxFactorDerivPhysical
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  (p.μ * intervalDomainLift (v t) x -
      p.ν * intervalDomainLift (u t) x ^ p.γ) *
      (1 + intervalDomainLift (v t) x) ^ (-p.β) -
    p.β * deriv (intervalDomainLift (v t)) x ^ 2 *
      (1 + intervalDomainLift (v t) x) ^ (-p.β - 1)

/-- First-order coefficient obtained by expanding the faithful divergence
`∂ₓ(uᵐ q)`. -/
def intervalDomainMLinearDrift
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  -p.χ₀ * p.m * intervalDomainLift (u t) x ^ (p.m - 1) *
    intervalDomainMFluxFactor p v t x

/-- Zeroth-order coefficient in the same expansion.  It contains the complete
`qₓ` contribution, so no term linear in a comparison positive part is left
outside the coefficient. -/
def intervalDomainMLinearReaction
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.a - p.b * intervalDomainLift (u t) x ^ p.α -
    p.χ₀ * intervalDomainLift (u t) x ^ (p.m - 1) *
      intervalDomainMFluxFactorDerivPhysical p u v t x

/-- Uniform drift bound supplied by a positive upper bound `U≤M` and the
elliptic estimate `|vₓ|≤Q`. -/
theorem intervalDomainMLinearDrift_abs_le
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {t x M Q : ℝ}
    (hm : 1 ≤ p.m) (hM : 0 ≤ M)
    (hU0 : 0 ≤ intervalDomainLift (u t) x)
    (hUM : intervalDomainLift (u t) x ≤ M)
    (hV0 : 0 ≤ intervalDomainLift (v t) x)
    (hVx : |deriv (intervalDomainLift (v t)) x| ≤ Q) :
    |intervalDomainMLinearDrift p u v t x| ≤
      |p.χ₀| * p.m * M ^ (p.m - 1) * Q := by
  have hm0 : 0 ≤ p.m := le_trans (by norm_num) hm
  have hm1 : 0 ≤ p.m - 1 := sub_nonneg.mpr hm
  have hpow : intervalDomainLift (u t) x ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
    Real.rpow_le_rpow hU0 hUM hm1
  have hpow0 : 0 ≤ intervalDomainLift (u t) x ^ (p.m - 1) :=
    Real.rpow_nonneg hU0 _
  have hden0 : 0 ≤ (1 + intervalDomainLift (v t) x) ^ (-p.β) :=
    Real.rpow_nonneg (by linarith) _
  have hden1 : (1 + intervalDomainLift (v t) x) ^ (-p.β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [p.hβ])
  have hfactor : |intervalDomainMFluxFactor p v t x| ≤ Q := by
    rw [intervalDomainMFluxFactor, abs_mul,
      abs_of_nonneg hden0]
    calc
      |deriv (intervalDomainLift (v t)) x| *
          (1 + intervalDomainLift (v t) x) ^ (-p.β)
          ≤ Q * 1 := mul_le_mul hVx hden1 hden0 (le_trans (abs_nonneg _) hVx)
      _ = Q := mul_one Q
  have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) hVx
  rw [intervalDomainMLinearDrift, abs_mul, abs_mul, abs_mul,
    abs_neg, abs_of_nonneg hm0, abs_of_nonneg hpow0]
  gcongr

/-- Uniform reaction-coefficient bound from `U≤M`, `v≥0`, `|vₓ|≤Q`, and
the elliptic reaction bound `|μv-νuᵞ|≤Q`. -/
theorem intervalDomainMLinearReaction_abs_le
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {t x M Q : ℝ}
    (hm : 1 ≤ p.m) (hM : 0 ≤ M)
    (hU0 : 0 ≤ intervalDomainLift (u t) x)
    (hUM : intervalDomainLift (u t) x ≤ M)
    (hV0 : 0 ≤ intervalDomainLift (v t) x)
    (hVx : |deriv (intervalDomainLift (v t)) x| ≤ Q)
    (hVxx : |p.μ * intervalDomainLift (v t) x -
      p.ν * intervalDomainLift (u t) x ^ p.γ| ≤ Q) :
    |intervalDomainMLinearReaction p u v t x| ≤
      p.a + p.b * M ^ p.α +
        |p.χ₀| * M ^ (p.m - 1) * (Q + p.β * Q ^ 2) := by
  have hm1 : 0 ≤ p.m - 1 := sub_nonneg.mpr hm
  have hpow : intervalDomainLift (u t) x ^ (p.m - 1) ≤ M ^ (p.m - 1) :=
    Real.rpow_le_rpow hU0 hUM hm1
  have hpow0 : 0 ≤ intervalDomainLift (u t) x ^ (p.m - 1) :=
    Real.rpow_nonneg hU0 _
  have hUa : intervalDomainLift (u t) x ^ p.α ≤ M ^ p.α :=
    Real.rpow_le_rpow hU0 hUM p.hα.le
  have hUa0 : 0 ≤ intervalDomainLift (u t) x ^ p.α :=
    Real.rpow_nonneg hU0 _
  have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) hVx
  have hden0 : 0 ≤ (1 + intervalDomainLift (v t) x) ^ (-p.β) :=
    Real.rpow_nonneg (by linarith) _
  have hden0' : (1 + intervalDomainLift (v t) x) ^ (-p.β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [p.hβ])
  have hden1 : 0 ≤ (1 + intervalDomainLift (v t) x) ^ (-p.β - 1) :=
    Real.rpow_nonneg (by linarith) _
  have hden1' : (1 + intervalDomainLift (v t) x) ^ (-p.β - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [p.hβ])
  have hvx_sq : deriv (intervalDomainLift (v t)) x ^ 2 ≤ Q ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hQ0] using hVx)
  have hterm1 :
      |(p.μ * intervalDomainLift (v t) x -
          p.ν * intervalDomainLift (u t) x ^ p.γ) *
          (1 + intervalDomainLift (v t) x) ^ (-p.β)| ≤ Q := by
    rw [abs_mul, abs_of_nonneg hden0]
    calc
      |p.μ * intervalDomainLift (v t) x -
          p.ν * intervalDomainLift (u t) x ^ p.γ| *
          (1 + intervalDomainLift (v t) x) ^ (-p.β)
          ≤ Q * 1 := mul_le_mul hVxx hden0' hden0
            (le_trans (abs_nonneg _) hVxx)
      _ = Q := mul_one Q
  have hterm2 :
      |p.β * deriv (intervalDomainLift (v t)) x ^ 2 *
          (1 + intervalDomainLift (v t) x) ^ (-p.β - 1)| ≤
        p.β * Q ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg p.hβ,
      abs_of_nonneg (sq_nonneg _), abs_of_nonneg hden1]
    have hinner : deriv (intervalDomainLift (v t)) x ^ 2 *
        (1 + intervalDomainLift (v t) x) ^ (-p.β - 1) ≤ Q ^ 2 := by
      calc
        deriv (intervalDomainLift (v t)) x ^ 2 *
            (1 + intervalDomainLift (v t) x) ^ (-p.β - 1)
            ≤ Q ^ 2 * 1 := mul_le_mul hvx_sq hden1' hden1 (sq_nonneg _)
        _ = Q ^ 2 := mul_one _
    have := mul_le_mul_of_nonneg_left hinner p.hβ
    simpa [mul_assoc] using this
  have hfactor : |intervalDomainMFluxFactorDerivPhysical p u v t x| ≤
      Q + p.β * Q ^ 2 := by
    unfold intervalDomainMFluxFactorDerivPhysical
    exact (abs_sub _ _).trans (add_le_add hterm1 hterm2)
  have hfactor0 : 0 ≤ Q + p.β * Q ^ 2 :=
    add_nonneg hQ0 (mul_nonneg p.hβ (sq_nonneg Q))
  have hbUa : p.b * intervalDomainLift (u t) x ^ p.α ≤
      p.b * M ^ p.α := mul_le_mul_of_nonneg_left hUa p.hb
  have hchem :
      |p.χ₀| * intervalDomainLift (u t) x ^ (p.m - 1) *
          |intervalDomainMFluxFactorDerivPhysical p u v t x| ≤
        |p.χ₀| * M ^ (p.m - 1) * (Q + p.β * Q ^ 2) := by
    have hinner := mul_le_mul hpow hfactor (abs_nonneg _)
      (Real.rpow_nonneg hM _)
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hinner (abs_nonneg p.χ₀))
  unfold intervalDomainMLinearReaction
  calc
    |p.a - p.b * intervalDomainLift (u t) x ^ p.α -
        p.χ₀ * intervalDomainLift (u t) x ^ (p.m - 1) *
          intervalDomainMFluxFactorDerivPhysical p u v t x|
        ≤ |p.a| + |p.b * intervalDomainLift (u t) x ^ p.α| +
          |p.χ₀ * intervalDomainLift (u t) x ^ (p.m - 1) *
            intervalDomainMFluxFactorDerivPhysical p u v t x| := by
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ p.a + p.b * M ^ p.α +
          |p.χ₀| * M ^ (p.m - 1) * (Q + p.β * Q ^ 2) := by
      rw [abs_of_nonneg p.ha, abs_mul, abs_of_nonneg p.hb,
        abs_of_nonneg hUa0, abs_mul, abs_mul, abs_of_nonneg hpow0]
      exact add_le_add (add_le_add le_rfl hbUa) hchem

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainMLinearDrift_abs_le
#print axioms ShenWork.Paper3.intervalDomainMLinearReaction_abs_le
