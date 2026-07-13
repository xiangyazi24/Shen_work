import ShenWork.Paper3.IntervalDomainMinimalPowerDifference
import ShenWork.Paper3.IntervalDomainEntropyStrong2

/-!
# Minimal-model entropy dissipation on the unit interval

This file implements Section 8.1 after the orbit-independent eventual box is
available.  The mass constraint converts the half diffusion left by Young's
inequality into an `L²` distance, while the signal floor and the local
power-difference slope control the chemotactic term.
-/

open Filter MeasureTheory Set Topology
open scoped Topology Interval

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

/-- On a positive mass-constrained slice lying below `uBar`, the entropy
gradient controls the squared `L²` distance to the conserved mean. -/
theorem intervalDomain_minimal_weightedGradient_ge_l2
    {p : CM2Params} {T t uStar uBar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (huBar : 0 < uBar)
    (hmass : intervalDomain.integral (u t) = uStar)
    (hupper : ∀ x : intervalDomainPoint, u t x ≤ uBar) :
    uBar ^ (-2 : ℝ) *
        (∫ y in (0 : ℝ)..1,
          (intervalDomainLift (u t) y - uStar) ^ 2) ≤
      intervalDomainLpWeightedGradientDissipation 0 u t := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let Ux : ℝ → ℝ := deriv U
  let g : ℝ → ℝ := fun y => U y ^ (-2 : ℝ) * Ux y ^ 2
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU2 : ContDiffOn ℝ 2 U (Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hUcont : ContinuousOn U (Icc (0 : ℝ) 1) := hU2.continuousOn
  have hUxcont : ContinuousOn Ux (Icc (0 : ℝ) 1) := by
    dsimp [Ux]
    exact (deriv_lift_contDiffOn_one_Icc hU2
      (derivWithin_left_zero hsol ht0 htT u (Or.inl rfl))
      (derivWithin_right_zero hsol ht0 htT u (Or.inl rfl))).continuousOn
  have hUpos : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U y := by
    intro y hy
    simpa [U] using solution_lift_pos_Icc hsol ht y hy
  have hUupper : ∀ y ∈ Icc (0 : ℝ) 1, U y ≤ uBar := by
    intro y hy
    simpa [U, intervalDomainLift, hy] using
      hupper (⟨y, hy⟩ : intervalDomainPoint)
  have hUxSqInt : IntervalIntegrable (fun y => Ux y ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hUxcont.pow 2
  have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    dsimp [g]
    exact (hUcont.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))).mul (hUxcont.pow 2)
  have hgint : IntervalIntegrable g volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hgcont
  have hcoeff : 0 ≤ uBar ^ (-2 : ℝ) :=
    Real.rpow_nonneg huBar.le _
  have hpoincare := intervalDomain_classicalSlice_poincare
    hsol ht0 htT hmass
  have hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      uBar ^ (-2 : ℝ) * Ux y ^ 2 ≤ g y := by
    intro y hy
    have hpow : uBar ^ (-2 : ℝ) ≤ U y ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (hUpos y hy) (hUupper y hy) (by norm_num)
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  have hG := intervalDomain_lpGradient_zero_eq_integral hsol ht0 htT
  calc
    uBar ^ (-2 : ℝ) *
          (∫ y in (0 : ℝ)..1, (U y - uStar) ^ 2) ≤
        uBar ^ (-2 : ℝ) *
          (∫ y in (0 : ℝ)..1, Ux y ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa [U, Ux] using hpoincare) hcoeff
    _ = ∫ y in (0 : ℝ)..1, uBar ^ (-2 : ℝ) * Ux y ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ y in (0 : ℝ)..1, g y := by
      exact intervalIntegral.integral_mono_on (by norm_num)
        (hUxSqInt.const_mul _) hgint hweight
    _ = intervalDomainLpWeightedGradientDissipation 0 u t := by
      simpa [g, U, Ux] using hG.symm

/-- The exact positive coefficient left in the Section 8.1 entropy estimate
after Poincare, the elliptic multiplier, and the power-difference bound. -/
def minimal1EntropyCoefficient
    (p : CM2Params) (uStar uBar vLower : ℝ) : ℝ :=
  uStar / 2 *
    (uBar ^ (-2 : ℝ) -
      p.χ₀ ^ 2 * p.ν ^ 2 * minimalPowerSlope p uStar uBar ^ 2 /
        (4 * p.μ * ((1 + vLower) ^ p.β) ^ 2))

/-- The third entry in `chiMinimal1Formula` makes the concrete entropy
coefficient strictly positive. -/
theorem minimal1EntropyCoefficient_pos_of_chi_lt
    (p : CM2Params) {uStar uBar vLower : ℝ}
    (huStar : 0 < uStar) (huBar : 0 < uBar) (hvLower : 0 ≤ vLower)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiMinimal1Formula p 1 uStar uBar vLower) :
    0 < minimal1EntropyCoefficient p uStar uBar vLower := by
  let S : ℝ := minimalPowerSlope p uStar uBar
  let B : ℝ := (1 + vLower) ^ p.β
  have hS : 0 < S := by
    simpa [S] using minimalPowerSlope_pos p huStar huBar
  have hbase : 0 < 1 + vLower := by linarith
  have hB : 0 < B := Real.rpow_pos_of_pos hbase _
  have hGamma : GammaMinimalFormula p.γ uStar uBar = S * uBar := by
    simpa [S] using GammaMinimalFormula_eq_slope_mul p huBar
  have hsqrt : 0 < Real.sqrt p.μ := Real.sqrt_pos.mpr p.hμ
  have hden : 0 < p.ν * (S * uBar) :=
    mul_pos p.hν (mul_pos hS huBar)
  have hthird :
      p.χ₀ < 2 * Real.sqrt p.μ * B / (p.ν * (S * uBar)) := by
    have := hχ.trans_le (min_le_right
      (min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
      (2 * Real.sqrt (p.μ * 1) * (1 + vLower) ^ p.β /
        (p.ν * GammaMinimalFormula p.γ uStar uBar)))
    simpa [chiMinimal1Formula, B, hGamma] using this
  have hmul :
      p.χ₀ * (p.ν * (S * uBar)) < 2 * Real.sqrt p.μ * B :=
    (lt_div_iff₀ hden).mp hthird
  have hleft : 0 < p.χ₀ * (p.ν * (S * uBar)) :=
    mul_pos hχpos hden
  have hright : 0 < 2 * Real.sqrt p.μ * B :=
    mul_pos (mul_pos (by norm_num) hsqrt) hB
  have hsqrtSq : (Real.sqrt p.μ) ^ 2 = p.μ := Real.sq_sqrt p.hμ.le
  have hsq :
      p.χ₀ ^ 2 * p.ν ^ 2 * S ^ 2 * uBar ^ 2 <
        4 * p.μ * B ^ 2 := by
    have hsquare :
        (p.χ₀ * (p.ν * (S * uBar))) ^ 2 <
          (2 * Real.sqrt p.μ * B) ^ 2 := by
      nlinarith [sq_nonneg
        (2 * Real.sqrt p.μ * B - p.χ₀ * (p.ν * (S * uBar)))]
    nlinarith [hsqrtSq]
  have hD : 0 < 4 * p.μ * B ^ 2 :=
    mul_pos (mul_pos (by norm_num) p.hμ) (sq_pos_of_pos hB)
  have huSq : 0 < uBar ^ 2 := sq_pos_of_pos huBar
  have hquot :
      p.χ₀ ^ 2 * p.ν ^ 2 * S ^ 2 / (4 * p.μ * B ^ 2) <
        1 / uBar ^ 2 := by
    exact (div_lt_div_iff₀ hD huSq).2 (by simpa using hsq)
  have huNegTwo : uBar ^ (-2 : ℝ) = 1 / uBar ^ 2 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg huBar.le, Real.rpow_two]
    rw [one_div]
  unfold minimal1EntropyCoefficient
  rw [huNegTwo]
  dsimp [S, B] at hquot ⊢
  exact mul_pos (div_pos huStar (by norm_num)) (sub_pos.mpr hquot)

#print axioms intervalDomain_minimal_weightedGradient_ge_l2
#print axioms minimal1EntropyCoefficient_pos_of_chi_lt

end

end ShenWork.Paper3
