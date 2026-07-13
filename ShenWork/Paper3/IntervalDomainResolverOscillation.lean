/-
# Oscillation control for the unit-interval elliptic resolver

This is the concrete form of Paper 3, Lemma 7.1 needed by the rectangle
argument.  The constant mode is removed by subtracting the constant lower
envelope.  Cosine--Bessel controls the remaining source coefficients and the
already proved diagonal-resolver estimate controls the gradient.

No abstract `Paper3Constants` field is used.
-/
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper3.IntervalDomainConstantResolver

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain ShenWork.PDE
open ShenWork.PDE.ResolventEstimate
open ShenWork.IntervalResolverWeakBounds
open ShenWork.Paper2
open scoped BigOperators

namespace ShenWork.Paper3

noncomputable section

/-- The concrete coefficient-space constant in the interval resolver estimate
`|d/dx R(u)| <= C * nu * (uMax^gamma-uMin^gamma)`. -/
def unitIntervalResolverGradientOscillationConstant (p : CM2Params) : ℝ :=
  2 * Real.sqrt
    (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2)

theorem unitIntervalResolverGradientOscillationConstant_nonneg
    (p : CM2Params) :
    0 ≤ unitIntervalResolverGradientOscillationConstant p := by
  unfold unitIntervalResolverGradientOscillationConstant
  positivity

/-- The normalized constant used in the Paper 3 rectangle system.  With
`V = v/vStar`, the physical estimate becomes
`|V_x| <= M0 * sqrt(mu) * (Umax^gamma-Umin^gamma)`. -/
def unitIntervalNormalizedResolverGradientConstant (p : CM2Params) : ℝ :=
  Real.sqrt p.μ * unitIntervalResolverGradientOscillationConstant p

theorem unitIntervalNormalizedResolverGradientConstant_nonneg
    (p : CM2Params) :
    0 ≤ unitIntervalNormalizedResolverGradientConstant p := by
  unfold unitIntervalNormalizedResolverGradientConstant
  exact mul_nonneg (Real.sqrt_nonneg _) <|
    unitIntervalResolverGradientOscillationConstant_nonneg p

private theorem constant_lift_continuousOn (c : ℝ) :
    ContinuousOn (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (Set.Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun _ : ℝ => c) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const
  refine hc.congr ?_
  intro x hx
  simp [intervalDomainLift, hx]

/-- Direct cosine--Bessel estimate after subtracting a constant lower
envelope.  Unlike the local Lipschitz estimate, this retains the exact power
oscillation `uMax^gamma-uMin^gamma` and therefore the paper's threshold.
-/
theorem source_coeffL2Norm_le_power_oscillation
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {uMin uMax : ℝ}
    (huMin : 0 ≤ uMin)
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hlo : ∀ x ∈ Set.Icc (0 : ℝ) 1, uMin ≤ intervalDomainLift u x)
    (hhi : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u x ≤ uMax) :
    coeffL2Norm
        (fun k : ℕ => intervalNeumannResolverSourceCoeff p u k -
          intervalNeumannResolverSourceCoeff p (fun _ => uMin) k)
      ≤ 2 * (p.ν * (uMax ^ p.γ - uMin ^ p.γ)) := by
  let u0 : intervalDomainPoint → ℝ := fun _ => uMin
  have hU0cont : ContinuousOn (intervalDomainLift u0) (Set.Icc (0 : ℝ) 1) :=
    constant_lift_continuousOn uMin
  have hsrcCont : ContinuousOn
      (fun x : ℝ => p.ν * intervalDomainLift u x ^ p.γ)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul
      (hUcont.rpow_const (fun _ _ => Or.inr p.hγ.le))
  have hsrc0Cont : ContinuousOn
      (fun x : ℝ => p.ν * intervalDomainLift u0 x ^ p.γ)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.mul
      (hU0cont.rpow_const (fun _ _ => Or.inr p.hγ.le))
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have huMax : 0 ≤ uMax := le_trans huMin <| le_trans (hlo 0 h0mem) (hhi 0 h0mem)
  have hgap : 0 ≤ uMax ^ p.γ - uMin ^ p.γ := by
    exact sub_nonneg.mpr <| Real.rpow_le_rpow huMin
      (le_trans (hlo 0 h0mem) (hhi 0 h0mem)) p.hγ.le
  let L : ℝ := p.ν * (uMax ^ p.γ - uMin ^ p.γ)
  have hL : 0 ≤ L := mul_nonneg p.hν.le hgap
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (p.ν * intervalDomainLift u x ^ p.γ -
          p.ν * intervalDomainLift u0 x ^ p.γ) ^ 2 ≤ L ^ 2 := by
    intro x hx
    have hu0 : intervalDomainLift u0 x = uMin := by
      simp [u0, intervalDomainLift, hx]
    have hux0 : 0 ≤ intervalDomainLift u x := huMin.trans (hlo x hx)
    have hpLo : uMin ^ p.γ ≤ intervalDomainLift u x ^ p.γ :=
      Real.rpow_le_rpow huMin (hlo x hx) p.hγ.le
    have hpHi : intervalDomainLift u x ^ p.γ ≤ uMax ^ p.γ :=
      Real.rpow_le_rpow hux0 (hhi x hx) p.hγ.le
    have hdiff0 : 0 ≤ p.ν * intervalDomainLift u x ^ p.γ -
        p.ν * intervalDomainLift u0 x ^ p.γ := by
      rw [hu0]
      exact sub_nonneg.mpr <| mul_le_mul_of_nonneg_left hpLo p.hν.le
    have hdiffL : p.ν * intervalDomainLift u x ^ p.γ -
        p.ν * intervalDomainLift u0 x ^ p.γ ≤ L := by
      rw [hu0]
      dsimp [L]
      nlinarith [mul_le_mul_of_nonneg_left hpHi p.hν.le]
    nlinarith
  have hsqCont : ContinuousOn
      (fun x : ℝ =>
        (p.ν * intervalDomainLift u x ^ p.γ -
          p.ν * intervalDomainLift u0 x ^ p.γ) ^ 2)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hsrcCont.sub hsrc0Cont).pow 2
  have hInt :
      (∫ x in (0 : ℝ)..1,
        (p.ν * intervalDomainLift u x ^ p.γ -
          p.ν * intervalDomainLift u0 x ^ p.γ) ^ 2) ≤ L ^ 2 := by
    have hconstInt : IntervalIntegrable (fun _ : ℝ => L ^ 2) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (by norm_num)
      hsqCont.intervalIntegrable hconstInt hpoint
    simpa using hmono
  have henergy := sourceCoeff_diff_energy_le_integral_of_continuousOn
    p hsrcCont hsrc0Cont
  rw [coeffL2Norm]
  have henergy' :
      coeffL2Energy
          (fun k : ℕ => intervalNeumannResolverSourceCoeff p u k -
            intervalNeumannResolverSourceCoeff p u0 k) ≤ (2 * L) ^ 2 := by
    calc
      coeffL2Energy
          (fun k : ℕ => intervalNeumannResolverSourceCoeff p u k -
            intervalNeumannResolverSourceCoeff p u0 k)
          ≤ 4 * ∫ x in (0 : ℝ)..1,
              (p.ν * intervalDomainLift u x ^ p.γ -
                p.ν * intervalDomainLift u0 x ^ p.γ) ^ 2 := henergy
      _ ≤ 4 * L ^ 2 := mul_le_mul_of_nonneg_left hInt (by norm_num)
      _ = (2 * L) ^ 2 := by ring
  calc
    Real.sqrt
        (coeffL2Energy
          (fun k : ℕ => intervalNeumannResolverSourceCoeff p u k -
            intervalNeumannResolverSourceCoeff p (fun _ => uMin) k))
        ≤ Real.sqrt ((2 * L) ^ 2) := by
          simpa [u0] using Real.sqrt_le_sqrt henergy'
    _ = 2 * L := by rw [Real.sqrt_sq (by positivity)]
    _ = 2 * (p.ν * (uMax ^ p.γ - uMin ^ p.γ)) := rfl

/-- Concrete unit-interval version of Paper 3, Lemma 7.1. -/
theorem intervalDomain_resolverGradient_abs_le_power_oscillation
    (p : CM2Params) {u : intervalDomainPoint → ℝ} {uMin uMax x : ℝ}
    (huMin : 0 ≤ uMin)
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hlo : ∀ y ∈ Set.Icc (0 : ℝ) 1, uMin ≤ intervalDomainLift u y)
    (hhi : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u y ≤ uMax)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |resolverGradReal p u x| ≤
      unitIntervalResolverGradientOscillationConstant p *
        (p.ν * (uMax ^ p.γ - uMin ^ p.γ)) := by
  let u0 : intervalDomainPoint → ℝ := fun _ => uMin
  have hU0cont : ContinuousOn (intervalDomainLift u0) (Set.Icc (0 : ℝ) 1) :=
    constant_lift_continuousOn uMin
  have hsrc := resolverSourceCoeff_diff_re_sq_summable_of_continuousOn
    p hUcont hU0cont
  have hl2u : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
  have hl2u0 : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u0 k).re) ^ 2 := by
    simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
      resolverSourceCoeff_re_sq_summable_of_continuousOn p hU0cont
  have hsumu := resolver_sineSeries_summable_of_sourceL2 p hl2u x
  have hsumu0 := resolver_sineSeries_summable_of_sourceL2 p hl2u0 x
  have hgrad := intervalNeumannResolverR_grad_sup_lipschitz
    p u u0 hsrc ⟨x, hx⟩ hsumu hsumu0
  have hu0grad : resolverGradReal p u0 x = 0 := by
    rw [resolverGradReal_eq p u0 ⟨x, hx⟩]
    exact intervalNeumannResolverRGrad_const p uMin ⟨x, hx⟩
  rw [← resolverGradReal_eq p u ⟨x, hx⟩,
    ← resolverGradReal_eq p u0 ⟨x, hx⟩, hu0grad, sub_zero] at hgrad
  refine hgrad.trans ?_
  have hcoeff := source_coeffL2Norm_le_power_oscillation
    p huMin hUcont hlo hhi
  unfold unitIntervalResolverGradientOscillationConstant
  calc
    Real.sqrt
          (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        coeffL2Norm
          (fun k : ℕ => intervalNeumannResolverSourceCoeff p u k -
            intervalNeumannResolverSourceCoeff p u0 k)
      ≤ Real.sqrt
          (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * (uMax ^ p.γ - uMin ^ p.γ))) :=
        mul_le_mul_of_nonneg_left (by simpa [u0] using hcoeff)
          (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt
          (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
            (p.ν * (uMax ^ p.γ - uMin ^ p.γ)) := by ring

#print axioms source_coeffL2Norm_le_power_oscillation
#print axioms intervalDomain_resolverGradient_abs_le_power_oscillation

end

end ShenWork.Paper3
