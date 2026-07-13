/- Exact eliminated-signal decomposition along a legacy interval solution. -/
import ShenWork.Paper3.IntervalDomainConstantResolver
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.PDE
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalResolverWeakBounds

noncomputable section

/-- Common summability/integrability hypotheses for the exact signal split at
one positive-time solution slice. -/
structure IntervalSolutionSignalSplitData
    (p : CM2Params) (uStar : ℝ)
    (w : intervalDomainPoint → ℝ) : Prop where
  linear_integrable : IntervalIntegrable
    (paper3IntervalEllipticLinearProfile p uStar w) volume 0 1
  remainder_integrable : IntervalIntegrable
    (paper3IntervalEllipticRemainderProfile p uStar w) volume 0 1
  source_sq_summable : Summable fun k : ℕ =>
    ((intervalNeumannResolverSourceCoeff p w k).re) ^ 2
  equilibrium_source_sq_summable : Summable fun k : ℕ =>
    ((intervalNeumannResolverSourceCoeff p (fun _ => uStar) k).re) ^ 2
  linear_source_sq_summable : Summable fun k : ℕ =>
    (paper3LinearEllipticSourceCoeffReal p uStar w k) ^ 2
  remainder_source_sq_summable : Summable fun k : ℕ =>
    (paper3QuadraticEllipticSourceCoeffReal p uStar w k) ^ 2

/-- At every interior point, the physical chemical perturbation is exactly the
sum of the resolved linear signal and its nonlinear source correction. -/
theorem solution_lift_v_sub_eq_signalComponents
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (H : IntervalSolutionSignalSplitData p uStar (u t))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift (v t) x - vStar =
      paper3LinearSignalValue p uStar (u t) x +
        paper3QuadraticSignalValue p uStar (u t) x := by
  let xp : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  have hv := solution_v_eq_resolver_pointwise_unconditional hsol ht hx
  have hsplit := paper3IntervalResolver_value_sub_eq_signalComponents
    p uStar (u t) H.linear_integrable H.remainder_integrable
    H.source_sq_summable H.equilibrium_source_sq_summable
    H.linear_source_sq_summable H.remainder_source_sq_summable xp
  have hconst := intervalNeumannResolverR_const_eq_vStar p heq xp
  dsimp [xp] at hv hsplit hconst
  linarith

/-- On the closed interval, the physical chemical gradient is exactly the sum
of the resolved linear and nonlinear gradient components. -/
theorem solution_lift_v_deriv_eq_signalGradientComponents
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (_heq : Paper3ConstantEquilibrium p uStar vStar)
    (H : IntervalSolutionSignalSplitData p uStar (u t))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (intervalDomainLift (v t)) x =
      paper3LinearSignalGradient p uStar (u t) x +
        paper3QuadraticSignalGradient p uStar (u t) x := by
  let xp : intervalDomainPoint := ⟨x, hx⟩
  have hvgrad := solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hx
  rw [resolverGradReal_eq p (u t) xp] at hvgrad
  have hsplit := paper3IntervalResolver_gradient_sub_eq_signalComponents
    p uStar (u t) H.linear_integrable H.remainder_integrable
    H.source_sq_summable H.equilibrium_source_sq_summable
    H.linear_source_sq_summable H.remainder_source_sq_summable xp
  have hconst := intervalNeumannResolverRGrad_const p uStar xp
  dsimp [xp] at hvgrad hsplit hconst
  linarith

#print axioms solution_lift_v_sub_eq_signalComponents
#print axioms solution_lift_v_deriv_eq_signalGradientComponents

end

end ShenWork.Paper3
