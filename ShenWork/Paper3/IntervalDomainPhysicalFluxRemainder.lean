/- Physical realization and quadratic bound for the eliminated flux remainder. -/
import ShenWork.Paper3.IntervalDomainChemotaxisRemainderMode

namespace ShenWork.Paper3

open Set Real
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalDomain

noncomputable section

/-- The physical faithful flux minus its eliminated linear part is literally
the scalar eliminated flux remainder. -/
theorem paper3ChemFluxRemainderProfileM_eq_eliminated
    (p : CM2Params) (uStar vStar : ℝ)
    (u v : intervalDomainPoint → ℝ)
    {x : ℝ} (_hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hv_nonneg : 0 ≤ intervalDomainLift v x) :
    paper3ChemFluxRemainderProfileM p uStar vStar u v x =
      paper3EliminatedFluxRemainder
        ((intervalDomainLift u x) ^ p.m) (uStar ^ p.m)
        (paper3SensitivityFactor p.β (intervalDomainLift v x))
        (paper3SensitivityFactor p.β vStar)
        (deriv (intervalDomainLift v) x)
        (paper3LinearSignalGradient p uStar u x) := by
  have hvbase : 0 < 1 + intervalDomainLift v x := by linarith
  unfold paper3ChemFluxRemainderProfileM
    paper3LinearChemFluxProfile intervalFluxM
    paper3EliminatedFluxRemainder paper3EliminatedFluxValue
    paper3EliminatedLinearFluxValue paper3SensitivityFactor
  rw [Real.rpow_neg hvbase.le]
  ring

/-- Along a classical solution, the exact three-term expansion uses the
physical gradient split `grad(v-vStar)=grad Z1+grad Z2`. -/
theorem solution_paper3ChemFluxRemainderProfileM_eq_threeTerms
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit : IntervalSolutionSignalSplitData p uStar (u t))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    paper3ChemFluxRemainderProfileM
        p uStar vStar (u t) (v t) x =
      (((intervalDomainLift (u t) x) ^ p.m - uStar ^ p.m) *
          paper3SensitivityFactor p.β vStar *
            paper3LinearSignalGradient p uStar (u t) x) +
      ((intervalDomainLift (u t) x) ^ p.m *
          paper3SensitivityFactor p.β vStar *
            paper3QuadraticSignalGradient p uStar (u t) x) +
      ((intervalDomainLift (u t) x) ^ p.m *
          (paper3SensitivityFactor p.β (intervalDomainLift (v t) x) -
            paper3SensitivityFactor p.β vStar) *
          deriv (intervalDomainLift (v t)) x) := by
  have hv_nonneg : 0 ≤ intervalDomainLift (v t) x := by
    simpa [intervalDomainLift, hx] using
      (hsol.v_nonneg (t := t)
        (x := (⟨x, hx⟩ : intervalDomainPoint)) ht.1 ht.2)
  rw [paper3ChemFluxRemainderProfileM_eq_eliminated
    p uStar vStar (u t) (v t) hx hv_nonneg]
  apply paper3EliminatedFluxRemainder_eq
  exact solution_lift_v_deriv_eq_signalGradientComponents
    hsol ht heq Hsplit hx

/-- Direct pointwise quadratic estimate for the physical flux remainder.  All
constants are supplied by the local power/sensitivity and resolved-signal
bounds; the exact physical gradient split is discharged above. -/
theorem solution_paper3ChemFluxRemainderProfileM_quadratic
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit : IntervalSolutionSignalSplitData p uStar (u t))
    (H : EliminatedFluxQuadraticBounds)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (huDiff :
      |(intervalDomainLift (u t) x) ^ p.m - uStar ^ p.m| ≤ H.Cu * H.M)
    (hu : |(intervalDomainLift (u t) x) ^ p.m| ≤ H.U)
    (hqDiff :
      |paper3SensitivityFactor p.β (intervalDomainLift (v t) x) -
          paper3SensitivityFactor p.β vStar| ≤ H.Cq * (H.Cz * H.L))
    (hzGrad : |deriv (intervalDomainLift (v t)) x| ≤ H.CzGrad * H.L)
    (hz1Grad :
      |paper3LinearSignalGradient p uStar (u t) x| ≤ H.Cz1Grad * H.L)
    (hz2Grad :
      |paper3QuadraticSignalGradient p uStar (u t) x| ≤
        H.Cz2Grad * H.M * H.L) :
    |paper3ChemFluxRemainderProfileM
        p uStar vStar (u t) (v t) x| ≤
      eliminatedFluxQuadraticConstant H
          (paper3SensitivityFactor p.β vStar) * H.M * H.L := by
  have hv_nonneg : 0 ≤ intervalDomainLift (v t) x := by
    simpa [intervalDomainLift, hx] using
      (hsol.v_nonneg (t := t)
        (x := (⟨x, hx⟩ : intervalDomainPoint)) ht.1 ht.2)
  rw [paper3ChemFluxRemainderProfileM_eq_eliminated
    p uStar vStar (u t) (v t) hx hv_nonneg]
  exact paper3EliminatedFluxRemainder_quadratic H
    (solution_lift_v_deriv_eq_signalGradientComponents
      hsol ht heq Hsplit hx)
    huDiff hu hqDiff hzGrad hz1Grad hz2Grad

#print axioms paper3ChemFluxRemainderProfileM_eq_eliminated
#print axioms solution_paper3ChemFluxRemainderProfileM_eq_threeTerms
#print axioms solution_paper3ChemFluxRemainderProfileM_quadratic

end

end ShenWork.Paper3
