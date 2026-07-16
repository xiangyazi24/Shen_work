/- Physical realization and quadratic bound for the faithful general-`m` flux remainder. -/
import ShenWork.Paper3.IntervalDomainPhysicalFluxRemainder
import ShenWork.Paper3.IntervalDomainSolutionSignalDecompositionGeneralM

namespace ShenWork.Paper3

open Set Real
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalDomain

noncomputable section

/-- Along a faithful `intervalDomainM` classical solution, the exact
three-term expansion uses the resolved physical gradient split. -/
theorem solution_paper3ChemFluxRemainderProfileM_eq_threeTerms_generalM
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
  exact solution_lift_v_deriv_eq_signalGradientComponents_generalM
    hsol ht heq Hsplit hx

/-- The existing scalar eliminated-flux bound applies unchanged to a faithful
general-`m` solution once the local power and signal bounds are supplied. -/
theorem solution_paper3ChemFluxRemainderProfileM_quadratic_generalM
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
    (solution_lift_v_deriv_eq_signalGradientComponents_generalM
      hsol ht heq Hsplit hx)
    huDiff hu hqDiff hzGrad hz1Grad hz2Grad

#print axioms solution_paper3ChemFluxRemainderProfileM_eq_threeTerms_generalM
#print axioms solution_paper3ChemFluxRemainderProfileM_quadratic_generalM

end


end ShenWork.Paper3
