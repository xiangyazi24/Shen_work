/-
  Closed-space positive-time derivative of the faithful mild solution.

  At spatial endpoints the chemotaxis source trace is kept as the continuous
  physical representative `conjugateMildChemDivJointRep`; it is not replaced
  by the ordinary derivative of the zero-extended flux.
-/
import ShenWork.Paper2.IntervalConjugateMildChemTimeDerivativeClosed
import ShenWork.Paper2.IntervalConjugateMildLogisticTimeDerivative
import ShenWork.Paper2.IntervalFullSemigroupTimeDerivative

open MeasureTheory Filter Set Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)

/-- The closed-space representative of the positive-time derivative of the
faithful mild solution.  On the open spatial interval it agrees with the
literal parabolic right-hand side; at the endpoints it records the continuous
trace selected by the Duhamel formula. -/
def conjugateMildTimeDerivJointRep
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀) (t x : ℝ) : ℝ :=
  deriv (fun y : ℝ ↦ deriv
      (fun z : ℝ ↦
        intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y) x
    + (-p.χ₀) *
      ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ ↦ deriv
          (fun z : ℝ ↦ intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p (D.u s)) z) y) x)
        + conjugateMildChemDivJointRep p D.u t x)
    + ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ ↦ deriv
          (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) z) y) x)
        + logisticLifted p (D.u t) x)

/-- Direct target-time differentiation of all three faithful mild-equation
legs at every point of the closed physical interval. -/
theorem conjugateMild_intervalDomainLift_hasDerivAt_time_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t < D.T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun tau : ℝ ↦ intervalDomainLift (D.u tau) x)
      (conjugateMildTimeDerivJointRep D t x) t := by
  have hinit :=
    intervalFullSemigroupOperator_lift_hasDerivAt_time_secondDeriv_Icc
      hu₀_cont ht hx
  have hchem := conjugateMild_chemDuhamel_hasDerivAt_time_Icc
    D hu₀_bound hu₀_meas ht htT hx
  have hlog := conjugateMild_logisticDuhamel_hasDerivAt_time
    D hu₀_bound hu₀_meas ht htT hx
  let rhs : ℝ → ℝ := fun tau ↦
    intervalFullSemigroupOperator tau (intervalDomainLift u₀) x
      + (-p.χ₀) * (∫ s in (0 : ℝ)..tau,
          intervalConjugateKernelOperator (tau - s)
            (chemFluxLifted p (D.u s)) x)
      + ∫ s in (0 : ℝ)..tau,
          intervalFullSemigroupOperator (tau - s)
            (logisticLifted p (D.u s)) x
  have hrhs : HasDerivAt rhs (conjugateMildTimeDerivJointRep D t x) t := by
    dsimp [rhs, conjugateMildTimeDerivJointRep]
    exact (hinit.add (hchem.const_mul (-p.χ₀))).add hlog
  have hev :
      (fun tau : ℝ ↦ intervalDomainLift (D.u tau) x) =ᶠ[nhds t] rhs := by
    filter_upwards [Ioo_mem_nhds ht htT] with tau htau
    have hm := D.hmild tau htau.1 htau.2.le ⟨x, hx⟩
    simpa [rhs, intervalDomainLift, hx, intervalConjugateDuhamelMap] using hm
  exact hev.hasDerivAt_iff.mpr hrhs

section AxiomAudit

#print axioms conjugateMild_intervalDomainLift_hasDerivAt_time_Icc

end AxiomAudit

end ShenWork.Paper2
