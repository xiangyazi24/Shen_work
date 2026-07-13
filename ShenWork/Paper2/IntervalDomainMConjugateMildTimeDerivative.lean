/-
  Faithful positive-time derivative and the literal parabolic equation.

  The three actual mild legs are differentiated directly in target time.
  Their generator terms are then identified with the already-proved genuine
  second spatial derivative of the mild slice.  No source-time derivative,
  restart hypothesis, spectral agreement, or classical-solution premise is
  used.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildChemTimeDerivative
import ShenWork.Paper2.IntervalDomainMConjugateMildLogisticTimeDerivative
import ShenWork.Paper2.IntervalFullSemigroupTimeDerivative
import ShenWork.Paper2.IntervalDomainMConjugateMildInteriorC2

open MeasureTheory Filter Set Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainM intervalDomainChemotaxisDivM intervalDomainLaplacian
    intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (intervalConjugateDuhamelMapM chemFluxMLifted)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator)

/-- Direct target-time differentiation of all three faithful mild-equation
legs at a positive interior time and spatial point. -/
theorem conjugateMildM_intervalDomainLift_hasDerivAt_time_expanded
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t < D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun tau : ℝ => intervalDomainLift (D.u tau) x)
      (deriv (fun y : ℝ => deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y) x
        + (-p.χ₀) *
          ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
              (fun z : ℝ => intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (D.u s)) z) y) x)
            + deriv (chemFluxMLifted p (D.u t)) x)
        + ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) z) y) x)
            + logisticLifted p (D.u t) x))
      t := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hinit :=
    intervalFullSemigroupOperator_lift_hasDerivAt_time_secondDeriv_Icc
      hu₀_cont ht hxIcc
  have hchem := conjugateMildM_chemDuhamel_hasDerivAt_time
    D hu₀_bound hu₀_meas ht htT hx
  have hlog := conjugateMildM_logisticDuhamel_hasDerivAt_time
    D hu₀_bound hu₀_meas ht htT hxIcc
  let rhs : ℝ → ℝ := fun tau =>
    intervalFullSemigroupOperator tau (intervalDomainLift u₀) x
      + (-p.χ₀) * (∫ s in (0 : ℝ)..tau,
          intervalConjugateKernelOperator (tau - s)
            (chemFluxMLifted p (D.u s)) x)
      + ∫ s in (0 : ℝ)..tau,
          intervalFullSemigroupOperator (tau - s)
            (logisticLifted p (D.u s)) x
  have hrhs : HasDerivAt rhs
      (deriv (fun y : ℝ => deriv
          (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) y) x
        + (-p.χ₀) *
          ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
              (fun z : ℝ => intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (D.u s)) z) y) x)
            + deriv (chemFluxMLifted p (D.u t)) x)
        + ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) z) y) x)
            + logisticLifted p (D.u t) x)) t := by
    dsimp [rhs]
    exact (hinit.add (hchem.const_mul (-p.χ₀))).add hlog
  have hev :
      (fun tau : ℝ => intervalDomainLift (D.u tau) x) =ᶠ[nhds t] rhs := by
    filter_upwards [Ioo_mem_nhds ht htT] with tau htau
    have hm := D.hmild tau htau.1 htau.2.le ⟨x, hxIcc⟩
    simpa [rhs, intervalDomainLift, hxIcc, intervalConjugateDuhamelMapM] using hm
  exact hev.hasDerivAt_iff.mpr hrhs

/-- The faithful mild solution satisfies the literal parabolic `u` equation
at every positive interior space-time point. -/
theorem conjugateMildM_intervalDomainLift_hasDerivAt_time_pde
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t < D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun tau : ℝ => intervalDomainLift (D.u tau) x)
      (intervalDomainLaplacian (D.u t)
          ⟨x, Set.Ioo_subset_Icc_self hx⟩
        - p.χ₀ * intervalDomainChemotaxisDivM p (D.u t)
          (coupledChemicalConcentration p D.u t)
          ⟨x, Set.Ioo_subset_Icc_self hx⟩
        + D.u t ⟨x, Set.Ioo_subset_Icc_self hx⟩ *
          (p.a - p.b * (D.u t ⟨x, Set.Ioo_subset_Icc_self hx⟩) ^ p.α))
      t := by
  have htime := conjugateMildM_intervalDomainLift_hasDerivAt_time_expanded
    D hu₀_cont hu₀_bound hu₀_meas ht htT hx
  let I₂ : ℝ := deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalFullSemigroupOperator t
      (intervalDomainLift u₀) z) y) x
  let Iker : ℝ := ∫ z, deriv (fun y : ℝ => deriv
    (fun w : ℝ => intervalNeumannFullKernel t w z) y) x *
      intervalDomainLift u₀ z ∂(intervalMeasure 1)
  let C₂ : ℝ := ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalConjugateKernelOperator (t - s)
      (chemFluxMLifted p (D.u s)) z) y) x
  let R₂ : ℝ := ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalFullSemigroupOperator (t - s)
      (logisticLifted p (D.u s)) z) y) x
  let Qx : ℝ := deriv (chemFluxMLifted p (D.u t)) x
  let Lx : ℝ := logisticLifted p (D.u t) x
  let U₂ : ℝ := deriv
    (fun y : ℝ => deriv (intervalDomainLift (D.u t)) y) x
  change HasDerivAt _ (I₂ + (-p.χ₀) * (C₂ + Qx) + (R₂ + Lx)) t at htime
  have hinit₂ :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_deriv_fst
      ht hu₀_meas hu₀_bound x
  have hI₂ : I₂ = Iker := by
    simpa [I₂, Iker] using hinit₂.deriv
  have hspace := conjugateMildM_intervalDomainLift_deriv_hasDerivAt_interior
    D hu₀_bound hu₀_meas ht htT.le hx
  have hU₂ : U₂ = Iker + (-p.χ₀) * C₂ + R₂ := by
    simpa [U₂, Iker, C₂, R₂] using hspace.deriv
  have hQx : Qx = intervalDomainChemotaxisDivM p (D.u t)
      (coupledChemicalConcentration p D.u t)
      ⟨x, Set.Ioo_subset_Icc_self hx⟩ := by
    dsimp [Qx]
    calc
      deriv (chemFluxMLifted p (D.u t)) x =
          conjugateMildMChemDivJointRep p D.u t x :=
        deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
          D hu₀_bound hu₀_meas ht htT.le hx
      _ = intervalDomainChemotaxisDivM p (D.u t)
          (coupledChemicalConcentration p D.u t)
          ⟨x, Set.Ioo_subset_Icc_self hx⟩ :=
        (intervalDomainMChemotaxisDiv_eq_conjugateMildMChemDivJointRep_interior
          D hu₀_bound hu₀_meas ht htT.le hx).symm
  have hLx : Lx = D.u t ⟨x, Set.Ioo_subset_Icc_self hx⟩ *
      (p.a - p.b * (D.u t ⟨x, Set.Ioo_subset_Icc_self hx⟩) ^ p.α) := by
    simp [Lx, logisticLifted, intervalLogisticSource,
      intervalDomainLift, Set.Ioo_subset_Icc_self hx]
  have hUlap : U₂ = intervalDomainLaplacian (D.u t)
      ⟨x, Set.Ioo_subset_Icc_self hx⟩ := by
    rfl
  have hcoef :
      I₂ + (-p.χ₀) * (C₂ + Qx) + (R₂ + Lx) =
        intervalDomainLaplacian (D.u t)
            ⟨x, Set.Ioo_subset_Icc_self hx⟩
          - p.χ₀ * intervalDomainChemotaxisDivM p (D.u t)
            (coupledChemicalConcentration p D.u t)
            ⟨x, Set.Ioo_subset_Icc_self hx⟩
          + D.u t ⟨x, Set.Ioo_subset_Icc_self hx⟩ *
            (p.a - p.b *
              (D.u t ⟨x, Set.Ioo_subset_Icc_self hx⟩) ^ p.α) := by
    rw [hI₂]
    calc
      Iker + (-p.χ₀) * (C₂ + Qx) + (R₂ + Lx) =
          (Iker + (-p.χ₀) * C₂ + R₂) +
            (-p.χ₀) * Qx + Lx := by ring
      _ = U₂ + (-p.χ₀) * Qx + Lx := by rw [← hU₂]
      _ = _ := by rw [hUlap, hQx, hLx]; ring
  exact htime.congr_deriv hcoef

/-- Pointwise derivative form of the literal `u` equation on the subtype
domain. -/
theorem conjugateMildM_timeDeriv_eq_pde_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t < D.T)
    {X : intervalDomainPoint} (hX : X.1 ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun tau : ℝ => D.u tau X) t =
      intervalDomainLaplacian (D.u t) X
        - p.χ₀ * intervalDomainChemotaxisDivM p (D.u t)
          (coupledChemicalConcentration p D.u t) X
        + D.u t X * (p.a - p.b * (D.u t X) ^ p.α) := by
  have hmain := conjugateMildM_intervalDomainLift_hasDerivAt_time_pde
    D hu₀_cont hu₀_bound hu₀_meas ht htT hX
  have hfun : (fun tau : ℝ => D.u tau X) =
      fun tau : ℝ => intervalDomainLift (D.u tau) X.1 := by
    funext tau
    simp [intervalDomainLift]
  rw [hfun]
  simpa using hmain.deriv

/-- `BoundedDomainData.timeDeriv` form consumed by the classical-solution
assembly. -/
theorem conjugateMildM_intervalDomainM_pde_u
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t < D.T)
    {X : intervalDomainPoint} (hX : X ∈ intervalDomainM.inside) :
    intervalDomainM.timeDeriv D.u t X =
      intervalDomainM.laplacian (D.u t) X
        - p.χ₀ * intervalDomainM.chemotaxisDiv p (D.u t)
          (coupledChemicalConcentration p D.u t) X
        + D.u t X * (p.a - p.b * (D.u t X) ^ p.α) := by
  change deriv (fun tau : ℝ => D.u tau X) t = _
  exact conjugateMildM_timeDeriv_eq_pde_interior
    D hu₀_cont hu₀_bound hu₀_meas ht htT hX

section AxiomAudit

#print axioms conjugateMildM_intervalDomainLift_hasDerivAt_time_pde
#print axioms conjugateMildM_intervalDomainM_pde_u

end AxiomAudit

end ShenWork.Paper2
