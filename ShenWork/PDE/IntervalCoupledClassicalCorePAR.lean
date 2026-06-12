import ShenWork.PDE.IntervalCoupledClassicalCoreDischarge
import ShenWork.PDE.IntervalChemDivTimeDerivative
import ShenWork.PDE.IntervalProfileBoundaryRegularity
import ShenWork.PDE.IntervalSemigroupNeumann

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalFullKernelRegularity
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalSemigroupNeumann
open ShenWork.Paper2
open ShenWork.PDE.IntervalMildSourceDecayHelper

/-- The seven explicit conjuncts of `intervalDomainClassicalRegularity`.
This is the PAR decomposition of the `classicalRegularity` field. -/
structure IntervalClassicalRegularityAtoms
    (T : ℝ) (u v : ℝ → intervalDomainPoint → ℝ) : Prop where
  interiorC2 :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Ioo (0 : ℝ) 1) ∧
        ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0 : ℝ) 1)
  timeC1 :
    ∀ x : intervalDomainPoint, ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      (DifferentiableAt ℝ (fun s : ℝ => u s x) t ∧
          DifferentiableAt ℝ (fun s : ℝ => v s x) t) ∧
        (ContinuousOn (fun s : ℝ => deriv (fun r : ℝ => u r x) s)
            (Set.Ioo (0 : ℝ) T) ∧
          ContinuousOn (fun s : ℝ => deriv (fun r : ℝ => v r x) s)
            (Set.Ioo (0 : ℝ) T))
  jointTimeDeriv :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (v s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1)
  neumannLimits :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      (Filter.Tendsto (deriv (intervalDomainLift (u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (deriv (intervalDomainLift (u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) ∧
      (Filter.Tendsto (deriv (intervalDomainLift (v t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (deriv (intervalDomainLift (v t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
  closedC2 :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      (ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) ∧
          deriv (intervalDomainLift (u t)) 0 = 0 ∧
          deriv (intervalDomainLift (u t)) 1 = 0) ∧
        (ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) ∧
          deriv (intervalDomainLift (v t)) 0 = 0 ∧
          deriv (intervalDomainLift (v t)) 1 = 0)
  closedJointTimeDeriv :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift (v s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  jointValue :
    ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)

theorem intervalDomainClassicalRegularity_of_atoms
    {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (A : IntervalClassicalRegularityAtoms T u v) :
    intervalDomainClassicalRegularity T u v := by
  exact ⟨A.interiorC2, A.timeC1, A.jointTimeDeriv, A.neumannLimits,
    A.closedC2, A.closedJointTimeDeriv, A.jointValue⟩

theorem coupledDuhamelReducedClassicalCore_of_atoms
    {p : CM2Params} {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hu_pos : ∀ t x, 0 < t → t < T → 0 < u t x)
    (hpde : ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
              (coupledChemicalConcentration p u t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α))
    (A : IntervalClassicalRegularityAtoms T u (coupledChemicalConcentration p u))
    (htrace : InitialTrace intervalDomain u₀ u) :
    CoupledDuhamelReducedClassicalCore p T u₀ u := by
  refine
    { u_pos := hu_pos
      pde_u := hpde
      classicalRegularity := intervalDomainClassicalRegularity_of_atoms A
      initialTrace := htrace }

/-- Closed spatial regularity and Neumann data for a homogeneous heat slice. -/
theorem homogeneousProfile_closedC2_neumann
    {t : ℝ} {f : ℝ → ℝ} {M : ℝ} {w : intervalDomainPoint → ℝ}
    (ht : 0 < t) (hf : Continuous f)
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    (hEq : Set.EqOn (intervalDomainLift w)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) *
            Real.cos ((m : ℝ) * Real.pi * y))) :
    ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) ∧
      Filter.Tendsto (deriv (intervalDomainLift w))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (intervalDomainLift w))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) ∧
      deriv (intervalDomainLift w) 0 = 0 ∧
      deriv (intervalDomainLift w) 1 = 0 := by
  let S : ℝ → ℝ := fun x => intervalFullSemigroupOperator t f x
  have hS2 : ContDiff ℝ 2 S :=
    intervalFullSemigroupOperator_contDiff_two_unconditional t ht f hf hM hkernel
  have hS1 : ContDiff ℝ 1 S := hS2.of_le (by norm_num)
  have hS0 : deriv S 0 = 0 := by
    simpa [S] using
      intervalFullSemigroupOperator_neumann_at_zero ht hf hM
  have hS1end : deriv S 1 = 0 := by
    simpa [S] using
      intervalFullSemigroupOperator_neumann_at_one ht hf hM
  exact
    ⟨intervalFullSemigroupProfile_contDiffOn_two_closed ht hf hM hEq hkernel,
      neumann_limit_left_of_eqOn_C1 hS1 hS0 hEq,
      neumann_limit_right_of_eqOn_C1 hS1 hS1end hEq,
      deriv_intervalDomainLift_eq_zero_at_zero w,
      deriv_intervalDomainLift_eq_zero_at_one w⟩

/-- Closed spatial regularity and Neumann data for a spectral Duhamel slice
whose source coefficients satisfy the time-`C¹` package. -/
theorem duhamelProfile_closedC2_neumann_of_timeC1_source
    {t : ℝ} {a : ℝ → ℕ → ℝ} {w : intervalDomainPoint → ℝ}
    (src : DuhamelSourceTimeC1 a) (ht : 0 < t)
    (hEq : Set.EqOn (intervalDomainLift w)
      (fun x => ∫ s in (0 : ℝ)..t,
        unitIntervalCosineHeatValue (t - s) (a s) x)
      (Set.Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) ∧
      Filter.Tendsto (deriv (intervalDomainLift w))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (intervalDomainLift w))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) ∧
      deriv (intervalDomainLift w) 0 = 0 ∧
      deriv (intervalDomainLift w) 1 = 0 := by
  let S : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..t,
    unitIntervalCosineHeatValue (t - s) (a s) x
  have hpack := intervalDuhamelTerm_closedC2_of_timeC1_source src ht
  have hS2 : ContDiff ℝ 2 S := hpack.1
  have hS1 : ContDiff ℝ 1 S := hS2.of_le (by norm_num)
  exact
    ⟨intervalDomainLift_profile_contDiffOn_two_closed hS2 hEq,
      neumann_limit_left_of_eqOn_C1 hS1 hpack.2.1 hEq,
      neumann_limit_right_of_eqOn_C1 hS1 hpack.2.2.1 hEq,
      deriv_intervalDomainLift_eq_zero_at_zero w,
      deriv_intervalDomainLift_eq_zero_at_one w⟩

/-- Coupled-source specialization of the Duhamel closed-C2/Neumann slice. -/
theorem duhamelProfile_closedC2_neumann_of_coupledChemicalSource
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {t : ℝ} {w : intervalDomainPoint → ℝ}
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    (hcoeffSplit : coupledChemicalSourceCoeffs p u =
      fun s n => -(p.χ₀ * coupledChemDivSourceCoeffs p u s n)
        + coupledLogisticSourceCoeffs p u s n)
    (hchem : CoupledChemDivTimeC1Fields p u)
    (ht : 0 < t)
    (hEq : Set.EqOn (intervalDomainLift w)
      (fun x => ∫ s in (0 : ℝ)..t,
        unitIntervalCosineHeatValue (t - s)
          (coupledChemicalSourceCoeffs p u s) x)
      (Set.Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) ∧
      Filter.Tendsto (deriv (intervalDomainLift w))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (intervalDomainLift w))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) ∧
      deriv (intervalDomainLift w) 0 = 0 ∧
      deriv (intervalDomainLift w) 1 = 0 := by
  have hchemSrc : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) :=
    coupledChemDivSource_timeC1_of_fields hchem
  exact duhamelProfile_closedC2_neumann_of_timeC1_source
    (coupledChemicalSource_duhamelSourceTimeC1 hlog hchemSrc hcoeffSplit)
    ht hEq

end ShenWork.IntervalCoupledRegularityBootstrap
