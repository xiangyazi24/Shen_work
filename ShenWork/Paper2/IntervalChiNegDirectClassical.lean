import ShenWork.Paper2.IntervalChiNegAssembly
import ShenWork.Paper2.IntervalConjugateMildJointTimeDerivativeInterior
import ShenWork.Paper2.IntervalConjugateMildClassicalRegularityFromJointUT
import ShenWork.Paper2.IntervalDomainTheorem11CorePath
import ShenWork.Paper2.IntervalDuhamelIntegrability

/-!
# Direct classical closure for the faithful chi-negative V6 solution

The truncated zero extension does not have a global closed-endpoint source
`DuhamelSourceTimeC1` package.  After energy and Jensen have produced the full
positive conjugate mild solution, the direct Duhamel differentiation chain
instead gives its genuine closed-space joint time derivative.  This file
packages that derivative and feeds the EWA-free reduced-classical-core route.
-/

open MeasureTheory Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildSolutionData UniformConjugateMildExistenceCore
   uniformConjugateMildExistenceCore_exists)
open ShenWork.IntervalCoupledRegularityBootstrap
  (CoupledDuhamelReducedClassicalCore)

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegAssembly

/-- The direct Duhamel time derivative, together with the already-proved joint
value and positivity fields, supplies the exact resolver-time input package. -/
def conjugateMild_resolverTimeFromJointUTData_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ S.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ShenWork.Paper2.ResolverTimeFromJointUTData S.T S.u
      (ShenWork.Paper2.conjugateMildTimeDerivJointRep S) where
  jointValue :=
    ShenWork.Paper2.conjugateMild_jointValue_u S hu₀_bound hu₀_meas
  jointTimeDeriv :=
    ShenWork.Paper2.conjugateMildTimeDerivJointRep_jointContinuousOn
      S hu₀_cont hu₀_bound hu₀_meas
  positive := by
    intro t ht x hx
    simpa [intervalDomainLift, hx] using S.hpos t ht.1 ht.2.le ⟨x, hx⟩
  hasTimeDeriv := by
    intro t ht x hx
    exact ShenWork.Paper2.conjugateMild_intervalDomainLift_hasDerivAt_time_Icc
      S hu₀_cont hu₀_bound hu₀_meas ht.1 ht.2 hx

/-- A full conjugate mild solution has the reduced classical core directly,
without a global spectral source package. -/
theorem conjugateMild_reducedClassicalCore_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ S.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    (htrace : InitialTrace intervalDomain u₀ S.u) :
    CoupledDuhamelReducedClassicalCore p S.T u₀ S.u :=
  ShenWork.Paper2.conjugateMild_reducedClassicalCore_of_jointUT
    S hu₀_cont hu₀_bound hu₀_meas
      (conjugateMild_resolverTimeFromJointUTData_direct
        S hu₀_cont hu₀_bound hu₀_meas)
      htrace

/-- Energy, Jensen, and the faithful truncated map produce a uniform reduced
classical core for every paper-positive datum. -/
theorem chiNegDatumUniformCore
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : UniformTruncatedAssemblyInputs p) :
    ShenWork.ChiNegDatumUniformCore p := by
  intro M hM
  obtain ⟨T, hT, Huniform⟩ :=
    uniformConjugateMildExistenceCore_exists p hα hγ M hM
  refine ⟨T, hT, ?_⟩
  intro u₀ hu₀ hbound
  have hu₀pos : PositiveInitialDatum intervalDomain u₀ := hu₀.toPositive
  obtain ⟨C, hCT⟩ := Huniform hu₀.admissible.2 hbound
  let A := H.mapCertificate hM hu₀pos hbound C
  let HT :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.uniformTruncatedConjugateMildExistenceCore_of_uniformCore
      C A
  let Henergy := H.energy hM hu₀pos hbound C A
  let HJensen := H.jensenStrictPos hM hu₀pos hbound C
  let S : ConjugateMildSolutionData p u₀ :=
    conjugateMildSolutionData_of_truncatedEnergyJensen
      HT Henergy HJensen
  have htrace : InitialTrace intervalDomain u₀ S.u := by
    simpa [S] using
      initialTrace_of_truncatedEnergyJensen
        hu₀pos HT Henergy HJensen
  have hu₀_bound_lift : ∀ y, |intervalDomainLift u₀ y| ≤ S.M := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · have hbase := C.hbase_ball ⟨y, hy⟩
      have hM0R : C.M0 ≤ C.R := by
        rw [C.hR_eq]
        linarith [C.hM0]
      simpa [S, conjugateMildSolutionData_of_truncatedEnergyJensen,
        intervalDomainLift, hy] using hbase.trans hM0R
    · simp [S, conjugateMildSolutionData_of_truncatedEnergyJensen,
        intervalDomainLift, hy, C.hR.le]
  have hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀.admissible.2
  refine ⟨S.u, ?_⟩
  have hcore := conjugateMild_reducedClassicalCore_direct
    S hu₀.admissible.2 hu₀_bound_lift hu₀_meas htrace
  simpa [S, conjugateMildSolutionData_of_truncatedEnergyJensen, hCT] using hcore

/-- Unconditional chi-negative V6 assembly from its three proved producers.
The former global-source spectral route is retained as
`paper2_chiNeg_spectral`; this theorem is the endpoint-faithful closure. -/
theorem paper2_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (H : UniformTruncatedAssemblyInputs p) :
    Theorem_1_1 intervalDomain p :=
  ShenWork.chiNeg_theorem_1_1_of_uniformCore
    p hχ ha hb hα hγ (chiNegDatumUniformCore p hα hγ H)

#print axioms conjugateMild_resolverTimeFromJointUTData_direct
#print axioms conjugateMild_reducedClassicalCore_direct
#print axioms chiNegDatumUniformCore
#print axioms paper2_chiNeg

end ShenWork.Paper2.IntervalChiNegAssembly
