/-
  Faithful classical-solution assembly for the general-m conjugate mild
  solution.  The positive-strip fixed point supplies the genuine joint time
  derivative, while the concrete elliptic resolver supplies the second
  equation and its Neumann boundary condition.
-/
import ShenWork.Paper2.IntervalConjugateMildClassicalRegularityFromJointUT
import ShenWork.Paper2.IntervalDomainMConjugateMildClosedSpatial
import ShenWork.Paper2.IntervalDomainMConjugateMildCoupledJointValue
import ShenWork.Paper2.IntervalDomainMConjugateMildJointTimeDerivativeInterior
import ShenWork.Paper2.IntervalDomainMConjugateMildTimeDerivative

open MeasureTheory Filter Topology Set

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainM intervalMeasure)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalCoupledRegularityBootstrap

/-- The direct general-m mild derivative and its closed-space continuity form
the exact resolver-time datum needed by the elliptic series argument. -/
theorem conjugateMildM_resolverTimeFromJointUTData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ResolverTimeFromJointUTData D.T D.u
      (conjugateMildMTimeDerivJointRep D) := by
  refine
    { jointValue := conjugateMildM_jointValue_u D hu₀_bound hu₀_meas
      jointTimeDeriv :=
        conjugateMildMTimeDerivJointRep_jointContinuousOn
          D hu₀_cont hu₀_bound hu₀_meas
      positive := ?_
      hasTimeDeriv := ?_ }
  · intro t ht x hx
    simp only [intervalDomainLift, hx, dif_pos]
    exact D.hc.trans_le (D.hfloor t ht.1 ht.2.le ⟨x, hx⟩)
  · intro t ht x hx
    exact conjugateMildM_intervalDomainLift_hasDerivAt_time_Icc
      D hu₀_cont hu₀_bound hu₀_meas ht.1 ht.2 hx

/-- Assemble all seven classical-regularity atoms for the faithful general-m
mild solution. -/
theorem conjugateMildM_classicalRegularityAtoms
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    IntervalClassicalRegularityAtoms D.T D.u
      (coupledChemicalConcentration p D.u) := by
  let H := conjugateMildM_resolverTimeFromJointUTData
    D hu₀_cont hu₀_bound hu₀_meas
  have hvTime := H.coupledChemical_timeRegularity (p := p)
  refine
    { interiorC2 := conjugateMildM_coupled_interiorC2 D hu₀_bound hu₀_meas
      timeC1 := ?_
      jointTimeDeriv :=
        ⟨H.u_timeDeriv_jointContinuousOn_interior, hvTime.2.1⟩
      neumannLimits :=
        conjugateMildM_coupled_neumannLimits D hu₀_bound hu₀_meas
      closedC2 := conjugateMildM_coupled_closedC2 D hu₀_bound hu₀_meas
      closedJointTimeDeriv :=
        ⟨H.u_timeDeriv_jointContinuousOn_closed, hvTime.2.2⟩
      jointValue := conjugateMildM_coupled_jointValue D hu₀_bound hu₀_meas }
  intro X t ht
  have huTime := H.u_timeSlices X
  have hvTimeX := hvTime.1 X
  exact ⟨⟨huTime.1 t ht, hvTimeX.1 t ht⟩, ⟨huTime.2, hvTimeX.2⟩⟩

/-- The genuine general-m mild fixed point has the paper's full classical
regularity on its positive lifespan. -/
theorem conjugateMildM_classicalRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    intervalDomainM.classicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u) :=
  intervalDomainClassicalRegularity_of_atoms
    (conjugateMildM_classicalRegularityAtoms
      D hu₀_cont hu₀_bound hu₀_meas)

/-- The faithful positive-strip mild fixed point is a classical solution of
the published general-m parabolic-elliptic system. -/
theorem conjugateMildM_isPaper2ClassicalSolution
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    IsPaper2ClassicalSolution intervalDomainM p D.T D.u
      (coupledChemicalConcentration p D.u) := by
  let A := conjugateMildM_classicalRegularityAtoms
    D hu₀_cont hu₀_bound hu₀_meas
  have hpos : ∀ t x, 0 < t → t < D.T → 0 < D.u t x := by
    intro t x ht htT
    exact D.hc.trans_le (D.hfloor t ht htT.le x)
  refine IsPaper2ClassicalSolution.of_components D.hT
    (intervalDomainClassicalRegularity_of_atoms A) hpos ?_ ?_ ?_ ?_
  · intro t x ht htT
    exact coupledChemical_nonneg p
      (fun s hs hsT y ↦ (hpos s y hs hsT).le)
      (fun s hs hsT ↦ D.hcont s hs hsT.le) ht htT x
  · intro t x ht htT hx
    exact conjugateMildM_intervalDomainM_pde_u
      D hu₀_cont hu₀_bound hu₀_meas ht htT hx
  · intro t x ht htT hx
    exact coupledChemical_ellipticPDE_of_closedC2_neumann p hpos
      (fun s hs hsT ↦ (A.closedC2 s ⟨hs, hsT⟩).1.1)
      (fun s hs hsT ↦ (A.neumannLimits s ⟨hs, hsT⟩).1.1)
      (fun s hs hsT ↦ (A.neumannLimits s ⟨hs, hsT⟩).1.2)
      t x ht htT hx
  · intro t x ht htT hx
    exact coupledChemical_neumannBC_of_closedC2_neumann p hpos
      (fun s hs hsT ↦ (A.closedC2 s ⟨hs, hsT⟩).1.1)
      (fun s hs hsT ↦ (A.neumannLimits s ⟨hs, hsT⟩).1.1)
      (fun s hs hsT ↦ (A.neumannLimits s ⟨hs, hsT⟩).1.2)
      t x ht htT hx

section AxiomAudit

#print axioms conjugateMildM_resolverTimeFromJointUTData
#print axioms conjugateMildM_classicalRegularityAtoms
#print axioms conjugateMildM_classicalRegularity
#print axioms conjugateMildM_isPaper2ClassicalSolution

end AxiomAudit

end ShenWork.Paper2
