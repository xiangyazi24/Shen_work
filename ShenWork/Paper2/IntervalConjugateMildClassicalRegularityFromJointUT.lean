/-
  Faithful classical-regularity assembly from the genuine joint time
  derivative of the conjugate mild solution.

  The only time-regularity input is `ResolverTimeFromJointUTData`: it records
  a jointly continuous closed-space representative `ut` and proves that this
  representative is the actual time derivative of `u`.  The elliptic time
  regularity is then derived by the resolver series, while all spatial and
  value-continuity fields come from the direct conjugate-mild construction.
-/
import ShenWork.Paper2.IntervalResolverTimeFromJointUT
import ShenWork.Paper2.IntervalConjugateMildClosedSpatial
import ShenWork.Paper2.IntervalConjugateMildCoupledJointValue
import ShenWork.Paper2.IntervalConjugateMildTimeDerivative
import ShenWork.PDE.IntervalCoupledClassicalCorePAR

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

namespace ShenWork.Paper2

/-- The `u`-side time-slice regularity encoded by a genuine closed-space
joint time derivative. -/
theorem ResolverTimeFromJointUTData.u_timeSlices
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut)
    (X : intervalDomainPoint) :
    (∀ t ∈ Set.Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (fun s : ℝ => u s X) t) ∧
    ContinuousOn
      (fun t : ℝ => deriv (fun s : ℝ => u s X) t)
      (Set.Ioo (0 : ℝ) T) := by
  have hfun :
      (fun s : ℝ => intervalDomainLift (u s) X.1) =
        (fun s : ℝ => u s X) := by
    funext s
    simp [intervalDomainLift]
  have hut_cont : ContinuousOn (fun t : ℝ => ut t X.1)
      (Set.Ioo (0 : ℝ) T) := by
    exact H.jointTimeDeriv.comp
      (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => Set.mem_prod.mpr ⟨ht, X.2⟩)
  refine ⟨?_, hut_cont.congr ?_⟩
  · intro t ht
    have hderiv := H.hasTimeDeriv t ht X.1 X.2
    rw [hfun] at hderiv
    exact hderiv.differentiableAt
  · intro t ht
    have hderiv := H.hasTimeDeriv t ht X.1 X.2
    rw [hfun] at hderiv
    exact hderiv.deriv

/-- The literal lifted `u_t` field is jointly continuous up to both spatial
endpoints. -/
theorem ResolverTimeFromJointUTData.u_timeDeriv_jointContinuousOn_closed
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine H.jointTimeDeriv.congr ?_
  intro q hq
  obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
  simpa [Function.uncurry] using
    (H.hasTimeDeriv q.1 ht q.2 hx).deriv

/-- Interior restriction of the genuine lifted `u_t` continuity theorem. -/
theorem ResolverTimeFromJointUTData.u_timeDeriv_jointContinuousOn_interior
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    {ut : ℝ → ℝ → ℝ} (H : ResolverTimeFromJointUTData T u ut) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) :=
  H.u_timeDeriv_jointContinuousOn_closed.mono
    (Set.prod_mono_right Set.Ioo_subset_Icc_self)

/-- Assemble all seven classical-regularity atoms from the faithful mild
solution and its genuine joint time derivative. -/
theorem conjugateMild_classicalRegularityAtoms_of_jointUT
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {ut : ℝ → ℝ → ℝ}
    (H : ResolverTimeFromJointUTData D.T D.u ut) :
    IntervalClassicalRegularityAtoms D.T D.u
      (coupledChemicalConcentration p D.u) := by
  have hvTime := H.coupledChemical_timeRegularity (p := p)
  refine
    { interiorC2 := conjugateMild_coupled_interiorC2 D hu₀_bound hu₀_meas
      timeC1 := ?_
      jointTimeDeriv :=
        ⟨H.u_timeDeriv_jointContinuousOn_interior, hvTime.2.1⟩
      neumannLimits :=
        conjugateMild_coupled_neumannLimits D hu₀_bound hu₀_meas
      closedC2 := conjugateMild_coupled_closedC2 D hu₀_bound hu₀_meas
      closedJointTimeDeriv :=
        ⟨H.u_timeDeriv_jointContinuousOn_closed, hvTime.2.2⟩
      jointValue := conjugateMild_coupled_jointValue D hu₀_bound hu₀_meas }
  intro X t ht
  have huTime := H.u_timeSlices X
  have hvTimeX := hvTime.1 X
  exact ⟨⟨huTime.1 t ht, hvTimeX.1 t ht⟩, ⟨huTime.2, hvTimeX.2⟩⟩

/-- The direct classical-regularity conclusion obtained from the same
faithful atoms. -/
theorem conjugateMild_classicalRegularity_of_jointUT
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {ut : ℝ → ℝ → ℝ}
    (H : ResolverTimeFromJointUTData D.T D.u ut) :
    intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u) :=
  intervalDomainClassicalRegularity_of_atoms
    (conjugateMild_classicalRegularityAtoms_of_jointUT
      D hu₀_cont hu₀_bound hu₀_meas H)

/-- Reduced classical core for the faithful conjugate mild solution.  The
parabolic equation, positivity, and initial trace are consumed from their
direct construction-level producers; no classical/PDE/restart/spectral
premise is carried. -/
theorem conjugateMild_reducedClassicalCore_of_jointUT
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionData p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {ut : ℝ → ℝ → ℝ}
    (H : ResolverTimeFromJointUTData D.T D.u ut)
    (htrace : InitialTrace intervalDomain u₀ D.u) :
    CoupledDuhamelReducedClassicalCore p D.T u₀ D.u := by
  exact coupledDuhamelReducedClassicalCore_of_atoms
    (fun t x ht htT => D.hpos t ht htT.le x)
    (fun t x ht htT hx =>
      conjugateMild_intervalDomain_pde_u
        D hu₀_cont hu₀_bound hu₀_meas ht htT hx)
    (conjugateMild_classicalRegularityAtoms_of_jointUT
      D hu₀_cont hu₀_bound hu₀_meas H)
    htrace

section AxiomAudit

#print axioms ResolverTimeFromJointUTData.u_timeSlices
#print axioms ResolverTimeFromJointUTData.u_timeDeriv_jointContinuousOn_closed
#print axioms conjugateMild_classicalRegularityAtoms_of_jointUT
#print axioms conjugateMild_classicalRegularity_of_jointUT
#print axioms conjugateMild_reducedClassicalCore_of_jointUT

end AxiomAudit

end ShenWork.Paper2
