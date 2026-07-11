/-
  Specialization of the faithful joint-time-derivative assembly to the
  concrete conjugate Picard fixed point.

  The initial-datum bound is derived at the same radius `DB.M` carried by the
  existence data: the zeroth Picard iterate is the heat semigroup, so its ball
  bound passes to the datum through strong continuity at time zero.  No PDE,
  restart, spectral, or classical-regularity premise is added here.
-/
import ShenWork.Paper2.IntervalConjugateMildClassicalRegularityFromJointUT
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalPicardIterateInitialApproach
import ShenWork.Paper2.IntervalDuhamelIntegrability

open MeasureTheory Set
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugateMildSolutionData_of_data
    conjugatePicardIter conjugatePicardLimit)
open ShenWork.IntervalPicardIterateInitialApproach (semigroup_initialApproach)
open ShenWork.IntervalDuhamelIntegrability
  (intervalDomainLift_aestronglyMeasurable_of_continuous)
open ShenWork.IntervalCoupledRegularityBootstrap
  (CoupledDuhamelReducedClassicalCore)

noncomputable section

namespace ShenWork.Paper2

/-- The initial datum is bounded by the exact ball radius carried by the
concrete conjugate Picard existence data. -/
theorem conjugateMildExistenceData_datum_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (DB : ConjugateMildExistenceData p u₀) :
    ∀ x : intervalDomainPoint, |u₀ x| ≤ DB.M := by
  intro x
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨δ, hδ, hδclose⟩ := semigroup_initialApproach p hu₀_cont ε hε
  let t₀ : ℝ := min (δ / 2) DB.T
  have ht₀_pos : 0 < t₀ := lt_min (by linarith) DB.hT
  have ht₀_le_T : t₀ ≤ DB.T := min_le_right _ _
  have ht₀_lt_δ : t₀ < δ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hball := DB.hbase_ball t₀ ht₀_pos ht₀_le_T x
  have hiter :
      conjugatePicardIter p u₀ 0 t₀ x =
        intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1 := rfl
  rw [hiter] at hball
  have hclose := hδclose t₀ ht₀_pos ht₀_lt_δ x
  have htri :
      |u₀ x| ≤
        |u₀ x - intervalFullSemigroupOperator t₀
          (intervalDomainLift u₀) x.1| +
        |intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1| := by
    have := abs_add_le
      (u₀ x - intervalFullSemigroupOperator t₀
        (intervalDomainLift u₀) x.1)
      (intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1)
    simpa using this
  have hclose' :
      |u₀ x - intervalFullSemigroupOperator t₀
        (intervalDomainLift u₀) x.1| < ε := by
    rw [abs_sub_comm]
    exact hclose
  calc
    |u₀ x| ≤
        |u₀ x - intervalFullSemigroupOperator t₀
          (intervalDomainLift u₀) x.1| +
        |intervalFullSemigroupOperator t₀ (intervalDomainLift u₀) x.1| := htri
    _ ≤ ε + DB.M := add_le_add (le_of_lt hclose') hball
    _ = DB.M + ε := by ring

/-- The corresponding globally quantified zero-extension bound.  Outside the
interval the lift is zero, and `DB.hM` supplies the same radius's nonnegativity. -/
theorem conjugateMildExistenceData_lift_datum_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (DB : ConjugateMildExistenceData p u₀) :
    ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ DB.M := by
  intro y
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simpa [intervalDomainLift, hy] using
      (conjugateMildExistenceData_datum_bound hu₀_cont DB ⟨y, hy⟩)
  · simp [intervalDomainLift, hy, DB.hM.le]

/-- The actual conjugate Picard fixed point has the reduced classical core as
soon as its genuine jointly continuous time derivative has been constructed.
All remaining inputs are derived from `DB` and continuity of the original
datum. -/
theorem conjugatePicardLimit_reducedClassicalCore_of_jointUT
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) (DB : ConjugateMildExistenceData p u₀)
    {ut : ℝ → ℝ → ℝ}
    (H : ResolverTimeFromJointUTData DB.T
      (conjugatePicardLimit p u₀ DB.T) ut) :
    CoupledDuhamelReducedClassicalCore p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T) := by
  let D := conjugateMildSolutionData_of_data DB
  have hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M := by
    change ∀ y, |intervalDomainLift u₀ y| ≤ DB.M
    exact conjugateMildExistenceData_lift_datum_bound hu₀_cont DB
  have hu₀_meas :
      AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1) :=
    intervalDomainLift_aestronglyMeasurable_of_continuous hu₀_cont
  have H_D : ResolverTimeFromJointUTData D.T D.u ut := by
    change ResolverTimeFromJointUTData DB.T
      (conjugatePicardLimit p u₀ DB.T) ut
    exact H
  have htrace : InitialTrace intervalDomain u₀ D.u := by
    change InitialTrace intervalDomain u₀
      (conjugatePicardLimit p u₀ DB.T)
    exact BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
      p hu₀_cont DB
  change CoupledDuhamelReducedClassicalCore p D.T u₀ D.u
  exact conjugateMild_reducedClassicalCore_of_jointUT
    D hu₀_cont hu₀_bound hu₀_meas H_D htrace

section AxiomAudit

#print axioms conjugateMildExistenceData_datum_bound
#print axioms conjugateMildExistenceData_lift_datum_bound
#print axioms conjugatePicardLimit_reducedClassicalCore_of_jointUT

end AxiomAudit

end ShenWork.Paper2
