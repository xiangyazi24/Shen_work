import ShenWork.Paper2.IntervalConjugatePicardFloorCoreInhabit
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalChiNegDirectClassical
import ShenWork.Paper2.IntervalDomainQuantFromThreshold

/-!
# Paper-positive local existence for all positive exponents
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalConjugatePicard
open ShenWork.Paper2.IntervalChiNegAssembly

/-- Upgrade any inhabited positive-floor Picard datum to a classical solution
at its explicit horizon. -/
theorem intervalDomain_classicalSolution_of_floorData_allExponents
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (D : ConjugateMildExistenceFloorData p u₀) :
    let S : ConjugateMildSolutionData p u₀ := conjugateMildSolutionData_of_floorData D
    ∃ v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p D.T S.u v ∧
      InitialTrace intervalDomain u₀ S.u := by
  let S : ConjugateMildSolutionData p u₀ := conjugateMildSolutionData_of_floorData D
  have htrace : InitialTrace intervalDomain u₀ S.u :=
    ShenWork.Paper2.BFormInitialTrace.conjugateMildSolutionData_initialTrace
      p hu₀.admissible.2 S
  have hu₀_bound_lift : ∀ y, |intervalDomainLift u₀ y| ≤ S.M := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · have hsemigroup :=
        ShenWork.IntervalPicardIterateInitialApproach.semigroup_initialApproach
      simp only [S, conjugateMildSolutionData_of_floorData,
        intervalDomainLift, dif_pos hy]
      -- The inhabited floor core chose `D.M` to dominate the datum; recover
      -- this directly from the heat-ball construction at an arbitrary time
      -- using the explicit constructor equality is unnecessary: its base
      -- homogeneous bound and strong initial approach pass to the limit.
      by_contra hnot
      push_neg at hnot
      obtain ⟨δ, hδ, hclose⟩ := hsemigroup p hu₀.admissible.2
        ((|u₀ ⟨y, hy⟩| - D.M) / 2) (by linarith)
      let t := min D.T δ / 2
      have hmin : 0 < min D.T δ := lt_min D.hT hδ
      have ht : 0 < t := by dsimp [t]; linarith
      have htT : t ≤ D.T := by dsimp [t]; linarith [min_le_left D.T δ]
      have htδ : t < δ := by dsimp [t]; linarith [min_le_right D.T δ]
      have hb := D.hbase_ball t ht htT ⟨y, hy⟩
      have hclose' := hclose t ht htδ ⟨y, hy⟩
      simp only [conjugatePicardIter] at hb
      have htri : |u₀ ⟨y, hy⟩| ≤
          |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y - u₀ ⟨y, hy⟩| +
          |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y| := by
        have := abs_add_le
          (u₀ ⟨y, hy⟩ -
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
              (intervalDomainLift u₀) y)
          (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y)
        rw [sub_add_cancel] at this
        simpa [abs_sub_comm, add_comm] using this
      linarith
    · simp [S, conjugateMildSolutionData_of_floorData, intervalDomainLift, hy, D.hM.le]
  have hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀.admissible.2
  have hcore := conjugateMild_reducedClassicalCore_direct
    S hu₀.admissible.2 hu₀_bound_lift hu₀_meas htrace
  have hreg :=
    ShenWork.IntervalCoupledRegularityBootstrap.regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
      p hcore
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace'⟩ := hreg
  exact ⟨v,
    IsPaper2ClassicalSolution.of_components S.hT hclassreg hpos hvnn hpde_u hpde_v hbc,
    htrace'⟩

/-- Faithful local classical existence for arbitrary paper-positive data and
all parameter exponents allowed by `CM2Params`. -/
theorem intervalDomain_localExistence_paperPositive_allExponents
    (p : CM2Params) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, _⟩ := conjugateMildExistenceFloorData_exists p hu₀
  let S : ConjugateMildSolutionData p u₀ := conjugateMildSolutionData_of_floorData D
  obtain ⟨v, hsol, htrace⟩ :=
    intervalDomain_classicalSolution_of_floorData_allExponents p hu₀ D
  exact ⟨D.T, D.hT, S.u, v, hsol, htrace⟩

/-- The local lifespan is uniform on every positive strip
`{w | |w| ≤ M, c ≤ w}` for all positive exponents. -/
theorem intervalDomain_thresholdLocalExistence_positiveStrip_allExponents
    (p : CM2Params) :
    QuantFromThreshold.ThresholdQuantitativeLocalExistence p := by
  intro M c hM hc
  obtain ⟨δ, hδ, hfactory⟩ :=
    conjugateMildExistenceFloorData_exists_uniform p M c hc
  refine ⟨δ, hδ, ?_⟩
  intro w hw hbound hfloor
  have hwPaper : PaperPositiveInitialDatum intervalDomain w :=
    ⟨hw.admissible, ⟨c, hc, hfloor⟩⟩
  obtain ⟨D, hDδ⟩ := hfactory w hw.admissible.2 hbound hfloor
  let S : ConjugateMildSolutionData p w := conjugateMildSolutionData_of_floorData D
  obtain ⟨v, hsol, htrace⟩ :=
    intervalDomain_classicalSolution_of_floorData_allExponents p hwPaper D
  subst δ
  exact ⟨S.u, v, hsol, htrace⟩

#print axioms intervalDomain_localExistence_paperPositive_allExponents
#print axioms intervalDomain_thresholdLocalExistence_positiveStrip_allExponents

end ShenWork.Paper2.IntervalDomainM

end
