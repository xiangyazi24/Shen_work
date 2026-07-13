/- Small-data global existence near a linearly stable positive equilibrium. -/
import ShenWork.Paper2.IntervalDomainL2USubHorizonGluing
import ShenWork.Paper2.IntervalConjugatePicardFloorCoreInhabit
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalConjugateMildJointTimeDerivativeInterior
import ShenWork.Paper2.IntervalConjugateMildClassicalRegularityFromJointUT
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.PDE.IntervalCoupledClassicalCoreDischarge
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.Paper3.IntervalDomainWeakSupBasinEntry

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalDomainExistence
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

/-! ### Unconditional local Cauchy producer

The Paper-2 all-exponent local theorem imports a much larger theorem-level
assembly.  The small-data continuation only needs its already-proved local
ingredients, so we expose the same direct reduced-core route here without any
global or stability hypothesis. -/

/-- Direct joint-value/time-derivative package for a positive-floor conjugate
mild solution. -/
def paper3ConjugateMildResolverTimeData
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

/-- The reduced classical core for an arbitrary positive-floor conjugate mild
solution, assembled only from the direct local regularity producers. -/
theorem paper3ConjugateMild_reducedClassicalCore
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
      (paper3ConjugateMildResolverTimeData
        S hu₀_cont hu₀_bound hu₀_meas)
      htrace

/-- Upgrade an inhabited positive-floor Picard datum to a classical solution
at its explicit horizon, for every exponent allowed by `CM2Params`. -/
theorem paper3ClassicalSolution_of_floorData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (D : ConjugateMildExistenceFloorData p u₀) :
    let S : ConjugateMildSolutionData p u₀ :=
      conjugateMildSolutionData_of_floorData D
    ∃ v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p D.T S.u v ∧
      InitialTrace intervalDomain u₀ S.u := by
  let S : ConjugateMildSolutionData p u₀ :=
    conjugateMildSolutionData_of_floorData D
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
      by_contra hnot
      push Not at hnot
      obtain ⟨delta, hdelta, hclose⟩ := hsemigroup p hu₀.admissible.2
        ((|u₀ ⟨y, hy⟩| - D.M) / 2) (by linarith)
      let t := min D.T delta / 2
      have hmin : 0 < min D.T delta := lt_min D.hT hdelta
      have ht : 0 < t := by dsimp [t]; linarith
      have htT : t ≤ D.T := by
        dsimp [t]
        linarith [min_le_left D.T delta]
      have htdelta : t < delta := by
        dsimp [t]
        linarith [min_le_right D.T delta]
      have hb := D.hbase_ball t ht htT ⟨y, hy⟩
      have hclose' := hclose t ht htdelta ⟨y, hy⟩
      simp only [conjugatePicardIter] at hb
      have htri : |u₀ ⟨y, hy⟩| ≤
          |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y - u₀ ⟨y, hy⟩| +
          |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y| := by
        have h := abs_add_le
          (u₀ ⟨y, hy⟩ -
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
              (intervalDomainLift u₀) y)
          (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) y)
        rw [sub_add_cancel] at h
        simpa [abs_sub_comm, add_comm] using h
      linarith
    · simp [S, conjugateMildSolutionData_of_floorData,
        intervalDomainLift, hy, D.hM.le]
  have hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀.admissible.2
  have hcore := paper3ConjugateMild_reducedClassicalCore
    S hu₀.admissible.2 hu₀_bound_lift hu₀_meas htrace
  have hreg :=
    ShenWork.IntervalCoupledRegularityBootstrap.regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
      p hcore
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace'⟩ := hreg
  exact ⟨v,
    IsPaper2ClassicalSolution.of_components S.hT hclassreg hpos hvnn
      hpde_u hpde_v hbc,
    htrace'⟩

/-- Uniform local classical existence on a positive strip.  This is the
continuation factory used below; its lifespan is fixed before the datum. -/
theorem paper3ThresholdLocalExistence_positiveStrip
    (p : CM2Params) :
    ∀ M c : ℝ, 0 < M → 0 < c → ∃ delta : ℝ, 0 < delta ∧
      ∀ w : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain w →
        (∀ x, |w x| ≤ M) →
        (∀ x, c ≤ w x) →
        ∃ uw vw,
          IsPaper2ClassicalSolution intervalDomain p delta uw vw ∧
          InitialTrace intervalDomain w uw := by
  intro M c hM hc
  obtain ⟨delta, hdelta, hfactory⟩ :=
    conjugateMildExistenceFloorData_exists_uniform p M c hc
  refine ⟨delta, hdelta, ?_⟩
  intro w hw hbound hfloor
  have hwPaper : PaperPositiveInitialDatum intervalDomain w :=
    ⟨hw.admissible, ⟨c, hc, hfloor⟩⟩
  obtain ⟨D, hDdelta⟩ := hfactory w hw.admissible.2 hbound hfloor
  let S : ConjugateMildSolutionData p w :=
    conjugateMildSolutionData_of_floorData D
  obtain ⟨v, hsol, htrace⟩ := paper3ClassicalSolution_of_floorData p hwPaper D
  subst delta
  exact ⟨S.u, v, hsol, htrace⟩

/-- A finite classical solution with a bounded initial trace is uniformly
bounded on every closed half-horizon `(0,t]`, with `t` strictly below its
classical horizon.  The short-time leg comes from the initial trace and the
remaining compact slab from joint continuity. -/
theorem intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    {p : CM2Params} {T t : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd₀ : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    (ht0 : 0 < t) (htT : t < T) :
    ∃ M : ℝ, ∀ τ, 0 < τ → τ ≤ t →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (u τ) x| ≤ M := by
  obtain ⟨eta, heta, _hetaT, hnear⟩ :=
    initialSupNormApproach_intervalDomain p u₀ hu₀ hbdd₀ hsol.T_pos
      hsol htrace (by norm_num : (0 : ℝ) < 1)
  let a := min (eta / 2) (t / 2)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by linarith)
  have hat : a ≤ t := by
    have : a ≤ t / 2 := by dsimp [a]; exact min_le_right _ _
    linarith
  have haeta : a < eta := by
    have : a ≤ eta / 2 := by dsimp [a]; exact min_le_left _ _
    linarith
  let slab := Set.Icc a t ×ˢ Set.Icc (0 : ℝ) 1
  have hslabCompact : IsCompact slab := by
    dsimp [slab]
    exact isCompact_Icc.prod isCompact_Icc
  have hslabSub : slab ⊆
      Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 := by
    dsimp [slab]
    exact Set.prod_mono (Set.Icc_subset_Ioo ha htT) Subset.rfl
  have hjoint :=
    ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity.intervalDomain_solution_jointContinuousOn
      hsol
  have habsCont : ContinuousOn
      (fun tx : ℝ × ℝ =>
        |intervalDomainLift (u tx.1) tx.2|) slab :=
    continuous_abs.comp_continuousOn (hjoint.mono hslabSub)
  have hslabNonempty : slab.Nonempty := by
    refine ⟨(a, 0), ?_⟩
    exact ⟨⟨le_rfl, hat⟩, by norm_num⟩
  obtain ⟨txmax, _htxmax, hmax⟩ :=
    hslabCompact.exists_isMaxOn hslabNonempty habsCont
  let Mcompact := |intervalDomainLift (u txmax.1) txmax.2|
  let Mnear := intervalDomain.supNorm u₀ + 1
  let M := max Mnear Mcompact
  refine ⟨M, ?_⟩
  intro τ hτ hτt x hx
  by_cases hτa : τ < a
  · have hτT : τ < T := lt_of_le_of_lt hτt htT
    have habs := abs_lift_le_supNorm hsol ⟨hτ, hτT⟩ hx
    have hsup : intervalDomain.supNorm (u τ) ≤ Mnear := by
      dsimp [Mnear]
      exact hnear τ hτ (lt_trans hτa haeta)
    exact habs.trans (hsup.trans (by dsimp [M]; exact le_max_left _ _))
  · have hτmem : (τ, x) ∈ slab := by
      dsimp [slab]
      exact ⟨⟨le_of_not_gt hτa, hτt⟩, hx⟩
    have hcompact : |intervalDomainLift (u τ) x| ≤ Mcompact := by
      simpa [Mcompact] using hmax hτmem
    exact hcompact.trans (by dsimp [M]; exact le_max_right _ _)

/-- Parameter-independent overlap uniqueness for the paper's uniformly
positive initial data.  Stability is not used: on each strict sub-horizon,
positivity and compact boundedness supply the two-sided strip needed by the
existing L2 energy argument. -/
def intervalDomainPaperPositiveOverlapUniqueAt
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    IntervalClassicalSolutionOverlapUniqueAt p u₀ := by
  intro T₁ T₂ d₁ d₂ t ht0 htmin x
  refine intervalDomain_classicalSolution_overlap_unique_of_subHorizonBound
    d₁.sol d₂.sol d₁.trace d₂.trace hu₀.admissible.1 ?_ t ht0 htmin x
  intro T' hT' hT'min
  have hT'₁ : T' < T₁ := hT'min.trans_le (min_le_left _ _)
  have hT'₂ : T' < T₂ := hT'min.trans_le (min_le_right _ _)
  obtain ⟨delta₁, hdelta₁, hlo₁⟩ := lift_u_uniformPositive_on_halfHorizon
    d₁.sol d₁.trace hu₀.floor hu₀.admissible hT' hT'₁
  obtain ⟨delta₂, hdelta₂, hlo₂⟩ := lift_u_uniformPositive_on_halfHorizon
    d₂.sol d₂.trace hu₀.floor hu₀.admissible hT' hT'₂
  obtain ⟨M₁, hM₁⟩ := intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    d₁.sol d₁.trace hu₀.toPositive hu₀.admissible.1 hT' hT'₁
  obtain ⟨M₂, hM₂⟩ := intervalDomain_solution_lift_uniform_abs_on_halfHorizon
    d₂.sol d₂.trace hu₀.toPositive hu₀.admissible.1 hT' hT'₂
  refine ⟨min delta₁ delta₂, max M₁ M₂, lt_min hdelta₁ hdelta₂, ?_⟩
  intro τ hτ hτT'
  constructor
  · intro y hy
    exact ⟨(min_le_left _ _).trans (hlo₁ τ hτ hτT' y hy),
      (le_abs_self _).trans
        ((hM₁ τ hτ hτT' y hy).trans (le_max_left _ _))⟩
  · intro y hy
    exact ⟨(min_le_right _ _).trans (hlo₂ τ hτ hτT' y hy),
      (le_abs_self _).trans
        ((hM₂ τ hτ hτT' y hy).trans (le_max_right _ _))⟩

#print axioms paper3ConjugateMildResolverTimeData
#print axioms paper3ConjugateMild_reducedClassicalCore
#print axioms paper3ClassicalSolution_of_floorData
#print axioms paper3ThresholdLocalExistence_positiveStrip
#print axioms intervalDomain_solution_lift_uniform_abs_on_halfHorizon
#print axioms intervalDomainPaperPositiveOverlapUniqueAt

end

end ShenWork.Paper3
