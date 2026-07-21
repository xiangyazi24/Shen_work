import ShenWork.Paper2.IntervalDomainLpHeadline
import ShenWork.Paper2.IntervalDomainMTheorem12Headline

/-!
# Paper 2, Theorem 1.2: honest slow-branch closure

The legacy `intervalDomain` statement asks only for one bounded short-time
solution.  That conclusion follows directly from the positive-cone Picard
construction: its fixed point stays in a uniform pointwise ball on the whole
constructed lifespan.  No slow-diffusion energy estimate is needed for this
weak legacy residual.

The paper-faithful general-`m` model is `intervalDomainM`.  Its corrected
maximal-continuation statement is stronger: every finite or global carrier is
bounded.  That result uses the genuinely slow-specific finite-exponent descent
and restarted `Lp`-to-`Linf` estimate already proved in
`IntervalDomainMSlowLpBound` and `IntervalDomainMSlowLinfBound`.  It does not
assert that a slow carrier is global, because for `0 < m < 1` an upper bound
alone does not exclude collapse of the positive floor at a finite endpoint.
-/

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem12SlowBranchClosure

open ShenWork.IntervalConjugatePicard
open ShenWork.Paper2.IntervalDomainLpHeadline
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMTheorem12Headline

private theorem intervalDomain_boundedBefore_of_pointwise_uniform_bound
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hpoint : ∃ M, ∀ t, 0 < t → t < T →
      ∀ x : intervalDomainPoint, |u t x| ≤ M) :
    IsPaper2BoundedBefore intervalDomain T u := by
  obtain ⟨M, hM⟩ := hpoint
  refine ⟨M, ?_⟩
  intro t ht0 htT
  have hM_nonneg : 0 ≤ M := by
    let x0 : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    exact (abs_nonneg (u t x0)).trans (hM t ht0 htT x0)
  change intervalDomainSupNorm (u t) ≤ M
  unfold intervalDomainSupNorm
  exact Real.sSup_le
    (fun _ hy => by obtain ⟨x, rfl⟩ := hy; exact hM t ht0 htT x)
    hM_nonneg

/-- A finite-window bound for every horizon and an eventual global bound join
to one uniform bound on the whole positive time axis.  This isolates the
short-time issue: it is enough to control one finite initial window. -/
theorem intervalDomainM_allPositive_bound_of_everyFinite_and_eventual
    {u : ℝ → intervalDomainPoint → ℝ}
    (hfinite : ∀ T, 0 < T → IsPaper2BoundedBefore intervalDomainM T u)
    (heventual : IsPaper2Bounded intervalDomainM u) :
    ∃ M, ∀ t, 0 < t → intervalDomainM.supNorm (u t) ≤ M := by
  obtain ⟨Mlate, hMlate_eventually⟩ := heventual
  obtain ⟨T0, hMlate⟩ := Filter.eventually_atTop.1 hMlate_eventually
  let H : ℝ := max 1 (T0 + 1)
  have hH_pos : 0 < H :=
    lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) (T0 + 1))
  have hT0H : T0 < H :=
    lt_of_lt_of_le (by linarith : T0 < T0 + 1)
      (le_max_right (1 : ℝ) (T0 + 1))
  obtain ⟨Mearly, hMearly⟩ := hfinite H hH_pos
  refine ⟨max Mearly Mlate, ?_⟩
  intro t ht
  by_cases htH : t < H
  · exact (hMearly t ht htH).trans (le_max_left _ _)
  · exact (hMlate t (hT0H.le.trans (le_of_not_gt htH))).trans
      (le_max_right _ _)

/-- The positive-cone local fixed point is uniformly bounded on its complete
constructed lifespan.  This is stronger than bare local existence and is
independent of the slow/critical parameter split. -/
theorem intervalDomain_localExistence_bounded_allExponents
    (p : CM2Params) :
    ∀ u0 : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u0 →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v ∧
          InitialTrace intervalDomain u0 u ∧
          IsPaper2BoundedBefore intervalDomain T u := by
  intro u0 hu0
  obtain ⟨D, _⟩ := conjugateMildExistenceFloorData_exists p hu0
  let S : ConjugateMildSolutionData p u0 :=
    conjugateMildSolutionData_of_floorData D
  obtain ⟨v, hsol, htrace⟩ :=
    intervalDomain_classicalSolution_of_floorData_allExponents p hu0 D
  refine ⟨D.T, D.hT, S.u, v, hsol, htrace, ?_⟩
  exact intervalDomain_boundedBefore_of_pointwise_uniform_bound
    ⟨S.M, fun t ht0 htT x => S.hbound t ht0 htT.le x⟩

/-- The exact residual used by the legacy slow-branch wrapper is
unconditional.  Its weakness is intentional: it asks only for one bounded
local Picard trajectory, not boundedness of a maximal continuation. -/
theorem IntervalDomainTheorem12SlowBranchResidual_unconditional
    (p : CM2Params) :
    IntervalDomainTheorem12SlowBranchResidual p := by
  intro _hm_pos _hm_lt u0 hu0
  exact intervalDomain_localExistence_bounded_allExponents p u0 hu0

/-- Closure of the repository's legacy `intervalDomain` Theorem 1.2 on its
necessary parameter slice.  The slow half is the weak local statement above;
the critical half is the already proved unconditional branch. -/
theorem Theorem_1_2_intervalDomain_unconditional
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b) :
    Theorem_1_2 intervalDomain p :=
  Theorem_1_2_intervalDomain_of_slowBranchResidual
    p hguard (IntervalDomainTheorem12SlowBranchResidual_unconditional p)

/-- Paper-faithful slow branch on the genuine general-`m` interval model.
Every canonical finite/global carrier is bounded; no globality claim is made
in the slow regime. -/
theorem correctedTheorem12_slowBranch_faithful_unconditional
    (p : CM2Params)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hbeta : 1 ≤ p.β) (hm_lt : p.m < 1) :
    ∀ u0 : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomainM u0 →
        Nonempty (Paper2MaximalContinuation intervalDomainM p u0) ∧
          ∀ branch : Paper2MaximalContinuation intervalDomainM p u0,
            branch.IsBounded :=
  correctedTheorem12_slowBranch_intervalDomainM p hguard hbeta hm_lt

/-- If a slow maximal carrier is on the global branch, its supremum norm is
in fact uniformly bounded for every `t > 0`, not merely eventually.  The
initial window comes from the trace-aware finite-horizon theorem. -/
theorem slowBranch_global_allPositive_bound
    {p : CM2Params}
    {u0 : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu0 : PositiveInitialDatum intervalDomainM u0)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u0 u)
    (hbeta : 1 ≤ p.β) (hm_lt : p.m < 1) :
    ∃ M, ∀ t, 0 < t → intervalDomainM.supNorm (u t) ≤ M := by
  apply intervalDomainM_allPositive_bound_of_everyFinite_and_eventual
  · intro T hT
    exact slow_bounded_before hguard hu0 (hglobal.classical hT) htrace hbeta hm_lt
  · exact slow_bounded_global hguard hu0 hglobal htrace hbeta hm_lt

/-- Fully assembled corrected Theorem 1.2 on the paper-faithful general-`m`
interval model. -/
theorem correctedTheorem12_intervalDomain_faithful_unconditional
    (p : CM2Params) :
    CorrectedTheorem_1_2 intervalDomainM p :=
  correctedTheorem12_intervalDomainM p

#print axioms intervalDomain_localExistence_bounded_allExponents
#print axioms IntervalDomainTheorem12SlowBranchResidual_unconditional
#print axioms Theorem_1_2_intervalDomain_unconditional
#print axioms correctedTheorem12_slowBranch_faithful_unconditional
#print axioms slowBranch_global_allPositive_bound
#print axioms correctedTheorem12_intervalDomain_faithful_unconditional

end ShenWork.Paper2.IntervalDomainTheorem12SlowBranchClosure

end
