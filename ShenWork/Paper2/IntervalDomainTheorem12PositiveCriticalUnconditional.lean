import ShenWork.Paper2.IntervalChiNegV6Headline
import ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer
import ShenWork.Paper2.IntervalDomainUniformContinuation
import ShenWork.Paper2.IntervalDomainPiecewiseClassical
import ShenWork.Paper2.IntervalDomainGlueExtension
import ShenWork.Paper2.IntervalDomainL2UEnergyUniformGammaGeOne
import ShenWork.Paper2.IntervalDomainTheorem11CorePath

/-!
# Unconditional positive-critical continuation for Paper 2

This file removes the two Cauchy-theory hypotheses from the positive-critical
Theorem 1.2 branch.  The local factory is the sign-agnostic conjugate B-form
construction.  At a putative finite maximal horizon, the affine-restart bound
rules out upper blow-up; a paper-positive restart slice and the quantitative
local factory extend the solution past the supremum.  Overlap uniqueness then
glues arbitrarily long reachable solutions into one global solution.
-/

open Filter Set Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer
open ShenWork.Paper2.IntervalChiNegV6Assembly
open ShenWork.Paper2.StrongPath
open ShenWork.IntervalDomainExistence

/-- The already produced V6 local core is a quantitative PPID local factory.
The construction is sign-agnostic; the old `chiNeg` name records only its first
headline consumer. -/
def positiveCriticalQuantitativeLocalPPID_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    ChiNegDatumUniformConstructionPPID p :=
  ShenWork.ppid_of_uniformCore
    (chiNegDatumUniformCore_v6 p hα hγ
      (uniformTruncatedV6AssemblyInputs_producer p hα hγ))

/-- Per-datum local existence from the quantitative PPID factory. -/
theorem positiveCriticalLocalExistence_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨M₀, hM₀⟩ := hu₀.admissible.1
  let M : ℝ := max M₀ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ x, |u₀ x| ≤ M := by
    intro x
    exact (hM₀ (Set.mem_range_self x)).trans (le_max_left _ _)
  obtain ⟨T, hT, hfactory⟩ :=
    positiveCriticalQuantitativeLocalPPID_geOne p hα hγ M hM
  obtain ⟨u, v, hsol, htrace⟩ := hfactory hu₀ hbound
  exact ⟨T, hT, u, v, hsol, htrace⟩

/-- The positive-critical finite-horizon estimate supplies the upper-only
uniform lift bound needed by the `γ ≥ 1` overlap uniqueness theorem. -/
def positiveCriticalUniformLiftBoundZeroM_geOne
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hχ : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    IntervalDomainUniformLiftBoundZeroM p where
  bound := by
    intro u₀ hu₀ T₁ T₂ u₁ v₁ u₂ v₂ hsol₁ hsol₂ htr₁ htr₂
    obtain ⟨M₁, hM₁⟩ :=
      critical_bounded_before_positive_restarted_affine_intervalDomain
        hguard hu₀ hsol₁ htr₁ hβ hm hχ hthreshold
    obtain ⟨M₂, hM₂⟩ :=
      critical_bounded_before_positive_restarted_affine_intervalDomain
        hguard hu₀ hsol₂ htr₂ hβ hm hχ hthreshold
    let M : ℝ := max (max M₁ M₂) 0
    have hMnn : 0 ≤ M := le_max_right _ _
    refine ⟨M, hMnn, ?_⟩
    intro τ hτ0 hτmin
    have hτ₁ : τ ∈ Set.Ioo (0 : ℝ) T₁ :=
      ⟨hτ0, lt_of_lt_of_le hτmin (min_le_left _ _)⟩
    have hτ₂ : τ ∈ Set.Ioo (0 : ℝ) T₂ :=
      ⟨hτ0, lt_of_lt_of_le hτmin (min_le_right _ _)⟩
    constructor
    · intro x hx
      have hpos := solution_lift_pos hsol₁ hτ₁ x hx
      have habs := abs_lift_le_supNorm hsol₁ hτ₁ hx
      rw [abs_of_pos hpos] at habs
      exact ⟨hpos.le,
        (habs.trans (hM₁ τ hτ₁.1 hτ₁.2)).trans
          (le_trans (le_max_left M₁ M₂) (le_max_left _ _))⟩
    · intro x hx
      have hpos := solution_lift_pos hsol₂ hτ₂ x hx
      have habs := abs_lift_le_supNorm hsol₂ hτ₂ hx
      rw [abs_of_pos hpos] at habs
      exact ⟨hpos.le,
        (habs.trans (hM₂ τ hτ₂.1 hτ₂.2)).trans
          (le_trans (le_max_right M₁ M₂) (le_max_left _ _))⟩

/-- Positive-critical overlap uniqueness, obtained from the branch's own
finite-horizon affine bound rather than the negative-sensitivity maximum
principle. -/
def positiveCriticalOverlapUnique_geOne
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hχ : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p)
    (hγ : 1 ≤ p.γ) :
    IntervalClassicalSolutionOverlapUnique p :=
  IntervalClassicalSolutionOverlapUnique_of_l2EnergyMethod
    (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
      (intervalDomainL2UBoundedDatumUniform_of_bounded
        (boundednessHypothesis_of_uniformSupBoundZeroM hγ
          (positiveCriticalUniformLiftBoundZeroM_geOne
            p hguard hβ hm hχ hthreshold))))

/-- A bounded realized solution at a finite maximal horizon can be restarted
from a paper-positive interior slice and glued past that horizon. -/
theorem positiveCritical_reachablePast_of_bounded_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hχ : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hbdd : IsPaper2BoundedBefore intervalDomain T u) :
    ReachablePast p u₀ T := by
  obtain ⟨B, hB⟩ := hbdd
  let M : ℝ := max (max B 1) (intervalDomainSupNorm u₀ + 1)
  have hM : 0 < M :=
    lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right B 1) (le_max_left _ _))
  have hslice_bound : ∀ t, 0 < t → t < T → ∀ x, |u t x| ≤ M := by
    intro t ht0 htT x
    have hrange := classicalSolution_u_range_bddAbove hsol ⟨ht0, htT⟩
    have habs : |u t x| ≤ intervalDomainSupNorm (u t) := by
      unfold intervalDomainSupNorm
      exact le_csSup hrange (Set.mem_range_self x)
    exact (habs.trans (hB t ht0 htT)).trans
      (le_trans (le_max_left B 1) (le_max_left _ _))
  have hu₀_bound : ∀ x, |u₀ x| ≤ M := by
    intro x
    have hraw := hu₀.admissible.1
    have habs : |u₀ x| ≤ intervalDomainSupNorm u₀ := by
      unfold intervalDomainSupNorm
      exact le_csSup hraw (Set.mem_range_self x)
    exact habs.trans (by
      have : intervalDomainSupNorm u₀ ≤ intervalDomainSupNorm u₀ + 1 := by linarith
      exact this.trans (le_max_right _ _))
  obtain ⟨δ, hδ, hfactory⟩ :=
    positiveCriticalQuantitativeLocalPPID_geOne p hα hγ M hM
  by_cases hsmall : T ≤ δ / 2
  · obtain ⟨uw, vw, hsolw, htracew⟩ := hfactory hu₀ hu₀_bound
    refine ⟨δ, by linarith, ?_⟩
    exact ⟨hδ, uw, vw, hsolw, htracew⟩
  · push Not at hsmall
    let τ : ℝ := T - δ / 4
    have hτ0 : 0 < τ := by dsimp [τ]; linarith
    have hτT : τ < T := by dsimp [τ]; linarith
    have hτmem : τ ∈ Set.Ioo (0 : ℝ) T := ⟨hτ0, hτT⟩
    have hτpaper : PaperPositiveInitialDatum intervalDomain (u τ) :=
      UniformContinuation.classicalSolution_slice_paperPositiveInitialDatum hsol hτmem
    have hτbound : ∀ x, |u τ x| ≤ M := hslice_bound τ hτ0 hτT
    obtain ⟨w, z, hsolw, htracew⟩ := hfactory hτpaper hτbound
    have hshift : IsPaper2ClassicalSolution intervalDomain p (T - τ)
        (fun t x => u (t + τ) x) (fun t x => v (t + τ) x) :=
      TimeShift.classicalSolution_timeShift TimeShift.regularityTimeShiftWorks
        hsol hτ0 hτT
    have hshiftTrace : InitialTrace intervalDomain (u τ) (fun t x => u (t + τ) x) :=
      GlueExtension.timeShiftInitialTraceWorks hsol hτ0 hτT
    have huniq : IntervalClassicalSolutionOverlapUnique p :=
      positiveCriticalOverlapUnique_geOne
        p hguard hβ hm hχ hthreshold hγ
    have hmin : min (T - τ) δ = T - τ := by
      dsimp [τ]
      rw [min_eq_left]
      linarith
    have hoverU : ∀ s, τ < s → s < T → ∀ x,
        u s x = w (s - τ) x := by
      intro s hsτ hsT x
      have hs := huniq hτpaper.toPositive
        { T_pos := by dsimp [τ]; linarith
          u := fun t x => u (t + τ) x
          v := fun t x => v (t + τ) x
          sol := hshift
          trace := hshiftTrace }
        { T_pos := hδ, u := w, v := z, sol := hsolw, trace := htracew }
        (s - τ) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.1
    have hoverV : ∀ s, τ < s → s < T → ∀ x,
        v s x = z (s - τ) x := by
      intro s hsτ hsT x
      have hs := huniq hτpaper.toPositive
        { T_pos := by dsimp [τ]; linarith
          u := fun t x => u (t + τ) x
          v := fun t x => v (t + τ) x
          sol := hshift
          trace := hshiftTrace }
        { T_pos := hδ, u := w, v := z, sol := hsolw, trace := htracew }
        (s - τ) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.2
    let T' : ℝ := T + δ / 2
    have hT' : 0 < T' := by dsimp [T']; linarith
    have hT'le : T' ≤ τ + δ := by dsimp [T', τ]; linarith
    have hsol' := PiecewiseClassical.piecewiseClassicalWorks p
      hT hδ hτ0 hτT hsol hsolw hoverU hoverV T' hT' hT'le
    have htrace' : InitialTrace intervalDomain u₀
        (fun t x => if t < T then u t x else w (t - τ) x) := by
      intro ε hε
      obtain ⟨d, hd, htr⟩ := htrace ε hε
      refine ⟨min d T, lt_min hd hT, ?_⟩
      intro t ht0 htd
      have htT : t < T := lt_of_lt_of_le htd (min_le_right _ _)
      have htd' : t < d := lt_of_lt_of_le htd (min_le_left _ _)
      have heq : (fun x => (if t < T then u t x else w (t - τ) x) - u₀ x) =
          (fun x => u t x - u₀ x) := by
        funext x
        rw [if_pos htT]
      change intervalDomainSupNorm
        (fun x => (if t < T then u t x else w (t - τ) x) - u₀ x) < ε
      rw [heq]
      exact htr t ht0 htd'
    refine ⟨T', by dsimp [T']; linarith, ?_⟩
    exact ⟨hT', _, _, hsol', htrace'⟩

/-- Arbitrarily long reachable horizons for every paper-positive datum in the
positive critical branch. -/
theorem positiveCritical_reachableArbitrarilyLong_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hχ : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ReachableArbitrarilyLong p u₀ := by
  let hlocal := positiveCriticalLocalExistence_geOne p hα hγ
  have huniq : IntervalClassicalSolutionOverlapUnique p :=
    positiveCriticalOverlapUnique_geOne
      p hguard hβ hm hχ hthreshold hγ
  by_cases hbdd : BddAbove (reachableClassicalHorizonSet p u₀)
  · obtain ⟨T₀, hT₀, u₀sol, v₀sol, hsol₀, htrace₀⟩ := hlocal u₀ hu₀
    have hreach₀ : ReachableClassicalHorizon p u₀ T₀ :=
      ⟨hT₀, u₀sol, v₀sol, hsol₀, htrace₀⟩
    have hne : (reachableClassicalHorizonSet p u₀).Nonempty :=
      ⟨T₀, hreach₀⟩
    have hTmax : 0 < finiteMaximalReachableHorizon p u₀ :=
      lt_of_lt_of_le hT₀
        (reachable_le_finiteMaximalReachableHorizon hbdd hreach₀)
    let u := boundedReachableGluedU hbdd hne
    let v := boundedReachableGluedV hbdd hne
    have hsol : IsPaper2ClassicalSolution intervalDomain p
        (finiteMaximalReachableHorizon p u₀) u v :=
      boundedReachableGlued_isPaper2ClassicalSolution_of_overlapUnique
        huniq hu₀.toPositive hbdd hne hTmax
    have htrace : InitialTrace intervalDomain u₀ u :=
      boundedReachableGlued_initialTrace_of_overlapUnique
        huniq hu₀.toPositive hbdd hne
    have hbound :=
      critical_bounded_before_positive_restarted_affine_intervalDomain
        hguard hu₀.toPositive hsol htrace hβ hm hχ hthreshold
    exact False.elim
      (not_reachablePast_finiteMaximalReachableHorizon hbdd
        (positiveCritical_reachablePast_of_bounded_geOne
          p hα hγ hguard hβ hm hχ hthreshold hu₀ hsol.T_pos hsol htrace hbound))
  · exact reachableArbitrarilyLong_of_not_bddAbove hbdd

/-- Construct the canonical global solution by gluing the arbitrarily long
reachable horizons, then apply the affine-restart global bound. -/
theorem positiveCriticalGlobalSolution_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hχ : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
      InitialTrace intervalDomain u₀ u ∧
      IsPaper2Bounded intervalDomain u := by
  have huniq : IntervalClassicalSolutionOverlapUnique p :=
    positiveCriticalOverlapUnique_geOne
      p hguard hβ hm hχ hthreshold hγ
  have hreach : ReachableArbitrarilyLong p u₀ :=
    positiveCritical_reachableArbitrarilyLong_geOne
      p hα hγ hguard hβ hm hχ hthreshold hu₀
  obtain ⟨u, v, hglobal, htrace⟩ :=
    (GlobalSolutionGluingFromReachability_of_overlapUnique huniq)
      u₀ hu₀.toPositive hreach
  have hbounded : IsPaper2Bounded intervalDomain u :=
    critical_bounded_global_positive_restarted_affine_intervalDomain
      hguard hu₀.toPositive hglobal htrace hβ hm hχ hthreshold
  exact ⟨u, v, hglobal, htrace, hbounded⟩

/-- Non-vacuous replacement for the old conditional wrapper.  There is no
`hlocal` and no impossible arbitrary-total-function `hglobalExtension` input:
the global pair is constructed internally. -/
theorem Theorem_1_2_intervalDomain_positive_critical_branch_unconditional_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hguard : p.a = 0 ∨ 0 < p.b) (hχ : 0 < p.χ₀) :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
          InitialTrace intervalDomain u₀ u ∧
          IsPaper2Bounded intervalDomain u := by
  intro hβ hm hthreshold u₀ hu₀
  exact positiveCriticalGlobalSolution_geOne
    p hα hγ hguard hβ hm hχ hthreshold u₀ hu₀

/-- Faithful maximal-continuation version of the positive critical branch.
The constructed carrier is global.  Conversely, every finite carrier would
carry the `m ≥ 1` blow-up alternative, contradicted by the same finite-horizon
affine-restart estimate. -/
theorem correctedTheorem12_positiveCriticalBranch_unconditional_geOne
    (p : CM2Params) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hguard : p.a = 0 ∨ 0 < p.b) (hχ : 0 < p.χ₀)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hthreshold : p.χ₀ < chiBeta p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        Nonempty (Paper2MaximalContinuation intervalDomain p u₀) ∧
        ∀ branch : Paper2MaximalContinuation intervalDomain p u₀,
          branch.IsGlobal ∧ branch.IsBounded := by
  intro u₀ hu₀
  obtain ⟨u, v, hglobal, htrace, hbounded⟩ :=
    positiveCriticalGlobalSolution_geOne
      p hα hγ hguard hβ hm hχ hthreshold u₀ hu₀
  constructor
  · exact ⟨Paper2MaximalContinuation.global u v hglobal htrace⟩
  · intro branch
    cases branch with
    | global U V hglob htr =>
        exact ⟨True.intro,
          critical_bounded_global_positive_restarted_affine_intervalDomain
            hguard hu₀.toPositive hglob htr hβ hm hχ hthreshold⟩
    | finite T U V hT hsol htr _halt hmge =>
        have hbdd : IsPaper2BoundedBefore intervalDomain T U :=
          critical_bounded_before_positive_restarted_affine_intervalDomain
            hguard hu₀.toPositive hsol htr hβ hm hχ hthreshold
        have hcontrols : SupNormControlsPointwiseBefore T U :=
          supNormControlsPointwiseBefore_of_bddAbove_abs
            (fun t ht0 htT => classicalSolution_u_range_bddAbove hsol ⟨ht0, htT⟩)
        have hpw : PointwiseBoundedBefore T U :=
          pointwiseBoundedBefore_of_boundedBefore_and_supNormControls
            hbdd hcontrols
        have hfalse : False :=
          (not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore hpw)
            (hmge (by rw [hm]))
        exact False.elim hfalse

#print axioms positiveCriticalQuantitativeLocalPPID_geOne
#print axioms positiveCriticalLocalExistence_geOne
#print axioms positiveCritical_reachableArbitrarilyLong_geOne
#print axioms positiveCriticalGlobalSolution_geOne
#print axioms Theorem_1_2_intervalDomain_positive_critical_branch_unconditional_geOne
#print axioms correctedTheorem12_positiveCriticalBranch_unconditional_geOne

end ShenWork.Paper2.IntervalDomainM

end
