import ShenWork.Paper2.IntervalDomainLocalExistenceAllExponents
import ShenWork.Paper2.IntervalDomainPositiveCriticalOverlapAllExponents
import ShenWork.Paper2.IntervalDomainBoundaryChemDivLimit
import ShenWork.Paper2.IntervalDomainPersistAssembly
import ShenWork.Paper2.IntervalDomainTheorem12PositiveCriticalUnconditional

/-!
# Unconditional positive-critical continuation for all positive exponents

The local restart time is uniform on each positive strip.  A Hamilton minimum
estimate, with the chemotaxis coefficient bounded in absolute value, preserves
a positive floor up to every finite horizon.  These two facts rule out a finite
maximal reachable horizon and give a canonical global solution without any
external local-existence or continuation hypothesis.
-/

open Filter Set Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalDomainExistence
open ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer
open ShenWork.Paper2.QuantFromThreshold
open ShenWork.MinPersistenceAtoms

/-- A bounded positive-critical classical solution has a positive lower floor
on the terminal half of every finite horizon.  The estimate is valid for every
`α,γ > 0` and either sensitivity sign; here it is used in the positive branch. -/
theorem positiveCritical_minimumPersistence_of_bounded_allExponents
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hbdd : IsPaper2BoundedBefore intervalDomain T u) :
    ∃ c : ℝ, 0 < c ∧
      ∀ t, T / 2 ≤ t → t < T → ∀ x : intervalDomainPoint, c ≤ u t x := by
  obtain ⟨B, hB⟩ := hbdd
  let M : ℝ := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hSup : ∀ s ∈ Set.Ico (T / 2 / 2) T, ∀ y,
      |intervalDomainLift (u s) y| ≤ M := by
    intro s hs y
    have hquarter : 0 < T / 2 / 2 :=
      div_pos (div_pos hsol.T_pos (by norm_num)) (by norm_num)
    have hs0 : 0 < s := lt_of_lt_of_le hquarter hs.1
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · have habs := abs_lift_le_supNorm hsol ⟨hs0, hs.2⟩ hy
      exact (habs.trans (hB s hs0 hs.2)).trans (le_max_left _ _)
    · simp [intervalDomainLift, hy, hM]
  have hChem := boundaryChemDivEndpointLimitBounds_of_classicalSolution p
  have hbdry : ∀ s ∈ Set.Ico (T / 2 / 2) T,
      ∀ ys ∈ Set.Icc (0 : ℝ) 1, ys = 0 ∨ ys = 1 →
        intervalDomainLift (u s) ys =
            sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) →
          -(|p.χ₀| * fluxCoeffConst p.β (p.ν * M ^ p.γ) + p.b * M ^ p.α) *
              sInf (intervalDomainLift (u s) '' Set.Icc (0 : ℝ) 1) ≤
            deriv (fun r => intervalDomainLift (u r) ys) s := by
    intro s hs ys hys hendpoint harg
    have hquarter : 0 < T / 2 / 2 :=
      div_pos (div_pos hsol.T_pos (by norm_num)) (by norm_num)
    have hs0 : 0 < s := lt_of_lt_of_le hquarter hs.1
    have hu_le : ∀ x : intervalDomainPoint, u s x ≤ M := by
      intro x
      have hx := hSup s hs x.1
      have hx' : |u s x| ≤ M := by
        simpa [intervalDomainLift, x.property] using hx
      exact (le_abs_self _).trans hx'
    rcases hendpoint with rfl | rfl
    · exact hbdry_left_of_chemDivLimit hChem.left hsol hs0 hs.2 hM hu_le harg
    · exact hbdry_right_of_chemDivLimit hChem.right hsol hs0 hs.2 hM hu_le harg
  let Kp : ℝ :=
    |p.χ₀| * fluxCoeffConst p.β (p.ν * M ^ p.γ) + p.b * M ^ p.α
  have hKp : 0 ≤ Kp := by
    dsimp [Kp]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _)
        (fluxCoeffConst_nonneg p.hβ
          (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))))
      (mul_nonneg p.hb (Real.rpow_nonneg hM _))
  have hbound := hbound_full_allChi hsol (show 0 < T / 2 by linarith [hsol.T_pos])
    (show T / 2 < T by linarith [hsol.T_pos]) hM hSup hbdry
  exact solution_persist_exists_c hsol hKp
    (show 0 < T / 2 by linarith [hsol.T_pos])
    (show T / 2 < T by linarith [hsol.T_pos]) le_rfl hbound

/-- A bounded realized solution at a finite horizon can be restarted from a
uniformly positive terminal slice and glued strictly past that horizon. -/
theorem positiveCritical_reachablePast_of_bounded_allExponents
    (p : CM2Params)
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
  obtain ⟨c, hc, hpersist⟩ :=
    positiveCritical_minimumPersistence_of_bounded_allExponents hsol hbdd
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨B₀, hB₀⟩ := hu₀.admissible.1
  obtain ⟨η, hη, hηu₀⟩ := hu₀.floor
  let c' : ℝ := min c η
  have hc' : 0 < c' := lt_min hc hη
  let M : ℝ := max (max B B₀) 1
  have hM : 0 < M :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hu₀_bound : ∀ x, |u₀ x| ≤ M := by
    intro x
    exact (hB₀ (Set.mem_range_self x)).trans
      ((le_max_right B B₀).trans (le_max_left _ _))
  have hu₀_floor : ∀ x, c' ≤ u₀ x := fun x =>
    (min_le_right c η).trans (hηu₀ x)
  have hslice_bound : ∀ t, 0 < t → t < T → ∀ x, |u t x| ≤ M := by
    intro t ht0 htT x
    have habs := abs_lift_le_supNorm hsol ⟨ht0, htT⟩ x.2
    have habs' : |u t x| ≤ intervalDomainSupNorm (u t) := by
      simpa [intervalDomainLift, x.property] using habs
    exact (habs'.trans (hB t ht0 htT)).trans
      ((le_max_left B B₀).trans (le_max_left _ _))
  obtain ⟨δ, hδ, hfactory⟩ :=
    intervalDomain_thresholdLocalExistence_positiveStrip_allExponents p M c' hM hc'
  by_cases hsmall : T ≤ δ / 2
  · obtain ⟨uw, vw, hsolw, htracew⟩ :=
      hfactory u₀ hu₀.toPositive hu₀_bound hu₀_floor
    refine ⟨δ, by linarith, hδ, uw, vw, hsolw, htracew⟩
  · push Not at hsmall
    let τ : ℝ := T - δ / 4
    have hτ0 : 0 < τ := by dsimp [τ]; linarith
    have hτT : τ < T := by dsimp [τ]; linarith
    have hτmem : τ ∈ Set.Ioo (0 : ℝ) T := ⟨hτ0, hτT⟩
    have hτpaper : PaperPositiveInitialDatum intervalDomain (u τ) :=
      UniformContinuation.classicalSolution_slice_paperPositiveInitialDatum hsol hτmem
    have hτfloor : ∀ x, c' ≤ u τ x := fun x =>
      (min_le_left c η).trans (hpersist τ (by dsimp [τ]; linarith) hτT x)
    obtain ⟨w, z, hsolw, htracew⟩ :=
      hfactory (u τ) hτpaper.toPositive (hslice_bound τ hτ0 hτT) hτfloor
    have hshift : IsPaper2ClassicalSolution intervalDomain p (T - τ)
        (fun t x => u (t + τ) x) (fun t x => v (t + τ) x) :=
      TimeShift.classicalSolution_timeShift TimeShift.regularityTimeShiftWorks
        hsol hτ0 hτT
    have hshiftTrace : InitialTrace intervalDomain (u τ) (fun t x => u (t + τ) x) :=
      GlueExtension.timeShiftInitialTraceWorks hsol hτ0 hτT
    have huniq : IntervalClassicalSolutionOverlapUniqueAt p (u τ) :=
      positiveCriticalOverlapUniqueAt_allExponents
        p hguard hβ hm hχ hthreshold hτpaper
    have hmin : min (T - τ) δ = T - τ := by
      dsimp [τ]
      rw [min_eq_left]
      linarith
    have hoverU : ∀ s, τ < s → s < T → ∀ x,
        u s x = w (s - τ) x := by
      intro s hsτ hsT x
      have hs := huniq
        { T_pos := by dsimp [τ]; linarith
          u := fun t x => u (t + τ) x
          v := fun t x => v (t + τ) x
          sol := hshift, trace := hshiftTrace }
        { T_pos := hδ, u := w, v := z, sol := hsolw, trace := htracew }
        (s - τ) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.1
    have hoverV : ∀ s, τ < s → s < T → ∀ x,
        v s x = z (s - τ) x := by
      intro s hsτ hsT x
      have hs := huniq
        { T_pos := by dsimp [τ]; linarith
          u := fun t x => u (t + τ) x
          v := fun t x => v (t + τ) x
          sol := hshift, trace := hshiftTrace }
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
    refine ⟨T', by dsimp [T']; linarith, hT', _, _, hsol', htrace'⟩

/-- Every prescribed finite horizon is reachable from a paper-positive datum
in the positive critical branch. -/
theorem positiveCritical_reachableArbitrarilyLong_allExponents
    (p : CM2Params)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hχ : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ReachableArbitrarilyLong p u₀ := by
  let hlocal := intervalDomain_localExistence_paperPositive_allExponents p
  have huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀ :=
    positiveCriticalOverlapUniqueAt_allExponents
      p hguard hβ hm hχ hthreshold hu₀
  by_cases hbdd : BddAbove (reachableClassicalHorizonSet p u₀)
  · obtain ⟨T₀, hT₀, u₀sol, v₀sol, hsol₀, htrace₀⟩ := hlocal u₀ hu₀
    have hreach₀ : ReachableClassicalHorizon p u₀ T₀ :=
      ⟨hT₀, u₀sol, v₀sol, hsol₀, htrace₀⟩
    have hne : (reachableClassicalHorizonSet p u₀).Nonempty := ⟨T₀, hreach₀⟩
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
        (positiveCritical_reachablePast_of_bounded_allExponents
          p hguard hβ hm hχ hthreshold hu₀ hsol.T_pos hsol htrace hbound))
  · exact reachableArbitrarilyLong_of_not_bddAbove hbdd

/-- Canonical global solution and the horizon-independent affine-restart
bound, for all positive exponents. -/
theorem positiveCriticalGlobalSolution_allExponents
    (p : CM2Params)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hχ : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
      InitialTrace intervalDomain u₀ u ∧
      IsPaper2Bounded intervalDomain u := by
  have huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀ :=
    positiveCriticalOverlapUniqueAt_allExponents
      p hguard hβ hm hχ hthreshold hu₀
  have hreach := positiveCritical_reachableArbitrarilyLong_allExponents
    p hguard hβ hm hχ hthreshold hu₀
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolution_of_reachableArbitrarilyLong_of_overlapUniqueAt
      huniq hu₀.toPositive hreach
  have hbounded : IsPaper2Bounded intervalDomain u :=
    critical_bounded_global_positive_restarted_affine_intervalDomain
      hguard hu₀.toPositive hglobal htrace hβ hm hχ hthreshold
  exact ⟨u, v, hglobal, htrace, hbounded⟩

/-- Fully unconditional, non-vacuous positive critical branch of Theorem 1.2.
There are no exponent lower bounds and no external Cauchy-theory hypotheses. -/
theorem Theorem_1_2_intervalDomain_positive_critical_branch_unconditional
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b) (hχ : 0 < p.χ₀) :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
          InitialTrace intervalDomain u₀ u ∧
          IsPaper2Bounded intervalDomain u := by
  intro hβ hm hthreshold u₀ hu₀
  exact positiveCriticalGlobalSolution_allExponents
    p hguard hβ hm hχ hthreshold u₀ hu₀

/-- Maximal-continuation formulation of the same all-exponent result. -/
theorem correctedTheorem12_positiveCriticalBranch_unconditional
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b) (hχ : 0 < p.χ₀)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hthreshold : p.χ₀ < chiBeta p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        Nonempty (Paper2MaximalContinuation intervalDomain p u₀) ∧
        ∀ branch : Paper2MaximalContinuation intervalDomain p u₀,
          branch.IsGlobal ∧ branch.IsBounded := by
  intro u₀ hu₀
  obtain ⟨u, v, hglobal, htrace, hbounded⟩ :=
    positiveCriticalGlobalSolution_allExponents
      p hguard hβ hm hχ hthreshold u₀ hu₀
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

#print axioms positiveCritical_minimumPersistence_of_bounded_allExponents
#print axioms positiveCritical_reachablePast_of_bounded_allExponents
#print axioms positiveCritical_reachableArbitrarilyLong_allExponents
#print axioms positiveCriticalGlobalSolution_allExponents
#print axioms Theorem_1_2_intervalDomain_positive_critical_branch_unconditional
#print axioms correctedTheorem12_positiveCriticalBranch_unconditional

end ShenWork.Paper2.IntervalDomainM

end
