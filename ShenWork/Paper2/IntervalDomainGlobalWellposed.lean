import ShenWork.Paper2.IntervalLemma31Closure
/-
  ShenWork/Paper2/IntervalDomainGlobalWellposed.lean

  Top-level assembly for interval-domain global existence.

  This file deliberately sits above both layers:
  * `PDE.IntervalDomainExistence` supplies local existence, maximal
    continuation skeletons, and the corrected existential-global interface;
  * `Paper2.IntervalDomainMoserClosure` supplies the downstream finite-horizon
    boundedness machinery.

  Keeping this composition here avoids the import cycle
  `IntervalDomainExistence -> Theorem11/MoserClosure -> IntervalDomainExistence`.
-/
import ShenWork.PDE.IntervalDomainExistence
import ShenWork.Paper2.IntervalDomainMoserClosure
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

open ShenWork.Paper2
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence

noncomputable section

namespace ShenWork.Paper2.IntervalDomainGlobalWellposed

/-- From Lemma 3.1 monotonicity on `(0,t]` and initial sup-norm approach,
derive `supNorm(u t) <= supNorm u₀`. -/
private theorem supNorm_le_initial_of_Ioc_monotone_and_approach
    {u : ℝ → intervalDomain.Point → ℝ} {u₀ : intervalDomain.Point → ℝ}
    {t : ℝ} (ht_pos : 0 < t)
    (hmono : SupNormNonincreasingOn intervalDomain u (Set.Ioc (0 : ℝ) t))
    (happroach : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε) :
    intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  by_contra h_gt
  push Not at h_gt
  set gap := intervalDomain.supNorm (u t) - intervalDomain.supNorm u₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := happroach (gap / 2) (by linarith)
  set s := min (δ / 2) (t / 2) with hs_def
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_le_t : s ≤ t :=
    le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hs_in_Ioc : s ∈ Set.Ioc (0 : ℝ) t := ⟨hs_pos, hs_le_t⟩
  have ht_in_Ioc : t ∈ Set.Ioc (0 : ℝ) t := ⟨ht_pos, le_rfl⟩
  have h_mono := hmono s hs_in_Ioc t ht_in_Ioc hs_le_t
  have h_approach := hδ_bound s hs_pos hs_lt_δ
  linarith

/-- From Lemma 3.1 monotonicity on `(0,T)` and initial sup-norm approach,
derive `supNorm(u t) <= supNorm u₀`. -/
private theorem supNorm_le_initial_of_Ioo_monotone_and_approach
    {u : ℝ → intervalDomain.Point → ℝ} {u₀ : intervalDomain.Point → ℝ}
    {T : ℝ} (_hT : 0 < T)
    (hmono : SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) T))
    (happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < T) :
    intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  by_contra h_gt
  push Not at h_gt
  set gap := intervalDomain.supNorm (u t) - intervalDomain.supNorm u₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith
  obtain ⟨δ, hδ_pos, _hδ_le_T, hδ_bound⟩ :=
    happroach (gap / 2) (by linarith)
  set s := min (δ / 2) (t / 2) with hs_def
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_lt_t : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs_lt_T : s < T := lt_trans hs_lt_t ht_lt
  have hs_in_Ioo : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs_pos, hs_lt_T⟩
  have ht_in_Ioo : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht_pos, ht_lt⟩
  have h_mono := hmono s hs_in_Ioo t ht_in_Ioo hs_lt_t.le
  have h_approach := hδ_bound s hs_pos hs_lt_δ
  linarith

/-- Nonminimal branch sup-norm estimate from Lemma 3.1 plus the corrected
initial sup-norm approach field. -/
theorem nonminimal_supNorm_bound_of_corrected_initial_approach
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomain.Point → ℝ} {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε) :
    ∀ t, 0 < t → t < T →
      intervalDomain.supNorm (u t) ≤
        max (intervalDomain.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)) := by
  intro t ht_pos ht_lt
  by_cases h_below :
      intervalDomain.supNorm (u t) ≤ (p.a / p.b) ^ (1 / p.α)
  · exact le_trans h_below (le_max_right _ _)
  · push Not at h_below
    have hL31 := ShenWork.Paper2.Lemma31Closure.Lemma_3_1_intervalDomain p
    have hmono :=
      (hL31 hχ).1 ha hb T hT u v hsol t ht_pos ht_lt h_below
    have h_le_init :=
      supNorm_le_initial_of_Ioc_monotone_and_approach ht_pos hmono
        (fun ε hε => by
          obtain ⟨δ, hδ_pos, _hδ_le, hδ_bound⟩ := happroach ε hε
          exact ⟨δ, hδ_pos, hδ_bound⟩)
    exact le_trans h_le_init (le_max_left _ _)

/-- Minimal branch sup-norm estimate from Lemma 3.1 plus the corrected initial
sup-norm approach field. -/
theorem minimal_supNorm_bound_of_corrected_initial_approach
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u₀ : intervalDomain.Point → ℝ} {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε) :
    ∀ t, 0 < t → t < T →
      intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ := by
  intro t ht_pos ht_lt
  have hL31 := ShenWork.Paper2.Lemma31Closure.Lemma_3_1_intervalDomain p
  have hmono := (hL31 hχ).2 ha hb T hT u v hsol
  exact supNorm_le_initial_of_Ioo_monotone_and_approach
    hT hmono happroach ht_pos ht_lt

/-- Nonminimal negative-sensitivity finite-horizon boundedness using only the
corrected initial-approach mechanism, not the legacy same-tail existence
package. -/
theorem boundedBefore_nonminimal_of_corrected_initial_approach
    (p : CM2Params)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε := by
    intro ε hε
    exact ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
      p u₀ hu₀ (hboundedInitial u₀ hu₀) hT hsol htrace hε
  refine ⟨max (intervalDomain.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  exact nonminimal_supNorm_bound_of_corrected_initial_approach
    p hχ ha hb hT hsol happroach

/-- Minimal negative-sensitivity finite-horizon boundedness using only the
corrected initial-approach mechanism. -/
theorem boundedBefore_minimal_of_corrected_initial_approach
    (p : CM2Params)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε := by
    intro ε hε
    exact ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
      p u₀ hu₀ (hboundedInitial u₀ hu₀) hT hsol htrace hε
  refine ⟨intervalDomain.supNorm u₀, ?_⟩
  exact minimal_supNorm_bound_of_corrected_initial_approach
    p hχ ha hb hT hsol happroach

/-- Spatial time-slice boundedness gives the pointwise control needed to turn
an interval-domain sup-norm bound into exclusion of pointwise blow-up. -/
theorem supNormControlsPointwiseBefore_of_timeSlice_rangeBounded
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hrangeBounded :
      ∀ t, 0 < t → t < T →
        BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|))) :
    ShenWork.IntervalDomainExistence.SupNormControlsPointwiseBefore T u :=
  ShenWork.IntervalDomainExistence.supNormControlsPointwiseBefore_of_bddAbove_abs
    hrangeBounded

/-- Nonminimal branch: local existence, maximal continuation, finite-horizon
boundedness, and gluing yield the corrected existential-global package. -/
theorem intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hsupControls :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ShenWork.IntervalDomainExistence.SupNormControlsPointwiseBefore T u)
    (hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p) :
    ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p := by
  refine
    intervalDomainGlobalSolutionExists_of_boundedContinuation_and_gluing
      p hlocal hboundedInitial hrealize
      hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative
      ?_ hsupControls hglue
  intro u₀ hu₀ T hT u v hsol htrace
  exact boundedBefore_nonminimal_of_corrected_initial_approach
    p hboundedInitial hχ ha hb hu₀ hT hsol htrace

/-- Minimal branch: local existence, maximal continuation, finite-horizon
boundedness, and gluing yield the corrected existential-global package. -/
theorem intervalDomainGlobalSolutionExists_minimal_of_continuation_and_gluing
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hsupControls :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ShenWork.IntervalDomainExistence.SupNormControlsPointwiseBefore T u)
    (hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p) :
    ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p := by
  refine
    intervalDomainGlobalSolutionExists_of_boundedContinuation_and_gluing
      p hlocal hboundedInitial hrealize
      hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative
      ?_ hsupControls hglue
  intro u₀ hu₀ T hT u v hsol htrace
  exact boundedBefore_minimal_of_corrected_initial_approach
    p hboundedInitial hχ ha hb hu₀ hT hsol htrace

/-- Corrected-existence bridge for Paper 2 Theorem 1.1 on `intervalDomain`.

The global branch chooses the continued global solution supplied by
`IntervalDomainGlobalSolutionExists`; the finite-time sup-norm estimates are
proved from Lemma 3.1 and the corrected initial-approach field. -/
theorem Theorem_1_1_intervalDomain_of_corrected_global_existence
    (p : CM2Params)
    (hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p) :
    Theorem_1_1 intervalDomain p := by
  intro hχ
  constructor
  · intro ha hb u₀ hu₀
    by_cases hm : 1 ≤ p.m
    · obtain ⟨u, v, hglobal, htrace⟩ :=
        hexist.globalSolutionExists u₀ hu₀ hm
      have hT : (0 : ℝ) < 1 := by norm_num
      have hsol : IsPaper2ClassicalSolution intervalDomain p 1 u v :=
        hglobal.classical hT
      refine ⟨1, hT, u, v, hsol, htrace, ?_, fun _ => hglobal⟩
      exact nonminimal_supNorm_bound_of_corrected_initial_approach
        p hχ ha hb hT hsol
        (hexist.initialSupNormApproach u₀ hu₀ 1 hT u v hsol htrace)
    · obtain ⟨T, hT, u, v, hsol, htrace⟩ :=
        hexist.localExistence u₀ hu₀
      refine ⟨T, hT, u, v, hsol, htrace, ?_, ?_⟩
      · exact nonminimal_supNorm_bound_of_corrected_initial_approach
          p hχ ha hb hT hsol
          (hexist.initialSupNormApproach u₀ hu₀ T hT u v hsol htrace)
      · intro hm'
        exact False.elim (hm hm')
  · intro ha hb u₀ hu₀
    by_cases hm : 1 ≤ p.m
    · obtain ⟨u, v, hglobal, htrace⟩ :=
        hexist.globalSolutionExists u₀ hu₀ hm
      have hT : (0 : ℝ) < 1 := by norm_num
      have hsol : IsPaper2ClassicalSolution intervalDomain p 1 u v :=
        hglobal.classical hT
      refine ⟨1, hT, u, v, hsol, htrace, ?_, fun _ => hglobal⟩
      exact minimal_supNorm_bound_of_corrected_initial_approach
        p hχ ha hb hT hsol
        (hexist.initialSupNormApproach u₀ hu₀ 1 hT u v hsol htrace)
    · obtain ⟨T, hT, u, v, hsol, htrace⟩ :=
        hexist.localExistence u₀ hu₀
      refine ⟨T, hT, u, v, hsol, htrace, ?_, ?_⟩
      · exact minimal_supNorm_bound_of_corrected_initial_approach
          p hχ ha hb hT hsol
          (hexist.initialSupNormApproach u₀ hu₀ T hT u v hsol htrace)
      · intro hm'
        exact False.elim (hm hm')

/-! ### Internal collapse of `extend_finite` into `extend_mge`

In the regime `1 ≤ p.m` that drives the global-existence path (the only regime
in which `IntervalDomainGlobalSolutionExists.globalSolutionExists` is invoked),
the `extend_finite` hypothesis of the standard maximal-continuation interface
is internally derivable from `extend_mge` plus the unconditional Lemma 3.1 +
spatial regularity machinery already in the repo.  Three ingredients:

1. `mgeOneFiniteHorizonAlternative_imp_finiteHorizonAlternative` — pure logical
   implication on the disjunction (`MGeOne` is the unboundedness disjunct
   of `Finite`).

2. `not_mgeOneFiniteHorizonAlternative_of_realize_in_negative_regime` —
   internally derive `¬ MGeOneFiniteHorizonAlternative` at the realized `T*`,
   by combining
     - `boundedBefore_nonminimal_of_corrected_initial_approach` (Lemma 3.1 +
       initial sup-norm approach gives a sup-norm bound on the open `(0, T*)`),
     - `supNormControlsPointwiseBefore_of_timeSlice_rangeBounded` (regularity
       conjunct (7), already discharged by `classicalSolution_u_range_bddAbove`),
     - `not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore`.

3. Consequence: when invoking the maximal-continuation alternative inside the
   `1 ≤ p.m` branch, `¬ Finite → ¬ MGeOne`, and `hextend_mge` produces the
   contradicting `ReachablePast`.  No use is ever made of `hextend_finite` in
   this branch, so it can be dropped from the umbrella interface.

This is genuine internal progress on the maximal-continuation theorem: the
`extend_finite` PDE-textbook input is **eliminated** from the umbrella's
hypothesis surface, leaving only `realize` and `extend_mge` as the two genuine
analytic frontiers (compactness at `sSup` + restart past `sSup`). -/

/-- The `MGeOne` blow-up alternative implies the `Finite` continuation
alternative: the `Finite` alternative is the disjunction "blow up OR vanish",
of which `MGeOne` is the first disjunct. -/
lemma mgeOneFiniteHorizonAlternative_imp_finiteHorizonAlternative
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (h : MGeOneFiniteHorizonAlternative intervalDomain T u) :
    FiniteHorizonAlternative intervalDomain T u :=
  Or.inl h

/-- Contrapositive of the previous: `¬ Finite → ¬ MGeOne`. -/
lemma not_mgeOneFiniteHorizonAlternative_of_not_finiteHorizonAlternative
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (h : ¬ FiniteHorizonAlternative intervalDomain T u) :
    ¬ MGeOneFiniteHorizonAlternative intervalDomain T u :=
  fun hmge => h (mgeOneFiniteHorizonAlternative_imp_finiteHorizonAlternative hmge)

/-- Internal derivation of `¬ MGeOneFiniteHorizonAlternative` at any realized
classical horizon in the negative-sensitivity regime, using only the
unconditional Lemma 3.1 + initial sup-norm approach + closed-domain spatial
`C²` regularity (conjunct (7)).  No PDE-textbook continuation input is
consumed. -/
theorem not_mgeOneFiniteHorizonAlternative_of_realize_in_negative_regime
    (p : CM2Params)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    ¬ MGeOneFiniteHorizonAlternative intervalDomain T u := by
  -- Lemma 3.1 + corrected initial-approach gives a sup-norm bound on (0, T).
  have hbdd : IsPaper2BoundedBefore intervalDomain T u :=
    boundedBefore_nonminimal_of_corrected_initial_approach
      p hboundedInitial hχ ha hb hu₀ hT hsol htrace
  -- Conjunct (7) of regularity (closed-Icc spatial C²) plus continuity-on-compact
  -- gives that every time slice has a bounded absolute-value range.
  have hrange :
      ∀ t, 0 < t → t < T →
        BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
    intro t ht_pos ht_T
    exact ShenWork.Paper2.classicalSolution_u_range_bddAbove hsol ⟨ht_pos, ht_T⟩
  -- Spatial sup-norm controls the per-time-slice point values.
  have hsup :
      ShenWork.IntervalDomainExistence.SupNormControlsPointwiseBefore T u :=
    supNormControlsPointwiseBefore_of_timeSlice_rangeBounded hrange
  -- Combine for a pointwise upper bound below T.
  have hpw :
      ShenWork.IntervalDomainExistence.PointwiseBoundedBefore T u :=
    ShenWork.IntervalDomainExistence.pointwiseBoundedBefore_of_boundedBefore_and_supNormControls
      hbdd hsup
  -- Pointwise upper bound rules out the (m ≥ 1) blow-up alternative.
  exact
    ShenWork.IntervalDomainExistence.not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore
      hpw

/-- **Direct global branch from `extend_mge` only (no `extend_finite`).**

In the negative-sensitivity regime with `1 ≤ p.m`, the
`hextend_of_not_finiteAlternative` field of the standard maximal-continuation
interface is internally redundant: given `hrealize` and `hextend_of_not_mgeAlternative`,
plus the unconditional Lemma 3.1 + closed-domain spatial `C²` regularity,
one can directly contradict any putative bounded upper bound on the reachable
horizon set, yielding `ReachableArbitrarilyLong`.

Proof sketch:
1. Assume for contradiction `hbdd : BddAbove (reachableClassicalHorizonSet p u₀)`.
2. By `hrealize`, get a classical solution `(u, v)` on `[0, T*)` with the
   prescribed initial trace, where `T* = finiteMaximalReachableHorizon p u₀ > 0`.
3. Internally derive `¬ MGeOneFiniteHorizonAlternative T* u` from Lemma 3.1 +
   initial-approach + conjunct (7) of regularity
   (`not_mgeOneFiniteHorizonAlternative_of_realize_in_negative_regime`).
4. By `hextend_of_not_mgeAlternative`, obtain `ReachablePast p u₀ T*`,
   contradicting `not_reachablePast_finiteMaximalReachableHorizon`.

The `extend_finite` hypothesis is never consumed. -/
theorem reachableArbitrarilyLong_of_realize_extend_mge_in_negative_regime
    (p : CM2Params)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hm : 1 ≤ p.m) :
    ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ := by
  by_contra hnot
  -- From the negation, derive that reachable horizons are bounded above.
  -- Use the contrapositive of `reachableArbitrarilyLong_of_not_bddAbove`.
  by_cases hbdd :
      BddAbove (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀)
  · -- Bounded case: extract realized solution at T*, derive contradiction.
    have hT_pos :
        0 < ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon p u₀ :=
      ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon_pos_of_localExistence
        p hlocal hu₀ hbdd
    obtain ⟨u, v, hsol, htrace⟩ := hrealize u₀ hu₀ hbdd
    have hnotMge :
        ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon p u₀) u :=
      not_mgeOneFiniteHorizonAlternative_of_realize_in_negative_regime
        p hboundedInitial hχ ha hb hu₀ hT_pos hsol htrace
    have hpast :
        ShenWork.IntervalDomainExistence.ReachablePast p u₀
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon p u₀) :=
      hextend_of_not_mgeAlternative u₀ hu₀ hbdd hsol htrace hm hnotMge
    exact
      ShenWork.IntervalDomainExistence.not_reachablePast_finiteMaximalReachableHorizon
        hbdd hpast
  · -- Unbounded case: contradicts `hnot` by `reachableArbitrarilyLong_of_not_bddAbove`.
    exact hnot
      (ShenWork.IntervalDomainExistence.reachableArbitrarilyLong_of_not_bddAbove hbdd)

/-- **Refined existential-global package: nonminimal branch, `extend_finite`
eliminated.**  Same conclusion as
`intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing`,
but with the `hextend_of_not_finiteAlternative` hypothesis removed: it is
internally redundant in the `1 ≤ p.m` regime that drives the global branch,
because `¬ MGeOneFiniteHorizonAlternative` at the realized `T*` follows from
Lemma 3.1 + initial-approach + closed-domain spatial `C²` regularity, and
`hextend_of_not_mgeAlternative` alone suffices to contradict the bounded-supremum
assumption. -/
theorem
    intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing_no_extend_finite
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p) :
    ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p := by
  refine intervalDomainGlobalSolutionExists_of_local_global_bounded_initial
    p hlocal hboundedInitial ?_
  intro u₀ hu₀ hm
  -- Build ReachableArbitrarilyLong directly via the no-extend_finite chain.
  have hlong :
      ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀ :=
    reachableArbitrarilyLong_of_realize_extend_mge_in_negative_regime
      p hboundedInitial hχ ha hb hlocal hrealize hextend_of_not_mgeAlternative
      hu₀ hm
  -- Apply the gluing closure.
  exact hglue u₀ hu₀ hlong

end ShenWork.Paper2.IntervalDomainGlobalWellposed

end
