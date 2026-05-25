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
    have hL31 := ShenWork.Paper2.Lemma_3_1_intervalDomain p
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
  have hL31 := ShenWork.Paper2.Lemma_3_1_intervalDomain p
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

end ShenWork.Paper2.IntervalDomainGlobalWellposed

end
