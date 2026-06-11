import ShenWork.Paper2.IntervalLemma31Closure
import ShenWork.PDE.IntervalDomainExistence

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.ChiNegativeResidual

/-- From Lemma 3.1 monotonicity on `(0,t]` and initial sup-norm approach,
derive `supNorm (u t) <= supNorm u₀`. -/
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

/-- The nonminimal `a,b>0` Theorem 1.1 sup-norm estimate, proved directly from
the already-proved interval Lemma 3.1 plus the concrete initial-trace approach.

This theorem is the bound half of the χ₀<0 assembly: it assumes a classical
coupled solution already exists, and it supplies the stated bound. -/
theorem nonminimal_supNorm_bound_from_Lemma_3_1_intervalDomain_and_trace
    (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    ∀ t, 0 < t → t < T →
      intervalDomain.supNorm (u t) ≤
        max (intervalDomain.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)) := by
  have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε := by
    intro ε hε
    exact initialSupNormApproach_intervalDomain p u₀ hu₀ hu₀.admissible.1
      hT hsol htrace hε
  intro t ht_pos ht_lt
  by_cases h_below :
      intervalDomain.supNorm (u t) ≤ (p.a / p.b) ^ (1 / p.α)
  · exact le_trans h_below (le_max_right _ _)
  · push Not at h_below
    have hL31 := Lemma31Closure.Lemma_3_1_intervalDomain p
    have hmono :=
      (hL31 hχ).1 ha hb T hT u v hsol t ht_pos ht_lt h_below
    have h_le_init :=
      supNorm_le_initial_of_Ioc_monotone_and_approach ht_pos hmono
        (fun ε hε => by
          obtain ⟨δ, hδ_pos, _hδ_le, hδ_bound⟩ := happroach ε hε
          exact ⟨δ, hδ_pos, hδ_bound⟩)
    exact le_trans h_le_init (le_max_left _ _)

/-- Precise residual for the χ₀<0, `a,b>0` interval-domain Theorem 1.1
assembly.

The first field is the coupled-flux classical local Cauchy problem for every
positive datum.  The second field is the global classical solution existence
needed only when the theorem's `1 <= m` conclusion is active.  Initial
sup-norm approach is not a residual here: for `intervalDomain` it follows from
`InitialTrace` by `initialSupNormApproach_intervalDomain`. -/
structure ChiNegativeNonminimalCoupledExistenceResidual
    (p : CM2Params) : Prop where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  globalSolutionExists :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        1 ≤ p.m →
          ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
            InitialTrace intervalDomain u₀ u

/-- The repository's corrected global-existence package is stronger than the
χ₀<0 nonminimal residual named above. -/
theorem chiNegativeResidual_of_intervalDomainGlobalSolutionExists
    (p : CM2Params)
    (hexist : IntervalDomainGlobalSolutionExists p) :
    ChiNegativeNonminimalCoupledExistenceResidual p :=
  ⟨hexist.localExistence, hexist.globalSolutionExists⟩

/-- Nonminimal branch of Theorem 1.1 for χ₀<0, conditional exactly on the
coupled-existence residual.  The displayed sup-norm bound is supplied by
`Lemma_3_1_intervalDomain`. -/
theorem chiNegative_nonminimal_branch_of_coupledResidual
    (p : CM2Params) (hχ : p.χ₀ < 0)
    (H : ChiNegativeNonminimalCoupledExistenceResidual p) :
    0 < p.a → 0 < p.b →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u ∧
            (∀ t, 0 < t → t < Tmax →
              intervalDomain.supNorm (u t) ≤
                max (intervalDomain.supNorm u₀) ((p.a / p.b) ^ (1 / p.α))) ∧
            (1 ≤ p.m → IsPaper2GlobalClassicalSolution intervalDomain p u v) := by
  intro ha hb u₀ hu₀
  by_cases hm : 1 ≤ p.m
  · obtain ⟨u, v, hglobal, htrace⟩ := H.globalSolutionExists u₀ hu₀ hm
    have hT : (0 : ℝ) < 1 := by norm_num
    have hsol : IsPaper2ClassicalSolution intervalDomain p 1 u v :=
      hglobal.classical hT
    refine ⟨1, hT, u, v, hsol, htrace, ?_, fun _ => hglobal⟩
    exact nonminimal_supNorm_bound_from_Lemma_3_1_intervalDomain_and_trace
      p (le_of_lt hχ) ha hb hu₀ hT hsol htrace
  · obtain ⟨T, hT, u, v, hsol, htrace⟩ := H.localExistence u₀ hu₀
    refine ⟨T, hT, u, v, hsol, htrace, ?_, ?_⟩
    · exact nonminimal_supNorm_bound_from_Lemma_3_1_intervalDomain_and_trace
        p (le_of_lt hχ) ha hb hu₀ hT hsol htrace
    · intro hm'
      exact False.elim (hm hm')

/-- χ₀<0, `a,b>0` assembly of Paper 2 Theorem 1.1 on `intervalDomain`,
conditional on the precise coupled-existence residual.  The hypotheses
`1 <= α` and `1 <= γ` are part of the paper regime, but this final wiring does
not consume them once the residual has produced the coupled classical
solutions. -/
theorem Theorem_1_1_intervalDomain_chiNegative_nonminimal_of_coupledResidual
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (_hb : 0 < p.b)
    (_hα : 1 ≤ p.α) (_hγ : 1 ≤ p.γ)
    (H : ChiNegativeNonminimalCoupledExistenceResidual p) :
    Theorem_1_1 intervalDomain p := by
  intro _hχ_nonpos
  constructor
  · exact chiNegative_nonminimal_branch_of_coupledResidual p hχ H
  · intro ha0 _hb0 _u₀ _hu₀
    exact False.elim ((ne_of_gt ha) ha0)

end ShenWork.Paper2.ChiNegativeResidual
