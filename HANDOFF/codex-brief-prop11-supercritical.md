# Codex Brief — Prop 1.1(2) supercritical branch assembly

Repo ~/Shen_work (HEAD b85cea95). Rules: 0 sorry, 0 axiom, NEW file only,
`lake build ShenWork.Paper1.<Module>` green before claiming done. Do NOT commit.
You may append one import line to ShenWork.lean.

Everything needed is committed:
- `wholeLineCauchyGlobal_uniformLimsupLe_parameterCeiling_of_chi_pos_supercritical`
  and `wholeLineCauchyGlobal_le_max_of_chi_pos_supercritical`
  (ShenWork/Paper1/WholeLineChiPosSupercriticalLongTimeBound.lean) — for
  `hχ : 0 < p.χ` and `hsuper : p.m + p.γ - 1 < p.α`, NO smallness on χ.
- `Proposition_1_1_positive_critical_branch`
  (ShenWork/Paper1/Proposition11PositiveCritical.lean) — the pattern to mirror
  (global nonneg solution + range bound + UniformEventuallyBounded + limsup).
- `wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom`,
  `wholeLineCauchyGlobal_nonnegative` (need a WholeLineCauchyCeilingRegime; in the
  supercritical case construct it internally as `Or.inr ⟨hχ.le, Or.inl hsuper⟩`).

TASK: new file ShenWork/Paper1/Proposition11PositiveSupercritical.lean proving

theorem Proposition_1_1_positive_supercritical_branch
    (p : CMParams) (hχ : 0 < p.χ) (hsuper : p.m + p.γ - 1 < p.α)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      (∀ t x, 0 ≤ t → u t x ≤
        max (wholeLineCauchyParameterCeiling p) ‖wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1‖) ∧
      UniformEventuallyBounded u ∧
      UniformLimsupLe u (wholeLineCauchyParameterCeiling p)

mirroring Proposition11PositiveCritical.lean line by line (the UniformEventuallyBounded
witness comes from the range bound plus nonnegativity via abs_of_nonneg).

THEN, in the same file, a combined statement covering BOTH positive branches:

theorem Proposition_1_1_positive_branches_of_regime
    (p : CMParams) (hχ : 0 < p.χ)
    (hbranch : (p.m + p.γ - 1 < p.α) ∨ (p.χ < chiStar p ∧ p.α = p.m + p.γ - 1))
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧ UniformEventuallyBounded u

(the two ceilings differ, so the common conclusion keeps only global existence +
eventual boundedness — which is exactly the paper's (1.10)). Case-split on hbranch.

Report per-item build status and the exact statement you landed.
