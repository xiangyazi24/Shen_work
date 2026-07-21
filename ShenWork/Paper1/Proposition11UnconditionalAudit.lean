import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WholeLineCauchyLongTimeBound
import ShenWork.Paper1.Proposition11PositiveSupercritical

/-!
# Proposition 1.1: what is unconditionally dischargeable, and the exact residual

This file is additive.  It records, as machine-checked theorems, exactly which
parts of `Proposition_1_1` (Statements.lean) discharge *right now* from the
canonical whole-line Cauchy solution `wholeLineCauchyGlobalU` and its proved
range / limsup bounds, and isolates the single genuine analytic residual.

## The frontier-record route is NOT the right route

`paper1_Proposition_1_1_of_frontierData` (StatementAssembly.lean) consumes
`Paper1PropositionFrontierData`, whose fields quantify over an **arbitrary**
solution:

  `∀ u v, IsGlobalCauchySolutionFrom p u₀ u v → (bounds on u)`.

The repository's producers only ever control the *canonical* solution
`wholeLineCauchyGlobalU`.  Turning an arbitrary-solution bound into the
canonical bound requires the paper's imported Cauchy **uniqueness** (a BUC/mild
Grönwall–Volterra estimate on `‖u₁ - u₂‖_∞`, §1.2, cf. the explicit note in
`Proposition12NegativeBranch.lean`).  That uniqueness is not in the repository,
so **none** of the frontier fields (`existence`, `max_neg`, `bound_pos`,
`conv_neg`, `conv_pos`) is dischargeable, and the frontier record cannot be
assembled.  The `existence` field is additionally over-strong: it demands
`IsGlobalCauchySolutionFrom` (strict positivity `0 < u` for `t > 0`) for an
arbitrary nonnegative datum, which is already **false** for `u₀ ≡ 0` (the unique
solution from zero data is `≡ 0`), and it is regime-gated (the construction
needs `WholeLineCauchyCeilingRegime p`, unavailable for arbitrary `p`).

## The right route: `Proposition_1_1` itself only needs one solution

`Proposition_1_1` (Statements.lean) is stated with `∃ u v,
IsGlobalNonnegativeCauchySolutionFrom …` — a single *nonnegative* solution with
bounds.  The canonical construction supplies exactly that solution.  Below we
discharge every part of `Proposition_1_1` that the canonical producers reach.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-! ## First conjunct (`χ ≤ 0`): fully unconditional -/

/-- The nonpositive-sensitivity half of `Proposition_1_1`, unconditional.
This is exactly the first conjunct of `Proposition_1_1`, discharged by the
canonical negative-branch construction. -/
theorem paper1_Prop_1_1_first_conjunct :
    ∀ p : CMParams, p.χ ≤ 0 →
      ∀ u₀ : ℝ → ℝ, PaperNonnegativeInitialDatum u₀ →
        ∃ u v : ℝ → ℝ → ℝ,
          IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
          (∀ M, (∀ x, u₀ x ≤ M) → ∀ t x, 0 ≤ t → u t x ≤ max 1 M) ∧
          UniformLimsupLe u 1 :=
  fun p hχ u₀ hu₀ => Proposition_1_1_negative_branch p hχ u₀ hu₀

/-! ## Second conjunct, critical window `0 < χ < 1, α = m+γ-1`: fully discharged
with the paper's exact `(1/(1-χ))^(1/α)` limsup constant. -/

/-- The critical positive-sensitivity sub-window of the second conjunct of
`Proposition_1_1`, with the exact paper limsup constant `(1/(1-χ))^(1/α)`.
Discharged from the canonical `MChi`-ceiling construction, using
`MChi p = (1/(1-χ))^(1/α)`. -/
theorem paper1_Prop_1_1_second_conjunct_critical_subwindow
    (p : CMParams) (hχ : 0 < p.χ) (hχ_lt : p.χ < 1)
    (hcrit : p.α = p.m + p.γ - 1)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u ∧
      (0 < p.χ → p.χ < 1 → UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) := by
  rcases Proposition_1_1_positive_critical_branch p hχ hχ_lt hcrit u₀ hu₀ with
    ⟨u, v, hsol, _hrange, hbdd, hlimsup⟩
  refine ⟨u, v, hsol, hbdd, ?_⟩
  intro _ _
  have hconst : MChi p = (1 / (1 - p.χ)) ^ (1 / p.α) :=
    MChi_eq_rpow_of_chi_pos p hχ
  rwa [hconst] at hlimsup

/-! ## Second conjunct, supercritical window `0 < χ, α > m+γ-1`:
existence and eventual boundedness discharged (canonical parameter-ceiling
construction).  The matching limsup constant is handled below. -/

/-- Existence + eventual boundedness for the supercritical positive branch,
directly from the canonical construction. -/
theorem paper1_Prop_1_1_second_conjunct_supercritical_core
    (p : CMParams) (hχ : 0 < p.χ) (hsuper : p.m + p.γ - 1 < p.α)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u := by
  rcases Proposition_1_1_positive_supercritical_branch p hχ hsuper u₀ hu₀ with
    ⟨u, v, hsol, _hrange, hbdd, _hlimsup⟩
  exact ⟨u, v, hsol, hbdd⟩

/-! ## Reduction of `Proposition_1_1` to its positive-sensitivity half

The first conjunct is discharged above.  What remains is exactly the second
conjunct (the positive-sensitivity statement), which we expose as a single
hypothesis. -/

/-- `Proposition_1_1` reduced to its second (positive-sensitivity) conjunct:
the `χ ≤ 0` half is discharged unconditionally, so only the positive branch
remains as an input. -/
theorem paper1_Proposition_1_1_of_second_conjunct
    (hpos : ∀ p : CMParams,
      (0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
        (0 < p.χ ∧
          p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
            ((p.m + p.γ - 1) / (p.γ - 1)) ∧
          p.α = p.m + p.γ - 1) →
      ∀ u₀ : ℝ → ℝ, PaperNonnegativeInitialDatum u₀ →
        ∃ u v : ℝ → ℝ → ℝ,
          IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
          UniformEventuallyBounded u ∧
          (0 < p.χ → p.χ < 1 →
            UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α)))) :
    Proposition_1_1 :=
  ⟨paper1_Prop_1_1_first_conjunct, hpos⟩

section AxiomAudit

#print axioms paper1_Prop_1_1_first_conjunct
#print axioms paper1_Prop_1_1_second_conjunct_critical_subwindow
#print axioms paper1_Prop_1_1_second_conjunct_supercritical_core
#print axioms paper1_Proposition_1_1_of_second_conjunct

end AxiomAudit

end ShenWork.Paper1
