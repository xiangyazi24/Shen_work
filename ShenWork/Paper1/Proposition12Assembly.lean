import ShenWork.Paper1.Proposition12NegativeBranch

/-!
# Paper 1, Proposition 1.2 — assembly through the closed negative branch

`Proposition_1_2` (Statements.lean) now quantifies over the paper-faithful
phase space `PaperNonnegativeInitialDatum` (bounded and uniformly continuous,
eq. (1.7) `C_unif^b(ℝ)`), so the landed unconditional negative-branch theorem
`Proposition_1_2_negative_branch` discharges its first conjunct verbatim.

This file records that reduction: the whole headline is now equivalent to its
positive-sensitivity conjunct (`0 < χ < 1/2`, `m + γ - 1 ≤ α`), which is the
remaining open branch.
-/

noncomputable section

namespace ShenWork.Paper1

/-- The remaining open content of Proposition 1.2: the positive-sensitivity
convergence branch. -/
def Proposition12PositiveBranch : Prop :=
  ∀ p : CMParams, 0 < p.χ → p.χ < (1 / 2 : ℝ) →
    p.m + p.γ - 1 ≤ p.α →
    ∀ u₀ : ℝ → ℝ, PaperNonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1

/-- Proposition 1.2 reduces to its positive-sensitivity branch: the negative
branch is discharged by the unconditional `Proposition_1_2_negative_branch`. -/
theorem Proposition_1_2.of_positive_branch
    (hpos : Proposition12PositiveBranch) :
    Proposition_1_2 :=
  ⟨fun p hχ u₀ hu₀ hu₀_pos =>
      Proposition_1_2_negative_branch p hχ u₀ hu₀ hu₀_pos,
    hpos⟩

end ShenWork.Paper1
