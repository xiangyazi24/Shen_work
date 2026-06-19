import ShenWork.PaperOne.WholeLineMildMap

open MeasureTheory Filter Topology Real

noncomputable section

namespace ShenWork.PaperOne

private def obstructionParams : CMParams where
  m := 1
  α := 1
  γ := 1
  χ := 0
  hm := by norm_num
  hα := by norm_num
  hγ := by norm_num

/-- The requested lower pointwise logistic margin is not a consequence of the
constant-barrier trap, even in the admissible `χ ≤ 0` branch. -/
theorem wholeLine_logistic_lower_margin_from_trap_fails :
    ∃ p : CMParams, p.χ ≤ 0 ∧
      ∃ U : ℝ → ℝ, (∀ x, (1 : ℝ) ≤ U x ∧ U x ≤ 2) ∧
        ¬ (∀ x, (1 : ℝ) ≤ wholeLineReaction p U x) := by
  refine ⟨obstructionParams, by norm_num [obstructionParams], fun _ : ℝ => (2 : ℝ), ?_⟩
  constructor
  · intro x
    norm_num
  · intro h
    have hbad := h 0
    norm_num [wholeLineReaction, obstructionParams] at hbad

/-- Equivalently, the uniform theorem shape `trap -> lo ≤ L(U)` is false. -/
theorem wholeLine_logistic_lower_bound_on_constant_barrier_trap_fails :
    ¬ (∀ U : ℝ → ℝ, (∀ x, (1 : ℝ) ≤ U x ∧ U x ≤ 2) →
      ∀ x, (1 : ℝ) ≤ wholeLineReaction obstructionParams U x) := by
  intro h
  have htrap : ∀ x : ℝ, (1 : ℝ) ≤ (fun _ : ℝ => (2 : ℝ)) x ∧
      (fun _ : ℝ => (2 : ℝ)) x ≤ 2 := by
    intro x
    norm_num
  have hbad := h (fun _ : ℝ => (2 : ℝ)) htrap 0
  norm_num [wholeLineReaction, obstructionParams] at hbad

#print axioms wholeLine_logistic_lower_margin_from_trap_fails
#print axioms wholeLine_logistic_lower_bound_on_constant_barrier_trap_fails

end ShenWork.PaperOne
