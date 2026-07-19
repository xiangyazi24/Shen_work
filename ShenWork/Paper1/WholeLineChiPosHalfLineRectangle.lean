import ShenWork.Paper1.WholeLineChiPosRectangleSqueeze
import ShenWork.Paper1.WholeLineCauchyLeftTailBridge

/-!
# The buffered half-line rectangle iteration (χ>0 left equilibrium)

Abstract layer for the positive-sensitivity analogue of
`wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_neg_natural`.

The whole-line iteration of `WholeLineChiPosRectangleSqueeze` squeezes a
rectangle valid for ALL `x`.  On the front problem the datum is not uniformly
positive, so the rectangle can only be claimed on a co-moving LEFT half-line
`z ≤ x₀`; the resolver bounds then acquire the kernel-tail defect
`τ = exp (-R) / 2` from the mass outside the buffer `[x₀, x₀ + R]`.  That
defect enters the two barrier budgets exactly like the finite-time slack `δ`
already carried by `ChiPosWholeLineRectangleStep`, so the scalar contraction is
unchanged: only the successor CONSTRUCTION differs (buffered comparisons in
place of whole-line ones).

This file isolates the part that does not depend on which comparison produced
the successor: the half-line rectangle, its step relation, and the endgame
delivering `UniformCoMovingLeftEquilibriumConvergence`.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- An eventual rectangle for the co-moving solution on a left half-line. -/
structure ChiPosHalfLineRectangle
    (p : CMParams) (c : ℝ) (u : ℝ → ℝ → ℝ) where
  ell : ℝ
  M : ℝ
  start : ℝ
  cut : ℝ
  ell_pos : 0 < ell
  ell_lt_one : ell < 1
  one_lt_M : 1 < M
  floor_margin : 0 < chiPosFloorGap p M ell
  ceiling_margin : 0 < chiPosCeilingGap p ell M
  bounds : ∀ t, start ≤ t → ∀ z, z ≤ cut →
    ell ≤ coMovingPath c u t z ∧ coMovingPath c u t z ≤ M

/-- The numerical data carried from one half-line round to the next.  The
`cut` is allowed to move left, which is what a growing buffer requires. -/
structure ChiPosHalfLineRectangleStep
    (p : CMParams) {c : ℝ} {u : ℝ → ℝ → ℝ} (δ : ℝ)
    (old new : ChiPosHalfLineRectangle p c u) : Prop where
  ell_le : old.ell ≤ new.ell
  M_le : new.M ≤ old.M
  cut_le : new.cut ≤ old.cut
  floor_budget :
    1 - new.ell ^ p.α ≤
      p.χ * (new.ell ^ (p.m - 1) * (old.M ^ p.γ - new.ell ^ p.γ)) + δ
  ceiling_budget :
    new.M ^ p.α - 1 ≤
      p.χ * (new.M ^ (p.m - 1) * (new.M ^ p.γ - new.ell ^ p.γ)) + δ

/-- The scalar gap contracts exactly as in the whole-line case, under the
paper's full exponent hypothesis `m + γ - 1 ≤ α`. -/
theorem ChiPosHalfLineRectangleStep.gap_le
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ → ℝ} {δ : ℝ}
    {old new : ChiPosHalfLineRectangle p c u}
    (h : ChiPosHalfLineRectangleStep p δ old new)
    (hle : p.m + p.γ - 1 ≤ p.α) (hχ : 0 ≤ p.χ) :
    new.M ^ p.α - new.ell ^ p.α ≤
      2 * p.χ * (old.M ^ p.α - old.ell ^ p.α) + 2 * δ :=
  chiPos_squeeze_gap_step_of_le p.hm p.hγ hle hχ
    old.ell_pos h.ell_le new.ell_lt_one.le new.one_lt_M.le h.M_le
    h.floor_budget h.ceiling_budget

/-- Endgame: if every strict-margin half-line rectangle admits another round,
the co-moving solution converges to the left equilibrium `1` uniformly on
far-left half-lines. -/
theorem uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors
    (p : CMParams) {c : ℝ} {u : ℝ → ℝ → ℝ}
    (hχ : 0 ≤ p.χ) (hχ_half : p.χ < 1 / 2)
    (hle : p.m + p.γ - 1 ≤ p.α)
    (seed : ChiPosHalfLineRectangle p c u)
    (hsuccessor : ∀ δ, 0 < δ → ∀ old : ChiPosHalfLineRectangle p c u,
      Nonempty {new : ChiPosHalfLineRectangle p c u //
        ChiPosHalfLineRectangleStep p δ old new}) :
    UniformCoMovingLeftEquilibriumConvergence c u := by
  intro epsilon hepsilon
  let r : ℝ := 2 * p.χ
  let δ : ℝ := epsilon * (1 - r) / 4
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let next : ChiPosHalfLineRectangle p c u →
      ChiPosHalfLineRectangle p c u := fun old =>
    (Classical.choice (hsuccessor δ hδ old)).1
  have hnext : ∀ old : ChiPosHalfLineRectangle p c u,
      ChiPosHalfLineRectangleStep p δ old (next old) := fun old =>
    (Classical.choice (hsuccessor δ hδ old)).2
  let rectangles : ℕ → ChiPosHalfLineRectangle p c u := fun n =>
    next^[n] seed
  have hrectangleStep : ∀ n,
      ChiPosHalfLineRectangleStep p δ (rectangles n) (rectangles (n + 1)) := by
    intro n
    simpa [rectangles, Function.iterate_succ_apply'] using hnext (rectangles n)
  let gap : ℕ → ℝ := fun n =>
    (rectangles n).M ^ p.α - (rectangles n).ell ^ p.α
  have hgapStep : ∀ n, gap (n + 1) ≤ r * gap n + 2 * δ := by
    intro n
    simpa [gap, r] using (hrectangleStep n).gap_le hle hχ
  have hstationary : (2 * δ) / (1 - r) < epsilon := by
    have heq : (2 * δ) / (1 - r) = epsilon / 2 := by
      dsimp [δ]
      field_simp
      ring
    rw [heq]
    linarith
  obtain ⟨n, hgap⟩ := exists_index_affine_recurrence_lt
    hr0 hr1 (mul_nonneg (by norm_num) hδ.le) hgapStep hstationary
  refine ⟨-(rectangles n).cut, (rectangles n).start, ?_⟩
  intro t z ht hz
  have hzcut : z ≤ (rectangles n).cut := by
    have := neg_le_neg hz
    simpa using this
  have hrect := (rectangles n).bounds t ht z hzcut
  have habs := abs_sub_one_le_rpow_gap p.hα
    (rectangles n).ell_pos (rectangles n).ell_lt_one.le
    (rectangles n).one_lt_M.le hrect.1 hrect.2
  exact habs.trans_lt hgap

section AxiomAudit

#print axioms ChiPosHalfLineRectangleStep.gap_le
#print axioms uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors

end AxiomAudit

end ShenWork.Paper1
