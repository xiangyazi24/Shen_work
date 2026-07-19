import ShenWork.Paper1.Proposition11PositiveErrata
import ShenWork.Paper1.WholeLineCauchyChiPosRangeBound
import ShenWork.Paper1.WholeLineCauchyLongTimeBound

/-!
# Proposition 1.1(2), the critical window covered by the `MChi` ceiling

Mirror of `Proposition_1_1_negative_branch` for positive sensitivity at the
critical exponent `α = m + γ - 1`, on the window `χ < chiStar p` where the
relaxing `MChi` ceiling is available.

This is a FAITHFUL PARTIAL of the paper's Proposition 1.1(2): the source
permits the wider window `paper1PositiveCriticalThreshold` (see
`Proposition11PositiveErrata.lean`), whose complement
`chiStar p ≤ χ` is proved there to be nonempty and is obtained in the paper by
a local `L^p` iteration rather than a constant-ceiling comparison.  The
supercritical branch `m + γ - 1 < α` is covered separately and needs no
smallness on `χ` at all.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- The critical positive-sensitivity window of Proposition 1.1(2): global
existence, a time-uniform range bound, eventual uniform boundedness, and the
paper's `MChi` limsup ceiling. -/
theorem Proposition_1_1_positive_critical_branch
    (p : CMParams) (hχ : 0 < p.χ) (hχStar : p.χ < chiStar p)
    (hcritical : p.α = p.m + p.γ - 1)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      (∀ t x, 0 ≤ t → u t x ≤ max (MChi p) ‖wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1‖) ∧
      UniformEventuallyBounded u ∧
      UniformLimsupLe u (MChi p) := by
  have hχ_lt : p.χ < 1 := hχStar.trans_le (chiStar_le_one p)
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hregime : WholeLineCauchyCeilingRegime p :=
    Or.inr ⟨hχ.le, Or.inr ⟨hχStar, hcritical⟩⟩
  have hrange : ∀ t x, 0 ≤ t →
      wholeLineCauchyGlobalU p w t x ≤ max (MChi p) ‖w‖ := by
    intro t x ht
    exact wholeLineCauchyGlobal_le_max_of_chi_pos
      p hχ hχ_lt hcritical hregime w hw0 ht x
  have hnonneg : ∀ t x, 0 ≤ t → 0 ≤ wholeLineCauchyGlobalU p w t x := by
    intro t x ht
    exact wholeLineCauchyGlobal_nonnegative p hregime w hw0 ht x
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w, ?_, hrange,
    ⟨max (MChi p) ‖w‖, ?_⟩,
    wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos
      p hχ hχ_lt hcritical hregime w hw0⟩
  · simpa [w] using
      wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom
        p hregime w hw0
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht x
    rw [abs_of_nonneg (hnonneg t x ht)]
    exact hrange t x ht

/-- The paper's own threshold is strictly weaker than the window covered
above, so this branch is explicitly a faithful partial: the residual window is
inhabited. -/
theorem Proposition_1_1_positive_critical_residual_window_nonempty :
    ∃ p : CMParams, 0 < p.χ ∧ p.α = p.m + p.γ - 1 ∧
      paper1PositiveCriticalThreshold p ∧ chiStar p ≤ p.χ := by
  refine ⟨⟨1, 2, 2, 3/2, le_refl 1, by norm_num, by norm_num⟩, by norm_num,
    by norm_num, ?_, ?_⟩
  · unfold paper1PositiveCriticalThreshold
    norm_num
  · have h := chiStar_le_one ⟨1, 2, 2, 3/2, le_refl 1, by norm_num, by norm_num⟩
    show chiStar _ ≤ (3/2 : ℝ)
    linarith

section AxiomAudit

#print axioms Proposition_1_1_positive_critical_branch
#print axioms Proposition_1_1_positive_critical_residual_window_nonempty

end AxiomAudit

end ShenWork.Paper1
