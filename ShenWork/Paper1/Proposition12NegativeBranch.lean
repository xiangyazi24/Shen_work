import ShenWork.Paper1.WholeLineCauchyLongTimeFloor

open Filter Topology MeasureTheory Real Set Function

noncomputable section

namespace ShenWork.Paper1

/-!
# Proposition 1.2, χ ≤ 0 branch (capstone)

The two hypotheses carried by `Proposition_1_2_negative_branch_of_floor`
discharge from the global exponential floor: for Paper data with a uniform
positive gap, the canonical whole-line solution stays above the rising
barrier `wholeLineCauchyExpFloor c c`, which gives both the uniform lower
envelope at `1` and strict interior positivity.  This is the χ ≤ 0
stabilization branch of Proposition 1.2 in the same canonical-solution form
as the proved `Proposition_1_1_negative_branch`.
-/

theorem Proposition_1_2_negative_branch
    (p : CMParams) (hχ : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀)
    (hpos : UniformlyPositive u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      UniformConvergesToConstant u 1 := by
  rcases hpos with ⟨δ, hδ, hδle⟩
  have hw0 : ∀ x, 0 ≤ (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1).1 x := by
    intro x
    simpa using hu₀.2 x
  have hc0 : 0 < min δ 1 := lt_min hδ one_pos
  have hc1 : min δ 1 ≤ 1 := min_le_right _ _
  have hinit : ∀ x, min δ 1 ≤ (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1).1 x := by
    intro x
    have hx : min δ 1 ≤ u₀ x := (min_le_left δ 1).trans (hδle x)
    simpa using hx
  have hfloor :
      UniformLiminfGe
        (wholeLineCauchyGlobalU p (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1)) 1 :=
    wholeLineCauchyGlobal_uniformLiminfGe_one_of_chi_nonpos
      p hχ (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1) hw0 (min δ 1) hc0 hc1 hinit
  have hstrict : ∀ t x : ℝ, 0 < t →
      0 < wholeLineCauchyGlobalU p (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1) t x := by
    intro t x ht
    have hge := wholeLineCauchyGlobal_ge_expFloor_of_chi_nonpos
      p hχ (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1) hw0 (min δ 1) hc0 hc1 hinit
      ht.le x
    have hbpos : 0 < wholeLineCauchyExpFloor (min δ 1) (min δ 1) t :=
      wholeLineCauchyExpFloor_pos hc0 hc1 hc0.le ht.le
    linarith
  exact Proposition_1_2_negative_branch_of_floor p hχ u₀ hu₀ hfloor hstrict

end ShenWork.Paper1
