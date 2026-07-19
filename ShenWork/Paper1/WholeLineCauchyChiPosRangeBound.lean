import ShenWork.Paper1.WholeLineCauchyChiPosLongTimeBound

open Filter Topology Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Global range bounds in the positive-sensitivity branch

The relaxing positive-sensitivity ceiling never exceeds its initial height.
Taking that height to be the maximum of `MChi p` and the norm of the initial
datum therefore gives a time-independent global range bound.
-/

/-- The canonical global solution is bounded by the larger of `MChi p` and
the norm of its initial datum when `0 < p.χ < 1`. -/
theorem wholeLineCauchyGlobal_le_max_of_chi_pos
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (halpha : p.α = p.m + p.γ - 1)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤ max (MChi p) ‖u₀‖ := by
  let C : ℝ := max (MChi p) ‖u₀‖
  have hC : MChi p ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hinit : ∀ y, u₀.1 y ≤ C := by
    intro y
    exact (WholeLineBUC.apply_le_norm u₀ y).trans (le_max_right _ _)
  exact
    (wholeLineCauchyGlobal_le_chiPosCeiling_of_chi_pos
      p hχ_pos hχ_lt halpha hregime u₀ hu₀ C hC hinit ht x).trans
      (wholeLineCauchyChiPosCeiling_le hC ht)

/-- A convenient common range bound which also dominates `1`. -/
theorem wholeLineCauchyGlobal_le_max_max_one_norm_MChi_of_chi_pos
    (p : CMParams) (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1)
    (halpha : p.α = p.m + p.γ - 1)
    (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    wholeLineCauchyGlobalU p u₀ t x ≤ max (max 1 ‖u₀‖) (MChi p) := by
  refine (wholeLineCauchyGlobal_le_max_of_chi_pos
    p hχ_pos hχ_lt halpha hregime u₀ hu₀ ht x).trans ?_
  apply max_le
  · exact le_max_right _ _
  · exact (le_max_right (1 : ℝ) ‖u₀‖).trans (le_max_left _ _)

section WholeLineCauchyChiPosRangeBoundAxiomAudit

#print axioms wholeLineCauchyGlobal_le_max_of_chi_pos
#print axioms wholeLineCauchyGlobal_le_max_max_one_norm_MChi_of_chi_pos

end WholeLineCauchyChiPosRangeBoundAxiomAudit

end ShenWork.Paper1
