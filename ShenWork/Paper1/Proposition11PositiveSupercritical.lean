import ShenWork.Paper1.Proposition11PositiveCritical
import ShenWork.Paper1.WholeLineChiPosSupercriticalLongTimeBound

/-!
# Proposition 1.1(2), the positive-sensitivity supercritical branch

This file assembles the canonical whole-line solution in the supercritical
regime `m + γ - 1 < α`, where the explicit parameter ceiling gives a
time-uniform range bound and the corresponding uniform limsup estimate.  It
also combines this branch with the positive critical window.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- The supercritical positive-sensitivity branch of Proposition 1.1(2):
global existence, a time-uniform range bound, eventual uniform boundedness,
and the explicit parameter-ceiling limsup bound. -/
theorem Proposition_1_1_positive_supercritical_branch
    (p : CMParams) (hχ : 0 < p.χ) (hsuper : p.m + p.γ - 1 < p.α)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      (∀ t x, 0 ≤ t → u t x ≤
        max (wholeLineCauchyParameterCeiling p) ‖wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1‖) ∧
      UniformEventuallyBounded u ∧
      UniformLimsupLe u (wholeLineCauchyParameterCeiling p) := by
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hregime : WholeLineCauchyCeilingRegime p :=
    Or.inr ⟨hχ.le, Or.inl hsuper⟩
  have hrange : ∀ t x, 0 ≤ t →
      wholeLineCauchyGlobalU p w t x ≤
        max (wholeLineCauchyParameterCeiling p) ‖w‖ := by
    intro t x ht
    exact wholeLineCauchyGlobal_le_max_of_chi_pos_supercritical
      p hχ hsuper w hw0 ht x
  have hnonneg : ∀ t x, 0 ≤ t → 0 ≤ wholeLineCauchyGlobalU p w t x := by
    intro t x ht
    exact wholeLineCauchyGlobal_nonnegative p hregime w hw0 ht x
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w, ?_, hrange,
    ⟨max (wholeLineCauchyParameterCeiling p) ‖w‖, ?_⟩,
    wholeLineCauchyGlobal_uniformLimsupLe_parameterCeiling_of_chi_pos_supercritical
      p hχ hsuper w hw0⟩
  · simpa [w] using
      wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom
        p hregime w hw0
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht x
    rw [abs_of_nonneg (hnonneg t x ht)]
    exact hrange t x ht

/-- The two positive-sensitivity regimes currently covered by the canonical
ceiling construction both give a global nonnegative solution that is
eventually uniformly bounded. -/
theorem Proposition_1_1_positive_branches_of_regime
    (p : CMParams) (hχ : 0 < p.χ)
    (hbranch : (p.m + p.γ - 1 < p.α) ∨
      (p.χ < chiStar p ∧ p.α = p.m + p.γ - 1))
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧ UniformEventuallyBounded u := by
  rcases hbranch with hsuper | ⟨hχStar, hcritical⟩
  · rcases Proposition_1_1_positive_supercritical_branch
      p hχ hsuper u₀ hu₀ with ⟨u, v, hsolution, _, hbounded, _⟩
    exact ⟨u, v, hsolution, hbounded⟩
  · rcases Proposition_1_1_positive_critical_branch
      p hχ hχStar hcritical u₀ hu₀ with ⟨u, v, hsolution, _, hbounded, _⟩
    exact ⟨u, v, hsolution, hbounded⟩

section AxiomAudit

#print axioms Proposition_1_1_positive_supercritical_branch
#print axioms Proposition_1_1_positive_branches_of_regime

end AxiomAudit

end ShenWork.Paper1
