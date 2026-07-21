import ShenWork.Paper1.Proposition11UnconditionalAudit
import ShenWork.Paper1.WholeLineChiPosEquilibriumDescent
import ShenWork.Paper1.WholeLineChiPosEquilibriumRootLocation

/-!
# Proposition 1.1: the positive-sensitivity conjunct below `chi = 1`

This file upgrades the supercritical canonical solution from the exact scalar
equilibrium ceiling to the explicit bound in Proposition 1.1.  It then joins
that branch to the critical `chi < 1` branch.  The only part of the positive
conjunct not produced here is existence and eventual uniform boundedness in
the critical window `1 <= chi`.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- In the positive supercritical regime, the canonical solution has the full
second-conjunct payload from Proposition 1.1.  When `chi < 1`, monotonicity of
`UniformLimsupLe` upgrades the exact equilibrium-ceiling estimate to the
paper's explicit bound. -/
theorem paper1_Prop_1_1_second_conjunct_supercritical_full
    (p : CMParams) (hchi : 0 < p.χ)
    (hsuper : p.m + p.γ - 1 < p.α)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u ∧
      (0 < p.χ → p.χ < 1 →
        UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) := by
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hregime : WholeLineCauchyCeilingRegime p :=
    Or.inr ⟨hchi.le, Or.inl hsuper⟩
  have hsolution : IsGlobalNonnegativeCauchySolutionFrom p u₀
      (wholeLineCauchyGlobalU p w) (wholeLineCauchyGlobalV p w) := by
    simpa [w] using
      wholeLineCauchyGlobal_isGlobalNonnegativeCauchySolutionFrom
        p hregime w hw0
  have hnonneg : ∀ t x, 0 ≤ t →
      0 ≤ wholeLineCauchyGlobalU p w t x := by
    intro t x ht
    exact wholeLineCauchyGlobal_nonnegative p hregime w hw0 ht x
  have hrange : ∀ t x, 0 ≤ t →
      wholeLineCauchyGlobalU p w t x ≤
        max (chiPosEquilibriumCeiling p) ‖w‖ := by
    intro t x ht
    exact
      wholeLineCauchyGlobal_le_max_equilibriumCeiling_of_chi_pos_supercritical
        p hchi hsuper w hw0 ht x
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w,
    hsolution, ?_, ?_⟩
  · refine ⟨max (chiPosEquilibriumCeiling p) ‖w‖, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    intro x
    rw [abs_of_nonneg (hnonneg t x ht)]
    exact hrange t x ht
  · intro _hchi hchi_lt
    exact
      (wholeLineCauchyGlobal_uniformLimsupLe_equilibriumCeiling_of_chi_pos_supercritical
          p hchi hsuper w hw0).mono
        (chiPosEquilibriumCeiling_le_supercritical_bound
          p hchi hchi_lt hsuper)

/-- The full second-conjunct payload in the range reached by the current
canonical constructions: `0 < chi < 1` and
`m + gamma - 1 <= alpha`. -/
theorem paper1_Prop_1_1_second_conjunct_of_chi_lt_one
    (p : CMParams) (hchi : 0 < p.χ) (hchi_lt : p.χ < 1)
    (halpha : p.m + p.γ - 1 ≤ p.α)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
      UniformEventuallyBounded u ∧
      (0 < p.χ → p.χ < 1 →
        UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) := by
  rcases halpha.eq_or_lt with hcritical | hsuper
  · exact paper1_Prop_1_1_second_conjunct_critical_subwindow
      p hchi hchi_lt hcritical.symm u₀ hu₀
  · exact paper1_Prop_1_1_second_conjunct_supercritical_full
      p hchi hsuper u₀ hu₀

/-- The positive-sensitivity conjunct of Proposition 1.1, with its exact
`bound_pos`-style parameter disjunction, restricted to `chi < 1`. -/
theorem paper1_Proposition_1_1_positive_conjunct_of_chi_lt_one :
    ∀ p : CMParams,
      ((0 < p.χ ∧ p.α > p.m + p.γ - 1) ∨
        (0 < p.χ ∧
          p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
            ((p.m + p.γ - 1) / (p.γ - 1)) ∧
          p.α = p.m + p.γ - 1)) →
      p.χ < 1 →
      ∀ u₀ : ℝ → ℝ, PaperNonnegativeInitialDatum u₀ →
        ∃ u v : ℝ → ℝ → ℝ,
          IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
          UniformEventuallyBounded u ∧
          (0 < p.χ → p.χ < 1 →
            UniformLimsupLe u ((1 / (1 - p.χ)) ^ (1 / p.α))) := by
  intro p hbranch hchi_lt u₀ hu₀
  rcases hbranch with ⟨hchi, hsuper⟩ |
      ⟨hchi, _hthreshold, hcritical⟩
  · exact paper1_Prop_1_1_second_conjunct_of_chi_lt_one
      p hchi hchi_lt hsuper.le u₀ hu₀
  · exact paper1_Prop_1_1_second_conjunct_of_chi_lt_one
      p hchi hchi_lt hcritical.symm.le u₀ hu₀

/-- If the critical part of the paper's parameter window is restricted to
`chi < 1`, the preceding assembly and the already proved nonpositive branch
give Proposition 1.1. -/
theorem paper1_Proposition_1_1_of_chi_lt_one
    (hcritical_chi_lt_one : ∀ p : CMParams,
      0 < p.χ →
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)) →
      p.α = p.m + p.γ - 1 →
      p.χ < 1) :
    Proposition_1_1 := by
  apply paper1_Proposition_1_1_of_second_conjunct
  intro p hbranch u₀ hu₀
  rcases hbranch with ⟨hchi, hsuper⟩ |
      ⟨hchi, hthreshold, hcritical⟩
  · exact paper1_Prop_1_1_second_conjunct_supercritical_full
      p hchi hsuper u₀ hu₀
  · exact paper1_Proposition_1_1_positive_conjunct_of_chi_lt_one
      p (Or.inr ⟨hchi, hthreshold, hcritical⟩)
        (hcritical_chi_lt_one p hchi hthreshold hcritical) u₀ hu₀

/-- Exact residual form of Proposition 1.1.  The only carried producer is
existence plus eventual uniform boundedness in the critical `1 <= chi`
window; its limsup obligation is vacuous because it assumes `chi < 1`. -/
theorem paper1_Proposition_1_1_of_large_chi_critical_residual
    (hcritical_large : ∀ p : CMParams,
      0 < p.χ →
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)) →
      1 ≤ p.χ →
      p.α = p.m + p.γ - 1 →
      ∀ u₀ : ℝ → ℝ, PaperNonnegativeInitialDatum u₀ →
        ∃ u v : ℝ → ℝ → ℝ,
          IsGlobalNonnegativeCauchySolutionFrom p u₀ u v ∧
          UniformEventuallyBounded u) :
    Proposition_1_1 := by
  apply paper1_Proposition_1_1_of_second_conjunct
  intro p hbranch u₀ hu₀
  rcases hbranch with ⟨hchi, hsuper⟩ |
      ⟨hchi, hthreshold, hcritical⟩
  · exact paper1_Prop_1_1_second_conjunct_supercritical_full
      p hchi hsuper u₀ hu₀
  · by_cases hchi_lt : p.χ < 1
    · exact paper1_Proposition_1_1_positive_conjunct_of_chi_lt_one
        p (Or.inr ⟨hchi, hthreshold, hcritical⟩) hchi_lt u₀ hu₀
    · have hchi_large : 1 ≤ p.χ := le_of_not_gt hchi_lt
      rcases hcritical_large p hchi hthreshold hchi_large hcritical u₀ hu₀ with
        ⟨u, v, hsolution, hbounded⟩
      refine ⟨u, v, hsolution, hbounded, ?_⟩
      intro _ hchi_lt'
      exact (hchi_lt hchi_lt').elim

section AxiomAudit

#print axioms paper1_Prop_1_1_second_conjunct_supercritical_full
#print axioms paper1_Prop_1_1_second_conjunct_of_chi_lt_one
#print axioms paper1_Proposition_1_1_positive_conjunct_of_chi_lt_one
#print axioms paper1_Proposition_1_1_of_chi_lt_one
#print axioms paper1_Proposition_1_1_of_large_chi_critical_residual

end AxiomAudit

end ShenWork.Paper1
