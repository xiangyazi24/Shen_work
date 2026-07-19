import ShenWork.Paper1.Proposition12Assembly
import ShenWork.Paper1.WholeLineChiPosRectangleSqueeze
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural

open Filter Topology MeasureTheory Real Set Function

noncomputable section

namespace ShenWork.Paper1

/-!
# Proposition 1.2, positive-sensitivity critical branch

This is the critical-exponent part of `Proposition12PositiveBranch`.  The
supercritical case `m + γ - 1 < α` is deliberately not included here.  The
scalar ceiling regime is kept explicit, matching the hypotheses of the
canonical whole-line construction.
-/

/-- The `α = m + γ - 1` restriction of `Proposition12PositiveBranch`, with
the canonical scalar ceiling regime stated explicitly. -/
def Proposition12PositiveBranchCritical : Prop :=
  ∀ p : CMParams, 0 < p.χ → p.χ < (1 / 2 : ℝ) →
    p.α = p.m + p.γ - 1 → WholeLineCauchyCeilingRegime p →
    ∀ u₀ : ℝ → ℝ, PaperNonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1

/-- The canonical whole-line solution closes the critical positive branch of
Proposition 1.2 under the explicit ceiling regime. -/
theorem Proposition_1_2_positive_branch_critical :
    Proposition12PositiveBranchCritical := by
  intro p hχ hχhalf hcritical hregime u₀ hu₀ hpositive
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hwpositive : UniformlyPositive w.1 := by
    rcases hpositive with ⟨δ, hδ, hδle⟩
    refine ⟨δ, hδ, ?_⟩
    intro x
    simpa [w] using hδle x
  have hconverges :
      UniformConvergesToConstant (wholeLineCauchyGlobalU p w) 1 :=
    wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_pos_half
      p hχ hχhalf hcritical hregime w hw0 hwpositive
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w, ?_, hconverges⟩
  simpa [w] using
    (wholeLineCauchyGlobal_isGlobalCauchySolutionFrom_of_posAtBot
      p hregime w hw0 hwpositive.strictlyPositiveAtLeft)

section AxiomAudit

#print axioms Proposition12PositiveBranchCritical
#print axioms Proposition_1_2_positive_branch_critical

end AxiomAudit

end ShenWork.Paper1
