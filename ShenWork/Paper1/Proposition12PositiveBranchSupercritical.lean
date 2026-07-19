import ShenWork.Paper1.Proposition12PositiveBranchCritical
import ShenWork.Paper1.WholeLineChiPosSupercriticalRectangle

open Filter Topology MeasureTheory Real Set Function

noncomputable section

namespace ShenWork.Paper1

/-!
# Proposition 1.2, positive-sensitivity supercritical branch

The strict supercritical squeeze closes the remaining positive-sensitivity
case.  Splitting the paper hypothesis `m + γ - 1 ≤ α` into strict and
equality cases then gives the full positive branch.
-/

/-- The `m + γ - 1 < α` restriction of `Proposition12PositiveBranch`, with
the canonical scalar ceiling regime stated explicitly. -/
def Proposition12PositiveBranchSupercritical : Prop :=
  ∀ p : CMParams, 0 < p.χ → p.χ < (1 / 2 : ℝ) →
    p.m + p.γ - 1 < p.α → WholeLineCauchyCeilingRegime p →
    ∀ u₀ : ℝ → ℝ, PaperNonnegativeInitialDatum u₀ → UniformlyPositive u₀ →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        UniformConvergesToConstant u 1

/-- The canonical whole-line solution closes the strictly supercritical
positive branch under the explicit ceiling regime. -/
theorem Proposition_1_2_positive_branch_supercritical :
    Proposition12PositiveBranchSupercritical := by
  intro p hχ hχhalf hsuper hregime u₀ hu₀ hpositive
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
    wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_pos_half_supercritical
      p hχ hχhalf hsuper hregime w hw0 hwpositive
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w, ?_, hconverges⟩
  simpa [w] using
    (wholeLineCauchyGlobal_isGlobalCauchySolutionFrom_of_posAtBot
      p hregime w hw0 hwpositive.strictlyPositiveAtLeft)

/-- Proposition 1.2's full positive branch, obtained by splitting its exponent
inequality into the strict supercritical and critical cases. -/
theorem Proposition_1_2_positive_branch :
    Proposition12PositiveBranch := by
  intro p hχ hχhalf hle u₀ hu₀ hpositive
  rcases lt_or_eq_of_le hle with hsuper | heq
  · let hregime : WholeLineCauchyCeilingRegime p :=
      Or.inr ⟨hχ.le, Or.inl hsuper⟩
    exact Proposition_1_2_positive_branch_supercritical
      p hχ hχhalf hsuper hregime u₀ hu₀ hpositive
  · have hχ_lt : p.χ < 1 := by linarith
    let hregime : WholeLineCauchyCeilingRegime p :=
      Or.inr ⟨hχ.le, Or.inr ⟨hχ_lt, heq.symm⟩⟩
    exact Proposition_1_2_positive_branch_critical
      p hχ hχhalf heq.symm hregime u₀ hu₀ hpositive

section AxiomAudit

#print axioms Proposition12PositiveBranchSupercritical
#print axioms Proposition_1_2_positive_branch_supercritical
#print axioms Proposition_1_2_positive_branch

end AxiomAudit

end ShenWork.Paper1
