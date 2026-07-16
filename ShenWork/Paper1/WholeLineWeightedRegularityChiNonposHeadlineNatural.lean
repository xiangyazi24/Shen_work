import ShenWork.Paper1.WholeLineWeightedRegularityChiNegStabilityNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroStabilityNatural

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Paper 1 Theorem 1.2 for nonpositive sensitivity

This is the paper-datum branch of the corrected moving-coordinate statement.
Unlike the historical `Theorem_1_2_amended` predicate, the datum is explicitly
required to lie in the paper's bounded uniformly continuous phase space.
-/

/-- The corrected stability conclusion for every nonpositive sensitivity and
every paper-admissible initial datum.  The speed family and perturbed-root
budget are constructed explicitly; the solution is the canonical strict
global Cauchy solution. -/
theorem paper1_Theorem_1_2_chi_nonpos_paperDatum
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ ≤ 0) :
    ∃ cStarStar : ℝ → ℝ,
      ∃ budget : Paper531StabilityBudget p cStarStar,
        StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
        ∀ c : ℝ, cStarStar p.χ < c →
        ∀ U V : ℝ → ℝ,
          IsTravelingWave p c U V →
          TravelingWaveRegularity p c U V →
          HasStrictWaveUpperTailBound p c U →
          (∃ kappaOne, kappa c < kappaOne ∧ kappaOne < 1 ∧
            HasWaveRightTailAsymptotic c kappaOne U) →
          ∀ eta : ℝ, paper531RootMinus c budget.A budget.B < eta →
            eta < stabilityWeightCap p →
            ∀ u₀ : ℝ → ℝ,
              PaperNonnegativeInitialDatum u₀ →
              StrictlyPositiveAtLeft u₀ →
              WeightedL2InitialCloseness eta u₀ U →
              ∃ u v : ℝ → ℝ → ℝ,
                IsGlobalCauchySolutionFrom p u₀ u v ∧
                CoMovingWeightedL2Convergence eta c u U ∧
                UniformMovingFrameConvergence c u U := by
  refine ⟨paper5CorrectedCStarStar p,
    paper531ConcreteStabilityBudget p hregime,
    paper5CorrectedCStarStar_asymptotic p,
    paper5CorrectedCStarStar_baseline_le p, ?_⟩
  intro c hc U V hTW hreg hstrict htail eta hroot hetaCap
    u₀ hu₀ hleft hinitial
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w, ?_⟩
  rcases lt_or_eq_of_le hchi with hchiNeg | hchiZero
  · obtain ⟨kappaOne, hkappaOne, hkappaOne_one, hrightTail⟩ := htail
    simpa [w] using
      wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_neg_natural
        p hregime hchiNeg hc hTW hreg hstrict
          hkappaOne hkappaOne_one hrightTail hroot hetaCap
          u₀ hu₀ hleft hinitial
  · simpa [w] using
      wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_zero_natural
        p hregime hchiZero hc hTW hreg hstrict hroot hetaCap
          u₀ hu₀ hleft hinitial

/-- Strictly negative sensitivity is the corresponding specialization of the
nonpositive branch. -/
theorem paper1_Theorem_1_2_chi_neg_paperDatum
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ < 0) :
    ∃ cStarStar : ℝ → ℝ,
      ∃ budget : Paper531StabilityBudget p cStarStar,
        StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
        ∀ c : ℝ, cStarStar p.χ < c →
        ∀ U V : ℝ → ℝ,
          IsTravelingWave p c U V →
          TravelingWaveRegularity p c U V →
          HasStrictWaveUpperTailBound p c U →
          (∃ kappaOne, kappa c < kappaOne ∧ kappaOne < 1 ∧
            HasWaveRightTailAsymptotic c kappaOne U) →
          ∀ eta : ℝ, paper531RootMinus c budget.A budget.B < eta →
            eta < stabilityWeightCap p →
            ∀ u₀ : ℝ → ℝ,
              PaperNonnegativeInitialDatum u₀ →
              StrictlyPositiveAtLeft u₀ →
              WeightedL2InitialCloseness eta u₀ U →
              ∃ u v : ℝ → ℝ → ℝ,
                IsGlobalCauchySolutionFrom p u₀ u v ∧
                CoMovingWeightedL2Convergence eta c u U ∧
                UniformMovingFrameConvergence c u U :=
  paper1_Theorem_1_2_chi_nonpos_paperDatum p hregime hchi.le

section AxiomAudit

#print axioms paper1_Theorem_1_2_chi_nonpos_paperDatum
#print axioms paper1_Theorem_1_2_chi_neg_paperDatum

end AxiomAudit

end ShenWork.Paper1
