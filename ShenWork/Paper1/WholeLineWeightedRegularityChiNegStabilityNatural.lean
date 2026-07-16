import ShenWork.Paper1.WholeLineWeightedRegularityChiNegLeftEquilibriumNatural
import ShenWork.Paper1.WholeLineWeightedRegularityStabilityNatural

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Complete negative-sensitivity stability

The weighted-energy and dynamic left-equilibrium producers are assembled here
into the faithful canonical global solution, weighted convergence, and uniform
moving-frame convergence for strictly negative sensitivity.
-/

/-- The canonical paper solution has both forms of stability when `chi < 0`.
No whole-line positive floor is assumed: the datum is only strictly positive
at the left end. -/
theorem
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_neg_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ < 0)
    {c eta kappaOne : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrictWave : HasStrictWaveUpperTailBound p c U)
    (hkappaOne : kappa c < kappaOne)
    (hkappaOne_one : kappaOne < 1)
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀)
    (hleft₀ : StrictlyPositiveAtLeft u₀)
    (hinitial : WeightedL2InitialCloseness eta u₀ U) :
    let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
    IsGlobalCauchySolutionFrom p u₀
        (wholeLineCauchyGlobalU p w) (wholeLineCauchyGlobalV p w) ∧
      CoMovingWeightedL2Convergence eta c
          (wholeLineCauchyGlobalU p w) U ∧
        UniformMovingFrameConvergence c
          (wholeLineCauchyGlobalU p w) U := by
  dsimp only
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw₀ : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hleftW : StrictlyPositiveAtLeft w.1 := by
    simpa [w] using hleft₀
  have hinitialW : WeightedL2InitialCloseness eta w.1 U := by
    simpa [w] using hinitial
  have hleftEq : UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p w) :=
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_neg_natural
      p hregime hchi hc hTW hreg hstrictWave hkappaOne hkappaOne_one htail
        hroot hetaCap w hw₀ hleftW hinitialW
  simpa [w] using
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_nonpos_of_leftEquilibrium
      p hregime hchi.le hc hTW hreg hstrictWave hroot hetaCap
        u₀ hu₀ hleft₀ hinitial hleftEq

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_neg_natural

end AxiomAudit

end ShenWork.Paper1
