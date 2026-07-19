import ShenWork.Paper1.WholeLineChiPosStabilityAssembly
import ShenWork.Paper1.WholeLineWeightedRegularityChiPosLeftEquilibriumNatural

/-!
# Paper 1 Theorem 1.2 for positive sensitivity — unconditional Step 4

Combines the χ>0 Step-4 assembly with the now-proved χ>0 left-equilibrium
convergence.  Mirror of
`wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_neg_natural`.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-- Positive-sensitivity stability: the canonical global solution converges to
the traveling wave both in the weighted `L²` norm and uniformly in the moving
frame.  No carried analytic hypothesis. -/
theorem
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    {c eta kappaOne : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hkappaOne : kappa c < kappaOne)
    (hkappaOne_one : kappaOne < 1)
    (htail : HasWaveRightTailAsymptotic c kappaOne U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    IsGlobalCauchySolutionFrom p u₀.1
        (wholeLineCauchyGlobalU p u₀) (wholeLineCauchyGlobalV p u₀) ∧
      CoMovingWeightedL2Convergence eta c (wholeLineCauchyGlobalU p u₀) U ∧
        UniformMovingFrameConvergence c (wholeLineCauchyGlobalU p u₀) U := by
  have hchi_one : p.χ < 1 := by linarith
  have hleftEq : UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) :=
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural
      p hregime hchi hchi_half hcritical hc hTW hreg hstrict
        hkappaOne hkappaOne_one htail hroot hetaCap u₀ hu₀ hleft hinitial
  exact
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_of_leftEquilibrium
      p hregime hchi hchi_one hc hTW hreg hstrict.hasWaveUpperTailBound
        hroot hetaCap u₀ hu₀ hleft hinitial hleftEq

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_natural

end AxiomAudit

end ShenWork.Paper1
