import ShenWork.Paper1.WholeLineChiPosHalfLineSeed
import ShenWork.Paper1.WholeLineChiPosHalfLineSuccessor

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-sensitivity left-equilibrium convergence

The persistent plateau produces the first strict half-line rectangle.  The
buffered successor theorem advances every such rectangle, and the abstract
rectangle endgame contracts the scalar gap because `2 * chi < 1`.
-/

/-- Under the positive critical regime, the canonical orbit converges
uniformly to the equilibrium `1` on sufficiently far-left co-moving
half-lines. -/
theorem
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural
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
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) := by
  obtain ⟨seed⟩ := exists_initial_chiPosHalfLineRectangle
    p hregime hchi hchi_half hcritical hc hTW hreg hstrict
      hkappaOne hkappaOne_one htail hroot hetaCap u₀ hu₀ hleft hinitial
  have hchi_one : p.χ < 1 := by linarith
  exact uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors
    p hchi.le hchi_half (by linarith [hcritical]) seed
      (fun delta hdelta old =>
        exists_next_chiPosHalfLineRectangle
          p hregime hchi hchi_one hcritical hc hTW hreg
            hstrict.hasWaveUpperTailBound hroot hetaCap u₀ hu₀ hleft
            hinitial hdelta old)

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_natural

end AxiomAudit

end ShenWork.Paper1
