import ShenWork.Paper1.WholeLineChiPosHalfLineSeedMGTOne
import ShenWork.Paper1.WholeLineChiPosHalfLineSharpRectangle
import ShenWork.Paper1.WholeLineChiPosStabilityAssembly

/-!
# Positive left equilibrium beyond `chi < 1 / 2` when `m > 1`

The direct seed for degenerate mobility and the sharp half-line recurrence
combine under the exact condition

`chi * gamma < alpha * (1 - chi)`,

or equivalently `chi < alpha / (alpha + gamma)`.  At the critical exponent
`alpha = m + gamma - 1`, this threshold is strictly larger than `1 / 2`
whenever `m > 1`.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-- Critical positive-sensitivity far-left equilibrium convergence for the
strictly enlarged `m > 1` window. -/
theorem
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_m_gt_one
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_one : p.χ < 1) (hm : 1 < p.m)
    (hcritical : p.α = p.m + p.γ - 1)
    (hcontract : p.χ * p.γ < p.α * (1 - p.χ))
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) := by
  obtain ⟨seed⟩ := exists_initial_chiPosHalfLineRectangle_m_gt_one
    p hregime hchi hchi_one hm hcritical hc hTW hreg hbound hroot
      hetaCap u₀ hu₀ hleft hinitial
  exact
    uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_m_gt_one
      p hm hchi.le hchi_one hcritical hcontract seed
        (fun delta hdelta old =>
          exists_next_chiPosHalfLineRectangle
            p hregime hchi hchi_one hcritical hc hTW hreg hbound hroot
              hetaCap u₀ hu₀ hleft hinitial hdelta old)

/-- The new far-left result feeds the already χ-general Step-4 bridge, giving
weighted and uniform moving-frame stability throughout the same enlarged
window. -/
theorem
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_m_gt_one
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_one : p.χ < 1) (hm : 1 < p.m)
    (hcritical : p.α = p.m + p.γ - 1)
    (hcontract : p.χ * p.γ < p.α * (1 - p.χ))
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hleft : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    IsGlobalCauchySolutionFrom p u₀.1
        (wholeLineCauchyGlobalU p u₀) (wholeLineCauchyGlobalV p u₀) ∧
      CoMovingWeightedL2Convergence eta c
          (wholeLineCauchyGlobalU p u₀) U ∧
        UniformMovingFrameConvergence c
          (wholeLineCauchyGlobalU p u₀) U := by
  have hleftEq : UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀) :=
    wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_m_gt_one
      p hregime hchi hchi_one hm hcritical hcontract hc hTW hreg hbound
        hroot hetaCap u₀ hu₀ hleft hinitial
  exact
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_of_leftEquilibrium
      p hregime hchi hchi_one hc hTW hreg hbound hroot hetaCap u₀ hu₀
        hleft hinitial hleftEq

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_uniformCoMovingLeftEquilibriumConvergence_chi_pos_m_gt_one
#print axioms
  wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_m_gt_one

end AxiomAudit

end ShenWork.Paper1
