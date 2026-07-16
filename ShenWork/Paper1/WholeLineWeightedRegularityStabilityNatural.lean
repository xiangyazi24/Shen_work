import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroConvergenceNatural
import ShenWork.Paper1.WholeLineWeightedRegularityWeightedConvergenceNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural
import ShenWork.Paper1.WholeLineCauchyLeftTailBridge
import ShenWork.Paper1.Theorem12Step4EnergyProducer

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical nonpositive-sensitivity stability assembly

The exact-weight energy argument is complete for both `chi < 0` and
`chi = 0`.  This file packages those two branches with the canonical strict
global solution.  Its second theorem records the precise remaining dynamic
input for uniform convergence: convergence to the left equilibrium in the
co-moving frame.  That input is not inferred from weighted `L2` decay.
-/

/-- For every nonpositive sensitivity, the canonical solution is a genuine
strict global Cauchy solution and has the corrected co-moving weighted-`L2`
convergence. -/
theorem wholeLineCauchyGlobal_solution_and_weightedConvergence_chi_nonpos_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ ≤ 0)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrictWave : HasStrictWaveUpperTailBound p c U)
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
  have hceiling : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi
  have hsol : IsGlobalCauchySolutionFrom p u₀
      (wholeLineCauchyGlobalU p w) (wholeLineCauchyGlobalV p w) := by
    simpa [w] using
      (wholeLineCauchyGlobal_isGlobalCauchySolutionFrom_of_posAtBot
        p hceiling w hw₀ hleftW)
  have hweighted : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p w) U := by
    rcases lt_or_eq_of_le hchi with hchiNeg | hchiZero
    · exact
        wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_neg_natural
          p hregime hchiNeg hc hTW
            hstrictWave.hasWaveUpperTailBound hreg hroot hetaCap
            w hw₀ hinitialW
    · exact
        wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_zero_natural
          p hregime hchiZero hc hTW
            hstrictWave.hasWaveUpperTailBound hreg hroot hetaCap
            w hw₀ hinitialW
  exact ⟨hsol, hweighted⟩

/-- Once the genuine left-equilibrium dynamics is supplied, the canonical
nonpositive-sensitivity branch also has uniform moving-frame convergence.
All other Step 4 inputs are constructed internally. -/
theorem
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_nonpos_of_leftEquilibrium
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ ≤ 0)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrictWave : HasStrictWaveUpperTailBound p c U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀)
    (hleft₀ : StrictlyPositiveAtLeft u₀)
    (hinitial : WeightedL2InitialCloseness eta u₀ U)
    (hleftEq : UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p
        (wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1))) :
    let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
    IsGlobalCauchySolutionFrom p u₀
        (wholeLineCauchyGlobalU p w) (wholeLineCauchyGlobalV p w) ∧
      CoMovingWeightedL2Convergence eta c
          (wholeLineCauchyGlobalU p w) U ∧
        UniformMovingFrameConvergence c
          (wholeLineCauchyGlobalU p w) U := by
  dsimp only
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hbase :=
    wholeLineCauchyGlobal_solution_and_weightedConvergence_chi_nonpos_natural
      p hregime hchi hc hTW hreg hstrictWave hroot hetaCap
        u₀ hu₀ hleft₀ hinitial
  have hw₀ : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hceiling : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi
  have hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c (wholeLineCauchyGlobalU p w)) U :=
    wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
      p hceiling w hw₀ c hTW hreg
  have henergyInt : EventuallyIntegrableMovingFrameEnergy eta 0
      (coMovingPath c (wholeLineCauchyGlobalU p w)) U := by
    unfold EventuallyIntegrableMovingFrameEnergy
    simpa [movingFrameError, coMovingPath] using hbase.2.1
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc).trans
      hroot
  have hleft : UniformMovingFrameLeftTailConvergence 0
      (coMovingPath c (wholeLineCauchyGlobalU p w)) U := by
    apply uniformMovingFrameLeftTailConvergence_of_leftEquilibrium
    · simpa [w] using hleftEq
    · exact hTW.lim_neg_inf.1
  have huniform : UniformMovingFrameConvergence c
      (wholeLineCauchyGlobalU p w) U :=
    uniformMovingFrameConvergence_of_coMovingWeightedL2_of_step4
      heta henergyInt hbase.2 hmod hleft
  exact ⟨hbase.1, hbase.2, huniform⟩

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_solution_and_weightedConvergence_chi_nonpos_natural
#print axioms
  wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_nonpos_of_leftEquilibrium

end AxiomAudit

end ShenWork.Paper1
