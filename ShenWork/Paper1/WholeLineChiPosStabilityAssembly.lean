import ShenWork.Paper1.WholeLineWeightedRegularityWeightedConvergenceChiPosNatural
import ShenWork.Paper1.WholeLineWeightedRegularityStabilityNatural
import ShenWork.Paper1.WholeLineCauchyLeftTailBridge

/-!
# Paper 1 Theorem 1.2, positive sensitivity: everything except the left tail

Mirror of
`wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_nonpos_of_leftEquilibrium`
for `0 < χ`.  The left-equilibrium input is carried as an explicit hypothesis,
exactly as the χ≤0 wrapper does: this isolates the ONE remaining analytic
obligation of the positive branch and shows every other link of the Step-4 chain
is already available for `χ > 0`.

Chain used here (all committed):
* global solution — `wholeLineCauchyGlobal_isGlobalCauchySolutionFrom_of_posAtBot`
  (ceiling regime, now available for the whole window `χ < 1`);
* weighted `L²` convergence —
  `wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural`;
* eventual integrability of the moving-frame energy —
  `wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_pos_of_initialCloseness`;
* eventually-uniform spatial modulus — χ-general;
* left tail from left equilibrium — χ-general
  (`uniformMovingFrameLeftTailConvergence_of_leftEquilibrium`);
* Step-4 combination — χ-general
  (`uniformMovingFrameConvergence_of_coMovingWeightedL2_of_step4`).
-/

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-- Positive-sensitivity Step 4: once the left-equilibrium dynamics is supplied,
the canonical solution has weighted `L²` convergence AND uniform moving-frame
convergence to the wave. -/
theorem
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_of_leftEquilibrium
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_lt : p.χ < 1)
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
    (hleft₀ : StrictlyPositiveAtLeft u₀.1)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U)
    (hleftEq : UniformCoMovingLeftEquilibriumConvergence c
      (wholeLineCauchyGlobalU p u₀)) :
    IsGlobalCauchySolutionFrom p u₀.1
        (wholeLineCauchyGlobalU p u₀) (wholeLineCauchyGlobalV p u₀) ∧
      CoMovingWeightedL2Convergence eta c (wholeLineCauchyGlobalU p u₀) U ∧
        UniformMovingFrameConvergence c (wholeLineCauchyGlobalU p u₀) U := by
  have hceiling : WholeLineCauchyCeilingRegime p := by
    rcases hregime with hneg | hpos
    · exact Or.inl hneg.1.le
    · exact Or.inr ⟨hpos.1, Or.inr ⟨hchi_lt, hpos.2.2⟩⟩
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc).trans hroot
  have heta_one : eta < 1 := by
    have hcap_one : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    exact hetaCap.trans_le hcap_one
  have hs : Paper5WaveStaticNaturalData p c U V :=
    paper5WaveStaticNaturalData_of_wave p (ne_of_gt hchi) hc hTW hbound hreg
  -- global solution
  have hsol : IsGlobalCauchySolutionFrom p u₀.1
      (wholeLineCauchyGlobalU p u₀) (wholeLineCauchyGlobalV p u₀) :=
    wholeLineCauchyGlobal_isGlobalCauchySolutionFrom_of_posAtBot
      p hceiling u₀ hu₀ hleft₀
  -- weighted L² convergence
  have hweighted : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U :=
    wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural
      p hregime hchi hc hTW hbound hreg hroot hetaCap u₀ hu₀ hinitial
  -- eventual integrability of the moving-frame energy
  have henergyInt : EventuallyIntegrableMovingFrameEnergy eta 0
      (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U := by
    unfold EventuallyIntegrableMovingFrameEnergy
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simpa [movingFrameError, coMovingPath] using
      (wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_pos_of_initialCloseness
        (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hregime hchi u₀ ht heta heta_one hTW hbound hreg hs.hD hs.hFD
          hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
          hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
          hs.hgrad_int hinitial)
  -- spatial modulus (χ-general)
  have hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U :=
    wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
      p hceiling u₀ hu₀ c hTW hreg
  -- left tail from the carried left-equilibrium input (χ-general)
  have hlefttail : UniformMovingFrameLeftTailConvergence 0
      (coMovingPath c (wholeLineCauchyGlobalU p u₀)) U :=
    uniformMovingFrameLeftTailConvergence_of_leftEquilibrium
      hleftEq hTW.lim_neg_inf.1
  exact ⟨hsol, hweighted,
    uniformMovingFrameConvergence_of_coMovingWeightedL2_of_step4
      heta henergyInt hweighted hmod hlefttail⟩

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_of_leftEquilibrium

end AxiomAudit

end ShenWork.Paper1
