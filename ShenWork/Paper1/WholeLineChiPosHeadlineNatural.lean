import ShenWork.Paper1.WholeLineChiPosStabilityNatural
import ShenWork.Paper1.WholeLineWeightedRegularityChiNonposHeadlineNatural

/-!
# Paper 1 Theorem 1.2 — the paper-datum headline on both sensitivity branches

`paper1_Theorem_1_2_chi_nonpos_paperDatum` covers `χ ≤ 0`.  This file adds the
positive branch and the combined statement.

Scope note (faithful, not an over-claim): the paper states Theorem 1.2 for
`0 ≤ χ < χ*` at the critical exponent, but its left-tail step (Section 5, Step 4)
invokes Proposition 1.2, whose positive branch the paper proves only for
`χ < 1/2`.  Our positive branch therefore carries `χ < 1/2` — exactly the range
the source's own argument supports.  The window `[1/2, χ*)` is recorded as open
in HANDOFF/CAPSTONE_REGISTRY.md (no linear instability, no bifurcation and no
known counterexample there, so it is plausibly true but unproved).
-/

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-- Theorem 1.2 for positive sensitivity below the paper's Proposition 1.2
threshold, in the paper's phase space. -/
theorem paper1_Theorem_1_2_chi_pos_paperDatum
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1) :
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
  obtain ⟨kappaOne, hkappaOne, hkappaOne_one, hrightTail⟩ := htail
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw₀ : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hleftW : StrictlyPositiveAtLeft w.1 := by simpa [w] using hleft
  have hinitialW : WeightedL2InitialCloseness eta w.1 U := by
    simpa [w] using hinitial
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w, ?_⟩
  simpa [w] using
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_natural
      p hregime hchi hchi_half hcritical hc hTW hreg hstrict
        hkappaOne hkappaOne_one hrightTail hroot hetaCap w hw₀ hleftW hinitialW

/-- Theorem 1.2 on the union of the two proved sensitivity ranges: every
`χ ≤ 0` (with the paper's exponent inequality carried by the regime) and every
`0 < χ < 1/2` at the critical exponent. -/
theorem paper1_Theorem_1_2_paperDatum_of_chi_lt_half
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hbranch : p.χ ≤ 0 ∨ (0 < p.χ ∧ p.χ < 1 / 2 ∧ p.α = p.m + p.γ - 1)) :
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
  rcases hbranch with hnonpos | ⟨hpos, hhalf, hcritical⟩
  · exact paper1_Theorem_1_2_chi_nonpos_paperDatum p hregime hnonpos
  · exact paper1_Theorem_1_2_chi_pos_paperDatum p hregime hpos hhalf hcritical

section AxiomAudit

#print axioms paper1_Theorem_1_2_chi_pos_paperDatum
#print axioms paper1_Theorem_1_2_paperDatum_of_chi_lt_half

end AxiomAudit

end ShenWork.Paper1
