import ShenWork.Paper1.Theorem13ChiNonposNatural
import ShenWork.Paper1.WholeLineChiPosStabilityNatural

/-!
# Paper 1 Theorem 1.3 (uniqueness) for positive sensitivity

Mirror of `Theorem_1_3_amended_chi_nonpos`.  The uniqueness argument itself is
χ-free: feeding the second wave as initial datum, the two-wave weighted
closeness from the common right-tail asymptotic, the paper phase-space
membership and left positivity of a wave profile, the profile identification
from a common orbit, and the recovery of `V` from `U` are all sign-agnostic.
The ONLY sensitivity-specific inputs are the two invocations of Step 4, which
now exist for `0 < χ < 1/2` at the critical exponent.

The critical exponent is not an extra hypothesis: for `0 < χ` the
`StableWaveParameterRegime` positive branch already carries
`α = m + γ - 1`.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-- Uniqueness of the traveling wave for positive sensitivity below the
paper's Proposition 1.2 threshold. -/
theorem Theorem_1_3_amended_chi_pos
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_half : p.χ < 1 / 2) :
    ∃ cStarStar : ℝ → ℝ, ∃ budget : Paper531StabilityBudget p cStarStar,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        TravelingWaveRegularity p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        TravelingWaveRegularity p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, paper531RootMinus c budget.A budget.B < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  -- the critical exponent comes from the regime's positive branch
  have hcritical : p.α = p.m + p.γ - 1 := by
    rcases hregime with hneg | hpos
    · exact absurd hneg.1 (not_lt.mpr hchi.le)
    · exact hpos.2.2
  refine ⟨paper5CorrectedCStarStar p,
    paper531ConcreteStabilityBudget p hregime,
    paper5CorrectedCStarStar_asymptotic p,
    paper5CorrectedCStarStar_baseline_le p, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hreg₁ hTW₂ hreg₂ hstrict₁ hstrict₂ htailPair
  rcases htailPair with ⟨κ₁, hroot_κ₁, hκ₁_one, htail₁, htail₂⟩
  let budget : Paper531StabilityBudget p (paper5CorrectedCStarStar p) :=
    paper531ConcreteStabilityBudget p hregime
  have hkappa_κ₁ : kappa c < κ₁ :=
    (budget.kappa_le_rootMinus hc).trans_lt hroot_κ₁
  have hroot_cap :
      paper531RootMinus c budget.A budget.B < stabilityWeightCap p :=
    (budget.cap_between c hc).1
  rcases exists_between (lt_min hroot_κ₁ hroot_cap) with
    ⟨eta, hroot_eta, heta_min⟩
  have heta_κ₁ : eta < κ₁ := lt_of_lt_of_le heta_min (min_le_left _ _)
  have heta_cap : eta < stabilityWeightCap p :=
    lt_of_lt_of_le heta_min (min_le_right _ _)
  have heta_pos : 0 < eta := (budget.rootMinus_pos hc).trans hroot_eta
  -- the second wave as an admissible datum (all χ-free)
  have hclose₂₁ : WeightedL2InitialCloseness eta U₂ U₁ :=
    WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
      heta_pos heta_κ₁ hreg₁.U_cont hreg₂.U_cont
      hstrict₁.hasWaveUpperTailBound hstrict₂.hasWaveUpperTailBound
      htail₁ htail₂
  have hU₂paper : PaperNonnegativeInitialDatum U₂ :=
    ⟨⟨travelingWave_U_uniformContinuous hTW₂ hreg₂.U_cont,
      hstrict₂.isBddFun⟩, fun x => (hTW₂.U_pos x).le⟩
  have hU₂left : StrictlyPositiveAtLeft U₂ :=
    IsTravelingWave.strictlyPositiveAtLeft hTW₂
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd U₂ hU₂paper.1
  have hw₀ : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hU₂paper.2 x
  have hwleft : StrictlyPositiveAtLeft w.1 := by simpa [w] using hU₂left
  -- the orbit of the second wave converges to BOTH profiles
  have hconvs :
      UniformMovingFrameConvergence c (wholeLineCauchyGlobalU p w) U₁ ∧
        UniformMovingFrameConvergence c (wholeLineCauchyGlobalU p w) U₂ := by
    constructor
    · have hclose : WeightedL2InitialCloseness eta w.1 U₁ := by
        simpa [w] using hclose₂₁
      exact
        (wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_natural
          p hregime hchi hchi_half hcritical hc hTW₁ hreg₁ hstrict₁
            hkappa_κ₁ hκ₁_one htail₁ hroot_eta heta_cap w hw₀ hwleft
            hclose).2.2
    · have hrefl : WeightedL2InitialCloseness eta w.1 U₂ := by
        simpa [w] using WeightedL2InitialCloseness.refl eta U₂
      exact
        (wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_pos_natural
          p hregime hchi hchi_half hcritical hc hTW₂ hreg₂ hstrict₂
            hkappa_κ₁ hκ₁_one htail₂ hroot_eta heta_cap w hw₀ hwleft
            hrefl).2.2
  have hU : ∀ x, U₁ x = U₂ x :=
    UniformMovingFrameConvergence.profile_eq_of_common_orbit hconvs.1 hconvs.2
  have hU_fun : U₁ = U₂ := funext hU
  refine ⟨hU, ?_⟩
  intro x
  rw [V_eq_frozenElliptic_of_TravelingWaveRegularity
        hTW₁ hstrict₁.hasWaveUpperTailBound hreg₁,
    V_eq_frozenElliptic_of_TravelingWaveRegularity
        hTW₂ hstrict₂.hasWaveUpperTailBound hreg₂,
    hU_fun]

/-- Uniqueness on the union of the two proved sensitivity ranges. -/
theorem Theorem_1_3_amended_of_chi_lt_half
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hbranch : p.χ ≤ 0 ∨ (0 < p.χ ∧ p.χ < 1 / 2)) :
    ∃ cStarStar : ℝ → ℝ, ∃ budget : Paper531StabilityBudget p cStarStar,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U₁ V₁ U₂ V₂ : ℝ → ℝ,
        IsTravelingWave p c U₁ V₁ →
        TravelingWaveRegularity p c U₁ V₁ →
        IsTravelingWave p c U₂ V₂ →
        TravelingWaveRegularity p c U₂ V₂ →
        HasStrictWaveUpperTailBound p c U₁ →
        HasStrictWaveUpperTailBound p c U₂ →
        (∃ κ₁, paper531RootMinus c budget.A budget.B < κ₁ ∧ κ₁ < 1 ∧
          HasWaveRightTailAsymptotic c κ₁ U₁ ∧
          HasWaveRightTailAsymptotic c κ₁ U₂) →
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  rcases hbranch with hnonpos | ⟨hpos, hhalf⟩
  · exact Theorem_1_3_amended_chi_nonpos p hregime hnonpos
  · exact Theorem_1_3_amended_chi_pos p hregime hpos hhalf

section AxiomAudit

#print axioms Theorem_1_3_amended_chi_pos
#print axioms Theorem_1_3_amended_of_chi_lt_half

end AxiomAudit

end ShenWork.Paper1
