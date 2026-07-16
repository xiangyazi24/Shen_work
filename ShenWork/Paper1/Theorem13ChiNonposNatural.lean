import ShenWork.Paper1.Theorem13Corrected
import ShenWork.Paper1.WholeLineWeightedRegularityChiNonposHeadlineNatural

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Paper 1 Theorem 1.3 for nonpositive sensitivity

The canonical Cauchy solution with the second wave as initial datum is used
twice: stability about the first wave and stability about the second wave
make the same orbit converge uniformly to both profiles.  Thus no
unrestricted whole-line Cauchy uniqueness principle is needed.
-/

/-- Uniform moving-frame limits of one orbit are unique. -/
theorem UniformMovingFrameConvergence.profile_eq_of_common_orbit
    {c : ℝ} {u : ℝ → ℝ → ℝ} {U₁ U₂ : ℝ → ℝ}
    (h₁ : UniformMovingFrameConvergence c u U₁)
    (h₂ : UniformMovingFrameConvergence c u U₂) :
    ∀ x, U₁ x = U₂ x := by
  intro y
  by_contra hne
  have hdist_pos : 0 < |U₁ y - U₂ y| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  rcases h₁ (|U₁ y - U₂ y| / 3) (by positivity) with ⟨T₁, hT₁⟩
  rcases h₂ (|U₁ y - U₂ y| / 3) (by positivity) with ⟨T₂, hT₂⟩
  let t : ℝ := max T₁ T₂
  let x : ℝ := y + c * t
  have hframe : x - c * t = y := by
    dsimp [x]
    ring
  have h₁lt : |u t x - U₁ y| < |U₁ y - U₂ y| / 3 := by
    simpa [hframe] using hT₁ t x (by simp [t])
  have h₂lt : |u t x - U₂ y| < |U₁ y - U₂ y| / 3 := by
    simpa [hframe] using hT₂ t x (by simp [t])
  have htri :
      |U₁ y - U₂ y| ≤ |U₁ y - u t x| + |u t x - U₂ y| :=
    abs_sub_le (U₁ y) (u t x) (U₂ y)
  have hsum :
      |U₁ y - u t x| + |u t x - U₂ y| <
        |U₁ y - U₂ y| / 3 + |U₁ y - U₂ y| / 3 :=
    add_lt_add (by simpa [abs_sub_comm] using h₁lt) h₂lt
  linarith

/-- The exact corrected Theorem 1.3 conclusion for every nonpositive
sensitivity.  The speed family and the perturbed-root budget are the concrete
ones from the Section 5 energy construction. -/
theorem Theorem_1_3_amended_chi_nonpos
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ ≤ 0) :
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
  have heta_κ₁ : eta < κ₁ :=
    lt_of_lt_of_le heta_min (min_le_left _ _)
  have heta_cap : eta < stabilityWeightCap p :=
    lt_of_lt_of_le heta_min (min_le_right _ _)
  have heta_pos : 0 < eta :=
    (budget.rootMinus_pos hc).trans hroot_eta
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
  have hconvs :
      UniformMovingFrameConvergence c (wholeLineCauchyGlobalU p w) U₁ ∧
        UniformMovingFrameConvergence c (wholeLineCauchyGlobalU p w) U₂ := by
    rcases lt_or_eq_of_le hchi with hchiNeg | hchiZero
    · constructor
      · have hfull :=
          wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_neg_natural
            p hregime hchiNeg hc hTW₁ hreg₁ hstrict₁
              hkappa_κ₁ hκ₁_one htail₁ hroot_eta heta_cap
              U₂ hU₂paper hU₂left hclose₂₁
        simpa [w, budget] using hfull.2.2
      · have hfull :=
          wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_neg_natural
            p hregime hchiNeg hc hTW₂ hreg₂ hstrict₂
              hkappa_κ₁ hκ₁_one htail₂ hroot_eta heta_cap
              U₂ hU₂paper hU₂left
              (WeightedL2InitialCloseness.refl eta U₂)
        simpa [w, budget] using hfull.2.2
    · constructor
      · have hfull :=
          wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_zero_natural
            p hregime hchiZero hc hTW₁ hreg₁ hstrict₁
              hroot_eta heta_cap U₂ hU₂paper hU₂left hclose₂₁
        simpa [w, budget] using hfull.2.2
      · have hfull :=
          wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_zero_natural
            p hregime hchiZero hc hTW₂ hreg₂ hstrict₂
              hroot_eta heta_cap U₂ hU₂paper hU₂left
              (WeightedL2InitialCloseness.refl eta U₂)
        simpa [w, budget] using hfull.2.2
  have hU : ∀ x, U₁ x = U₂ x :=
    UniformMovingFrameConvergence.profile_eq_of_common_orbit hconvs.1 hconvs.2
  have hU_fun : U₁ = U₂ := funext hU
  constructor
  · exact hU
  · intro x
    rw [V_eq_frozenElliptic_of_TravelingWaveRegularity
          hTW₁ hstrict₁.hasWaveUpperTailBound hreg₁,
      V_eq_frozenElliptic_of_TravelingWaveRegularity
          hTW₂ hstrict₂.hasWaveUpperTailBound hreg₂,
      hU_fun]

/-- Strictly negative sensitivity is the corresponding specialization. -/
theorem Theorem_1_3_amended_chi_neg
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ < 0) :
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
        (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  Theorem_1_3_amended_chi_nonpos p hregime hchi.le

section AxiomAudit

#print axioms UniformMovingFrameConvergence.profile_eq_of_common_orbit
#print axioms Theorem_1_3_amended_chi_nonpos
#print axioms Theorem_1_3_amended_chi_neg

end AxiomAudit

end ShenWork.Paper1
