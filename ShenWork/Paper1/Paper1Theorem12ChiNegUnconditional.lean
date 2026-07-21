/-
  Paper 1, Theorem 1.2 (strictly negative sensitivity, χ<0) — UNCONDITIONAL in
  the wave.

  Mirrors `paper1_Theorem_1_2_chi_pos_unconditional`.  The traveling wave, its
  full Section-5 regularity, the strict min-form upper tail bound, and the sharp
  right-tail asymptotic are all CONSTRUCTED (via
  `paper1_negativeConstruction_selfStep_reg_strictBarrier`), so the only wave
  hypothesis on the stability datum that survives is the inherent
  `WeightedL2InitialCloseness`.

  Speed threshold: `max (paper5CorrectedCStarStar p χ) (cStarLower p)` — the
  stability threshold combined with the negative construction threshold, folded
  so the `χ → 0` asymptotic `γ + γ⁻¹` is preserved (the max only bites at the
  actual parameter `χ = p.χ`).
-/
import ShenWork.Paper1.WaveNegativeStrictBarrierConstruction
import ShenWork.Paper1.WholeLineWeightedRegularityChiNonposHeadlineNatural

open Filter Topology MeasureTheory

namespace ShenWork.Paper1

noncomputable section

/-- Combined negative-sensitivity speed threshold: the stability threshold
`paper5CorrectedCStarStar` raised to also clear the construction threshold
`cStarLower p`, but only at the actual parameter value `χ = p.χ` so the paper's
`γ + γ⁻¹` asymptotic (which reads the threshold family off values `χ ≠ p.χ`) is
untouched. -/
def cStarStarNeg (p : CMParams) : ℝ → ℝ :=
  fun χ =>
    if χ = p.χ then max (paper5CorrectedCStarStar p χ) (cStarLower p)
    else paper5CorrectedCStarStar p χ

theorem cStarStarNeg_at_param (p : CMParams) :
    cStarStarNeg p p.χ = max (paper5CorrectedCStarStar p p.χ) (cStarLower p) := by
  have h : cStarStarNeg p p.χ =
      if p.χ = p.χ then max (paper5CorrectedCStarStar p p.χ) (cStarLower p)
      else paper5CorrectedCStarStar p p.χ := rfl
  rw [h, if_pos rfl]

theorem paper5CorrectedCStarStar_le_cStarStarNeg (p : CMParams) :
    paper5CorrectedCStarStar p p.χ ≤ cStarStarNeg p p.χ := by
  rw [cStarStarNeg_at_param]; exact le_max_left _ _

theorem cStarLower_le_cStarStarNeg (p : CMParams) :
    cStarLower p ≤ cStarStarNeg p p.χ := by
  rw [cStarStarNeg_at_param]; exact le_max_right _ _

/-- The combined threshold keeps the `χ → 0` asymptotic `γ + γ⁻¹`, because for
`|χ| < |p.χ|` we have `χ ≠ p.χ` and the threshold equals the paper witness
`γ + γ⁻¹ + |χ|^{1/6}`. -/
theorem cStarStarNeg_asymptotic (p : CMParams) (hchi : p.χ < 0) :
    StabilitySpeedThresholdFamilyAsymptotic p (cStarStarNeg p) := by
  refine ⟨1, one_pos, |p.χ|, abs_pos.mpr (ne_of_lt hchi), ?_⟩
  intro χ hχsmall
  have hne : χ ≠ p.χ := by
    intro heq; subst χ; exact (lt_irrefl |p.χ|) hχsmall
  have h1 : cStarStarNeg p χ = paper5CorrectedCStarStar p χ := by
    simp only [cStarStarNeg, if_neg hne]
  rw [h1, paper5CorrectedCStarStar]
  simp only [hne, ↓reduceIte, cStarStarWitness]
  have hpow : 0 ≤ |χ| ^ (1 / 6 : ℝ) := Real.rpow_nonneg (abs_nonneg χ) _
  rw [show p.γ + p.γ⁻¹ + |χ| ^ (1 / 6 : ℝ) - (p.γ + p.γ⁻¹)
      = |χ| ^ (1 / 6 : ℝ) by ring, abs_of_nonneg hpow, one_mul]

theorem cStarStarNeg_baseline_le (p : CMParams) :
    stabilitySpeedBaseline p ≤ cStarStarNeg p p.χ :=
  le_trans (paper5CorrectedCStarStar_baseline_le p)
    (paper5CorrectedCStarStar_le_cStarStarNeg p)

/-- **Paper 1, Theorem 1.2, strictly negative sensitivity, unconditional in the
wave.** For `χ < 0` in the stable-wave regime, there is a speed threshold and a
stability budget such that above the threshold a traveling wave `U,V` **exists**
(constructed) with full regularity, and every nonnegative, left-positive datum
weighted-`L²`-close to `U` generates a global solution converging to `U` both in
weighted `L²` and uniformly in the moving frame. -/
theorem paper1_Theorem_1_2_chi_neg_unconditional
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ < 0) :
    ∃ cStarStar : ℝ → ℝ,
      ∃ budget : Paper531StabilityBudget p cStarStar,
        StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
        ∀ c : ℝ, cStarStar p.χ < c →
          ∃ U V : ℝ → ℝ,
            IsTravelingWave p c U V ∧
            TravelingWaveRegularity p c U V ∧
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
  have hα : p.α ≤ p.m + p.γ - 1 := hregime.alpha_le
  have hMpos : 0 < MChi p := hregime.MChi_pos
  have hAnn : 0 ≤ paper531ConcreteA p := (paper531ConcreteAB_nonneg p hMpos).1
  have hBnn : 0 ≤ paper531ConcreteB p := (paper531ConcreteAB_nonneg p hMpos).2
  -- combined stability budget for the combined threshold
  let budget : Paper531StabilityBudget p (cStarStarNeg p) :=
    paper531StabilityBudget_of_cap_threshold hAnn hBnn
      (by
        rw [cStarStarNeg_at_param]
        exact le_trans (paper5CorrectedCStarStar_cap_le p) (le_max_left _ _))
  refine ⟨cStarStarNeg p, budget, cStarStarNeg_asymptotic p hchi,
    cStarStarNeg_baseline_le p, ?_⟩
  intro c hc
  have hc_stab : paper5CorrectedCStarStar p p.χ < c :=
    lt_of_le_of_lt (paper5CorrectedCStarStar_le_cStarStarNeg p) hc
  have hc_lower : cStarLower p < c :=
    lt_of_le_of_lt (cStarLower_le_cStarStarNeg p) hc
  -- construct the wave with the strict min-form barrier
  obtain ⟨U, hprofile, hreg, hstrict, htail⟩ :=
    paper1_negativeConstruction_selfStep_reg_strictBarrier p hα hchi c hc_lower
  refine ⟨U, frozenElliptic p U, hprofile.to_travelingWave, hreg, ?_⟩
  intro eta hroot hetaCap u₀ hu₀ hleft hinitial
  -- pick a right-tail exponent strictly between `kappa c` and `1`
  have hcaplt : kappa c < negativeBranchTailCap p c :=
    kappa_lt_negativeBranchTailCap p hc_lower
  have hcap_le1 : negativeBranchTailCap p c ≤ 1 := by
    simp only [negativeBranchTailCap]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  set kappaOne : ℝ := (kappa c + negativeBranchTailCap p c) / 2 with hk1_def
  have hkappaOne : kappa c < kappaOne := by rw [hk1_def]; linarith
  have hkappaOne_cap : kappaOne < negativeBranchTailCap p c := by rw [hk1_def]; linarith
  have hkappaOne_one : kappaOne < 1 := lt_of_lt_of_le hkappaOne_cap hcap_le1
  have htailOne : HasWaveRightTailAsymptotic c kappaOne U :=
    htail kappaOne hkappaOne hkappaOne_cap
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  refine ⟨wholeLineCauchyGlobalU p w, wholeLineCauchyGlobalV p w, ?_⟩
  simpa [w] using
    wholeLineCauchyGlobal_solution_weighted_and_uniformConvergence_chi_neg_natural
      p hregime hchi hc_stab hprofile.to_travelingWave hreg hstrict
        hkappaOne hkappaOne_one htailOne hroot hetaCap
        u₀ hu₀ hleft hinitial

section AxiomAudit
#print axioms paper1_Theorem_1_2_chi_neg_unconditional
end AxiomAudit

end

end ShenWork.Paper1
