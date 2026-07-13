/- Hypothesis-free assembly of Paper 1, Theorem 1.1. -/
import ShenWork.Paper1.WaveNegativeRotheCore
import ShenWork.Paper1.WavePositiveConstruction

namespace ShenWork.Paper1

noncomputable section

/-- Paper 1, Theorem 1.1 with both sign branches constructed internally.
The proof directly assembles the two genuine self-step producers; no assumed
branch adapter or Route-A positive package occurs in the proof term. -/
theorem Theorem_1_1.unconditional : Theorem_1_1 := by
  constructor
  · intro p hα hχ c hc
    obtain ⟨U, hprofile, hUmono, hVmono, hupper, htail⟩ :=
      paper1_negativeConstruction_selfStep p hα hχ c hc
    exact
      ⟨U, frozenElliptic p U,
        hprofile.to_monotoneTravelingWave hUmono hVmono,
        hupper, by simpa [negativeBranchTailCap] using htail⟩
  · intro p hα hχ0 hχsmall c hc
    obtain ⟨U, hprofile, _hU2, _hV2, hupper, htail⟩ :=
      paper1_positiveConstruction_selfStep p hα hχ0 hχsmall c hc
    exact
      ⟨U, frozenElliptic p U, hprofile.to_travelingWave, hupper, htail⟩

/-- An explicit attraction-regime instance of the headline has a genuinely
nonzero wave: the constructed profile is strictly positive at the origin. -/
theorem Theorem_1_1.unconditional_positive_nonvacuous :
    ∃ p : CMParams, ∃ c : ℝ, ∃ U V : ℝ → ℝ,
      p.α = p.m + p.γ - 1 ∧
      0 ≤ p.χ ∧ p.χ < min (1 / 2 : ℝ) (chiStar p) ∧
      2 < c ∧ IsTravelingWave p c U V ∧
      ShenUpperBoundPositive p c U ∧ 0 < U 0 := by
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 1 / 4
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hα : p.α = p.m + p.γ - 1 := by norm_num [p]
  have hχ0 : 0 ≤ p.χ := by norm_num [p]
  have hχsmall : p.χ < min (1 / 2 : ℝ) (chiStar p) := by
    norm_num [p, chiStar]
  have hc : (2 : ℝ) < 3 := by norm_num
  obtain ⟨U, hprofile, _hU2, _hV2, hupper, _htail⟩ :=
    paper1_positiveConstruction_selfStep p hα hχ0 hχsmall 3 hc
  exact ⟨p, 3, U, frozenElliptic p U, hα, hχ0, hχsmall, hc,
    hprofile.to_travelingWave, hupper, hprofile.U_pos 0⟩

section AxiomAudit

#print axioms Theorem_1_1.unconditional
#print axioms Theorem_1_1.unconditional_positive_nonvacuous

end AxiomAudit

end

end ShenWork.Paper1
