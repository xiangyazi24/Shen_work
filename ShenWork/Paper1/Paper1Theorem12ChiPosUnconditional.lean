import ShenWork.Paper1.WholeLineChiPosHeadlineNatural
import ShenWork.Paper1.WavePositiveConstruction

/-!
# Paper 1, Theorem 1.2 (positive sensitivity) — wave hypothesis DISCHARGED

`paper1_Theorem_1_2_chi_pos_paperDatum` proves stability *given* a traveling wave
`U,V` with `IsTravelingWave`, `TravelingWaveRegularity`, `HasStrictWaveUpperTailBound`,
and a right-tail asymptotic.  Those are exactly the outputs of the Schauder
construction `paper1_positiveConstruction_selfStep` (which is what
`Theorem_1_1.unconditional` uses).  This file composes the two, so the traveling
wave is **constructed, not assumed** — the only remaining hypothesis on the datum is
the inherent `WeightedL2InitialCloseness` (the initial datum is close to the wave),
which is the meaning of a stability theorem, not smuggled hard content.

Range: `0 < χ < min(½, chiStar p)` — the construction's range (the `χ < ½` of the
stability assembly intersected with the `χ < chiStar` needed to build the wave; note
`chiStar p < ½` occurs for large `m`).  Speed `2 < c` is derived from the stability
speed threshold via `two_lt_of_stabilitySpeedBaseline_lt`.

-/

namespace ShenWork.Paper1

noncomputable section

/-- **Paper 1, Theorem 1.2, positive sensitivity, unconditional in the wave.**
For `0 < χ < min(½, chiStar p)` at the critical exponent, there is a speed threshold
`cStarStar` and a stability budget such that for every `c` above the threshold a
traveling wave `U,V` **exists** (constructed) with full regularity, and every nonneg,
left-positive datum `u₀` that is weighted-`L²`-close to `U` generates a global solution
converging to `U` both in weighted `L²` and uniformly in the moving frame. -/
theorem paper1_Theorem_1_2_chi_pos_unconditional
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : 0 < p.χ) (hchi_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hcritical : p.α = p.m + p.γ - 1) :
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
  have hhalf : p.χ < 1 / 2 := lt_of_lt_of_le hchi_small (min_le_left _ _)
  have hχ0 : 0 ≤ p.χ := le_of_lt hchi
  have hχ1 : p.χ < 1 := by linarith
  obtain ⟨cStarStar, budget, hasymp, hbaseline, Hstab⟩ :=
    paper1_Theorem_1_2_chi_pos_paperDatum p hregime hchi hhalf hcritical
  refine ⟨cStarStar, budget, hasymp, hbaseline, ?_⟩
  intro c hc
  have h2c : 2 < c := two_lt_of_stabilitySpeedBaseline_lt hbaseline hc
  obtain ⟨U, hprofile, _hU2, _hV2, hreg, hupper, htail⟩ :=
    paper1_positiveConstruction_selfStep p hcritical hχ0 hchi_small c h2c
  -- the construction gives the right-tail as a ∀-over-admissible-`κ₁`; the stability
  -- headline wants an existential with `κ₁ < 1`.  Instantiate at the midpoint of
  -- `(kappa c, UB)`, where `UB` is the construction's admissible ceiling and `UB ≤ 1`.
  have hkc_pos : 0 < kappa c := kappa_pos_of_two_lt h2c
  have hkc_lt1 : kappa c < 1 := kappa_lt_one_of_two_lt h2c
  set UB : ℝ := min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) with hUB
  have hUB_le1 : UB ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hkc_lt_UB : kappa c < UB := by
    refine lt_min ?_ (lt_min ?_ hkc_lt1)
    · nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one p.hα) hkc_pos]
    · nlinarith [mul_nonneg (by linarith [p.hm] : (0 : ℝ) ≤ p.m - 1) hkc_pos.le]
  have htailE : ∃ kappaOne, kappa c < kappaOne ∧ kappaOne < 1 ∧
      HasWaveRightTailAsymptotic c kappaOne U :=
    ⟨(kappa c + UB) / 2, by linarith, by linarith,
      htail _ (by linarith) (by linarith)⟩
  refine ⟨U, frozenElliptic p U, hprofile.to_travelingWave, hreg, ?_⟩
  intro eta hroot hetaCap u₀ hu₀ hleft hinitial
  exact Hstab c hc U (frozenElliptic p U) hprofile.to_travelingWave hreg
    (hupper.hasStrictWaveUpperTailBound hχ0 hχ1) htailE
    eta hroot hetaCap u₀ hu₀ hleft hinitial

section AxiomAudit

#print axioms paper1_Theorem_1_2_chi_pos_unconditional

end AxiomAudit

end

end ShenWork.Paper1
