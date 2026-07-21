import ShenWork.Paper1.WholeLineWeightedRegularityChiNonposHeadlineNatural
import ShenWork.Paper1.WavePositiveConstruction

/-!
# Paper 1, Theorem 1.2 (zero sensitivity `χ = 0`) — wave hypothesis DISCHARGED

`paper1_Theorem_1_2_chi_nonpos_paperDatum` proves stability *given* a traveling
wave `U,V` with `IsTravelingWave`, `TravelingWaveRegularity`,
`HasStrictWaveUpperTailBound`, and a right-tail asymptotic, for every `χ ≤ 0`.
At the strict barrier value `χ = 0` those wave inputs are exactly the outputs of
the **positive** Schauder construction `paper1_positiveConstruction_selfStep`
(which covers `0 ≤ χ`): the construction supplies `ShenUpperBoundPositive`, whose
`hasStrictWaveUpperTailBound` yields the *min-form* strict barrier
`U x < min (MChi p) (exp(-κx))`.  This is precisely the input the `χ < 0` branch
cannot produce — the negative construction only supplies the *max-form*
`ShenUpperBoundNegative`, strictly weaker off `x = 0` — and it is why `χ = 0`
closes unconditionally while `χ < 0` does not.

Because the positive construction runs off `2 < c` (not `cStarLower p < c`), the
speed threshold is exactly the stability datum's own `paper5CorrectedCStarStar p`;
no threshold surgery is needed.  This file composes the two, so the traveling wave
is **constructed, not assumed** — the only remaining hypothesis on the datum is the
inherent `WeightedL2InitialCloseness`, the meaning of a stability theorem.

Set `χ = 0` concretely.  The `StableWaveParameterRegime` then forces the positive
branch, giving both `p.χ < chiStar p` (hence `0 < chiStar p`) and the critical
exponent `p.α = p.m + p.γ - 1`.
-/

namespace ShenWork.Paper1

noncomputable section

/-- **Paper 1, Theorem 1.2, zero sensitivity, unconditional in the wave.**
For `χ = 0` at the critical exponent, there is a speed threshold `cStarStar` and a
stability budget such that for every `c` above the threshold a traveling wave `U,V`
**exists** (constructed via the positive Schauder self-step, which covers `0 ≤ χ`)
with full regularity and the strict min-form upper barrier, and every nonneg,
left-positive datum `u₀` that is weighted-`L²`-close to `U` generates a global
solution converging to `U` both in weighted `L²` and uniformly in the moving
frame. -/
theorem paper1_Theorem_1_2_chi_zero_unconditional
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi0 : p.χ = 0) :
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
  have hχ0 : (0 : ℝ) ≤ p.χ := hchi0.ge
  have hχ1 : p.χ < 1 := by rw [hchi0]; norm_num
  -- `χ = 0` lands in the positive branch of the stable regime, exposing both the
  -- strict small-`χ` bound (`χ < chiStar p`) and the critical exponent.
  obtain ⟨hchiStar, hcritical⟩ := hregime.positive_branch_of_chi_nonneg hχ0
  have hchi_small : p.χ < min (1 / 2 : ℝ) (chiStar p) :=
    lt_min (by rw [hchi0]; norm_num) hchiStar
  -- Conditional stability datum for `χ ≤ 0` (with `χ = 0`), threshold and budget
  -- constructed explicitly.
  obtain ⟨cStarStar, budget, hasymp, hbaseline, Hstab⟩ :=
    paper1_Theorem_1_2_chi_nonpos_paperDatum p hregime hchi0.le
  refine ⟨cStarStar, budget, hasymp, hbaseline, ?_⟩
  intro c hc
  have h2c : 2 < c := two_lt_of_stabilitySpeedBaseline_lt hbaseline hc
  -- The positive construction runs off `2 < c` and covers `0 ≤ χ`, so it applies
  -- at `χ = 0` and delivers the wave, its regularity, and `ShenUpperBoundPositive`.
  obtain ⟨U, hprofile, _hU2, _hV2, hreg, hupper, htail⟩ :=
    paper1_positiveConstruction_selfStep p hcritical hχ0 hchi_small c h2c
  -- Convert the construction's `∀`-over-admissible-`κ₁` right tail into the
  -- existential with `κ₁ < 1` that the stability headline wants, instantiating at
  -- the midpoint of `(kappa c, UB)` with `UB ≤ 1`.
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

#print axioms paper1_Theorem_1_2_chi_zero_unconditional

end AxiomAudit

end

end ShenWork.Paper1
