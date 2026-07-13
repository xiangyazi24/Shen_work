/- Unconditional positive-attraction traveling-wave producer. -/
import ShenWork.Paper1.WavePositiveSelfStepClosedGraph
import ShenWork.Paper1.WavePositiveStrictBarrier
import ShenWork.Paper1.StationaryUpperTail

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Genuine positive headline construction from the compact-convex
nonmonotone lower-pinned trap and the diagonal whole-line Green self-step.
All scalar choices, Schauder compactness, closed graph, endpoint selection,
strict upper comparison, and tail squeeze are internal theorems. -/
theorem paper1_positiveConstruction_selfStep :
    ∀ p : CMParams, p.α = p.m + p.γ - 1 →
      0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
      ∀ c : ℝ, 2 < c →
        ∃ U : ℝ → ℝ,
          FrozenStationaryWaveProfile p c U ∧
          ContDiff ℝ 2 U ∧
          ContDiff ℝ 2 (frozenElliptic p U) ∧
          ShenUpperBoundPositive p c U ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
            HasWaveRightTailAsymptotic c κ₁ U := by
  intro p hα hχ0 hχsmall c hc
  let hcond := positiveSelfStepExactConditions_of_branchCap
    p hα hχ0 hχsmall hc
  obtain ⟨D, hD1, hDmin, hplateau⟩ :=
    exists_positivePlateau_D p
      (lt_of_lt_of_le hχsmall (min_le_left _ _))
      hcond.hκ0 (sub_pos.mpr hcond.hgap)
  let s : Paper1PositiveLocalStepScalarData p c D :=
    Classical.choice (paper1PositiveLocalStepScalarData_exists p D
      (lt_of_lt_of_le zero_lt_one hcond.hM))
  obtain ⟨U, hU, _hfix, A, hstat, hU2⟩ :=
    paperPositive_fixed_stationary_of_selfStep
      hcond hDmin hD1 hplateau s
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hpos : ∀ x, 0 < U x := by
    intro x
    exact lt_of_lt_of_le
      (lowerBarrierPlateau_pos hcond.hκ0
        (sub_pos.mpr hcond.hgap) hDpos x)
      (hU.lower x)
  have hright : Tendsto U atTop (nhds 0) :=
    hU.bare.tendsto_atTop_zero hcond.hκ0
  have hleft : Tendsto U atBot (nhds 1) := by
    apply positiveStationary_tendsto_atBot_one p hα hχ0
      (lt_of_lt_of_le hχsmall (min_le_left _ _))
      (lt_of_lt_of_le zero_lt_one hcond.hM) hcond.hκ0
      (sub_pos.mpr hcond.hgap) hDpos
      (by simpa [paperPositiveSelfStepModulus] using hU)
      A s.hlam s.hΛ0 hstat
  have hprofile : FrozenStationaryWaveProfile p c U :=
    FrozenStationaryWaveProfile.mk_auto_limits
      (lt_trans two_pos hc) hpos hU.bare.cunif_bdd hstat hleft hright
  have hstrict : ∀ x,
      U x < upperBarrier (kappa c) (MChi p) x :=
    positiveStationary_strict_upperBarrier p hα hχ0 hχsmall hc
      hU.bare hpos hU2 hstat hright
  have hχ1 : p.χ < 1 := by
    have hhalf : p.χ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hχsmall (min_le_left _ _)
    linarith
  have hupper : ShenUpperBoundPositive p c U :=
    ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
      hχ0 hχ1 hpos hstrict
  have htail : ∀ κ₁, kappa c < κ₁ →
      κ₁ < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) →
      HasWaveRightTailAsymptotic c κ₁ U :=
    lowerPinnedWaveTrap_tail_family_for_branch
      (p := p) (c := c) (κtilde := positiveBranchTailCap p c)
      (D := D) hDpos.le (by simp [positiveBranchTailCap])
      hU.bare hU.lower
  have hV2 : ContDiff ℝ 2 (frozenElliptic p U) :=
    frozenElliptic_contDiff_two_of_inWaveTrapSet p hU.bare
  exact ⟨U, hprofile, hU2, hV2, hupper, htail⟩

/-- Concrete attraction-regime witness proving that the positive producer is
not an implication over an empty parameter class. -/
theorem paper1_positiveConstruction_selfStep_nonvacuous :
    ∃ p : CMParams, ∃ c : ℝ,
      p.α = p.m + p.γ - 1 ∧
      0 ≤ p.χ ∧ p.χ < min (1 / 2 : ℝ) (chiStar p) ∧
      2 < c ∧
      ∃ U : ℝ → ℝ,
        FrozenStationaryWaveProfile p c U ∧
        ContDiff ℝ 2 U ∧
        ContDiff ℝ 2 (frozenElliptic p U) ∧
        ShenUpperBoundPositive p c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U := by
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
  exact ⟨p, 3, hα, hχ0, hχsmall, hc,
    paper1_positiveConstruction_selfStep p hα hχ0 hχsmall 3 hc⟩

section AxiomAudit

#print axioms paper1_positiveConstruction_selfStep
#print axioms paper1_positiveConstruction_selfStep_nonvacuous

end AxiomAudit

end ShenWork.Paper1
