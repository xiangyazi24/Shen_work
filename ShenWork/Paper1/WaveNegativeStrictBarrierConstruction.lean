/-
  Paper 1, negative sensitivity (χ<0): the constructed wave carries the strict
  min-form upper tail bound.

  `paper1_negativeConstruction_selfStep_reg` exposes only the max-form
  `ShenUpperBoundNegative`.  This file re-runs the SAME Schauder self-step
  construction body and, using the trap membership available at the fixed point
  together with `negativeWave_hasStrictWaveUpperTailBound`, upgrades the output
  to the strict min-form `HasStrictWaveUpperTailBound p c U`.  This is exactly
  the wave input required by `paper1_Theorem_1_2_chi_nonpos_paperDatum`.
-/
import ShenWork.Paper1.Paper1Theorem12ChiNonposUnconditional
import ShenWork.Paper1.WaveNegativeStrictBarrier

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- **Negative Schauder construction with the strict min-form barrier.**
For `α ≤ m+γ-1`, `χ < 0`, and `c > cStarLower p`, the constructed frozen
stationary wave carries full traveling-wave regularity, the strict min-form
upper tail bound, and the sharp right-tail asymptotic family. -/
theorem paper1_negativeConstruction_selfStep_reg_strictBarrier :
    ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ < 0 →
      ∀ c : ℝ, cStarLower p < c →
        ∃ U : ℝ → ℝ,
          FrozenStationaryWaveProfile p c U ∧
          TravelingWaveRegularity p c U (frozenElliptic p U) ∧
          HasStrictWaveUpperTailBound p c U ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < negativeBranchTailCap p c →
              HasWaveRightTailAsymptotic c κ₁ U := by
  intro p hα hχ c hc
  let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ.le hc
  let D := paper1NegativeRotheD p c
  let s := paper1NegativeLocalStepScalars p hα hχ.le hc
  obtain ⟨U, hU, hfix, hstat, hUdiff, hUderivDiff, hsourceTail⟩ :=
    paperNegativePinned_fixed_stationary_of_selfStep
      hcond (paper1NegativeRotheD_gt p c)
      (paper1NegativeRotheD_one_le p c) s
  have hUpin : InLowerPinnedMonotoneTrap (kappa c) 1
      (lowerBarrierRaw (kappa c) (negativeBranchTailCap p c) D) U :=
    hU.toLowerPinned
  have hgap : 0 < negativeBranchTailCap p c - kappa c :=
    sub_pos.mpr hcond.hgap
  have hDpos : 0 < D := D_pos_of_paperDMin_lt hcond
    (paper1NegativeRotheD_gt p c)
  have hnontriv : ProfileNontrivial U :=
    profileNontrivial_of_lowerBarrierRaw_tail_bound hcond
      (paper1NegativeRotheD_gt p c) (fun x _hx => hUpin.lower x)
  have hpos : ∀ x, 0 < U x :=
    stationaryProfile_strictlyPositive_of_trap_regularity
      one_pos hUpin.bare hstat hUdiff hUderivDiff hnontriv
  have hsource : FrozenStationaryGreenSourceTail c s.lam U := by
    simpa [PaperGreenSourceTailData, FrozenStationaryGreenSourceTail] using
      hsourceTail
  have hflat : FrozenStationaryFlatAtLeft p U :=
    frozenStationaryFlatAtLeft_of_green_source_tail
      s.hlam one_pos hUpin hUdiff hsource
  have hleft : Tendsto U atBot (nhds 1) :=
    InMonotoneWaveTrapSet.tendsto_atBot_one_of_stationary_flat_and_lowerBarrierRaw_pin
      hcond.hκ0 hgap hDpos hUpin.bare hUpin.lower hflat hstat
  have hright : Tendsto U atTop (nhds 0) :=
    hUpin.bare.tendsto_atTop_zero hcond.hκ0
  have hcpos : 0 < c := by
    rw [hcond.hc]
    have hinv : 0 < (kappa c)⁻¹ := inv_pos.mpr hcond.hκ0
    nlinarith [hcond.hκ0, hinv]
  let hprofile : FrozenStationaryWaveProfile p c U :=
    FrozenStationaryWaveProfile.mk_auto_limits hcpos hpos
      hUpin.bare.trap.cunif_bdd hstat hleft hright
  have htail : ∀ κ₁, kappa c < κ₁ →
      κ₁ < negativeBranchTailCap p c →
        HasWaveRightTailAsymptotic c κ₁ U :=
    lowerPinnedRawMonotoneTrap_tail_family_for_branch
      (le_trans zero_le_one (paper1NegativeRotheD_one_le p c))
      (by simp [negativeBranchTailCap]) hUpin
  -- traveling-wave regularity, recovered from the fixed-point step datum
  let d := paperNegativePinnedSelfStepData s hU
  have hdU : d.fixed.W = U :=
    (paperNegativePinnedSelfStepMap_eq s hU).symm.trans hfix
  have hU2 : ContDiff ℝ 2 U := by
    have := d.contDiff_two s.hlam
    rwa [hdU] at this
  have hA : PaperStepAnalytic p c s.lam 1 (kappa c) s.Λ U U U := by
    simpa only [hdU] using paperStepAnalytic_of_core s.hlam d.fixed.analyticCore
  have hMchi : MChi p = 1 := MChi_eq_one_of_chi_nonpos p hχ.le
  have htrapM : InWaveTrapSet (kappa c) (MChi p) U := by
    rw [hMchi]; exact hUpin.bare.trap
  have haM : PaperStepAnalytic p c s.lam (MChi p) (kappa c) s.Λ U U U := by
    rw [hMchi]; exact hA
  have hV2 : ContDiff ℝ 2 (frozenElliptic p U) :=
    frozenElliptic_contDiff_two_of_inWaveTrapSet p hUpin.bare.trap
  have hreg : TravelingWaveRegularity p c U (frozenElliptic p U) :=
    hprofile.travelingWaveRegularity_of_green_step haM s.hlam htrapM hU2 hV2
  -- strict min-form barrier from the trap membership at the fixed point
  have hstrict : HasStrictWaveUpperTailBound p c U :=
    negativeWave_hasStrictWaveUpperTailBound p hχ hα hc hUpin.bare
      hstat hpos hUdiff hUderivDiff hright
  exact ⟨U, hprofile, hreg, hstrict, htail⟩

section AxiomAudit
#print axioms paper1_negativeConstruction_selfStep_reg_strictBarrier
end AxiomAudit

end

end ShenWork.Paper1
