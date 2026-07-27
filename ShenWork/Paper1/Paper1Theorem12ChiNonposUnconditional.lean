import ShenWork.Paper1.WaveNegativeRotheCore
import ShenWork.Paper1.WavePositiveConstruction

/-!
# Paper 1, Theorem 1.2 (nonpositive sensitivity) — wave regularity DISCHARGED

`paper1_negativeConstruction_selfStep_reg` upgrades the genuine negative Schauder
construction `paper1_negativeConstruction_selfStep` so that it ALSO exposes
`TravelingWaveRegularity p c U (frozenElliptic p U)`.  The key point is that the
stationary self-step producer only outputs
`Differentiable U` and `Differentiable (deriv U)`, not `ContDiff 2 U`; but the
`ContDiff 2` is already present at the fixed-point step data
(`PaperLocalFixedStepData.contDiff_two`) and, since the fixed point `W` IS the
stationary profile `U`, it transfers.  Feeding it plus the analytic step and the
trap into the generic producer
`FrozenStationaryWaveProfile.travelingWaveRegularity_of_green_step` yields the
Section 5 regularity package for the constructed negative wave.

This closes the regularity input of `paper1_Theorem_1_2_chi_nonpos_paperDatum`
for the constructed negative wave.  The paperDatum has one further wave input,
`HasStrictWaveUpperTailBound p c U` (`∀ x, U x < min (MChi p) (exp(-κx))`, the
min-form strict barrier).  The negative construction only supplies
`ShenUpperBoundNegative` (the max-form `U x < max 1 (exp(-κx))`), which is
strictly weaker off `x = 0`; the min-form strict barrier for the negative branch
is NOT yet in the library for `χ < 0` (see the report accompanying this file).
Hence the fully composed `paper1_Theorem_1_2_chi_nonpos_unconditional` is not
stated here — only the regularity crux it needs is discharged.
-/

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- **Negative Schauder construction, now with full traveling-wave regularity.**

Same genuine cross-frozen self-implicit-step fixed point as
`paper1_negativeConstruction_selfStep`, additionally exposing
`TravelingWaveRegularity`.  The extra output is not an assumption: `ContDiff 2 U`
is recovered from the fixed-point step datum (`d.contDiff_two`), and the analytic
step `PaperStepAnalytic` is the step datum's `analyticCore`. -/
theorem paper1_negativeConstruction_selfStep_reg :
    ∀ p : CMParams, p.α ≤ p.m + p.γ - 1 → p.χ ≤ 0 →
      ∀ c : ℝ, cStarLower p < c →
        ∃ U : ℝ → ℝ,
          FrozenStationaryWaveProfile p c U ∧
          TravelingWaveRegularity p c U (frozenElliptic p U) ∧
          ShenUpperBoundNegative c U ∧
          (∀ x, deriv U x ≤ 0) ∧
          (∀ x, deriv (frozenElliptic p U) x ≤ 0) ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < negativeBranchTailCap p c →
              HasWaveRightTailAsymptotic c κ₁ U := by
  intro p hα hχ c hc
  let hcond := negativePaperLemma42ExactConditions_of_branchCap p hα hχ hc
  let D := paper1NegativeRotheD p c
  let s := paper1NegativeLocalStepScalars p hα hχ hc
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
  have hstrict0 : U 0 < 1 := by
    refine lt_of_le_of_ne (hUpin.bare.le_M 0) ?_
    intro hU0
    exact upperBarrier_interfaceNoContact_of_profile_differentiable
      hcond.hκ0 one_pos hUpin.bare hUdiff 0 (by simp) hU0
  have hupper : ShenUpperBoundNegative c U :=
    ShenUpperBoundNegative_of_strictAtZero hcond.hκ0 hUpin.bare
      hprofile.U_pos hstrict0
  have htail : ∀ κ₁, kappa c < κ₁ →
      κ₁ < negativeBranchTailCap p c →
        HasWaveRightTailAsymptotic c κ₁ U :=
    lowerPinnedRawMonotoneTrap_tail_family_for_branch
      (le_trans zero_le_one (paper1NegativeRotheD_one_le p c))
      (by simp [negativeBranchTailCap]) hUpin
  -- The extra content: recover `ContDiff 2 U` + the analytic step from the
  -- fixed-point step datum, and assemble the Section 5 regularity package.
  let d := paperNegativePinnedSelfStepData s hU
  have hdU : d.fixed.W = U :=
    (paperNegativePinnedSelfStepMap_eq s hU).symm.trans hfix
  have hU2 : ContDiff ℝ 2 U := by
    have := d.contDiff_two s.hlam
    rwa [hdU] at this
  have hA : PaperStepAnalytic p c s.lam 1 (kappa c) s.Λ U U U := by
    simpa only [hdU] using paperStepAnalytic_of_core s.hlam d.fixed.analyticCore
  have hMchi : MChi p = 1 := MChi_eq_one_of_chi_nonpos p hχ
  have htrapM : InWaveTrapSet (kappa c) (MChi p) U := by
    rw [hMchi]; exact hUpin.bare.trap
  have haM : PaperStepAnalytic p c s.lam (MChi p) (kappa c) s.Λ U U U := by
    rw [hMchi]; exact hA
  have hV2 : ContDiff ℝ 2 (frozenElliptic p U) :=
    frozenElliptic_contDiff_two_of_inWaveTrapSet p hUpin.bare.trap
  have hreg : TravelingWaveRegularity p c U (frozenElliptic p U) :=
    hprofile.travelingWaveRegularity_of_green_step haM s.hlam htrapM hU2 hV2
  exact ⟨U, hprofile, hreg, hupper, hUpin.bare.deriv_nonpos,
    frozenElliptic_deriv_nonpos_of_monotone_trap
      p (kappa c) 1 U hUpin.bare, htail⟩

section AxiomAudit

#print axioms paper1_negativeConstruction_selfStep_reg

end AxiomAudit

end

end ShenWork.Paper1
