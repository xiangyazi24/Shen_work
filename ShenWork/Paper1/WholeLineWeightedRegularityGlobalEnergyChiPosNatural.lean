import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyNatural

open Filter Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# χ>0 global energy inequality via StableWaveParameterRegime

Mirror of `wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_natural`
for positive sensitivity χ>0.  The three χ<0–specific ingredients are replaced:

1. Ceiling regime: `StableWaveParameterRegime.toWholeLineCauchyCeilingRegime`
2. MChi ≤ clamp: critical-case `parameterCeiling = MChi` via α = m+γ-1
3. χ ≠ 0 witness: `ne_of_gt` instead of `ne_of_lt`
-/

theorem
    wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_chi_pos_natural
    (p : CMParams) (hstable : StableWaveParameterRegime p) (hchi_pos : 0 < p.χ)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {M Blog eta c t D E Kflux FD B : ℝ}
    (ht : 0 < t) (hMChi : MChi p ≤ M)
    (htarget : ∀ x, wholeLineCauchyGlobalU p u₀ t x ≤ M)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (hetaCap : eta < stabilityWeightCap p)
    {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hlog : ∀ y, |deriv U y / U y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    deriv (paper5WeightedEnergy eta c
      (wholeLineCauchyGlobalU p u₀) U) t ≤
      2 * paper531Quadratic c (paper531CommonA p M)
        (paper531CommonB p M) eta *
        paper5WeightedEnergy eta c (wholeLineCauchyGlobalU p u₀) U t := by
  let M₀ := wholeLineCauchyGlobalClamp p u₀
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let a := (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
    wholeLineCauchyGlobalStep p u₀
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let d := wholeLineCauchyGlobalPreferredSpatialShift p u₀ c t
  let Base := wholeLineCauchyGlobalSegment p u₀
    (wholeLineCauchyGlobalIndex p u₀ t)
  let datum := wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t
  let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 x
  have hregime : WholeLineCauchyCeilingRegime p :=
    hstable.toWholeLineCauchyCeilingRegime
  have hM₀ : 0 ≤ M₀ := (wholeLineCauchyGlobalClamp_pos p u₀).le
  have hH : 0 ≤ H := (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
  have hq0 : 0 < q := by
    simpa only [q] using wholeLineCauchyGlobalLocalTime_pos p u₀ ht
  have hqH : q < H := by
    simpa only [q, H] using
      wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le
  have hMChi₀ : MChi p ≤ M₀ := by
    have hbranch := hstable.positive_branch_of_chi_nonneg hchi_pos.le
    have hparam : wholeLineCauchyParameterCeiling p = MChi p := by
      unfold wholeLineCauchyParameterCeiling
      rw [if_neg (not_lt.mpr (le_of_eq hbranch.2))]
    have hle : MChi p ≤ wholeLineCauchyStableCeiling p u₀ := by
      rw [← hparam]
      exact le_max_right _ _
    unfold M₀ wholeLineCauchyGlobalClamp
    linarith
  have hstrip : ∀ z : Set.Icc (0 : ℝ) H, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM₀ hH datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) z).1 x ∈
          Set.Icc (0 : ℝ) M₀ := by
    intro z x
    have hbase :=
      (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀
        (wholeLineCauchyGlobalIndex p u₀ t)).2.1 z (x + d)
    change (Traj z).1 x ∈ Set.Icc (0 : ℝ) M₀
    rw [show Traj = wholeLineBUCTrajectorySpatialTranslate hH d Base by
      simpa only [Traj, d, Base, hH] using
        wholeLineCauchyGlobalPreferredTranslatedSegment_eq p u₀ c t]
    simpa only [wholeLineBUCTrajectorySpatialTranslate_apply,
      M₀, H, d, Base] using hbase
  have htargetLocal : ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM₀ hH datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        ⟨q, hq0.le, hqH.le⟩).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro x
    let zq : Set.Icc (0 : ℝ) H := ⟨q, hq0.le, hqH.le⟩
    have hext : wholeLineBUCTrajectoryExtend hH Traj q = Traj zq :=
      wholeLineBUCTrajectoryExtend_eq hH Traj zq.2
    have hco := congrFun
      (wholeLineCauchyGlobal_coMoving_eq_preferredTranslatedSegment
        p u₀ (c := c) ht) (x - c * q)
    have hnonneg := wholeLineCauchyGlobal_nonnegative
      p hregime u₀ hu₀ ht.le (x - c * q + c * t)
    have hupper := htarget (x - c * q + c * t)
    change (Traj zq).1 x ∈ Set.Icc (0 : ℝ) M
    have heq : (Traj zq).1 x =
        wholeLineCauchyGlobalU p u₀ t (x - c * q + c * t) := by
      calc
        (Traj zq).1 x =
            (wholeLineBUCTrajectoryExtend hH Traj q).1 x := by
          rw [hext]
        _ = wholeLineCauchyGlobalU p u₀ t
              (x - c * q + c * t) := by
          simpa only [coMovingPath, sub_add_cancel, H, Traj, q] using hco.symm
    rw [heq]
    exact ⟨hnonneg, hupper⟩
  have hdata : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |datum.1 x - U x| ^ 2) := by
    simpa only [datum] using
      wholeLineCauchyGlobalPreferredTranslatedDatum_fullWeightedL2_integrable_wave
        p u₀ (t := t) heta heta_one hTW hbound hreg hMChi₀ hD hFD hB
        hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
        hreact_cont hgrad_int
        (by simpa only [WeightedL2InitialCloseness] using hinitial)
  have hlocal :=
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_common_of_target_bound_natural
      p hM₀ hH hq0 hqH hBlog heta heta_one hetaCap datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) hstrip
        (ne_of_gt hchi_pos) hc hTW hbound hreg hMChi₀ hMChi htargetLocal
        hlog hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has
        hfluxd_cont hreact hreact_cont hgrad_int hdata
  dsimp only at hlocal
  have hderiv :=
    wholeLineCauchyGlobal_weightedEnergy_deriv_eq_preferredTranslated
      p hregime u₀ hu₀ (eta := eta) (c := c) (U := U) ht
  dsimp only at hderiv
  have henergy :=
    (wholeLineCauchyGlobal_weightedEnergy_eventuallyEq_preferredTranslated
      p hregime u₀ hu₀ (eta := eta) (c := c) (U := U) ht).eq_of_nhds
  have henergy' : paper5WeightedEnergy eta c u U q =
      paper5WeightedEnergy eta c (wholeLineCauchyGlobalU p u₀) U t := by
    simpa only [u, Traj, q, wholeLineCauchyGlobalLocalTime, a] using
      henergy.symm
  rw [hderiv]
  calc
    deriv (paper5WeightedEnergy eta c u U) q ≤
        2 * paper531Quadratic c (paper531CommonA p M)
          (paper531CommonB p M) eta * paper5WeightedEnergy eta c u U q := by
      simpa only [u, Traj, M₀, H, q, datum] using hlocal
    _ = 2 * paper531Quadratic c (paper531CommonA p M)
          (paper531CommonB p M) eta *
          paper5WeightedEnergy eta c (wholeLineCauchyGlobalU p u₀) U t := by
      rw [henergy']

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_chi_pos_natural

end AxiomAudit

end ShenWork.Paper1
