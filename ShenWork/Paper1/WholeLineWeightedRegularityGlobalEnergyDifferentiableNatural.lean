import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyNatural

open Filter Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time differentiability of the natural global weighted energy

The scalar differential inequality is useful only together with an actual
energy derivative.  The canonical natural regularity producer supplies a
derivative of the half-energy on each positive local segment; this file
records the corresponding differentiability and transports it through the
phase-normalized preferred global chart.
-/

/-- The natural regularity capstone makes the full local weighted energy
differentiable at every strictly positive interior time. -/
theorem
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_differentiableAt_natural
    (p : CMParams)
    {M T t Blog eta c D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht0 : 0 < t) (htT : t < T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta)
    (heta_one : eta < 1) (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hMChi : MChi p ≤ M)
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
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀.1 y - U y| ^ 2)) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    DifferentiableAt ℝ (paper5WeightedEnergy eta c u U) t := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  obtain ⟨_hu2, hhalf, _hdiff, _hWx2⟩ :=
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_regularInputs_natural
      p hM hT ht0 htT hBlog heta heta_one hetaCap u₀ hsmall hstrip
        hchi hc hTW hbound hreg hMChi hlog hD hFD hB hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
        hdata_full
  have henergy : HasDerivAt (paper5WeightedEnergy eta c u U)
      (2 * ∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
    simpa only [paper5WeightedEnergy] using hhalf.const_mul 2
  exact henergy.differentiableAt

/-- The canonical global weighted energy is differentiable at every strictly
positive time.  The proof uses the phase-normalized preferred segment, so no
spurious exponential phase factor appears. -/
theorem wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_natural
    (p : CMParams) (hchi : p.χ < 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c t D E Kflux FD B : ℝ}
    (ht : 0 < t) (hBlog : 0 ≤ Blog)
    (heta : 0 < eta) (heta_one : eta < 1)
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
    DifferentiableAt ℝ (paper5WeightedEnergy eta c
      (wholeLineCauchyGlobalU p u₀) U) t := by
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
  have hchi_le : p.χ ≤ 0 := hchi.le
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi_le
  have hM₀ : 0 ≤ M₀ := (wholeLineCauchyGlobalClamp_pos p u₀).le
  have hH : 0 ≤ H := (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
  have hq0 : 0 < q := by
    simpa only [q] using wholeLineCauchyGlobalLocalTime_pos p u₀ ht
  have hqH : q < H := by
    simpa only [q, H] using
      wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le
  have hMChi₀ : MChi p ≤ M₀ := by
    rw [MChi_eq_one_of_chi_nonpos p hchi_le]
    have hstable : 1 ≤ wholeLineCauchyStableCeiling p u₀ :=
      wholeLineCauchyStableCeiling_one_le hregime u₀
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
  have hdata : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |datum.1 x - U x| ^ 2) := by
    simpa only [datum] using
      wholeLineCauchyGlobalPreferredTranslatedDatum_fullWeightedL2_integrable_wave
        p u₀ (t := t) heta heta_one hTW hbound hreg hMChi₀ hD hFD hB
        hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
        hreact_cont hgrad_int
        (by simpa only [WeightedL2InitialCloseness] using hinitial)
  have hlocal : DifferentiableAt ℝ
      (paper5WeightedEnergy eta c u U) q := by
    simpa only [u, Traj, M₀, H, q, datum] using
      (wholeLineCauchyBUCMildFixedPoint_weightedEnergy_differentiableAt_natural
        p hM₀ hH hq0 hqH hBlog heta heta_one hetaCap datum
          (wholeLineCauchyGlobalSegmentTime_rate p u₀) hstrip
          (ne_of_lt hchi) hc hTW hbound hreg hMChi₀ hlog hD hFD hB
          hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
          hreact_cont hgrad_int hdata)
  have hshift : DifferentiableAt ℝ
      (fun s => paper5WeightedEnergy eta c u U (s - a)) t := by
    have hcomp := hlocal.comp t (differentiableAt_id.sub_const a)
    simpa only [q, wholeLineCauchyGlobalLocalTime, a] using hcomp
  have henergy :=
    wholeLineCauchyGlobal_weightedEnergy_eventuallyEq_preferredTranslated
      p hregime u₀ hu₀ (eta := eta) (c := c) (U := U) ht
  dsimp only at henergy
  exact henergy.differentiableAt_iff.mpr hshift

section AxiomAudit

#print axioms
  wholeLineCauchyBUCMildFixedPoint_weightedEnergy_differentiableAt_natural
#print axioms
  wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_natural

end AxiomAudit

end ShenWork.Paper1
