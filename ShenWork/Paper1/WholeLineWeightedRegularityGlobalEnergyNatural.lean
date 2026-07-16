import ShenWork.Paper1.WholeLineWeightedRegularityEnergyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalH0

open Filter Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Global transport of the natural weighted-energy inequality

Every positive time of the glued Cauchy solution lies in the interior of a
preferred canonical segment.  The segment is spatially translated by the
accumulated wave phase before applying the local energy theorem.  This makes
its moving-frame energy exactly equal to the global moving-frame energy.
-/

/-- Near a positive global time, the moving-frame global orbit is the
phase-normalized preferred segment with its local time shifted by the segment
base time. -/
theorem wholeLineCauchyGlobal_coMoving_eventuallyEq_preferredTranslated
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {c t : ℝ} (ht : 0 < t) :
    let a := (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
      wholeLineCauchyGlobalStep p u₀
    let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
    let u : ℝ → ℝ → ℝ := fun q x =>
      (wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj q).1 x
    (fun s => coMovingPath c (wholeLineCauchyGlobalU p u₀) s)
      =ᶠ[nhds t] fun s => coMovingPath c u (s - a) := by
  dsimp only
  let a := (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
    wholeLineCauchyGlobalStep p u₀
  let d := wholeLineCauchyGlobalPreferredSpatialShift p u₀ c t
  let Base := wholeLineCauchyGlobalSegment p u₀
    (wholeLineCauchyGlobalIndex p u₀ t)
  let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
  let u : ℝ → ℝ → ℝ := fun q x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj q).1 x
  filter_upwards [wholeLineCauchyGlobalBUC_eventuallyEq_preferred
      p hregime u₀ hu₀ ht] with s hs
  funext x
  have hsx := congrArg (fun w : WholeLineBUC => w.1 (x + c * s)) hs
  change wholeLineCauchyGlobalU p u₀ s (x + c * s) =
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj (s - a)).1
      (x + c * (s - a))
  rw [show Traj = wholeLineBUCTrajectorySpatialTranslate
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le d Base by
    simpa only [Traj, d, Base] using
      wholeLineCauchyGlobalPreferredTranslatedSegment_eq p u₀ c t]
  rw [wholeLineBUCTrajectoryExtend_spatialTranslate]
  simp only [wholeLineBUCTranslate_apply]
  change wholeLineCauchyGlobalU p u₀ s (x + c * s) =
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Base (s - a)).1
      (x + c * (s - a) + d)
  have hd : d = c * a := by
    simp only [d, a, wholeLineCauchyGlobalPreferredSpatialShift]
  rw [hd, show x + c * (s - a) + c * a = x + c * s by ring]
  simpa only [wholeLineCauchyGlobalU, Base, a] using hsx

/-- Scalar weighted energies agree on the same preferred global chart. -/
theorem wholeLineCauchyGlobal_weightedEnergy_eventuallyEq_preferredTranslated
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {eta c t : ℝ} {U : ℝ → ℝ} (ht : 0 < t) :
    let a := (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
      wholeLineCauchyGlobalStep p u₀
    let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
    let u : ℝ → ℝ → ℝ := fun q x =>
      (wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj q).1 x
    (paper5WeightedEnergy eta c (wholeLineCauchyGlobalU p u₀) U)
      =ᶠ[nhds t] fun s => paper5WeightedEnergy eta c u U (s - a) := by
  dsimp only
  let a := (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
    wholeLineCauchyGlobalStep p u₀
  let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
  let u : ℝ → ℝ → ℝ := fun q x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj q).1 x
  have hco := wholeLineCauchyGlobal_coMoving_eventuallyEq_preferredTranslated
    p hregime u₀ hu₀ (c := c) ht
  dsimp only at hco
  filter_upwards [hco] with s hs
  unfold paper5WeightedEnergy paper5WeightedHalfEnergy
    ShenWork.PaperOne.wholeLineHalfEnergy paper5WeightedPopulation
  rw [hs]

/-- The derivative of the global energy at a positive time is the derivative
of its phase-normalized preferred segment at the preferred local time. -/
theorem wholeLineCauchyGlobal_weightedEnergy_deriv_eq_preferredTranslated
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {eta c t : ℝ} {U : ℝ → ℝ} (ht : 0 < t) :
    let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
    let u : ℝ → ℝ → ℝ := fun q x =>
      (wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj q).1 x
    deriv (paper5WeightedEnergy eta c (wholeLineCauchyGlobalU p u₀) U) t =
      deriv (paper5WeightedEnergy eta c u U)
        (wholeLineCauchyGlobalLocalTime p u₀ t) := by
  dsimp only
  let a := (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
    wholeLineCauchyGlobalStep p u₀
  let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
  let u : ℝ → ℝ → ℝ := fun q x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj q).1 x
  have hE :=
    wholeLineCauchyGlobal_weightedEnergy_eventuallyEq_preferredTranslated
      p hregime u₀ hu₀ (eta := eta) (c := c) (U := U) ht
  dsimp only at hE
  rw [Filter.EventuallyEq.deriv_eq hE, deriv_comp_sub_const]
  rfl

/-- Strictly negative sensitivity gives the global positive-time energy
inequality at any common bound valid on the target slice.  The canonical
construction clamp is used only for local existence and regularity; it does
not enter the corrected quadratic. -/
theorem
    wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_natural
    (p : CMParams) (hchi : p.χ < 0)
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
        (ne_of_lt hchi) hc hTW hbound hreg hMChi₀ hMChi htargetLocal
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

#print axioms wholeLineCauchyGlobal_coMoving_eventuallyEq_preferredTranslated
#print axioms
  wholeLineCauchyGlobal_weightedEnergy_eventuallyEq_preferredTranslated
#print axioms
  wholeLineCauchyGlobal_weightedEnergy_deriv_eq_preferredTranslated
#print axioms
  wholeLineCauchyGlobal_weightedEnergy_deriv_le_common_of_target_bound_natural

end AxiomAudit

end ShenWork.Paper1
