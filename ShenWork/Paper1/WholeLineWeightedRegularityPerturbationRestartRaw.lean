import ShenWork.Paper1.WholeLineWeightedRegularityPerturbationRestartDQ
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQIdentity

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

theorem rawSpatialDifferenceQuotient_intervalIntegral
    {a b eta d x : ℝ} {F : ℝ → ℝ → ℝ}
    (hFx : IntervalIntegrable (fun s => F s x) volume a b)
    (hFxd : IntervalIntegrable (fun s => F s (x + d)) volume a b) :
    rawSpatialDifferenceQuotient eta d
        (fun y => ∫ s in a..b, F s y) x =
      ∫ s in a..b, rawSpatialDifferenceQuotient eta d (F s) x := by
  unfold rawSpatialDifferenceQuotient
  rw [spatialDifferenceQuotient_intervalIntegral hFx hFxd]
  rw [← intervalIntegral.integral_const_mul]
  have hDQ : IntervalIntegrable
      (fun s => spatialDifferenceQuotient d (F s) x) volume a b := by
    simpa only [spatialDifferenceQuotient] using (hFxd.sub hFx).div_const d
  rw [intervalIntegral.integral_add (hFx.const_mul eta) hDQ]

theorem paper5MovingFrameHeatOp_raw_eq_eta_add_spatialDQ_buc
    {q : ℝ} (hq : 0 < q) (eta c d : ℝ)
    (u : WholeLineBUC) (x : ℝ) :
    paper5MovingFrameHeatOp c q
        (rawSpatialDifferenceQuotient eta d u.1) x =
      eta * paper5MovingFrameHeatOp c q u.1 x +
        paper5MovingFrameHeatOp c q
          (spatialDifferenceQuotient d u.1) x := by
  have hraw := rawSpatialDifferenceQuotient_movingFrameHeatOp
    hq c d eta u x
  have hdq := spatialDifferenceQuotient_paper5MovingFrameHeatOp
    hq c d u x
  unfold rawSpatialDifferenceQuotient at hraw
  rw [hdq] at hraw
  exact hraw.symm

theorem paper5MovingFrameHeatGradOp_raw_eq_eta_add_spatialDQ_buc
    {q : ℝ} (hq : 0 < q) (eta c d : ℝ)
    (u : WholeLineBUC) (x : ℝ) :
    paper5MovingFrameHeatGradOp c q
        (rawSpatialDifferenceQuotient eta d u.1) x =
      eta * paper5MovingFrameHeatGradOp c q u.1 x +
        paper5MovingFrameHeatGradOp c q
          (spatialDifferenceQuotient d u.1) x := by
  have hraw := rawSpatialDifferenceQuotient_movingFrameHeatGradOp
    hq c d eta u x
  have hdq := spatialDifferenceQuotient_paper5MovingFrameHeatGradOp
    hq c d u x
  unfold rawSpatialDifferenceQuotient at hraw
  rw [hdq] at hraw
  exact hraw.symm

/-- Undifferentiated matched perturbation restart.  This is the value half
combined with the spatial-DQ identity in the conjugated raw restart below. -/
theorem wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_identity
    (p : CMParams) {M T a q c x D E F FD R : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ha : 0 < a) (hq : 0 < q) (haq : a + q ≤ T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int_x : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hq.le).trans haq⟩
    let zaq : Set.Icc (0 : ℝ) T :=
      ⟨a + q, (add_pos ha hq).le, haq⟩
    let us : ℝ → ℝ → ℝ := fun s y =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s)
    (Traj zaq).1 (x + c * (a + q)) - Uw x =
      paper5MovingFrameHeatOp c q
        (fun y => (Traj za).1 (y + c * a) - Uw y) x +
      (-p.χ) * (∫ s in a..(a + q),
        paper5MovingFrameHeatGradOp c (a + q - s)
          (fun y => wholeLineChemotaxisFlux p (us s) y -
            wholeLineChemotaxisFlux p Uw y) x) +
      ∫ s in a..(a + q),
        paper5MovingFrameHeatOp c (a + q - s)
          (fun y => wholeLineCauchyShiftedReaction p (us s) y -
            wholeLineCauchyShiftedReaction p Uw y) x := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hq.le).trans haq⟩
  let zaq : Set.Icc (0 : ℝ) T :=
    ⟨a + q, (add_pos ha hq).le, haq⟩
  let us : ℝ → ℝ → ℝ := fun s y =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s)
  let Fw : ℝ → ℝ := wholeLineChemotaxisFlux p Uw
  let Rw : ℝ → ℝ := wholeLineCauchyShiftedReaction p Uw
  let Fc : ℝ → ℝ → ℝ := fun s => wholeLineChemotaxisFlux p (us s)
  let Rc : ℝ → ℝ → ℝ := fun s => wholeLineCauchyShiftedReaction p (us s)
  let Hc : ℝ := paper5MovingFrameHeatOp c q
    (fun y => (Traj za).1 (y + c * a)) x
  let Hw : ℝ := paper5MovingFrameHeatOp c q Uw x
  let Gc : ℝ → ℝ := fun s => paper5MovingFrameHeatGradOp c (a + q - s)
    (Fc s) x
  let Gw : ℝ → ℝ := fun s => paper5MovingFrameHeatGradOp c (a + q - s)
    Fw x
  let Qc : ℝ → ℝ := fun s => paper5MovingFrameHeatOp c (a + q - s)
    (Rc s) x
  let Qw : ℝ → ℝ := fun s => paper5MovingFrameHeatOp c (a + q - s)
    Rw x
  have hcan := wholeLineCauchyBUCMildFixedPoint_coMoving_restart_identity
    p hM hT u₀ hsmall ha hq haq hstrip (c := c) (x := x)
  dsimp only at hcan
  have hCF (s : ℝ) :
      wholeLineCauchyCoMovingFluxSource p c hM hT Traj s = Fc s := by
    simpa only [Fc, us] using
      wholeLineCauchyCoMovingFluxSource_eq_genuineFlux_of_strip
        p c hM hT Traj hstrip s
  have hCR (s : ℝ) :
      wholeLineCauchyCoMovingReactionSource p c hM hT Traj s = Rc s := by
    simpa only [Rc, us] using
      wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
        p c hM hT Traj hstrip s
  dsimp only [Traj] at hCF hCR
  simp_rw [hCF, hCR] at hcan
  have hwave := IsTravelingWave.stationary_divergence_mild_identity_on_window
    p hTW hbound hreg hq hD hFD hR hUd hUdd hUddcont
      hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
      hgrad_int_x (a := a) (x := x)
  have hFwEq : wholeLineTravelingWaveFlux p Uw Vw = Fw := by
    simpa only [Fw] using
      IsTravelingWave.wholeLineTravelingWaveFlux_eq_chemotaxisFlux
        p hTW hbound hreg
  rw [hFwEq] at hwave
  change (Traj zaq).1 (x + c * (a + q)) =
    Hc + (-p.χ) * (∫ s in a..(a + q), Gc s) +
      ∫ s in a..(a + q), Qc s at hcan
  change Uw x = Hw + (-p.χ) * (∫ s in a..(a + q), Gw s) +
      ∫ s in a..(a + q), Qw s at hwave
  let UaBUC : WholeLineBUC := wholeLineBUCTranslate (c * a) (Traj za)
  have hUwBound : ∀ y, |Uw y| ≤ MChi p := by
    intro y
    rw [abs_of_pos (hbound.pos y)]
    exact hbound.le_MChi y
  let UwBUC : WholeLineBUC := wholeLineBUCOfUniformBound Uw
    (travelingWave_U_uniformContinuous hTW hreg.U_cont) (MChi p) hUwBound
  have hHsub : paper5MovingFrameHeatOp c q
      (fun y => (Traj za).1 (y + c * a) - Uw y) x = Hc - Hw := by
    simpa only [UaBUC, UwBUC, Hc, Hw,
      wholeLineBUCTranslate_apply, wholeLineBUCOfUniformBound_apply] using
      paper5MovingFrameHeatOp_sub_buc hq c UaBUC UwBUC x
  let FcBUC : ℝ → WholeLineBUC := fun s =>
    wholeLineCauchyCoMovingFluxSourceBUC p c hM hT Traj s
  have hFcBUCFun (s : ℝ) : (FcBUC s : ℝ → ℝ) = Fc s := by
    funext y
    change wholeLineCauchyCoMovingFluxSource p c hM hT Traj s y = Fc s y
    exact congrFun (hCF s) y
  have hFwDiff : Differentiable ℝ Fw := by
    intro y
    rw [← hFwEq]
    exact (hflux_has y).differentiableAt
  have hFwNN : ∀ y, ‖deriv Fw y‖₊ ≤ ⟨FD, hFD⟩ := by
    intro y
    apply NNReal.coe_le_coe.mp
    rw [← hFwEq]
    simpa [Real.norm_eq_abs] using hfluxd y
  have hFwUC : UniformContinuous Fw :=
    (lipschitzWith_of_nnnorm_deriv_le hFwDiff hFwNN).uniformContinuous
  let FwBUC : WholeLineBUC := wholeLineBUCOfUniformBound Fw hFwUC F (by
    intro y
    rw [← hFwEq]
    exact hflux y)
  have hGc_int : IntervalIntegrable Gc volume a (a + q) := by
    have hbase := wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
      p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj x (c := c)
    apply hbase.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [hCF s]
  have hGw_int : IntervalIntegrable Gw volume a (a + q) := by
    have hbase : IntervalIntegrable (fun r =>
        paper5MovingFrameHeatGradOp c r Fw x) volume 0 q := by
      simpa only [← hFwEq] using hgrad_int_x
    have hcomp := (hbase.comp_sub_left (a + q)).symm
    convert hcomp using 1 <;> ring
  have hGsub :
      (∫ s in a..(a + q), paper5MovingFrameHeatGradOp c (a + q - s)
        (fun y => Fc s y - Fw y) x) =
        (∫ s in a..(a + q), Gc s) - ∫ s in a..(a + q), Gw s := by
    calc
      _ = ∫ s in a..(a + q), Gc s - Gw s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume (a + q)] with s hne hs
        rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
        have hlag : 0 < a + q - s := sub_pos.mpr
          (lt_of_le_of_ne hs.2 hne)
        have hsub := paper5MovingFrameHeatGradOp_sub_buc
          hlag c (FcBUC s) FwBUC x
        rw [hFcBUCFun s] at hsub
        simpa only [Gc, Gw, FwBUC,
          wholeLineBUCOfUniformBound_apply] using hsub
      _ = _ := intervalIntegral.integral_sub hGc_int hGw_int
  let RcBUC : ℝ → WholeLineBUC := fun s =>
    wholeLineCauchyCoMovingReactionSourceBUC p c hM hT Traj s
  have hRcBUCFun (s : ℝ) : (RcBUC s : ℝ → ℝ) = Rc s := by
    funext y
    change wholeLineCauchyCoMovingReactionSource p c hM hT Traj s y = Rc s y
    exact congrFun (hCR s) y
  have hMw : 0 ≤ MChi p :=
    (hbound.pos 0).le.trans (hbound.le_MChi 0)
  have hUwMem : ∀ y, Uw y ∈ Set.Icc (0 : ℝ) (MChi p) := fun y =>
    ⟨(hbound.pos y).le, hbound.le_MChi y⟩
  let RwBUC : WholeLineBUC :=
    wholeLineCauchyTruncatedReactionBUC p (MChi p) hMw UwBUC
  have hRwBUC (y : ℝ) : (RwBUC : ℝ → ℝ) y = Rw y := by
    change wholeLineCauchyTruncatedReaction p (MChi p) Uw y = Rw y
    rw [wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hMw hUwMem]
  have hQc_int : IntervalIntegrable Qc volume a (a + q) := by
    have hbase := wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
      p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj x (c := c)
    apply hbase.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [hCR s]
  have hQw_int : IntervalIntegrable Qw volume a (a + q) := by
    have hbase : IntervalIntegrable (fun r =>
        paper5MovingFrameHeatOp c r Rw x) volume 0 q := by
      simpa only [Rw] using wholeLineCauchyMovingHeatOp_intervalIntegrable
        hq hR hreact_cont hreact (x := x)
    have hcomp := (hbase.comp_sub_left (a + q)).symm
    convert hcomp using 1 <;> ring
  have hRsub :
      (∫ s in a..(a + q), paper5MovingFrameHeatOp c (a + q - s)
        (fun y => Rc s y - Rw y) x) =
        (∫ s in a..(a + q), Qc s) - ∫ s in a..(a + q), Qw s := by
    calc
      _ = ∫ s in a..(a + q), Qc s - Qw s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume (a + q)] with s hne hs
        rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
        have hlag : 0 < a + q - s := sub_pos.mpr
          (lt_of_le_of_ne hs.2 hne)
        have hsub := paper5MovingFrameHeatOp_sub_buc
          hlag c (RcBUC s) RwBUC x
        rw [hRcBUCFun s] at hsub
        have hRwFun : (RwBUC : ℝ → ℝ) = Rw := funext hRwBUC
        rw [hRwFun] at hsub
        simpa only [Qc, Qw] using hsub
      _ = _ := intervalIntegral.integral_sub hQc_int hQw_int
  calc
    (Traj zaq).1 (x + c * (a + q)) - Uw x =
        (Hc + (-p.χ) * (∫ s in a..(a + q), Gc s) +
          ∫ s in a..(a + q), Qc s) -
        (Hw + (-p.χ) * (∫ s in a..(a + q), Gw s) +
          ∫ s in a..(a + q), Qw s) := by rw [hcan, hwave]
    _ = (Hc - Hw) +
        (-p.χ) * ((∫ s in a..(a + q), Gc s) -
          ∫ s in a..(a + q), Gw s) +
        ((∫ s in a..(a + q), Qc s) -
          ∫ s in a..(a + q), Qw s) := by ring
    _ = _ := by rw [← hHsub, ← hGsub, ← hRsub]

/-- Exact conjugated raw spatial-DQ restart for the matched co-moving
perturbation.  Both source legs use the named `rawSpatialDifferenceQuotient`
of the genuine nonlinear source difference. -/
theorem wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_rawSpatialDQ_identity
    (p : CMParams) {M T a q eta c d x D E F FD R : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ha : 0 < a) (hq : 0 < q) (haq : a + q ≤ T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int_x : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hgrad_int_xd : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) (x + d)) volume 0 q) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hq.le).trans haq⟩
    let zaq : Set.Icc (0 : ℝ) T :=
      ⟨a + q, (add_pos ha hq).le, haq⟩
    let us : ℝ → ℝ → ℝ := fun s y =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s)
    rawSpatialDifferenceQuotient eta d
        (fun y => (Traj zaq).1 (y + c * (a + q)) - Uw y) x =
      paper5MovingFrameHeatOp c q
        (rawSpatialDifferenceQuotient eta d
          (fun y => (Traj za).1 (y + c * a) - Uw y)) x +
      (-p.χ) * (∫ s in a..(a + q),
        paper5MovingFrameHeatGradOp c (a + q - s)
          (rawSpatialDifferenceQuotient eta d (fun y =>
            wholeLineChemotaxisFlux p (us s) y -
              wholeLineChemotaxisFlux p Uw y)) x) +
      ∫ s in a..(a + q),
        paper5MovingFrameHeatOp c (a + q - s)
          (rawSpatialDifferenceQuotient eta d (fun y =>
            wholeLineCauchyShiftedReaction p (us s) y -
              wholeLineCauchyShiftedReaction p Uw y)) x := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hq.le).trans haq⟩
  let zaq : Set.Icc (0 : ℝ) T :=
    ⟨a + q, (add_pos ha hq).le, haq⟩
  let us : ℝ → ℝ → ℝ := fun s y =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s)
  let W₀ : ℝ → ℝ := fun y => (Traj za).1 (y + c * a) - Uw y
  let W₁ : ℝ → ℝ := fun y => (Traj zaq).1 (y + c * (a + q)) - Uw y
  let Fw : ℝ → ℝ := wholeLineChemotaxisFlux p Uw
  let Rw : ℝ → ℝ := wholeLineCauchyShiftedReaction p Uw
  let Fc : ℝ → ℝ → ℝ := fun s => wholeLineChemotaxisFlux p (us s)
  let Rc : ℝ → ℝ → ℝ := fun s => wholeLineCauchyShiftedReaction p (us s)
  let G : ℝ → ℝ → ℝ := fun s y => Fc s y - Fw y
  let Q : ℝ → ℝ → ℝ := fun s y => Rc s y - Rw y
  let HV : ℝ := paper5MovingFrameHeatOp c q W₀ x
  let HD : ℝ := paper5MovingFrameHeatOp c q
    (spatialDifferenceQuotient d W₀) x
  let GV : ℝ → ℝ := fun s => paper5MovingFrameHeatGradOp c (a + q - s)
    (G s) x
  let GD : ℝ → ℝ := fun s => paper5MovingFrameHeatGradOp c (a + q - s)
    (spatialDifferenceQuotient d (G s)) x
  let RV : ℝ → ℝ := fun s => paper5MovingFrameHeatOp c (a + q - s)
    (Q s) x
  let RD : ℝ → ℝ := fun s => paper5MovingFrameHeatOp c (a + q - s)
    (spatialDifferenceQuotient d (Q s)) x
  have hval :=
    wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_identity
      p hM hT u₀ hsmall ha hq haq hstrip hTW hbound hreg
      hD hFD hR hUd hUdd hUddcont hflux hfluxd hflux_has
      hfluxd_cont hreact hreact_cont hgrad_int_x (x := x)
  dsimp only at hval
  change W₁ x = HV + (-p.χ) * (∫ s in a..(a + q), GV s) +
    ∫ s in a..(a + q), RV s at hval
  have hdq :=
    wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_spatialDQ_identity
      p hM hT u₀ hsmall ha hq haq hstrip hTW hbound hreg
      hD hFD hR hUd hUdd hUddcont hflux hfluxd hflux_has
      hfluxd_cont hreact hreact_cont hgrad_int_x hgrad_int_xd
      (c := c) (d := d) (x := x)
  dsimp only at hdq
  change spatialDifferenceQuotient d W₁ x =
    HD + (-p.χ) * (∫ s in a..(a + q), GD s) +
      ∫ s in a..(a + q), RD s at hdq
  let UaBUC : WholeLineBUC := wholeLineBUCTranslate (c * a) (Traj za)
  have hUwBound : ∀ y, |Uw y| ≤ MChi p := by
    intro y
    rw [abs_of_pos (hbound.pos y)]
    exact hbound.le_MChi y
  let UwBUC : WholeLineBUC := wholeLineBUCOfUniformBound Uw
    (travelingWave_U_uniformContinuous hTW hreg.U_cont) (MChi p) hUwBound
  let W₀BUC : WholeLineBUC := UaBUC - UwBUC
  have hW₀BUC : (W₀BUC : ℝ → ℝ) = W₀ := by
    funext y
    rfl
  have hHraw : paper5MovingFrameHeatOp c q
      (rawSpatialDifferenceQuotient eta d W₀) x = eta * HV + HD := by
    have hcore := paper5MovingFrameHeatOp_raw_eq_eta_add_spatialDQ_buc
      hq eta c d W₀BUC x
    rw [hW₀BUC] at hcore
    exact hcore
  have hCF (s : ℝ) :
      wholeLineCauchyCoMovingFluxSource p c hM hT Traj s = Fc s := by
    simpa only [Fc, us] using
      wholeLineCauchyCoMovingFluxSource_eq_genuineFlux_of_strip
        p c hM hT Traj hstrip s
  have hCR (s : ℝ) :
      wholeLineCauchyCoMovingReactionSource p c hM hT Traj s = Rc s := by
    simpa only [Rc, us] using
      wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
        p c hM hT Traj hstrip s
  dsimp only [Traj] at hCF hCR
  let FcBUC : ℝ → WholeLineBUC := fun s =>
    wholeLineCauchyCoMovingFluxSourceBUC p c hM hT Traj s
  have hFcBUCFun (s : ℝ) : (FcBUC s : ℝ → ℝ) = Fc s := by
    funext y
    change wholeLineCauchyCoMovingFluxSource p c hM hT Traj s y = Fc s y
    exact congrFun (hCF s) y
  have hFwEq : wholeLineTravelingWaveFlux p Uw Vw = Fw := by
    simpa only [Fw] using
      IsTravelingWave.wholeLineTravelingWaveFlux_eq_chemotaxisFlux
        p hTW hbound hreg
  have hFwDiff : Differentiable ℝ Fw := by
    intro y
    rw [← hFwEq]
    exact (hflux_has y).differentiableAt
  have hFwNN : ∀ y, ‖deriv Fw y‖₊ ≤ ⟨FD, hFD⟩ := by
    intro y
    apply NNReal.coe_le_coe.mp
    rw [← hFwEq]
    simpa [Real.norm_eq_abs] using hfluxd y
  have hFwUC : UniformContinuous Fw :=
    (lipschitzWith_of_nnnorm_deriv_le hFwDiff hFwNN).uniformContinuous
  let FwBUC : WholeLineBUC := wholeLineBUCOfUniformBound Fw hFwUC F (by
    intro y
    rw [← hFwEq]
    exact hflux y)
  let GBUC : ℝ → WholeLineBUC := fun s => FcBUC s - FwBUC
  have hGBUCFun (s : ℝ) : (GBUC s : ℝ → ℝ) = G s := by
    funext y
    change (FcBUC s).1 y - FwBUC.1 y = Fc s y - Fw y
    rw [hFcBUCFun s]
    rfl
  have hGcx := wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
    p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj x (c := c)
  have hGcxd := wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
    p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj (x + d) (c := c)
  have hGwx0 : IntervalIntegrable (fun r =>
      paper5MovingFrameHeatGradOp c r Fw x) volume 0 q := by
    simpa only [← hFwEq] using hgrad_int_x
  have hGwxd0 : IntervalIntegrable (fun r =>
      paper5MovingFrameHeatGradOp c r Fw (x + d)) volume 0 q := by
    simpa only [← hFwEq] using hgrad_int_xd
  have hGwx : IntervalIntegrable (fun s =>
      paper5MovingFrameHeatGradOp c (a + q - s) Fw x) volume a (a + q) := by
    have hcomp := (hGwx0.comp_sub_left (a + q)).symm
    convert hcomp using 1 <;> ring
  have hGwxd : IntervalIntegrable (fun s =>
      paper5MovingFrameHeatGradOp c (a + q - s) Fw (x + d))
      volume a (a + q) := by
    have hcomp := (hGwxd0.comp_sub_left (a + q)).symm
    convert hcomp using 1 <;> ring
  have hGVx : IntervalIntegrable GV volume a (a + q) := by
    apply (hGcx.sub hGwx).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (a + q))] with s hs hne
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    have hsub := paper5MovingFrameHeatGradOp_sub_buc
      hlag c (FcBUC s) FwBUC x
    rw [hFcBUCFun s] at hsub
    rw [hCF s]
    simpa only [GV, G, FwBUC, wholeLineBUCOfUniformBound_apply] using hsub.symm
  have hGVxd : IntervalIntegrable (fun s =>
      paper5MovingFrameHeatGradOp c (a + q - s) (G s) (x + d))
      volume a (a + q) := by
    apply (hGcxd.sub hGwxd).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (a + q))] with s hs hne
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    have hsub := paper5MovingFrameHeatGradOp_sub_buc
      hlag c (FcBUC s) FwBUC (x + d)
    rw [hFcBUCFun s] at hsub
    rw [hCF s]
    simpa only [G, FwBUC, wholeLineBUCOfUniformBound_apply] using hsub.symm
  have hGDeval : IntervalIntegrable (fun s => spatialDifferenceQuotient d
      (fun y => paper5MovingFrameHeatGradOp c (a + q - s) (G s) y) x)
      volume a (a + q) := by
    simpa only [spatialDifferenceQuotient] using (hGVxd.sub hGVx).div_const d
  have hGDint : IntervalIntegrable GD volume a (a + q) := by
    apply hGDeval.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (a + q))] with s hs hne
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    have hcomm := spatialDifferenceQuotient_paper5MovingFrameHeatGradOp
      hlag c d (GBUC s) x
    rw [hGBUCFun s] at hcomm
    simpa only [GD] using hcomm
  have hGraw :
      (∫ s in a..(a + q), paper5MovingFrameHeatGradOp c (a + q - s)
        (rawSpatialDifferenceQuotient eta d (G s)) x) =
        eta * (∫ s in a..(a + q), GV s) +
          ∫ s in a..(a + q), GD s := by
    calc
      _ = ∫ s in a..(a + q), eta * GV s + GD s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume (a + q)] with s hne hs
        rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
        have hlag : 0 < a + q - s := sub_pos.mpr
          (lt_of_le_of_ne hs.2 hne)
        have hcore := paper5MovingFrameHeatGradOp_raw_eq_eta_add_spatialDQ_buc
          hlag eta c d (GBUC s) x
        rw [hGBUCFun s] at hcore
        simpa only [GV, GD] using hcore
      _ = _ := by
        rw [intervalIntegral.integral_add (hGVx.const_mul eta) hGDint,
          intervalIntegral.integral_const_mul]
  let RcBUC : ℝ → WholeLineBUC := fun s =>
    wholeLineCauchyCoMovingReactionSourceBUC p c hM hT Traj s
  have hRcBUCFun (s : ℝ) : (RcBUC s : ℝ → ℝ) = Rc s := by
    funext y
    change wholeLineCauchyCoMovingReactionSource p c hM hT Traj s y = Rc s y
    exact congrFun (hCR s) y
  have hMw : 0 ≤ MChi p :=
    (hbound.pos 0).le.trans (hbound.le_MChi 0)
  have hUwMem : ∀ y, Uw y ∈ Set.Icc (0 : ℝ) (MChi p) := fun y =>
    ⟨(hbound.pos y).le, hbound.le_MChi y⟩
  let RwBUC : WholeLineBUC :=
    wholeLineCauchyTruncatedReactionBUC p (MChi p) hMw UwBUC
  have hRwBUC (y : ℝ) : (RwBUC : ℝ → ℝ) y = Rw y := by
    change wholeLineCauchyTruncatedReaction p (MChi p) Uw y = Rw y
    rw [wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hMw hUwMem]
  let QBUC : ℝ → WholeLineBUC := fun s => RcBUC s - RwBUC
  have hQBUCFun (s : ℝ) : (QBUC s : ℝ → ℝ) = Q s := by
    funext y
    change (RcBUC s).1 y - RwBUC.1 y = Rc s y - Rw y
    rw [hRcBUCFun s, hRwBUC y]
  have hRcx := wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
    p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj x (c := c)
  have hRcxd := wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
    p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj (x + d) (c := c)
  have hRwx0 : IntervalIntegrable (fun r =>
      paper5MovingFrameHeatOp c r Rw x) volume 0 q := by
    simpa only [Rw] using wholeLineCauchyMovingHeatOp_intervalIntegrable
      hq hR hreact_cont hreact (x := x)
  have hRwxd0 : IntervalIntegrable (fun r =>
      paper5MovingFrameHeatOp c r Rw (x + d)) volume 0 q := by
    simpa only [Rw] using wholeLineCauchyMovingHeatOp_intervalIntegrable
      hq hR hreact_cont hreact (x := x + d)
  have hRwx : IntervalIntegrable (fun s =>
      paper5MovingFrameHeatOp c (a + q - s) Rw x) volume a (a + q) := by
    have hcomp := (hRwx0.comp_sub_left (a + q)).symm
    convert hcomp using 1 <;> ring
  have hRwxd : IntervalIntegrable (fun s =>
      paper5MovingFrameHeatOp c (a + q - s) Rw (x + d))
      volume a (a + q) := by
    have hcomp := (hRwxd0.comp_sub_left (a + q)).symm
    convert hcomp using 1 <;> ring
  have hRVx : IntervalIntegrable RV volume a (a + q) := by
    apply (hRcx.sub hRwx).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (a + q))] with s hs hne
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    have hsub := paper5MovingFrameHeatOp_sub_buc
      hlag c (RcBUC s) RwBUC x
    rw [hRcBUCFun s] at hsub
    have hRwFun : (RwBUC : ℝ → ℝ) = Rw := funext hRwBUC
    rw [hRwFun] at hsub
    rw [hCR s]
    simpa only [RV, Q] using hsub.symm
  have hRVxd : IntervalIntegrable (fun s =>
      paper5MovingFrameHeatOp c (a + q - s) (Q s) (x + d))
      volume a (a + q) := by
    apply (hRcxd.sub hRwxd).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (a + q))] with s hs hne
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    have hsub := paper5MovingFrameHeatOp_sub_buc
      hlag c (RcBUC s) RwBUC (x + d)
    rw [hRcBUCFun s] at hsub
    have hRwFun : (RwBUC : ℝ → ℝ) = Rw := funext hRwBUC
    rw [hRwFun] at hsub
    rw [hCR s]
    simpa only [Q] using hsub.symm
  have hRDeval : IntervalIntegrable (fun s => spatialDifferenceQuotient d
      (fun y => paper5MovingFrameHeatOp c (a + q - s) (Q s) y) x)
      volume a (a + q) := by
    simpa only [spatialDifferenceQuotient] using (hRVxd.sub hRVx).div_const d
  have hRDint : IntervalIntegrable RD volume a (a + q) := by
    apply hRDeval.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (a + q))] with s hs hne
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    have hcomm := spatialDifferenceQuotient_paper5MovingFrameHeatOp
      hlag c d (QBUC s) x
    rw [hQBUCFun s] at hcomm
    simpa only [RD] using hcomm
  have hRraw :
      (∫ s in a..(a + q), paper5MovingFrameHeatOp c (a + q - s)
        (rawSpatialDifferenceQuotient eta d (Q s)) x) =
        eta * (∫ s in a..(a + q), RV s) +
          ∫ s in a..(a + q), RD s := by
    calc
      _ = ∫ s in a..(a + q), eta * RV s + RD s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume (a + q)] with s hne hs
        rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
        have hlag : 0 < a + q - s := sub_pos.mpr
          (lt_of_le_of_ne hs.2 hne)
        have hcore := paper5MovingFrameHeatOp_raw_eq_eta_add_spatialDQ_buc
          hlag eta c d (QBUC s) x
        rw [hQBUCFun s] at hcore
        simpa only [RV, RD] using hcore
      _ = _ := by
        rw [intervalIntegral.integral_add (hRVx.const_mul eta) hRDint,
          intervalIntegral.integral_const_mul]
  calc
    rawSpatialDifferenceQuotient eta d W₁ x =
        eta * W₁ x + spatialDifferenceQuotient d W₁ x := rfl
    _ = eta * (HV + (-p.χ) * (∫ s in a..(a + q), GV s) +
          ∫ s in a..(a + q), RV s) +
        (HD + (-p.χ) * (∫ s in a..(a + q), GD s) +
          ∫ s in a..(a + q), RD s) := by rw [hval, hdq]
    _ = (eta * HV + HD) +
        (-p.χ) * (eta * (∫ s in a..(a + q), GV s) +
          ∫ s in a..(a + q), GD s) +
        (eta * (∫ s in a..(a + q), RV s) +
          ∫ s in a..(a + q), RD s) := by ring
    _ = _ := by rw [← hHraw, ← hGraw, ← hRraw]

#print axioms rawSpatialDifferenceQuotient_intervalIntegral
#print axioms paper5MovingFrameHeatOp_raw_eq_eta_add_spatialDQ_buc
#print axioms paper5MovingFrameHeatGradOp_raw_eq_eta_add_spatialDQ_buc
#print axioms
  wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_identity
#print axioms
  wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_rawSpatialDQ_identity

end ShenWork.Paper1
