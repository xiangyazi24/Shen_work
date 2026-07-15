import ShenWork.Paper1.WholeLineWeightedRegularityPerturbationRestartValue

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

theorem paper5MovingFrameHeatOp_spatialDifferenceQuotient_sub_buc
    {t : ℝ} (ht : 0 < t) (c d : ℝ)
    (u₂ u₁ : WholeLineBUC) (x : ℝ) :
    paper5MovingFrameHeatOp c t
        (spatialDifferenceQuotient d (fun y => u₂.1 y - u₁.1 y)) x =
      paper5MovingFrameHeatOp c t
          (spatialDifferenceQuotient d u₂.1) x -
        paper5MovingFrameHeatOp c t
          (spatialDifferenceQuotient d u₁.1) x := by
  let q₂ : WholeLineBUC := wholeLineBUCSpatialDifferenceQuotientCLM d u₂
  let q₁ : WholeLineBUC := wholeLineBUCSpatialDifferenceQuotientCLM d u₁
  have hsub := wholeLineCauchyHeatOp_sub_buc ht q₂ q₁ (x + c * t)
  have hdq : spatialDifferenceQuotient d
      (fun y => u₂.1 y - u₁.1 y) = fun y =>
        spatialDifferenceQuotient d u₂.1 y -
          spatialDifferenceQuotient d u₁.1 y := by
    funext y
    unfold spatialDifferenceQuotient
    ring
  rw [hdq]
  simpa [paper5MovingFrameHeatOp, q₂, q₁] using hsub

theorem paper5MovingFrameHeatGradOp_spatialDifferenceQuotient_sub_buc
    {t : ℝ} (ht : 0 < t) (c d : ℝ)
    (u₂ u₁ : WholeLineBUC) (x : ℝ) :
    paper5MovingFrameHeatGradOp c t
        (spatialDifferenceQuotient d (fun y => u₂.1 y - u₁.1 y)) x =
      paper5MovingFrameHeatGradOp c t
          (spatialDifferenceQuotient d u₂.1) x -
        paper5MovingFrameHeatGradOp c t
          (spatialDifferenceQuotient d u₁.1) x := by
  let q₂ : WholeLineBUC := wholeLineBUCSpatialDifferenceQuotientCLM d u₂
  let q₁ : WholeLineBUC := wholeLineBUCSpatialDifferenceQuotientCLM d u₁
  have hsub := wholeLineCauchyHeatGradOp_sub_buc ht q₂ q₁ (x + c * t)
  have hdq : spatialDifferenceQuotient d
      (fun y => u₂.1 y - u₁.1 y) = fun y =>
        spatialDifferenceQuotient d u₂.1 y -
          spatialDifferenceQuotient d u₁.1 y := by
    funext y
    unfold spatialDifferenceQuotient
    ring
  rw [hdq]
  simpa [paper5MovingFrameHeatGradOp, q₂, q₁] using hsub

theorem IsTravelingWave.wholeLineTravelingWaveFlux_eq_chemotaxisFlux
    (p : CMParams) {c : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V) :
    wholeLineTravelingWaveFlux p U V = wholeLineChemotaxisFlux p U := by
  have hVEq : V = frozenElliptic p U :=
    IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg
  rw [hVEq]
  rfl

/-- Exact finite spatial-DQ restart for the co-moving perturbation between
the canonical positive solution and a stationary traveling-wave profile.
Both nonlinear legs are genuine matched source differences. -/
theorem wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_spatialDQ_identity
    (p : CMParams) {M T a q c d x D E F FD R : ℝ}
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
    spatialDifferenceQuotient d
        (fun y => (Traj zaq).1 (y + c * (a + q)) - Uw y) x =
      paper5MovingFrameHeatOp c q
        (spatialDifferenceQuotient d
          (fun y => (Traj za).1 (y + c * a) - Uw y)) x +
      (-p.χ) * (∫ s in a..(a + q),
        paper5MovingFrameHeatGradOp c (a + q - s)
          (spatialDifferenceQuotient d (fun y =>
            wholeLineChemotaxisFlux p (us s) y -
              wholeLineChemotaxisFlux p Uw y)) x) +
      ∫ s in a..(a + q),
        paper5MovingFrameHeatOp c (a + q - s)
          (spatialDifferenceQuotient d (fun y =>
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
  let Fw : ℝ → ℝ := wholeLineChemotaxisFlux p Uw
  let Rw : ℝ → ℝ := wholeLineCauchyShiftedReaction p Uw
  let Fc : ℝ → ℝ → ℝ := fun s => wholeLineChemotaxisFlux p (us s)
  let Rc : ℝ → ℝ → ℝ := fun s => wholeLineCauchyShiftedReaction p (us s)
  let Hc : ℝ := paper5MovingFrameHeatOp c q
    (spatialDifferenceQuotient d (fun y => (Traj za).1 (y + c * a))) x
  let Hw : ℝ := paper5MovingFrameHeatOp c q
    (spatialDifferenceQuotient d Uw) x
  let Gc : ℝ → ℝ := fun s => paper5MovingFrameHeatGradOp c (a + q - s)
    (spatialDifferenceQuotient d (Fc s)) x
  let Gw : ℝ → ℝ := fun s => paper5MovingFrameHeatGradOp c (a + q - s)
    (spatialDifferenceQuotient d Fw) x
  let Qc : ℝ → ℝ := fun s => paper5MovingFrameHeatOp c (a + q - s)
    (spatialDifferenceQuotient d (Rc s)) x
  let Qw : ℝ → ℝ := fun s => paper5MovingFrameHeatOp c (a + q - s)
    (spatialDifferenceQuotient d Rw) x
  have hcan :=
    wholeLineCauchyBUCMildFixedPoint_coMoving_restart_spatialDQ_identity
      p hM hT u₀ hsmall ha hq haq hstrip (c := c) (d := d) (x := x)
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
  have hwave :=
    IsTravelingWave.stationary_divergence_mild_spatialDQ_identity_on_window
      p hTW hbound hreg hq hD hFD hR hUd hUdd hUddcont
      hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
      hgrad_int_x hgrad_int_xd (a := a) (d := d) (x := x)
  have hFwEq : wholeLineTravelingWaveFlux p Uw Vw = Fw := by
    simpa only [Fw] using
      IsTravelingWave.wholeLineTravelingWaveFlux_eq_chemotaxisFlux
        p hTW hbound hreg
  rw [hFwEq] at hwave
  change spatialDifferenceQuotient d
      (fun y => (Traj zaq).1 (y + c * (a + q))) x =
    Hc + (-p.χ) * (∫ s in a..(a + q), Gc s) +
      ∫ s in a..(a + q), Qc s at hcan
  change spatialDifferenceQuotient d Uw x =
    Hw + (-p.χ) * (∫ s in a..(a + q), Gw s) +
      ∫ s in a..(a + q), Qw s at hwave
  let UaBUC : WholeLineBUC := wholeLineBUCTranslate (c * a) (Traj za)
  have hUwBound : ∀ y, |Uw y| ≤ MChi p := by
    intro y
    rw [abs_of_pos (hbound.pos y)]
    exact hbound.le_MChi y
  let UwBUC : WholeLineBUC := wholeLineBUCOfUniformBound Uw
    (travelingWave_U_uniformContinuous hTW hreg.U_cont) (MChi p) hUwBound
  have hHsub : paper5MovingFrameHeatOp c q
        (spatialDifferenceQuotient d
          (fun y => (Traj za).1 (y + c * a) - Uw y)) x = Hc - Hw := by
    simpa only [UaBUC, UwBUC, Hc, Hw,
      wholeLineBUCTranslate_apply, wholeLineBUCOfUniformBound_apply] using
      paper5MovingFrameHeatOp_spatialDifferenceQuotient_sub_buc
        hq c d UaBUC UwBUC x
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
  have hGc_x := wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
    p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj x (c := c)
  have hGc_xd := wholeLineCauchyCoMovingGradientIntegrand_intervalIntegrable
    p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj (x + d) (c := c)
  have hGc_eval : IntervalIntegrable (fun s => spatialDifferenceQuotient d
      (fun y => paper5MovingFrameHeatGradOp c (a + q - s)
        (wholeLineCauchyCoMovingFluxSource p c hM hT Traj s) y) x)
      volume a (a + q) := by
    simpa only [spatialDifferenceQuotient] using (hGc_xd.sub hGc_x).div_const d
  have hGc_int : IntervalIntegrable Gc volume a (a + q) := by
    apply hGc_eval.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (a + q))] with s hs hne
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    have hcomm := spatialDifferenceQuotient_paper5MovingFrameHeatGradOp
      hlag c d (FcBUC s) x
    rw [hFcBUCFun s] at hcomm
    rw [hCF s]
    simpa only [Gc] using hcomm
  have hGw0_eval : IntervalIntegrable (fun r => spatialDifferenceQuotient d
      (fun y => paper5MovingFrameHeatGradOp c r Fw y) x)
      volume 0 q := by
    simpa only [spatialDifferenceQuotient, ← hFwEq] using
      (hgrad_int_xd.sub hgrad_int_x).div_const d
  have hGw0 : IntervalIntegrable (fun r =>
      paper5MovingFrameHeatGradOp c r (spatialDifferenceQuotient d Fw) x)
      volume 0 q := by
    apply hGw0_eval.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with r hr hr0
    rw [Set.uIoc_of_le hq.le] at hr
    have hcomm := spatialDifferenceQuotient_paper5MovingFrameHeatGradOp
      hr.1 c d FwBUC x
    simpa only [FwBUC, wholeLineBUCOfUniformBound_apply] using hcomm
  have hGw_int : IntervalIntegrable Gw volume a (a + q) := by
    have hcomp := (hGw0.comp_sub_left (a + q)).symm
    convert hcomp using 1 <;> ring
  have hGsub :
      (∫ s in a..(a + q), paper5MovingFrameHeatGradOp c (a + q - s)
        (spatialDifferenceQuotient d (fun y => Fc s y - Fw y)) x) =
        (∫ s in a..(a + q), Gc s) - ∫ s in a..(a + q), Gw s := by
    calc
      _ = ∫ s in a..(a + q), Gc s - Gw s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume (a + q)] with s hne hs
        rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
        have hlag : 0 < a + q - s := sub_pos.mpr
          (lt_of_le_of_ne hs.2 hne)
        have hsub :=
          paper5MovingFrameHeatGradOp_spatialDifferenceQuotient_sub_buc
            hlag c d (FcBUC s) FwBUC x
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
  have hQc_x := wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
    p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj x (c := c)
  have hQc_xd := wholeLineCauchyCoMovingValueIntegrand_intervalIntegrable
    p hM hT ha.le (le_add_of_nonneg_right hq.le) Traj (x + d) (c := c)
  have hQc_eval : IntervalIntegrable (fun s => spatialDifferenceQuotient d
      (fun y => paper5MovingFrameHeatOp c (a + q - s)
        (wholeLineCauchyCoMovingReactionSource p c hM hT Traj s) y) x)
      volume a (a + q) := by
    simpa only [spatialDifferenceQuotient] using (hQc_xd.sub hQc_x).div_const d
  have hQc_int : IntervalIntegrable Qc volume a (a + q) := by
    apply hQc_eval.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (a + q))] with s hs hne
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
    have hlag : 0 < a + q - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
    have hcomm := spatialDifferenceQuotient_paper5MovingFrameHeatOp
      hlag c d (RcBUC s) x
    rw [hRcBUCFun s] at hcomm
    rw [hCR s]
    simpa only [Qc] using hcomm
  have hQw_x : IntervalIntegrable (fun r =>
      paper5MovingFrameHeatOp c r Rw x) volume 0 q := by
    simpa only [Rw] using wholeLineCauchyMovingHeatOp_intervalIntegrable
      hq hR hreact_cont hreact (x := x)
  have hQw_xd : IntervalIntegrable (fun r =>
      paper5MovingFrameHeatOp c r Rw (x + d)) volume 0 q := by
    simpa only [Rw] using wholeLineCauchyMovingHeatOp_intervalIntegrable
      hq hR hreact_cont hreact (x := x + d)
  have hQw0_eval : IntervalIntegrable (fun r => spatialDifferenceQuotient d
      (fun y => paper5MovingFrameHeatOp c r Rw y) x) volume 0 q := by
    simpa only [spatialDifferenceQuotient] using
      (hQw_xd.sub hQw_x).div_const d
  have hQw0 : IntervalIntegrable (fun r =>
      paper5MovingFrameHeatOp c r (spatialDifferenceQuotient d Rw) x)
      volume 0 q := by
    apply hQw0_eval.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with r hr hr0
    rw [Set.uIoc_of_le hq.le] at hr
    have hcomm := spatialDifferenceQuotient_paper5MovingFrameHeatOp
      hr.1 c d RwBUC x
    have hRwFun : (RwBUC : ℝ → ℝ) = Rw := funext hRwBUC
    rw [hRwFun] at hcomm
    exact hcomm
  have hQw_int : IntervalIntegrable Qw volume a (a + q) := by
    have hcomp := (hQw0.comp_sub_left (a + q)).symm
    convert hcomp using 1 <;> ring
  have hRsub :
      (∫ s in a..(a + q), paper5MovingFrameHeatOp c (a + q - s)
        (spatialDifferenceQuotient d (fun y => Rc s y - Rw y)) x) =
        (∫ s in a..(a + q), Qc s) - ∫ s in a..(a + q), Qw s := by
    calc
      _ = ∫ s in a..(a + q), Qc s - Qw s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume (a + q)] with s hne hs
        rw [Set.uIoc_of_le (le_add_of_nonneg_right hq.le)] at hs
        have hlag : 0 < a + q - s := sub_pos.mpr
          (lt_of_le_of_ne hs.2 hne)
        have hsub := paper5MovingFrameHeatOp_spatialDifferenceQuotient_sub_buc
          hlag c d (RcBUC s) RwBUC x
        have hRwFun : (RwBUC : ℝ → ℝ) = Rw := funext hRwBUC
        rw [hRwFun] at hsub
        rw [hRcBUCFun s] at hsub
        simpa only [Qc, Qw] using hsub
      _ = _ := intervalIntegral.integral_sub hQc_int hQw_int
  calc
    spatialDifferenceQuotient d
        (fun y => (Traj zaq).1 (y + c * (a + q)) - Uw y) x =
      spatialDifferenceQuotient d
          (fun y => (Traj zaq).1 (y + c * (a + q))) x -
        spatialDifferenceQuotient d Uw x := by
          unfold spatialDifferenceQuotient
          ring
    _ = (Hc + (-p.χ) * (∫ s in a..(a + q), Gc s) +
          ∫ s in a..(a + q), Qc s) -
        (Hw + (-p.χ) * (∫ s in a..(a + q), Gw s) +
          ∫ s in a..(a + q), Qw s) := by rw [hcan, hwave]
    _ = (Hc - Hw) +
        (-p.χ) * ((∫ s in a..(a + q), Gc s) -
          ∫ s in a..(a + q), Gw s) +
        ((∫ s in a..(a + q), Qc s) -
          ∫ s in a..(a + q), Qw s) := by ring
    _ = _ := by
      rw [← hHsub, ← hGsub, ← hRsub]

#print axioms paper5MovingFrameHeatOp_spatialDifferenceQuotient_sub_buc
#print axioms paper5MovingFrameHeatGradOp_spatialDifferenceQuotient_sub_buc
#print axioms IsTravelingWave.wholeLineTravelingWaveFlux_eq_chemotaxisFlux
#print axioms
  wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_spatialDQ_identity

end ShenWork.Paper1
