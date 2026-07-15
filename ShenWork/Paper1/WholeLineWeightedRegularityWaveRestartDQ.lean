import ShenWork.Paper1.WholeLineWeightedRegularityPositiveRestartDQ

open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

/-- Spatial-DQ form of the stationary traveling-wave divergence mild identity.
The two explicit gradient-integrability assumptions are exactly the two
spatial evaluations used by the finite difference quotient. -/
theorem IsTravelingWave.stationary_divergence_mild_spatialDQ_identity
    (p : CMParams) {c q d x D E F FD R : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hq : 0 < q) (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int_x : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q)
    (hgrad_int_xd : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) (x + d)) volume 0 q) :
    spatialDifferenceQuotient d U x =
      paper5MovingFrameHeatOp c q (spatialDifferenceQuotient d U) x +
      (-p.χ) * (∫ r in (0 : ℝ)..q,
        paper5MovingFrameHeatGradOp c r
          (spatialDifferenceQuotient d
            (wholeLineTravelingWaveFlux p U V)) x) +
      ∫ r in (0 : ℝ)..q,
        paper5MovingFrameHeatOp c r
          (spatialDifferenceQuotient d
            (wholeLineCauchyShiftedReaction p U)) x := by
  let Flux : ℝ → ℝ := wholeLineTravelingWaveFlux p U V
  let React : ℝ → ℝ := wholeLineCauchyShiftedReaction p U
  let H₀ : ℝ → ℝ := fun y => paper5MovingFrameHeatOp c q U y
  let G : ℝ → ℝ → ℝ := fun r y =>
    paper5MovingFrameHeatGradOp c r Flux y
  let Q : ℝ → ℝ → ℝ := fun r y =>
    paper5MovingFrameHeatOp c r React y
  have hx : U x = H₀ x + (-p.χ) * (∫ r in (0 : ℝ)..q, G r x) +
      ∫ r in (0 : ℝ)..q, Q r x := by
    simpa [H₀, G, Q, Flux, React] using
      IsTravelingWave.stationary_divergence_mild_identity
        p hTW hbound hreg hq hD hFD hR
        hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
        hreact hreact_cont hgrad_int_x (x := x)
  have hxd : U (x + d) = H₀ (x + d) +
      (-p.χ) * (∫ r in (0 : ℝ)..q, G r (x + d)) +
      ∫ r in (0 : ℝ)..q, Q r (x + d) := by
    simpa [H₀, G, Q, Flux, React] using
      IsTravelingWave.stationary_divergence_mild_identity
        p hTW hbound hreg hq hD hFD hR
        hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
        hreact hreact_cont hgrad_int_xd (x := x + d)
  have hUbound : ∀ y, |U y| ≤ MChi p := by
    intro y
    rw [abs_of_pos (hbound.pos y)]
    exact hbound.le_MChi y
  let UBUC : WholeLineBUC := wholeLineBUCOfUniformBound U
    (travelingWave_U_uniformContinuous hTW hreg.U_cont) (MChi p) hUbound
  have hhom : spatialDifferenceQuotient d H₀ x =
      paper5MovingFrameHeatOp c q (spatialDifferenceQuotient d U) x := by
    simpa [H₀, UBUC] using
      spatialDifferenceQuotient_paper5MovingFrameHeatOp hq c d UBUC x
  have hFluxDiff : Differentiable ℝ Flux := by
    intro y
    exact (hflux_has y).differentiableAt
  have hFluxNN : ∀ y, ‖deriv Flux y‖₊ ≤ ⟨FD, hFD⟩ := by
    intro y
    apply NNReal.coe_le_coe.mp
    simpa [Flux, Real.norm_eq_abs] using hfluxd y
  have hFluxUC : UniformContinuous Flux :=
    (lipschitzWith_of_nnnorm_deriv_le hFluxDiff hFluxNN).uniformContinuous
  let FBUC : WholeLineBUC := wholeLineBUCOfUniformBound Flux hFluxUC F (by
    intro y
    exact hflux y)
  have hGdq₀ : spatialDifferenceQuotient d
        (fun y => ∫ r in (0 : ℝ)..q, G r y) x =
      ∫ r in (0 : ℝ)..q, spatialDifferenceQuotient d (G r) x :=
    spatialDifferenceQuotient_intervalIntegral hgrad_int_x hgrad_int_xd
  have hGcomm :
      (∫ r in (0 : ℝ)..q, spatialDifferenceQuotient d (G r) x) =
        ∫ r in (0 : ℝ)..q,
          paper5MovingFrameHeatGradOp c r
            (spatialDifferenceQuotient d Flux) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume 0] with r hr0 hr
    rw [Set.uIoc_of_le hq.le] at hr
    have hrpos : 0 < r := hr.1
    simpa [G, FBUC] using
      spatialDifferenceQuotient_paper5MovingFrameHeatGradOp
        hrpos c d FBUC x
  have hGdq : spatialDifferenceQuotient d
        (fun y => ∫ r in (0 : ℝ)..q, G r y) x =
      ∫ r in (0 : ℝ)..q,
        paper5MovingFrameHeatGradOp c r
          (spatialDifferenceQuotient d Flux) x :=
    hGdq₀.trans hGcomm
  have hM : 0 ≤ MChi p :=
    (hbound.pos 0).le.trans (hbound.le_MChi 0)
  have hUmem : ∀ y, U y ∈ Set.Icc (0 : ℝ) (MChi p) := fun y =>
    ⟨(hbound.pos y).le, hbound.le_MChi y⟩
  let RBUC : WholeLineBUC :=
    wholeLineCauchyTruncatedReactionBUC p (MChi p) hM UBUC
  have hRBUC (y : ℝ) : (RBUC : ℝ → ℝ) y = React y := by
    change wholeLineCauchyTruncatedReaction p (MChi p) U y = React y
    rw [wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hM hUmem]
  have hQx : IntervalIntegrable (fun r => Q r x) volume 0 q := by
    simpa [Q, React] using
      wholeLineCauchyMovingHeatOp_intervalIntegrable
        hq hR hreact_cont hreact (x := x)
  have hQxd : IntervalIntegrable (fun r => Q r (x + d)) volume 0 q := by
    simpa [Q, React] using
      wholeLineCauchyMovingHeatOp_intervalIntegrable
        hq hR hreact_cont hreact (x := x + d)
  have hQdq₀ : spatialDifferenceQuotient d
        (fun y => ∫ r in (0 : ℝ)..q, Q r y) x =
      ∫ r in (0 : ℝ)..q, spatialDifferenceQuotient d (Q r) x :=
    spatialDifferenceQuotient_intervalIntegral hQx hQxd
  have hQcomm :
      (∫ r in (0 : ℝ)..q, spatialDifferenceQuotient d (Q r) x) =
        ∫ r in (0 : ℝ)..q,
          paper5MovingFrameHeatOp c r
            (spatialDifferenceQuotient d React) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume 0] with r hr0 hr
    rw [Set.uIoc_of_le hq.le] at hr
    have hrpos : 0 < r := hr.1
    have hcomm := spatialDifferenceQuotient_paper5MovingFrameHeatOp
      hrpos c d RBUC x
    have hRfun : (RBUC : ℝ → ℝ) = React := funext hRBUC
    rw [hRfun] at hcomm
    simpa only [Q] using hcomm
  have hQdq : spatialDifferenceQuotient d
        (fun y => ∫ r in (0 : ℝ)..q, Q r y) x =
      ∫ r in (0 : ℝ)..q,
        paper5MovingFrameHeatOp c r
          (spatialDifferenceQuotient d React) x :=
    hQdq₀.trans hQcomm
  calc
    spatialDifferenceQuotient d U x =
        spatialDifferenceQuotient d (fun y =>
          H₀ y + (-p.χ) * (∫ r in (0 : ℝ)..q, G r y) +
            ∫ r in (0 : ℝ)..q, Q r y) x := by
      unfold spatialDifferenceQuotient
      rw [hx, hxd]
    _ = spatialDifferenceQuotient d H₀ x +
        (-p.χ) * spatialDifferenceQuotient d
          (fun y => ∫ r in (0 : ℝ)..q, G r y) x +
        spatialDifferenceQuotient d
          (fun y => ∫ r in (0 : ℝ)..q, Q r y) x := by
      unfold spatialDifferenceQuotient
      ring
    _ = _ := by
      rw [hhom, hGdq, hQdq]

/-- The stationary traveling-wave spatial-DQ formula rewritten on the same
absolute-time window `[a,a+q]` as the canonical positive-time restart. -/
theorem IsTravelingWave.stationary_divergence_mild_spatialDQ_identity_on_window
    (p : CMParams) {a c q d x D E F FD R : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hq : 0 < q) (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hR : 0 ≤ R)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ F)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ R)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int_x : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q)
    (hgrad_int_xd : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) (x + d)) volume 0 q) :
    spatialDifferenceQuotient d U x =
      paper5MovingFrameHeatOp c q (spatialDifferenceQuotient d U) x +
      (-p.χ) * (∫ s in a..(a + q),
        paper5MovingFrameHeatGradOp c (a + q - s)
          (spatialDifferenceQuotient d
            (wholeLineTravelingWaveFlux p U V)) x) +
      ∫ s in a..(a + q),
        paper5MovingFrameHeatOp c (a + q - s)
          (spatialDifferenceQuotient d
            (wholeLineCauchyShiftedReaction p U)) x := by
  have hbase :=
    IsTravelingWave.stationary_divergence_mild_spatialDQ_identity
      p hTW hbound hreg hq hD hFD hR hUd hUdd hUddcont
      hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
      hgrad_int_x hgrad_int_xd
  let G : ℝ → ℝ := fun r =>
    paper5MovingFrameHeatGradOp c r
      (spatialDifferenceQuotient d
        (wholeLineTravelingWaveFlux p U V)) x
  let Q : ℝ → ℝ := fun r =>
    paper5MovingFrameHeatOp c r
      (spatialDifferenceQuotient d
        (wholeLineCauchyShiftedReaction p U)) x
  have hGchange : (∫ r in (0 : ℝ)..q, G r) =
      ∫ s in a..(a + q), G (a + q - s) := by
    have hchange := intervalIntegral.integral_comp_sub_left
      (a := a) (b := a + q) G (a + q)
    simpa using hchange.symm
  have hQchange : (∫ r in (0 : ℝ)..q, Q r) =
      ∫ s in a..(a + q), Q (a + q - s) := by
    have hchange := intervalIntegral.integral_comp_sub_left
      (a := a) (b := a + q) Q (a + q)
    simpa using hchange.symm
  change spatialDifferenceQuotient d U x =
      paper5MovingFrameHeatOp c q (spatialDifferenceQuotient d U) x +
      (-p.χ) * (∫ r in (0 : ℝ)..q, G r) +
      ∫ r in (0 : ℝ)..q, Q r at hbase
  rw [hGchange, hQchange] at hbase
  simpa [G, Q] using hbase

#print axioms IsTravelingWave.stationary_divergence_mild_spatialDQ_identity
#print axioms
  IsTravelingWave.stationary_divergence_mild_spatialDQ_identity_on_window

end ShenWork.Paper1
