import ShenWork.Paper1.WholeLineWeightedRegularityCoMovingMatchedSource
import ShenWork.Paper1.WholeLineWeightedRegularityWaveRestartDQ
import ShenWork.Paper1.WholeLineWeightedRegularityActualHistory

open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Value identities for matched positive-time restarts

The spatial-DQ argument also needs the undifferentiated restart identity in
the same absolute-time window.  The small public linearity lemmas below keep
all integrability inside the existing BUC convolution interface.
-/

/-- Moving heat flow preserves differences of BUC inputs. -/
theorem paper5MovingFrameHeatOp_sub_buc
    {q : ℝ} (hq : 0 < q) (c : ℝ)
    (u v : WholeLineBUC) (x : ℝ) :
    paper5MovingFrameHeatOp c q (fun y => u.1 y - v.1 y) x =
      paper5MovingFrameHeatOp c q u.1 x -
        paper5MovingFrameHeatOp c q v.1 x := by
  simpa only [paper5MovingFrameHeatOp] using
    wholeLineCauchyHeatOp_sub_buc hq u v (x + c * q)

/-- Moving heat-gradient flow preserves differences of BUC inputs. -/
theorem paper5MovingFrameHeatGradOp_sub_buc
    {q : ℝ} (hq : 0 < q) (c : ℝ)
    (u v : WholeLineBUC) (x : ℝ) :
    paper5MovingFrameHeatGradOp c q (fun y => u.1 y - v.1 y) x =
      paper5MovingFrameHeatGradOp c q u.1 x -
        paper5MovingFrameHeatGradOp c q v.1 x := by
  simpa only [paper5MovingFrameHeatGradOp] using
    wholeLineCauchyHeatGradOp_sub_buc hq u v (x + c * q)

/-- The stationary traveling-wave divergence mild identity rewritten on the
same absolute-time window `[a,a+q]` as a canonical restart. -/
theorem IsTravelingWave.stationary_divergence_mild_identity_on_window
    (p : CMParams) {a c q x D E F FD R : ℝ} {U V : ℝ → ℝ}
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
    (hgrad_int : IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q) :
    U x = paper5MovingFrameHeatOp c q U x +
      (-p.χ) * (∫ s in a..(a + q),
        paper5MovingFrameHeatGradOp c (a + q - s)
          (wholeLineTravelingWaveFlux p U V) x) +
      ∫ s in a..(a + q),
        paper5MovingFrameHeatOp c (a + q - s)
          (wholeLineCauchyShiftedReaction p U) x := by
  have hbase := IsTravelingWave.stationary_divergence_mild_identity
    p hTW hbound hreg hq hD hFD hR hUd hUdd hUddcont
      hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
      (x := x)
  let G : ℝ → ℝ := fun r =>
    paper5MovingFrameHeatGradOp c r
      (wholeLineTravelingWaveFlux p U V) x
  let Q : ℝ → ℝ := fun r =>
    paper5MovingFrameHeatOp c r
      (wholeLineCauchyShiftedReaction p U) x
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
  change U x = paper5MovingFrameHeatOp c q U x +
      (-p.χ) * (∫ r in (0 : ℝ)..q, G r) +
      ∫ r in (0 : ℝ)..q, Q r at hbase
  rw [hGchange, hQchange] at hbase
  simpa [G, Q] using hbase

#print axioms paper5MovingFrameHeatOp_sub_buc
#print axioms paper5MovingFrameHeatGradOp_sub_buc
#print axioms IsTravelingWave.stationary_divergence_mild_identity_on_window

end ShenWork.Paper1
