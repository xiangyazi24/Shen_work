import ShenWork.Paper1.WholeLineWeightedRegularityPerturbationRestartRaw
import ShenWork.Paper1.WholeLineWeightedRegularityCap

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

/-- The exact raw spatial-difference-quotient restart after multiplication by
the square root of a cap weight.  The cap radius `R` is independent of the
reaction bound `B`; no weighted regularity assumption is needed for this
pointwise algebraic identity. -/
theorem wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_capWeightedRawSpatialDQ_identity
    (p : CMParams) {M T a q eta R c d x D E F FD B : ℝ}
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
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
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
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
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
    capWeightSqrt eta R x *
        rawSpatialDifferenceQuotient eta d
          (fun y => (Traj zaq).1 (y + c * (a + q)) - Uw y) x =
      capWeightSqrt eta R x *
          paper5MovingFrameHeatOp c q
            (rawSpatialDifferenceQuotient eta d
              (fun y => (Traj za).1 (y + c * a) - Uw y)) x +
      (-p.χ) * (∫ s in a..(a + q),
        capWeightSqrt eta R x *
          paper5MovingFrameHeatGradOp c (a + q - s)
            (rawSpatialDifferenceQuotient eta d (fun y =>
              wholeLineChemotaxisFlux p (us s) y -
                wholeLineChemotaxisFlux p Uw y)) x) +
      ∫ s in a..(a + q),
        capWeightSqrt eta R x *
          paper5MovingFrameHeatOp c (a + q - s)
            (rawSpatialDifferenceQuotient eta d (fun y =>
              wholeLineCauchyShiftedReaction p (us s) y -
                wholeLineCauchyShiftedReaction p Uw y)) x := by
  dsimp only
  have hraw :=
    wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_rawSpatialDQ_identity
      p hM hT u₀ hsmall ha hq haq hstrip hTW hbound hreg
      hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has
      hfluxd_cont hreact hreact_cont hgrad_int_x hgrad_int_xd
      (c := c) (eta := eta) (d := d) (x := x)
  dsimp only at hraw
  rw [hraw]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

#print axioms
  wholeLineCauchyBUCMildFixedPoint_coMoving_wavePerturbation_restart_capWeightedRawSpatialDQ_identity

end ShenWork.Paper1
