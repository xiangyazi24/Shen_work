import ShenWork.Paper1.WholeLineWeightedRegularityGlobalScaledTrapNatural

open MeasureTheory Set

noncomputable section

namespace ShenWork.Paper1

/-!
# The common scaled trap on every late global restart window

The restart-family producer is stated in the phase-normalized fixed-point
coordinates of each canonical segment.  The closed second-half transport
identity turns it into a statement about the canonical glued global orbit,
including the common endpoint of two consecutive segments.
-/

/-- A nonpositive-sensitivity orbit converging in the exact moving-frame
weight has one scaled paper-trap constant on every sufficiently late closed
global restart window. -/
theorem exists_eventual_common_global_inTimeWaveTrapSet_chi_nonpos
    (p : CMParams) (hchi : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c D E Kflux FD B : ℝ}
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (hkappa : 0 < kappa c) (hkappaEta : kappa c ≤ eta)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hlog : ∀ y, |deriv Uw y / Uw y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hconv : CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) Uw) :
    ∃ N : ℕ, ∃ Q : ℝ, 1 ≤ Q ∧
      ∀ n : ℕ, N ≤ n →
        InTimeWaveTrapSet (kappa c) Q
          (wholeLineCauchyGlobalStep p u₀)
          (fun r x => wholeLineCauchyGlobalU p u₀
            (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
            (x + c * (((n : ℝ) + 1) *
              wholeLineCauchyGlobalStep p u₀ + r))) := by
  obtain ⟨N, Q, hQ, htrap⟩ :=
    exists_eventual_common_shifted_inTimeWaveTrapSet_chi_nonpos
      p hchi u₀ hu₀ hBlog heta heta_one hkappa hkappaEta
        hTW hbound hreg hlog hD hFD hB hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
        hgrad_int hconv
  refine ⟨N, Q, hQ, ?_⟩
  intro n hn r hr
  let datum := wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n
  let Traj := wholeLineCauchyBUCMildFixedPoint p
    (wholeLineCauchyGlobalClamp_pos p u₀).le
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le datum
    (wholeLineCauchyGlobalSegmentTime_rate p u₀)
  let q : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1
        (x + c * s)
  have hglobal :
      (fun x => wholeLineCauchyGlobalU p u₀
        (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
        (x + c * (((n : ℝ) + 1) *
          wholeLineCauchyGlobalStep p u₀ + r))) =
        q (wholeLineCauchyGlobalStep p u₀ + r) :=
    wholeLineCauchyGlobal_coMoving_eq_translatedSegment_second_half_closed
      p (WholeLineCauchyCeilingRegime.of_nonpositive hchi) u₀ hu₀ c n
        hr.1 hr.2
  change
    IsCUnifBdd (fun x => wholeLineCauchyGlobalU p u₀
      (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
      (x + c * (((n : ℝ) + 1) *
        wholeLineCauchyGlobalStep p u₀ + r))) ∧
      ∀ x, 0 ≤ wholeLineCauchyGlobalU p u₀
        (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
        (x + c * (((n : ℝ) + 1) *
          wholeLineCauchyGlobalStep p u₀ + r)) ∧
        wholeLineCauchyGlobalU p u₀
          (((n : ℝ) + 1) * wholeLineCauchyGlobalStep p u₀ + r)
          (x + c * (((n : ℝ) + 1) *
            wholeLineCauchyGlobalStep p u₀ + r)) ≤
          scaledUpperBarrier (kappa c) Q x
  have hlocal := htrap n hn r hr
  constructor
  · rw [hglobal]
    exact hlocal.1
  · intro x
    have hx := congrFun hglobal x
    rw [hx]
    exact hlocal.2 x

#print axioms exists_eventual_common_global_inTimeWaveTrapSet_chi_nonpos

end ShenWork.Paper1
