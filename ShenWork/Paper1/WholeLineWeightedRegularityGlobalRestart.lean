import ShenWork.Paper1.WholeLineCauchyGlobalGluing
import ShenWork.Paper1.WholeLineWeightedRegularityRestart

open Filter Topology Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical global-to-restart charts for weighted regularity

The globally glued Cauchy solution is assembled from canonical BUC mild
fixed points.  This file exposes that fact without the intermediate
`wholeLineCauchyGlobalSegment` wrapper, both in the laboratory frame and in
the moving frame used by the weighted estimates.
-/

/-- At every nonnegative time, the canonical global BUC slice is exactly the
canonical fixed point on its preferred segment, evaluated at the preferred
local time. -/
theorem wholeLineCauchyGlobalBUC_eq_fixedPoint_localTime
    (p : CMParams) (u₀ : WholeLineBUC) {t : ℝ} (ht : 0 ≤ t) :
    wholeLineCauchyGlobalBUC p u₀ t =
      wholeLineCauchyBUCMildFixedPoint p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalDatum p u₀
          (wholeLineCauchyGlobalIndex p u₀ t))
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        ⟨wholeLineCauchyGlobalLocalTime p u₀ t,
          wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
          (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩ := by
  simpa [wholeLineCauchyGlobalSegment] using
    (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht)

/-- Function-valued population version of
`wholeLineCauchyGlobalBUC_eq_fixedPoint_localTime`. -/
theorem wholeLineCauchyGlobalU_eq_fixedPoint_localTime
    (p : CMParams) (u₀ : WholeLineBUC) {t : ℝ} (ht : 0 ≤ t) :
    wholeLineCauchyGlobalU p u₀ t =
      (wholeLineCauchyBUCMildFixedPoint p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalDatum p u₀
          (wholeLineCauchyGlobalIndex p u₀ t))
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        ⟨wholeLineCauchyGlobalLocalTime p u₀ t,
          wholeLineCauchyGlobalLocalTime_nonneg p u₀ ht,
          (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht).le⟩).1 := by
  funext x
  simpa [wholeLineCauchyGlobalU] using congrArg
    (fun w : WholeLineBUC => w.1 x)
    (wholeLineCauchyGlobalBUC_eq_fixedPoint_localTime p u₀ ht)

/-- Exact moving-frame chart at a positive global time.  The fixed point is
read at the preferred local time.  The spatial argument is shifted by the
global segment base time, so its local moving coordinate lands at the same
laboratory point as the global moving coordinate. -/
theorem wholeLineCauchyGlobal_coMoving_eq_fixedPointCoMoving_localTime
    (p : CMParams) (u₀ : WholeLineBUC) {c t : ℝ} (ht : 0 < t) :
    coMovingPath c (wholeLineCauchyGlobalU p u₀) t =
      fun x =>
        wholeLineCauchyBUCMildFixedPointCoMovingPath p
          (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
          (wholeLineCauchyGlobalDatum p u₀
            (wholeLineCauchyGlobalIndex p u₀ t))
          (wholeLineCauchyGlobalSegmentTime_rate p u₀) c
          (wholeLineCauchyGlobalLocalTime p u₀ t)
          (x + c * ((wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
            wholeLineCauchyGlobalStep p u₀)) := by
  funext x
  have hq : wholeLineCauchyGlobalLocalTime p u₀ t ∈
      Set.Icc (0 : ℝ) (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨(wholeLineCauchyGlobalLocalTime_pos p u₀ ht).le,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le).le⟩
  rw [wholeLineCauchyBUCMildFixedPointCoMovingPath_of_mem
    p (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalDatum p u₀
        (wholeLineCauchyGlobalIndex p u₀ t))
      (wholeLineCauchyGlobalSegmentTime_rate p u₀) c
      (wholeLineCauchyGlobalLocalTime p u₀ t) _ hq]
  unfold coMovingPath
  rw [wholeLineCauchyGlobalU_eq_fixedPoint_localTime p u₀ ht.le]
  unfold wholeLineCauchyGlobalLocalTime
  have hcoord :
      x + c * t =
        x + c * ((wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
          wholeLineCauchyGlobalStep p u₀) +
          c * (t - (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
            wholeLineCauchyGlobalStep p u₀) := by
    ring
  rw [hcoord]

/-- Every positive global time has a neighborhood on which the glued BUC
orbit is the extension of one concrete canonical mild fixed point.  This is
the time-window version of `wholeLineCauchyGlobalBUC_eq_fixedPoint_localTime`.
-/
theorem wholeLineCauchyGlobalBUC_eventuallyEq_fixedPoint
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 < t) :
    (fun s => wholeLineCauchyGlobalBUC p u₀ s) =ᶠ[nhds t]
      fun s =>
        wholeLineBUCTrajectoryExtend
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
          (wholeLineCauchyBUCMildFixedPoint p
            (wholeLineCauchyGlobalClamp_pos p u₀).le
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
            (wholeLineCauchyGlobalDatum p u₀
              (wholeLineCauchyGlobalIndex p u₀ t))
            (wholeLineCauchyGlobalSegmentTime_rate p u₀))
          (s - (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
            wholeLineCauchyGlobalStep p u₀) := by
  simpa [wholeLineCauchyGlobalSegment] using
    (wholeLineCauchyGlobalBUC_eventuallyEq_preferred
      p hregime u₀ hu₀ ht)

/-- Pointwise moving-frame form of the canonical positive-time chart.  On a
neighborhood of `t`, all time dependence comes from one explicit BUC mild
fixed-point trajectory; the moving observation point remains `x + c * s`.
-/
theorem wholeLineCauchyGlobal_coMoving_eventuallyEq_fixedPoint
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {c t x : ℝ} (ht : 0 < t) :
    (fun s => coMovingPath c (wholeLineCauchyGlobalU p u₀) s x)
        =ᶠ[nhds t]
      fun s =>
        (wholeLineBUCTrajectoryExtend
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
          (wholeLineCauchyBUCMildFixedPoint p
            (wholeLineCauchyGlobalClamp_pos p u₀).le
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
            (wholeLineCauchyGlobalDatum p u₀
              (wholeLineCauchyGlobalIndex p u₀ t))
            (wholeLineCauchyGlobalSegmentTime_rate p u₀))
          (s - (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
            wholeLineCauchyGlobalStep p u₀)).1 (x + c * s) := by
  filter_upwards [wholeLineCauchyGlobalBUC_eventuallyEq_fixedPoint
    p hregime u₀ hu₀ ht] with s hs
  simpa [coMovingPath, wholeLineCauchyGlobalU] using congrArg
    (fun w : WholeLineBUC => w.1 (x + c * s)) hs

section AxiomAudit

#print axioms wholeLineCauchyGlobalBUC_eq_fixedPoint_localTime
#print axioms wholeLineCauchyGlobalU_eq_fixedPoint_localTime
#print axioms wholeLineCauchyGlobal_coMoving_eq_fixedPointCoMoving_localTime
#print axioms wholeLineCauchyGlobalBUC_eventuallyEq_fixedPoint
#print axioms wholeLineCauchyGlobal_coMoving_eventuallyEq_fixedPoint

end AxiomAudit

end ShenWork.Paper1
