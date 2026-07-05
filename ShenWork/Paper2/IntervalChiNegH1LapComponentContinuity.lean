import ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
import ShenWork.PDE.P3MoserGradientContinuityFromDx

/-!
# Strict-window continuity of the H¹ Laplacian component

This file discharges the positive-time part of the `lapL2sq` component
continuity frontier from the scalar `liftDeriv2` joint-continuity hypothesis.
It intentionally stays on strict time windows; no continuity at `t = 0` is
claimed here.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity

/-- Closed-slab joint continuity of `u_xx` implies closed-window continuity of
the squared Laplacian component on that same slab. -/
theorem lapL2sq_continuousOn_Icc_of_liftDeriv2_jointContinuousOn
    {u : ℝ → intervalDomainPoint → ℝ} {a b : ℝ}
    (hcont :
      ContinuousOn (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) := by
  let F : ℝ → ℝ → ℝ := fun τ x => (liftDeriv2 u τ x) ^ 2
  have hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [F, Function.uncurry] using hcont.pow 2
  have hint :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hFcont
  simpa [F, lapL2sq, liftDeriv2] using hint

/-- The scalar strict-slab regularity package gives `lapL2sq` continuity on
every strict closed time window `[a,b] ⊂ (0,T)`. -/
theorem lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (h : H1LiftDeriv2JointContinuousBefore u T) :
    ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b) := by
  intro a b ha hab hbT
  exact lapL2sq_continuousOn_Icc_of_liftDeriv2_jointContinuousOn
    (h.cont ha hab hbT)

end ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity
