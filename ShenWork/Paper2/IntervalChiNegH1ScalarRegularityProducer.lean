import ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
import ShenWork.Paper2.IntervalChiNegH1EnergyIdentity

/-!
# H¹ scalar regularity producer

This file packages the honest part of the H¹ scalar regularity frontier:
`u_xx` L¹-continuity in time gives closed-window continuity of `H1energy`,
provided the time-zero right-continuity is supplied explicitly.  Derivative
interval-integrability remains a separate scalar FTC input.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer

/-- `u_xx` L¹ time-continuity gives `ContinuousOn` of the H¹ energy on every
closed pre-horizon interval, once the right-continuity at `t = 0` is supplied.
-/
theorem H1energy_continuousOn_before_of_uxxL1Cont
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0) :
    ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (H1energy u) (Set.Icc a b) := by
  intro a b ha _hab hb x hx
  by_cases hx0 : x = 0
  · subst x
    have hsub : Set.Icc a b ⊆ Set.Ici (0 : ℝ) := by
      intro y hy
      exact le_trans ha hy.1
    exact hcont0.mono_left (nhdsWithin_mono 0 hsub)
  · have hx_nonneg : 0 ≤ x := le_trans ha hx.1
    have hxpos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
    have hxT : x < T := lt_of_le_of_lt hx.2 hb
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) T := ⟨hxpos, hxT⟩
    have huxx_raw := hUxxL1 x hxpos hxT
    have huxx :
        ∀ ε > 0, ∃ δ > 0,
          ∀ s, |s - x| < δ → s ∈ Set.Ioo (0 : ℝ) T →
            ∫ y in (0 : ℝ)..1,
              ‖liftDeriv2 u s y - liftDeriv2 u x y‖ ≤ ε := by
      simpa [H1UxxL1ContBefore, liftDeriv2] using huxx_raw
    exact
      (H1energy_hasDerivAt_of_uxxL1Cont hsol hxIoo huxx).continuousAt.continuousWithinAt

/-- Package separately supplied scalar continuity and derivative-integrability
fields into the H¹ scalar regularity record. -/
theorem H1ScalarRegularityBefore_of_hcont_and_hderivInt
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hcont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (H1energy u) (Set.Icc a b))
    (hderivInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b) :
    H1ScalarRegularityBefore u T where
  hcont := hcont
  hderivInt := hderivInt

#print axioms H1energy_continuousOn_before_of_uxxL1Cont
#print axioms H1ScalarRegularityBefore_of_hcont_and_hderivInt

end ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
