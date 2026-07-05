import ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer

/-!
# Strict-slab representative transfer for `liftDeriv2`

This file fixes the exact seam shape for producing the H¹ `u_xx` regularity
input: a jointly continuous strict-slab representative plus an `EqOn` proof
against `liftDeriv2`.  Endpoint equality remains an explicit hypothesis.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer

/-- If `liftDeriv2 u` has a continuous strict-slab representative `F`, then the
current strict-positive-time joint-continuity package follows. -/
theorem H1LiftDeriv2JointContinuousBefore_of_strictSlab_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1LiftDeriv2JointContinuousBefore u T := by
  refine ⟨?_⟩
  intro a b ha hab hbT
  exact (hF (a := a) (b := b) ha hab hbT).congr
    (fun z hz => hEq (a := a) (b := b) ha hab hbT hz)

/-- The same strict-slab representative immediately discharges the current
`u_xx` L¹-continuity frontier. -/
theorem H1UxxL1ContBefore_of_strictSlab_eq_continuous
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEq : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) :
    H1UxxL1ContBefore u T :=
  H1UxxL1ContBefore_of_liftDeriv2_jointContinuousBefore
    (H1LiftDeriv2JointContinuousBefore_of_strictSlab_eq_continuous
      (u := u) (T := T) (F := F) hF hEq)

section AxiomAudit

#print axioms H1LiftDeriv2JointContinuousBefore_of_strictSlab_eq_continuous
#print axioms H1UxxL1ContBefore_of_strictSlab_eq_continuous

end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
