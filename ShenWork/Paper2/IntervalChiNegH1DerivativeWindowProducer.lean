import ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer
import ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer

/-!
# H¹ derivative-window producer

This file splits full H¹ scalar derivative integrability into the same two
pieces used by the strict route: positive-start windows are produced from the
strict explicit-RHS component data, while zero-start windows remain the scalar
initial-window input.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge
open ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1DerivativeWindowProducer

/-- Derivative integrability of the scalar H¹ energy on windows whose left
endpoint is strictly positive. -/
def H1EnergyDerivativePositiveStartWindowIntegrableBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b

/-- Derivative integrability of the scalar H¹ energy on every closed
pre-horizon window with nonnegative left endpoint. -/
def H1EnergyDerivativeWindowIntegrableBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b

/-- Strict component continuity plus the pointwise H¹ identity produces
positive-start derivative-window integrability. -/
theorem H1EnergyDerivativePositiveStartWindowIntegrableBefore_of_componentsStrictBefore
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativePositiveStartWindowIntegrableBefore u T := by
  intro a b ha hab hbT
  have hRHSCont :
      ContinuousOn
        (H1IdentityRHSValue p u taxisX uvxx reactX) (Set.Icc a b) :=
    H1IdentityRHS_continuousOn_Icc_of_components
      (hStrict.lap_cont ha hab hbT)
      (hStrict.taxis_cont ha hab hbT)
      (hStrict.uvxx_cont ha hab hbT)
      (hStrict.react_cont ha hab hbT)
  have hRHSInt :
      IntervalIntegrable
        (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b :=
    hRHSCont.intervalIntegrable_of_Icc hab
  refine H1_deriv_intervalIntegrable_of_eq_on_Ioc
    (u := u) (D := H1IdentityRHSValue p u taxisX uvxx reactX)
    hab hRHSInt ?_
  intro r hr
  have hr0 : 0 < r := lt_trans ha hr.1
  have hrT : r < T := lt_of_le_of_lt hr.2 hbT
  have hEnergy := hId r ⟨hr0, hrT⟩
  unfold H1EnergyIdentity at hEnergy
  simpa [H1IdentityRHSValue] using hEnergy.deriv

/-- Full derivative-window integrability from the zero-start scalar input plus
positive-start derivative-window integrability. -/
theorem H1EnergyDerivativeWindowIntegrableBefore_of_initial_and_positiveStart
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hInit : H1EnergyDerivativeInitialWindowIntegrableBefore u T)
    (hPos : H1EnergyDerivativePositiveStartWindowIntegrableBefore u T) :
    H1EnergyDerivativeWindowIntegrableBefore u T := by
  intro a b ha hab hbT
  by_cases hzero : a = 0
  · subst a
    exact hInit hab hbT
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    exact hPos ha_pos hab hbT

/-- Strict component continuity plus scalar zero-start derivative integrability
produces the full derivative-window package. -/
theorem H1EnergyDerivativeWindowIntegrableBefore_of_componentsStrictBefore_initial
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hInit : H1EnergyDerivativeInitialWindowIntegrableBefore u T) :
    H1EnergyDerivativeWindowIntegrableBefore u T :=
  H1EnergyDerivativeWindowIntegrableBefore_of_initial_and_positiveStart
    hInit
    (H1EnergyDerivativePositiveStartWindowIntegrableBefore_of_componentsStrictBefore
      hId hStrict)

/-- Scalar regularity from `u_xx` L¹-continuity plus the strict-RHS/initial
derivative split. -/
theorem H1ScalarRegularityBefore_of_uxxL1Cont_componentsStrictBefore_initial
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hInit : H1EnergyDerivativeInitialWindowIntegrableBefore u T) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_uxxL1Cont_and_hderivInt
    hsol hUxxL1 hcont0
    (H1EnergyDerivativeWindowIntegrableBefore_of_componentsStrictBefore_initial
      hId hStrict hInit)

#print axioms
  H1EnergyDerivativePositiveStartWindowIntegrableBefore_of_componentsStrictBefore
#print axioms H1EnergyDerivativeWindowIntegrableBefore_of_initial_and_positiveStart
#print axioms
  H1EnergyDerivativeWindowIntegrableBefore_of_componentsStrictBefore_initial
#print axioms
  H1ScalarRegularityBefore_of_uxxL1Cont_componentsStrictBefore_initial

end ShenWork.Paper2.IntervalChiNegH1DerivativeWindowProducer
