import ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer

/-!
# Initial-window H¹ derivative FTC adapters

This file gives source-facing inputs for the zero-start scalar H¹ derivative
frontier.  It accepts the a.e. derivative identities produced by an integrated
energy/FTC argument and lowers them to the Task 83 majorant and integrability
interfaces.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1InitialDerivativeFTC

/-- Initial-window a.e. integrable proxy for the scalar derivative of H¹
energy.  This is the natural output shape of an integrated H¹ energy/FTC proof:
the derivative identity only needs to hold a.e. on each zero-start window. -/
def H1EnergyDerivativeInitialWindowAEProxyBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∃ g : ℝ → ℝ,
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      IntervalIntegrable g volume (0 : ℝ) b) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) b),
        deriv (H1energy u) r = g r)

/-- The pointwise proxy from Task 83 is a special case of the a.e. proxy. -/
theorem H1EnergyDerivativeInitialWindowAEProxyBefore_of_proxy
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hProxy : H1EnergyDerivativeInitialWindowProxyBefore u T) :
    H1EnergyDerivativeInitialWindowAEProxyBefore u T := by
  rcases hProxy with ⟨g, hg_integrable, hDeriv_eq⟩
  refine ⟨g, hg_integrable, ?_⟩
  intro b hb0 hbT
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
  exact Filter.Eventually.of_forall fun r hr =>
    hDeriv_eq hb0 hbT r hr

/-- An a.e. integrable derivative proxy gives the existing Task 83 majorant
frontier, using the proxy itself as the majorant. -/
theorem H1EnergyDerivativeInitialWindowMajorantBefore_of_aeProxy
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hProxy : H1EnergyDerivativeInitialWindowAEProxyBefore u T) :
    H1EnergyDerivativeInitialWindowMajorantBefore u T := by
  rcases hProxy with ⟨g, hg_integrable, hDeriv_eq⟩
  refine ⟨g, hg_integrable, ?_, ?_⟩
  · intro b hb0 hbT
    have hg_restrict :
        Integrable g (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
      simpa [IntegrableOn] using
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mp
          (hg_integrable hb0 hbT)
    have hEq :
        (fun r => deriv (H1energy u) r)
          =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) b)] g :=
      hDeriv_eq hb0 hbT
    exact (aestronglyMeasurable_congr hEq).mpr
      hg_restrict.aestronglyMeasurable
  · intro b hb0 hbT
    exact (hDeriv_eq hb0 hbT).mono fun r hr => by
      rw [hr]

/-- Direct adapter from an a.e. initial-window derivative proxy to the scalar
derivative integrability input consumed by the strict route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_aeProxy
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hProxy : H1EnergyDerivativeInitialWindowAEProxyBefore u T) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_majorant
    (H1EnergyDerivativeInitialWindowMajorantBefore_of_aeProxy hProxy)

/-- Integrated initial-window H¹ energy identity frontier.

Only `g_intervalIntegrable` and `deriv_eq_ae` are needed for the current
near-zero bottleneck; `energy_eq` records the actual FTC identity expected from
the future analytic source theorem. -/
def H1EnergyInitialWindowFTCBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∃ g : ℝ → ℝ,
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      IntervalIntegrable g volume (0 : ℝ) b) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) b),
        deriv (H1energy u) r = g r) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      H1energy u b - H1energy u 0 = ∫ r in (0 : ℝ)..b, g r)

/-- Extract the a.e. derivative proxy from the integrated H¹ energy FTC
package. -/
theorem H1EnergyDerivativeInitialWindowAEProxyBefore_of_initialWindowFTC
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hFTC : H1EnergyInitialWindowFTCBefore u T) :
    H1EnergyDerivativeInitialWindowAEProxyBefore u T := by
  rcases hFTC with ⟨g, hg_integrable, hDeriv_eq, _hEnergy_eq⟩
  exact ⟨g, hg_integrable, hDeriv_eq⟩

/-- Integrated H¹ energy FTC data give the existing Task 83 majorant frontier. -/
theorem H1EnergyDerivativeInitialWindowMajorantBefore_of_initialWindowFTC
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hFTC : H1EnergyInitialWindowFTCBefore u T) :
    H1EnergyDerivativeInitialWindowMajorantBefore u T :=
  H1EnergyDerivativeInitialWindowMajorantBefore_of_aeProxy
    (H1EnergyDerivativeInitialWindowAEProxyBefore_of_initialWindowFTC hFTC)

/-- Integrated H¹ energy FTC data give the zero-start scalar derivative
integrability input consumed by the strict route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_initialWindowFTC
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hFTC : H1EnergyInitialWindowFTCBefore u T) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_aeProxy
    (H1EnergyDerivativeInitialWindowAEProxyBefore_of_initialWindowFTC hFTC)

#print axioms H1EnergyDerivativeInitialWindowAEProxyBefore_of_proxy
#print axioms H1EnergyDerivativeInitialWindowMajorantBefore_of_aeProxy
#print axioms H1EnergyDerivativeInitialWindowIntegrableBefore_of_aeProxy
#print axioms H1EnergyDerivativeInitialWindowAEProxyBefore_of_initialWindowFTC
#print axioms H1EnergyDerivativeInitialWindowMajorantBefore_of_initialWindowFTC
#print axioms H1EnergyDerivativeInitialWindowIntegrableBefore_of_initialWindowFTC

end ShenWork.Paper2.IntervalChiNegH1InitialDerivativeFTC
