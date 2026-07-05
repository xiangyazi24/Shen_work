import ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability

/-!
# Initial-window H¹ derivative producers

This file keeps construction-facing near-zero inputs for
`H1EnergyDerivativeInitialWindowIntegrableBefore` separate from the strict-time
RHS bridge.  The frontiers here are scalar: they avoid zero-start `lapL2sq`
continuity and do not use downstream boundedness.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer

/-- Initial-window integrable proxy for the scalar derivative of H¹ energy.

The proxy may be an explicit construction-level RHS or an abstract derivative
field from an integrated H¹ energy identity. -/
def H1EnergyDerivativeInitialWindowProxyBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∃ g : ℝ → ℝ,
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      IntervalIntegrable g volume (0 : ℝ) b) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ r, r ∈ Set.Ioc (0 : ℝ) b →
        deriv (H1energy u) r = g r)

/-- An integrable derivative proxy gives the scalar derivative initial-window
input consumed by the strict H¹ RHS route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_proxy
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hProxy : H1EnergyDerivativeInitialWindowProxyBefore u T) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T := by
  rcases hProxy with ⟨g, hg_integrable, hDeriv_eq⟩
  intro b hb0 hbT
  exact H1_deriv_intervalIntegrable_of_eq_on_Ioc
    (u := u) (D := g) hb0
    (hg_integrable hb0 hbT)
    (hDeriv_eq hb0 hbT)

/-- Near-zero L¹ majorant for the scalar derivative of H¹ energy.

This is an estimate-level frontier.  It does not assert zero-start `lapL2sq`
continuity or componentwise H² trace data. -/
def H1EnergyDerivativeInitialWindowMajorantBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∃ G : ℝ → ℝ,
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      IntervalIntegrable G volume (0 : ℝ) b) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      AEStronglyMeasurable
        (fun r => deriv (H1energy u) r)
        (volume.restrict (Set.Ioc (0 : ℝ) b))) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) b),
        ‖deriv (H1energy u) r‖ ≤ ‖G r‖)

/-- A near-zero L¹ majorant gives the scalar derivative initial-window input
consumed by the strict H¹ RHS route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_majorant
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hMaj : H1EnergyDerivativeInitialWindowMajorantBefore u T) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T := by
  rcases hMaj with ⟨G, hG_integrable, hDeriv_meas, hDeriv_bound⟩
  intro b hb0 hbT
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0]
  rw [IntegrableOn]
  have hG :
      Integrable G (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
    simpa [IntegrableOn] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mp
        (hG_integrable hb0 hbT)
  exact Integrable.mono' hG.norm
    (hDeriv_meas hb0 hbT)
    (by simpa using hDeriv_bound hb0 hbT)

#print axioms H1EnergyDerivativeInitialWindowIntegrableBefore_of_proxy
#print axioms H1EnergyDerivativeInitialWindowIntegrableBefore_of_majorant

end ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer
