import ShenWork.Paper2.IntervalChiNegH1InitialDerivativeFTC

/-!
# Initial-window H¹ derivative producers from assembled RHS data

This file records the non-circular direction from an independently produced
zero-start integrable H¹ identity RHS to the scalar derivative proxy.  It does
not use the full `H1IdentityRHSIntegrableBefore` package, bounded-before data,
or zero-start component continuity.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeFTC

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS

/-- Near-zero L¹ majorant for the assembled H¹ identity RHS.

This is weaker than zero-start component continuity: it only estimates the
already assembled scalar RHS on zero-start windows. -/
def H1IdentityRHSInitialWindowMajorantBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) : Prop :=
  ∃ G : ℝ → ℝ,
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      IntervalIntegrable G volume (0 : ℝ) b) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      AEStronglyMeasurable
        (H1IdentityRHSValue p u taxisX uvxx reactX)
        (volume.restrict (Set.Ioc (0 : ℝ) b))) ∧
    (∀ {b : ℝ}, 0 ≤ b → b < T →
      ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) b),
        ‖H1IdentityRHSValue p u taxisX uvxx reactX r‖ ≤ ‖G r‖)

/-- A near-zero majorant for the assembled H¹ identity RHS gives the explicit
initial-window RHS integrability input. -/
theorem H1IdentityRHSInitialWindowIntegrableBefore_of_majorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX := by
  rcases hMaj with ⟨G, hG_integrable, hRHS_meas, hRHS_bound⟩
  intro b hb0 hbT
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0]
  rw [IntegrableOn]
  have hG :
      Integrable G (volume.restrict (Set.Ioc (0 : ℝ) b)) := by
    simpa [IntegrableOn] using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mp
        (hG_integrable hb0 hbT)
  exact Integrable.mono' hG.norm
    (hRHS_meas hb0 hbT)
    (by simpa using hRHS_bound hb0 hbT)

/-- An independently integrable assembled H¹ identity RHS on every zero-start
window gives the pointwise derivative proxy from Task 83.

The H¹ identity is used only on `Ioc 0 b`; the endpoint value at zero is not
queried. -/
theorem H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hInitRHS : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowProxyBefore u T := by
  refine
    ⟨H1IdentityRHSValue p u taxisX uvxx reactX, ?_, ?_⟩
  · intro b hb0 hbT
    exact hInitRHS hb0 hbT
  · intro b _hb0 hbT r hr
    have hrT : r < T := lt_of_le_of_lt hr.2 hbT
    have hEnergy := hId r ⟨hr.1, hrT⟩
    unfold H1EnergyIdentity at hEnergy
    simpa [H1IdentityRHSValue] using hEnergy.deriv

/-- The same assembled-RHS initial-window data, lowered to the a.e. proxy
frontier from Task 86. -/
theorem H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSInitialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hInitRHS : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowAEProxyBefore u T :=
  H1EnergyDerivativeInitialWindowAEProxyBefore_of_proxy
    (H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
      hId hInitRHS)

/-- Assembled-RHS initial-window integrability gives the Task 83 derivative
majorant frontier. -/
theorem H1EnergyDerivativeInitialWindowMajorantBefore_of_identityRHSInitialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hInitRHS : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowMajorantBefore u T :=
  H1EnergyDerivativeInitialWindowMajorantBefore_of_aeProxy
    (H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSInitialWindow
      hId hInitRHS)

/-- Assembled-RHS initial-window integrability gives the scalar derivative
initial-window input consumed by the strict route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSInitialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hInitRHS : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_proxy
    (H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
      hId hInitRHS)

/-- An assembled-RHS majorant plus the pointwise H¹ identity gives the Task 83
pointwise derivative proxy. -/
theorem H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowProxyBefore u T :=
  H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
    hId
    (H1IdentityRHSInitialWindowIntegrableBefore_of_majorant hMaj)

/-- An assembled-RHS majorant plus the pointwise H¹ identity gives the Task 86
a.e. derivative proxy. -/
theorem H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowAEProxyBefore u T :=
  H1EnergyDerivativeInitialWindowAEProxyBefore_of_proxy
    (H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSMajorant
      hId hMaj)

/-- An assembled-RHS majorant plus the pointwise H¹ identity gives the Task 83
derivative majorant frontier. -/
theorem H1EnergyDerivativeInitialWindowMajorantBefore_of_identityRHSMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowMajorantBefore u T :=
  H1EnergyDerivativeInitialWindowMajorantBefore_of_aeProxy
    (H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSMajorant
      hId hMaj)

/-- An assembled-RHS majorant plus the pointwise H¹ identity gives the scalar
derivative initial-window input consumed by the strict route. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_proxy
    (H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSMajorant
      hId hMaj)

#print axioms H1IdentityRHSInitialWindowIntegrableBefore_of_majorant
#print axioms
  H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSInitialWindow
#print axioms
  H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSInitialWindow
#print axioms
  H1EnergyDerivativeInitialWindowMajorantBefore_of_identityRHSInitialWindow
#print axioms
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSInitialWindow
#print axioms
  H1EnergyDerivativeInitialWindowProxyBefore_of_identityRHSMajorant
#print axioms
  H1EnergyDerivativeInitialWindowAEProxyBefore_of_identityRHSMajorant
#print axioms
  H1EnergyDerivativeInitialWindowMajorantBefore_of_identityRHSMajorant
#print axioms
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSMajorant

end ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS
