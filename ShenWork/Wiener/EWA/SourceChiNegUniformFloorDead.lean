/-
  ShenWork/Wiener/EWA/SourceChiNegUniformFloorDead.lean

  Machine-visible dead-route markers for the all-PPID strict-negative routes
  whose inputs require a common positive datum floor depending only on a sup
  bound.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegUniformBridgeC3Obstruction
import ShenWork.Wiener.EWA.SourceChiNegDatumWienerDataObstruction

namespace ShenWork.EWA

/-- The C3/Neumann uniform-floor residual cannot be a route to the all-PPID
chi-negative headline, because its premise is uninhabited. -/
theorem no_allPPID_route_via_uniformFlooredC3NeumannData (p : CM2Params) :
    ¬ UniformFlooredC3NeumannData p :=
  not_uniformFlooredC3NeumannData p

/-- The monolithic datum-Wiener residual cannot be a route to the all-PPID
chi-negative headline, because its premise is uninhabited. -/
theorem no_allPPID_route_via_datumWienerData (p : CM2Params) :
    ¬ DatumWienerData p :=
  not_datumWienerData p

end ShenWork.EWA

#print axioms ShenWork.EWA.no_allPPID_route_via_uniformFlooredC3NeumannData
#print axioms ShenWork.EWA.no_allPPID_route_via_datumWienerData
