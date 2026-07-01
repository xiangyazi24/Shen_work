# Q3002 (shen1) — reducing `energyWindowFTC` in the regular-energy coefficient-gap route

Repo: `xiangyazi24/Shen_work`  
Audited pushed HEAD: `c6694aa8c2a9d89aa7b2a2e30569602a7b7c934d` (`Add Paper2 coefficient-gap frontier surface`)  
Scope: source-grounded Lean audit/design for the next additive route reducing the `energyWindowFTC` field in the regular-energy coefficient-gap residuals.  
Constraint respected: do **not** touch `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.  
Additive only: no deletion/replacement of existing regular-energy, integrated-step, lower/upper, or actual-linear routes.

## Executive answer

The smallest honest next route is **not** “FTC from classical continuity alone.”  The existing API already proves the routine FTC wiring, but it still needs genuine derivative-window integrability.  The next additive surface should split the current monolithic field

```lean
IntegratedMoserEnergyWindowFTC intervalDomain u T p0
```

into the two fields that the proved local producer actually consumes:

```lean
IntervalDomainPowerEnergyEndpointContinuity u T p0
IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0
```

This is the source-grounded local theorem already in `P3MoserEnergyContinuity`:

```lean
intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
```

Then, separately, global-classical wrappers can reduce the derivative-window integrability field to **positive-start windows proved from global classical regularity** plus an **honest initial-window residual**.  The endpoint field similarly reduces to a right endpoint proved from global classical regularity plus an **honest left-endpoint residual**.

So the next feasible additive patch should be two-layered:

1. Add a small `FTCLocalData` packaging structure in `P3MoserEnergyContinuity.lean`.
2. Add a residual sibling in `IntervalDomainMoserLadderAtoms.lean` that replaces `energyWindowFTC` with `energyWindowFTCData` and converts to the existing `IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals`.

This reduces the field without pretending the remaining endpoint/initial-window analytic inputs are solved.

## What currently produces `IntegratedMoserEnergyWindowFTC`?

### Core target and analytic derivative frontier

`P3MoserIntegratedClosure.lean` defines:

```lean
structure IntegratedMoserEnergyWindowFTC
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  deriv_intervalIntegrable : ...
  window_ftc : ...
```

and the derivative-only frontier:

```lean
def IntegratedMoserEnergyDerivativeWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop := ...
```

This confirms that window FTC is not just continuity; it explicitly carries derivative interval-integrability.

### Local producer

`P3MoserEnergyContinuity.lean` already proves:

```lean
theorem
  intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0)
    (hderivInt :
      IntegratedMoserEnergyDerivativeWindowIntegrability
        intervalDomain u T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0
```

This is the canonical local reduction of `energyWindowFTC`.

### Global-classical producers

`P3MoserEnergyContinuity.lean` also already proves these increasingly PDE-shaped FTC producers:

```lean
intervalDomain_integratedMoserEnergyWindowFTC_of_global_endpoint_powerInit
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_powerInit
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeCombined
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeTerms
```

The key derivative-integrability bridges are:

```lean
intervalDomain_derivativeWindowIntegrability_of_global_classical_initial
intervalDomain_derivativeWindowIntegrability_of_global_powerDerivIntegral
intervalDomain_derivativeWindowIntegrability_of_global_weightedTimeTerm
intervalDomain_derivativeWindowIntegrability_of_global_pdeTerms
```

The key endpoint bridge is:

```lean
intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
```

and the trace/anchoring source for the left endpoint is:

```lean
intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
```

## Can global classical regularity plus existing initial-window packages remove the field?

**Yes, but not for free.**  Global classical regularity supplies:

* positive-start derivative windows via
  `intervalDomain_derivativePositiveStartWindowIntegrability_of_global_classical`;
* right-endpoint power-energy continuity via the longer-horizon interior continuity argument in
  `intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical`.

But two honest residuals remain unless the trajectory is re-anchored and an initial-window estimate is supplied:

1. **Left endpoint power-energy continuity**:

   ```lean
   IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
   ```

   This is not a consequence of the finite-horizon `IsPaper2ClassicalSolution` API.  It can be produced for the re-anchored representative from initial trace + paper-positive datum + global classical regularity:

   ```lean
   intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
   ```

2. **Initial-window derivative integrability**, in one of the already-defined residual forms:

   ```lean
   IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0
   IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0
   IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0
   IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0
   ```

   The thinnest PDE-shaped input is currently

   ```lean
   IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0
   ```

   because the componentwise `IntervalDomainLpPDETermInitialWindowIntegrability` implies it, and the weighted-time-term bridge goes both ways around the combined scalar profile on the initial window.

Therefore, **global classical regularity plus existing initial-window packages does wire the FTC**, but an honest initial-window residual remains.  There is no no-residual route from classical regularity alone.

## Recommended additive code: `P3MoserEnergyContinuity.lean`

### Placement

Add this in:

```text
ShenWork/PDE/P3MoserEnergyContinuity.lean
```

immediately after the theorem:

```lean
intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
```

and before the strict-window derivative-integrability block.

### Exact code

```lean
/-- Local data sufficient to produce the abstract Moser-energy window FTC on the
interval domain.

This packages the two inputs consumed by
`intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable`.
It deliberately does not claim that classical regularity alone provides them. -/
structure IntervalDomainIntegratedMoserEnergyWindowFTCLocalData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0
  derivativeWindowIntegrability :
    IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0

/-- Produce the interval-domain Moser-energy window FTC from the packaged local
endpoint-continuity and derivative-integrability data. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_localData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hdata : IntervalDomainIntegratedMoserEnergyWindowFTCLocalData u T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    hsol hdata.endpointEnergy hdata.derivativeWindowIntegrability

/-- Global-classical, initial-window PDE data sufficient to produce the local FTC
data package.

The remaining assumptions are exactly the honest left-endpoint continuity and
initial-window PDE-side integrability residuals.  Positive-start derivative
windows and the right endpoint are produced from global classical regularity. -/
structure IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop where
  atZero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
  pdeCombinedInitial :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0

/-- Convert global-classical initial-window PDE data to the local FTC data
package. -/
theorem
    intervalDomain_integratedMoserEnergyWindowFTCLocalData_of_globalPDEInitialData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata :
      IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
        params u v T p0) :
    IntervalDomainIntegratedMoserEnergyWindowFTCLocalData u T p0 where
  endpointEnergy :=
    intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hT hdata.atZero
  derivativeWindowIntegrability :=
    intervalDomain_derivativeWindowIntegrability_of_global_weightedTimeTerm
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal
      (intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial
        (params := params) (T := T) (p0 := p0) (u := u) (v := v)
        hglobal hdata.pdeCombinedInitial)

/-- Direct FTC producer from global-classical initial-window PDE data. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hdata :
      IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
        params u v T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyWindowFTC_of_localData
    (params := params) (T := T) (p0 := p0) (u := u) (v := v)
    (hglobal.classical hT)
    (intervalDomain_integratedMoserEnergyWindowFTCLocalData_of_globalPDEInitialData
      (params := params) (T := T) (p0 := p0) (u := u) (v := v)
      hglobal hT hdata)
```

### `#print axioms` lines

Add near the existing axiom-audit lines in `P3MoserEnergyContinuity.lean`:

```lean
#print axioms intervalDomain_integratedMoserEnergyWindowFTC_of_localData
#print axioms
  intervalDomain_integratedMoserEnergyWindowFTCLocalData_of_globalPDEInitialData
#print axioms intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData
```

## Recommended additive code: `IntervalDomainMoserLadderAtoms.lean`

### Placement

After the pending local structure:

```lean
end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals
```

add the following sibling surface.  If needed, add this open line near the existing opens:

```lean
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

No new import should be necessary if `P3MoserRegularityProducer` is already imported, but adding a direct import is also harmless and clearer:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
```

### Exact code

```lean
/-- Regular-energy coefficient-gap residuals with the window-FTC field reduced to
local endpoint-continuity and derivative-window-integrability data. -/
structure IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTCData :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserEnergyWindowFTCLocalData u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals

/-- Collapse the local-FTC-data residual surface to the existing regular-energy
coefficient-gap residual package. -/
def to_regularEnergyCoeffGapResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  classicalRegularity := h.classicalRegularity
  energyWindowFTC := fun hsol hcross hboot =>
    intervalDomain_integratedMoserEnergyWindowFTC_of_localData
      hsol (h.energyWindowFTCData hsol hcross hboot)
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Convert to the canonical integrated-step residual package through the existing
regular-energy coefficient-gap residual. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p :=
  h.to_regularEnergyCoeffGapResiduals.to_integratedStepResiduals

/-- Convert to the old mass/Lp/smoothing route residual package. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_regularEnergyCoeffGapResiduals.to_routeResiduals

/-- A-priori bound from the local-FTC-data regular-energy coefficient-gap route. -/
def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_regularEnergyCoeffGapResiduals.aprioriBound

end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals
```

### `#print axioms` lines

Add near the pending regular-energy residual axiom audit in `IntervalDomainMoserLadderAtoms.lean`:

```lean
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals.to_regularEnergyCoeffGapResiduals
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals.to_routeResiduals
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals.aprioriBound
```

## Why I do not recommend a “global-only” ladder residual now

One might try to replace `energyWindowFTCData` by fields like:

```lean
IsPaper2GlobalClassicalSolution intervalDomain p u v
IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
IntervalDomainLpPDECombinedInitialWindowIntegrability p u v T p0
```

inside the mass/Lp/smoothing residual.  This is typeable if you add a field that upgrades every local `hsol` to a global classical solution, but it is not the right next route: the mass/Lp/smoothing residual package is a finite-horizon a-priori package and its canonical consumers only pass local `IsPaper2ClassicalSolution intervalDomain p T u v`.  Requiring a global solution there would be mathematically circular for the global-existence route.

The layer-safe approach is:

* keep the ladder residual local and reduce `energyWindowFTC` to local FTC data;
* use the global-classical initial-window data wrapper where the caller genuinely has a global solution or a re-anchored global representative;
* leave initial-window integrability as an explicit frontier until a producer proves it.

## Build targets

For the FTC packaging patch:

```bash
lake build ShenWork.PDE.P3MoserEnergyContinuity
```

For the ladder residual patch after the pending regular-energy residual lands:

```bash
lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
```

Combined campaign target:

```bash
lake build \
  ShenWork.PDE.P3MoserEnergyContinuity \
  ShenWork.PDE.IntervalDomainMoserLadderAtoms \
  ShenWork.Paper2.IntervalDomainStatementAssembly \
  ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
```

## Smallest viable alternative

If the pending `IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals` has not landed yet, add only the `P3MoserEnergyContinuity.lean` local-data packaging first.  It is independent of the pending ladder surface and immediately documents the honest reduction:

```lean
IntegratedMoserEnergyWindowFTC
  ← endpoint power-energy continuity
  + derivative-window integrability
```

Then, after the pending regular-energy residual lands, add the ladder sibling `IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals` exactly as above.
