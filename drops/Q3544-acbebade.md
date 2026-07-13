ANSWER Q3544 acbebade

# Q3544 audit: zero-start primitive frontier for the Paper2 physical H¹ route

Audited current main `d015613d`. This is an audit only. The active sqrt-bound work is out of scope except for noting that `H1PhysicalRHSSqrtBoundsBefore` remains a separate dependency.

## Status check

`ShenWork/Paper2/IntervalChiNegH1PhysicalIdentityRouteC.lean` now contains the Route-C substitution machinery and the identity producer:

```lean
H1PhysicalRHSRouteCSubstitutionBefore
H1PhysicalRHSRouteCSubstitutionAt_of_classicalSolution
H1PhysicalRHSRouteCSubstitutionBefore_of_classicalSolution
H1PhysicalRHSIdentityBefore_of_classical_uxxL1Cont_routeCSubstitution
H1PhysicalRHSIdentityBefore_of_classicalSolution
```

So the physical identity is no longer the blocker. The remaining non-sqrt route input under audit here is `H1ZeroStartPhysicalPrimitiveDataBefore`.

## Exact primitive package

`H1ZeroStartPhysicalPrimitiveDataBefore` is defined in `ShenWork/Paper2/IntervalChiNegH1ZeroStartComponents.lean`. Its fields are:

```lean
u_cont0 : ∀ {b}, 0 ≤ b → b < T →
  ContinuousOn (Function.uncurry (fun t x => intervalDomainLift (u t) x))
    (Set.Icc 0 b ×ˢ Set.Icc 0 1)

v_cont0 : ∀ {b}, 0 ≤ b → b < T →
  ContinuousOn (Function.uncurry (fun t x => intervalDomainLift (v t) x))
    (Set.Icc 0 b ×ˢ Set.Icc 0 1)

ux_cont0 : ∀ {b}, 0 ≤ b → b < T →
  ContinuousOn (Function.uncurry (fun t x => deriv (intervalDomainLift (u t)) x))
    (Set.Icc 0 b ×ˢ Set.Icc 0 1)

vx_cont0 : ∀ {b}, 0 ≤ b → b < T →
  ContinuousOn (Function.uncurry (fun t x => deriv (intervalDomainLift (v t)) x))
    (Set.Icc 0 b ×ˢ Set.Icc 0 1)

u_pos0 : ∀ {b}, 0 ≤ b → b < T →
  ∀ z ∈ Set.Icc 0 b ×ˢ Set.Icc 0 1,
    0 < Function.uncurry (fun t x => intervalDomainLift (u t) x) z

v_nonneg0 : ∀ {b}, 0 ≤ b → b < T →
  ∀ z ∈ Set.Icc 0 b ×ˢ Set.Icc 0 1,
    0 ≤ Function.uncurry (fun t x => intervalDomainLift (v t) x) z

time_cont0 : ∀ {b}, 0 ≤ b → b < T →
  ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
    (Set.Icc 0 b ×ˢ Set.Icc 0 1)

eqInterior0 : ∀ {b}, 0 ≤ b → b < T →
  Set.EqOn
    (Function.uncurry (fun t x => liftDeriv2 u t x))
    (Function.uncurry
      (liftDeriv2PhysicalRHSWithChemRep p u
        (liftChemotaxisDivPhysicalRep p u v)))
    (Set.Icc 0 b ×ˢ Set.Ioo 0 1)
```

The file already explains the intended split: primitive zero-start continuity of `u`, `v`, `u_x`, and `v_x` algebraically supplies the physical chemotaxis representative; the genuinely analytic inputs remain `time_cont0` and `eqInterior0`.

## Existing producers and near-producers

### What is already reduced

`IntervalChiNegH1ZeroStartComponents.lean` proves:

```lean
liftChemotaxisDivPhysicalRep_continuousOn_zeroSlab_of_primitives
H1ZeroStartPhysicalRHSDataBefore_of_zeroStartPrimitiveData
H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPrimitiveData
```

These are reducers from the primitive package. They do not produce the primitive package itself.

`IntervalChiNegH1ZeroSlabPhysicalRHS.lean` contains the lower-level zero-slab representative interfaces:

```lean
H1ZeroStartPhysicalRHSDataBefore
H1ZeroStartPhysicalRHSDataBefore_of_lift_continuous_positive
H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHSData
H1LiftDeriv2ZeroSlabRepBefore_of_zeroStartPhysicalRHS_lift_positive
```

This file explicitly says it does not produce zero-time H²/lap trace data; it packages a continuous zero-start physical RHS representative plus interior equality to `liftDeriv2`.

`IntervalChiNegH1PhysicalClassicalContinuity.lean` supplies strict-positive-time analogues only, e.g.

```lean
liftDeriv2PhysicalRHSWithChemRep_continuousOn_strictSlab_of_classicalSolution
liftDeriv2_eq_liftDeriv2PhysicalRHSWithChemRep_strictSlab_interior_of_classicalSolution
H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
H1PhysicalLogisticReactionPart_continuousOn_strictSlab_of_classicalSolution
```

Their hypotheses include `0 < a`; they do not provide closed-time-at-zero data.

`IntervalChiNegH1InitialContinuity.lean` gives H¹-energy endpoint data such as:

```lean
H1InitialEndpointData
H1energy_continuousWithinAt_zero_of_initialEndpointData
H1energy_continuousOn_before_of_uxxL1Cont_initialEndpointData
```

These are scalar H¹ energy statements, not zero-slab continuity for `u`, `v`, `u_x`, `v_x`, `u_t`, or `u_xx`.

### What is not currently found

I did not find an exact theorem producing:

```lean
H1ZeroStartPhysicalPrimitiveDataBefore p u v T
```

from `IsPaper2ClassicalSolution`, `InitialTrace`, `PaperPositiveInitialDatum`/`PositiveInitialDatum`, `H1InitialEndpointData`, or the current positivity APIs.

This is expected: `IsPaper2ClassicalSolution` is explicitly positive-time. In `Statements.lean`, its regularity, positivity, nonnegativity, PDE, and Neumann fields are all for `0 < t` and `t < T`. That cannot by itself give continuity or PDE identities on `[0,b]` including `t = 0`.

## Field-by-field classification

### Likely routine wrappers, once stronger zero-start assumptions are supplied

These are mostly algebra/packaging if the actual zero-start continuity facts exist:

- `liftChemotaxisDivPhysicalRep_continuousOn_zeroSlab_of_primitives`: already proves chem representative continuity from `u_cont0`, `v_cont0`, `ux_cont0`, `vx_cont0`, `u_pos0`, and `v_nonneg0`.
- `logisticReaction_continuousOn_zeroSlab_of_lift_continuous_positive`: already proves reaction continuity from `u_cont0` plus `u_pos0`.
- `H1ZeroStartPhysicalRHSDataBefore_of_zeroStartPrimitiveData`: already packages primitive data into the lower zero-start physical RHS package.

### Genuine zero-start regularity / compatibility fields

These are not supplied by strict classical regularity:

- `u_cont0`: needs closed-time trace/joint continuity of `u` up to `t=0`, not merely pointwise `InitialTrace` unless upgraded to joint `ContinuousOn` on `[0,b]×[0,1]`.
- `v_cont0`: needs zero-time compatibility for the elliptic component `v`, likely resolver continuity as `t → 0` plus a specified/compatible `v 0`; `InitialTrace` usually speaks about `u`, not `v`.
- `ux_cont0`: needs C¹ spatial trace of `u` at `t=0`; this is stronger than ordinary initial trace and stronger than H¹ energy endpoint convergence.
- `vx_cont0`: needs C¹ spatial trace of the elliptic component at `t=0`; likely requires resolver-gradient continuity from the initial `u` trace and a compatible `v 0`.
- `time_cont0`: needs closed-time continuity of `u_t` on `[0,b]×[0,1]`. This is a parabolic regularity/PDE compatibility condition at the initial time, not present in `IsPaper2ClassicalSolution`.
- `eqInterior0`: needs the PDE equality `u_xx = u_t + χ₀ * chemRep - reaction` on the zero-start slab, including `t=0` and `x∈(0,1)`. Current PDE fields only hold for `0<t<T`. This is the strongest compatibility requirement: it is essentially an initial-time PDE compatibility/H² statement.

### Positivity/nonnegativity fields

- `u_pos0` may be routine if one has `u_cont0`, a compatible zero slice, and a strictly positive initial datum with a uniform floor. But current `IsPaper2ClassicalSolution.u_pos'` only gives `t>0`; it says nothing at `t=0`.
- `v_nonneg0` may be routine if one has `v_cont0` and a compatible nonnegative elliptic initial `v`. But that compatibility is not currently a standard `InitialTrace` field.

## Circularity warning

Do not derive these zero-start primitive fields from `IsPaper2BoundedBefore` or the H¹ physical route itself. That would be circular: the primitive package is currently used upstream to produce the zero-window component-square/spatial-Young data consumed by the H¹ physical route.

Similarly, using the route’s bounded-before result to get `u_x`, `v_x`, or `u_t` zero-start regularity would not be a valid source-side producer.

## Smaller honest interface

The current primitive package is source-facing and adequate, but it is stronger than some downstream uses. A useful split would separate primitive continuity/positivity from the actual PDE-at-zero seam.

Recommended split:

```lean
structure H1ZeroStartPhysicalPrimitiveContinuityBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  u_cont0 : ∀ {b}, 0 ≤ b → b < T →
    ContinuousOn (Function.uncurry (fun t x => intervalDomainLift (u t) x))
      (Set.Icc 0 b ×ˢ Set.Icc 0 1)
  v_cont0 : ∀ {b}, 0 ≤ b → b < T →
    ContinuousOn (Function.uncurry (fun t x => intervalDomainLift (v t) x))
      (Set.Icc 0 b ×ˢ Set.Icc 0 1)
  ux_cont0 : ∀ {b}, 0 ≤ b → b < T →
    ContinuousOn (Function.uncurry (fun t x => deriv (intervalDomainLift (u t)) x))
      (Set.Icc 0 b ×ˢ Set.Icc 0 1)
  vx_cont0 : ∀ {b}, 0 ≤ b → b < T →
    ContinuousOn (Function.uncurry (fun t x => deriv (intervalDomainLift (v t)) x))
      (Set.Icc 0 b ×ˢ Set.Icc 0 1)
  u_pos0 : ∀ {b}, 0 ≤ b → b < T →
    ∀ z ∈ Set.Icc 0 b ×ˢ Set.Icc 0 1,
      0 < Function.uncurry (fun t x => intervalDomainLift (u t) x) z
  v_nonneg0 : ∀ {b}, 0 ≤ b → b < T →
    ∀ z ∈ Set.Icc 0 b ×ˢ Set.Icc 0 1,
      0 ≤ Function.uncurry (fun t x => intervalDomainLift (v t) x) z

structure H1ZeroStartPhysicalPDESeamBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop where
  time_cont0 : ∀ {b}, 0 ≤ b → b < T →
    ContinuousOn (Function.uncurry (fun t x => liftTimeDeriv u t x))
      (Set.Icc 0 b ×ˢ Set.Icc 0 1)
  eqInterior0 : ∀ {b}, 0 ≤ b → b < T →
    Set.EqOn
      (Function.uncurry (fun t x => liftDeriv2 u t x))
      (Function.uncurry
        (liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v)))
      (Set.Icc 0 b ×ˢ Set.Ioo 0 1)
```

Then add a zero-sorry constructor:

```lean
theorem H1ZeroStartPhysicalPrimitiveDataBefore_of_continuity_and_pdeSeam
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hcont : H1ZeroStartPhysicalPrimitiveContinuityBefore p u v T)
    (hseam : H1ZeroStartPhysicalPDESeamBefore p u v T) :
    H1ZeroStartPhysicalPrimitiveDataBefore p u v T :=
  { u_cont0 := hcont.u_cont0
    v_cont0 := hcont.v_cont0
    ux_cont0 := hcont.ux_cont0
    vx_cont0 := hcont.vx_cont0
    u_pos0 := hcont.u_pos0
    v_nonneg0 := hcont.v_nonneg0
    time_cont0 := hseam.time_cont0
    eqInterior0 := hseam.eqInterior0 }
```

This split is useful because the continuity/positivity side may be produced from initial trace plus classical regularity or construction-level EWA data, while `time_cont0` and `eqInterior0` remain the true initial-time PDE compatibility seam.

## Recommended next Lean attempt

Do not attempt a theorem named `H1ZeroStartPhysicalPrimitiveDataBefore_of_classicalSolution`; current source evidence does not support it.

The smallest safe edit is the split above, added to `IntervalChiNegH1ZeroStartComponents.lean`. It does not close a mathematical frontier, but it makes the remaining frontier sharper and lets future producers target either:

1. zero-start primitive continuity/positivity, or
2. the initial-time PDE seam.

A later source producer should likely come from construction-specific regularity, not from `IsPaper2ClassicalSolution` alone. Its honest name should mention the source of the stronger zero-start data, for example `..._of_reducedCore_zeroStartRegularity` or `..._of_globalPDEInitialCompatibility`, not `..._of_classicalSolution`.
