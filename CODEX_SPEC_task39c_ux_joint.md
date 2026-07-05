# Task 39c: u_x joint continuity (close the chain)

## Context

`ShenWork/PDE/P3MoserDxJointContinuity.lean` already has:
- `continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc` (parametric integral continuity)
- `intervalDomain_dx_v_jointlyContinuous` — v_x is ContinuousOn (0,T)×[0,1] ✓
- `intervalDomain_dx_u_left_neumann` — deriv(lift(u t)) 0 = 0 ✓
- `intervalDomain_laplacian_u_eq_time_chem_logistic` — u_xx = u_t + χ₀·chemDiv - logistic ✓
- `intervalDomain_u_logisticPrimitive_jointContinuous` — ∫₀ˣ logistic jointly continuous ✓

## Goal

APPEND to the same file:

```lean
theorem intervalDomain_dx_u_jointlyContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (u t)) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

## Proof route

By FTC + Neumann, for t ∈ (0,T) and x ∈ [0,1]:

```
u_x(t,x) = ∫₀ˣ u_xx(t,s) ds
         = ∫₀ˣ [∂_t u(t,s) + χ₀·chemDiv(t,s) - logistic(t,s)] ds
         = ∫₀ˣ ∂_t u(t,s) ds + χ₀·[flux(t,s)]₀ˣ - ∫₀ˣ logistic(t,s) ds
         = ∫₀ˣ ∂_t u(t,s) ds + χ₀·flux(t,x) - ∫₀ˣ logistic(t,s) ds
```

where `flux(t,y) = lift(u t)(y) · deriv(lift(v t))(y) / (1 + lift(v t)(y))^β`.

Note: `flux(t,0) = lift(u t)(0) · deriv(lift(v t))(0) / ... = u(t,0) · 0 / ... = 0` (by Neumann v_x(t,0)=0).

Each term is jointly continuous on (0,T) × [0,1]:
1. `∫₀ˣ ∂_t u(t,s) ds` — parametric primitive of ∂_t u. Field 8 of classicalRegularity gives ∂_t u ContinuousOn (Ioo 0 T ×ˢ Icc 0 1). Apply `continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc`.
2. `flux(t,x) = u(t,x)·v_x(t,x)/(1+v(t,x))^β` — algebraic combo:
   - u(t,x): ContinuousOn from field 9
   - v_x(t,x): ContinuousOn from `intervalDomain_dx_v_jointlyContinuous`
   - v(t,x): ContinuousOn from field 9, v ≥ 0 so 1+v > 0
   - Product/division of ContinuousOn functions
3. `∫₀ˣ logistic(t,s) ds` — already proved ContinuousOn

Then: `u_x = sum of ContinuousOn functions` → ContinuousOn. Transfer to `deriv(lift(u t))` via pointwise identity (FTC).

## The FTC identity for u_x

For fixed t ∈ (0,T): from ContDiffOn 2 (lift(u t)) on [0,1] (field 7):
```
deriv(lift(u t))(x) = deriv(lift(u t))(0) + ∫₀ˣ (deriv(deriv(lift(u t)))) s ds
                    = 0 + ∫₀ˣ laplacian(u t)(s) ds    [Neumann at 0]
```

And from the PDE: `laplacian(u t)(s) = timeDeriv(u,t,s) + χ₀·chemDiv(s) - logistic(s)`.

The chemDiv integral telescopes:
```
∫₀ˣ chemDiv(t,s) ds = ∫₀ˣ deriv(flux(t,·))(s) ds = flux(t,x) - flux(t,0) = flux(t,x)
```

This gives the pointwise identity:
```
deriv(lift(u t))(x) = (∫₀ˣ ∂_t u ds) + χ₀·flux(t,x) - (∫₀ˣ logistic ds)
```

## Key steps in Lean

### Step A: ∂_t u parametric primitive

```lean
theorem intervalDomain_u_timeDeriv_primitive_jointContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun z : ℝ × ℝ =>
        ∫ s in (0 : ℝ)..z.2,
          deriv (fun r => intervalDomainLift (u r) s) z.1)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

Proof: Apply `continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc` to the time derivative. The time derivative's joint continuity is field 8 of classicalRegularity.

### Step B: Flux joint continuity

```lean
theorem intervalDomain_chemotaxis_flux_jointContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (fun z : ℝ × ℝ =>
        intervalDomainLift (u z.1) z.2 *
          deriv (intervalDomainLift (v z.1)) z.2 /
            (1 + intervalDomainLift (v z.1) z.2) ^ params.β)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

Proof: Algebraic composition of:
- `u` ContinuousOn (field 9): `ContinuousOn (fun z => intervalDomainLift (u z.1) z.2) ...`
- `v_x` ContinuousOn (`intervalDomain_dx_v_jointlyContinuous`)
- `v` ContinuousOn (field 9)
- `v ≥ 0` so `1 + v > 0` → `(1+v)^β` ContinuousOn and positive
- Use `ContinuousOn.mul`, `ContinuousOn.div`, `ContinuousOn.rpow_const`

### Step C: FTC identity

Prove for all t ∈ (0,T), x ∈ [0,1]:
```
deriv(lift(u t))(x) = (∫₀ˣ ∂_t u(t,s) ds) + χ₀·flux(t,x) - (∫₀ˣ logistic(t,s) ds)
```

This uses:
1. `ContDiffOn ℝ 2 (lift(u t)) (Icc 0 1)` → deriv has derivative at interior points
2. The PDE identity for the second derivative
3. `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` (FTC)
4. `deriv(lift(u t))(0) = 0` (Neumann)
5. chemDiv integral = flux(x) - flux(0) = flux(x) - 0

### Step D: Transfer ContinuousOn

```lean
exact ContinuousOn.congr (sum_of_continuous_terms) (fun z hz => identity_at_z)
```

## Lean hints for the chemDiv integral

The function `y ↦ lift(u t)(y) · deriv(lift(v t))(y) / (1 + lift(v t)(y))^β` is the flux.

Its derivative at y is `intervalDomainChemotaxisDiv params (u t) (v t) ⟨y, hy⟩` BY DEFINITION:
```
intervalDomainChemotaxisDiv p u v x =
  deriv (y ↦ lift u y * deriv (lift v) y / (1 + lift v y)^β) x.1
```

So `HasDerivAt flux (chemDiv at y) y` means `HasDerivAt flux (deriv flux y) y` — which holds when flux is differentiable at y.

Flux is differentiable on (0,1) because:
- `lift(u t)` is C² on [0,1] (field 7) → differentiable
- `deriv(lift(v t))` is C¹ on [0,1] (from ContDiffOn 2 for v) → differentiable
- `(1 + lift(v t))^β`: v is C² on [0,1], v ≥ 0 → 1+v > 0 → `rpow` differentiable

Show `DifferentiableOn ℝ flux (Ioo 0 1)` using product/division rules, then `DifferentiableOn.hasDerivAt` at each interior point.

For the FTC applied to flux:
```
∫₀ˣ (deriv flux) s ds = flux(x) - flux(0)
```
Needs: flux ContinuousOn [0,x] + HasDerivAt at interior + deriv IntervalIntegrable.

deriv is IntervalIntegrable because it equals chemDiv which is continuous on (0,1) (C¹ functions' derivatives are continuous when the source is C²). On [0,x] ⊂ [0,1], a function continuous on the open interior and continuous at the endpoints is IntervalIntegrable (or bounded + measurable suffices).

## Alternative simpler approach

If the chemDiv FTC is too hard to formalize directly, there's a simpler path:

Use the FULL u_xx integration directly (without splitting out the chemDiv telescope):

```
u_x(t,x) = ∫₀ˣ u_xx(t,s) ds
```

And `u_xx(t,s) = ∂_t u(t,s) + χ₀·chemDiv(t,s) - logistic(t,s)` for s ∈ (0,1).

If you can show `u_xx` (= `intervalDomainLaplacian (u t)`) is jointly continuous on (0,T) × (0,1), then the parametric primitive gives u_x jointly continuous.

How: `u_xx = ∂_t u + χ₀·chemDiv - logistic`. ∂_t u is ContinuousOn (field 8). Logistic is ContinuousOn. chemDiv is ContinuousOn if the flux is C¹ on (0,1) — which it is (u C², v C², v ≥ 0).

So alternatively: prove chemDiv ContinuousOn (0,T) × (0,1), then u_xx ContinuousOn, then ∫₀ˣ u_xx ContinuousOn, then = u_x.

Pick whichever approach is easier in Lean.

## Constraints

- NO sorry, NO axiom
- `#print axioms` only `[propext, Classical.choice, Quot.sound]`
- Build: `~/.elan/bin/lake build ShenWork.PDE.P3MoserDxJointContinuity`
- APPEND to existing file
- If fully stuck, deliver the ∂_t u primitive continuity + flux continuity + the stall report
