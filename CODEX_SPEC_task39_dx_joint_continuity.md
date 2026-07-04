# Task 39: ∂_x u joint continuity from the PDE (Approach C)

## Goal

Create `ShenWork/PDE/P3MoserDxJointContinuity.lean` that proves:

**Given `IsPaper2ClassicalSolution intervalDomain params T u v`, the spatial
derivative `∂_x u` is jointly continuous on `(0,T) × [0,1]`.**

This is a THEOREM derived from the existing API — no definition changes needed.

## Why this matters

The downstream chain:
```
∂_x u jointly continuous
  → integratedMoserGradientEnergy ContinuousOn (0,T)
  → IntervalIntegrable on strict windows (hG_int)
  → dissipation drop (task 38v2) becomes hypothesis-free
  → 1D bypass: H1 → gradient → Agmon → L∞ → BoundedBefore
  → eliminates 3 of 4 irreducible frontiers
```

## Proof route (THREE STEPS)

### Step 1: ∂_x v jointly continuous

From the v-equation (IsPaper2ClassicalSolution, 6th conjunct):
```
0 = D.laplacian (v t) x - params.μ * v t x + params.ν * (u t x) ^ params.γ
```

Rearranging:
```
D.laplacian (v t) x = params.μ * v(t,x) - params.ν * u(t,x)^γ
```

In 1D: `intervalDomainLaplacian (v t) x = deriv (deriv (lift (v t))) x.1`

So `∂²_x v(t,x) = μ·v(t,x) - ν·u(t,x)^γ`.

The RHS involves ONLY u and v (no spatial derivatives!) — both are jointly
continuous on `Ioo 0 T ×ˢ Icc 0 1` (field 9 of classicalRegularity).

By FTC + Neumann BC (`deriv (lift (v t)) 0 = 0` from field 7):
```
deriv (lift (v t)) x = ∫ s in 0..x, (μ * v(t,s) - ν * u(t,s)^γ)
```

This is a parametric integral of a jointly continuous function with variable
upper limit → jointly continuous in (t,x).

### Step 2: ∂_x u jointly continuous

From the u-equation (5th conjunct):
```
D.timeDeriv u t x = D.laplacian (u t) x
  - params.χ₀ * D.chemotaxisDiv params (u t) (v t) x
  + u(t,x) * (params.a - params.b * u(t,x)^params.α)
```

Rearranging:
```
D.laplacian (u t) x = D.timeDeriv u t x
  + params.χ₀ * D.chemotaxisDiv params (u t) (v t) x
  - u(t,x) * (params.a - params.b * u(t,x)^params.α)
```

Integrating from 0 to x (using FTC for the second derivative):
```
∂_x u(t,x) = ∂_x u(t,0) + ∫₀ˣ ∂²_s u(t,s) ds
            = 0 + ∫₀ˣ [∂_t u + χ₀ · chemotaxisDiv - logistic](t,s) ds
```

The chemotaxisDiv term integrates EXACTLY by FTC:
```
∫₀ˣ ∂_s [lift(u t)(s) · deriv(lift(v t))(s) / (1 + lift(v t)(s))^β] ds
= [lift(u t) · deriv(lift(v t)) / (1 + lift(v t))^β]₀ˣ
= u(t,x) · v_x(t,x) / (1 + v(t,x))^β - u(t,0) · v_x(t,0) / (1 + v(t,0))^β
= u(t,x) · v_x(t,x) / (1 + v(t,x))^β - 0   (Neumann: v_x(t,0) = 0)
```

So:
```
∂_x u(t,x) = ∫₀ˣ ∂_t u(t,s) ds
           + χ₀ · u(t,x) · v_x(t,x) / (1 + v(t,x))^β
           - ∫₀ˣ u(t,s) · (a - b · u(t,s)^α) ds
```

Each term is jointly continuous:
1. `∫₀ˣ ∂_t u(t,s) ds` — parametric integral of ∂_t u (jointly continuous, field 8) ✓
2. `u · v_x / (1+v)^β` — product of jointly continuous functions (u from field 9, v_x from Step 1, v from field 9, v ≥ 0 from 4th conjunct so 1+v > 0) ✓
3. `∫₀ˣ logistic ds` — parametric integral of jointly continuous function ✓

### Step 3: gradient energy ContinuousOn (optional, may be separate file)

From ∂_x u jointly continuous + u > 0 + u jointly continuous:
```
∂_x(u^{p/2})(t,x) = (p/2) · u(t,x)^{p/2-1} · ∂_x u(t,x)
```
This is jointly continuous for p ≥ 2.

Then `integratedMoserGradientEnergy D u p t = ∫₀¹ (∂_x(u^{p/2})(t,x))² dx`
is ContinuousOn (0,T) → IntervalIntegrable on strict windows.

## What to prove

### Main theorem (MUST deliver)

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

### Intermediate lemma (v_x joint continuity)

```lean
theorem intervalDomain_dx_v_jointlyContinuous
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (intervalDomainLift (v t)) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
```

### Bonus theorem (if achievable)

```lean
theorem intervalDomain_moserGradientEnergy_continuousOn
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn
      (fun t => integratedMoserGradientEnergy intervalDomain u p t)
      (Set.Ioo (0 : ℝ) T)
```

## Key API to read (in order)

1. `ShenWork/Paper2/Statements.lean:70-100` — IsPaper2ClassicalSolution definition
   - 5th conjunct: u-PDE on D.inside
   - 6th conjunct: v-PDE on D.inside
   - 7th conjunct: Neumann BC on D.boundary

2. `ShenWork/PDE/IntervalDomain.lean:2768-2913` — classicalRegularity definition
   - Field 7 (line ~2869): `deriv (lift (u t)) 0 = 0` and `deriv (lift (u t)) 1 = 0`
   - Field 8 (line ~2883): joint ContinuousOn of ∂_t u on `Ioo 0 T ×ˢ Icc 0 1`
   - Field 9 (line ~2906): joint ContinuousOn of u on `Ioo 0 T ×ˢ Icc 0 1`

3. `ShenWork/PDE/IntervalDomain.lean:2919-2930` — definitions
   - `intervalDomainLaplacian f x = deriv (deriv (lift f)) x.1`
   - `intervalDomainChemotaxisDiv p u v x = deriv (y ↦ lift u y * deriv (lift v) y / (1 + lift v y)^β) x.1`

4. `ShenWork/Paper2/Statements.lean:145-150` — accessor `IsPaper2ClassicalSolution.regularity`

5. `ShenWork/PDE/P3MoserIntegratedClosure.lean:500-510` — integratedMoserGradientEnergy definition

## Key Mathlib tools

### Parametric integral with variable upper limit

The key result needed: if `f : ℝ × ℝ → ℝ` is ContinuousOn on `K × [0,1]` (K compact),
then `(t,x) ↦ ∫ s in 0..x, f(t,s)` is ContinuousOn on `K × [0,1]`.

In Mathlib, this can be assembled from:
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` (FTC)
- `ContinuousOn.integral_comp_Icc` or similar
- `ContinuousOn.intervalIntegral` for the parameter-continuity half
- For the variable-limit half: `HasDerivAt` of x ↦ ∫₀ˣ g(s) ds (= g(x) when g is continuous)

Alternative approach: prove the joint continuity directly by showing:
- For fixed t: x ↦ ∫₀ˣ f(t,s) ds has derivative f(t,x), hence is C¹ in x
- For fixed x: t ↦ ∫₀ˣ f(t,s) ds is ContinuousOn by dominated convergence
- Joint continuity on compact sets from uniform continuity

### FTC for the second derivative

If `g` is `ContDiffOn ℝ 2` on `Icc 0 1`, then:
```
deriv g x = deriv g 0 + ∫ s in 0..x, deriv (deriv g) s
```

This is `integral_eq_sub_of_hasDerivAt_of_le` applied to `deriv g`.

### Neumann BC extraction

From `hsol.regularity`:
- Field 7, line ~2871: `deriv (intervalDomainLift (u t)) 0 = 0`
- Field 7, line ~2873: `deriv (intervalDomainLift (v t)) 0 = 0`

Access path: `hsol.regularity.2.2.2.2.2.1` (field 6 = closed-domain C² + Neumann)

## Lean proof hints

### Getting the v-PDE as an equation for laplacian

```lean
-- From the 6th conjunct of IsPaper2ClassicalSolution:
have hpde_v := hsol.2.2.2.2.2.1  -- the v-PDE
-- hpde_v : ∀ t x, 0 < t → t < T → x ∈ D.inside →
--   0 = D.laplacian (v t) x - params.μ * v t x + params.ν * (u t x) ^ params.γ
-- Rearrange to: D.laplacian (v t) x = params.μ * v t x - params.ν * (u t x) ^ params.γ
```

Wait — the v-PDE might be in a different position. Read the definition carefully:
```
IsPaper2ClassicalSolution D p T u v :=
  0 < T ∧                                    -- .1
  D.classicalRegularity T u v ∧              -- .2.1
  (∀ t x, 0 < t → t < T → 0 < u t x) ∧     -- .2.2.1
  (∀ t x, 0 < t → t < T → 0 ≤ v t x) ∧     -- .2.2.2.1
  (u-PDE) ∧                                  -- .2.2.2.2.1
  (v-PDE) ∧                                  -- .2.2.2.2.2.1
  (Neumann)                                  -- .2.2.2.2.2.2
```

So:
- v-PDE: `hsol.2.2.2.2.2.1`
- Neumann: `hsol.2.2.2.2.2.2`
- u-PDE: `hsol.2.2.2.2.1`
- v nonneg: `hsol.2.2.2.1`

### The v-PDE is an ELLIPTIC equation (0 = Δv - μv + νu^γ)

Note: the v-equation has `0 = laplacian(v t) x - μ * v(t,x) + ν * u(t,x)^γ`.
There is NO time derivative in the v-equation — it is ELLIPTIC.
So: `laplacian(v t)(x) = μ * v(t,x) - ν * u(t,x)^γ`

### Variable-limit integral joint continuity (core Lean challenge)

The hardest Lean step is showing:
```
(t,x) ↦ ∫ s in 0..x, f(t,s)
```
is ContinuousOn when f is ContinuousOn.

Approach 1 (recommended): Factor as composition:
- F(t,a,b) = ∫ s in a..b, f(t,s) — continuous in (t,a,b) when f is jointly continuous
  (use `ContinuousOn.intervalIntegral_comp_sub_left` or similar)
- Then (t,x) ↦ F(t, 0, x) — composition with continuous map

Approach 2: Direct proof:
- |∫₀^{x₁} f(t₁,s) ds - ∫₀^{x₂} f(t₂,s) ds|
  ≤ |∫₀^{x₁} (f(t₁,s) - f(t₂,s)) ds| + |∫_{x₁}^{x₂} f(t₂,s) ds|
- First term → 0 by uniform continuity of f on compact set
- Second term → 0 since |x₂ - x₁| → 0 and f bounded on compact

Approach 3: Show ContinuousOn in t (by parametric integral continuity) +
ContinuousOn in x (by FTC) + separate-variable continuity on compact = joint
(use `ContinuousOn.of_comp_continuousOn_left_right` or similar).

### If the variable-limit integral proof is too hard

Deliver the intermediate results:
1. `∂²_x v(t,x) = μv(t,x) - νu(t,x)^γ` (pointwise identity from PDE)
2. `∂²_x v` is jointly continuous (algebraic)
3. `∂_x v(t,x) = ∫₀ˣ ∂²_s v(t,s) ds` (FTC + Neumann)
4. For fixed t: `∂_x v(t,·)` is continuous on [0,1] (from C² regularity)
5. For fixed x: `t ↦ ∂_x v(t,x)` is continuous on (0,T) (from parametric integral continuity in t)

Items 4+5 give SEPARATE-VARIABLE continuity. For joint continuity on compact
sets, you can use: "if f is separately continuous and one variable gives
equicontinuous family, then f is jointly continuous" — or just sorry the joint
continuity step and report what blocks it.

## Constraints

- NO sorry, NO axiom
- `#print axioms` must give only `[propext, Classical.choice, Quot.sound]`
- Build: `~/.elan/bin/lake build ShenWork.PDE.P3MoserDxJointContinuity`
- If the full u_x theorem is too hard, deliver v_x joint continuity + the identity for u_x + a precise stall report

## Imports

```lean
import ShenWork.PDE.IntervalDomain
import ShenWork.Paper2.Statements
import ShenWork.PDE.P3MoserIntegratedClosure
```

Add additional Mathlib imports as needed (measure theory, interval integrals, FTC).

## If stuck

1. Deliver `intervalDomain_dx_v_jointlyContinuous` (the v_x step) — this is the easier half
2. Deliver the IDENTITY `∂_x u(t,x) = ∫₀ˣ ∂_t u + χ₀·u·v_x/(1+v)^β - ∫₀ˣ logistic`
3. Report exactly what Mathlib API is missing for the variable-limit integral continuity
4. Do NOT sorry — deliver what compiles
