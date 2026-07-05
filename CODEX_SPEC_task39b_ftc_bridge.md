# Task 39b: FTC bridge — close v_x and u_x joint continuity

## Context

`ShenWork/PDE/P3MoserDxJointContinuity.lean` already has (all building clean):
- `continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc` — variable-limit integral continuity
- `intervalDomain_v_xx_eq_reaction_lift` — `deriv (deriv (lift (v t))) x = μ·(lift v t x) - ν·(lift u t x)^γ` for interior x
- `intervalDomain_dx_v_left_neumann` — `deriv (lift (v t)) 0 = 0`
- `intervalDomain_dx_u_left_neumann` — `deriv (lift (u t)) 0 = 0`
- `intervalDomain_v_x_reactionPrimitive_jointContinuous` — `(t,x) ↦ ∫₀ˣ (μv - νu^γ) ds` is ContinuousOn
- `intervalDomain_u_logisticPrimitive_jointContinuous` — logistic primitive is ContinuousOn

## Goal

Add to the SAME file the following theorems. APPEND to the end (before the final `#print axioms` block).

### Theorem 1: v_x joint continuity

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

**Proof route:**
1. From `classicalRegularity` field 7: for each t ∈ (0,T), `ContDiffOn ℝ 2 (lift (v t)) (Icc 0 1)`.
2. Therefore `deriv (lift (v t))` has derivative `deriv (deriv (lift (v t)))` at each x ∈ (0,1).
   Specifically: `ContDiffOn ℝ 2 f S → ContDiffOn ℝ 1 (deriv f) (interior S)` or similar.
   And `ContinuousOn (deriv (lift (v t))) (Icc 0 1)`.
3. From `intervalDomain_v_xx_eq_reaction_lift`: on the interior, `deriv (deriv (lift (v t))) x = μ·v(t,x) - ν·u(t,x)^γ`.
4. FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`): for x ∈ [0,1],
   `∫₀ˣ (deriv (deriv (lift (v t)))) s ds = deriv(lift(v t))(x) - deriv(lift(v t))(0)`.
5. By step 3: `∫₀ˣ (μv - νu^γ)(t,s) ds = deriv(lift(v t))(x) - 0` (Neumann).
6. So: `deriv(lift(v t))(x) = ∫₀ˣ (μv - νu^γ)(t,s) ds` for all t ∈ (0,T), x ∈ [0,1].
7. The RHS is ContinuousOn (by `intervalDomain_v_x_reactionPrimitive_jointContinuous`).
8. Since the two functions agree pointwise, `deriv(lift(v t))` is ContinuousOn too.

**Key Mathlib API:**
- `ContDiffOn.deriv_of_isOpen` or `ContDiffOn.hasFDerivAt` — get HasDerivAt from ContDiffOn
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` — the FTC
- `ContinuousOn.congr` — transfer ContinuousOn from one function to another that agrees pointwise

### Theorem 2: u_x joint continuity

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

**Proof route:**
1. Same FTC approach as v_x but using the u-equation.
2. From u-PDE: `∂²_x u = ∂_t u + χ₀·chemotaxisDiv - logistic`.
3. FTC from 0 to x: `u_x(t,x) = ∫₀ˣ ∂²_s u ds = ∫₀ˣ (∂_t u + χ₀·chemDiv - logistic) ds`.
4. The chemotaxisDiv integral collapses by FTC:
   `∫₀ˣ ∂_s[lift(u t)·deriv(lift(v t))/(1+lift(v t))^β] ds`
   `= lift(u t)(x)·deriv(lift(v t))(x)/(1+lift(v t)(x))^β - 0` (since deriv(lift(v t))(0)=0).
5. So: `u_x(t,x) = ∫₀ˣ ∂_t u ds + χ₀·u·v_x/(1+v)^β - ∫₀ˣ logistic ds`.
6. Each term is ContinuousOn:
   - `∫₀ˣ ∂_t u ds`: apply `continuousOn_parametric_primitive_of_continuousOn_Ioo_Icc` to ∂_t u (ContinuousOn from field 8)
   - `u·v_x/(1+v)^β`: algebraic combo of v_x (Theorem 1), u (field 9), v (field 9), v≥0 (4th conjunct)
   - `∫₀ˣ logistic ds`: already proved (`intervalDomain_u_logisticPrimitive_jointContinuous`)

**Key subtlety:** For the chemotaxis FTC, you need `lift(u t)·deriv(lift(v t))/(1+lift(v t))^β` to be differentiable on (0,1). This follows from:
- `lift(u t)` is C² on [0,1] (field 7 for u)
- `deriv(lift(v t))` is C¹ on [0,1] (from ContDiffOn 2 for v)
- `lift(v t)` is C² and v ≥ 0 so `1+v > 0`, hence `(1+v)^β` is smooth and nonzero

## What to read first

1. `ShenWork/PDE/P3MoserDxJointContinuity.lean` — the file you're extending (READ ALL OF IT)
2. `ShenWork/PDE/IntervalDomain.lean:2860-2913` — classicalRegularity fields 7-9
3. `ShenWork/Paper2/Statements.lean:70-130` — IsPaper2ClassicalSolution definition

## Lean proof strategy hints

### Getting ContDiffOn 2 → HasDerivAt for the second derivative

```lean
-- From classicalRegularity field 7:
have hC2v : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Icc 0 1) := ...

-- ContDiffOn 2 → differentiable on interior:
have hC1_deriv : ContDiffOn ℝ 1 (deriv (intervalDomainLift (v t))) (Set.Ioo 0 1) := by
  exact (hC2v.mono Set.Ioo_subset_Icc_self).of_le (by norm_num) le_top
  -- or use contDiffOn_succ_iff_deriv

-- Then for x ∈ Ioo 0 1:
have hHD : HasDerivAt (deriv (lift (v t))) (deriv (deriv (lift (v t))) x) x := ...
```

### The ContinuousOn transfer

```lean
-- Once you have the pointwise identity:
-- ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc 0 1,
--   deriv (lift (v t)) x = ∫₀ˣ (μ·v - ν·u^γ) ds

-- The RHS is ContinuousOn (already proved)
-- Transfer:
exact ContinuousOn.congr
  (intervalDomain_v_x_reactionPrimitive_jointContinuous hsol)
  (fun z hz => (pointwise_identity z.1 z.2 hz.1 hz.2).symm)
```

### Extracting classicalRegularity fields

```lean
-- IsPaper2ClassicalSolution is:
-- 0 < T ∧ reg ∧ u>0 ∧ v≥0 ∧ u-PDE ∧ v-PDE ∧ Neumann
-- So:
have hreg := hsol.2.1  -- classicalRegularity
-- Field 7 of classicalRegularity:
-- hreg.2.2.2.2.2.1 gives the C² + Neumann conjuncts
-- Check the exact destructuring by reading the definition
```

## Constraints

- NO sorry, NO axiom
- `#print axioms` only `[propext, Classical.choice, Quot.sound]`
- Build: `~/.elan/bin/lake build ShenWork.PDE.P3MoserDxJointContinuity`
- APPEND to the existing file — do NOT rewrite what's already there
- If u_x is too hard, deliver v_x at minimum
