# Task 41: 1D Bypass Assembly — from dx continuity to BoundedBefore

## Strategic Goal

Create a NEW file `ShenWork/PDE/P3Moser1DBypassAssembly.lean` that produces
`IsPaper2BoundedBefore intervalDomain T u` from `IsPaper2ClassicalSolution`
with MINIMAL carried hypotheses — ideally just `hlogistic_dominates : 2 * params.γ < params.α`
(a parameter condition, not a data hypothesis).

## What's Available (all axiom-clean, in the repo)

### From task 39+40 (just committed):
- `intervalDomain_dx_u_jointlyContinuous` — u_x ContinuousOn (0,T)×[0,1]
- `intervalDomain_dx_v_jointlyContinuous` — v_x ContinuousOn (0,T)×[0,1]
- `intervalDomain_gradientIntegrability_of_classical` — hG_int discharged

### From existing files:
- `chiNeg_H1_norm_bound` (IntervalChiNegH1Energy.lean) — uniform H1 bound from hlocal/havg/hwin/hWnn
- `produce_pointwiseGradientBound_full` (IntervalDomainH1GradientBound.lean) — H1 → gradient bound at p=2
- `produce_pointwiseGradientBound_general_pExp` (same file) — H1 + L∞ → gradient at all p≥2
- `intervalDomain_Proposition_2_5_1d` (IntervalDomain1DLinfRoute.lean) — gradient bound → BoundedBefore
- `intervalDomain_Linf_of_Lp_and_gradient` (same file) — Agmon L∞ from Lp + gradient
- `H1EnergyIdentity_of_classicalSolution_and_uxxL1Cont` (IntervalChiNegH1EnergyIdentity.lean)
- `h1_diffIneq_of_sup_bounds` (IntervalChiNegH1Energy.lean) — DI from sup bounds

## The Chain (what you need to wire)

```
IsPaper2ClassicalSolution
  │
  ├── [Task 40] → gradient integrability at p=2
  │       = H1energy IntervalIntegrable on strict windows
  │
  ├── [H1 DI] → H1energy' ≤ A·H1energy + B
  │     needs: H1EnergyIdentity (which needs hUxxL1Cont)
  │     + sup bounds on taxis/reaction terms
  │
  ├── [Gronwall/averaging] → chiNeg_H1_norm_bound
  │     → H1energy ≤ Y₁ uniformly on (0,T)
  │
  ├── [p=2 gradient] → produce_pointwiseGradientBound_full
  │     = IntervalDomainPointwiseMoserGradientBoundBefore u T 2
  │
  ├── [Agmon] → L∞ from H1
  │     intervalDomain_Linf_of_Lp_and_gradient at p=2
  │
  ├── [general p] → produce_pointwiseGradientBound_general_pExp
  │     = gradient bound at all p≥2
  │
  └── [Prop 2.5] → intervalDomain_Proposition_2_5_1d
        = BoundedBefore
```

## Key Step: Discharge hUxxL1Cont

`hUxxL1Cont` says: ∀ ε > 0, ∃ δ > 0, |s-τ| < δ → ∫₀¹ ‖u_xx(s,x) - u_xx(τ,x)‖ dx ≤ ε

From the PDE: u_xx(t,x) = u_t(t,x) + χ₀·chemDiv(t,x) - logistic(t,x)

All three terms are jointly continuous on (0,T)×[0,1]:
- u_t: field 8 of classicalRegularity
- chemDiv: differentiable flux (from C² regularity + v≥0 + u>0) → derivative is continuous
- logistic: algebraic in u (jointly continuous from field 9)

Jointly continuous on compact [a,b]×[0,1] → uniformly continuous → L¹ distance → 0.

ALTERNATIVELY: u_xx is ContinuousOn since it's `deriv(deriv(lift(u t)))` and u is C² (field 7).
On [a,b]×[0,1] compact, uniform continuity gives the L¹ time-continuity directly.

## Potential Simplification: Skip the Full DI

IF the full H1 DI wiring is too complex (many intermediate lemmas), consider:

**Direct route**: H1energy = ½∫|u_x|² is ContinuousOn (0,T) (from dx joint continuity).
A continuous function on (0,T) is bounded on any compact [a,b] ⊂ (0,T).
Then for any 0 < a < T: H1energy bounded on [a, T-ε] → gradient bound on [a, T-ε] → BoundedBefore on [a, T-ε].

This avoids the DI entirely! The uniform bound comes from CONTINUITY on the open interval (0,T).

PROBLEM: ContinuousOn (0,T) only gives bounded on compact SUBSETS — not a UNIFORM bound on all of (0,T). The issue is behavior near t=0 and t=T.

FIX: `IntervalDomainPointwiseMoserGradientBoundBefore u T 2` says "∀ t ∈ (0,T), gradient ≤ M". We need the bound on ALL of (0,T), not just compact subsets.

The DI approach gives a GLOBAL bound. Without it, we'd need to handle the behavior near endpoints.

## Recommended Approach: Conditional Assembly

Since the full chain from classical solution → BoundedBefore is long and may hit unforeseen gaps, deliver a CONDITIONAL theorem:

```lean
theorem intervalDomain_boundedBefore_of_classical_1d_bypass
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hlogistic : 2 * params.γ < params.α)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁)
    -- ^ this is the ONE remaining hypothesis from the DI analysis
    :
    IsPaper2BoundedBefore intervalDomain T u
```

This reduces the entire problem to ONE carried hypothesis: uniform H1 bound. The gradient integrability (hG_int) is DISCHARGED by Task 40.

## Files to Read

1. `ShenWork/PDE/IntervalDomain1DLinfRoute.lean` — Proposition 2.5, Agmon, L∞
2. `ShenWork/Paper2/IntervalDomainH1GradientBound.lean` — gradient bound producers
3. `ShenWork/PDE/P3MoserGradientContinuityFromDx.lean` — Task 40 (gradient integrability)
4. `ShenWork/Paper2/IntervalChiNegH1Energy.lean` — chiNeg_H1_norm_bound

## What to Produce

### Minimum deliverable:
```lean
theorem intervalDomain_boundedBefore_of_H1bound_and_logistic
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hlogistic : 2 * params.γ < params.α)
    {Y₁ : ℝ} (hY1 : 0 ≤ Y₁)
    (hH1bnd : ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁) :
    IsPaper2BoundedBefore intervalDomain T u
```

This wires: H1 bound → gradient at p=2 → Agmon L∞ → gradient at all p → Prop 2.5.

### Stretch goal (if feasible):
Also discharge `hH1bnd` from the DI analysis to get a fully unconditional theorem (modulo the parameter condition `hlogistic`).

## Constraints

- NO sorry, NO axiom
- Build: `~/.elan/bin/lake build ShenWork.PDE.P3Moser1DBypassAssembly`
- New file: `ShenWork/PDE/P3Moser1DBypassAssembly.lean`
- `#print axioms` must show only `[propext, Classical.choice, Quot.sound]`
- If stuck on the full unconditional version, deliver the conditional version (with hH1bnd) — that's still a major milestone
