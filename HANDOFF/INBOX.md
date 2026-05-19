# Shen_work Lean 4 Formalization — Full Task List for Codex

## Project state

- **Repo**: `~/repos/shen_work`, Lean 4 + Mathlib
- **Build**: `cd ~/repos/shen_work && ~/.openclaw/workspace/scripts/remote-build.sh shen_work` (DO NOT run local `lake build`)
- **Single file**: `~/.openclaw/workspace/scripts/remote-build.sh shen_work --file ShenWork/Defs.lean`
- **Current invariant**: 0 sorry, full build clean
- **Papers**: `paper1.pdf` (traveling waves), `paper2.pdf` (boundedness), `paper3.pdf` (persistence)

## What's wrong

All paper theorems are defined as `def Foo : Prop := ...` (statement targets) with
projection lemmas proved between them. **No actual PDE theorem is proved.** The 0-sorry
invariant is fake — it just means nothing uses `sorry` because the hard theorems are
encoded as Prop definitions, not as `theorem ... := sorry`.

## What to do

Convert statement targets into real theorems (with `sorry` initially) and then prove them.
Introduce `sorry` honestly where real math is needed, then eliminate each one.

## Priority 1: Psi elliptic ODE identity

The resolvent `v(x) = Ψ(x; f, λ, μ) = (μ/(2√λ)) ∫ e^{-√λ|x-y|} f(y) dy` satisfies:

```
v''(x) - λ v(x) + μ f(x) = 0
```

This is in `ShenWork/PDE/LeibnizRule.lean` as `Psi_elliptic_ode` (currently `sorry`).

**Proof strategy**: 
1. The first derivative `v'(x)` is already proved as `Psi_derivative_formula_general`
2. v'(x) = -(μ/2) e^{-ax} L(x) + (μ/2) e^{ax} R(x) where a = √λ
3. L(x) = ∫_{Iic x} e^{ay} f(y) dy, R(x) = ∫_{Ioi x} e^{-ay} f(y) dy
4. Use FTC: L'(x) = e^{ax}f(x), R'(x) = -e^{-ax}f(x)
5. Product rule → v''(x) = a²v(x) - μf(x) = λv(x) - μf(x)

FTC for half-line integrals: `hasDerivAt_setIntegral_Iic_of_continuous` is started (also in LeibnizRule.lean, currently `sorry`). Use `Set.Iic_union_Ioc_eq_Iic` to split, then `intervalIntegral.integral_hasDerivAt_right` for the interval part.

## Priority 2: Lemma 4.1 — upper barrier supersolution

`IsFrozenSuperSolution p c u (upperBarrier κ M)` — the upper barrier `min(M, exp(-κx))` 
is a supersolution of the frozen wave equation when u is in the trap set.

Key facts already proved:
- `expDecay_logistic_wave_nonpos_at_kappa`: exponential part satisfies logistic ≤ 0
- `constant_logistic_nonpos`: constant M ≥ 1 satisfies logistic ≤ 0
- Comparison principle proved in `ParabolicMaxPrinciple.lean`

The chemotaxis term `χ·(W^m · V_x)_x` needs Psi ODE identity (Priority 1) to handle.

## Priority 3: Lemma 4.2 — lower barrier subsolution  

Similar structure but for `lowerBarrierPlateau` and constant subsolutions.

## Priority 4: Paper1 Proposition 1.1 — global existence

Schauder fixed point on the function space `E_T(u₀)`. Needs comparison principle + 
compactness. Very involved.

## Priority 5: Paper2/Paper3 theorems

Less urgent. Paper2 bounded-domain PDE predicates need genuine instantiation first.

## Build rules

- **Remote only**: `~/.openclaw/workspace/scripts/remote-build.sh shen_work`
- **Never** run `lake build` or `lake env lean` locally
- Introduce `sorry` where needed — honest sorry is better than fake 0-sorry
- Run `rg -n "\bsorry\b|axiom|admit" ShenWork --glob '*.lean'` to track progress
