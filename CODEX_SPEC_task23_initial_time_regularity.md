# CODEX_SPEC Task 23: Investigate initial-time regularity (item 2)

## Goal

Investigate whether `IntervalDomainLpPDETermInitialWindowIntegrability` can be
produced from global classical solution data, or if it's a genuine frontier.

## The residual

```lean
def IntervalDomainLpPDETermInitialWindowIntegrability
    (params : CM2Params) (u v : ℝ → D.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q → ∀ b ∈ Set.Icc 0 T,
    (IntervalIntegrable (diffusion_term q u) volume 0 b) ∧
    (IntervalIntegrable (chemotaxis_term params q u v) volume 0 b) ∧
    (IntervalIntegrable (logistic_term params q u) volume 0 b)
```

This asks: are the individual PDE terms (diffusion, chemotaxis, logistic
integrals) integrable on [0, b] for b ∈ [0, T]?

## Two investigation routes (per oracle analysis)

### Route A: Classical regularity at t=0
Check what `IsPaper2ClassicalSolution` and `IsPaper2GlobalClassicalSolution`
assert at t = 0. The relevant structure is defined in
`ShenWork/Paper2/Statements.lean`. Key question:

- If the solution is regular on the CLOSED interval [0, T] (not just (0, T)),
  then all PDE terms are continuous on [0, T] × Ω̄, hence bounded, hence
  integrable. The chain collapses.
- If regularity is only on the OPEN interval (0, T), then t → 0 may have
  singular behavior (t^{-1/2} from heat kernel smoothing), but t^{-1/2} is
  still integrable on [0, b].

### Route B: Time-weighted reformulation
The existing chain uses `WeightedTimeTerm` as an intermediate. If we reformulate
to work with `t^k · E(t)` (or `φ(t) · E(t)` with `φ(0) = 0`) instead of `E(t)`
directly, the initial trace is zero by construction and initial-window
integrability becomes free. Check:
- Where in the chain does the time weight enter?
- Can we push the weight earlier to absorb the t → 0 singularity?

## What to produce

Write `ShenWork/PDE/P3MoserInitialTimeRegularity.lean`:

EITHER:
(A) A theorem producing `IntervalDomainLpPDETermInitialWindowIntegrability`
    from `IsPaper2GlobalClassicalSolution` (if the regularity data extends
    to t = 0), OR

(B) A precise report documenting:
    - What `IsPaper2ClassicalSolution` asserts at t = 0 (open vs closed)
    - Whether the PDE terms have integrable singularities at t = 0
    - Which route (A or B above) is more promising
    - Any partial wiring theorems that compile

## Files to read

1. `ShenWork/Paper2/Statements.lean` — search for `IsPaper2ClassicalSolution`
   definition, check if regularity is on (0,T) or [0,T]
2. `ShenWork/PDE/P3MoserEnergyContinuity.lean` lines 1365-1400 — the
   definitions of the window integrability types
3. `ShenWork/PDE/P3MoserEnergyContinuity.lean` lines 1895-1940 — the
   positive-start window integrability (which IS automatic from classical)
4. `ShenWork/PDE/P3MoserPDECombinedInitialProducer.lean` — existing wiring

## Rules

- 0 sorry, 0 custom axiom
- Write ONLY `ShenWork/PDE/P3MoserInitialTimeRegularity.lean`
- This is INVESTIGATION first — read extensively before writing
- Add `#print axioms` for any theorems
- Verify: `lake env lean ShenWork/PDE/P3MoserInitialTimeRegularity.lean`
