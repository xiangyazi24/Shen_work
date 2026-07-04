# Task 31: Discharge SubintervalMoserInputResidual

## Goal

Create `ShenWork/PDE/P3MoserSubintervalInput.lean` that proves
`SubintervalMoserInputResidual` (defined in `P3MoserRealInduction.lean`).

## Background

```lean
def SubintervalMoserInputResidual (p : CM2Params) : Prop :=
  ∀ {T τ : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
      BoundedBeforeOnSubinterval intervalDomain u τ T →
        0 ≤ τ →
          ∃ rho p0,
            CrossDiffusionBootstrapEstimate intervalDomain p τ rho u v ∧
              AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) τ rho p0 ∧
                LpBootstrapEnergyInequalityWithGap intervalDomain u τ rho p0
```

Given classical solution on [0,T] and bounded-before on [0,τ), produce the 3
bootstrap ingredients on the subinterval [0,τ]:
1. `CrossDiffusionBootstrapEstimate` on [0,τ]
2. `AbstractLpBootstrapHypothesis` on [0,τ]
3. `LpBootstrapEnergyInequalityWithGap` on [0,τ]

## Type analysis

### CrossDiffusionBootstrapEstimate (Statements.lean:1126)
```
∀ eps > 0, ∀ pExp > 1, ∃ Ceps,
    ∀ t, 0 < t → t < τ →
      D.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
        eps * D.integral (...) + Ceps * D.integral (...)
```
This is the Young inequality for the cross-diffusion term. On the subinterval [0,τ],
it follows from the SAME classical solution data — the estimate is pointwise in time
and doesn't depend on the horizon. So if it holds on [0,T], it holds on [0,τ] (just
restrict the time range).

### AbstractLpBootstrapHypothesis (Statements.lean:2200)
```
0 < rho ∧ 0 < T ∧ max 1 (rho * N / 2) < p0 ∧ LpPowerBoundedBefore D p0 τ u
```
Choose rho = 2*p.γ (the standard choice), p0 = max(p.N, max(p.m * p.N, p.γ * p.N)) + 1
or similar. The key ingredient is `LpPowerBoundedBefore D p0 τ u`.

`LpPowerBoundedBefore` is `∃ C, ∀ t, 0 < t → t < τ → ...L^p0 norm...≤ C`.

From `BoundedBeforeOnSubinterval` we have pointwise bounds: `∀ t ∈ (0,τ), ∃ M, ∀ x, |u t x| ≤ M`.
On intervalDomain (domain has measure 1), `‖u(t)‖_{p0} ≤ M` (since the L^p norm on [0,1]
is at most the L^∞ norm).

But wait — `BoundedBeforeOnSubinterval` has M depending on t, not uniform. We need a
uniform C for `LpPowerBoundedBefore`. This might need the assembly...

ALTERNATIVE APPROACH: The `BoundedBeforeOnSubinterval` gives per-t bounds, but for
a fixed τ₀ we only need to show `LpPowerBoundedBefore` on (0,τ₀). If the classical
solution is continuous in time (which it is from regularity), then on any compact
sub-interval [ε, τ₀-ε] the Lp norm is bounded. On (0, τ₀), we can use the classical
solution's spatial boundedness (from T29's `intervalDomain_slice_bounded_of_classical`)
which gives a bound M_t for each t, and then:
- The function t ↦ ‖u(t)‖_{Lp} is continuous on (0,T) (from time continuity of the
  classical solution)
- On any [ε, τ₀-ε], it's bounded by compactness
- Need to handle near t=0

SIMPLEST APPROACH: Define a residual predicate for the Lp bound from bounded-before
if you can't close it directly. But try first:

From `BoundedBeforeOnSubinterval`, each t ∈ (0,τ) has M_t with |u t x| ≤ M_t.
On intervalDomain (measure 1), ∫|u t x|^p dx ≤ M_t^p. So ‖u(t)‖_p ≤ M_t.
But we need UNIFORM M_t across t ∈ (0,τ).

OPTION: Prove this conditional on a residual predicate if needed.

### LpBootstrapEnergyInequalityWithGap on subinterval
This follows from T26's `intervalDomain_gap_of_classical_pDep` restricted to [0,τ].
The gap estimate is pointwise in time and independent of the horizon.

## Approach

1. For CrossDiffusion: restrict the T-horizon estimate to τ (monotonicity in T)
2. For Gap: use T26's producer, restricted to τ
3. For AbstractLpBootstrap: the hardest part is `LpPowerBoundedBefore` from
   `BoundedBeforeOnSubinterval`. If you can prove uniform Lp bound from per-t
   pointwise bounds, do it. If not, introduce a named residual.

## Files to read first

1. `ShenWork/PDE/P3MoserRealInduction.lean` — the residual definition
2. `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean` — BoundedBeforeOnSubinterval
3. `ShenWork/Paper2/Statements.lean` lines 1126-1160 — CrossDiffusionBootstrapEstimate
4. `ShenWork/Paper2/Statements.lean` lines 2200-2230 — AbstractLpBootstrapHypothesis
5. `ShenWork/PDE/P3MoserGapProducerWiring.lean` — T26's gap producer
6. `ShenWork/PDE/P3MoserShortTimeBounded.lean` — T29's slice boundedness

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserSubintervalInput.lean
```
