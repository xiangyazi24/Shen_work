# CODEX_SPEC Task 21: Investigate and produce hBoundedBefore

## Goal

Write `ShenWork/PDE/P3MoserBoundedBeforeProducer.lean` — investigate the
producer chain for `IsPaper2BoundedBefore` and produce a theorem that gives
the assembly filler's `hBoundedBefore` hypothesis from available data.

## Target type

The assembly filler's hBoundedBefore is:
```lean
∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
  IsPaper2ClassicalSolution intervalDomain p T u v →
  CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
  AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
    IsPaper2BoundedBefore intervalDomain T u
```

## Existing producers (in P3MoserIntegratedClosure.lean and P3MoserDissipationShape.lean)

All existing `IsPaper2BoundedBefore` producers need:
1. `AbstractLpBootstrapHypothesis` (we have this)
2. Some form of energy inequality or dissipation data
3. `IntegratedMoserFirstCrossingStep` or equivalent crossing step
4. Downward `LpPowerBoundedBefore` monotonicity (`hLpMono`)
5. `IntervalDomainMoserQuantitativeEndpoint` (the dyadic endpoint)

Key producers to check:
- `intervalDomain_boundedBefore_of_relative_dissipation_nonnegB` (P3MoserDissipationShape.lean:340)
  Takes: boot + energy + dissipation + relative interpolation + LpMono + endpoint
- `intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB` (P3MoserDissipationShape.lean:377)
  Takes: dissipation supplier + relative interpolation supplier → Corollary_2_1

The chain: `(hsol,hcross,hboot)` → energy inequality (already have) → dissipation
(produced by assembly's integratedMoserDissipationCore, but that's what we're
BUILDING with the assembly) → crossing → all-Lp → bounded.

## The circular dependency

NOTE: The assembly filler uses hBoundedBefore to produce relativeMassGradient,
which feeds into integratedMoserDissipation. Then integratedMoserDissipation
is used downstream. So hBoundedBefore is an INPUT to the assembly, not derived
from its outputs.

The question: can hBoundedBefore be produced INDEPENDENTLY of the assembly,
directly from `(hsol, hcross, hboot)`?

## Investigation steps

1. Read `ShenWork/PDE/IntervalDomainExistence.lean` lines 4340-4350 — there's
   a `have hbounded : IsPaper2BoundedBefore intervalDomain (1 : ℝ) u` in
   the existence theorem. Check what it uses.

2. Read `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean` lines 220-240 and
   350-370 — producers from ladder atoms.

3. Read `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean` lines
   592-621 — the structured Moser bootstrap data.

4. Read `ShenWork/PDE/P3MoserDissipationShape.lean` lines 340-400 — dissipation
   shape producers.

5. Grep for `Corollary_2_1` to see if there's a direct route from classical
   solution to all-Lp-bounded to bounded-before.

## What to produce

EITHER:
(A) A theorem producing hBoundedBefore from `(hsol, hcross, hboot)` with
    possibly additional carried hypotheses (LpMono, quantitative endpoint, etc.)
    — document what's carried.

OR:
(B) A precise report documenting the exact chain from `(hsol, hcross, hboot)`
    to `IsPaper2BoundedBefore`, identifying which pieces exist and which are
    missing. Write the report as comments in the file.

If (A) is possible, also provide the theorem. If only (B), provide the report
with any partial wiring theorems that compile.

## Rules

- 0 sorry, 0 custom axiom
- Write ONLY `ShenWork/PDE/P3MoserBoundedBeforeProducer.lean`
- This is an INVESTIGATION + WIRING task — read extensively before writing
- Add `#print axioms` for any theorems at the end
- Verify: `lake env lean ShenWork/PDE/P3MoserBoundedBeforeProducer.lean`
