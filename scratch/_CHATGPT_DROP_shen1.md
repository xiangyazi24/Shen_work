# Q2495 shen1 — help

Repo: `xiangyazi24/Shen_work`

This is a compact help page for the `shen1` git-drop workflow and the kinds of requests that are most useful for the current Shen_work Lean/PDE track.

## What to send

A good request should include:

```text
Q#### (shen1): <short task title>
Repo/branch/file context.
Current verified facts, theorem names, signatures, and compile errors.
Hard constraints: forbidden routes, names that must be used, and what not to prove.
Delivery: git-drop to scratch/_CHATGPT_DROP_shen1.md on chatgpt-scratch.
```

The most useful Lean requests are narrow and signature-driven, for example:

```text
Q#### (shen1): Audit theorem X against current APIs A/B/C.
Give a compile-oriented patch skeleton only. Do not introduce sorry/axioms.
Do not conclude Y; only package Z.
Identify exact imports, namespaces, theorem names, and #print axioms targets.
```

## What I can provide in a git-drop

I can write one of these into `scratch/_CHATGPT_DROP_shen1.md` and commit it:

1. A source-grounded audit of existing files and theorem interfaces.
2. A compile-oriented Lean patch skeleton with exact namespaces/imports.
3. A theorem DAG with proposed names and dependency order.
4. A no-go analysis explaining why a tempting route is mathematically false or too strong.
5. A minimal refactor plan that avoids cycles and preserves existing public wrappers.
6. A checklist of likely Lean elaboration risks: implicit arguments, open namespaces, typeclass inference, interval-integral orientation, and `IntervalIntegrable`/`IntegrableOn` mismatches.

## Current Shen_work PDE/Moser guidance

For the current integrated-Moser/precrossing line, the safe rules are:

* Do not convert a time-integral or average estimate for `Y_{p+rho}` directly into `LpPowerBoundedBefore`.
* Do not manufacture `IntegratedMoserFirstCrossingStep` from fixed-window estimates without a genuine high-excursion/thickness or pointwise extraction theorem.
* Do not derive `MoserDissipationDropBeforeNonnegB` or `RelativeMoserInterpolationBefore` from route-level conclusions like `Corollary_2_1`.
* Keep abstract `BoundedDomainData` statements honest: positivity of integrals, interval integrability, continuity, and endpoint behavior are often extra hypotheses unless a concrete `intervalDomain` producer is supplied.
* Prefer wrappers that conclude only what the current APIs justify: route residuals, time-integral bounds, average bounds, or explicitly frontier-parameterized first-crossing statements.

## Useful output templates

### Compile-oriented patch skeleton

```markdown
# Q#### shen1 — <title>

## Source facts
- File: `...`
- Existing names:
  - `...`

## Patch
```lean
import ...

open ...

namespace ...

-- code skeleton

#print axioms new_theorem_name

end ...
```

## Compile risks
- ...

## No-go routes
- ...
```

### Frontier map

```markdown
# Q#### shen1 — <title>

## Goal
Final target theorem:
```lean
...
```

## Dependency order
1. Feasible plumbing lemma A.
2. Feasible packaging lemma B.
3. Real analytic frontier C.
4. Final wrapper D.

## What not to prove
- No fake conversion from weaker estimate to stronger pointwise statement.
```

## Git-drop contract

For these requests, success means a real commit to `xiangyazi24/Shen_work` on branch `chatgpt-scratch`, updating:

```text
scratch/_CHATGPT_DROP_shen1.md
```

If the connector is unavailable or read-only, the correct failure message is:

```text
GIT-DROP FAILED: connector unavailable
```

No sandbox files or download links satisfy the delivery rule.
