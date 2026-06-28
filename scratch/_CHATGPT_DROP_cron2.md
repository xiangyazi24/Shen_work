# Q1604 (cron2) — value majorant vs gradient majorant

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

Your `O(k^-2)` summability is sufficient for the **value** cutoff resolver series:

```lean
cutoffResolverSeries_contDiff_two
```

It is **not** sufficient for the **gradient** joint `C²` theorem if that theorem is proved by a separate gradient-series `contDiff_tsum`.

The current file confirms the split:

* `heatResolver_jointContDiffAt_two` goes through `cutoffResolverSeries_contDiff_two`.
* `heatResolver_grad_jointContDiffAt_two` does **not** currently go through `cutoffResolverSeries_contDiff_two`; it extracts `PhysicalResolverJointC2Data` and calls `coupledChemical_grad_jointContDiffAt_two`.

So the value majorant can be closed with H² IBP decay, but the current gradient path is still tied to the physical gradient data unless rewritten.

## Value series calculation

For the value term

```text
phi(t) * w_k * srcTimeCoeff_k(t) * cos(k*pi*x),
```

with joint derivative order `j <= 2`, the worst spatial factor is `(k*pi)^j`. If H² Neumann gives

```text
|srcTimeCoeff_k(t)| <= C / (k*pi)^2
```

uniformly for `t >= c/2`, then

```text
iSup_q ||D^j(value term_k)(q)||
  <= C * w_k * (k*pi)^j / (k*pi)^2
  = C * (k*pi)^(j-2) / (mu + (k*pi)^2).
```

For `j = 2`, this is

```text
C / (mu + (k*pi)^2) = O(k^-2),
```

hence summable. Therefore H² / quadratic IBP decay is enough for `cutoffResolverMajorant_summable` for the value `C²` theorem.

## Gradient series calculation

The gradient term is one spatial derivative higher:

```text
phi(t) * w_k * srcTimeCoeff_k(t) * d/dx cos(k*pi*x).
```

For gradient joint order `j <= 2`, the worst spatial factor is `(k*pi)^(j+1)`, not `(k*pi)^j`. With only H² decay:

```text
iSup_q ||D^j(gradient term_k)(q)||
  <= C * w_k * (k*pi)^(j+1) / (k*pi)^2
  = C * (k*pi)^(j-1) / (mu + (k*pi)^2).
```

For `j = 2`, this is

```text
C * (k*pi) / (mu + (k*pi)^2) = O(k^-1),
```

which is not summable. Thus the gradient `C²` series needs stronger decay, effectively one more power than H² gives. Since cosine IBP gives decay in pairs, the natural safe package is H⁴ / quartic decay:

```text
|srcTimeCoeff_k(t)| <= C / (k*pi)^4.
```

Then the worst gradient term is

```text
w_k * (k*pi)^3 / (k*pi)^4 = O(k^-3),
```

which is summable.

## Current proof path in `IntervalHeatResolverJointC2.lean`

The value theorem is direct:

```lean
have hCutoff := (cutoffResolverSeries_contDiff_two ...).contDiffAt
...
exact hCutoff.congr_of_eventuallyEq ...
```

So replacing the value majorant with the direct H² IBP proof is enough for `heatResolver_jointContDiffAt_two`.

The gradient theorem currently has this shape:

```lean
obtain ⟨Bt, hBt⟩ :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont hu₀_pos
exact ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_grad_jointContDiffAt_two
  hBt hx₀
```

So it does **not** reuse `cutoffResolverSeries_contDiff_two`. It goes through the physical gradient assembler, whose generic gradient series uses `boundedWeightJointGradMajorant`, i.e. the one-extra-spatial-derivative majorant.

## Answer to the question

`O(k^-2)` is sufficient for the value cutoff series but not for the gradient `C²` series.

If the only target is `heatResolver_jointContDiffAt_two`, the H² IBP route is enough.

If the target is also `heatResolver_grad_jointContDiffAt_two`, then either:

1. keep the current physical route and discharge `PhysicalResolverJointC2Data`, or
2. build a separate direct gradient cutoff series, but then prove stronger source coefficient decay, naturally H⁴ / quartic IBP, for the source time slices.

The current `heatResolver_grad_jointContDiffAt_two` goes through the second/generic gradient path via `PhysicalResolverJointC2Data`, not through `cutoffResolverSeries_contDiff_two`.
