# Q1576 (cron2) — callers of `coupledChemical_jointContDiffAt_two`

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

I searched the repo through the GitHub connector for the exact token:

```text
coupledChemical_jointContDiffAt_two
```

The code-search hit files were:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
ShenWork/PDE/IntervalIteratePicardJointC2.lean
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean
UNDERSTANDING.md
```

Only two Lean files contain real theorem applications/callers. The other hits are definition, comments, docs, or `open` references.

## Actual callers

### `ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean`

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:30
```

Used in `coupledChemical_innerCommute_of_physicalJointC2` to obtain the initial value `C²` input for the Clairaut bridge:

```lean
have hFC2 : ContDiffAt ℝ 2 (Function.uncurry F) (s, y) :=
  coupledChemical_jointContDiffAt_two H hy
```

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:38
```

Used in the same theorem for the spatial bridge at `(r,y)`:

```lean
have hgr : ContDiffAt ℝ 2 (Function.uncurry F) (r, y) :=
  coupledChemical_jointContDiffAt_two H hy
```

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:50
```

Used in the same theorem for the time bridge at `(s,z)`:

```lean
have hgr : ContDiffAt ℝ 2 (Function.uncurry F) (s, z) :=
  coupledChemical_jointContDiffAt_two H hz
```

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:84
```

Used in `coupledChemDivFlux_timeBridge_of_physicalJointC2` to supply the `hv` input to `coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt`:

```lean
filter_upwards [hopen] with y hy using coupledChemical_jointContDiffAt_two H hy
```

### `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean`

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:885
```

Used in the old heat-level wrapper `heatResolverJointContDiffAt_two` after first extracting `PhysicalResolverJointC2Data`:

```lean
exact coupledChemical_jointContDiffAt_two hBt hx₀
```

## Non-caller hits

`ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean` contains the theorem definition itself, not a caller.

`ShenWork/PDE/IntervalIteratePicardJointC2.lean`, `ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean`, and `UNDERSTANDING.md` only mention the name in comments or documentation.

`ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` also has documentation and an `open ... (coupledChemical_jointContDiffAt_two ...)` reference; the only actual application I found there is line 885.

## Rewiring verdict

For the **heat Level0 lane**, yes: the old heat wrapper call at `IntervalHeatSemigroupHighRegularity.lean:885` can be replaced by the direct theorem

```lean
ShenWork.Paper2.HeatResolverJointC2Direct.heatResolver_jointContDiffAt_two
```

with the heat positivity floor supplied from `heatSemigroup_pos_of_pos`.

Do **not** blindly rewrite the generic FAC lemmas in `IntervalChemDivFACCommuteDischarge.lean`. Those theorems are polymorphic in arbitrary

```lean
u : ℝ → intervalDomainPoint → ℝ
```

and assume

```lean
H : PhysicalResolverJointC2Data p u Bt
```

The direct theorem is heat-specific: it applies to

```lean
u = conjugatePicardIter p u₀ 0
```

not to arbitrary `u`.

The correct FAC move is to keep the generic physical-route lemmas and add heat-specific direct analogues, for example:

```lean
coupledChemical_innerCommute_of_heatDirect
coupledChemDivFlux_timeBridge_of_heatDirect
coupledChemDivFluxFactorJointC2Inputs_of_heatDirect
```

The heat-specific inner commute should copy the proof shape of `coupledChemical_innerCommute_of_physicalJointC2`, but replace the three value-`C²` calls with `heatResolver_jointContDiffAt_two`. The one important local edit is the spatial bridge: the physical proof uses all `r`, but the direct proof is positive-time/local. Use an eventual neighborhood `r ∈ Ioi c` around `s` with `c < s`, then call the direct theorem at `(r,y)`.

For the FAC flux time bridge, value `C²` alone is not enough. The bridge also needs:

```lean
hgradv : ContDiffAt ℝ 2 (spatial derivative of v)
hgv    : inner commute ∂ₜ∂ₓv = ∂ₓ∂ₜv
```

So a full direct FAC rewire needs direct replacements for value `C²`, gradient `C²`, and the inner commute. If `heatResolver_grad_jointContDiffAt_two` is also genuinely direct/sorry-free in your branch, then the heat Level0 FAC path can avoid `PhysicalResolverJointC2Data` entirely. If only the value theorem is direct, then only the `hv` leg is freed.

## Final list

Actual callers of `coupledChemical_jointContDiffAt_two`:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:30
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:38
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:50
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean:84
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:885
```
