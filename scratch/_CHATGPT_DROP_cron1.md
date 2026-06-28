# Q1575 (cron1) -- can old heat resolver theorem delegate to direct route?

Repository: `xiangyazi24/Shen_work`  
Branch committed: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Note on inspection branch

The delivery target is `chatgpt-scratch`.  The connector could not fetch

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

from `chatgpt-scratch`, so I inspected the indexed/default repo files.  The analysis below is therefore about the current/default code surface returned by GitHub search.  The scratch answer itself is committed to `chatgpt-scratch` as requested.

## Executive answer

At the type/signature level: **yes**, the old route theorem

```lean
HeatResolverJointRegularity.heatResolverJointContDiffAt_two
```

can be proved by delegating to the direct theorem

```lean
HeatResolverJointC2Direct.heatResolver_jointContDiffAt_two
```

because the old theorem has all inputs needed to manufacture the direct theorem's extra `hfloor` hypothesis:

```lean
hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

from `hu₀_cont` and `hu₀_pos`, using

```lean
HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
```

and the old theorem already carries `hc : 0 < c`, `hs₀ : c < s₀`, and `hx₀ : x₀ ∈ Ioo 0 1`.

But there are two important caveats.

1. **Import cycle:** currently `IntervalHeatResolverJointC2.lean` imports `IntervalHeatSemigroupHighRegularity.lean`.  Therefore `IntervalHeatSemigroupHighRegularity.lean` cannot simply import the direct file and delegate to it without creating a cycle.

2. **Current direct file still depends on the old physical route in the fetched code.**  In the fetched current/default file, the direct majorant and gradient proof extract

```lean
HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
```

from the old route.  So if that is still true in the branch being built, then delegating the old theorem to the direct theorem would be circular and would not remove the old-route sorry burden.  If the new 0-sorry direct route has been refactored to avoid this dependency, then the wrapper below is the right replacement after resolving the import placement.

## Exact signatures

### Direct theorem

Current/default `IntervalHeatResolverJointC2.lean` has:

```lean
theorem heatResolver_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p
            (conjugatePicardIter p u₀ 0) q.1) q.2)
        (s₀, x₀)
```

### Old theorem

Current/default `IntervalHeatSemigroupHighRegularity.lean` has:

```lean
theorem heatResolverJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {c : ℝ} (_hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀)
```

So the conclusions match exactly, and the old route has enough inputs to call the direct theorem.

## Concrete wrapper proof

If the import cycle is solved, the old theorem can be replaced by:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

namespace ShenWork.Paper2.HeatResolverJointRegularity

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)

/-- Old route theorem delegated to the direct cutoff resolver theorem. -/
theorem heatResolverJointContDiffAt_two_directWrapper
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀) := by
  have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
    intro t ht x hx
    exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
      (p := p) hu₀_cont hu₀_pos ht hx
  exact ShenWork.Paper2.HeatResolverJointC2Direct.heatResolver_jointContDiffAt_two
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hu₀_pos hfloor hc hs₀ hx₀

end ShenWork.Paper2.HeatResolverJointRegularity
```

To use this as the actual old theorem body, put the body in a place where the direct theorem is already available without import cycle.  Do **not** add

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
```

at the top of `IntervalHeatSemigroupHighRegularity.lean` while `IntervalHeatResolverJointC2.lean` imports `IntervalHeatSemigroupHighRegularity.lean`.

## How to resolve the import-cycle issue

There are three workable approaches.

### Option A: move the old wrapper out of the old file

Create a new downstream adapter file, for example:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2Adapter.lean
```

that imports both files and proves a new name, e.g.

```lean
heatResolverJointContDiffAt_two_of_direct
```

This avoids cycles, but it does not replace callers that refer to the old exact theorem name.

### Option B: move the direct theorem lower

Split the direct route into a lower file that does **not** import `IntervalHeatSemigroupHighRegularity.lean`.  Then `IntervalHeatSemigroupHighRegularity.lean` can import that lower direct file and define the old theorem by delegation.

This is the clean replacement if callers must keep the exact old theorem name.

### Option C: stop using the old theorem name

If the FAC chain does not actually call `heatResolverJointContDiffAt_two`, update the relevant Level0/FAC caller to import and use the direct theorem directly, or better, use a direct package that provides both value and gradient C² fields.

## Important caveat: the fetched direct theorem is not independent yet

In the fetched current/default `IntervalHeatResolverJointC2.lean`, the majorant and gradient still depend on old-route `PhysicalResolverJointC2Data`:

```lean
obtain ⟨Bt, hBt⟩ :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont hu₀_pos
```

This appears in `cutoffResolverMajorant_summable` and `cutoffResolverTerm_iteratedFDeriv_bound`.  The gradient theorem also ends by applying

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_grad_jointContDiffAt_two hBt hx₀
```

after extracting the same old-route data.

Therefore, under the fetched code, delegating old theorem to direct theorem would be circular.  It only becomes a real solution if the new 0-sorry direct route has removed this dependency and proves both value and gradient from cutoff/`contDiff_tsum` directly.

## Does the FAC chain actually need `heatResolverJointContDiffAt_two`?

I do **not** see direct code-search consumers of the old theorem name outside `IntervalHeatSemigroupHighRegularity.lean` and documentation.

The actual FAC/resolver C² chain has two main surfaces.

### Physical resolver route

`IntervalChemDivFACCommuteDischarge.lean` uses `PhysicalResolverJointC2Data` and then calls:

```lean
coupledChemical_jointContDiffAt_two H hy
coupledChemical_grad_jointContDiffAt_two H hy
```

So this route needs a `PhysicalResolverJointC2Data` package, not the old standalone `heatResolverJointContDiffAt_two` theorem.

### Spectral C2 data route

`IntervalChemDivFluxFactorFAC.lean` uses:

```lean
coupledChemicalConcentration_resolver_jointC2At_c2Data
```

from `IntervalCoupledResolverJointC2.lean`, taking a `ResolverHasSpectralAgreementC2Coeff` package and a local spectral-series producer.  This route also does not call the old standalone theorem by name.

So the FAC chain generally needs **both value and gradient C²** at the resolver, supplied either by:

```lean
coupledChemical_jointContDiffAt_two / coupledChemical_grad_jointContDiffAt_two
```

from `PhysicalResolverJointC2Data`, or by

```lean
coupledChemicalConcentration_resolver_jointC2At_c2Data
```

from a spectral C2 package.

A standalone value-only theorem `heatResolverJointContDiffAt_two` is not enough for the full FAC fields unless paired with the gradient theorem.

## Recommendation

If the new direct route is truly independent and axiom-clean:

1. Keep `IntervalHeatResolverJointC2.lean` as the direct value+gradient provider.
2. Add a small Level0-specific FAC adapter that uses:

```lean
HeatResolverJointC2Direct.heatResolver_jointContDiffAt_two
HeatResolverJointC2Direct.heatResolver_grad_jointContDiffAt_two
```

for the `hv_c2` and `hgradv_c2` FAC fields.

3. Do not try to route through `PhysicalResolverJointC2Data` unless you also want to discharge the old source-time-C² / `FlooredSourceTimeData` chain.

If callers require the exact old name `HeatResolverJointRegularity.heatResolverJointContDiffAt_two`, first break the import cycle by moving the direct theorem to a lower file, then replace the old theorem body with the wrapper above.

## Final verdict

* Typewise, old `heatResolverJointContDiffAt_two` can delegate to direct `heatResolver_jointContDiffAt_two`; `hfloor` is derivable from `hu₀_cont + hu₀_pos`.
* Filewise, direct import currently points from direct file to old file, so old file cannot import direct without a cycle.
* In the fetched code, direct theorem still depends on old physical-route data in majorant/gradient pieces; if still true, delegation is circular and not a real fix.
* FAC does not appear to need the old theorem name directly. It needs resolver value+gradient C², usually through `PhysicalResolverJointC2Data` or `ResolverHasSpectralAgreementC2Coeff`; a Level0 direct adapter using both direct theorems is the cleanest way to bypass the old route.
