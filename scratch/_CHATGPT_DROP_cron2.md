# Q1060 + Q1051 (cron2) — closed reps and Option A floor weakening

Static GitHub-connector inspection only; I did **not** run Lean.

I treated the pasted prompt as two questions:

1. **Q1060:** whether `PhysicalResolverJointC2Data` and its 3F/3G producers also provide the closed-slab continuous representatives needed for 1A and 2A-sup.
2. **Q1051:** whether weakening `IterateSourceTimeData.floor` from all-time positivity to positive-time positivity is really an ~11-file one-line Option A that makes the heat-base `FlooredSourceTimeData` and downstream `PhysicalResolverJointC2Data` fillable.

---

## Executive verdict

### Q1060

**No.** `PhysicalResolverJointC2Data` does not by itself provide the closed-slab continuous representatives needed for 1A and 2A-sup.

It gives interior resolver joint `C²` and, through `IntervalChemDivFACCommuteDischarge.lean`, discharges the **flux time-partial bridge**. But the closed-slab representative required for `htime_cont` is still a separate datum/proof lane. In `IntervalChemDivTimeDerivClosed.lean`, the key object is explicitly:

```lean
import ShenWork.PDE.IntervalChemDivTimeDerivClosed

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

#check ChemDivMixedTimeDerivClosedRepr
#check chemDivMixedTimeDeriv_jointContinuousOn_closed
#check coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged

end ShenWork.IntervalCoupledRegularityBootstrap
```

`chemDivMixedTimeDeriv_jointContinuousOn_closed` transfers continuity from a representative `Gmix`; it does not construct `Gmix` from `PhysicalResolverJointC2Data` alone.

There are later representative producers, but they require extra inputs. `IntervalChemDivMixedReprConstruct.lean` isolates a `ChemDivMixedReprData` bundle of ten globally continuous representatives, and `IntervalChemDivMixedReprWitness.lean` / `IntervalIterateGradMajorant.lean` assemble such a witness from:

```lean
import ShenWork.PDE.IntervalIterateGradMajorant

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalResolverJointC2Physical (boundedWeightJointGradMajorant)
open ShenWork.IntervalIteratePicardJointC2 (IteratePicardJointC2Data)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (PhysicalResolverJointC2Data resolverTimeCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalChemDivMixedReprConstruct
open ShenWork.IntervalChemDivMixedReprWitness
open ShenWork.IntervalIterateGradMajorant

noncomputable section

namespace ShenWork.IntervalIterateGradMajorant

#check chemDivMixedClosedRepr_of_iterateGradSummable

end ShenWork.IntervalIterateGradMajorant
```

That route consumes not just `PhysicalResolverJointC2Data`, but also iterate joint-`C²`, iterate gradient majorant summability, a resolver-representative floor, and a boundary equality. Thus the closed-representative work is **separate** from the bare physical resolver joint-`C²` data.

For 1A and 2A-sup, Q1032’s warning still applies: an interior `FluxJointC2Hyp` gives joint `C²` on the interior, but a compact uniform bound needs a continuous representative on the closed slab, including endpoint behavior. The existing `Gmix` lane may be reusable, but 1A’s `secondDeriv` bound and 2A-sup’s source sup bound still need their own closed-representative bridge for the exact fields they bound.

### Q1051

I do **not** confirm the “~11 files, each ~1 line” claim from the repo surface I inspected.

The actual `IterateSourceTimeData.floor` code surface I found is small, but weakening the field is **not** a pure one-line change as typed, because the producer still targets all-time `FlooredSourceTimeData`. After weakening, the existing proof calls need a proof that the local time `s` is positive, and the current target quantifies over arbitrary `τ : ℝ` and `s ∈ Metric.ball τ δ`.

Also, the heat semigroup six obligations in `IntervalHeatSemigroupFlooredSourceTimeData.lean` do **not** become fillable merely by weakening `IterateSourceTimeData.floor`, because that file directly targets all-time `FlooredSourceTimeData`, including `t = 0`.

---

## Q1060 — detailed trace

### What `PhysicalResolverJointC2Data` gives

In `IntervalResolverJointC2PhysicalConcrete.lean`, `PhysicalResolverJointC2Data` is a coefficient regularity/summability package. It yields:

```lean
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalResolverJointC2PhysicalConcrete

noncomputable section

namespace ShenWork.IntervalResolverJointC2PhysicalConcrete

#check PhysicalResolverJointC2Data
#check coupledChemical_jointContDiffAt_two
#check coupledChemical_grad_jointContDiffAt_two

end ShenWork.IntervalResolverJointC2PhysicalConcrete
```

Those two producer theorems are interior: they require `x ∈ Ioo 0 1`. They are enough for the local Clairaut/time-bridge work, but they are not closed-slab representative theorems.

### What `IntervalChemDivFACCommuteDischarge.lean` discharges

`IntervalChemDivFACCommuteDischarge.lean` proves:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

#check coupledChemical_innerCommute_of_physicalJointC2
#check coupledChemDivFlux_timeBridge_of_physicalJointC2
#check coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged

end ShenWork.IntervalCoupledRegularityBootstrap
```

The important point is that `coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged` still takes an `other` bundle containing:

* eventual closed-slice source continuity;
* u-side Picard joint `C²`;
* closed-slab continuity of `Function.uncurry (coupledChemDivTimeDerivativeLift p u)`.

So 3F discharges the flux time bridge, not all closed-representative obligations.

### What `IntervalChemDivTimeDerivClosed.lean` discharges

`IntervalChemDivTimeDerivClosed.lean` defines the representative requirement:

```lean
import ShenWork.PDE.IntervalChemDivTimeDerivClosed

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

example (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)

end ShenWork.IntervalCoupledRegularityBootstrap
```

Then `chemDivMixedTimeDeriv_jointContinuousOn_closed` converts this representative into the closed-slab `ContinuousOn`. This is a separate assumption/producer input, not a corollary of `PhysicalResolverJointC2Data` alone.

---

## Q1051 — exact file surface and cascade

### Files found

I cannot verify an 11-file list. The relevant files I found are:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean  (read from main)
```

Additional search hits were comments/docs:

```text
ShenWork/PDE/IntervalIteratePicardJointC2.lean
ShenWork/Paper2/IntervalBootstrapDecomp.lean
ShenWork/Paper2/IntervalCosineSobolevEmbedding.lean
UNDERSTANDING.md
BANK_CHECKLIST.md
```

The exact `H.floor` use I found was only in `ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean`.

### Why the field weakening is not enough

Current shape:

```lean
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalFlooredSourceTimeDataIterate

-- Current field shape inside `IterateSourceTimeData`:
example (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, 0 < intervalDomainLift (u t) x

-- Proposed positive-time field shape:
example (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x ∈ Ioo (0 : ℝ) 1,
    0 < intervalDomainLift (u t) x

end ShenWork.IntervalFlooredSourceTimeDataIterate
```

But `flooredSourceTimeData_of_iterate` currently uses the floor as:

```lean
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalFlooredSourceTimeDataIterate

-- Existing proof pattern:
--   exact hasDerivAt_srcSlice (H.floor s x hx) (hdiff x hx s hs)
--   exact hasDerivAt_srcSlice1 (H.floor s x hx) h1 h2
--
-- After weakening, those calls need:
--   have hspos : 0 < s := ?_
--   exact hasDerivAt_srcSlice (H.floor s hspos x hx) (hdiff x hx s hs)
--   exact hasDerivAt_srcSlice1 (H.floor s hspos x hx) h1 h2

end ShenWork.IntervalFlooredSourceTimeDataIterate
```

The missing `hspos : 0 < s` is not available from the current all-time `FlooredSourceTimeData` target. Its `d0` and `d1` fields quantify over every `τ : ℝ`; for `τ ≤ 0`, the local ball cannot be made entirely positive without changing the target.

### Why the six heat-base obligations do not become fillable as typed

`IntervalHeatSemigroupFlooredSourceTimeData.lean` directly targets:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice sliceFam FlooredSourceTimeData)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

#check heatSemigroup_flooredSourceTimeData

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

That theorem returns an all-time `FlooredSourceTimeData`, not an `IterateSourceTimeData`. The heat smoothing lemmas I saw in `IntervalHeatSemigroupHighRegularity.lean` are positive-time statements, e.g. `heatSemigroup_contDiff_four` requires `0 < t`, and the joint cutoff argument is local around `s₀ > c > 0`.

Thus the six heat obligations are plausible on a positive window `[c,T]`, `0 < c`, but not as all-time obligations for merely continuous `u₀`. At `t = 0`, the heat slice is just `u₀`; it need not be spatial `C²`, satisfy the Neumann derivative data, or have the uniform Laplacian bounds needed for the `(kπ)⁻²` envelope.

---

## Direct answers to Q1051’s numbered questions

### 1. Exact 11 files?

Not verified. I found the real code surface listed above, not 11 files. The exact `H.floor` use appears only in `IntervalFlooredSourceTimeDataIterate.lean`.

### 2. One-line or cascading?

Cascading. The immediate break is that positive-time-only `floor` requires an `0 < s` proof inside `flooredSourceTimeData_of_iterate`, but the current all-time target does not provide one.

### 3. Would the six heat sorries become fillable?

Not as typed. They become plausible only after a positive-window retyping or stronger initial-data assumptions. The current all-time `FlooredSourceTimeData` still hits `t = 0`.

### 4. Would this fill `PhysicalResolverJointC2Data` and close 3C/3D directly?

Not directly as typed. A positive-window Option A route could avoid the VOC / `DuhamelSourceTimeC2Coeff` route for positive-time consumers, but it needs a windowed source/resolver package and downstream consumer wiring. Merely weakening `IterateSourceTimeData.floor` does not fill the current all-time `FlooredSourceTimeData` gate.

---

## Recommended route

The safe version of Option A is not just a field weakening. It is a positive-window split:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice sliceFam)

noncomputable section

namespace ShenWork.IntervalPhysicalSourceTimeC2Concrete

/-- Schematic positive-window replacement for the all-time source package. -/
structure FlooredSourceTimeDataOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) (c T : ℝ) : Prop where
  hc : 0 < c
  hct : c ≤ T
  d0 : ∀ τ ∈ Icc c T, ∃ δ : ℝ, 0 < δ ∧ True
  d1 : ∀ τ ∈ Icc c T, ∃ δ : ℝ, 0 < δ ∧ True
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t ∈ Icc c T,
    ContDiffOn ℝ 2 ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0 : ℝ) 1)
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t ∈ Icc c T, True
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ True
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ True

end ShenWork.IntervalPhysicalSourceTimeC2Concrete
```

Then prove the six heat obligations on `[c,T]` using positive-time heat smoothing, add a windowed physical resolver producer, and feed only positive-time FAC consumers. Separately, close 1A and 2A-sup by proving closed-slab representatives for the exact fields their compactness bounds consume.
