# Q1083 (cron2) — does `heatResolverJointContDiffAt_two` already exist?

Static GitHub-connector inspection only; I did **not** run Lean locally.  I used GitHub code/file search plus direct file fetches from the connected repo.

## Short answer

Yes.  The exact theorem exists:

```text
ShenWork.Paper2.HeatResolverJointRegularity.heatResolverJointContDiffAt_two
```

It is in:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:861
```

The theorem itself has **0 local `sorry`** in its body, but it is **upstream-sorry-tainted**: it calls `heatSemigroup_level0_resolverJointC2Data`, which has 2 local `sorry`s, and that producer calls `heatSemigroup_flooredSourceTimeData`, which has 6 local `sorry`s.  So the known upstream sorry count on this route is **8**.

## Search report

| Query | Result |
|---|---|
| `heatResolverJointContDiffAt_two` | Found in `IntervalHeatSemigroupHighRegularity.lean` and mentioned in `UNDERSTANDING.md`. |
| `heatResolver_jointContDiffAt` | No result found by GitHub connector search. |
| `resolver jointContDiffAt two` / resolver-ish joint C² names | Relevant hits are the generic physical producers `coupledChemical_jointContDiffAt_two` and `coupledChemical_grad_jointContDiffAt_two`, plus the Level0 wrapper `heatResolverJointContDiffAt_two`. |
| Theorem in `IntervalHeatSemigroupHighRegularity.lean` giving resolver joint C² | `heatResolverJointContDiffAt_two` at line 861. |

## Exact theorem in `IntervalHeatSemigroupHighRegularity.lean`

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data coupledChemical_jointContDiffAt_two resolverTimeCoeff)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

#check heatResolverJointContDiffAt_two

/-- Current committed theorem, copied from the inspected file. -/
theorem heatResolverJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (_hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀) := by
  -- `_hc` and `_hs₀` are retained in the API for downstream callers that pass
  -- a time-positivity witness; the bounded-weight route via
  -- `PhysicalResolverJointC2Data` is globally valid (no time cutoff needed).
  obtain ⟨Bt, hBt⟩ := heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont
  exact coupledChemical_jointContDiffAt_two hBt hx₀

end ShenWork.Paper2.HeatResolverJointRegularity
```

Line map from the inspected file:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:735
  theorem heatSemigroup_jointContDiffAt_two

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:822
  theorem heatSemigroup_level0_resolverJointC2Data

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:842
  sorry  -- value_summable for physicalSourceTimeC2_of_floored

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:845
  sorry  -- grad_summable for physicalSourceTimeC2_of_floored

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:861
  theorem heatResolverJointContDiffAt_two

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:877
  #print axioms heatResolverJointContDiffAt_two
```

## What are the `sorry`s?

### Local body of `heatResolverJointContDiffAt_two`

No local `sorry` in the theorem body.  The theorem just extracts `PhysicalResolverJointC2Data` from `heatSemigroup_level0_resolverJointC2Data` and applies the generic physical producer `coupledChemical_jointContDiffAt_two`.

### Upstream producer: `heatSemigroup_level0_resolverJointC2Data`

This is the immediate dependency of `heatResolverJointContDiffAt_two` and has 2 local `sorry`s:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

#check heatSemigroup_level0_resolverJointC2Data

/-- Excerpt: the two direct `sorry`s in the current upstream data producer. -/
theorem heatSemigroup_level0_resolverJointC2Data_sorry_excerpt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
  set u := conjugatePicardIter p u₀ 0
  have hFSTD := ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
    hu₀_bound hu₀_cont (p := p)
  set Es := ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs hFSTD
  have hSTC2 : ShenWork.IntervalPhysicalResolverDataConcrete.PhysicalSourceTimeC2 p u Es :=
    ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored hFSTD
      (by
        -- value_summable: ∀ m ≤ 2,
        --   Summable (boundedWeightJointMajorant (wₖ·Es) m)
        intro m hm
        sorry)
      (by
        -- grad_summable: ∀ m ≤ 2,
        --   Summable (boundedWeightJointGradMajorant (wₖ·Es) m)
        intro m hm
        sorry)
  exact ⟨_, ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor hSTC2⟩

end ShenWork.Paper2.HeatResolverJointRegularity
```

The two direct holes are:

1. `value_summable`: prove `∀ m ≤ 2, Summable (boundedWeightJointMajorant (wₖ·Es) m)`.
2. `grad_summable`: prove `∀ m ≤ 2, Summable (boundedWeightJointGradMajorant (wₖ·Es) m)`.

### Upstream source-time floor producer: `heatSemigroup_flooredSourceTimeData`

`heatSemigroup_level0_resolverJointC2Data` calls `heatSemigroup_flooredSourceTimeData`.  That theorem currently has 6 local `sorry`s:

```text
ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean:103
  theorem heatSemigroup_flooredSourceTimeData

ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean:117
  sorry  -- d0

ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean:125
  sorry  -- d1

ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean:136
  sorry  -- sliceC2

ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean:143
  sorry  -- sliceNeumann

ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean:151
  sorry  -- zerothBound

ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean:160
  sorry  -- laplBound
```

The six fields are:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData (heatDu heatD2u)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

#check heatSemigroup_flooredSourceTimeData

/-- Shape of the six-field producer; each field is currently sorry'd in the file. -/
example
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀) :
    ShenWork.IntervalPhysicalSourceTimeC2Concrete.FlooredSourceTimeData
      p (conjugatePicardIter p u₀ 0)
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) := by
  exact heatSemigroup_flooredSourceTimeData _hu₀_bound _hu₀_cont

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

## Generic resolver joint-C² producers found

The Level0 theorem is a wrapper over generic producers in `IntervalResolverJointC2PhysicalConcrete.lean`:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean:116
  theorem coupledChemical_jointContDiffAt_two

ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean:138
  theorem coupledChemical_grad_jointContDiffAt_two
```

These are the value and gradient resolver joint-C² producers from `PhysicalResolverJointC2Data`.

```lean
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete

open ShenWork.IntervalResolverJointC2PhysicalConcrete

#check coupledChemical_jointContDiffAt_two
#check coupledChemical_grad_jointContDiffAt_two
```

The value theorem is what `heatResolverJointContDiffAt_two` applies.  There is **not** currently a separate heat-Level0 gradient wrapper named something like `heatResolverGradJointContDiffAt_two` in `IntervalHeatSemigroupHighRegularity.lean`; instead, once `Bt, hBt` are available from `heatSemigroup_level0_resolverJointC2Data`, the gradient version follows directly by applying `coupledChemical_grad_jointContDiffAt_two hBt hx₀`.

## Bottom line

`heatResolverJointContDiffAt_two` already exists, but it is not an axiom-clean direct cutoff proof.  It is a wrapper around `PhysicalResolverJointC2Data`:

```text
heatResolverJointContDiffAt_two
  depends on heatSemigroup_level0_resolverJointC2Data
    has 2 local sorries: value_summable, grad_summable
    depends on heatSemigroup_flooredSourceTimeData
      has 6 local sorries: d0, d1, sliceC2, sliceNeumann, zerothBound, laplBound
```

So the accurate count is:

```text
local sorries in heatResolverJointContDiffAt_two: 0
known upstream sorries on its current route: 8
```
