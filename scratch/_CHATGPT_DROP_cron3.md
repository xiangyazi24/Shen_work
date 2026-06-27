# Q1079 (cron3): PhysicalResolverJointC2Data for heat Level0 after Option A `4000f01`

## Verdict

`PhysicalResolverJointC2Data` is constructed **directly** from `PhysicalSourceTimeC2` by:

```lean
ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor
```

There is no additional intermediate structure between `PhysicalSourceTimeC2` and `PhysicalResolverJointC2Data`. The only intermediate object is the coefficient-bound function:

```lean
Bt := fun i k => intervalNeumannResolverWeight p k * Es i k
```

where `Es := ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs hFSTD`.

However, after `4000f01`, the source-side producer `physicalSourceTimeC2_of_floored` is **not fully closed**: it contains new/remaining `sorry`s caused by the positive-time retyping. In addition, the heat-Level0 wrapper `heatSemigroup_level0_resolverJointC2Data` still has two summability sorries (`hval` and `hgrad`).

So the exact chain is:

```text
heatSemigroup_flooredSourceTimeData
  → hFSTD : FlooredSourceTimeData p (conjugatePicardIter p u₀ 0) ...
  → Es := builtEs hFSTD
  → physicalSourceTimeC2_of_floored hFSTD hval hgrad
  → hSTC2 : PhysicalSourceTimeC2 p (conjugatePicardIter p u₀ 0) Es
  → physicalResolverJointC2Data_of_floor hSTC2
  → PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0)
       (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

## Imports for the mapped construction

```lean
import ShenWork.Paper2.IntervalHeatSemigroupFlooredSourceTimeData
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
```

## Exact construction skeleton

```lean
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ScratchTrace

/-- Exact post-Option-A constructor path for heat Level0 resolver physical joint C² data. -/
theorem heatLevel0_physicalResolverJointC2Data_trace
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    -- still needed: weighted source majorant summability for the built `Es`
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointMajorant
        (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
          ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs
            (ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
              (p := p) hu₀_bound hu₀_cont) i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradMajorant
        (fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k *
          ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs
            (ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
              (p := p) hu₀_bound hu₀_cont) i k) m)) :
    ∃ Bt : ℕ → ℕ → ℝ,
      ShenWork.IntervalResolverJointC2PhysicalConcrete.PhysicalResolverJointC2Data
        p (conjugatePicardIter p u₀ 0) Bt := by
  -- Step 1: heat Level0 source-side floored data.
  let hFSTD :=
    ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
      (p := p) hu₀_bound hu₀_cont

  -- Step 2: built source envelope from the FlooredSourceTimeData.
  let Es : ℕ → ℕ → ℝ :=
    ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs hFSTD

  -- Step 3: source-time C² package.
  have hSTC2 :
      ShenWork.IntervalPhysicalResolverDataConcrete.PhysicalSourceTimeC2
        p (conjugatePicardIter p u₀ 0) Es := by
    simpa [Es, hFSTD] using
      ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored
        hFSTD hval hgrad

  -- Step 4: direct physical resolver joint C² constructor.
  refine ⟨fun i k => ShenWork.PDE.intervalNeumannResolverWeight p k * Es i k, ?_⟩
  exact ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor hSTC2

end ScratchTrace
```

This skeleton is exactly what `IntervalHeatSemigroupHighRegularity.lean` is already doing, except that the file keeps the `hval`/`hgrad` summability proofs as local `sorry`s.

## Where `PhysicalResolverJointC2Data` is defined

The structure is in `IntervalResolverJointC2PhysicalConcrete.lean`:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

The **constructor theorem** is in `IntervalPhysicalResolverDataConcrete.lean`:

```lean
theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

It is direct. It uses:

```lean
resolverTimeCoeff_eq_weight_smul
resolverTimeCoeff_bound
```

and then copies:

```lean
value_summable := H.value_summable
grad_summable  := H.grad_summable
```

## How `IntervalHeatSemigroupHighRegularity` uses it

The heat-Level0 wrapper is:

```lean
ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
```

Its body is already the exact chain:

```lean
set u := conjugatePicardIter p u₀ 0
have hFSTD := heatSemigroup_flooredSourceTimeData hu₀_bound hu₀_cont (p := p)
set Es := builtEs hFSTD
have hSTC2 : PhysicalSourceTimeC2 p u Es :=
  physicalSourceTimeC2_of_floored hFSTD
    (by intro m hm; sorry)   -- value_summable
    (by intro m hm; sorry)   -- grad_summable
exact ⟨_, physicalResolverJointC2Data_of_floor hSTC2⟩
```

Then the public consumer theorem is:

```lean
ShenWork.Paper2.HeatResolverJointRegularity.heatResolverJointContDiffAt_two
```

It does:

```lean
obtain ⟨Bt, hBt⟩ := heatSemigroup_level0_resolverJointC2Data
  (p := p) hu₀_bound hu₀_cont
exact coupledChemical_jointContDiffAt_two hBt hx₀
```

So `heatResolverJointContDiffAt_two` uses `PhysicalResolverJointC2Data` only through:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_jointContDiffAt_two
```

There is no spectral `DuhamelSourceTimeC2Coeff` step on this route.

## Does `physicalSourceTimeC2_of_floored` have new/remaining sorries after `4000f01`?

Yes. At ref `4000f01`, `IntervalPhysicalSourceTimeC2Concrete.lean` has four relevant `sorry`s in the `physicalSourceTimeC2_of_floored` section.

### 1. `srcTimeCoeff_contDiffAt`

```lean
theorem srcTimeCoeff_contDiffAt
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) t := by
  sorry
```

What it needs:

* use `srcTimeCoeff_hasDerivAt H k ht` for the first derivative at positive times;
* use `cosS1_hasDerivAt H k ht` for the second derivative at positive times;
* use `cosS2_continuousAt H k ht` for continuity of the second derivative;
* assemble local `ContDiffAt ℝ 2` on the open neighborhood inside `Ioi 0`.

This is local calculus / positive-time assembly, not new PDE analysis.

### 2. `srcTimeCoeff_iteratedDeriv2`

```lean
private theorem srcTimeCoeff_iteratedDeriv2
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (srcTimeCoeff p u k) t = cosineCoeffs (s₂ t) k := by
  sorry
```

What it needs:

* show near `t` (inside `Ioi 0`) that
  `iteratedDeriv 1 (srcTimeCoeff p u k) s = cosineCoeffs (s₁ s) k`
  using `srcTimeCoeff_hasDerivAt H k hs`;
* then take `deriv` at `t` and use `cosS1_hasDerivAt H k ht`.

Again, this is a local positive-time derivative bookkeeping proof.

### 3. `src_contDiff` field inside `physicalSourceTimeC2_of_floored`

```lean
src_contDiff k := by
  -- The positive-time data gives ContDiffAt at every t > 0 via
  -- srcTimeCoeff_contDiffAt.  Extension to global ContDiff on ℝ
  -- follows from the structure of srcTimeCoeff (defined on all ℝ).
  sorry
```

What it needs:

This is the real type mismatch introduced by positive-time weakening. `PhysicalSourceTimeC2` still asks for global:

```lean
∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
```

but `FlooredSourceTimeData` now supplies only positive-time information. To fill this without retyping, one must prove global `ContDiff` by separately handling `t ≤ 0` from the concrete definition of `srcTimeCoeff`. The alternative is to retype `PhysicalSourceTimeC2.src_contDiff` to positive-time, e.g. `∀ k t, 0 < t → ContDiffAt ... t`, which would match the new `FlooredSourceTimeData` more honestly.

### 4. `src_bound` field inside `physicalSourceTimeC2_of_floored`

```lean
src_bound i k t hi := by
  -- For t > 0: srcTimeCoeff_bound H i k t hi ht.
  -- For t ≤ 0: separate envelope argument from the definition of srcTimeCoeff.
  sorry
```

What it needs:

For `t > 0`, this is already:

```lean
srcTimeCoeff_bound H i k t hi ht
```

For `t ≤ 0`, the current global `PhysicalSourceTimeC2` type still demands a bound:

```lean
‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ builtEs H i k
```

so it needs either a separate nonpositive-time envelope proof, or the same positive-time retyping of `PhysicalSourceTimeC2.src_bound`.

## Remaining sorries in the heat-Level0 wrapper

Even if `physicalSourceTimeC2_of_floored` is fixed, `heatSemigroup_level0_resolverJointC2Data` still needs the two weighted summability proofs:

```lean
hval : ∀ m ≤ 2,
  Summable (boundedWeightJointMajorant
    (fun i k => intervalNeumannResolverWeight p k * builtEs hFSTD i k) m)

hgrad : ∀ m ≤ 2,
  Summable (boundedWeightJointGradMajorant
    (fun i k => intervalNeumannResolverWeight p k * builtEs hFSTD i k) m)
```

The comments say these should follow from the `(kπ)⁻²` decay in `builtEs` plus the elliptic weight:

```lean
wₖ = intervalNeumannResolverWeight p k = 1 / (p.μ + λ_k)
```

Useful existing lemmas include:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.eigenvalue_mul_resolverWeight_le_one
ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu
ShenWork.IntervalResolverJointC2PhysicalConcrete.valueCosWeight_one_mul_resolverWeight_le
```

The target is finite because `builtEs` has a zeroth-mode constant and a `(kπ)⁻²` bound for `k ≥ 1`, while the worst value/gradient weights are absorbed by the elliptic factor and the declared majorant structure.

## Answer to the critical question

`PhysicalResolverJointC2Data` is **directly** constructed from `PhysicalSourceTimeC2` by:

```lean
physicalResolverJointC2Data_of_floor
```

No additional named structure sits in between. The exact bridge is:

```lean
PhysicalSourceTimeC2 p u Es
  → PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

The post-`4000f01` blockers are not between `PhysicalSourceTimeC2` and `PhysicalResolverJointC2Data`; they are **upstream**:

1. the six heat-Level0 `FlooredSourceTimeData` sorries in `heatSemigroup_flooredSourceTimeData`;
2. the four positive-time-to-global sorries in `physicalSourceTimeC2_of_floored` and its helpers;
3. the two `hval/hgrad` bounded-weight summability sorries in `heatSemigroup_level0_resolverJointC2Data`.

Once those are supplied, the resolver construction is one theorem call:

```lean
ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor hSTC2
```
