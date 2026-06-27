# Q1084 (cron2) — `heatResolverJointContDiffAt_two` and direct cutoff Option B

Static GitHub-connector inspection only; I did **not** run Lean locally.

## Verdict

`heatResolverJointContDiffAt_two` **is already committed** in:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

But the committed theorem is **not** the direct cutoff-plus-`contDiff_tsum` Option B described in the prompt.  It is the existing *physical data* route:

```text
heatSemigroup_flooredSourceTimeData
  → physicalSourceTimeC2_of_floored
  → physicalResolverJointC2Data_of_floor
  → heatSemigroup_level0_resolverJointC2Data
  → coupledChemical_jointContDiffAt_two
  → heatResolverJointContDiffAt_two
```

So the answer to the key question is:

* **As currently committed:** yes, `heatResolverJointContDiffAt_two` still needs the `FlooredSourceTimeData` lane through `heatSemigroup_level0_resolverJointC2Data`.
* **For the proposed direct cutoff Option B:** no, it should bypass `FlooredSourceTimeData` entirely.  It still needs positive-time source coefficient regularity and summable bounded-weight majorants, but those should be proved locally/on the cutoff window, not packaged as global/all-time `FlooredSourceTimeData`.

## Exact current committed theorem

The current theorem body is already present and is short:

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

/-- Current committed theorem: resolver joint `C²` at heat Level0.

This theorem is committed, but it is not the direct cutoff proof.  It obtains
`PhysicalResolverJointC2Data` from `heatSemigroup_level0_resolverJointC2Data`, then
uses the generic physical assembler `coupledChemical_jointContDiffAt_two`. -/
theorem heatResolverJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (_hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀) := by
  obtain ⟨Bt, hBt⟩ := heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont
  exact coupledChemical_jointContDiffAt_two hBt hx₀

end ShenWork.Paper2.HeatResolverJointRegularity
```

Notice the important diagnostic: `_hc` and `_hs₀` are unused.  A true cutoff proof would use them to choose the positive-time cutoff window.  The current theorem ignores them because it relies on globally packaged `PhysicalResolverJointC2Data`.

## What `sorry` does the committed theorem have?

The theorem body itself has no local `sorry`, but it depends on `heatSemigroup_level0_resolverJointC2Data`, which currently has two local `sorry` blocks for the summability hypotheses needed by `physicalSourceTimeC2_of_floored`:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

/-- Upstream data producer used by the current `heatResolverJointContDiffAt_two`.
The two local holes are exactly the `value_summable` and `grad_summable` inputs. -/
theorem heatSemigroup_level0_resolverJointC2Data_excerpt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      ShenWork.IntervalResolverJointC2PhysicalConcrete.PhysicalResolverJointC2Data
        p (conjugatePicardIter p u₀ 0) Bt := by
  set u := conjugatePicardIter p u₀ 0
  have hFSTD :=
    ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
      hu₀_bound hu₀_cont (p := p)
  set Es := ShenWork.IntervalPhysicalSourceTimeC2Concrete.builtEs hFSTD
  have hSTC2 :
      ShenWork.IntervalPhysicalResolverDataConcrete.PhysicalSourceTimeC2 p u Es :=
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
  exact ⟨_,
    ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor hSTC2⟩

end ShenWork.Paper2.HeatResolverJointRegularity
```

And `heatSemigroup_level0_resolverJointC2Data` calls `heatSemigroup_flooredSourceTimeData`, whose six fields are still sorry'd:

```text
d0
d1
sliceC2
sliceNeumann
zerothBound
laplBound
```

Those six are the floor/source-slice obligations, while the two in `heatSemigroup_level0_resolverJointC2Data` are the weighted value/gradient summability obligations.  Therefore the current committed theorem should still be considered axiom-tainted through upstream `sorryAx`.

## Direct cutoff Option B status

I found no committed direct resolver cutoff theorem analogous to the heat semigroup chain:

```text
heatTerm
cutoffHeatTerm
cutoffHeatTerm_contDiff_two
cutoffHeatTerm_iteratedFDeriv_bound
cutoffHeatSeries_contDiff_two
heatSeries_eventuallyEq_cutoff
heatSemigroup_jointContDiffAt_two
```

For the resolver, the closest already-committed reusable infrastructure is not a resolver cutoff theorem, but the generic bounded-weight physical assembler:

```text
IntervalResolverJointC2Physical.boundedWeightJointTerm
IntervalResolverJointC2Physical.boundedWeightJointMajorant
IntervalResolverJointC2Physical.boundedWeightJointTerm_contDiff
IntervalResolverJointC2Physical.boundedWeightJointTerm_iteratedFDeriv_le
IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two
IntervalResolverJointC2PhysicalConcrete.coupledChemical_lift_eq_series
IntervalResolverJointC2PhysicalConcrete.coupledChemical_jointContDiffAt_two
```

The direct cutoff proof should reuse this bounded-weight series machinery, but with **cutoff resolver coefficients** instead of demanding global `PhysicalResolverJointC2Data`.

## What the direct route should look like

A clean direct theorem should introduce a cutoff coefficient

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverJointC2Physical
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant boundedWeightJointSeries_contDiff_two)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (resolverTimeCoeff coupledChemical_lift_eq_series)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff smoothRightCutoff_eventually_eq_one)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

/-- Cut off the resolver coefficient in positive time. -/
def cutoffResolverCoeff
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (c : ℝ) : ℕ → ℝ → ℝ :=
  fun k t => smoothRightCutoff (c / 2) c t *
    resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t

/-- The cutoff resolver series. -/
def cutoffResolverSeries
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (c : ℝ) : ℝ × ℝ → ℝ :=
  fun q => ∑' k : ℕ,
    boundedWeightJointTerm (cutoffResolverCoeff p u₀ c) k q

end ShenWork.Paper2.HeatResolverJointRegularity
```

Then prove these new local/windowed lemmas:

```text
cutoffResolverCoeff_contDiff_two
  : ContDiff ℝ 2 (cutoffResolverCoeff p u₀ c k)

cutoffResolverCoeff_iteratedFDeriv_bound
  : ‖iteratedFDeriv ℝ i (cutoffResolverCoeff p u₀ c k) t‖ ≤ B i k

cutoffResolverMajorant_summable
  : ∀ m ≤ 2, Summable (boundedWeightJointMajorant B m)

cutoffResolverSeries_contDiff_two
  : ContDiff ℝ 2 (cutoffResolverSeries p u₀ c)

resolverSeries_eventuallyEq_cutoff
  : original resolver lift series =ᶠ[𝓝 (s₀, x₀)] cutoffResolverSeries p u₀ c

heatResolverJointContDiffAt_two_direct
  : ContDiffAt ℝ 2 (fun q => intervalDomainLift (coupledChemicalConcentration p
      (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀)
```

The key observation is that the cutoff theorem only needs source/resolver coefficient regularity on the positive band where `smoothRightCutoff (c/2) c` is nonzero.  That means it should not require global `FlooredSourceTimeData`, and it should not require any `t = 0` uniform bound.

## Source coefficient regularity input needed

The proof still needs the following positive-time facts, but they should be built directly, not via `FlooredSourceTimeData`:

1. `srcTimeCoeff p (conjugatePicardIter p u₀ 0) k` is `C²` on a positive-time neighborhood/window.
2. `resolverTimeCoeff = intervalNeumannResolverWeight p k * srcTimeCoeff`, using the already-existing theorems:

```text
IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_weight_smul
IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_smul
IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_iteratedFDeriv_eq
```

3. The three time-order envelopes for the cutoff coefficient have summable bounded-weight majorants.  This is the same bounded-weight mechanism already used by `PhysicalResolverJointC2Data`; it is not the Duhamel/eigen-cube route.

## Does it need `DuhamelSourceTimeC2Coeff`?

No, not for this cutoff version.

The file `IntervalResolverLevel0SpectralC2Coeff.lean` contains the variation-of-constants / `ResolverHasSpectralAgreementC2Coeff` route, but that is a different lane.  It has major unresolved obligations around `DuhamelSourceTimeC2Coeff`, coefficient derivatives, and spectral reconstruction.  The direct cutoff route should avoid that file and use the bounded-weight joint series route instead.

## Final answer

* `heatResolverJointContDiffAt_two` is committed.
* It currently has no local `sorry`, but it is only a wrapper around `heatSemigroup_level0_resolverJointC2Data`, which still has two local summability `sorry`s and depends on the six-field `heatSemigroup_flooredSourceTimeData` producer.
* Therefore the committed theorem is **not** the clean direct Option B proof.
* A true direct cutoff proof can bypass `FlooredSourceTimeData` entirely, provided you add local positive-time resolver/source coefficient regularity and bounded-weight summability lemmas for the cutoff coefficients.
* The best implementation path is to reuse `boundedWeightJointSeries_contDiff_two` with `cutoffResolverCoeff`, then transfer by eventual equality using `smoothRightCutoff_eventually_eq_one` and `coupledChemical_lift_eq_series`.
