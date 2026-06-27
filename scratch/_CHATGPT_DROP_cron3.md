# Q1162 (cron3): `FlooredSourceTimeData` heat-semigroup source-slice fields

## Verdict

The four fields are **not already proved as fields of**
`HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData`.
The target file itself still has the four `sorry`s for

* `sliceC2`,
* `sliceNeumann`,
* `zerothBound`, and
* `laplBound`.

There is useful infrastructure, but it is only partial:

1. `IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_eigenvalue_summable` already proves the **base power-source weak-H²/Neumann package** for a slice
   `x ↦ ν * intervalDomainLift w x ^ γ`, assuming a cosine representation with
   eigenvalue-weighted summability and strict positivity on `[0,1]`.
2. `IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound` and `IntervalWeakH2Neumann_cosineCoeff_quadratic_decay` already prove the **IBP coefficient decay** once such a weak-H² Neumann package is available.
3. `IntervalFlooredSourceTimeDataIterate.IterateSourceTimeData` already has the exact abstract shape needed to wire space-C², Neumann, zeroth, and `(kπ)⁻²` data into `FlooredSourceTimeData`, and `flooredSourceTimeData_of_iterate` performs that wiring.
4. `IntervalPicardLevel0SourceTimeC1On` is mostly about the **logistic** level-0 source and time-C¹ on a positive window. It supplies useful heat-profile representation / continuity lemmas, but it does not prove these four `ν * (S(t)u₀)^γ` fields.

The larger issue is that `FlooredSourceTimeData` asks for **uniform-in-all-positive-time** constants for `zerothBound` and `laplBound`. With only `Continuous u₀` and bounded heat coefficients, those uniform global bounds are not available for the heat time-derivative slices near `t = 0`. So the current target is at least missing hypotheses, and for `i = 1,2` it is likely false as stated unless the data are strengthened or the fields are retyped/windowed.

## What the target file currently asks for

In `ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean`, the fields are:

```lean
structure FlooredSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) : Prop where
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, 0 < t →
    ContDiffOn ℝ 2 ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0:ℝ) 1)
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, 0 < t →
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0 = 0 ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 1 = 0
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ), 0 < t → ∀ (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
```

In `ShenWork/Paper2/IntervalHeatSemigroupFlooredSourceTimeData.lean`, the theorem
`heatSemigroup_flooredSourceTimeData` still fills all four of these with `sorry`.
The comments there correctly describe the intended analytic route, but no proof is
present.

## Existing infrastructure, field by field

### `sliceC2`

**Partially covered for `i = 0`, not as the target field.**

For the base source slice

```lean
srcSlice p (conjugatePicardIter p u₀ 0) t x
  = p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ^ p.γ
```

`IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_eigenvalue_summable`
constructs an `IntervalWeakH2Neumann` package from:

* eigenvalue-weighted summability of the heat coefficients,
* agreement of the heat slice with its cosine series on `[0,1]`, and
* strict positivity on `[0,1]`.

Inside that proof it builds:

```lean
have hC2u : ContDiffOn ℝ 2 u (Set.Icc (0 : ℝ) 1) := ...
have hC2g : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1) := ...
```

where `g x = ν * u x ^ γ`. But the returned structure does **not expose** `hC2g`; it only stores the weak second-derivative data. Therefore it cannot directly fill `FlooredSourceTimeData.sliceC2`. You either need to duplicate that small construction at the call site or refactor it into a helper that returns both the `ContDiffOn`/Neumann fields and the `IntervalWeakH2Neumann` certificate.

For `i = 1,2`, I did not find an existing theorem proving `ContDiffOn ℝ 2` of

```lean
srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t
srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t
```

The proof has to be added. It is straightforward analytically for each fixed `t > 0`: write the three smooth cosine representatives

```lean
U0 t x = ∑' n, exp (-t * λ_n)       * a_n * cos(nπx)
U1 t x = ∑' n, (-λ_n) * exp (-t*λ_n) * a_n * cos(nπx)
U2 t x = ∑' n, λ_n^2 * exp (-t*λ_n)  * a_n * cos(nπx)
```

and show they are spatial `C²`. Then use product/rpow closure under a positive lower bound for `U0 t`.

Relevant already-proved tools:

```lean
ShenWork.Paper2.HeatSemigroupHighRegularity.heatSemigroup_contDiff_four
ShenWork.Paper2.HeatSemigroupHighRegularity.heatSemigroup_eigenvalueSq_summable
ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable
ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_coeff_exp_summable
ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
```

`heatSemigroup_contDiff_four` handles `U0`.  For `U1`, use `cosineCoeffSeries_contDiff_two` with coefficients `-λ_n * exp(-tλ_n) * a_n`; the needed summability is essentially `∑ λ_n^2 exp(-tλ_n)|a_n|`, already available from `heatSemigroup_eigenvalueSq_summable`. For `U2`, use coefficient sequence `λ_n^2 * exp(-tλ_n) * a_n`; `C²` needs an extra `λ_n`, so use an `m = 3` exponential majorant from `eigenvalue_pow_mul_exp_summable`/`eigenvalue_pow_mul_coeff_exp_summable`.

### `sliceNeumann`

**Partially covered for `i = 0`, not exposed as the target field.**

Again, `intervalWeakH2Neumann_of_eigenvalue_summable` proves the endpoint data internally:

```lean
hbc0 : deriv g 0 = 0
hbc1 : deriv g 1 = 0
htend0 : Tendsto (deriv g) (nhdsWithin 0 (Ioi 0)) (nhds 0)
htend1 : Tendsto (deriv g) (nhdsWithin 1 (Iio 1)) (nhds 0)
```

but only the final weak-H² package is returned. It cannot directly fill `sliceNeumann` without refactoring or duplicating the proof.

For `i = 1,2`, no complete field proof appears elsewhere. The proof should be by cosine-series endpoint symmetry:

* `U0' 0 = U0' 1 = 0`,
* `U1' 0 = U1' 1 = 0`,
* `U2' 0 = U2' 1 = 0`,

because all three are cosine series with enough weighted summability to justify differentiating. Then differentiate the formulas

```lean
S0 = p.ν * U0 ^ p.γ
S1 = p.ν * p.γ * U0 ^ (p.γ - 1) * U1
S2 = p.ν * p.γ * (p.γ - 1) * U0 ^ (p.γ - 2) * U1^2
   + p.ν * p.γ * U0 ^ (p.γ - 1) * U2
```

At the endpoints every product-rule term contains one of `U0'`, `U1'`, or `U2'`, so the derivative vanishes. The one-sided tendsto clauses then follow from continuity of those derivatives, once `S0`, `S1`, `S2` are `C¹` in space near the endpoints.

### `zerothBound`

**Not proved for these fields.**

There are generic coefficient-bound tools, for example `cosineCoeffs_abs_le_of_continuous_bounded` in `IntervalMildPicardRegularity`, and there are logistic-specific/windowed estimates in `IntervalPicardLevel0SourceTimeC1On`, e.g.

```lean
heatSourceCoeff_abs_le
```

But these are for the logistic source/time derivative, not for the power source family
`ν * (S(t)u₀)^γ`, `srcSlice1`, `srcSlice2`.

For `i = 0`, a uniform positive-time zeroth bound is plausible from the heat semigroup sup bound and continuity/boundedness of `u₀` on the compact interval:

```text
|cosineCoeffs (ν * U0(t)^γ) 0| ≤ sup_x |ν * U0(t,x)^γ| ≤ ν * B^γ
```

provided `U0` is bounded uniformly in `t > 0`.

For `i = 1,2`, a global bound for all `t > 0` is not supplied and is generally not available from merely continuous initial data. `U1 = ∂ₜS(t)u₀ = ΔS(t)u₀` and `U2 = ∂ₜ²S(t)u₀ = Δ²S(t)u₀` can blow up as `t ↓ 0`. Thus `zerothBound` for the time-derivative source slices is much stronger than positive-time smoothing.

### `laplBound`

**The IBP decay theorem exists; the uniform hypotheses do not.**

Two usable engines exist:

```lean
ShenWork.IntervalSourceDecayQuantitative
  .intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound

ShenWork.IntervalCosineCoeffDecay.cosineCoeff_decay
```

The first consumes an `IntervalWeakH2Neumann f` plus an explicit bound on
`∫₀¹ |f''|`. The second consumes the exposed `ContDiffOn`/Neumann data plus a uniform bound on the Laplacian coefficient. Both prove the desired `(kπ)⁻²` shape.

For each fixed `t > 0`, the proof for `i = 0` is already almost wired:

```lean
import ShenWork.PDE.IntervalMildSourceDecayHelper
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.Paper2.IntervalPicardIterateRepresentation
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

-- Schematic: this is the per-time base-slice H² package already available.
theorem basePowerSource_H2_at_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (ht : 0 < t)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
      (fun x : ℝ =>
        p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ^ p.γ) := by
  have hsum : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        |Real.exp (-t * unitIntervalCosineEigenvalue n) * heatCoeff u₀ n|) :=
    ShenWork.IntervalSemigroupNeumann.heatCoeff_eigenvalue_summable
      ht hu₀_bound
  have hagree : Set.EqOn
      (intervalDomainLift (conjugatePicardIter p u₀ 0 t))
      (fun x => ∑' n : ℕ,
        (Real.exp (-t * unitIntervalCosineEigenvalue n) * heatCoeff u₀ n) *
          cosineMode n x)
      (Icc (0 : ℝ) 1) :=
    ShenWork.IntervalPicardIterateRepresentation.hagree_zero
      p u₀ ht hu₀_cont hu₀_bound
  exact
    ShenWork.PDE.IntervalMildSourceDecayHelper
      .intervalWeakH2Neumann_of_eigenvalue_summable
        p.hν p.hγ hsum hagree hpos

-- Given a uniform L¹ bound on the second derivative over a positive window,
-- the existing quantitative theorem gives the `(kπ)^-2` bound.
theorem basePowerSource_lapl_decay_from_uniform_H2_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ B c T : ℝ}
    (hc : 0 < c)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ t ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hB : ∀ t ∈ Icc c T,
      let H := basePowerSource_H2_at_time
        (p := p) (u₀ := u₀) (M₀ := M₀) (t := t)
        (lt_of_lt_of_le hc ‹t ∈ Icc c T›.1) hu₀_cont hu₀_bound
        (hpos t ‹t ∈ Icc c T›)
      (∫ x in (0 : ℝ)..1, |H.secondDeriv x|) ≤ B) :
    ∀ t ∈ Icc c T, ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs
        (fun x : ℝ =>
          p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ^ p.γ) k|
        ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2 := by
  intro t ht k hk
  let H := basePowerSource_H2_at_time
    (p := p) (u₀ := u₀) (M₀ := M₀) (t := t)
    (lt_of_lt_of_le hc ht.1) hu₀_cont hu₀_bound (hpos t ht)
  exact
    ShenWork.IntervalSourceDecayQuantitative
      .intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
        H (hB t ht) k hk

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

That sketch shows the correct wiring, but it also shows the missing hypothesis: a **uniform** bound `B`. The existing weak-H² constructor only gives a bound depending on `t` through `H.second_abs_integral_bound`; it does not produce a single `B` valid for all `t > 0`.

## The key obstruction: global `∀ t > 0` bounds near `t = 0`

The comments in `IntervalHeatSemigroupFlooredSourceTimeData.lean` say “for `t > 0`, heat smoothing makes it work.” That is true for pointwise-in-time `sliceC2` and `sliceNeumann`, but it is not enough for the global `zerothBound` and `laplBound` fields.

The current theorem has assumptions only:

```lean
(_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
(_hu₀_cont : Continuous u₀)
```

No positive lower time cutoff `c > 0`, no high-regularity initial datum, and no global uniform bounds on `ΔS(t)u₀` or `Δ²S(t)u₀` as `t ↓ 0` are supplied.

For the time-derivative slices:

```lean
srcSlice1 = ν * γ * U0^(γ-1) * U1
srcSlice2 = ν * γ * (γ-1) * U0^(γ-2) * U1^2
          + ν * γ * U0^(γ-1) * U2
```

where

```lean
U1 = ΔS(t)u₀
U2 = Δ²S(t)u₀
```

there is no reason for the zeroth cosine coefficients or the quadratic-decay constants to stay bounded uniformly as `t ↓ 0` for merely continuous `u₀`. This is exactly why other level-0 source infrastructure works on positive closed windows `[c,T]`, for example `IntervalPicardLevel0SourceTimeC1On.level0Source_timeC1On`, which takes `hc : 0 < c` and additional window bounds as hypotheses.

So the likely correct design is one of:

1. Retype these `zerothBound` / `laplBound` fields to be **local/windowed in time**, e.g. for each `τ > 0` produce a slab or for each `[c,T]` with `c > 0` produce constants.
2. Strengthen initial data enough to control `U1`, `U2`, and the relevant source-slice second derivatives uniformly all the way to `t = 0`.
3. For the existing `FlooredSourceTimeData`, add explicit global hypotheses giving exactly the required zeroth and Laplacian envelopes for all three slices.

## Positivity caveat

The question says “`S(t)u₀ > 0` on `[0,1]` from `_hu₀_nonneg + heat nonneg preservation.” Nonnegativity preservation only gives `0 ≤ S(t)u₀`. For real `γ`, the rpow chain rule needs nonzero/strict positivity of the base wherever powers like `γ - 1` or `γ - 2` occur.

To get strict positivity from the existing heat machinery, use one of:

* a closed-domain positive floor (`PaperPositiveInitialDatum.floor`) and a heat-floor theorem;
* the strict propagator theorem `IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_pos`, which requires the initial datum to be nonnegative on `[0,1]` and positive somewhere;
* an explicit positive-window assumption `∀ t ∈ Icc c T, ∀ x ∈ Icc 0 1, 0 < ...`.

The current `heatSemigroup_flooredSourceTimeData` signature does not contain any of these positivity hypotheses, so the rpow-based proofs are not available from its listed assumptions alone.

## Recommended implementation path

### Step 1: introduce a reusable exposed package

Refactor the currently hidden proof content of
`intervalWeakH2Neumann_of_eigenvalue_summable` into an exposed package:

```lean
import ShenWork.PDE.IntervalMildSourceDecayHelper

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.PDE.IntervalMildSourceDecayHelper

structure C2NeumannData (f : ℝ → ℝ) : Prop where
  c2 : ContDiffOn ℝ 2 f (Icc (0 : ℝ) 1)
  tend0 : Tendsto (deriv f) (𝓝[Ioi 0] 0) (𝓝 0)
  tend1 : Tendsto (deriv f) (𝓝[Iio 1] 1) (𝓝 0)
  bc0 : deriv f 0 = 0
  bc1 : deriv f 1 = 0

noncomputable def C2NeumannData.toWeakH2 {f : ℝ → ℝ}
    (H : C2NeumannData f) : IntervalWeakH2Neumann f :=
  intervalWeakH2Neumann_of_contDiffOn H.c2 H.tend0 H.tend1 H.bc0 H.bc1

-- New helper to add: same proof as `intervalWeakH2Neumann_of_eigenvalue_summable`,
-- but return `C2NeumannData` before converting it to `IntervalWeakH2Neumann`.
noncomputable def powerSource_C2NeumannData_of_eigenvalue_summable
    {ν γ : ℝ} (hν : 0 < ν) (hγ : 0 < γ)
    {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    C2NeumannData (fun x : ℝ => ν * intervalDomainLift w x ^ γ) := by
  -- Copy the `hC2g`, `htend0`, `htend1`, `hbc0`, `hbc1` construction
  -- currently inside `intervalWeakH2Neumann_of_eigenvalue_summable`.
  sorry

end ShenWork.PDE.IntervalMildSourceDecayHelper
```

Then `sliceC2` and `sliceNeumann` for `i = 0` become direct projections from this package, and `laplBound` can use `toWeakH2` plus `IntervalSourceDecayQuantitative`.

### Step 2: add heat-side C² representatives for `U1` and `U2`

Add lemmas proving that the `heatDu` and `heatD2u` representatives are spatially `C²` at `t > 0`, and prove their endpoint derivatives vanish.

Schematic shape:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On
import ShenWork.Paper2.IntervalConjugatePicard

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

-- Schematic helper for the first time derivative representative.
theorem heatDu_contDiffOn_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (ht : 0 < t)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) :
    ContDiffOn ℝ 2 (heatDu u₀ t) (Icc (0 : ℝ) 1) := by
  -- unfold `heatDu`; the positive branch is
  -- `unitIntervalCosineHeatLaplacianValue t (heatCoeff u₀)`.
  -- Rewrite it as a cosine coefficient series with coefficients
  -- `fun n => -unitIntervalCosineEigenvalue n * Real.exp (-t*λ_n) * heatCoeff u₀ n`.
  -- Apply `cosineCoeffSeries_contDiff_two`; the needed summability is controlled by
  -- `heatSemigroup_eigenvalueSq_summable`.
  sorry

-- Schematic helper for the second time derivative representative.
theorem heatD2u_contDiffOn_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (ht : 0 < t)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) :
    ContDiffOn ℝ 2 (heatD2u u₀ t) (Icc (0 : ℝ) 1) := by
  -- unfold `heatD2u`; positive branch is already a cosine series with coefficients
  -- `λ_n^2 * exp(-tλ_n) * heatCoeff u₀ n`.
  -- For `C²`, prove `∑ λ_n * |λ_n^2 exp(-tλ_n) a_n|`, dominated by
  -- `M₀ * ∑ λ_n^3 exp(-tλ_n)`.
  -- Use `HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable 3 ht`.
  sorry

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
```

### Step 3: prove `S0/S1/S2` C² and Neumann from `U0/U1/U2`

With `U0`, `U1`, `U2` C² and endpoint derivative-zero, prove the source slices:

```lean
S0 t x = p.ν * U0 t x ^ p.γ
S1 t x = p.ν * p.γ * U0 t x ^ (p.γ - 1) * U1 t x
S2 t x = p.ν * p.γ * (p.γ - 1) * U0 t x ^ (p.γ - 2) * (U1 t x)^2
       + p.ν * p.γ * U0 t x ^ (p.γ - 1) * U2 t x
```

are `ContDiffOn ℝ 2` and Neumann. This is mostly `ContDiffOn.mul`, `ContDiffOn.add`, and `ContDiffOn.rpow_const_of_ne`, plus endpoint product-rule calculations.

### Step 4: fix the uniform-bound story

Do **not** try to prove the existing global `zerothBound`/`laplBound` for `i = 1,2` from only positive-time smoothing. Either:

* retype `FlooredSourceTimeData` to carry local/windowed bounds, or
* add explicit assumptions / stronger initial data.

On a positive window `[c,T]`, the proof is standard:

1. build joint continuous representatives for each source slice and for its second spatial derivative on `[c,T] × [0,1]`;
2. use compactness to get a uniform sup bound;
3. use `cosineCoeffs_abs_le_of_continuous_bounded` for `zerothBound`;
4. use `IntervalCosineCoeffDecay.exists_laplacianCoeff_bound` + `cosineCoeff_decay`, or the weak-H² quantitative theorem, for `laplBound`.

The compact-bound pattern is:

```lean
import Mathlib.Topology.Order.Compact

open Set Topology

noncomputable section

example {c T : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Icc c T ×ˢ Icc (0 : ℝ) 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |F (t, x)| ≤ B := by
  have hK : IsCompact (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro t ht x hx
  have hmem : (t, x) ∈ Icc c T ×ˢ Icc (0 : ℝ) 1 := by
    exact mem_prod.mpr ⟨ht, hx⟩
  have hnorm : ‖F (t, x)‖ ≤ C := hC (t, x) hmem
  have habs : |F (t, x)| ≤ C := by
    simpa [Real.norm_eq_abs] using hnorm
  exact habs.trans (le_max_left C 0)
```

## Bottom line

* `IntervalSourceDecayQuantitative.lean` gives the **decay engine**, not the four fields.
* `IntervalPicardLevel0SourceTimeC1On.lean` gives useful heat/logistic windowed machinery, not the power-source `FlooredSourceTimeData` fields.
* `IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_eigenvalue_summable` covers the **base slice’s weak-H²/Neumann proof internally**, but it does not expose `sliceC2`/`sliceNeumann`, and it does not handle the first/second time-derivative slices.
* `IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate` is the right wiring abstraction, but its current input structure is all-time and still requires the same fields upstream.
* The current global `∀ t > 0` `zerothBound`/`laplBound` requirements are too strong for merely continuous heat initial data, especially for `srcSlice1` and `srcSlice2` near `t = 0`. A positive-window/local retype or stronger initial-data hypotheses are needed.
