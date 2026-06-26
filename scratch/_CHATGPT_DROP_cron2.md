# Q876 (cron2) — existing `FlooredSourceTimeData` constructions?

Static repo inspection only; I did **not** run Lean.

## Short answer

The repo has **one real constructor** of `FlooredSourceTimeData`:

```lean
ShenWork.IntervalFlooredSourceTimeDataIterate.flooredSourceTimeData_of_iterate
```

but it is **not** an instantiated witness for a specific named trajectory such as
`picardIter`, `conjugatePicardIter`, a heat semigroup level, or a mild solution.
It is a generic/residual constructor:

```lean
theorem flooredSourceTimeData_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u) :
    FlooredSourceTimeData p u (srcSlice1 p u du) (srcSlice2 p u du d2u)
```

So the answer to “does the repo already have an actual `FlooredSourceTimeData`
witness for a concrete trajectory?” is: **not that I found**.

It has the **right abstraction layer** (`IterateSourceTimeData`) and the bridge
from that abstraction to `FlooredSourceTimeData`, but the hard trajectory-specific
input `IterateSourceTimeData p u du d2u` is still a residual/hypothesis elsewhere.

## Search results inspected

Searches performed:

```text
FlooredSourceTimeData
flooredSourceTimeData_of
flooredSourceTimeData_of_iterate
IterateSourceTimeData
FlooredSourceTimeData picardIter
FlooredSourceTimeData conjugatePicardIter
FlooredSourceTimeData heatSemigroup_level0_resolverJointC2Data
flooredSource
```

Relevant files returned:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
ShenWork.lean
```

Only the first three contain substantive construction/consumer logic.  The heat
file only mentions `FlooredSourceTimeData` as a future/blocked route for the heat
semigroup resolver data.

## Definitions and constructors found

### 1. `FlooredSourceTimeData` itself

File:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

Definition:

```lean
structure FlooredSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) : Prop where
  d0 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s) ∧
    ContinuousOn (Function.uncurry s₁) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  d1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (s₁ s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => s₁ r x) (s₂ s x) s) ∧
    ContinuousOn (Function.uncurry s₂) (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2 ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0:ℝ) 1)
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0 = 0 ∧
    deriv ((sliceFam (srcSlice p u) s₁ s₂ i) t) 1 = 0
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) 0| ≤ D
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) s₁ s₂ i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
```

This is the generic source-side bundle.  It is not tied to a concrete trajectory.

### 2. Generic bridge from `FlooredSourceTimeData` to `PhysicalSourceTimeC2`

Same file:

```lean
theorem physicalSourceTimeC2_of_floored
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2 p u (builtEs H)
```

This is also generic.  It consumes `FlooredSourceTimeData`; it does not produce one.

### 3. `IterateSourceTimeData`

File:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

This file defines the explicit first and second source time-derivative slices:

```lean
def srcSlice1 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * du t x

def srcSlice2 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du d2u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (p.γ - 1) * (intervalDomainLift (u t) x) ^ (p.γ - 1 - 1)
      * (du t x) ^ (2 : ℕ)
    + p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * d2u t x
```

Then it defines the residual/source-data structure:

```lean
structure IterateSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (du d2u : ℝ → ℝ → ℝ)
    : Prop where
  floor : ∀ t : ℝ, ∀ x ∈ Ioo (0:ℝ) 1, 0 < intervalDomainLift (u t) x
  time1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => intervalDomainLift (u r) x) (du s x) s) ∧
    ContinuousOn (Function.uncurry (srcSlice1 p u du))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  time2 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice1 p u du s) (Icc (0:ℝ) 1)) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => intervalDomainLift (u r) x) (du s x) s ∧
      HasDerivAt (fun r => du r x) (d2u s x) s) ∧
    ContinuousOn (Function.uncurry (srcSlice2 p u du d2u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2
      ((sliceFam (srcSlice p u) (srcSlice1 p u du) (srcSlice2 p u du d2u) i) t)
      (Icc (0:ℝ) 1)
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    Tendsto (deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
    Tendsto (deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t)) (𝓝[Iio 1] 1) (𝓝 0) ∧
    deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 0 = 0 ∧
    deriv ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 1 = 0
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
    |cosineCoeffs ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) 0| ≤ D
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
    |cosineCoeffs ((sliceFam (srcSlice p u) (srcSlice1 p u du)
      (srcSlice2 p u du d2u) i) t) k| ≤ M / ((k:ℝ) * Real.pi) ^ 2
```

Again, this is not a concrete witness.  It is a residual bundle: if you can prove
these fields for a trajectory `u`, then the constructor below produces
`FlooredSourceTimeData`.

### 4. The only `flooredSourceTimeData_of_*` theorem found

File:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

Signature:

```lean
theorem flooredSourceTimeData_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u) :
    FlooredSourceTimeData p u (srcSlice1 p u du) (srcSlice2 p u du d2u)
```

The proof is real and explicit: it fills `d0` using `hasDerivAt_srcSlice`, fills
`d1` using `hasDerivAt_srcSlice1`, and passes through `sliceC2`, `sliceNeumann`,
`zerothBound`, and `laplBound` from `H`.

So this is a genuine constructor, but only from the residual structure
`IterateSourceTimeData`.

### 5. End-to-end consumer from `IterateSourceTimeData`

Same file has:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_iterate
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    (H : IterateSourceTimeData p u du d2u)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k *
          builtEs (flooredSourceTimeData_of_iterate H) i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k *
          builtEs (flooredSourceTimeData_of_iterate H) i k) m))
    (other : ... ) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This confirms the intended pipeline:

```lean
IterateSourceTimeData
  → flooredSourceTimeData_of_iterate
  → physicalSourceTimeC2_of_floored
  → coupledChemDivFluxFactorJointC2Inputs_of_floor
```

But it still starts from the residual `IterateSourceTimeData`; it does not build
that residual for a named trajectory.

## What about a mild solution?

File:

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

This file is very explicit that a bare `GradientMildSolutionData` does **not** carry
the time-`C²`/space-`C²` regularity needed for `IterateSourceTimeData`.

It defines:

```lean
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  du : ℝ → ℝ → ℝ
  d2u : ℝ → ℝ → ℝ
  hiter : IterateSourceTimeData p u du d2u
  hval : ... builtEs (flooredSourceTimeData_of_iterate hiter) ...
  hgrad : ... builtEs (flooredSourceTimeData_of_iterate hiter) ...
  other : ...
  Cchem : ℝ
  ...
```

Then it proves:

```lean
noncomputable def coupledChemDivSource_timeC1On_of_gradientSolution
    (D : GradientMildSolutionData p u₀)
    (R : ChemDivSolutionRegularityResidual p D.u) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p D.u) 0 D.T
```

So the mild-solution path also does **not** construct `FlooredSourceTimeData` from
`GradientMildSolutionData` alone.  It requires the residual `R`, whose field
`hiter` already contains `IterateSourceTimeData`.

The file comments state the same design point: `GradientMildSolutionData` carries
only continuity/measurability/bounds/positivity, not the time-`C²` and space-`C²`
parabolic regularity demanded by `IterateSourceTimeData`.

## What about Picard / heat level?

I found no theorem of the form:

```lean
FlooredSourceTimeData p (picardIter p u₀ n) ...
FlooredSourceTimeData p (conjugatePicardIter p u₀ n) ...
FlooredSourceTimeData p (conjugatePicardIter p u₀ 0) ...
IterateSourceTimeData p (picardIter p u₀ n) ...
IterateSourceTimeData p (conjugatePicardIter p u₀ 0) ...
```

Searches for `FlooredSourceTimeData picardIter` and
`FlooredSourceTimeData conjugatePicardIter` only led to
`IntervalHeatSemigroupHighRegularity.lean`, where the heat-level resolver theorem
still has sorry'd fields and comments that building `FlooredSourceTimeData` for
the heat semigroup is a missing sub-piece.

The relevant heat theorem is:

```lean
theorem heatSemigroup_level0_resolverJointC2Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
  -- fields sorry'd
```

Its comments say the final form should go through `FlooredSourceTimeData` /
`physicalResolverJointC2Data_of_floor`, but this has not yet been implemented as a
concrete heat-level `FlooredSourceTimeData` witness.

## Bottom line

* **Exists:** `flooredSourceTimeData_of_iterate`.
* **Nature:** generic/residual constructor from `IterateSourceTimeData p u du d2u`.
* **Does not exist / not found:** an actual instantiated `FlooredSourceTimeData`
  witness for `picardIter`, `conjugatePicardIter`, the heat base iterate
  `conjugatePicardIter p u₀ 0`, or a `GradientMildSolutionData` solution.
* **Mild-solution consumer:** `IntervalChemDivWinDischarge.lean` explicitly packages
  the missing regularity as `ChemDivSolutionRegularityResidual`, whose `hiter` field
  is already an `IterateSourceTimeData`; it does not derive that field.

For cron2/Level0, this means the missing object is still a **heat-level / positive-window
instantiation of `IterateSourceTimeData` or directly of `FlooredSourceTimeData`**.
The repo has the bridge once that object exists, but not the object itself.
