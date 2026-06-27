# Q1330 (cron2) — `PhysicalSourceTimeC2` global obstruction vs direct cutoff path

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Short answer

Yes: for the heat-level resolver joint-`C²` goal, bypass `IntervalPhysicalSourceTimeC2Concrete.lean` and focus on the direct cutoff path in

```lean
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

The `src_contDiff` obligation in `PhysicalSourceTimeC2` asks for an all-`ℝ` statement:

```lean
src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
```

but the honest heat-level data available in the positive-time version is only:

```lean
srcTimeCoeff_contDiffAt ... {t : ℝ} (ht : 0 < t) :
  ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) t
```

That is exactly what the direct cutoff route consumes: it proves positive-time `ContDiffAt`, multiplies by a smooth cutoff that vanishes below `c/2`, and then obtains global `ContDiff` for the **cutoff coefficient**, not for the raw coefficient.

So the direct cutoff path is the right critical path.  Do not try to close global `src_contDiff` for the raw physical source unless you first retype the structure to a positive-time/windowed/cutoff version.

## What I found in the files

### 1. `PhysicalSourceTimeC2` is all-time

In `ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean`, the structure has:

```lean
structure PhysicalSourceTimeC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  /-- Each source coefficient is `C²` in time (`u^γ` smooth under the floor). -/
  src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
  /-- Three-time-order source coefficient bounds. -/
  src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
```

So both `src_contDiff` and `src_bound` quantify over all real time.

### 2. The positive-time physical producer cannot honestly fill this as stated

In the positive-time version of `IntervalPhysicalSourceTimeC2Concrete.lean`, the data structure is explicitly positive-time:

```lean
structure FlooredSourceTimeData ... where
  d0 : ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, ...
  d1 : ∀ τ : ℝ, 0 < τ → ∃ δ : ℝ, ...
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, 0 < t →
    ContDiffOn ℝ 2 ...
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, 0 < t → ...
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t → ...
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 < t → ...
```

and the proved regularity theorem is positive-time only:

```lean
theorem srcTimeCoeff_contDiffAt
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) t
```

The later producer still tries to build:

```lean
PhysicalSourceTimeC2 p u (builtEs H)
```

which requires global `ContDiff ℝ 2` and global bounds.  That is a type mismatch.  The comment saying “extension to global ContDiff on ℝ follows from the structure of srcTimeCoeff” is not a proof; for heat smoothing it is the false step.

### 3. The direct cutoff path intentionally avoids this global raw-coefficient demand

`ShenWork/Paper2/IntervalHeatResolverJointC2.lean` is explicitly the direct route.  It has:

```lean
theorem heatLevel0_srcTimeCoeff_contDiffAt_two
    ... {t : ℝ} (_ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  sorry
```

Then it proves resolver coefficient positive-time `ContDiffAt` by the constant elliptic weight:

```lean
theorem heatLevel0_resolverTimeCoeff_contDiffAt_two
    ... {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
  have hsrc := heatLevel0_srcTimeCoeff_contDiffAt_two ... ht k
  ...
  exact contDiffAt_const.mul hsrc
```

Then it multiplies by a cutoff:

```lean
theorem cutoffResolverCoeff_contDiff_two
    ... {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (fun t =>
      smoothRightCutoff (c / 2) c t *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t)
```

For `t ≥ c/2`, this uses positive-time `ContDiffAt`; for `t < c/2`, the cutoff is identically zero nearby.  This is exactly the correct way to globalize a positive-time regularity fact.

The main consumer is:

```lean
theorem heatResolver_jointContDiffAt_two
    ... {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1) q.2)
      (s₀, x₀)
```

This path does not need `PhysicalSourceTimeC2`; it imports `IntervalPhysicalResolverDataConcrete` for the coefficient definitions and the constant-weight identity, not for the all-time physical producer.

## Recommendation

### Critical path

Focus on these two direct-cutoff obligations:

```lean
heatLevel0_srcTimeCoeff_contDiffAt_two
cutoffResolverMajorant_summable / cutoffResolverTerm_iteratedFDeriv_bound
```

This closes the direct route:

```lean
heatLevel0_srcTimeCoeff_contDiffAt_two
  → heatLevel0_resolverTimeCoeff_contDiffAt_two
  → cutoffResolverCoeff_contDiff_two
  → cutoffResolverTerm_contDiff_two
  → cutoffResolverSeries_contDiff_two
  → heatResolver_jointContDiffAt_two
```

Do **not** spend effort trying to prove global `ContDiff ℝ 2` of the raw `srcTimeCoeff` unless the structure is retyped.

### If the physical route is still desired

Retype it.  Good options:

```lean
structure PhysicalSourceTimeC2On
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) (c T : ℝ) : Prop where
  src_contDiffAt : ∀ k t, t ∈ Ioo c T →
    ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) t
  src_bound : ∀ i k t, i ≤ 2 → t ∈ Ioo c T →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
  ...
```

or a cutoff version:

```lean
structure PhysicalSourceTimeC2Cutoff
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) (c : ℝ) : Prop where
  cutoff_src_contDiff : ∀ k,
    ContDiff ℝ (2 : ℕ∞)
      (fun t => smoothRightCutoff (c / 2) c t * srcTimeCoeff p u k t)
  cutoff_src_bound : ...
```

The direct cutoff file is already implementing the second idea at resolver-coefficient level.

## About `src_bound` for `t ≤ 0`

There are two different conventions to separate.

### A. Concrete current `intervalFullSemigroupOperator` value at `t = 0`

The repo has `ShenWork/PDE/IntervalSemigroupAtZero.lean`, which proves:

```lean
theorem intervalFullSemigroupOperator_zero (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator 0 f x = 0
```

The file also explains the reason: with the concrete `heatKernel` definition,

```lean
heatKernel 0 x = 0
```

so the full Neumann kernel at `t = 0` is identically zero.  Thus, for the current concrete `conjugatePicardIter` level 0 definition,

```lean
conjugatePicardIter p u₀ 0 t x =
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
```

at `t = 0` the slice is zero, not `u₀`.

For `t < 0`, the same degeneracy should be true by the same `Real.sqrt_eq_zero_of_nonpos` mechanism, but I did not find a named theorem in the inspected files.  A useful atom would be:

```lean
lemma intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  -- prove heatKernel t _ = 0 from sqrt_eq_zero_of_nonpos (4πt ≤ 0),
  -- then intervalNeumannFullKernel t x y = 0, then simp the integral.
  sorry
```

If you prove this atom, then for level 0 and `t ≤ 0`:

```lean
srcSlice p (conjugatePicardIter p u₀ 0) t x = 0
```

because `p.γ > 0` and `0 ^ p.γ = 0`.  Then all source coefficients are zero.  For `src_bound`, the nonpositive-time branch is trivial:

```lean
0 ≤ builtEs H i k
```

provided you have a small lemma proving `builtEs_nonneg` from the nonnegative `Classical.choose_spec` bounds.

However, this does **not** fix global `src_contDiff` at `0`: the positive-time right limit is generally the source of `u₀`, while the value at zero is zero in the concrete kernel convention.  So global `ContDiff` still fails generically.

### B. Intended mathematical convention `S(0)u₀ = u₀`, or a clamped `t ≤ 0` extension

If you intentionally redefine/extend the heat level so that for `t ≤ 0`

```lean
u t = u₀
```

then the source slice for `t ≤ 0` is indeed

```lean
fun x => p.ν * intervalDomainLift u₀ x ^ p.γ
```

In that convention, the bound for `i = 0` needs **new initial-source spatial data**.  It is not supplied by the positive-time `FlooredSourceTimeData` fields.

The right assumptions would be something like:

```lean
def initialSource (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => p.ν * intervalDomainLift u₀ x ^ p.γ

hinitC2 : ContDiffOn ℝ 2 (initialSource p u₀) (Icc (0 : ℝ) 1)
hinitNeu :
  Tendsto (deriv (initialSource p u₀)) (𝓝[Ioi 0] 0) (𝓝 0) ∧
  Tendsto (deriv (initialSource p u₀)) (𝓝[Iio 1] 1) (𝓝 0) ∧
  deriv (initialSource p u₀) 0 = 0 ∧
  deriv (initialSource p u₀) 1 = 0
hinit0 : |cosineCoeffs (initialSource p u₀) 0| ≤ Dinit
hinitLap : ∀ k, 1 ≤ k →
  |cosineCoeffs (initialSource p u₀) k| ≤ Minit / ((k : ℝ) * Real.pi) ^ 2
```

Then enlarge the envelope:

```lean
Dnew i = max Dpositive_i Dinit   -- for i = 0
Mnew i = max Mpositive_i Minit   -- for i = 0
```

For `i = 1,2`, if the extension is constant for `t < 0`, the derivatives are zero on `t < 0`; but at `t = 0` the derivatives generally do not exist or do not match the right derivatives unless you impose compatibility/flatness.  So an all-`ℝ` `src_bound` based on `iteratedFDeriv` at `t = 0` is still not honest unless the extension is smoothed/cut off.

## What bound works at `t ≤ 0`?

If using the current concrete kernel convention and proving `S(t)=0` for `t≤0`, the bound is:

```lean
‖iteratedFDeriv ℝ i (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ = 0
```

away from the transition, so use:

```lean
0 ≤ builtEs H i k
```

But this still leaves differentiability at `0` broken.

If using the intended `S(0)u₀ = u₀` / constant-left extension, the `i=0` bound is a separate initial-source coefficient bound.  There is no bound from the existing positive-time `H` alone.  You need to add an initial regularity/bound hypothesis or choose a cutoff/windowed structure.

## Final verdict

The direct cutoff path is the right path for the heat-level resolver joint-`C²` theorem.  `PhysicalSourceTimeC2` is over-strong for this use case because it asks for global raw coefficient `ContDiff ℝ 2` and global raw coefficient bounds.  The direct path only needs positive-time `ContDiffAt` and uses the cutoff to globalize safely.

So:

```text
Bypass PhysicalSourceTimeC2 for the heat-level direct resolver proof.
Focus on IntervalHeatResolverJointC2.lean.
Retype PhysicalSourceTimeC2 only if a later consumer genuinely needs it.
```
