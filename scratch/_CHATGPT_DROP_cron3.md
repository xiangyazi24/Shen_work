# Q1096 (cron3): Is `IteratePicardJointC2Data` trivial for heat Level0?

## Verdict

No — not as currently typed.

`IteratePicardJointC2Data` is **not** merely “`u` has joint `C²` plus a summable majorant.” It is a stronger, coefficient-level package that *implies* joint `C²` via `iterate_lift_jointContDiffAt_two`. It requires:

1. exact cosine-series reconstruction of the lifted iterate slice;
2. a chosen coefficient family `c k t` that is globally `ContDiff ℝ 2` in `t`;
3. global-in-time coefficient derivative bounds `Bt i k`;
4. summability of the bounded-weight joint majorants built from those `Bt`.

For heat Level0, a **positive-time/windowed analogue** is very natural and should be easy from the explicit heat coefficients and heat kernel exponential summability. But the current global structure is not trivially inhabited for `u = conjugatePicardIter p u₀ 0`.

The main reason: the natural heat coefficients

```lean
c k t = Real.exp (-t * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k
```

are smooth in `t`, but their global-in-time bounds fail as `t → -∞`, and the exact reconstruction is only available/true in the current infrastructure at positive time. The theorem `heatSemigroup_jointContDiffAt_two` gives only a local positive-time `ContDiffAt` result for the **summed series**; it does not produce the coefficient-level fields required by `IteratePicardJointC2Data`.

## The structure definition

From `ShenWork/PDE/IntervalIteratePicardJointC2.lean`:

```lean
structure IteratePicardJointC2Data
    (u : ℝ → intervalDomainPoint → ℝ) (c : ℕ → ℝ → ℝ) (Bt : ℕ → ℕ → ℝ) : Prop where
  /-- The iterate slice equals its cosine series on `[0,1]`. -/
  lift_eq_series : ∀ {t x : ℝ}, x ∈ Icc (0 : ℝ) 1 →
    intervalDomainLift (u t) x = ∑' k : ℕ, c k t * cosineMode k x
  /-- Each coefficient is `C²` in time (the honest iterate time-`C²` leg). -/
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (c k)
  /-- Three-time-order coefficient bounds. -/
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (c k) t‖ ≤ Bt i k
  /-- The bounded-weight VALUE joint majorant is summable (orders `0,1,2`). -/
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
```

It is then consumed by:

```lean
theorem iterate_lift_jointContDiffAt_two
    (H : IteratePicardJointC2Data u c Bt) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)
```

and by the slab version:

```lean
theorem iterate_hu_c2_slab
    (H : IteratePicardJointC2Data u c Bt) :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)
```

So the data structure is upstream of joint `C²`; it is not a consequence of the joint `C²` theorem.

## Natural heat Level0 choice of `c`

For heat Level0,

```lean
u := conjugatePicardIter p u₀ 0
```

and `conjugatePicardIter` is definitionally:

```lean
conjugatePicardIter p u₀ 0 =
  fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
```

The natural coefficient family is:

```lean
cHeat (u₀ : intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t * unitIntervalCosineEigenvalue k) *
    cosineCoeffs (intervalDomainLift u₀) k
```

This is also the `n = 0` branch of:

```lean
ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff p u₀ 0 t k
```

## Field-by-field status for heat Level0

### 1. `lift_eq_series`

**Positive-time fillable:** yes.

Existing theorem:

```lean
ShenWork.IntervalPicardIterateRepresentation.hagree_zero
```

Shape:

```lean
theorem hagree_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
```

For B-form Level0, `conjugatePicardIter p u₀ 0` is the same heat semigroup form, so the same spectral identity / subtype adapter route applies.

**But as currently typed:** not trivial. `IteratePicardJointC2Data.lift_eq_series` is quantified over all `t : ℝ`, not just `0 < t`. The existing `hagree_zero` requires `0 < σ`. At `t = 0`, exact pointwise reconstruction of an arbitrary continuous initial datum from its cosine series is not automatically available. At `t < 0`, the semigroup convention/definition is not the positive heat series. Thus this field is not globally trivial.

### 2. `coeff_contDiff`

**For the explicit heat coefficients:** yes, this part is trivial/smooth.

For

```lean
cHeat k t = Real.exp (-t * unitIntervalCosineEigenvalue k) * û₀ k
```

one should prove:

```lean
∀ k, ContDiff ℝ (2 : ℕ∞) (cHeat u₀ k)
```

by `fun_prop` / smoothness of `exp` and multiplication by constants.

**But:** this field alone is not enough, and the coefficient family must still be the one satisfying `lift_eq_series` for all `t`. If one instead chooses a zero/cutoff coefficient family to match the nonpositive-time semigroup convention, global `ContDiff` at `t = 0` becomes nontrivial and can fail for rough initial data.

### 3. `coeff_bound`

**Positive-window fillable:** yes.

For `t ≥ τ₀ > 0`, explicit derivatives have shape:

```lean
∂ₜ^i cHeat k t = (-λ_k)^i * Real.exp (-t * λ_k) * û₀ k
```

so a bound is available from:

```lean
|∂ₜ^i cHeat k t| ≤ λ_k^i * M₀ * Real.exp (-τ₀ * λ_k)
```

This is exactly the kind of bound used in `IntervalHeatSemigroupHighRegularity.lean`, where cutoff heat terms are bounded by an exponential majorant.

**But as currently typed:** not globally fillable with the natural heat coefficients. The field requires:

```lean
∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (c k) t‖ ≤ Bt i k
```

with no `0 < t` or window assumption. For `cHeat k t = exp(-tλ_k) û₀k`, this is unbounded as `t → -∞` for every `k > 0` with nonzero coefficient. Therefore no finite global `Bt i k` exists for the natural coefficients.

A smooth right cutoff can produce global bounds, and `IntervalHeatSemigroupHighRegularity.lean` does exactly that for local `ContDiffAt`; but then the cutoff coefficients only agree with the heat series near a chosen positive-time window, not globally for every `t`.

### 4. `value_summable`

**Positive-window/cutoff fillable:** yes.

The relevant existing heat summability lemmas include:

```lean
ShenWork.Paper2.HeatSemigroupHighRegularity.heatSemigroup_eigenvalueSq_summable
ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable
ShenWork.Paper2.HeatSemigroupJointRegularity.cutoffHeatSeries_contDiff_two
```

For a positive lower time `τ₀`, the exponential majorant gives summability of all required value weights for orders `≤ 2`. This is routine heat-kernel/eigenvalue exponential decay.

**But as currently typed:** it depends on the global `Bt` from `coeff_bound`; since global `Bt` is not available for the natural heat coefficients, `value_summable` is not an immediate global field.

## Relation to `heatSemigroup_jointContDiffAt_two`

The theorem:

```lean
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

has shape:

```lean
theorem heatSemigroup_jointContDiffAt_two
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) (s₀, x₀)
```

This is a **local positive-time conclusion** for the summed heat series. It is proved by constructing a smooth cutoff series and showing it agrees near `(s₀,x₀)`. It does not expose a global coefficient family `c`, a global majorant `Bt`, or the exact `lift_eq_series` field for all `t`.

Therefore, `heatSemigroup_jointContDiffAt_two` cannot directly fill `IteratePicardJointC2Data`. The construction direction is the opposite:

```text
coefficient family + coefficient bounds + summable majorant + series agreement
  → IteratePicardJointC2Data
  → iterate_lift_jointContDiffAt_two
  → hu_c2 slab
```

`heatSemigroup_jointContDiffAt_two` is closer to the output `hu_c2`, not the input data.

## What would make heat Level0 easy?

A positive-time/windowed variant would be straightforward:

```lean
structure IteratePicardJointC2DataOn
    (u : ℝ → intervalDomainPoint → ℝ) (c : ℕ → ℝ → ℝ)
    (Bt : ℕ → ℕ → ℝ) (lo hi : ℝ) : Prop where
  lift_eq_series : ∀ {t x : ℝ}, t ∈ Icc lo hi → x ∈ Icc (0 : ℝ) 1 →
    intervalDomainLift (u t) x = ∑' k, c k t * cosineMode k x
  coeff_contDiffOn : ∀ k, ContDiffOn ℝ 2 (c k) (Icc lo hi)
  coeff_bound : ∀ i k t, i ≤ 2 → t ∈ Icc lo hi →
    ‖iteratedFDeriv ℝ i (c k) t‖ ≤ Bt i k
  value_summable : ∀ m, (m : ℕ∞) ≤ 2 → Summable (boundedWeightJointMajorant Bt m)
```

For heat Level0 on a window `0 < lo ≤ hi`, choose:

```lean
c k t = Real.exp (-t * unitIntervalCosineEigenvalue k) *
  cosineCoeffs (intervalDomainLift u₀) k

Bt i k = unitIntervalCosineEigenvalue k ^ i * M₀ *
  Real.exp (-lo * unitIntervalCosineEigenvalue k)
```

Then:

* `lift_eq_series` comes from `hagree_zero` / heat spectral identity;
* `coeff_contDiffOn` is smoothness of exponential;
* `coeff_bound` is the explicit derivative formula plus `t ≥ lo`;
* `value_summable` follows from `eigenvalue_pow_mul_exp_summable` / `heatSemigroup_eigenvalueSq_summable`.

This would be the honest positive-time form needed by 3G for Level0.

## Answer to the prompt questions

### Is `IteratePicardJointC2Data` essentially just “u has joint C² + summable majorant”?

No. It is a coefficient-level sufficient condition for joint `C²`. It includes exact series reconstruction and per-mode time-regularity/bounds. The theorem `iterate_lift_jointContDiffAt_two` derives joint `C²` from it.

### Can it be constructed from `heatSemigroup_jointContDiffAt_two` + heat kernel eigenvalue summability?

Not directly. `heatSemigroup_jointContDiffAt_two` is too weak and points in the wrong direction: it is a local `ContDiffAt` theorem for the already-summed series. To build `IteratePicardJointC2Data`, use the explicit heat coefficients and spectral identity directly. Heat kernel eigenvalue summability is useful for `coeff_bound`/`value_summable`, but the current global structure still blocks the natural construction outside positive time.

### Field-by-field heat Level0 status

| Field | Heat Level0 status |
|---|---|
| `lift_eq_series` | Fillable on `t > 0` by `hagree_zero` / heat spectral identity; not global as typed. |
| `coeff_contDiff` | Trivial for explicit heat coefficients `exp(-tλ) û₀`; problematic if coefficients are altered to match nonpositive-time semigroup convention. |
| `coeff_bound` | Fillable on positive windows using exponential decay; false globally for explicit heat coefficients because of `t → -∞`. |
| `value_summable` | Fillable on positive windows via `eigenvalue_pow_mul_exp_summable`; not an immediate global field without global `Bt`. |

## Bottom line

For 3G, heat Level0 does not get `IteratePicardJointC2Data` “for free” from `heatSemigroup_jointContDiffAt_two`. The right fix is either:

1. add a positive-windowed/positive-time version of `IteratePicardJointC2Data` and build it from explicit heat coefficients; or
2. use a smooth-cutoff coefficient family local to the target positive slab, mirroring `heatSemigroup_jointContDiffAt_two`.

The current global `IteratePicardJointC2Data` is stronger than needed for positive-time 3G and is not trivially constructible for heat Level0.
