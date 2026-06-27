# Q1231 (cron2) — heat cosine time-derivative signatures

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Exact `unitIntervalCosineHeatValue_hasDerivAt_time` signature

The theorem exists in:

```text
ShenWork/PDE/IntervalDuhamelClosedC2.lean
```

Namespace:

```lean
ShenWork.IntervalDuhamelClosedC2
```

Exact declaration:

```lean
/-- **Time derivative of the cosine heat value = the second-spatial-derivative
series.**  For `r > 0` and bounded coefficients, `r ↦ unitIntervalCosineHeatValue r
a x` is differentiable with derivative `unitIntervalCosineHeatSecondValue r a x`
(`= ∑'ₙ −λₙ e^{−rλₙ}cos(nπx)·aₙ`).  This is the **time half** of the spectral heat
equation; termwise `∂ᵣ(e^{−rλₙ}cos) = −λₙ e^{−rλₙ}cos`, dominated near `r` by the
`4/((r/2)²π²)·n⁻²` majorant. -/
theorem unitIntervalCosineHeatValue_hasDerivAt_time
    {r x : ℝ} (hr : 0 < r) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatValue s a x)
      (unitIntervalCosineHeatSecondValue r a x) r
```

To use it with fully qualified names:

```lean
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
```

The import is:

```lean
import ShenWork.PDE.IntervalDuhamelClosedC2
```

## Related per-mode time derivative theorem

The per-mode theorem used inside `unitIntervalCosineHeatValue_hasDerivAt_time` is in:

```text
ShenWork/Paper2/IntervalDomainJointTimeRegularity.lean
```

Namespace:

```lean
ShenWork.Paper2
```

Signature:

```lean
theorem unitIntervalCosineHeatPointWeight_hasDerivAt_time
    (x : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight s x n)
      (-(unitIntervalCosineEigenvalue n) *
        unitIntervalCosineHeatPointWeight t x n) t
```

Qualified name:

```lean
ShenWork.Paper2.unitIntervalCosineHeatPointWeight_hasDerivAt_time
```

There is also a closely related theorem in `RegularityBootstrap.lean` that uses the Laplacian point-weight name:

```lean
theorem unitIntervalCosineHeatPointWeight_hasTimeDerivAt_laplacian
    (t x : ℝ) (n : ℕ) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatPointWeight τ x n)
      (unitIntervalCosineHeatLaplacianPointWeight t x n) t
```

and its coefficient-multiplied version:

```lean
theorem unitIntervalCosineHeatTerm_hasTimeDerivAt_laplacian
    (t x : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    HasDerivAt
      (fun τ : ℝ => unitIntervalCosineHeatPointWeight τ x n * a n)
      (unitIntervalCosineHeatLaplacianPointWeight t x n * a n) t
```

Qualified names:

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatPointWeight_hasTimeDerivAt_laplacian
ShenWork.RegularityBootstrap.unitIntervalCosineHeatTerm_hasTimeDerivAt_laplacian
```

## HasDerivAt of tsum cosine series in the time direction

### 1. Bounded-coefficient heat-value theorem

This is the requested theorem above:

```lean
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
```

It assumes only bounded coefficients:

```lean
(hM : ∀ n, |a n| ≤ M)
```

and proves:

```lean
HasDerivAt (fun s => unitIntervalCosineHeatValue s a x)
  (unitIntervalCosineHeatSecondValue r a x) r
```

### 2. Generic summable-bound theorem

In `ShenWork/PDE/RegularityBootstrap.lean`:

```lean
theorem unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound
    {t x t₀ : ℝ} {a : ℕ → ℝ} {u : ℕ → ℝ}
    (hu : Summable u)
    (hbound :
      ∀ n τ,
        ‖unitIntervalCosineHeatLaplacianPointWeight τ x n * a n‖ ≤ u n)
    (h₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t₀ x n * a n) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
      (unitIntervalCosineHeatLaplacianValue t a x) t
```

Qualified name:

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound
```

### 3. Local positive-time summable-bound theorem

Also in `RegularityBootstrap.lean`:

```lean
theorem unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound_on_Ioi
    {r t x t₀ : ℝ} {a : ℕ → ℝ} {u : ℕ → ℝ}
    (hrt : r < t) (hr₀ : r < t₀)
    (hu : Summable u)
    (hbound :
      ∀ n τ, τ ∈ Set.Ioi r →
        ‖unitIntervalCosineHeatLaplacianPointWeight τ x n * a n‖ ≤ u n)
    (h₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t₀ x n * a n) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
      (unitIntervalCosineHeatLaplacianValue t a x) t
```

Qualified name:

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_summable_bound_on_Ioi
```

### 4. Positive-time L² coefficient theorem

Also in `RegularityBootstrap.lean`:

```lean
theorem unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
    {t x : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n => (a n) ^ 2) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
      (unitIntervalCosineHeatLaplacianValue t a x) t
```

Qualified name:

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
```

There is a bundled theorem too:

```lean
theorem unitIntervalCosineHeatValue_c1_time_c2_space_of_l2
    {t x : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n => (a n) ^ 2) :
    HasDerivAt (fun τ : ℝ => unitIntervalCosineHeatValue τ a x)
        (unitIntervalCosineHeatLaplacianValue t a x) t ∧
      HasDerivAt
        (fun z : ℝ =>
          deriv (fun y : ℝ => unitIntervalCosineHeatValue t a y) z)
        (unitIntervalCosineHeatLaplacianValue t a x) x
```

### 5. Generic time derivative of a coefficient cosine series

In `ShenWork/PDE/IntervalChemDivMixedReprWitness.lean`:

```lean
theorem cosineSeries_timeDeriv_hasDerivAt
    {c : ℕ → ℝ → ℝ} {Bt1 : ℕ → ℝ} (x : ℝ)
    (hc : ∀ k, Differentiable ℝ (c k))
    (hb : ∀ k r, ‖deriv (c k) r‖ ≤ Bt1 k)
    (hsum : Summable Bt1)
    {r : ℝ} (hval : Summable (fun k => c k r * cosineMode k x)) :
    HasDerivAt (fun s => ∑' k : ℕ, c k s * cosineMode k x)
      (∑' k : ℕ, deriv (c k) r * cosineMode k x) r
```

Qualified name:

```lean
ShenWork.IntervalChemDivMixedReprWitness.cosineSeries_timeDeriv_hasDerivAt
```

This is not heat-specific; it is the generic `∑ c_k(t) cos(kπx)` time derivative theorem with a summable derivative majorant.

### 6. Reversed-time Duhamel integrand theorem

In `IntervalDuhamelClosedC2.lean`:

```lean
theorem unitIntervalCosineHeatPointWeight_sub_hasDerivAt
    (t x : ℝ) (n : ℕ) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n)
      (-(unitIntervalCosineHeatSecondPointWeight (t - s₀) x n)) s₀
```

```lean
theorem unitIntervalCosineHeatTerm_sub_hasDerivAt
    (t x : ℝ) (n : ℕ) {a adot : ℝ → ℕ → ℝ} {s₀ : ℝ}
    (hda : HasDerivAt (fun s : ℝ => a s n) (adot s₀ n) s₀) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatPointWeight (t - s) x n * a s n)
      (-(unitIntervalCosineHeatSecondPointWeight (t - s₀) x n) * a s₀ n
        + unitIntervalCosineHeatPointWeight (t - s₀) x n * adot s₀ n) s₀
```

and the assembled theorem:

```lean
theorem duhamelIntegrand_hasDerivAt
    {t x : ℝ} {a adot : ℝ → ℕ → ℝ} {M Mdot : ℝ}
    (hbound : ∀ s n, |a s n| ≤ M) (hbound' : ∀ s n, |adot s n| ≤ Mdot)
    (hda : ∀ s n, HasDerivAt (fun σ : ℝ => a σ n) (adot s n) s)
    {s₀ : ℝ} (hs₀lt : s₀ < t) :
    HasDerivAt (fun s : ℝ => unitIntervalCosineHeatValue (t - s) (a s) x)
      (-(unitIntervalCosineHeatSecondValue (t - s₀) (a s₀) x)
        + unitIntervalCosineHeatValue (t - s₀) (adot s₀) x) s₀
```

Qualified names:

```lean
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatPointWeight_sub_hasDerivAt
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatTerm_sub_hasDerivAt
ShenWork.IntervalDuhamelClosedC2.duhamelIntegrand_hasDerivAt
```

## Practical recommendation

For a plain heat value with bounded initial cosine coefficients, use:

```lean
ShenWork.IntervalDuhamelClosedC2.unitIntervalCosineHeatValue_hasDerivAt_time
```

For heat value with only `ℓ²` coefficients, use:

```lean
ShenWork.RegularityBootstrap.unitIntervalCosineHeatValue_hasTimeDerivAt_of_l2
```

For a moving coefficient family `∑ c k t * cosineMode k x`, use:

```lean
ShenWork.IntervalChemDivMixedReprWitness.cosineSeries_timeDeriv_hasDerivAt
```

For Duhamel reversed time `s ↦ S(t-s)(a s)`, use:

```lean
ShenWork.IntervalDuhamelClosedC2.duhamelIntegrand_hasDerivAt
```
