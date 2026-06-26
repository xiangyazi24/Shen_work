# Q885 (cron2) — summability of `boundedWeightJointMajorant` / `boundedWeightJointGradMajorant` for `wₖ * builtEs`

Static repo inspection only; I did **not** run Lean.

## Short answer

The repo has **no turnkey theorem** of the exact form:

```lean
∀ m ≤ 2, Summable (boundedWeightJointMajorant
  (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)

∀ m ≤ 2, Summable (boundedWeightJointGradMajorant
  (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)
```

Searches for:

```text
boundedWeightJointMajorant summable
boundedWeightJointMajorant.*summable
boundedWeightJointGradMajorant summable
concreteRestartValueMajorant_summable
Majorant_summable
```

found useful related lemmas, but not this exact `builtEs` summability bridge.

Also, there is an important correction: **quadratic decay of `builtEs` is enough
for the value majorants, but not enough for the gradient majorants at order 2**.

Your estimate

```text
w_k * Es i k ≲ 1/k⁴
```

is correct for the coefficient part when `Es i k ≲ 1/(kπ)²` and
`w_k ≈ 1/(kπ)²`.  But `boundedWeightJointGradMajorant` includes an extra
spatial-gradient weight.  At order `m = 2`, the worst term is:

```lean
|kπ| * λ_k * Bt 0 k
```

so with `Bt 0 k ≈ 1/k⁴`, this behaves like `k³/k⁴ = 1/k`, which is **not
summable**.

Therefore:

* `value_summable` should be fillable from the existing `builtEs` quadratic decay
  plus `λ_k * w_k ≤ 1`.
* `grad_summable` needs **stronger source-side decay** than the current
  `builtEs`/`laplBound` gives, or it must remain an additional hypothesis / be
  proved from a stronger heat-specific source package.

## What exists in the repo

### 1. The definitions of the majorants

File:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

Value majorant:

```lean
def boundedWeightJointMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

Gradient majorant:

```lean
def boundedWeightJointGradMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * gradCosWeight (k - i) n
```

These files provide the generic `contDiff_tsum` assemblers, but the summability
fields are hypotheses, not automatically discharged from a pointwise decay lemma.

### 2. `physicalSourceTimeC2_of_floored` expects the two summability facts

File:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

The theorem consumes `hval` and `hgrad`:

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

So the repo design explicitly leaves both summability proofs outside
`FlooredSourceTimeData`; `FlooredSourceTimeData` supplies the envelope, and the
caller supplies the summability of the weighted majorants.

### 3. `builtEs` has exactly zeroth mode + quadratic IBP decay

Same file:

```lean
def builtEs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (i k : ℕ) : ℝ :=
  if hi : i ≤ 2 then
    (if k = 0 then Classical.choose (H.zerothBound i hi)
     else Classical.choose (H.laplBound i hi) / ((k:ℝ) * Real.pi) ^ 2)
  else 0
```

So for `k ≠ 0`, `builtEs H i k` is literally `M_i / (kπ)^2`.

### 4. Resolver-weight facts exist

File:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

Useful facts:

```lean
theorem eigenvalue_mul_resolverWeight_le_one (p : CM2Params) (n : ℕ) :
    unitIntervalNeumannSpectrum.eigenvalue n * intervalNeumannResolverWeight p n ≤ 1
```

and:

```lean
theorem resolverWeight_le_inv_mu (p : CM2Params) (n : ℕ) :
    intervalNeumannResolverWeight p n ≤ 1 / p.μ
```

These are exactly useful for the value-side proof.

### 5. Restart-specific summability exists, but it is not the same theorem

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

The exact searched lemmas exist:

```lean
theorem concreteRestartValueMajorant_summable
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (concreteRestartValueMajorant a₀ src offset s hτ k)
```

and:

```lean
theorem concreteRestartGradMajorant_summable
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (concreteRestartGradMajorant a₀ src offset s hτ k)
```

But these are for the restart/Duhamel spectral lane.  Their proof is:

```lean
(restartCoeffCoreMajorant_summable ...).mul_left _
```

where `restartCoeffCoreMajorant` is a much stronger custom majorant that already
contains the exact weighted terms needed for both value and gradient cutoff
series.  It is not expressed in terms of `builtEs H`.

So these lemmas are a **pattern**, not a direct solution for the HeatRegularity
`builtEs` sorries.

## Why value summability should work from quadratic `builtEs`

For `Bt i k = w_k * Es i k`, the value majorant is:

```lean
boundedWeightJointMajorant Bt m k
  = ∑ i ≤ m, choose(m,i) * (w_k * Es i k) * valueCosWeight (m-i) k
```

For `m ≤ 2`, `valueCosWeight (m-i) k` is one of:

```lean
1, |kπ|, λ_k
```

and it is bounded by a constant times `1 + λ_k`; for `k ≥ 1`, essentially by
`λ_k`.  Since the repo has:

```lean
λ_k * w_k ≤ 1
```

we get:

```text
(w_k * Es_i(k)) * valueCosWeight ≤ const * Es_i(k)
```

and `Es_i(k) ≲ 1/(kπ)^2`, which is summable.

The proof shape should be:

```lean
have hBt_nonneg : ∀ i k, 0 ≤ intervalNeumannResolverWeight p k * builtEs H i k := ...

-- For each fixed m ≤ 2, finite sum over i in range (m+1).
apply Summable.sum
intro i hi
-- show Summable of each component
-- split k = 0 and k ≥ 1
-- use λ_k * w_k ≤ 1 for valueCosWeight 2,
-- frequency ≤ λ for valueCosWeight 1,
-- and finite k=0 separately.
```

You will likely need a small helper for the p-series tail:

```lean
Summable (fun k : ℕ => if k = 0 then D else M / ((k : ℝ) * Real.pi)^2)
```

or a comparison against `fun k => C / (max 1 (k : ℝ))^2`.

## Why gradient summability does **not** follow from quadratic `builtEs`

The repo already has the exact order-2 gradient expansion in
`IntervalIterateGradMajorant.lean`:

```lean
theorem gradMajorant_two_eq (Bt : ℕ → ℕ → ℝ) (k : ℕ) :
    boundedWeightJointGradMajorant Bt 2 k
      = |(k : ℝ) * Real.pi| * unitIntervalCosineEigenvalue k * Bt 0 k
        + 2 * (unitIntervalCosineEigenvalue k * Bt 1 k)
        + |(k : ℝ) * Real.pi| * Bt 2 k
```

Substitute:

```lean
Bt i k = w_k * Es i k
Es i k ≈ 1 / (kπ)^2 = 1 / λ_k
w_k ≈ 1 / λ_k
```

Then the first gradient term behaves as:

```text
|kπ| * λ_k * (w_k * Es 0 k)
≈ |kπ| * λ_k * (1/λ_k^2)
= |kπ| / λ_k
≈ 1/k
```

which is **not summable**.

So the comment in `IntervalHeatSemigroupHighRegularity.lean` saying:

```lean
-- Same with an extra eigenvalue factor absorbed by (kπ)⁻² decay.
```

is too optimistic for `grad_summable` at order `m = 2`: the gradient majorant has
`|kπ| * λ_k`, not merely `λ_k`.

## What is needed for `grad_summable`

One of these needs to happen:

### Option A — strengthen `FlooredSourceTimeData` / `builtEs`

Add a stronger envelope field, for example source-side `(kπ)^(-4)` decay (or
slightly stronger than `(kπ)^(-3)`) for at least the `i = 0` slice, and compatible
weighted bounds for `i = 1,2`.

If `Es_i(k) ≲ 1/(kπ)^4`, then:

```text
w_k * Es_i(k) ≲ 1/k^6
|kπ| * λ_k * (w_k * Es_0(k)) ≲ k^3 / k^6 = 1/k^3
```

which is summable.

For a heat semigroup base iterate, this is mathematically plausible on positive
windows, because heat smoothing gives more than C² regularity.  But the current
`builtEs` only encodes the C²/IBP `(kπ)^(-2)` bound.

### Option B — keep `hgrad` as an additional heat-specific summability hypothesis

This is exactly what `physicalSourceTimeC2_of_floored` currently allows: `hgrad`
is supplied separately.  That is the least invasive route if you do not want to
change `FlooredSourceTimeData`.

### Option C — use a restart-style stronger core majorant

The restart lane solves this by proving a strong `restartCoeffCoreMajorant` that
simultaneously dominates all value/gradient weighted components and then proves:

```lean
concreteRestartValueMajorant_summable
concreteRestartGradMajorant_summable
```

For HeatRegularity, an analogous heat-specific core majorant could be introduced,
for example:

```lean
heatSourceCoreMajorant H k
```

which includes the needed `|kπ| * λ_k * w_k * builtEs H 0 k`-style terms directly.
But with only quadratic `builtEs`, that core majorant will still fail to be
summable unless it uses stronger heat smoothing than `builtEs` records.

## Concrete recommendation for the two HeatRegularity sorries

### Fill the value sorry separately

Make a helper like:

```lean
theorem builtEs_weighted_valueMajorant_summable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) :
    ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m) := by
  intro m hm
  -- finite-sum expansion in i
  -- split k=0 / k≥1
  -- use `eigenvalue_mul_resolverWeight_le_one`
  -- use `builtEs` + `H.laplBound`
  -- compare to p-series 1/k²
  sorry
```

This one should be valid with the current `builtEs`.

### Do not try to fill the gradient sorry from current `builtEs`

Instead, either leave it as a named residual or change the data to expose stronger
heat-specific decay:

```lean
theorem heatBuiltEs_weighted_gradMajorant_summable
    ... :
    ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * heatStrongEs i k) m)
```

where `heatStrongEs` has enough decay, e.g. `(kπ)^(-4)` for the relevant slices or
an exponential heat envelope on a positive window/cutoff lane.

## Bottom line

* **Existing exact lemmas for the `builtEs` majorants:** not found.
* **Existing analogous restart lemmas:** yes,
  `concreteRestartValueMajorant_summable` and `concreteRestartGradMajorant_summable`.
* **Value HeatRegularity sorry:** should be fillable from current `builtEs` +
  `λ_k * w_k ≤ 1` + p-series comparison.
* **Gradient HeatRegularity sorry:** current quadratic `builtEs` is insufficient;
  the order-2 gradient majorant contains `|kπ| * λ_k * Bt 0 k`, yielding a harmonic
  tail under only `Es ≲ (kπ)^(-2)`.

So the correct next move is not simply “reuse restart summability”; it is:

1. prove the value summability helper from current `builtEs`, and
2. strengthen/replace the gradient source envelope or keep `hgrad` as a separate
   heat-specific residual.
