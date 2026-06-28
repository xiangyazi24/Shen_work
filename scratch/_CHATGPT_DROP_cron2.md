# Q1565 (cron2) — gradient `C²`: value-`C³` shortcut vs separate gradient series

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

The shortcut is **mathematically viable but not the minimal route**.

You cannot get

```lean
heatResolver_grad_jointContDiffAt_two
```

from the existing value theorem

```lean
heatResolver_jointContDiffAt_two : ContDiffAt ℝ 2 value (s₀, x₀)
```

because `C²` of the value gives at most `C¹` for a first spatial derivative. To get `C²` of the gradient by differentiating the value function, you would need a **value `C³` theorem**:

```lean
ContDiffAt ℝ 3 value (s₀, x₀)
```

Then the map

```lean
q ↦ fderiv ℝ value q (0, 1)
```

is `ContDiffAt ℝ 2`, and on an interior spatial neighborhood it agrees with

```lean
q ↦ deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2.
```

So: **yes, value `C³` would imply gradient `C²`**, modulo the usual local equality between partial derivative and the single-variable spatial `deriv`.

But in the current file, `contDiff_tsum` only gives `C²` because every upstream component is explicitly order-2:

```lean
heatLevel0_srcTimeCoeff_contDiffAt_two
heatLevel0_resolverTimeCoeff_contDiffAt_two
cutoffResolverCoeff_contDiff_two
cutoffResolverTerm_contDiff_two
cutoffResolverMajorant_summable       -- only j ≤ 2
cutoffResolverTerm_iteratedFDeriv_bound -- only j ≤ 2
cutoffResolverSeries_contDiff_two
```

The fact that the heat semigroup is smooth at positive time does **not** by itself make the series proof `C∞`; `contDiff_tsum` requires summable uniform majorants for each derivative order you ask for. Existing infrastructure only asks for and only supplies order `≤ 2`.

## Recommendation

Do **not** use the value-`C³` shortcut as the main way to close the gradient sorry.

Use the separate gradient-series route. It is more targeted and already has generic infrastructure in

```lean
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

namely:

```lean
boundedWeightJointGradTerm
boundedWeightJointGradMajorant
boundedWeightJointGradTerm_iteratedFDeriv_le
boundedWeightJointGradSeries_contDiff_two
```

This route proves exactly the needed object:

```lean
ContDiff ℝ 2
  (fun q : ℝ × ℝ => ∑' n, c n q.1 * deriv (cosineMode n) q.2)
```

and therefore avoids proving a full value `C³` theorem.

## Why value `C³` is more expensive

The value series has terms

```text
c_k(t) · cos(kπx),
```

where

```text
c_k(t) = resolverTimeCoeff p u k t
       = (1 / (μ + λ_k)) · sourceCoeff_k(t).
```

A value `C³` `contDiff_tsum` would need:

1. per-mode `ContDiff ℝ 3` in `(t,x)`, hence `resolverTimeCoeff` `C³` in `t`;
2. a summable majorant for all joint derivatives of order `≤ 3`;
3. a new source time-coefficient theorem:

```lean
heatLevel0_srcTimeCoeff_contDiffAt_three
```

which would require a third time slice, morally

```lean
srcSlice3 p (conjugatePicardIter p u₀ 0) ...
```

and corresponding heat identities like `heatD3u`. I found only the existing C² chain using `srcSlice`, `srcSlice1`, `srcSlice2`, `heatDu`, and `heatD2u` in `IntervalHeatResolverJointC2.lean`.

The separate gradient-series route needs only time coefficient regularity up to order `2`, because the base spatial derivative is built into the spatial factor:

```text
c_k(t) · ∂ₓ cos(kπx).
```

Then a joint order-`≤2` theorem for this gradient series covers all derivatives needed by `heatResolver_grad_jointContDiffAt_two` without a third time derivative of `srcTimeCoeff`.

## Why the naive `C³` majorant can fail

If one tries to upgrade the old value majorant naively as

```text
w_k · (1 + λ_k)^j · sourceEnvelope_k
```

then for `j = 3`, with

```text
w_k = O(k^-2),
(1 + λ_k)^3 = O(k^6),
sourceEnvelope_k = O(k^-4)  -- from weak H⁴_N source IBP
```

the product is only

```text
O(k^-2) · O(k^6) · O(k^-4) = O(1),
```

which is not summable.

So value `C³` is viable only if you use a **sharper mixed-derivative majorant**, not the crude `(1+λ)^3` bound, or if you prove stronger source coefficient decay, for example H⁶-type decay. The sharper route must distinguish time and spatial derivatives:

```text
∂ₜ^a ∂ₓ^b [c_k(t) cos(kπx)],  a + b ≤ 3.
```

For the value `C³` majorant, the worst spatial factor for `a = 0, b = 3` is only

```text
|kπ|^3,
```

not `λ_k^3 = |kπ|^6`. With H⁴ source decay,

```text
|kπ|^3 · (μ + λ_k)^-1 · O(k^-4) = O(k^-3),
```

which is summable. But the mixed terms also require source time-derivative coefficient summability, for example roughly:

```text
|sourceCoeff_k| weighted by |kπ|,
|∂ₜ sourceCoeff_k| unweighted,
|∂ₜ² sourceCoeff_k| / |kπ|,
|∂ₜ³ sourceCoeff_k| / |kπ|².
```

That last line is exactly the extra C³ value burden. The gradient-series route avoids the `∂ₜ³ sourceCoeff_k` requirement.

## Concrete proof strategy for the gradient theorem

The target theorem is currently:

```lean
theorem heatResolver_grad_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (_hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift (coupledChemicalConcentration p
            (conjugatePicardIter p u₀ 0) q.1)) q.2)
        (s₀, x₀) := by
  sorry
```

There is a typo in the sketch above: the real file has the correct absolute-value hypothesis

```lean
|cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
```

The route should be:

### Step 1. Define the gradient cutoff term

Add, locally or in a helper file:

```lean
def cutoffResolverGradTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * deriv (cosineMode k) q.2)
```

This is the gradient analogue of

```lean
cutoffResolverTerm p u c k q
  = φ(q.1) * resolverTimeCoeff p u k q.1 * cosineMode k q.2.
```

### Step 2. Prove global `C²` of the gradient cutoff series

Use the generic physical gradient assembler:

```lean
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradSeries_contDiff_two
```

with

```lean
c n t := smoothRightCutoff (c / 2) c t *
  resolverTimeCoeff p (conjugatePicardIter p u₀ 0) n t
```

or equivalently absorb the cutoff into the coefficient family.

The needed time regularity remains order `2`:

```lean
∀ n, ContDiff ℝ 2 (fun t => φ(t) * resolverTimeCoeff p u n t)
```

which is already exactly `cutoffResolverCoeff_contDiff_two`.

The missing analytic part is a gradient majorant:

```lean
Bt i n ≥ ‖D_t^i (φ · resolverTimeCoeff_n)(t)‖,   i ≤ 2
```

and

```lean
Summable (boundedWeightJointGradMajorant Bt j),  j ≤ 2.
```

This is the real content, but it is smaller than proving a full value `C³` theorem.

### Step 3. Relate the gradient series to the spatial derivative

You need an eventually-equal bridge on the interior neighborhood:

```lean
{q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 (s₀, x₀)
```

On that neighborhood:

```text
intervalDomainLift (coupledChemicalConcentration p u q.1) q.2
  = ∑' k, resolverTimeCoeff p u k q.1 * cosineMode k q.2.
```

Then prove, by the gradient-series summability/interchange theorem, that

```text
deriv (fun x => intervalDomainLift (coupledChemicalConcentration p u q.1) x) q.2
  = ∑' k, resolverTimeCoeff p u k q.1 * deriv (cosineMode k) q.2.
```

For the cutoff version near `s₀ > c`, the cutoff is eventually `1`, so the raw gradient series and cutoff gradient series are eventually equal just like `resolverSeries_eventuallyEq_cutoff`.

### Step 4. Transfer `ContDiffAt`

Once the cutoff gradient series is globally `ContDiff ℝ 2`, take `.contDiffAt` at `(s₀, x₀)` and use `congr_of_eventuallyEq` to transfer to the actual target.

The final skeleton should look like:

```lean
have hGradCutoff : ContDiff ℝ 2 (fun q : ℝ × ℝ =>
    ∑' k : ℕ,
      cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  -- use boundedWeightJointGradSeries_contDiff_two
  sorry

have hGradCutoffAt := hGradCutoff.contDiffAt (x := (s₀, x₀))

have hEqRawToCutoff :
    (fun q : ℝ × ℝ => ∑' k : ℕ,
      resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1 *
        deriv (cosineMode k) q.2)
    =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ => ∑' k : ℕ,
      cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  -- same cutoff-eventually-one argument as `resolverSeries_eventuallyEq_cutoff`
  sorry

have hEqLiftDerivToRaw :
    (fun q : ℝ × ℝ =>
      deriv (intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1)) q.2)
    =ᶠ[𝓝 (s₀, x₀)]
    (fun q : ℝ × ℝ => ∑' k : ℕ,
      resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1 *
        deriv (cosineMode k) q.2) := by
  -- interior equality + derivative/tsum interchange for the resolver series
  sorry

exact hGradCutoffAt.congr_of_eventuallyEq
  (hEqLiftDerivToRaw.trans hEqRawToCutoff)
```

## If you still want the value-`C³` shortcut

The theorem you would need is:

```lean
theorem heatResolver_jointContDiffAt_three
    ... :
    ContDiffAt ℝ 3
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1) q.2)
      (s₀, x₀) := by
  -- must rerun cutoff + contDiff_tsum at order 3
  sorry
```

Then gradient `C²` follows conceptually from:

```lean
let F : ℝ × ℝ → ℝ := fun q =>
  intervalDomainLift (coupledChemicalConcentration p
    (conjugatePicardIter p u₀ 0) q.1) q.2

have hF3 : ContDiffAt ℝ 3 F (s₀, x₀) := ...

have hpartial : ContDiffAt ℝ 2
    (fun q => fderiv ℝ F q (0, 1)) (s₀, x₀) := by
  -- Mathlib API is usually via `ContDiffAt.fderiv` / `contDiffAt_fderiv`;
  -- after obtaining `ContDiffAt ℝ 2 (fun q => fderiv ℝ F q)`, apply it to
  -- the fixed vector `(0,1)` by continuous linear evaluation.
  sorry
```

Then prove local equality

```lean
(fun q => fderiv ℝ F q (0, 1))
  =ᶠ[𝓝 (s₀, x₀)]
(fun q => deriv (intervalDomainLift (coupledChemicalConcentration p
  (conjugatePicardIter p u₀ 0) q.1)) q.2)
```

using `x₀ ∈ (0,1)`.

This works, but it asks for a larger theorem than the gradient sorry needs.

## Final answer

* Existing value `C²` is not enough.
* Value `C³` would be enough in principle.
* Current `contDiff_tsum` only gives `C²` because the per-term regularity and summable majorant are only built for `j ≤ 2`.
* Upgrading to value `C³` is not automatic from heat smoothing; it requires a new order-3 source/resolver coefficient chain and a summable order-3 mixed-derivative majorant.
* The better closure path for `heatResolver_grad_jointContDiffAt_two` is the separate gradient-series `contDiff_tsum`, using the already-existing `boundedWeightJointGradSeries_contDiff_two` infrastructure, plus the local derivative/series equality on the interior.
