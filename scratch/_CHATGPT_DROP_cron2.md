# Q872 (cron2) — concrete `Bt` witness for heat-level `PhysicalResolverJointC2Data`

Static repo inspection only; I did **not** run Lean.

## Short answer

For the committed physical route, the final witness should still be

```lean
Bt i k = intervalNeumannResolverWeight p k * Es i k
```

where `Es` is the **source-side** time/coefficient envelope for

```lean
srcTimeCoeff p u k t
  = (intervalNeumannResolverSourceCoeff p (u t) k).re
  = cosineCoeffs (fun x => p.ν * intervalDomainLift (u t) x ^ p.γ) k
```

Do **not** bake a second resolver weight into `Es`.  If you use
`physicalResolverJointC2Data_of_floor`, `Es` is source-side only and the theorem
itself multiplies by `intervalNeumannResolverWeight p k`.

For now, yes: you can use a dummy explicit `Bt` while all four fields are `sorry`.
But do **not** literally write an opaque `fun _ _ => by sorry` witness.  Use an
explicit placeholder with the intended final shape, so later simplification and
summability goals are readable.

The best temporary placeholder is something like:

```lean
refine ⟨fun _i k => intervalNeumannResolverWeight p k, ?coeff_contDiff,
  ?coeff_bound, ?value_summable, ?grad_summable⟩
```

That is exactly the shape currently in `IntervalHeatSemigroupHighRegularity.lean`:

```lean
refine ⟨fun _i k => intervalNeumannResolverWeight p k,
  ?coeff_contDiff, ?coeff_bound, ?value_summable, ?grad_summable⟩
```

This is fine as a **pure placeholder** because all fields are still sorry'd.  It is
not the final mathematically honest envelope.

## Critical correction: global vs positive-window data

The current structure field is global in time:

```lean
coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
```

So a bound of the form

```lean
C_i * intervalNeumannResolverWeight p k * ... * exp (-c * λ_k)
```

is only honest for `t ≥ c` (or on `[c,T]`).  It cannot be used as a global
`PhysicalResolverJointC2Data` witness for the original heat semigroup unless the
theorem is localized or the coefficients are cut off in time.

This matters because the current heat theorem has no `c`/`T` in the data theorem:

```lean
theorem heatSemigroup_level0_resolverJointC2Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

but the proposed `exp(-c λ_k)` envelope depends on a positive left edge `c`.
For arbitrary continuous `u₀`, the original heat coefficients do not have a
uniform summable smoothing envelope for all `t : ℝ`.

So before trying to fill the fields honestly, choose one of these two routes:

1. **Local/cutoff route**: prove `PhysicalResolverJointC2Data` for a cutoff resolver
   coefficient family, then use eventual equality near `(s₀,x₀)`, exactly as
   `heatSemigroup_jointContDiffAt_two` does for the heat series.
2. **Window-local structure route**: introduce a localized variant of the source /
   resolver data whose `coeff_bound` only quantifies `t ∈ Icc c T`.

Do not try to prove the current global theorem with a `c`-dependent heat smoothing
majorant for the original, uncutoff heat semigroup.

## What concrete `Es` should look like

There are two reasonable future-fillable shapes.

### Option A: source-side polynomial decay from IBP / spatial smoothness

This is the cleaner Lean route if you package uniform spatial regularity of the
source time-derivative slices.

For each time order `i = 0,1,2`, prove a source-side theorem of the form:

```lean
∃ C_i, 0 ≤ C_i ∧ ∀ t ∈ Icc c T, ∀ k,
  ‖iteratedFDeriv ℝ i (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖
    ≤ C_i / (1 + unitIntervalNeumannSpectrum.eigenvalue k)^2
```

Then set:

```lean
Es i k = C_i / (1 + unitIntervalNeumannSpectrum.eigenvalue k)^2
Bt i k = intervalNeumannResolverWeight p k * Es i k
```

Why I prefer `(1+λ_k)^(-2)` over just `(1+λ_k)^(-1)`:

* For the **value** majorant, the worst spatial factor is `valueCosWeight 2 k = λ_k`,
  and the resolver weight gives `λ_k * w_k ≤ 1`, so even `Es ∈ ℓ¹` is enough.
* For the **gradient** majorant at order 2, the repo explicitly expands the worst
  term as

  ```lean
  |kπ| * λ_k * Bt 0 k + 2 * λ_k * Bt 1 k + |kπ| * Bt 2 k
  ```

  so after `Bt = w_k * Es`, the first term is roughly `|kπ| * Es 0 k`.
  If `Es 0 k ~ 1/λ_k`, this behaves like `1/k` and is not summable.  With
  `Es 0 k ~ 1/λ_k^2`, it behaves like `1/k^3`, which is summable.

So for the resolver **gradient** joint C² field, source-side C² decay
`(kπ)^(-2)` is not enough by itself; use source-side C⁴/IBP decay or an exponential
envelope.

A compact code skeleton for the final shape:

```lean
noncomputable def heatSourceEsShape
    (C : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun i k => C i / (1 + unitIntervalNeumannSpectrum.eigenvalue k)^2

noncomputable def heatResolverBtShape
    (p : CM2Params) (C : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun i k => intervalNeumannResolverWeight p k * heatSourceEsShape C i k
```

Then the intended final proof is:

```lean
obtain ⟨C, hCnonneg, Hsrc⟩ := heat_level0_physicalSourceTimeC2_data_on ...
let Es := heatSourceEsShape C
have H : PhysicalSourceTimeC2 p (conjugatePicardIter p u₀ 0) Es := by
  -- src_contDiff, src_bound, value_summable, grad_summable
  -- all source-side; no resolver algebra here.
  ...
exact ⟨fun i k => intervalNeumannResolverWeight p k * Es i k,
  physicalResolverJointC2Data_of_floor H⟩
```

Again: if the data is only valid on `[c,T]`, this exact global `PhysicalSourceTimeC2`
call is too strong.  Use a cutoff/globalized source coefficient or make a localized
version.

### Option B: exponential heat envelope

Your proposed form is also acceptable as a **window/cutoff** envelope:

```lean
Es i k = C_i * (1 + λ_k)^N * Real.exp (-(c / 2) * λ_k)
Bt i k = intervalNeumannResolverWeight p k * Es i k
```

Use a polynomial times exponential, not necessarily a negative power times
exponential.  The exponential already gives summability after all value/gradient
weights.  This shape matches the cutoff-heat-series style better: derivative
bounds usually produce polynomial factors `(1+λ_k)^N`, and the positive time
cutoff contributes `exp (-(c/2) λ_k)`.

For the nonlinear source `ν·S(t)u₀^γ`, proving a direct modewise exponential
coefficient bound for the composed source may be more painful than proving high
spatial regularity and doing repeated IBP.  So I would only choose this route if
you are already building a full analytic/cutoff source-series majorant.

## What not to do

Do **not** set:

```lean
Bt i k = C_i * w_k * (1 + λ_k)^(-1) * exp (-c * λ_k)
```

inside a proof that later calls:

```lean
physicalResolverJointC2Data_of_floor
```

unless you mean this as the **final `Bt`**, not `Es`.  The producer already applies
`w_k`, so source-side data should be:

```lean
Es i k = C_i * (1 + λ_k)^(-1) * exp (-c * λ_k)
```

and the resulting resolver data has:

```lean
Bt i k = w_k * Es i k
```

Also, `(1+λ)^(-1)` without the exponential is too weak for the gradient joint-C²
summability, as explained above.

## Practical recommendation

For the current sorry-driven implementation:

```lean
-- Fine as temporary witness while every field is sorry'd.
refine ⟨fun _i k => intervalNeumannResolverWeight p k,
  ?coeff_contDiff, ?coeff_bound, ?value_summable, ?grad_summable⟩
```

or, if you want a placeholder closer to the final summability proof:

```lean
refine ⟨fun _i k =>
    intervalNeumannResolverWeight p k /
      (1 + unitIntervalNeumannSpectrum.eigenvalue k)^2,
  ?coeff_contDiff, ?coeff_bound, ?value_summable, ?grad_summable⟩
```

The second one is better as a future proof shape, but it requires importing/opening
`unitIntervalNeumannSpectrum` and later adding constants `C_i`; without constants it
will not be the actual bound.

For the honest final proof, I would not handroll `PhysicalResolverJointC2Data`.
Instead, build a heat-level source-side package:

```lean
heatSemigroup_level0_physicalSourceTimeC2Data_on
```

or a cutoff/globalized equivalent, then finish with the existing theorem:

```lean
physicalResolverJointC2Data_of_floor
```

That keeps the resolver proof purely algebraic: the only hard work is proving the
source-side `Es` bounds and the two summability fields.

## Bottom line

* **Temporary:** yes, use an explicit dummy `Bt`; the current `fun _i k => w_k` is
  okay while all fields are sorry'd.
* **Final direct `Bt`:** `Bt = w_k * Es`, never more complicated than that at the
  resolver layer.
* **Best simple `Es`:** use a source-side C⁴/IBP envelope like
  `C_i / (1+λ_k)^2`, not merely `C_i / (1+λ_k)`, because `grad_summable` has the
  extra `|kπ|` factor.
* **If using `exp(-c λ_k)`:** localize/cut off first.  The current global
  `PhysicalResolverJointC2Data` field cannot honestly use a positive-window
  envelope for all `t : ℝ`.
