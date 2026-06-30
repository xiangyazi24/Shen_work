# Q2622 (cron1) — Lean 4 / Mathlib API for continuous parameter-dependent interval integrals

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Answer summary

The closest current Mathlib API is in:

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence
```

The relevant namespace is mostly `intervalIntegral`.

For a fixed interval integral with **global joint continuity**

```lean
hF : Continuous (Function.uncurry F)
```

the direct theorem is:

```lean
intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
```

It proves:

```lean
Continuous fun t => ∫ x in c..d, F t x ∂μ
```

and then `.continuousOn` gives the `ContinuousOn ... (Set.Icc a b)` goal.

For your stated hypothesis, **joint `ContinuousOn` only on a compact rectangle**, I do not see a one-shot theorem named `continuousOn_integral_of_compact` or equivalent. The usual Mathlib route is to prove `ContinuousOn` pointwise and apply:

```lean
intervalIntegral.continuousWithinAt_of_dominated_interval
```

at each parameter point `t₀ ∈ Set.Icc a b`. Compactness gives the domination bound, and joint `ContinuousOn` gives the section-continuity hypotheses.

So the short answer is:

* If you have `Continuous (Function.uncurry F)`, use `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.
* If you only have `ContinuousOn (Function.uncurry F)` on `Set.Icc a b ×ˢ [[c,d]]`, use `intervalIntegral.continuousWithinAt_of_dominated_interval` plus a compact bound from `IsCompact.bddAbove_image`.
* For raw dominated convergence of interval integrals, use `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`.

## Exact theorem names to try

### Parameter continuity wrappers for interval integrals

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

#check intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
#check intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
#check intervalIntegral.continuous_parametric_primitive_of_continuous
```

Meanings:

```lean
-- fixed endpoints, global joint continuity
#check intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
-- (hf : Continuous f.uncurry) (a₀ b₀ : ℝ) :
--   Continuous fun x => ∫ t in a₀..b₀, f x t ∂μ

-- variable upper endpoint, global joint continuity plus continuous endpoint map
#check intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
-- (hf : Continuous f.uncurry) (hs : Continuous s) :
--   Continuous fun x => ∫ t in a₀..s x, f x t ∂μ

-- primitive jointly continuous in parameter and endpoint
#check intervalIntegral.continuous_parametric_primitive_of_continuous
-- (hf : Continuous f.uncurry) :
--   Continuous fun p : X × ℝ => ∫ t in a₀..p.2, f p.1 t ∂μ
```

These convenient theorems live in the continuous-primitive section and have typeclass assumptions including:

```lean
[MeasureTheory.NullSingletonClass μ]
[MeasureTheory.IsLocallyFiniteMeasure μ]
```

For ordinary Lebesgue interval integrals, these are inferred for `μ := volume`.

### Dominated parameter-continuity theorems

These are usually the best fit for `ContinuousOn` on a compact rectangle.

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

#check intervalIntegral.continuousWithinAt_of_dominated_interval
#check intervalIntegral.continuousAt_of_dominated_interval
#check intervalIntegral.continuous_of_dominated_interval
```

The important one for a `ContinuousOn` target is:

```lean
#check intervalIntegral.continuousWithinAt_of_dominated_interval
-- {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ} {s : Set X}
-- (hF_meas : ∀ᶠ x in 𝓝[s] x₀,
--   AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
-- (h_bound : ∀ᶠ x in 𝓝[s] x₀,
--   ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
-- (bound_integrable : IntervalIntegrable bound μ a b)
-- (h_cont : ∀ᵐ t ∂μ,
--   t ∈ Ι a b → ContinuousWithinAt (fun x => F x t) s x₀) :
-- ContinuousWithinAt (fun x => ∫ t in a..b, F x t ∂μ) s x₀
```

For a goal

```lean
ContinuousOn (fun t => ∫ x in c..d, F t x ∂μ) (Set.Icc a b)
```

unfolding/using the definition of `ContinuousOn` reduces it to proving, for each `t₀ ∈ Set.Icc a b`,

```lean
ContinuousWithinAt (fun t => ∫ x in c..d, F t x ∂μ) (Set.Icc a b) t₀
```

which is exactly the conclusion of `intervalIntegral.continuousWithinAt_of_dominated_interval` with `s := Set.Icc a b`.

### Dominated convergence / limits of interval integrals

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

#check intervalIntegral.tendsto_integral_filter_of_dominated_convergence
#check TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
#check intervalIntegral.hasSum_integral_of_dominated_convergence
```

Meanings:

```lean
-- filter DCT for interval integrals
#check intervalIntegral.tendsto_integral_filter_of_dominated_convergence
-- Tendsto (fun n => ∫ x in a..b, F n x ∂μ) l
--   (𝓝 (∫ x in a..b, f x ∂μ))

-- uniform convergence on an interval, with eventually ContinuousOn integrands
#check TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
-- hF : ∀ᶠ i in l, ContinuousOn (F i) [[a,b]]
-- h_lim : TendstoUniformlyOn F f l [[a,b]]
-- conclusion: convergence of interval integrals

-- dominated convergence for series under interval integrals
#check intervalIntegral.hasSum_integral_of_dominated_convergence
```

### General Bochner integral DCT, not interval-specific

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory

#check MeasureTheory.tendsto_integral_of_dominated_convergence
#check MeasureTheory.tendsto_integral_filter_of_dominated_convergence
#check MeasureTheory.tendsto_integral_filter_of_norm_le_const
#check MeasureTheory.hasSum_integral_of_dominated_convergence
#check MeasureTheory.integral_tsum
#check MeasureTheory.integral_tsum_of_summable_integral_norm
```

Use these when the integral is not written as an interval integral `∫ x in a..b, ...`.

### Variable endpoint primitives

These are useful when the variable is an endpoint rather than a parameter in the integrand.

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

#check intervalIntegral.continuousOn_primitive
#check intervalIntegral.continuousOn_primitive_Icc
#check intervalIntegral.continuousOn_primitive_interval
#check intervalIntegral.continuousOn_primitive_interval_left
#check intervalIntegral.continuous_primitive
#check MeasureTheory.Integrable.continuous_primitive
```

These do **not** solve `t ↦ ∫ x in c..d, F t x` directly unless `t` is an endpoint. They are for maps like:

```lean
fun x => ∫ t in a..x, f t ∂μ
fun x => ∫ t in x..b, f t ∂μ
```

## Drop-in code: global joint continuity implies `ContinuousOn`

This is the clean path when your hypothesis is global `Continuous (Function.uncurry F)`.

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} [NullSingletonClass μ] [IsLocallyFiniteMeasure μ]
    {F : ℝ → ℝ → E} {a b c d : ℝ}
    (hF : Continuous (Function.uncurry F)) :
    ContinuousOn (fun t : ℝ => ∫ x in c..d, F t x ∂μ) (Set.Icc a b) :=
  (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := F) (μ := μ) hF c d).continuousOn
```

For Lebesgue measure, the same proof usually works with implicit `volume`:

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ → E} {a b c d : ℝ}
    (hF : Continuous (Function.uncurry F)) :
    ContinuousOn (fun t : ℝ => ∫ x in c..d, F t x) (Set.Icc a b) :=
  (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := F) (μ := volume) hF c d).continuousOn
```

For a variable upper endpoint:

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

example {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} [NullSingletonClass μ] [IsLocallyFiniteMeasure μ]
    {F : X → ℝ → E} {u : X → ℝ} {c : ℝ}
    (hF : Continuous (Function.uncurry F))
    (hu : Continuous u) :
    Continuous fun t : X => ∫ x in c..u t, F t x ∂μ :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := F) (μ := μ) (a₀ := c) hF hu
```

## Template: compact `ContinuousOn` route through domination

Suppose your real assumptions look like this informally:

```lean
S = Set.Icc a b
K = S ×ˢ [[c,d]]
hF : ContinuousOn (Function.uncurry F) K
```

Then there is not a one-line theorem of the form

```lean
continuousOn_integral_of_compact hF
```

that I found. Instead:

1. Prove a constant bound on the compact rectangle.
2. Use the bound as the `bound` argument in `continuousWithinAt_of_dominated_interval`.
3. Prove the section measurability and section continuity from `hF`.
4. Wrap the result pointwise to get `ContinuousOn`.

The theorem application has this shape:

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} {F : ℝ → ℝ → E}
    {S : Set ℝ} {t₀ c d : ℝ} {bound : ℝ → ℝ}
    (hF_meas : ∀ᶠ t in 𝓝[S] t₀,
      AEStronglyMeasurable (F t) (μ.restrict <| Ι c d))
    (h_bound : ∀ᶠ t in 𝓝[S] t₀,
      ∀ᵐ x ∂μ, x ∈ Ι c d → ‖F t x‖ ≤ bound x)
    (h_bound_int : IntervalIntegrable bound μ c d)
    (h_cont : ∀ᵐ x ∂μ,
      x ∈ Ι c d → ContinuousWithinAt (fun t => F t x) S t₀) :
    ContinuousWithinAt (fun t : ℝ => ∫ x in c..d, F t x ∂μ) S t₀ :=
  intervalIntegral.continuousWithinAt_of_dominated_interval
    hF_meas h_bound h_bound_int h_cont
```

For the compact-bound step, the names I would use are:

```lean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped Interval

#check IsCompact.prod
#check isCompact_Icc
#check isCompact_uIcc
#check IsCompact.bddAbove_image
#check ContinuousOn.norm
#check intervalIntegrable_const
#check uIoc_subset_uIcc
```

The pattern is:

```lean
-- S := Set.Icc a b
-- compact parameter set: isCompact_Icc
-- compact x-interval: isCompact_uIcc
-- compact rectangle: IsCompact.prod
-- bound: IsCompact.bddAbove_image applied to hF.norm
```

In prose, if

```lean
hK : IsCompact (S ×ˢ [[c,d]])
hF : ContinuousOn (Function.uncurry F) (S ×ˢ [[c,d]])
```

then use:

```lean
hK.bddAbove_image hF.norm
```

to get a real constant `C` bounding

```lean
fun p : ℝ × ℝ => ‖Function.uncurry F p‖
```

on the compact rectangle. Then use `bound := fun _ => C + 1` or a similar constant. For a locally finite measure, close the integrability side with:

```lean
intervalIntegrable_const
```

The inclusion from the interval-integral theorem's `Ι c d` to the compact interval is usually:

```lean
uIoc_subset_uIcc
```

This is why the DCT theorem's hypotheses mention `Ι c d`, while compact-continuity arguments often naturally produce facts on `[[c,d]]`.

## Practical recommendation

For your target:

```lean
ContinuousOn (fun t => ∫ x in c..d, F t x ∂μ) (Set.Icc a b)
```

try this order:

1. If possible, strengthen/obtain `hF : Continuous (Function.uncurry F)` and finish with:

   ```lean
   exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
     (f := F) (μ := μ) hF c d).continuousOn
   ```

2. If the hypothesis is only compact-rectangle `ContinuousOn`, use:

   ```lean
   intro t₀ ht₀
   refine intervalIntegral.continuousWithinAt_of_dominated_interval
     (F := F) (μ := μ) (s := Set.Icc a b) (x₀ := t₀)
     (bound := fun _ => C + 1) ?hF_meas ?h_bound ?h_bound_int ?h_cont
   ```

   with `C` from `IsCompact.bddAbove_image` on `Set.Icc a b ×ˢ [[c,d]]`.

3. If you are proving a limit statement first and converting it to continuity manually, the theorem name is:

   ```lean
   intervalIntegral.tendsto_integral_filter_of_dominated_convergence
   ```

My conclusion: `continuousOn_integral_of_compact` does not appear to be the exported Mathlib API name; the closest exported tools are `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` for global joint continuity and `intervalIntegral.continuousWithinAt_of_dominated_interval` for the compact `ContinuousOn`/dominated route.
