# Q714 / cron1: joint `C²` of the heat semigroup cosine series

Repo inspected: `xiangyazi24/Shen_work`.  Scratch write target: branch `chatgpt-scratch`.

Target shape:

```lean
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ =>
    ∑' k, a k * Real.exp (-q.1 * unitIntervalCosineEigenvalue k) * cosineMode k q.2)
  (s, x)
```

for `0 < s` and `x ∈ Ioo 0 1`.

## Verdict

The repo has strong **generic joint-series `C²` infrastructure**, especially:

```lean
boundedWeightJointSeries_contDiff_two
```

and the exact Mathlib tool is:

```lean
contDiff_tsum
```

from:

```text
Mathlib/Analysis/Calculus/SmoothSeries.lean
```

But I did **not** find a completed theorem specifically giving

```lean
ContDiffAt ℝ 2 (fun (s,x) => U s x) (s₀,x₀)
```

for the heat semigroup’s uncurried two-variable cosine series.  The repo has fixed-time spatial smoothness of heat slices and private heat-series **joint continuity** proofs, but not the exact public joint `ContDiffAt ℝ 2` theorem for the heat value series.

The practical route is therefore one of:

1. package the heat coefficients into the existing bounded-weight joint-series API, with a **local positive-time cutoff/local slab** so the exponential majorants are summable uniformly near `s₀`; or
2. prove a direct local `contDiff_tsum` theorem on a box `Ioo c d ×ˢ univ` with `0 < c < s₀ < d`, then take `.contDiffAt` at `(s₀,x₀)`.

## 1. Existing `boundedWeightJointSeries_contDiff_two` / joint `C²` cosine-series tools

The main generic file is:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

It defines the mode term:

```lean
def boundedWeightJointTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * cosineMode n q.2
```

and the joint majorant:

```lean
def boundedWeightJointMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

The key theorem is:

```lean
theorem boundedWeightJointSeries_contDiff_two
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
    (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
    (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant Bt k)) :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointTerm c n q)
```

It is implemented directly by Mathlib `contDiff_tsum`:

```lean
contDiff_tsum
  (𝕜 := ℝ) (f := boundedWeightJointTerm c)
  (v := boundedWeightJointMajorant Bt)
  ...
```

The same file also has the spatial-gradient analogue:

```lean
theorem boundedWeightJointGradSeries_contDiff_two ... :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointGradTerm c n q)
```

### Existing consumer for arbitrary Picard iterate data

```text
ShenWork/PDE/IntervalIteratePicardJointC2.lean
```

has the exact kind of `ContDiffAt` producer for an abstract cosine-series iterate:

```lean
structure IteratePicardJointC2Data
    (u : ℝ → intervalDomainPoint → ℝ) (c : ℕ → ℝ → ℝ) (Bt : ℕ → ℕ → ℝ) : Prop where
  lift_eq_series : ∀ {t x : ℝ}, x ∈ Icc (0 : ℝ) 1 →
    intervalDomainLift (u t) x = ∑' k : ℕ, c k t * cosineMode k x
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (c k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (c k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
```

and:

```lean
theorem iterate_lift_jointContDiffAt_two
    (H : IteratePicardJointC2Data u c Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)
```

This is very close structurally, but it is **not specialized to the heat semigroup coefficients**.  To use it for heat, you still need to instantiate the data with

```lean
c k t = a k * Real.exp (-t * unitIntervalCosineEigenvalue k)
```

and supply coefficient bounds/summability.

### Important caveat for heat

`boundedWeightJointSeries_contDiff_two` is a **global** `ContDiff` theorem, so the bound

```lean
∀ t, ‖∂ₜ^i c k t‖ ≤ Bt i k
```

must hold for all real `t`.  For heat coefficients `exp(-t λ_k)`, that global bound is false/summability-hostile as `t → -∞`.

For an interior point `s₀ > 0`, the natural proof is local:

```lean
choose c0 d0 with 0 < c0 < s₀ < d0
```

and use the uniform bound on `t ∈ Ioo c0 d0`:

```lean
|∂ₜ^i (a k * exp(-t λ_k))| ≤ |a k| * λ_k^i * exp(-c0 * λ_k)
```

This points to either a localized `contDiffOn_tsum` proof, or a smooth cutoff/local-restart trick to fit a global `contDiff_tsum` theorem.

## 2. Existing heat semigroup uncurried `ContDiffAt` theorem?

Searches run:

```text
heat semigroup ContDiffAt
heatValue ContDiffAt
unitIntervalCosineHeatValue ContDiff
heatCoeff ContDiffAt ℝ 2
conjugatePicardIter ContDiffAt ℝ 2 fun q
jointContDiffAt heat
HeatSmoothness ContDiffAt
```

I did **not** find an exported theorem directly stating joint two-variable heat semigroup regularity:

```lean
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ => unitIntervalCosineHeatValue q.1 a q.2)
  (s, x)
```

or:

```lean
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
  (s, x)
```

### What exists instead: fixed-time spatial heat smoothness

```text
ShenWork/Paper2/IntervalCD6HeatSmoothness.lean
```

has:

```lean
theorem unitIntervalCosineHeatValue_contDiff_seven
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    ContDiff ℝ 7 (fun x => unitIntervalCosineHeatValue t a x)
```

This is a **fixed-time spatial** theorem.  It uses `contDiff_tsum` with majorant

```lean
|(n : ℝ) * Real.pi| ^ k * Real.exp (-t * unitIntervalCosineEigenvalue n) * |M|
```

and the summability lemma:

```lean
frequency_pow_mul_exp_summable k ht
```

It proves high spatial smoothness of the slice `x ↦ S(t)u₀(x)`, but it does not give joint `(t,x)` `ContDiffAt`.

### What exists instead: private heat-series joint continuity

```text
ShenWork/Wiener/EWA/SourceJointRegularity.lean
```

has private heat-leg joint-continuity lemmas, e.g.

```lean
private theorem heatValueSeries_jointContinuousOn (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        ∑' n, Real.exp (-q.1 * unitIntervalCosineEigenvalue n) * u₀cos n * cosineMode n q.2)
      (Ioi (0 : ℝ) ×ˢ univ)
```

and a private time-derivative analogue:

```lean
private theorem heatDerivSeries_jointContinuousOn ...
```

These are only `ContinuousOn`, not `ContDiffAt ℝ 2`, and they are private.

```text
ShenWork/Wiener/EWA/SourceJointRegularityOn.lean
```

reproduces the same heat-leg helpers as private theorems because the original ones are private.

## 3. Exact Mathlib tool: `contDiff_tsum`

At the pinned Mathlib rev from the repo manifest (`v4.29.1`, commit `5e932f97...`), the theorem is in:

```text
Mathlib/Analysis/Calculus/SmoothSeries.lean
```

The exact theorem is:

```lean
theorem contDiff_tsum
    (hf : ∀ i, ContDiff 𝕜 N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α) (x : E), k ≤ N →
      ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x
```

There is also:

```lean
theorem iteratedFDeriv_tsum ...
```

and:

```lean
theorem contDiff_tsum_of_eventually ...
```

I did **not** find a `contDiffAt_tsum` theorem in the repo search.  The standard route is:

```lean
have h : ContDiff ℝ (2 : ℕ∞) (fun q => ∑' n, term n q) :=
  contDiff_tsum ...
exact h.contDiffAt
```

or, for a local domain, prove `ContDiffOn`/local `ContinuousOn` on a neighborhood and then use the corresponding local API/convert to `ContDiffAt` if available.

## 4. Other `contDiff_tsum` usages worth knowing

### Resolver restart assembly

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Assemble.lean
```

has:

```lean
theorem resolverSpectralJointC2At_of_contDiff_tsum ... :
    ResolverSpectralJointC2At a₀ a offset s x := by
  have hValue : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ =>
        ∑' n : ℕ, resolverSpectralValueTerm a₀ a offset n q) :=
    contDiff_tsum ...
  have hGrad : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, gradTerm n q) :=
    contDiff_tsum ...
  refine ⟨?_, ?_⟩
  · simpa [resolverSpectralSeries, resolverSpectralValueTerm] using
      hValue.contDiffAt
  · exact hGrad.contDiffAt.congr_of_eventuallyEq hGradEq
```

This is the cleanest pattern for “prove global/local series `ContDiff`, then take `.contDiffAt` and use eventual equality”.

### Fixed-time high spatial heat smoothness

```text
ShenWork/Paper2/IntervalCD6HeatSmoothness.lean
```

uses:

```lean
contDiff_tsum
  (f := fun n x => unitIntervalCosineHeatPointWeight t x n * a n)
  (v := v) (N := (7 : ℕ∞)) ...
```

This is useful for the spatial part of heat, but not enough for the requested two-variable `(s,x)` theorem.

## Recommended theorem to add

A useful target theorem would be local-positive-time, not global-in-time:

```lean
theorem heatCosineSeries_contDiffAt_two
    {a : ℕ → ℝ} {M s x : ℝ}
    (hs : 0 < s)
    (ha : ∀ k, |a k| ≤ M) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        ∑' k,
          Real.exp (-q.1 * unitIntervalCosineEigenvalue k) * a k * cosineMode k q.2)
      (s, x) := by
  -- choose c = s/2, local box `Ioo c (s+1) ×ˢ univ`
  -- use `contDiff_tsum` or a localized version with majorants
  --   |a k| * λ_k^i * |kπ|^j * exp(-c λ_k)
  -- for i+j ≤ 2; summability follows from exponential decay.
  -- take `.contDiffAt` at `(s,x)`.
```

For the interval-domain heat level:

```lean
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ => intervalDomainLift (picardIter p u₀ 0 q.1) q.2)
  (s, x)
```

with `x ∈ Ioo 0 1`, combine the cosine-series theorem with the existing interior agreement theorem:

```lean
ShenWork.IntervalPicardIterateRepresentation.hagree_zero
```

or its definitional representation for `conjugatePicardIter p u₀ 0`, using eventual equality on the open spatial neighborhood `Ioo 0 1`.

## Search summary

Searches run:

```text
contDiff_tsum
contDiffAt_tsum
jointSeries contDiff
JointSeries_contDiff
boundedWeight contDiff
heat semigroup ContDiffAt
heatValue ContDiffAt
unitIntervalCosineHeatValue ContDiff
heatCoeff ContDiffAt ℝ 2
conjugatePicardIter ContDiffAt ℝ 2 fun q
jointContDiffAt heat
HeatSmoothness ContDiffAt
```

Key files found:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
ShenWork/PDE/IntervalIteratePicardJointC2.lean
ShenWork/PDE/IntervalResolverSpectralJointC2Assemble.lean
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
ShenWork/Paper2/IntervalCD6HeatSmoothness.lean
ShenWork/Wiener/EWA/SourceJointRegularity.lean
ShenWork/Wiener/EWA/SourceJointRegularityOn.lean
Mathlib/Analysis/Calculus/SmoothSeries.lean
```
