# Q619 / cron1: eigenvalue-weighted resolver-source summability for the heat semigroup

## Verdict

I did **not** find a theorem in the repo that directly proves the target hypothesis

```lean
Summable (fun k : ℕ =>
  unitIntervalCosineEigenvalue k *
    |(intervalNeumannResolverSourceCoeff p (conjugatePicardIter p u₀ 0 s) k).re|)
```

or the equivalent heat-level statement for the resolver source `ν * (S(s)u₀)^γ`.

In other words: the repo has the **consumer** for this hypothesis, and it has several nearby heat/coefficient-summability engines, but I found no producer specialized to

```lean
u = conjugatePicardIter p u₀ 0 s
```

and no theorem whose conclusion is eigenvalue-`ℓ¹` summability of

```lean
(intervalNeumannResolverSourceCoeff p u k).re
```

for the heat semigroup / level-0 Picard iterate.

## Exact consumer found

`ShenWork/Paper2/IntervalResolverHighRegularity.lean` has the C⁴ resolver route.  The key theorem is generic and consumes exactly the missing source-side hypothesis:

```lean
theorem resolverR_contDiff_four
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 4 (resolverRSynthesis p u)
```

Location:

- `ShenWork/Paper2/IntervalResolverHighRegularity.lean:97-106`

Just above it, the file proves the comparison step:

```lean
theorem resolverR_eigenSqWeighted_summable_of_sourceEigenWeighted
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        (unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re|))
```

Location:

- `ShenWork/Paper2/IntervalResolverHighRegularity.lean:77-90`

So the C⁴ resolver theorem exists, but its `hsrc` is still an input.

## Nearby results that are **not** the target

### 1. Source `ℓ¹` gives resolver C², not source eigenvalue-`ℓ¹`

`ShenWork/PDE/IntervalResolverPhysicalC2.lean` proves:

```lean
theorem resolverR_eigenWeighted_summable_of_sourceL1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re|)
```

Location:

- `ShenWork/PDE/IntervalResolverPhysicalC2.lean:108-117`

This is resolver-coefficient weighted summability from source `ℓ¹`, i.e. the C² route, not eigenvalue-weighted summability of the source coefficients themselves.

### 2. Heat semigroup coefficient summability exists for the raw heat coefficients

`ShenWork/PDE/IntervalSemigroupNeumann.lean` has:

```lean
theorem heatCoeff_eigenvalue_summable {t : ℝ} (ht : 0 < t)
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * a n|)
```

Location:

- `ShenWork/PDE/IntervalSemigroupNeumann.lean:33-73`

This is the expected heat smoothing for the **linear heat coefficient leg**.  It is not about the nonlinear resolver source `ν * (S(t)u₀)^γ`.

On `main`, there is also a stronger raw heat theorem:

```lean
theorem heatSemigroup_eigenvalueSq_summable
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k => unitIntervalCosineEigenvalue k ^ 2 *
      |Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k|)
```

Location:

- `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:27-33`

Again, this is raw `S(t)u₀` coefficient summability, not the power-source/resolver-source coefficient family.

### 3. Per-slice gradient summability exists for a mild decomposition, but not resolver source

`ShenWork/Paper2/IntervalChiNegGradSummable.lean` has:

```lean
theorem gradSummable_heat ... :
    Summable (fun k : ℕ =>
      lam k * |Real.exp (-(τ * lam k)) * uhat0 k|)
```

and

```lean
theorem gradSummable_slice ... :
    Summable (fun k : ℕ =>
      lam k * |cosineCoeffs (intervalDomainLift (u τ)) k|)
```

Locations:

- `ShenWork/Paper2/IntervalChiNegGradSummable.lean:88-99`
- `ShenWork/Paper2/IntervalChiNegGradSummable.lean:123-189`

These concern the slice coefficients of `u τ`, not the nonlinear source coefficients of `ν * u^γ`.

### 4. Quadratic decay for the power source exists, but it is weaker than `hsrc`

On `main`, `ShenWork/Wiener/EWA/SourceResolverSpectralDischarge.lean` proves a pointwise quadratic-decay route:

```lean
def realSlice_resolverDecay ... :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      SourceCoeffQuadraticDecay p (realSlice u_star t)
```

Location:

- `ShenWork/Wiener/EWA/SourceResolverSpectralDischarge.lean:138-167`

And `ShenWork/Wiener/EWA/ResolverSourceWindowUniformDecay.lean` proves a window-uniform quadratic-decay constant for

```lean
cosineCoeffs (fun x => p.ν * intervalDomainLift (realSlice u_star σ) x ^ p.γ) k
```

Location:

- `ShenWork/Wiener/EWA/ResolverSourceWindowUniformDecay.lean:69-131`

But quadratic decay alone is not the desired `hsrc`: if `|a_k| ≤ C / ((kπ)^2)`, then `λ_k * |a_k| ≤ C`, which is not summable.  So these are not enough for `intervalResolverLiftR_contDiff_four` / `resolverR_contDiff_four`.

### 5. Weak source `ℓ²` exists, but not eigenvalue-`ℓ¹`

`ShenWork/Paper2/IntervalResolverWeakBounds.lean` proves only source coefficient square-summability from continuity:

```lean
theorem resolverSourceCoeff_re_sq_summable_of_continuousOn
    (p : CM2Params) {u : intervalDomainPoint → ℝ}
    (hUcont : ContinuousOn (intervalDomainLift u) (Set.Icc (0:ℝ) 1)) :
    Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u k -
        intervalNeumannResolverSourceCoeff p (fun _ => 0) k).re) ^ 2
```

Location:

- `ShenWork/Paper2/IntervalResolverWeakBounds.lean:63-90`

This is `ℓ²`, not `Summable (λ_k * |sourceCoeff k|)`.

### 6. Resolver-source time-`C¹` producer exists, but it is not this summability theorem

`ShenWork/Paper2/IntervalResolverSourceTimeC1.lean` has a global representation-fed producer:

```lean
noncomputable def resolverSource_timeC1_of_global_representation ... :
    DuhamelSourceTimeC1
      (fun s k => (ShenWork.PDE.intervalNeumannResolverSourceCoeff p (w s) k).re)
```

Location:

- `ShenWork/Paper2/IntervalResolverSourceTimeC1.lean:142-165`

It consumes representation summability of the underlying slice coefficients plus quadratic-decay/K1 data for the power source and produces a time-`C¹` package.  It does not conclude eigenvalue-weighted summability of the resolver source coefficients.

## Grep/search outcome

Searches I ran or effectively checked:

```text
resolverSourceCoeff eigenvalue summable
resolverSource summable
intervalResolverLiftR_contDiff_four / resolverR_contDiff_four
intervalNeumannResolverSourceCoeff Summable unitIntervalCosineEigenvalue
unitIntervalCosineEigenvalue k * |(intervalNeumannResolverSourceCoeff
conjugatePicardIter intervalNeumannResolverSourceCoeff Summable
conjugatePicardIter resolverSourceCoeff
sourceEigenWeighted
powerSource eigenvalue Summable resolverSource
```

The exact target shape only appears as a **hypothesis/consumer input** in `IntervalResolverHighRegularity.lean`, not as a produced theorem for the heat semigroup.

## Recommended next lemma

The missing theorem should be added as a producer, probably with a name like:

```lean
theorem heatResolverSourceCoeff_eigenvalue_summable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {s : ℝ}
    (hs : 0 < s)
    -- plus whatever boundedness/positivity/smoothness hypotheses the existing heat level-0 API carries
    : Summable (fun k : ℕ =>
        unitIntervalCosineEigenvalue k *
          |(intervalNeumannResolverSourceCoeff p
              (conjugatePicardIter p u₀ 0 s) k).re|)
```

Analytically, the intended route is plausible: heat smoothing gives exponential/polynomial-weight summability for the heat coefficients, and the power source `ν*(S(s)u₀)^γ` should inherit enough smoothness/decay on `s > 0`.  But I did not find the Lean theorem that packages this implication for the resolver source coefficients.
