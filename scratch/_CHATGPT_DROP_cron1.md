# Q526 / cron1: `intervalNeumannResolverR` spatial regularity and evenness audit

## Executive verdict

I found **landed C² resolver regularity**, but **no landed C⁴ resolver theorem** for

```lean
intervalNeumannResolverR p u
```

or for its real-line cosine synthesis.  The existing resolver regularity is in two files:

1. `ShenWork/PDE/IntervalResolverSpatialC2.lean` — coefficient-decay route from `SourceCoeffQuadraticDecay p u`.
2. `ShenWork/PDE/IntervalResolverPhysicalC2.lean` — physical elliptic route from `Summable (fun k => |(intervalNeumannResolverSourceCoeff p u k).re|)`.

Both prove `ContDiff ℝ 2` / `ContDiffOn ℝ 2` for the **cosine synthesis**

```lean
fun x : ℝ => ∑' k : ℕ,
  (intervalNeumannResolverCoeff p u k).re * cosineMode k x
```

not a literal global function `fun x => intervalNeumannResolverR p u x`, since `intervalNeumannResolverR p u` has domain `intervalDomainPoint`, i.e. the subtype `[0,1]`.  The bridge from the synthesis to the actual resolver value on interval points is `resolverR_eq_cosineSeries`.

For evenness: I found `cosineMode_neg`, and the resolver-floor code uses `cosineMode_neg` with `tsum_congr` inside the full real-line resolver synthesis.  I did **not** find a packaged theorem named like

```lean
intervalNeumannResolverR_even
resolverR_even
resolverSynthesis_even
```

or a literal statement `intervalNeumannResolverR p u (-x) = intervalNeumannResolverR p u x`.  Also, that literal statement is not type-correct as written unless one first works with a lifted/synthesis function on `ℝ`, because `intervalNeumannResolverR p u` takes `intervalDomainPoint`, not arbitrary `ℝ`.

## Exact hits: resolver definition and coefficient equation

`ShenWork/PDE/IntervalNeumannEllipticResolverR.lean` defines the source coefficient, resolver coefficient, and resolver:

* `intervalNeumannResolverSourceCoeff` at `IntervalNeumannEllipticResolverR.lean:76-80`.
* `intervalNeumannResolverCoeff` at `IntervalNeumannEllipticResolverR.lean:89-92`.
* `intervalNeumannResolverR` at `IntervalNeumannEllipticResolverR.lean:102-108`:

```lean
def intervalNeumannResolverR
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    intervalDomainPoint → ℝ :=
  fun x =>
    ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
        unitIntervalCosineMode k x.1
```

The coefficient-form elliptic identity is already landed:

* `intervalNeumannResolverCoeff_elliptic` at `IntervalNeumannEllipticResolverR.lean:141-149`:

```lean
theorem intervalNeumannResolverCoeff_elliptic
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) *
        intervalNeumannResolverCoeff p u k =
      intervalNeumannResolverSourceCoeff p u k := by
```

This is the equation needed to prove inequalities of the form

```lean
λ_k * |v̂_k| ≤ |â_k|
λ_k^2 * |v̂_k| ≤ λ_k * |â_k|
```

where `v̂_k = intervalNeumannResolverCoeff p u k` and `â_k = intervalNeumannResolverSourceCoeff p u k`.

## Existing C² route 1: `SourceCoeffQuadraticDecay`

File: `ShenWork/PDE/IntervalResolverSpatialC2.lean`.

The file header says it proves spatial C² regularity and Neumann endpoint facts for the elliptic resolver under `SourceCoeffQuadraticDecay`; specifically it lists `resolverR_summability`, `resolverR_eq_cosineSeries`, `resolverR_contDiff_two`, and endpoint derivative lemmas at `IntervalResolverSpatialC2.lean:13-25`.

Main theorem references:

* `resolverR_summability`, `IntervalResolverSpatialC2.lean:62-75`:

```lean
theorem resolverR_summability
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re|) := by
```

This is the one-eigenvalue-weight summability input for C².

* `resolverR_eq_cosineSeries`, `IntervalResolverSpatialC2.lean:82-89`:

```lean
theorem resolverR_eq_cosineSeries
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (x : intervalDomainPoint) :
    intervalNeumannResolverR p u x =
      ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k x.1 := by
```

This is the bridge from the actual subtype-valued resolver to the real-line synthesis form.

* `resolverR_contDiff_two`, `IntervalResolverSpatialC2.lean:96-102`:

```lean
theorem resolverR_contDiff_two
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    ContDiff ℝ 2
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x) :=
  cosineCoeffSeries_contDiff_two (resolverR_summability hdecay)
```

* `resolverR_contDiffOn_Icc`, `IntervalResolverSpatialC2.lean:128-135`:

```lean
theorem resolverR_contDiffOn_Icc
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    ContDiffOn ℝ 2
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) :=
  (resolverR_contDiff_two hdecay).contDiffOn
```

Endpoint Neumann facts are also there:

* `resolverR_deriv_at_zero`, `IntervalResolverSpatialC2.lean:107-112`.
* `resolverR_deriv_at_one`, `IntervalResolverSpatialC2.lean:117-122`.

## Existing C² route 2: physical/source-ℓ¹ route

File: `ShenWork/PDE/IntervalResolverPhysicalC2.lean`.

This file explicitly states that it proves a physical/elliptic C² route from source coefficient `ℓ¹`; see the summary at `IntervalResolverPhysicalC2.lean:34-40`.

Key theorem references:

* `resolverR_eigenWeighted_le_source`, `IntervalResolverPhysicalC2.lean:61-97`:

```lean
theorem resolverR_eigenWeighted_le_source
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re| ≤
      |(intervalNeumannResolverSourceCoeff p u k).re| := by
```

This is exactly the inequality you described for the C² level.

* `resolverR_eigenWeighted_summable_of_sourceL1`, `IntervalResolverPhysicalC2.lean:106-115`:

```lean
theorem resolverR_eigenWeighted_summable_of_sourceL1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re|) := by
```

* `resolverR_contDiff_two_of_source_l1`, `IntervalResolverPhysicalC2.lean:122-128`:

```lean
theorem resolverR_contDiff_two_of_source_l1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 2
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x) :=
  cosineCoeffSeries_contDiff_two (resolverR_eigenWeighted_summable_of_sourceL1 hsrc)
```

* `resolverR_contDiffOn_Icc_of_source_l1`, `IntervalResolverPhysicalC2.lean:131-138`:

```lean
theorem resolverR_contDiffOn_Icc_of_source_l1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiffOn ℝ 2
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) :=
  (resolverR_contDiff_two_of_source_l1 hsrc).contDiffOn
```

## Evidence that C⁴ is not already packaged for the resolver

I searched for the requested patterns:

* `intervalNeumannResolverR ContDiff`
* `intervalNeumannResolverR ContDiffOn`
* `resolver contDiff`
* `resolverR C2`
* `resolverR_contDiff_four`
* `cosineCoeffSeries_contDiff_four`

The resolver-specific hits bottom out at C² (`IntervalResolverSpatialC2.lean`, `IntervalResolverPhysicalC2.lean`, and audit/consumer files).  Search for `resolverR_contDiff_four` returned no hits.

There **is** a generic C⁴ cosine-series engine:

* `cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable`, `ShenWork/Paper2/IntervalParabolicDuhamelGainNonCircular.lean:354-405`:

```lean
theorem cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
    {b : ℕ → ℝ}
    (hb : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |b n|))) :
    ContDiff ℝ 4 (fun x : ℝ => ∑' n : ℕ, b n * cosineMode n x) := by
```

So the missing resolver-C⁴ lemma should be small and direct, but it is not currently named/packaged for the resolver.  The natural new lemma is the C⁴ analogue of `resolverR_eigenWeighted_le_source`:

```lean
λ_k * (λ_k * |(intervalNeumannResolverCoeff p u k).re|)
  ≤ λ_k * |(intervalNeumannResolverSourceCoeff p u k).re|
```

Then:

```lean
theorem resolverR_contDiff_four_of_source_eigenWeighted_l1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc1 : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 4
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x) :=
  cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
    (resolverR_eigenSqWeighted_summable_of_sourceEigenWeighted hsrc1)
```

That is exactly your heuristic: for C², source `ℓ¹` gives resolver eigenvalue-weight `ℓ¹`; for C⁴, source one-eigenvalue-weight `ℓ¹` gives resolver two-eigenvalue-weight `ℓ¹`.

## Audit file confirms no stronger Schauder-style resolver C²/C⁴ API

`ShenWork/Paper2/IntervalEllipticResolverC2Audit.lean` says the committed elliptic resolver regularity does **not** include a Schauder/Hölder-source theorem; the available spatial theorem is `IntervalResolverSpatialC2.resolverR_contDiff_two` with `SourceCoeffQuadraticDecay` as hypothesis.  See `IntervalEllipticResolverC2Audit.lean:28-47`.

This audit is about C², but it reinforces the same conclusion for C⁴: the repo has coefficient-series regularity engines and C² resolver wrappers, not a higher-order packaged resolver regularity theorem.

## Evenness / symmetry status

The primitive cosine-mode evenness theorem exists:

* `cosineMode_neg`, `ShenWork/Wiener/EWA/HeatFloor.lean:115-118`:

```lean
theorem cosineMode_neg (k : ℕ) (x : ℝ) :
    ShenWork.CosineSpectrum.cosineMode k (-x) = ShenWork.CosineSpectrum.cosineMode k x := by
```

The same file also has the period-two theorem:

* `cosineMode_add_two`, `HeatFloor.lean:121-126`.
* `cosineMode_add_int_two`, `HeatFloor.lean:149-154`.

For the resolver synthesis, `SourceResolverFloor.lean` uses these facts rather than packaging a standalone evenness theorem:

* `resolverSynthesis_eq_resolverR`, `ShenWork/Wiener/EWA/SourceResolverFloor.lean:152-157`, bridges the real-line synthesis to the actual resolver on `[0,1]`:

```lean
theorem resolverSynthesis_eq_resolverR (p : CM2Params) (uR : intervalDomainPoint → ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑' k : ℕ, (intervalNeumannResolverCoeff p uR k).re * cosineMode k x)
      = intervalNeumannResolverR p uR ⟨x, hx⟩ := by
```

* `resolverSynthesis_nonneg_all`, `SourceResolverFloor.lean:170-193`, reduces all real `x` to `[0,1]`; inside it, the equality step uses

```lean
rw [show x = y + 2 * (m : ℝ) from by rw [hy]; ring, cosineMode_add_int_two]
...
rw [h]; exact tsum_congr (fun k => by rw [cosineMode_neg])
```

So the ingredients for evenness are present, and the resolver synthesis already uses them, but I did **not** find a named theorem of the form

```lean
theorem resolverSynthesis_neg ...
theorem intervalNeumannResolverR_even ...
```

A minimal standalone theorem should be immediate:

```lean
theorem resolverSynthesis_neg (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    (∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k (-x)) =
      ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k x := by
  exact tsum_congr (fun k => by rw [ShenWork.EWA.cosineMode_neg])
```

For a statement involving `intervalNeumannResolverR`, formulate it on the subtype `[0,1]` via `resolverR_eq_cosineSeries`, or formulate it for the real-line synthesis.  The raw expression `intervalNeumannResolverR p u (-x)` is not type-correct unless `-x` is supplied as an `intervalDomainPoint`.