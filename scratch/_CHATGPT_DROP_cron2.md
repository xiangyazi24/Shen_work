# Q585 (cron2): `intervalNeumannResolverR` vs high-regularity resolver synthesis

## Executive verdict

On `chatgpt-scratch`, the high-regularity file does **not** currently use the names

```lean
intervalResolverLiftR
intervalResolverLiftR_contDiff_four
intervalResolverLiftR_even
intervalResolverLiftR_reflect_one
```

Instead, the corresponding real-line representative is named

```lean
resolverRSynthesis
```

with theorems

```lean
resolverR_contDiff_four
resolverR_even
resolverR_symm1
```

The answer to your mathematical question is: **yes, it is the same resolver on `[0,1]` / on `intervalDomainPoint`**.  The branch already has the bridge theorem:

```lean
theorem intervalNeumannResolverR_eq_resolverRSynthesis
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : intervalDomainPoint) :
    intervalNeumannResolverR p u x = resolverRSynthesis p u x.1
```

So for

```lean
u := conjugatePicardIter p u₀ 0 s
```

and

```lean
coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s
  = intervalNeumannResolverR p (conjugatePicardIter p u₀ 0 s)
```

by definition, you can rewrite the interval-domain resolver value to the real-line synthesis value at `x.1`.

The only difference is the **domain/codomain wrapper**:

- `intervalNeumannResolverR p u : intervalDomainPoint → ℝ`
- `resolverRSynthesis p u : ℝ → ℝ`

On `x : intervalDomainPoint`, they agree at `x.1`.  They do not differ in coefficients or basis.

## 1. Resolver used by the coupled concentration

`ShenWork/PDE/IntervalCoupledRegularityBootstrap.lean:29`

```lean
/-- The concrete elliptic signal attached to a coupled trajectory. -/
def coupledChemicalConcentration (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t => intervalNeumannResolverR p (u t)
```

Therefore for the level-0 heat trajectory:

```lean
coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s
  = intervalNeumannResolverR p (conjugatePicardIter p u₀ 0 s)
```

is just definitional unfolding.

## 2. Definition of the committed interval resolver

`ShenWork/PDE/IntervalNeumannEllipticResolverR.lean:104`

```lean
def intervalNeumannResolverR
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    intervalDomainPoint → ℝ :=
  fun x =>
    ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
        unitIntervalCosineMode k x.1
```

This is the subtype-valued resolver used downstream.

## 3. Definition of the high-regularity real-line representative

`ShenWork/Paper2/IntervalResolverHighRegularity.lean:42`

```lean
/-- The real-line cosine synthesis associated to the interval Neumann resolver.

This is the natural globally-defined representative of `intervalNeumannResolverR p u`.
On the fundamental interval `[0,1]`, it agrees with the subtype-valued resolver via
`IntervalResolverSpatialC2.resolverR_eq_cosineSeries`. -/
def resolverRSynthesis (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k x
```

This is exactly the object your message calls `intervalResolverLiftR`, modulo naming.

## 4. Existing bridge theorem: they agree on `intervalDomainPoint`

`ShenWork/Paper2/IntervalResolverHighRegularity.lean:50`

```lean
/-- The resolver value on the interval agrees with the real-line synthesis. -/
theorem intervalNeumannResolverR_eq_resolverRSynthesis
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : intervalDomainPoint) :
    intervalNeumannResolverR p u x = resolverRSynthesis p u x.1 := by
  simpa [resolverRSynthesis] using
    ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries (p := p) (u := u) x
```

So the bridge is already proved.  You do not need to reprove coefficient equality or basis equality for this connection.

## 5. Lower-level basis bridge

`ShenWork/PDE/IntervalResolverSpatialC2.lean:81` gives the intermediate theorem:

```lean
theorem resolverR_eq_cosineSeries
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (x : intervalDomainPoint) :
    intervalNeumannResolverR p u x =
      ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k x.1 := by
  unfold intervalNeumannResolverR
  refine tsum_congr (fun k => ?_)
  rw [unitIntervalCosineMode_eq_cosineMode]
```

The file header states the point explicitly: `intervalNeumannResolverR` uses `unitIntervalCosineMode`, and `unitIntervalCosineMode k y = cosineMode k y` is the bridge from `HeatKernelLpEstimates`.

`ShenWork/PDE/CosineSpectrum.lean:22` defines the ambient cosine mode:

```lean
/-- The same cosine mode as a function on the ambient real line. -/
def cosineMode (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos ((n : ℝ) * Real.pi * x)
```

`ShenWork/Wiener/EWA/ResolverEvalBridge.lean:37` also records the intended match:

```lean
-- Basis match (`cosineMode = unitIntervalCosineMode`).
-- ... These are definitionally the same (`Real.cos (kπx)`), bridged by the committed
-- `unitIntervalCosineMode_eq_cosineMode`.
```

So yes: both bases are the same cosine basis; the repo has a named bridge theorem for it.

## 6. High-regularity theorems available on the real-line representative

`ShenWork/Paper2/IntervalResolverHighRegularity.lean:97`

```lean
theorem resolverR_contDiff_four
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 4 (resolverRSynthesis p u)
```

`ShenWork/Paper2/IntervalResolverHighRegularity.lean:108`

```lean
theorem resolverR_even (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    resolverRSynthesis p u (-x) = resolverRSynthesis p u x
```

`ShenWork/Paper2/IntervalResolverHighRegularity.lean:115`

```lean
theorem resolverR_symm1 (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    resolverRSynthesis p u (2 - x) = resolverRSynthesis p u x
```

These are the current names corresponding to your `intervalResolverLiftR_contDiff_four`, `intervalResolverLiftR_even`, and `intervalResolverLiftR_reflect_one`.

## 7. Practical bridge for the level-0 coupled concentration

A direct lemma you can add/use:

```lean
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.Paper2.ResolverHighRegularity

@[simp] theorem coupledChemicalConcentration_eq_resolverRSynthesis_level0
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (s : ℝ)
    (x : intervalDomainPoint) :
    coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s x =
      resolverRSynthesis p (conjugatePicardIter p u₀ 0 s) x.1 := by
  rw [coupledChemicalConcentration]
  exact intervalNeumannResolverR_eq_resolverRSynthesis
    p (conjugatePicardIter p u₀ 0 s) x
```

Depending on namespace/imports, the proof may need fully qualified names:

```lean
  rw [ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration]
  exact ShenWork.Paper2.ResolverHighRegularity.intervalNeumannResolverR_eq_resolverRSynthesis
    p (conjugatePicardIter p u₀ 0 s) x
```

For a general trajectory `u`, the more reusable version is:

```lean
@[simp] theorem coupledChemicalConcentration_eq_resolverRSynthesis
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ)
    (x : intervalDomainPoint) :
    coupledChemicalConcentration p u s x =
      resolverRSynthesis p (u s) x.1 := by
  rw [ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration]
  exact ShenWork.Paper2.ResolverHighRegularity.intervalNeumannResolverR_eq_resolverRSynthesis
    p (u s) x
```

## 8. How to use C⁴/even/reflection for the interval resolver

If you need high regularity for the interval-domain resolver, work with the real-line representative:

```lean
have hC4 : ContDiff ℝ 4
    (resolverRSynthesis p (conjugatePicardIter p u₀ 0 s)) :=
  resolverR_contDiff_four hsrc
```

and transfer pointwise values to `coupledChemicalConcentration` / `intervalNeumannResolverR` using

```lean
intervalNeumannResolverR_eq_resolverRSynthesis
```

For derivatives at endpoint/reflection arguments, the real-line representative is the right object; the interval-domain function only has subtype domain and cannot itself be differentiated as `ℝ → ℝ` until you choose a real-line representative/lift.  The branch already chooses `resolverRSynthesis` for exactly this purpose.

## Conclusion

`intervalNeumannResolverR` and the high-regularity real-line synthesis do not differ analytically.  They are the same cosine series with the same coefficients and the same cosine basis; the only distinction is domain:

```text
intervalNeumannResolverR p u : intervalDomainPoint → ℝ
resolverRSynthesis p u       : ℝ → ℝ
```

On `x : intervalDomainPoint`, the equality is already proved by

```lean
intervalNeumannResolverR_eq_resolverRSynthesis p u x
```