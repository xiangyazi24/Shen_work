# Q578 / cron1: heat semigroup spectral identity for `intervalDomainLift u₀`

## Verdict

There are **two routes** in the repo:

1. **Closed interval `[0,1]`, continuous subtype datum**: use the committed constant-extension adapter

```lean
ShenWork.IntervalSpectralSubtypeAdapter
  .intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
```

This is the best route for your stated target with `x ∈ Icc 0 1` and `u₀ : intervalDomainPoint → ℝ` continuous.  It avoids the false hypothesis `Continuous (intervalDomainLift u₀)` by replacing the zero extension with the constant extension internally, then transfers back.

2. **Rough/L¹ input route**: yes, there is a theorem for integrable input,

```lean
ShenWork.IntervalNHGBricks.operator_eq_cosineModel_of_integrable
```

but it only gives the identity for **interior** points `x ∈ Ioo 0 1`, not the closed interval.  It is the L¹-dominated `FullKernelIntegralInterchange` route.

I did **not** find a direct theorem that states the full closed-interval spectral identity from only `AEStronglyMeasurable`/bounded input.  For bounded AEStronglyMeasurable input you can first get `Integrable f (intervalMeasure 1)` and then use the L¹ theorem on `Ioo`; for endpoints, the packaged theorem is the subtype-continuity/constant-extension adapter.

## Definitions and low-level facts

`intervalFullSemigroupOperator` itself accepts an arbitrary function syntactically:

```lean
-- ShenWork/PDE/IntervalNeumannFullKernel.lean:79-81
/-- The full periodised-image Neumann heat propagator on `[0,1]`. -/
def intervalFullSemigroupOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1
```

So the operator definition has no `Continuous`/`Measurable` argument.  Those hypotheses appear in theorems about the operator.

The low-level theorem in `IntervalNeumannFullKernel.lean` separates the hard identity from a named interchange hypothesis:

```lean
-- ShenWork/PDE/IntervalNeumannFullKernel.lean:126-130
def FullKernelIntegralInterchange (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  (∫ y, (∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
      (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) * f y
        ∂ intervalMeasure 1)
    = unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

and then:

```lean
-- ShenWork/PDE/IntervalNeumannFullKernel.lean:137-145
theorem intervalFullSemigroupOperator_eq_cosineHeatValue
    (t : ℝ) (_ht : 0 < t) (f : ℝ → ℝ) (x : ℝ)
    (_hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hkernel : ∀ y, intervalNeumannFullKernel t x y = ...)
    (hinterchange : FullKernelIntegralInterchange t f x) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

Thus the real question is which files produce `FullKernelIntegralInterchange t f x`.

## Continuous route: automatic but too strong for zero extension

`ShenWork/PDE/IntervalFullKernelInterchange.lean` proves the automatic interchange for continuous real-line inputs:

```lean
-- ShenWork/PDE/IntervalFullKernelInterchange.lean:80-83
/-- **`FullKernelIntegralInterchange` holds** for every continuous `f`. -/
theorem fullKernelIntegralInterchange_holds
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    FullKernelIntegralInterchange t f x
```

The cleaned closed-interval theorem in `IntervalFullKernelSpectralClean.lean` still takes global `Continuous f`:

```lean
-- ShenWork/PDE/IntervalFullKernelSpectralClean.lean:28-33
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

Do not feed this theorem with `f = intervalDomainLift u₀` for positive boundary data; the zero extension is not globally continuous.

## L¹/integrable route

`ShenWork/Paper2/IntervalNeumannHeatGradientL2Bricks.lean` has the L¹ interchange:

```lean
-- lines 20-23
/-- L¹-dominated interchange: `FullKernelIntegralInterchange` for integrable input. -/
theorem fullKernelIntegralInterchange_holds_of_integrable
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Integrable f (intervalMeasure 1)) (x : ℝ) :
    FullKernelIntegralInterchange t f x
```

and the operator identity:

```lean
-- lines 58-66
/-- Operator → cosine model for integrable input on `Ioo 0 1`. -/
theorem operator_eq_cosineModel_of_integrable
    {τ : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ}
    (hf : Integrable f (intervalMeasure 1)) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalFullSemigroupOperator τ f x
      = unitIntervalCosineHeatValue τ (cosineCoeffs f) x :=
  intervalFullSemigroupOperator_eq_cosineHeatValue τ hτ f x hx
    (fun y => intervalNeumannFullKernel_eq_cosineKernel_clean τ hτ x y)
    (fullKernelIntegralInterchange_holds_of_integrable τ hτ f hf x)
```

There is also an alias in `ShenWork/Paper2/IntervalNeumannHeatGradientL2.lean:92-97`:

```lean
theorem operator_eq_cosineModel_of_integrable
    {τ : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ}
    (hf : Integrable f (intervalMeasure 1)) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalFullSemigroupOperator τ f x
      = unitIntervalCosineHeatValue τ (cosineCoeffs f) x :=
  ShenWork.IntervalNHGBricks.operator_eq_cosineModel_of_integrable hτ hf hx
```

This answers the rough-input question: **yes, an L¹ version exists, but only for `x ∈ Ioo 0 1`.**

## From AEStronglyMeasurable + bounded to L¹

The repo has the generic finite-interval integrability helper:

```lean
-- ShenWork/PDE/IntervalDomain.lean:42-49
theorem intervalMeasure_integrable_of_abs_bound
    {L M : ℝ} {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ M) :
    Integrable f (intervalMeasure L)
```

So if you can prove:

```lean
hf_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1)
hf_bound : ∀ y, |intervalDomainLift u₀ y| ≤ M
```

then you get `Integrable (intervalDomainLift u₀) (intervalMeasure 1)`, and then the L¹ identity on `Ioo 0 1`.

For measurability of the zero extension from subtype continuity, there are private lemmas, not a public API:

```lean
-- ShenWork/Paper2/IntervalMildPicard.lean:103-123
private theorem intervalDomainLift_measurable_of_continuous
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    Measurable (intervalDomainLift f)
```

The same lemma is copied as private in `IntervalMildPicardThreshold.lean`:

```lean
-- ShenWork/Paper2/IntervalMildPicardThreshold.lean:31-33
The file-private measurability lemmas of IntervalMildPicard.lean are
copied verbatim (they are `private`, hence not importable).

-- lines 96-116
private theorem intervalDomainLift_measurable_of_continuous
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    Measurable (intervalDomainLift f)
```

Since those lemmas are private, downstream files cannot import them.  You can either reprove the small piecewise-measurable lemma, or route through `intervalDomainConstExtend` when you need global continuity/spectral identity.

## Closed interval `[0,1]`: use subtype-continuity adapter

For your exact target with `x ∈ Icc 0 1`, the best landed theorem is still:

```lean
-- ShenWork/PDE/IntervalSpectralSubtypeAdapter.lean:49-54
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
    {t : ℝ} (ht : 0 < t) {f : intervalDomainPoint → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs (intervalDomainLift f) n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t (intervalDomainLift f) x =
      unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x
```

It uses the constant extension internally:

```lean
-- ShenWork/PDE/IntervalSpectralSubtypeAdapter.lean:62-69
calc intervalFullSemigroupOperator t (intervalDomainLift f) x
    = intervalFullSemigroupOperator t (intervalDomainConstExtend f) x :=
      semigroupOperator_constExtend_eq_lift.symm
  _ = unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainConstExtend f)) x :=
      ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
        ht (constExtend_continuous hf) hM' hx
  _ = unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x := by
      rw [hcoef]
```

## Practical snippets

### Closed interval, continuous subtype datum

```lean
have hheat :
    intervalFullSemigroupOperator s (intervalDomainLift u₀) x =
      unitIntervalCosineHeatValue s (cosineCoeffs (intervalDomainLift u₀)) x :=
  ShenWork.IntervalSpectralSubtypeAdapter
    .intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      hs hu₀_cont hM hx
```

Then convert `unitIntervalCosineHeatValue` to the explicit tsum using the already-found EWA bridge:

```lean
have hsum :
    unitIntervalCosineHeatValue s (cosineCoeffs (intervalDomainLift u₀)) x =
      ∑' k : ℕ,
        (Real.exp (-s * unitIntervalCosineEigenvalue k) *
          cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
  simpa [unitIntervalCosineEigenvalue] using
    (ShenWork.EWA.cosineHeatSynthesis_eq_cosineHeatValue
      (cosineCoeffs (intervalDomainLift u₀)) s x).symm
```

### Interior only, L¹ input

```lean
have hf_int : Integrable (intervalDomainLift u₀) (intervalMeasure 1) := by
  -- e.g. from AEStronglyMeasurable + bounded via intervalMeasure_integrable_of_abs_bound
  ...

have hheat_interior :
    intervalFullSemigroupOperator s (intervalDomainLift u₀) x =
      unitIntervalCosineHeatValue s (cosineCoeffs (intervalDomainLift u₀)) x :=
  ShenWork.IntervalNHGBricks.operator_eq_cosineModel_of_integrable
    hs hf_int hxIoo
```

## Bottom line

For `x ∈ [0,1]`, do **not** try to use an AEStronglyMeasurable/L¹ theorem unless you also prove a boundary-continuity closure theorem.  Use the existing subtype-continuity adapter.  For `x ∈ (0,1)`, the L¹ theorem is already available and only needs `Integrable f (intervalMeasure 1)`.
