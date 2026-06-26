# Q740 (cron2): Level0 heat nonnegativity / resolver floor for sub-sorry 3E

Static repo inspection only; I did not run a Lean build.

## Executive verdict

The target as stated

```lean
∀ x ∈ Ioo 0 1, ∀ s ∈ Metric.ball τ 1,
  0 < 1 + intervalDomainLift
    (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s) x
```

is **not safely dischargeable from the landed positive-time heat/resolver lemmas unless the ball is known to stay in positive time**.

The reason: `conjugatePicardIter p u₀ 0 s` is **not** piecewise `u₀` at `s = 0`, nor is it clamped to `u₀`/zero by the Picard definition.  It is definitionally the full Neumann heat propagator for every real `s`:

```lean
conjugatePicardIter p u₀ 0 s x
= intervalFullSemigroupOperator s (intervalDomainLift u₀) x.1
```

The landed positivity lemmas for the heat propagator require `0 < s`.  There is also an explicit repo warning/theorem that the concrete propagator at `s = 0` is **not** the identity: `intervalFullSemigroupOperator 0 f x = 0` for every `f` and `x`.

So if sub-sorry 3E is using `Metric.ball τ 1`, the proof needs a hypothesis like `1 < τ` or should choose a smaller radius, e.g. `δ := τ / 2` when `0 < τ`, so that `s ∈ Metric.ball τ δ` implies `0 < s`.  This matches the positive-time nature of the heat and resolver positivity infrastructure.

## Question 1: what is `conjugatePicardIter p u₀ 0 s` for `s ≤ 0`?

Definition is in:

```text
ShenWork/Paper2/IntervalConjugatePicard.lean
```

The relevant lines are:

```lean
/-- B-form Picard iteration:
`u₀(t,x) = S(t)u₀(x)`, `u_{n+1} = Φᴮ(u_n)`. -/
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x
```

So level 0 has **no conditional branch** for `t = 0` or `t < 0`.  It is just `intervalFullSemigroupOperator t (intervalDomainLift u₀)` at all real times.

The full semigroup operator is defined in:

```text
ShenWork/PDE/IntervalNeumannFullKernel.lean
```

as:

```lean
def intervalFullSemigroupOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1
```

and the kernel is built from the real-line heat kernel:

```lean
def intervalNeumannFullKernel (t x y : ℝ) : ℝ :=
  ∑' k : ℤ, (heatKernel t (x - y + 2 * k) + heatKernel t (x + y + 2 * k))
```

Thus, at `s = 0`, the definition does **not** give `u₀`.  The repo has an explicit negative/degeneracy result:

```text
ShenWork/PDE/IntervalSemigroupAtZero.lean
```

It states:

```lean
theorem intervalFullSemigroupOperator_zero (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator 0 f x = 0
```

The file comments say the intended `S 0 = id` value statement is false for the concrete definition: `heatKernel 0 x = 0`, hence `intervalNeumannFullKernel 0 x y = 0`, hence the propagator value is `0` for every `f` and `x`.

For `s < 0`, I found no special branch and no named theorem simplifying `intervalFullSemigroupOperator s f x`.  The positivity infrastructure I found is all stated for `0 < s`, so negative times should be avoided in this sub-sorry.

## Question 2: does heat level 0 satisfy `u(s) ≥ 0` for all `s`, including `s ≤ 0`?

What is landed:

### Positive time

There is a full Neumann propagator positivity theorem in:

```text
ShenWork/PDE/IntervalResolverPositivity.lean
```

```lean
theorem intervalFullSemigroupOperator_nonneg {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x
```

There is also the weaker-on-support variant in:

```text
ShenWork/PDE/IntervalFullKernelLowerBound.lean
```

```lean
theorem intervalFullSemigroupOperator_nonneg_of_nonneg_on_Icc {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x
```

For strictly positive initial data, there is a stronger positive-time theorem in:

```text
ShenWork/Paper2/IntervalBFormNegPartStrictPosBarrier.lean
```

```lean
theorem intervalFullSemigroupOperator_pos_of_positiveInitialDatum
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < intervalFullSemigroupOperator t (intervalDomainLift u₀) x
```

This theorem is exactly what `IntervalConjugateLevel0BFormSourceOn.lean` uses to prove heat-level positivity on positive windows:

```lean
theorem level0_heat_pos_of_data ... :
    ∀ σ ∈ Icc c _D.T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x := by
  ...
  exact ShenWork.Paper2.BFormPositiveDatumNegPart.intervalFullSemigroupOperator_pos_of_positiveInitialDatum
    hu₀ hσpos x
```

### At `s = 0`

The concrete full semigroup is zero at `s = 0`:

```lean
intervalFullSemigroupOperator 0 f x = 0
```

so the level-0 iterate at `s = 0` is not `u₀`; it is zero pointwise after unfolding the semigroup operator.  That is nonnegative, but it is a degenerate artifact of the concrete `heatKernel 0` definition, not the mathematical identity `S(0)=Id`.

### Negative time

I found no theorem proving `0 ≤ intervalFullSemigroupOperator s (intervalDomainLift u₀) x` for `s < 0`, nor a theorem simplifying it to zero.  Existing heat-kernel and full-kernel positivity lemmas require `0 < t`.

Therefore, for sub-sorry 3E, the safe proof route is to ensure all `s` in the slab are positive.

## Resolver positivity connection

The resolver positivity theorem you mention exists in:

```text
ShenWork/PDE/IntervalResolverPositivity.lean
```

The closed-domain theorem is:

```lean
theorem intervalNeumannResolverR_nonneg_of_nonneg_source {p : CM2Params}
    {u : intervalDomainPoint → ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    (xp : intervalDomainPoint) :
    0 ≤ intervalNeumannResolverR p u xp
```

So to prove

```lean
0 < 1 + intervalDomainLift
  (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s) x
```

on `x ∈ Ioo 0 1`, the intended route is:

1. use positive-time heat positivity to show
   ```lean
   0 ≤ conjugatePicardIter p u₀ 0 s y
   ```
   for `0 < s`;
2. infer the resolver source `ν · u^γ` is nonnegative;
3. apply `intervalNeumannResolverR_nonneg_of_nonneg_source`;
4. rewrite `coupledChemicalConcentration p u s` to the interval resolver;
5. conclude `0 < 1 + v` from `0 ≤ v`.

This route is valid on positive-time slabs.  It is not available as-is on a ball that may include `s ≤ 0`.

## Question 3: existing heat/nonnegativity infrastructure found

Searches run included:

```text
nonneg heat
heat nonneg
conjugatePicardIter nonneg
intervalFullSemigroupOperator_nonneg
intervalFullSemigroupOperator_pos_of_positiveInitialDatum
intervalNeumannResolverR_nonneg_of_nonneg_source
```

Relevant landed facts:

### `HeatSemigroup.lean`

```lean
lemma heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
  0 ≤ heatKernel t x
```

```lean
lemma heatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
  0 < heatKernel t x
```

Again, both require `0 < t`.

### `IntervalResolverPositivity.lean`

```lean
theorem intervalFullSemigroupOperator_nonneg {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x
```

```lean
theorem intervalNeumannResolverR_nonneg_of_nonneg_source ... :
    0 ≤ intervalNeumannResolverR p u xp
```

### `IntervalFullKernelLowerBound.lean`

```lean
theorem intervalFullSemigroupOperator_nonneg_of_nonneg_on_Icc {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x
```

```lean
theorem intervalFullSemigroupOperator_lower_bound {t : ℝ} (ht : 0 < t) ... :
    c ≤ intervalFullSemigroupOperator t f x
```

### `IntervalBFormNegPartStrictPosBarrier.lean`

```lean
theorem intervalFullSemigroupOperator_pos_of_nonneg_nonzero
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
    (hf_pos_somewhere : ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < f y₀)
    (x : ℝ) :
    0 < intervalFullSemigroupOperator t f x
```

```lean
theorem intervalFullSemigroupOperator_pos_of_positiveInitialDatum
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < intervalFullSemigroupOperator t (intervalDomainLift u₀) x
```

### `IntervalConjugatePicard.lean`

The general Picard iterate nonnegativity theorem exists, but it is also on the positive horizon:

```lean
theorem conjugatePicardIter_ball ... :
  ... ∧
  (∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    0 ≤ conjugatePicardIter p u₀ n t x) ∧
  ...
```

### `IntervalConjugateLevel0BFormSourceOn.lean`

For level 0, the file has a positive-window extraction:

```lean
theorem level0_heat_pos_of_data ... :
  ∀ σ ∈ Icc c _D.T, ∀ x ∈ Icc (0 : ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x
```

This uses `0 < c` to derive `0 < σ`.

## Bottom line for sub-sorry 3E

The currently stated radius `Metric.ball τ 1` is the suspicious part.  To use existing heat/resolver positivity infrastructure, make the slab positive-time:

```lean
∃ δ > 0, ∀ s ∈ Metric.ball τ δ, 0 < s
```

usually with:

```lean
δ := τ / 2
```

when `0 < τ`.

Then use positive-time heat positivity + resolver positivity.  If the structure forces `δ = 1` for arbitrary `τ`, then the goal is too strong for the landed infrastructure and may be false/unsupported whenever the ball crosses `s ≤ 0`.
