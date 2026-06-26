# Q665 / cron1: exponential decay ⇒ `MemHSigma`?

## Verdict

I did **not** find a generic theorem of the form

```lean
(∀ k, |a k| ≤ C * Real.exp (-α * (k : ℝ)^2)) → 0 < α →
  MemHSigma σ a
```

nor a theorem of the cleaner eigenvalue form

```lean
(∀ k, |a k| ≤ C * Real.exp (-ε * unitIntervalCosineEigenvalue k)) → 0 < ε →
  MemHSigma σ a
```

for arbitrary real `σ`.

The repo does have many **fixed polynomial-weight heat-tail summability lemmas** and heat-factor adapters, but I did not find a reusable bridge named/typed as exponential decay ⇒ `MemHSigma`.

Searches checked included:

```text
MemHSigma exp
exponential decay MemHSigma
exp(-α k²) MemHSigma
exp_summable MemHSigma
MemHSigma heat
heatCoeff MemHSigma
dampedCoeff MemHSigma
MemHSigma of bound
MemHSigma_summable
mul_exp_summable
summable_pow_mul_exp_neg_nat_mul
```

## Relevant definitions

`MemHSigma` is defined in `ShenWork/Paper2/IntervalHSigmaScale.lean`:

```lean
/-- Membership in the fractional cosine `H^σ`: the `H^σ` energy series is
summable (i.e. converges). -/
def MemHSigma (σ : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable fun k : ℕ => (1 + lam k) ^ σ * (a k) ^ 2
```

Location:

- `ShenWork/Paper2/IntervalHSigmaScale.lean:36-39`

The theorem you found is indeed the positive route from `MemHSigma` to eigenvalue-`ℓ¹`:

```lean
theorem memHSigma_summable_eigenvalue_abs {σ : ℝ} (hσ : 5 / 2 < σ) {b : ℕ → ℝ}
    (hb : MemHSigma σ b) :
    Summable fun n => unitIntervalCosineEigenvalue n * |b n|
```

Location:

- `ShenWork/Paper2/IntervalCosineSobolevEmbedding.lean:111-121`

## What exists instead: fixed heat-tail summability lemmas

### `λ e^{-τλ}`

`ShenWork/Paper2/ChemMildC1etaComm.lean` proves:

```lean
theorem eigenvalue_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * Real.exp (-τ * unitIntervalCosineEigenvalue n))
```

and uses it for bounded damped coefficients:

```lean
theorem dampedCoeff_eigenvalue_summable {σ : ℝ} (hσ : 0 < σ) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineEigenvalue n
      * |Real.exp (-σ * unitIntervalCosineEigenvalue n) * a n|)
```

Locations:

- `eigenvalue_mul_exp_summable`: `ShenWork/Paper2/ChemMildC1etaComm.lean:65-87`
- `dampedCoeff_eigenvalue_summable`: `ShenWork/Paper2/ChemMildC1etaComm.lean:88-110`

### `λ² e^{-τλ}` and `λ³ e^{-τλ}`

`ShenWork/PDE/IntervalResolverSpectralTimeC2.lean` proves:

```lean
theorem eigenvalue_sq_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)))
```

and

```lean
theorem eigenvalue_cube_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            Real.exp (-τ * unitIntervalCosineEigenvalue n))))
```

Locations:

- `eigenvalue_sq_mul_exp_summable`: `ShenWork/PDE/IntervalResolverSpectralTimeC2.lean:59-106`
- `eigenvalue_cube_mul_exp_summable`: `ShenWork/PDE/IntervalResolverSpectralTimeC2.lean:107-158`

### Higher fixed powers, but not a public arbitrary-`σ` bridge

`ShenWork/Paper2/IntervalCD6Tail.lean` has a **private** generic helper:

```lean
private theorem eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m *
        Real.exp (-τ * unitIntervalCosineEigenvalue n))
```

and public wrappers for powers 4 through 7:

```lean
theorem eigenvalue_fourth_mul_exp_summable ...
theorem eigenvalue_fifth_mul_exp_summable ...
theorem eigenvalue_sixth_mul_exp_summable ...
theorem eigenvalue_seventh_mul_exp_summable ...
```

Locations:

- private generic helper: `ShenWork/Paper2/IntervalCD6Tail.lean:17-65`
- public wrappers: `ShenWork/Paper2/IntervalCD6Tail.lean:67-98`

Because the generic helper is `private`, it cannot be imported and used outside that file.  Also, even this helper is for natural powers `λ^m`, not directly for real `σ` and the `MemHSigma` weight `(1 + λ)^σ`.

## Heat semigroup coefficient result exists, but not as `MemHSigma`

`ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` proves raw heat semigroup `λ²` weighted summability:

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

- `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:23-33`

This is useful for C⁴ of the **raw heat profile**, but it is not a `MemHSigma σ` theorem and not for the nonlinear source coefficients of `ν*(S(t)u₀)^γ`.

## Heat-factor source-field adapters exist

The repo also has adapters that consume an explicit heat-factor bound and produce source coefficient-field packages, not `MemHSigma`.

In `ShenWork/Paper2/IntervalBC2H3EResolverAudit.lean`:

```lean
def source_fields_of_heat_factor_bounds
    {a : ℝ → ℕ → ℝ} {src : DuhamelSourceTimeC1 a}
    {eps M Mdot : ℝ} (heps : 0 < eps) (hM : 0 ≤ M)
    (hMdot : 0 ≤ Mdot)
    (hsrc : ∀ s, 0 ≤ s → ∀ n,
      |a s n| ≤ Real.exp (-eps * bc2Lam n) * M)
    (hadot : ∀ s, 0 ≤ s → ∀ n,
      |src.adot s n| ≤
        bc2Lam n * Real.exp (-eps * bc2Lam n) * Mdot) :
    SourceC2CoeffFields src
```

Location:

- `ShenWork/Paper2/IntervalBC2H3EResolverAudit.lean:70-83`

Inside it uses the fixed `λ`, `λ²`, `λ³` heat-tail summability lemmas to build the source/adot eigen and eigen-square envelopes:

- `ShenWork/Paper2/IntervalBC2H3EResolverAudit.lean:84-154`

Similarly, `ShenWork/Paper2/IntervalPicardLimitK1C2Heat.lean` has heat-shifted homogeneous coefficient fields.  It defines:

```lean
def shiftedHeatCoeff (ε : ℝ) (a₀ : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(ε + s) * unitIntervalCosineEigenvalue n) * a₀ n
```

and builds `SourceC2CoeffFields` using positive-time heat smoothing:

```lean
def shiftedHeatCoeff_sourceC2CoeffFields ... :
    SourceC2CoeffFields (shiftedHeatCoeff_timeC1 hε hM ha₀)
```

Locations:

- `shiftedHeatCoeff`: `ShenWork/Paper2/IntervalPicardLimitK1C2Heat.lean:26-28`
- `shiftedHeatCoeff_sourceC2CoeffFields`: `ShenWork/Paper2/IntervalPicardLimitK1C2Heat.lean:151-156`

Again: useful, but not `MemHSigma`.

## Suggested theorem to add

A likely reusable lemma is:

```lean
theorem memHSigma_of_exp_eigenvalue_bound
    {σ α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {a : ℕ → ℝ}
    (ha : ∀ k, |a k| ≤ C * Real.exp (-α * unitIntervalCosineEigenvalue k)) :
    ShenWork.Paper2.HSigmaScale.MemHSigma σ a := by
  -- prove `(1+λ)^σ * a_k^2 ≤ const * λ^m * exp(-(α) * λ_k)`
  -- for some natural `m` dominating `σ`, with the zero/negative-σ cases split.
```

or if the bound is stated in `k²`:

```lean
theorem memHSigma_of_exp_nat_sq_bound
    {σ α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {a : ℕ → ℝ}
    (ha : ∀ k, |a k| ≤ C * Real.exp (-α * (k : ℝ)^2)) :
    ShenWork.Paper2.HSigmaScale.MemHSigma σ a := by
  -- convert `(kπ)^2` and compare to polynomial times exp(-2α k²).
```

Implementation note: the repo already uses Mathlib's

```lean
Real.summable_pow_mul_exp_neg_nat_mul
```

in several heat-tail proofs.  The most reusable local precedent is the private helper in `IntervalCD6Tail.lean`; making that helper public and then adding a real-`σ` comparison lemma to `(1+λ)^σ` would get very close.

## Bottom line for the heat semigroup source

For `ν*(S(s)u₀)^γ`, the mathematical idea is sound, but I found no existing Lean theorem that packages “exponential coefficient decay ⇒ `MemHSigma σ` for all σ.”  Existing repo tools are fixed-polynomial heat-tail summability lemmas and C2/C2Coeff field adapters.  A small new generic lemma should be added before trying to route through `memHSigma_summable_eigenvalue_abs`.
