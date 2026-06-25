# Q623 / cron1: C²-Neumann ⇒ eigenvalue-weighted cosine-coefficient summability?

## Verdict

I did **not** find a theorem in `Shen_work` proving the reverse direction

```lean
ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) 1)
  + Neumann endpoint data
  ⟹
Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|)
```

Searches for variants of

```text
eigenvalue summable C2
H2 eigenvalue summable
contDiff_two implies eigenvalue summable
closedC2 eigenvalue summable
of_contDiffOn eigenvalue Summable cosineCoeffs
```

turn up only the **forward** APIs and weaker decay APIs, not the desired reverse theorem.

Also, analytically, the proposed reverse is not valid from bare `C²` alone.  The repo's existing C²/weak-H² route gives only quadratic coefficient decay

```text
|a_k| ≤ C / (kπ)^2
```

so

```text
λ_k |a_k| ≲ constant
```

which is not summable.  To get `∑ λ_k |a_k| < ∞`, one needs stronger input, for example a Sobolev/coefficient condition such as `H^σ` with `σ > 5/2`, or a genuinely stronger smoothness/analytic/exponential-decay theorem.

## What the repo **does** have

### 1. Forward direction: eigenvalue-ℓ¹ ⇒ C² cosine series

The eigenvalue-ℓ¹ space file explicitly identifies the membership predicate as the hypothesis consumed by `cosineCoeffSeries_contDiff_two`:

```lean
/-- Eigenvalue-ℓ¹ membership: `Σ_n λ_n |a_n|` converges. -/
def MemEig (a : ℕ → ℝ) : Prop :=
  Summable (fun n => unitIntervalCosineEigenvalue n * |a n|)
```

Location:

- `ShenWork/PDE/EigenvalueL1Space.lean:71-73`

The same file header says this is exactly the hypothesis that the committed `cosineCoeffSeries_contDiff_two` engine consumes to produce a `C²` cosine series:

- `ShenWork/PDE/EigenvalueL1Space.lean:12-19`

So the repo already treats eigenvalue-ℓ¹ as the **input** side of C² construction, not as a consequence of C².

### 2. C²/weak-H² ⇒ quadratic decay, not eigenvalue-ℓ¹

`IntervalMildSourceDecayHelper.lean` has the relevant weak-H²/C² bridge.  It packages closed C² + Neumann data into a weak `H²_N` certificate:

```lean
noncomputable def intervalWeakH2Neumann_of_contDiffOn
    {g : ℝ → ℝ}
    (hgC2 : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv g) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv g) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv g 0 = 0) (hbc1 : deriv g 1 = 0) :
    IntervalWeakH2Neumann g
```

Location:

- `ShenWork/PDE/IntervalMildSourceDecayHelper.lean:76-92`

But the conclusion extracted from weak `H²_N` is only:

```lean
theorem intervalWeakH2Neumann_cosineCoeff_quadratic_decay
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ C / ((k : ℝ) * Real.pi) ^ 2
```

Location:

- `ShenWork/PDE/IntervalMildSourceDecayHelper.lean:190-193`

This is the reverse-ish result present in the repo, and it is strictly weaker than `Summable (λ_k |a_k|)`.

### 3. Closed C² positive slice ⇒ `SourceCoeffQuadraticDecay`

The concrete power-source route similarly produces only quadratic decay:

```lean
def sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hC2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Set.Icc (0 : ℝ) 1))
    (hN0 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : Filter.Tendsto (deriv (intervalDomainLift u))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u x) :
    SourceCoeffQuadraticDecay p u
```

Location:

- `ShenWork/PDE/IntervalCoupledRegularityBootstrap.lean:51-59`

Inside, it builds a weak-H² certificate and then calls `intervalWeakH2Neumann_cosineCoeff_quadratic_decay`:

- `ShenWork/PDE/IntervalCoupledRegularityBootstrap.lean:73-93`

So this is exactly the `C² ⇒ O(k⁻²)` theorem, not `C² ⇒ eigenvalue-ℓ¹`.

### 4. Representation/eigenvalue-summable ⇒ weak-H² for power source

The power-source adapter goes the other way: it assumes eigenvalue summability of a profile representation and then constructs weak-H² for `ν*u^γ`:

```lean
noncomputable def intervalWeakH2Neumann_of_eigenvalue_summable
    {ν γ : ℝ} (hν : 0 < ν) (hγ : 0 < γ)
    {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    IntervalWeakH2Neumann (fun x : ℝ => ν * intervalDomainLift w x ^ γ)
```

Location:

- `ShenWork/PDE/IntervalMildSourceDecayHelper.lean:71-79`

Again: eigenvalue summability is an assumption, not derived from C².

### 5. Stronger available route: `MemHSigma σ`, `σ > 5/2` ⇒ eigenvalue-ℓ¹

The closest positive result to the desired conclusion is in `IntervalCosineSobolevEmbedding.lean`:

```lean
theorem memHSigma_summable_eigenvalue_abs {σ : ℝ} (hσ : 5 / 2 < σ) {b : ℕ → ℝ}
    (hb : MemHSigma σ b) :
    Summable fun n => unitIntervalCosineEigenvalue n * |b n|
```

Location:

- `ShenWork/Paper2/IntervalCosineSobolevEmbedding.lean:111-121`

The file header explains the mechanism: Cauchy–Schwarz/AM–GM gives

```text
Σ λ_n |b_n| ≤ 1/2 Σ (1+λ_n)^σ b_n² + 1/2 Σ λ_n²/(1+λ_n)^σ,
```

and the dual weight is summable exactly for `σ > 5/2`.

Locations:

- `ShenWork/Paper2/IntervalCosineSobolevEmbedding.lean:15-24`
- `ShenWork/Paper2/IntervalCosineSobolevEmbedding.lean:107-121`

This is likely the correct coefficient-space replacement for the invalid `C² ⇒ eigenvalue-ℓ¹` route.

## Consequence for the heat-semigroup resolver-source goal

For

```lean
f x = p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 s) x ^ p.γ
```

at `s > 0`, proving `f` is merely `C²` with Neumann data will only feed the existing quadratic-decay machinery.  It will not discharge

```lean
Summable (fun k => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|)
```

by any theorem I found.

The viable Lean routes are instead:

1. prove a stronger coefficient-space statement, e.g. `MemHSigma σ` for the source coefficients with `σ > 5/2`, then apply `memHSigma_summable_eigenvalue_abs`; or
2. prove the actual heat/analytic/exponential-decay statement directly for the source coefficients of `ν*(S(s)u₀)^γ`; or
3. prove a higher-regularity coefficient-decay theorem strong enough to imply `∑ λ_k |a_k| < ∞`.

The current repo has route (1)'s summability core, but I did not find a completed theorem applying it to the nonlinear resolver source at the level-0 heat semigroup.
