# Q620 (cron2): eigenvalue-weighted summability for `u^γ`

Static repo inspection only; I did not run a Lean build.

## Verdict

I did **not** find a repo theorem of the requested shape:

```lean
-- schematic target, not found
(Summable (fun k => unitIntervalCosineEigenvalue k * |cosineCoeffs u k|)) ->
  Summable (fun k => unitIntervalCosineEigenvalue k *
    |cosineCoeffs (fun x => u x ^ γ) k|)
```

Nor did I find a theorem under the requested search names:

```text
power_summable
rpow_summable
source_eigenvalue
u_gamma_summable
```

The repo has several nearby pieces, but they stop short of this exact eigenvalue-weighted summability closure for the nonlinear power source.

## What exists

### 1. The exact eigenvalue-`ℓ¹` predicate exists

`ShenWork/PDE/EigenvalueL1Space.lean` defines:

```lean
def MemEig (a : ℕ → ℝ) : Prop :=
  Summable (fun n => unitIntervalCosineEigenvalue n * |a n|)
```

The nearby closure lemmas I found are linear only:

```lean
memEig_zero
memEig_add
memEig_neg
memEig_smul
```

I did **not** find `memEig_mul`, `memEig_rpow`, `memEig_power`, or a nonlinear functional-calculus theorem for `MemEig`.

### 2. `intervalResolverLiftR_contDiff_four` needs exactly source eigenvalue-`ℓ¹`

`ShenWork/Paper2/IntervalResolverHighRegularity.lean` has the desired high-regularity consumer:

```lean
theorem intervalResolverLiftR_contDiff_four
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 4 (intervalResolverLiftR p u)
```

The previous lemma is:

```lean
theorem resolverCoeff_eigenSq_summable_of_sourceEigenL1
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        (unitIntervalCosineEigenvalue k *
          |(intervalNeumannResolverCoeff p u k).re|))
```

So the missing input is exactly:

```lean
Summable (fun k => unitIntervalCosineEigenvalue k *
  |(intervalNeumannResolverSourceCoeff p u k).re|)
```

and `resolverSourceCoeff_re_eq_cosineCoeffs` identifies this real part with

```lean
cosineCoeffs (fun x => p.ν * intervalDomainLift u x ^ p.γ) k
```

### 3. The repo has weak-`H²` / quadratic decay for `u^γ`, not eigenvalue-`ℓ¹`

The main nearby theorem is in `ShenWork/PDE/IntervalMildSourceDecayHelper.lean`:

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

Then the generic weak-`H²` theorem gives only:

```lean
∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
  |cosineCoeffs f k| ≤ C / ((k : ℝ) * Real.pi) ^ 2
```

This is **not** enough for eigenvalue-weighted summability: multiplying by
`λ_k = ((k : ℝ) * Real.pi)^2` leaves only a uniform constant bound, not a summable tail.

### 4. `IntervalResolverPowerDecay.lean` produces the R-Hvsrc-1 quadratic envelope

`ShenWork/Paper2/IntervalResolverPowerDecay.lean` is explicitly about:

```text
R-Hvsrc-1: window-uniform quadratic decay for the power source ν·u^γ
```

The key producer is:

```lean
theorem powerSource_window_uniform_decay
    ...
    (hbsum : ∀ σ ∈ Set.Icc c' d',
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    ... :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ σ ∈ Set.Icc c' d', ∀ k : ℕ, 1 ≤ k →
        |cosineCoeffs (fun x => ν * intervalDomainLift (w σ) x ^ γ) k|
          ≤ C / ((k : ℝ) * Real.pi) ^ 2) ∧
      (∀ σ ∈ Set.Icc c' d',
        |cosineCoeffs (fun x => ν * intervalDomainLift (w σ) x ^ γ) 0| ≤ C)
```

This is very close semantically, but it deliberately produces a **quadratic coefficient decay** package, not an eigenvalue-weighted summability package.  It is the right input for the existing weak-`H²`/Duhamel-source machinery, but not for `intervalResolverLiftR_contDiff_four`.

### 5. The clamped resolver-source witness consumes quadratic decay, not source eigenvalue-`ℓ¹`

`ShenWork/Paper2/IntervalResolverSourceClampedWitness.lean` consumes:

```lean
hdecay : ∀ σ ∈ Set.Icc c' d', ∀ k : ℕ, 1 ≤ k →
  |cosineCoeffs (fun x => p.ν * intervalDomainLift (w σ) x ^ p.γ) k|
    ≤ C / ((k : ℝ) * Real.pi) ^ 2
ha0 : ∀ σ ∈ Set.Icc c' d',
  |cosineCoeffs (fun x => p.ν * intervalDomainLift (w σ) x ^ p.γ) 0| ≤ C
```

Similarly, `IntervalDomainLogisticWeakH2Adapter.powerSource_duhamelSourceTimeC1_of_representation` consumes the weak-`H²` adapter plus carried `hdecay`/`ha0`.  Again: it is quadratic-decay infrastructure, not the requested eigenvalue-summability closure.

### 6. EWA/Wiener side has a power functional calculus, but not the interval `cosineCoeffs` theorem

The closest nonlinear functional-calculus result is in `ShenWork/Wiener/EWA/WienerLevy.lean` and `ShenWork/Wiener/EWA/Flux.lean`:

```lean
theorem realPow_eval_EWA :
  ∃ F : EWA T 1, ∀ τ x,
    evalST τ x (incl F) = ((evalST τ x (incl f)).re ^ γ : ℝ)
```

and the concrete wrapper:

```lean
def realPowEWA (f : EWA T 1) (γ : ℝ) : EWA T 1 :=
  f ^ (Nat.floor γ + 1) * FnegEWA f ((Nat.floor γ + 1 : ℝ) - γ)
```

Then `vFieldEWA` resolves `ν·u^γ` inside EWA:

```lean
def vFieldEWA (μ ν γ : ℝ) (hμ : 0 < μ) (u : EWA T 1) : EWA T 3 :=
  GWA.gResolver μ hμ ((ν : ℂ) • realPowEWA u γ)
```

This is the conceptual weighted-Wiener/power route, but I did not find a bridge theorem saying that a real interval profile with `MemEig (cosineCoeffs u)` implies `MemEig (cosineCoeffs (u^γ))` via `realPowEWA`.

## Bottom line for `intervalResolverLiftR_contDiff_four`

`intervalResolverLiftR_contDiff_four` wants source eigenvalue-`ℓ¹`:

```lean
Summable (fun k => λ_k * |cosineCoeffs (ν * u^γ) k|)
```

The current interval-side power-source infrastructure gives only:

```lean
|cosineCoeffs (ν * u^γ) k| ≤ C / λ_k
```

for `k ≥ 1`, plus a zeroth-mode bound.  That is enough for weak-`H²` / quadratic decay consumers, but it does **not** imply `∑ λ_k |coeff_k| < ∞`.

So the answer is: **No, not currently as a direct repo theorem.**  The missing lemma is a real gap if the plan is to feed `intervalResolverLiftR_contDiff_four` from an input assumption `∑ λ_k |û_k| < ∞`.

## Suggested theorem to add

A useful target would be something like:

```lean
theorem powerSource_memEig_of_memEig
    {ν γ : ℝ} (hν : 0 < ν) (hγ : 0 < γ)
    {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    Summable (fun k => unitIntervalCosineEigenvalue k *
      |cosineCoeffs (fun x => ν * intervalDomainLift w x ^ γ) k|)
```

But the existing weak-`H²` proof will not prove this; it loses exactly one summability order.  A plausible route is to use a weighted-Wiener algebra / functional-calculus argument: show `MemEig` is closed under positive real powers, with a coefficient bridge back to interval `cosineCoeffs`.  The EWA `realPowEWA` machinery suggests this is mathematically aligned with existing code, but the direct interval `MemEig` closure theorem does not appear to be present.

Alternative route: prove stronger regularity of `ν·u^γ` (for example `C⁴`/higher Neumann with summable top derivative coefficients) and extract eigenvalue-`ℓ¹`; the repo has higher-tail infrastructure such as `IntervalEigenCubeSummability.lean`, but that route requires much stronger `C⁸`-style source data and is not the requested implication from only `∑ λ_k |û_k| < ∞`.
