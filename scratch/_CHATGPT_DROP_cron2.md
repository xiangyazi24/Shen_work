# Q661 (cron2): resolver nonnegativity / `1 + R > 0`

Static repo inspection only; I did not run a Lean build.  I inspected the current default branch via the GitHub connector and wrote this report to `chatgpt-scratch`.

## Executive verdict

Yes: the repo **does prove `R(u) ≥ 0` on `[0,1]`**, but not by coefficient positivity.  The landed proof is the heat-Laplace / positivity-preserving semigroup route in

```text
ShenWork/PDE/IntervalResolverPositivity.lean
```

The main closed-domain theorem is:

```lean
theorem intervalNeumannResolverR_nonneg_of_nonneg_source {p : CM2Params}
    {u : intervalDomainPoint → ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    (xp : intervalDomainPoint) :
    0 ≤ intervalNeumannResolverR p u xp
```

There is also an interior version:

```lean
theorem intervalNeumannResolverR_nonneg_interior {p : CM2Params}
    {u : intervalDomainPoint → ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    {xp : intervalDomainPoint} (hx : xp.1 ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ intervalNeumannResolverR p u xp
```

So for the interval-domain resolver, the proof is already there.  From the closed-domain theorem, the denominator target follows immediately:

```lean
have hR : 0 ≤ intervalNeumannResolverR p u xp :=
  intervalNeumannResolverR_nonneg_of_nonneg_source hf_cont hf_nonneg hf_coeff hâ xp
have h1R : 0 < 1 + intervalNeumannResolverR p u xp := by linarith
```

## Important caveat: not “nonnegative coefficients”

Your correction is right: nonnegative cosine coefficients do **not** imply the reconstructed function is nonnegative, and the repo does not try to prove positivity that way.

The landed theorem assumes a **pointwise nonnegative continuous source representative**:

```lean
hf_nonneg : ∀ y, 0 ≤ f y
```

plus the coefficient identification

```lean
hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p u k).re
```

and square-summability of the source coefficients:

```lean
hâ : Summable (fun k => (cosineCoeffs f k) ^ 2)
```

This is the correct maximum-principle/positive-kernel analogue, not a coefficientwise positivity argument.

## How the repo proves it

The file header in `IntervalResolverPositivity.lean` says the route explicitly: use the positivity-preserving heat-Laplace representation

```text
R(u) = ∫₀^∞ e^{-μt} S(t)(ν u^γ) dt
```

implemented through finite truncations and a spectral limit.

Key landed pieces:

```lean
theorem intervalFullSemigroupOperator_nonneg
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x
```

```lean
theorem unitIntervalCosineHeatValue_nonneg_of_continuous
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

```lean
theorem laplaceHeatTrunc_nonneg
    {p : CM2Params} {f : ℝ → ℝ} (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ∫ t in (0:ℝ)..T,
      Real.exp (-p.μ * t) * unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

```lean
theorem laplaceHeatTrunc_tendsto
    {p : CM2Params} {â : ℕ → ℝ}
    (hâ : Summable (fun n => (â n) ^ 2)) (x : ℝ) :
    Filter.Tendsto
      (fun T => ∫ t in (0:ℝ)..T,
        Real.exp (-p.μ * t) * unitIntervalCosineHeatValue t â x)
      Filter.atTop
      (nhds (∑' k, â k * unitIntervalCosineMode k x
        / (p.μ + unitIntervalCosineEigenvalue k)))
```

The theorem `intervalNeumannResolverR_nonneg_interior` reconstructs `R(u)` as this spectral target and passes nonnegativity to the limit via closedness of `Ici 0`.  The closed-domain theorem extends from `(0,1)` to `[0,1]` by continuity of the reconstructed resolver cosine series.

## Strict positivity is also present

If you want a positive lower bound rather than merely `R ≥ 0`, there is a stronger file:

```text
ShenWork/Paper2/IntervalDomainResolverStrictPos.lean
```

It proves:

```lean
theorem intervalNeumannResolverR_ge_of_source_ge {p : CM2Params}
    {u : intervalDomainPoint → ℝ} {f : ℝ → ℝ} {c₀ : ℝ}
    (hf_cont : Continuous f) (hf_ge : ∀ y, c₀ ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    (hĝ : Summable (fun k => (cosineCoeffs (fun y => f y - c₀) k) ^ 2))
    (xp : intervalDomainPoint) :
    c₀ / p.μ ≤ intervalNeumannResolverR p u xp
```

and then:

```lean
theorem intervalNeumannResolverR_pos_of_source_ge {p : CM2Params}
    {u : intervalDomainPoint → ℝ} {f : ℝ → ℝ} {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hf_cont : Continuous f) (hf_ge : ∀ y, c₀ ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    (hĝ : Summable (fun k => (cosineCoeffs (fun y => f y - c₀) k) ^ 2))
    (xp : intervalDomainPoint) :
    0 < intervalNeumannResolverR p u xp
```

The most directly usable representation-based strict theorem is:

```lean
theorem resolverR_pos_of_representation (p : CM2Params)
    {u : intervalDomainPoint → ℝ} {cs : ℝ → ℝ} {m M : ℝ}
    (hcs_cont : Continuous cs)
    (hagree : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u x = cs x)
    (hm_pos : 0 < m)
    (hcs_lb : ∀ x ∈ Set.Icc (0:ℝ) 1, m ≤ cs x)
    (hcs_ub : ∀ x ∈ Set.Icc (0:ℝ) 1, cs x ≤ M)
    (hsrc_coeff : ∀ k, cosineCoeffs (fun x => p.ν * intervalDomainLift u x ^ p.γ) k
        = (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k =>
        (cosineCoeffs (fun x => p.ν * intervalDomainLift u x ^ p.γ) k) ^ 2))
    (hĝ : Summable (fun k =>
        (cosineCoeffs (fun x => p.ν * intervalDomainLift u x ^ p.γ - p.ν * m ^ p.γ) k) ^ 2))
    (xp : intervalDomainPoint) :
    0 < intervalNeumannResolverR p u xp
```

This is stronger than needed for `0 < 1 + R`, but useful if your source has a positive lower floor.

## Relation to `intervalResolverLiftR p u x` on all `x : ℝ`

The theorem above is for:

```lean
intervalNeumannResolverR p u xp
```

where

```lean
xp : intervalDomainPoint  -- i.e. x ∈ [0,1]
```

Your target mentions the ambient lifted series:

```lean
intervalResolverLiftR p u x
```

from `ShenWork/Paper2/IntervalResolverHighRegularity.lean`:

```lean
def intervalResolverLiftR (p : CM2Params) (u : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k x
```

That file states in the docstring that this agrees with `intervalNeumannResolverR` on `[0,1]`, but I did **not** find a named theorem packaging that agreement.  It does provide symmetry/periodicity lemmas:

```lean
theorem intervalResolverLiftR_even
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (-x) = intervalResolverLiftR p u x

theorem intervalResolverLiftR_reflect_one
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (2 - x) = intervalResolverLiftR p u x

theorem intervalResolverLiftR_periodic
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (x + 2) = intervalResolverLiftR p u x
```

So: the repo proves `R(u) ≥ 0` on `[0,1]`, and the lift is even/periodic, but I did **not** find a ready-made theorem

```lean
∀ x : ℝ, 0 ≤ intervalResolverLiftR p u x
```

nor a ready-made theorem

```lean
∀ x : ℝ, 0 < 1 + intervalResolverLiftR p u x
```

To get the all-real lifted version, likely add two thin bridge lemmas:

1. agreement on `[0,1]`:

```lean
lemma intervalResolverLiftR_eq_intervalNeumannResolverR_on_Icc
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalResolverLiftR p u x = intervalNeumannResolverR p u ⟨x, hx⟩ := by
  -- unfold both; `cosineMode` vs `unitIntervalCosineMode` should be definitional/`rfl`-level
```

2. reduce arbitrary `x : ℝ` to a representative in `[0,1]` using period `2` and reflection about `1`, then apply the closed-domain nonnegativity theorem.

For the immediate interval-domain denominator, however, no all-real lift theorem is needed:

```lean
have hR : 0 ≤ intervalNeumannResolverR p u xp :=
  intervalNeumannResolverR_nonneg_of_nonneg_source hf_cont hf_nonneg hf_coeff hâ xp
have hden : 0 < 1 + intervalNeumannResolverR p u xp := by linarith
```

## Search-result summary

Requested searches:

```text
resolverR_nonneg
intervalNeumannResolverR_nonneg
resolver_pos
resolver_ge_zero
```

Findings:

- `resolverR_nonneg` / `intervalNeumannResolverR_nonneg` lead to `ShenWork/PDE/IntervalResolverPositivity.lean` and its theorems `intervalNeumannResolverR_nonneg_interior` / `intervalNeumannResolverR_nonneg_of_nonneg_source`.
- `resolver_pos` / `resolver_ge_zero` did not return exact theorem-name hits, but the strict lower-bound file is `ShenWork/Paper2/IntervalDomainResolverStrictPos.lean` with `intervalNeumannResolverR_ge_of_source_ge`, `intervalNeumannResolverR_pos_of_source_ge`, and `resolverR_pos_of_representation`.
