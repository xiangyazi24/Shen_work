# Q1508 (cron3): `cosineCoeffs` normalization and `hu₀_bound` vs sup norm

## Search scope

Searched `xiangyazi24/Shen_work` for:

```text
def cosineCoeffs
def unitIntervalNeumannCosineCoeff
unitIntervalCosineRawCoeff
cosineCoeffs_pos_eq_integral
cosineCoeffs_zero_eq_integral
cosineCoeffs_eq_factor_mul_integral
hu₀_bound M₀ intervalDomainLift u₀
|cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
cosineCoeffs_abs_le_of_continuous_bounded
cosineCoeffs_dist_le_of_sup
BddAbove (Set.range fun x => |u₀ x|)
```

The indexed/default tree searched by the GitHub connector is commit `7db6d8e4b01d279823281613bb824200483faddd` for the relevant hits.

## Short answer

`cosineCoeffs` uses the **normalized Neumann cosine coefficients**:

```text
cosineCoeffs f 0 = ∫₀¹ f(x) dx
cosineCoeffs f k = 2 * ∫₀¹ cos(kπx) * f(x) dx   for k ≥ 1
```

So positive modes carry the factor `2`; the zeroth mode does not.

The hypothesis

```lean
hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
```

is a **uniform coefficient bound**, not a pointwise/sup-norm bound.  It does **not** imply

```lean
∀ x ∈ Icc 0 1, |intervalDomainLift u₀ x| ≤ M₀
```

and the repo does not appear to use it that way in the searched places.

The direction present in the repo is the opposite:

```text
sup bound on f  ==>  coefficient bound on cosineCoeffs f k
```

via `cosineCoeffs_abs_le_of_continuous_bounded` / `cosineCoeffs_dist_le_of_sup`.

A separate sup-norm datum is carried under names like `Msup`, `hubt`, or `BddAbove (Set.range fun x => |u₀ x|)`.  Do not identify `M₀` from `hu₀_bound` with the sup norm unless there is a separate theorem producing that specific `M₀` from a sup bound.

## Exact definitions

### `cosineCoeffs`

File:

```text
ShenWork/PDE/IntervalNeumannFullKernel.lean
```

Definition:

```lean
/-- The cosine coefficients used on the spectral side: the normalized Neumann cosine
coefficients (zeroth mode unscaled, positive modes carrying the factor `2`). -/
def cosineCoeffs (f : ℝ → ℝ) : ℕ → ℝ :=
  fun n => ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
    (fun x => (f x : ℂ)) n
```

The comment is explicit: zeroth mode unscaled, positive modes carry `2`.

### Raw coefficient and normalized coefficient

File:

```text
ShenWork/PDE/HeatKernelGradientEstimates.lean
```

Definitions:

```lean
/-- Raw, unnormalized cosine coefficient on the unit interval. -/
def unitIntervalCosineRawCoeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x

/-- Neumann cosine coefficients normalized for the unnormalized basis
`1, cos(πx), cos(2πx), ...`.  The zeroth mode is unscaled and all positive
cosine modes carry the usual factor `2`. -/
def unitIntervalNeumannCosineCoeff (f : ℝ → ℂ) (n : ℕ) : ℝ :=
  if n = 0 then (unitIntervalCosineRawCoeff f 0).re
  else 2 * (unitIntervalCosineRawCoeff f n).re
```

So the normalization is exactly:

```text
n = 0: raw real integral
n > 0: 2 * raw real integral
```

## Real integral lemmas already in the repo

File:

```text
ShenWork/Paper2/IntervalMildPicardRegularity.lean
```

Zeroth mode:

```lean
/-- The zeroth cosine coefficient equals `∫₀¹ f(x) dx` (no factor of 2). -/
theorem cosineCoeffs_zero_eq_integral (f : ℝ → ℝ) :
    cosineCoeffs f 0 =
      (∫ x in (0 : ℝ)..1, f x) := by
```

Positive modes:

```lean
/-- For a real-valued `f`, the positive-mode cosine coefficient equals
`2 * ∫₀¹ cos(nπx) * f(x) dx`. -/
theorem cosineCoeffs_pos_eq_integral {f : ℝ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    cosineCoeffs f n =
      2 * ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x := by
```

Uniform factor form:

```lean
/-- Uniform formula: `cosineCoeffs f n = c(n) * ∫₀¹ cos(nπx) * f(x) dx`
where `c(0) = 1` and `c(n) = 2` for `n ≥ 1`. -/
theorem cosineCoeffs_eq_factor_mul_integral (f : ℝ → ℝ) (n : ℕ) :
    cosineCoeffs f n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x := by
```

This is the theorem to use whenever a proof needs to unfold the real normalization safely.

## What `hu₀_bound` actually means in the code

In heat-semigroup regularity files, `hu₀_bound` is used as a coefficient bound, e.g.

```lean
theorem heatSemigroup_eigenvalueSq_summable
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k => unitIntervalCosineEigenvalue k ^ 2 *
      |Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k|) := by
```

The proof uses `hu₀_bound k` exactly to dominate the coefficient in the exponentially damped heat trace:

```lean
unitIntervalCosineEigenvalue k ^ 2 *
  (Real.exp (-t * unitIntervalCosineEigenvalue k) *
    |cosineCoeffs (intervalDomainLift u₀) k|)
≤ unitIntervalCosineEigenvalue k ^ 2 *
  (Real.exp (-t * unitIntervalCosineEigenvalue k) * M₀)
```

It does not infer any pointwise bound on `u₀`.

Same pattern in `IntervalPicardIterateRepresentation.lean`:

```lean
theorem hbsum_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ 0 σ k|) :=
  hom_eig_summable (M₁ := M₀) hσ hu₀_bound
```

Again: coefficient heat trace, not pointwise sup.

## Does `|a_k| ≤ M₀` imply `|u₀(x)| ≤ M₀`?

No.

With this normalization, take the simple cosine polynomial on `[0,1]`:

```text
f(x) = M₀ * (1 + cos(πx)),   M₀ > 0.
```

Then:

```text
a₀ = ∫₀¹ M₀(1 + cos πx) dx = M₀,
a₁ = 2∫₀¹ M₀(1 + cos πx) cos πx dx = M₀,
a_k = 0 for k ≥ 2,
```

so `∀ k, |a_k| ≤ M₀`, but

```text
sup_{x∈[0,1]} |f(x)| = f(0) = 2M₀ > M₀.
```

This is even nonnegative.  So the attempted implication fails in exactly the setting used for positive/nonnegative initial data.

## What direction the repo proves/uses instead

### Sup bound implies coefficient bound

The repo uses a coefficient bound from a pointwise bound in several places.  For example, `IntervalPicardLimitBddHcontP.lean` derives a datum-side source coefficient bound from a real sup bound:

```lean
have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |intervalDomainLift u₀ x| ≤ B := by
  intro x hx
  simp only [intervalDomainLift, dif_pos hx]
  exact le_csSup hbdd ⟨⟨x, hx⟩, rfl⟩
...
have := cosineCoeffs_abs_le_of_continuous_bounded hcontSrc hMa_nn hsrcbd k
```

This is the correct direction:

```text
B bounds |profile| on [0,1]
  ⇒ source pointwise bound
  ⇒ coefficient bound, with a factor 2 for positive modes.
```

### Sup-distance controls coefficient-distance

`IntervalPicardLimitCoeffConv.lean` proves the Lipschitz version:

```lean
/-- **The cosine functional is `2`-Lipschitz in the sup norm.**  If `g, h` are
continuous on `[0,1]` and `|g x − h x| ≤ B` there, then
`|cosineCoeffs g k − cosineCoeffs h k| ≤ 2·B`. -/
theorem cosineCoeffs_dist_le_of_sup {g h : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hh : ContinuousOn h (Set.Icc (0 : ℝ) 1))
    {B : ℝ} (hB : 0 ≤ B)
    (hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x - h x| ≤ B) (k : ℕ) :
    |cosineCoeffs g k - cosineCoeffs h k| ≤ 2 * B := by
```

This again goes from sup control to coefficient control, not inverse.

## Separate sup-norm hypotheses / constants

The repo carries sup bounds separately.

### `Msup` / `hubt` in patched source windows

In `IntervalPicardLimitBddProducer.lean`, the per-window bound explicitly takes:

```lean
{Msup : ℝ}
...
(hubt : ∀ σ, 0 < σ → ∀ x ∈ Set.Icc (0 : ℝ) 1,
  intervalDomainLift (u σ) x ≤ Msup)
```

and uses it to form constants like:

```lean
max (2 * B_log p.a p.b p.α Msup G1 G2)
    (Msup * (p.a + p.b * Msup ^ p.α))
```

That is a genuine slice sup bound, separate from coefficient `M₀`.

### Datum sup bound via `BddAbove (range |u₀|)`

In `IntervalPicardLimitBddHcontP.lean`, the datum-side coefficient bound has hypotheses:

```lean
theorem datum_source_coeff_bound (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hcont : Continuous u₀)
    (hbdd : BddAbove (Set.range fun x => |u₀ x|))
    (hpos : ∀ x, x ∈ intervalDomain.inside → 0 < u₀ x) :
    ∀ k, |cosineCoeffs (logisticLifted p u₀) k| ≤ datumBound p u₀ := by
```

The concrete sup constant is:

```lean
noncomputable def datumBound (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℝ :=
  2 * (sSup (Set.range fun x => |u₀ x|)
        * (p.a + p.b * (sSup (Set.range fun x => |u₀ x|)) ^ p.α))
```

Again: this is a separate sup-norm/boundedness assumption, used to produce a coefficient bound for the initial logistic source.  It is not recovered from `hu₀_bound`.

## Practical guidance

If a target needs `|u₀(x)| ≤ M` or `intervalDomainLift u₀ x ≤ M`, do **not** try to use

```lean
hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
```

unless the target only needs a spectral heat-trace coefficient bound after exponential damping.

For pointwise/sup estimates, look for or add one of:

```lean
-- direct pointwise bound
∀ x ∈ Set.Icc (0 : ℝ) 1, |intervalDomainLift u₀ x| ≤ M

-- subtype version
∀ x : intervalDomainPoint, |u₀ x| ≤ M

-- existential boundedness
BddAbove (Set.range fun x : intervalDomainPoint => |u₀ x|)
```

Then use the existing sup-to-coeff direction (`cosineCoeffs_abs_le_of_continuous_bounded` / `cosineCoeffs_dist_le_of_sup`) when a coefficient bound is needed.
