# Q789 (cron2) — boundedWeightJointTerm derivative bound for heatTerm reuse

Static repo inspection only; I did not run a Lean build.

## Search result

The theorem is in:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

Exact theorem name:

```lean
boundedWeightJointTerm_iteratedFDeriv_le
```

I did **not** find it under a name like `norm_iteratedFDeriv_boundedWeightJointTerm_le`; the actual name is the one above.

## Definitions around it

```lean
def boundedWeightJointTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * cosineMode n q.2
```

This is exactly the same separated structure as the heat term:

```lean
heatTerm u₀ n q =
  (Real.exp (-q.1 * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n q.2
```

with coefficient family

```lean
c n t = Real.exp (-t * unitIntervalCosineEigenvalue n) *
  cosineCoeffs (intervalDomainLift u₀) n
```

The theorem’s majorant is:

```lean
def boundedWeightJointMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

where `Bt i n` is the bound for the `i`-th time derivative of the scalar coefficient, and `valueCosWeight (k - i) n` bounds the `(k-i)`-th spatial derivative of `cosineMode n`.

## Exact theorem signature

```lean
theorem boundedWeightJointTerm_iteratedFDeriv_le
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hc : ContDiff ℝ (2 : ℕ∞) (c n)) (hk : (k : ℕ∞) ≤ (2 : ℕ∞))
    (hBt : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) q.1‖ ≤ Bt i n) :
    ‖iteratedFDeriv ℝ k (boundedWeightJointTerm c n) q‖ ≤
      boundedWeightJointMajorant Bt k n := by
  ...
```

## Proof ingredients confirmed

Inside the proof, it first builds the separated `ContDiff` facts:

```lean
have hcj : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => c n q.1) :=
  hc.comp contDiff_fst

have hcos₀ : ContDiff ℝ (2 : ℕ∞) (cosineMode n) := by
  unfold cosineMode; fun_prop

have hcos : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode n q.2) :=
  hcos₀.comp contDiff_snd
```

Then it applies the product Leibniz estimate:

```lean
have hprod := norm_iteratedFDeriv_mul_le hcj hcos q hkTop
```

and rewrites it to the separated summation:

```lean
have hprod' :
    ‖iteratedFDeriv ℝ k (boundedWeightJointTerm c n) q‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun q : ℝ × ℝ => cosineMode n q.2) q‖ := by
  simpa [boundedWeightJointTerm] using hprod
```

The time side is bounded using `norm_iteratedFDeriv_comp_fst_le` plus the supplied coefficient bound `hBt`:

```lean
have htime :
    ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ ≤ Bt i n :=
  (norm_iteratedFDeriv_comp_fst_le hc hiTop q).trans
    (hBt i (le_trans hik hkNat))
```

The cosine/spatial side is bounded using `norm_iteratedFDeriv_comp_snd_le` plus `cosineMode_iteratedFDeriv_bound`:

```lean
have hspace :
    ‖iteratedFDeriv ℝ (k - i)
      (fun q : ℝ × ℝ => cosineMode n q.2) q‖ ≤
      valueCosWeight (k - i) n :=
  (norm_iteratedFDeriv_comp_snd_le hcos₀ hkiTop q).trans
    (cosineMode_iteratedFDeriv_bound n (k - i) q.2 (by omega))
```

Then each Leibniz summand is bounded by:

```lean
(k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

and summing gives `boundedWeightJointMajorant Bt k n`.

## Direct reuse for `heatTerm`

For `heatTerm_iteratedFDeriv_global_bound`, the most direct reuse is:

```lean
private def heatCoeff (u₀ : intervalDomainPoint → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n
```

Then prove the definitional identification:

```lean
have hterm : heatTerm u₀ n =
    ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm
      (fun n t => heatCoeff u₀ n t) n := by
  funext q
  simp [heatTerm, heatCoeff,
    ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm]
```

Use `boundedWeightJointTerm_iteratedFDeriv_le` with

```lean
Bt i n = unitIntervalCosineEigenvalue n ^ i * M₀ *
  Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)
```

provided you have the required scalar coefficient derivative bound:

```lean
∀ i, i ≤ 2 →
  ‖iteratedFDeriv ℝ i (fun t => heatCoeff u₀ n t) q.1‖ ≤ Bt i n
```

That coefficient bound is valid only in the positive-time/cutoff-support branch where

```lean
c / 2 ≤ q.1
```

because otherwise `exp(-q.1 * λ_n)` can grow for negative `q.1`.

## Practical conclusion

The repo already has the exact separated-product machinery needed for the heat term.  The theorem to reuse is:

```lean
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm_iteratedFDeriv_le
```

It packages the result as the finite Leibniz majorant:

```lean
∑ i ∈ Finset.range (k + 1),
  (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

rather than directly as a collapsed `(1 + λ_n)^k` bound.  If the heat file wants the collapsed bound, add a separate finite-sum majorization lemma after applying this theorem.
