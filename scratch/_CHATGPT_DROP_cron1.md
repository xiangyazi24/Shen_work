# Q817 / cron1: `hagree_zero` heat-slice agreement

Repo inspected: `xiangyazi24/Shen_work`
Source refs inspected:
- `main` for `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`
- `chatgpt-scratch` for `ShenWork/Paper2/IntervalPicardIterateRepresentation.lean` and the scratch write target
Branch written: `chatgpt-scratch`

## Grep result requested

Command:

```bash
grep -n "hagree_zero\|hagree.*zero\|heatCoeff.*agree" \
  ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean | head -10
```

Current hits are the two `hagree_zero` uses:

```text
206:        exact ShenWork.IntervalPicardIterateRepresentation.hagree_zero
301:            ShenWork.IntervalPicardIterateRepresentation.hagree_zero
```

## First Level0 use: local `hU_agree`

Around the first hit, the file builds the heat cosine representative

```lean
set U_cos := fun x => ∑' k,
  (Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) *
    cosineMode k x with hU_cos_def
```

then proves:

```lean
-- U_cos agrees with intervalDomainLift (conjugatePicardIter p u₀ 0 s) on [0,1]
have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
    intervalDomainLift (conjugatePicardIter p u₀ 0 s) x = U_cos x := by
  intro x hx
  exact ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u₀ hs_pos _hu₀_cont _hu₀_bound hx
```

This is the direct pointwise form you asked for.

## Second Level0 use: `hagree_w : Set.EqOn ...`

Around the second hit, after setting

```lean
set w := conjugatePicardIter p u₀ 0 s
```

the file proves the packaged `EqOn` form:

```lean
have hagree_w : Set.EqOn (intervalDomainLift w)
    (fun x => ∑' k, (Real.exp (-s * unitIntervalCosineEigenvalue k) *
      heatCoeff u₀ k) * cosineMode k x) (Set.Icc (0 : ℝ) 1) :=
  ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u₀ hs_pos _hu₀_cont _hu₀_bound
```

This is probably the cleaner bridge to pass into downstream lemmas.

## Definition/source lemma

The definition is in:

```text
ShenWork/Paper2/IntervalPicardIterateRepresentation.lean
```

The coefficient family is:

```lean
def iterateReprCoeff (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℕ → ℝ
  | 0,     σ, k => Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
  | n + 1, σ, k => restartIterateCoeff p u₀ n σ k
```

The agreement lemma is:

```lean
theorem hagree_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  ...
```

Because level 0 of `conjugatePicardIter` and `picardIter` are both the same heat semigroup slice, the Level0 file can use this lemma directly for `conjugatePicardIter p u₀ 0 s`.

## `heatCoeff` alignment

`heatCoeff` is just the initial cosine-coefficient family:

```lean
abbrev heatCoeff (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ :=
  cosineCoeffs (intervalDomainLift u₀)
```

So the RHS in `hagree_zero`

```lean
∑' k, iterateReprCoeff p u₀ 0 s k * cosineMode k x
```

should align with the Level0 heat-series RHS

```lean
∑' k, (Real.exp (-s * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) * cosineMode k x
```

by simplification with:

```lean
simp [ShenWork.IntervalPicardIterateRepresentation.iterateReprCoeff,
      ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff]
```

(or equivalent local opens/simpa).