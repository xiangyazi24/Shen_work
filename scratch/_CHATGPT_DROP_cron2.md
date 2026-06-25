# Q582 (cron2): level-0 Picard / heat-semigroup spectral bridge

## Executive verdict

Yes: the repo already proves the level-0 spectral bridge on `chatgpt-scratch`, but the theorem is **not** named `picardIter_cosine_representation`.

The main level-0 bridge is:

```lean
ShenWork.IntervalPicardIterateRepresentation.hagree_zero
```

It proves, for `σ > 0`, subtype-continuous initial datum, and bounded initial cosine coefficients:

```lean
Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
  (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
  (Set.Icc (0 : ℝ) 1)
```

and `iterateReprCoeff p u₀ 0 σ k` is definitionally

```lean
Real.exp (-σ * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k
```

So this is exactly the spectral representation of the heat slice `S(σ)(lift u₀)` on `[0,1]`.

The direct semigroup bridge is also present:

```lean
intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
```

which proves

```lean
intervalFullSemigroupOperator t (intervalDomainLift f) x =
  unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x
```

on `[0,1]`, and `heatValue_eq_cosineSeries` rewrites `unitIntervalCosineHeatValue` as the explicit `∑' cosineMode` series.

`IntervalMildPicard.lean` itself mostly defines the Picard iteration and measurability/continuity infrastructure; the spectral representation theorem is in `IntervalPicardIterateRepresentation.lean`, with supporting semigroup identity in `IntervalSpectralSubtypeAdapter.lean` and heat-value series expansion in `IntervalPicardIterateRestart.lean`.

## 1. Level-0 coefficients

`ShenWork/Paper2/IntervalPicardIterateRepresentation.lean:64`

```lean
def iterateReprCoeff (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℕ → ℝ
  | 0,     σ, k => Real.exp (-σ * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
  | n + 1, σ, k => restartIterateCoeff p u₀ n σ k
```

Thus at level `0`, the representation coefficient is exactly the damped heat coefficient.

## 2. Level-0 summability

`ShenWork/Paper2/IntervalPicardIterateRepresentation.lean:74`

```lean
theorem hbsum_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Summable (fun k => (λ_ k) * |iterateReprCoeff p u₀ 0 σ k|)
```

This gives the eigenvalue-weighted summability for the level-0 damped coefficients.

## 3. Main level-0 agreement theorem: `hagree_zero`

`ShenWork/Paper2/IntervalPicardIterateRepresentation.lean:83`

```lean
theorem hagree_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {σ M₀ : ℝ} (hσ : 0 < σ)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
      (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1)
```

Proof route in the file:

```lean
have hlift : intervalDomainLift (picardIter p u₀ 0 σ) x
    = intervalFullSemigroupOperator σ (intervalDomainLift u₀) x := by
  simp only [intervalDomainLift, picardIter, dif_pos hx]

rw [ShenWork.IntervalSpectralSubtypeAdapter.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      hσ hu₀_cont hu₀_bound hx]
rw [heatValue_eq_cosineSeries]
rfl
```

So `hagree_zero` does exactly what you need: it bridges the level-0 Picard slice to the cosine-mode series on `[0,1]`.

## 4. Direct semigroup-to-heat-value identity

`ShenWork/PDE/IntervalSpectralSubtypeAdapter.lean:49`

```lean
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
    {t : ℝ} (ht : 0 < t) {f : intervalDomainPoint → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs (intervalDomainLift f) n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t (intervalDomainLift f) x =
      unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x
```

This is the closed-interval spectral identity with only subtype continuity of `f`, avoiding the false requirement that `intervalDomainLift f` be globally continuous on `ℝ`.

## 5. Heat value to explicit cosine series

`ShenWork/Paper2/IntervalPicardIterateRestart.lean:197`

```lean
theorem heatValue_eq_cosineSeries (t : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    unitIntervalCosineHeatValue t a x
      = ∑' k, (Real.exp (-t * (λ_ k)) * a k) * cosineMode k x
```

Combining this with the semigroup identity gives the direct statement:

```lean
intervalFullSemigroupOperator σ (intervalDomainLift u₀) x =
  ∑' k,
    (Real.exp (-σ * unitIntervalCosineEigenvalue k)
      * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x
```

for `0 < σ`, `x ∈ Icc 0 1`, assuming `Continuous u₀` and the coefficient bound.

## 6. Related theorem: `heatSlice_profile_eq_heatValue`

`ShenWork/Paper2/IntervalPicardLevel0SourceTimeC1On.lean:88`

```lean
theorem heatSlice_profile_eq_heatValue
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {σ x M₀ : ℝ} (hσ : 0 < σ) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (picardIter p u₀ 0 σ) x =
      unitIntervalCosineHeatValue σ (heatCoeff u₀) x
```

This is the same bridge but stops at `unitIntervalCosineHeatValue`; use `heatValue_eq_cosineSeries` to get the explicit `∑' cosineMode` form.

The same file also proves the level-0 coefficient identity:

`ShenWork/Paper2/IntervalPicardLevel0SourceTimeC1On.lean:102`

```lean
theorem heatSliceCoeff_eq_damped
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {σ M₀ : ℝ} (hσ : 0 < σ) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀) (k : ℕ) :
    cosineCoeffs (intervalDomainLift (picardIter p u₀ 0 σ)) k =
      Real.exp (-σ * (λ_ k)) * heatCoeff u₀ k
```

## 7. Related theorem for successor levels, not level 0

`ShenWork/Paper2/IntervalPicardIterateRestart.lean:293`

```lean
theorem iterate_lift_eq_cosineSeries
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceTimeC1
      (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k))
    {t : ℝ} (ht : 0 < t)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (logisticLifted p (picardIter p u₀ n s)))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (picardIter p u₀ (n+1) t) x
      = ∑' k, iterateCoeff p u₀ n t k * cosineMode k x
```

This is for `picardIter … (n+1)`, not the base `0` case.  It combines homogeneous heat plus Duhamel source terms.  For level 0, `hagree_zero` is the cleaner theorem.

## 8. Tower use confirms `hagree_zero` is the live base bridge

`ShenWork/Paper2/IntervalPicardSourceTower.lean:527` uses `hbsum_zero` and `hagree_zero` to build the base tower carrier:

```lean
def tower_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {M A₂ T : ℝ}
    (H : TowerInputs p u₀ M A₂ T) :
    TowerLevel p u₀ M A₂ T 0 :=
  ...
  { hrepr_sum := fun _ hσ _ => hbsum_zero p u₀ hσ H.hu₀_bound
    hrepr_agree := fun _ hσ _ => hagree_zero p u₀ hσ H.hu₀_cont H.hu₀_bound
    ... }
```

So `hagree_zero` is not stale; it is wired into the current tower base case.

## 9. Search/name conclusions

Search results on/around `chatgpt-scratch`:

- `picardIter_cosine_representation`: no exact theorem name found.
- `hagree_zero`: found and active in `IntervalPicardIterateRepresentation.lean`; used by `tower_zero`.
- `iterate_lift_eq`: found `iterate_lift_eq_cosineSeries`, but it is the successor-level theorem for `n+1`.
- `level0.*agree`: no better exact level-0 theorem name found on branch; `IntervalConjugateLevel0BFormSourceOn.lean` appears in indexed/default search results but is 404 on `chatgpt-scratch`.
- `semigroup.*agree`: the relevant branch theorem is `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont`, plus `heatValue_eq_cosineSeries`.

## Practical use

For the base level, use:

```lean
have hagree : Set.EqOn (intervalDomainLift (picardIter p u₀ 0 σ))
    (fun x => ∑' k, iterateReprCoeff p u₀ 0 σ k * cosineMode k x)
    (Set.Icc (0 : ℝ) 1) :=
  ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u₀ hσ hu₀_cont hu₀_bound
```

If you need the statement directly in terms of `intervalFullSemigroupOperator`, combine:

```lean
intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
heatValue_eq_cosineSeries
```

or copy the two-line proof pattern from `hagree_zero`.