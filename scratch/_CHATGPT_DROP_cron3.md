# Q1556 (cron3): hypothesis chain for `cutoffResolverTerm_contDiff_two`

## Short answer

Yes.  In the current `ShenWork/Paper2/IntervalHeatResolverJointC2.lean`, the proved direct-route theorem

```lean
theorem cutoffResolverTerm_contDiff_two
```

**does require `hfloor`** in its signature.

The dependency is not accidental.  The per-term `C²` proof goes through

```text
cutoffResolverTerm_contDiff_two
  → cutoffResolverCoeff_contDiff_two
  → heatLevel0_resolverTimeCoeff_contDiffAt_two
  → heatLevel0_srcTimeCoeff_contDiffAt_two
  → heatSemigroup_d0 / heatSemigroup_d1
  → rpow chain/product rules for source slices
```

and the `Real.rpow` chain/product rules need positivity of the heat profile.

Therefore, if the direct route is meant to be discharged from assumptions on `u₀`, it must carry either:

```lean
hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

or, more naturally upstream,

```lean
hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x
```

and then derive `hfloor` using the existing theorem

```lean
heatSemigroup_pos_of_pos hu₀_cont hu₀_pos
```

from `IntervalHeatSemigroupFlooredSourceTimeData.lean`.

## Exact signatures checked

### 1. `cutoffResolverTerm_contDiff_two` itself

Current signature in `IntervalHeatResolverJointC2.lean`:

```lean
theorem cutoffResolverTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) := by
  have hcoef := cutoffResolverCoeff_contDiff_two hu₀_bound hu₀_cont hfloor hc k
  ...
```

So the answer to the first question is directly **yes**: this theorem takes `hfloor`, and immediately passes it to `cutoffResolverCoeff_contDiff_two`.

### 2. `cutoffResolverCoeff_contDiff_two`

Current signature:

```lean
theorem cutoffResolverCoeff_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2 (fun t =>
      smoothRightCutoff (c / 2) c t *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) := by
```

Inside the positive-time branch:

```lean
by_cases ht : c / 2 ≤ t
· have ht_pos : 0 < t := by linarith
  exact (smoothRightCutoff_contDiff (c' := c / 2) (c := c)).contDiffAt.mul
    (heatLevel0_resolverTimeCoeff_contDiffAt_two hu₀_bound hu₀_cont hfloor ht_pos k)
```

So `hfloor` is needed exactly on the support where the cutoff is not locally zero.

### 3. `heatLevel0_resolverTimeCoeff_contDiffAt_two`

Current signature:

```lean
theorem heatLevel0_resolverTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
```

It immediately calls:

```lean
have hsrc := heatLevel0_srcTimeCoeff_contDiffAt_two
  (p := p) hu₀_bound hu₀_cont hfloor ht k
```

The resolver coefficient itself is just a constant elliptic weight times the source time coefficient:

```lean
resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k
  = fun s => intervalNeumannResolverWeight p k *
      srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s
```

So all positivity dependence comes from the source coefficient side.

### 4. `heatLevel0_srcTimeCoeff_contDiffAt_two`

Current signature includes the same `hfloor`:

```lean
theorem heatLevel0_srcTimeCoeff_contDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞)
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
```

It uses `hfloor` three times through the heat-semigroup source-slice lemmas:

```lean
obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
  heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor s hs
```

```lean
obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
  heatSemigroup_d1 (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor s hs
```

and again for continuity of the second source derivative coefficient:

```lean
obtain ⟨δ, hδ, _, _, hcd⟩ :=
  heatSemigroup_d1 (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor s hs
```

### 5. `heatSemigroup_d0` and `heatSemigroup_d1`

Both source-slice lemmas require `hfloor`.

`heatSemigroup_d0`:

```lean
theorem heatSemigroup_d0
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (τ : ℝ) (hτ : 0 < τ) :
    ...
```

`heatSemigroup_d1`:

```lean
theorem heatSemigroup_d1
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (τ : ℝ) (hτ : 0 < τ) :
    ...
```

In `d1`, the positivity is visibly used for `Real.rpow` continuity of powers such as

```lean
(intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1)
```

and

```lean
(intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1 - 1)
```

via code of the form:

```lean
hprofile.rpow_const (fun q hq => by
  obtain ⟨hσ, hx⟩ := mem_prod.mp hq
  exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hleft hσ.1) q.2 hx)))
```

So the floor is not cosmetic.  It is the condition that makes the nonlinear source `ν * u^γ` differentiable through `Real.rpow` along the heat profile.

## Chain from `cutoffResolverSeries_contDiff_two`

Current signature:

```lean
theorem cutoffResolverSeries_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q) := by
```

It calls `contDiff_tsum` with three obligations:

```lean
-- (1) Each cutoff term is C²
· intro k
  exact cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hfloor hc k

-- (2) Majorant summability for each j ≤ 2
· intro j hj
  exact cutoffResolverMajorant_summable hc hu₀_bound hu₀_cont hj

-- (3) Uniform iterated-derivative bound
· intro j k q hj
  exact cutoffResolverTerm_iteratedFDeriv_bound hu₀_bound hu₀_cont hc j k q hj
```

Thus the **currently declared** hypotheses for `cutoffResolverSeries_contDiff_two` are:

```lean
hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀
hu₀_cont  : Continuous u₀
hfloor    : ∀ t > 0, ∀ x ∈ [0,1], 0 < S(t)u₀(x)
hc        : 0 < c
```

Only obligation (1) currently passes `hfloor` into its subproof.

## Majorant signatures are currently too weak

The two majorant lemmas currently **do not** take `hfloor`:

```lean
theorem cutoffResolverMajorant_summable {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ} (hc : 0 < c)
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    {j : ℕ} (_hj : (j : ℕ∞) ≤ 2) :
    Summable (cutoffResolverMajorant p u₀ M₀ c hc j) := by
  sorry
```

```lean
theorem cutoffResolverTerm_iteratedFDeriv_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤
      cutoffResolverMajorant p u₀ M₀ c hc j k := by
  sorry
```

This is inconsistent with the real analytic path if those proofs estimate derivatives of the resolver coefficient by differentiating the nonlinear source coefficient `ν * (S(t)u₀)^γ`.

Reason: the derivative formulas behind the resolver coefficient are the same formulas used by `heatLevel0_resolverTimeCoeff_contDiffAt_two`, and those formulas run through `heatSemigroup_d0/d1`, which require `hfloor`.

So the honest signatures should be strengthened to something like:

```lean
theorem cutoffResolverMajorant_summable {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ} (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {j : ℕ} (hj : (j : ℕ∞) ≤ 2) :
    Summable (cutoffResolverMajorant p u₀ M₀ c hc j) := by
  ...
```

and

```lean
theorem cutoffResolverTerm_iteratedFDeriv_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) (j k : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤
      cutoffResolverMajorant p u₀ M₀ c hc j k := by
  ...
```

Then `cutoffResolverSeries_contDiff_two` should pass `hfloor` to all three `contDiff_tsum` obligations:

```lean
· intro k
  exact cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hfloor hc k
· intro j hj
  exact cutoffResolverMajorant_summable hc hu₀_bound hu₀_cont hfloor hj
· intro j k q hj
  exact cutoffResolverTerm_iteratedFDeriv_bound hu₀_bound hu₀_cont hfloor hc j k q hj
```

### Stronger note: `hfloor` may not be enough for the majorant constants

For pure pointwise `ContDiffAt`, pointwise positivity is enough.

For global majorants of derivatives on the cutoff support, one may need a **quantitative uniform lower bound** for the heat profile, not merely pointwise positivity, especially when powers like `p.γ - 2` occur.

The cleanest upstream assumption is therefore not just an abstract `hfloor`, but the original positive initial data:

```lean
hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x
```

Together with `hu₀_cont`, the existing theorem gives the floor:

```lean
theorem heatSemigroup_pos_of_pos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

Its proof uses compactness of the interval to get a positive minimum of `u₀`, then the heat semigroup lower bound to preserve that floor.  This is exactly the kind of fact the majorant estimates should use if they need lower bounds for negative or fractional powers.

## Main theorem hypothesis chain

The current main theorem in `IntervalHeatResolverJointC2.lean` is:

```lean
theorem heatResolver_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 ...
```

It obtains the cutoff-series `ContDiffAt` by:

```lean
have hCutoff := (cutoffResolverSeries_contDiff_two (p := p)
  hu₀_bound hu₀_cont hfloor hc).contDiffAt (x := (s₀, x₀))
```

So the full currently declared hypothesis chain for the value direct route is:

```text
hu₀_bound  : uniform cosine coefficient bound for u₀
hu₀_cont   : continuity of u₀
hfloor     : positivity of S(t)u₀ for all t > 0 and x ∈ [0,1]
hc         : cutoff threshold c is positive
hs₀        : target time s₀ lies after the cutoff plateau, c < s₀
hx₀        : target spatial point is interior, x₀ ∈ (0,1)
```

If we want the direct route stated only from initial-data hypotheses, replace `hfloor` at the public boundary by:

```lean
hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x
```

and set internally:

```lean
have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
  intro t ht x hx
  exact heatSemigroup_pos_of_pos hu₀_cont hu₀_pos ht hx
```

Then call the existing `heatResolver_jointContDiffAt_two`.

## Gradient theorem

The gradient theorem in the same file already has an `_hfloor` parameter:

```lean
theorem heatResolver_grad_jointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (_hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 ... := by
  sorry
```

The parameter is named `_hfloor` only because the proof is still `sorry`; an honest gradient proof via the same resolver/source coefficient route should use it.  If the gradient proof uses a separate gradient cutoff series, its per-term and majorant lemmas should carry the same positivity assumptions.

## Alternate/stale direct-route file

There is also an older/alternate file:

```text
ShenWork/Paper2/IntervalHeatResolverDirectJointC2.lean
```

In that file the placeholder direct-route signatures currently omit `hfloor`; for example:

```lean
theorem cutoffResolverTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀) (_hc : 0 < c) (n : ℕ) :
    ContDiff ℝ 2 (cutoffResolverTerm p u₀ c n) := by
  sorry
```

and the main theorem there also omits `hfloor` / `hu₀_pos`.

If that older file is still intended to be used, its signatures are too weak for the same reason.  It should be updated to match the newer `IntervalHeatResolverJointC2.lean` chain, or wrapped with `hu₀_pos` and `heatSemigroup_pos_of_pos`.

## Concrete recommendation

Use the following public hypothesis package for the direct heat-level-0 resolver route:

```lean
(hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
(hu₀_cont  : Continuous u₀)
(hu₀_pos   : ∀ x : intervalDomainPoint, 0 < u₀ x)
```

Then derive:

```lean
have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
  intro t ht x hx
  exact heatSemigroup_pos_of_pos hu₀_cont hu₀_pos ht hx
```

and feed `hfloor` into:

```text
heatResolver_jointContDiffAt_two
cutoffResolverSeries_contDiff_two
cutoffResolverTerm_contDiff_two
cutoffResolverCoeff_contDiff_two
heatLevel0_resolverTimeCoeff_contDiffAt_two
heatLevel0_srcTimeCoeff_contDiffAt_two
heatSemigroup_d0 / heatSemigroup_d1
```

Also strengthen the two currently-sorry majorant lemmas to take `hfloor` or, better, take `hu₀_pos` / a quantitative lower-floor package if the estimates need uniform control of fractional/negative powers.
