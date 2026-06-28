# Q1564 (cron1) -- source coefficient decay / boundedness at infinity

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Short answer

I did **not** find an existing theorem in the repo proving

```lean
Tendsto
  (fun t => srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t)
  atTop (𝓝 0)
```

for `k >= 1`, nor a theorem proving

```lean
S(t)u₀ → mean(u₀)
```

uniformly as `t → ∞`.

So the proposed route

```text
continuity on [c,∞) + vanishing at infinity -> bounded
```

is mathematically valid, but it requires a new `atTop` theorem that does not appear to exist yet.

For the immediate `BddAbove` proof, the shorter route is still the one from Q1552:

```text
L∞ contraction of heat semigroup
→ uniform spatial bound on ν*(S(t)u₀)^γ for all t >= c
→ cosine coefficient bound
→ resolverTimeCoeff bounded via resolverTimeCoeff = w_k * srcTimeCoeff
```

This avoids proving long-time convergence altogether.

## Search summary

I searched for variants of:

```text
srcTimeCoeff atTop Tendsto infinity decay
intervalFullSemigroupOperator atTop Tendsto mean average
heat semigroup tendsto atTop mean constant cosine
cosineCoeffs constant zero k >= 1
Tendsto atTop intervalFullSemigroupOperator cosineKernel exp_neg
```

No direct source-coefficient decay theorem or heat-semigroup-to-mean theorem turned up.

The closest heat-semigroup material found was in `IntervalSemigroupNeumann.lean`, which proves coefficient summability and Neumann boundary facts for positive time, but not an `atTop` limit. Example:

```lean
theorem heatCoeff_eigenvalue_summable {t : ℝ} (ht : 0 < t)
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * a n|)
```

and

```lean
theorem unitIntervalCosineHeatValue_eq_cosineCoeffSeries
    (t : ℝ) (a : ℕ → ℝ) :
    unitIntervalCosineHeatValue t a =
      fun x => ∑' n, (Real.exp (-t * unitIntervalCosineEigenvalue n) * a n) *
        cosineMode n x
```

These are useful ingredients for proving convergence, but they are not the convergence theorem itself.

## Existing identities that matter

`srcTimeCoeff` is already identified with the cosine coefficient of the source slice:

```lean
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ

theorem srcTimeCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k := by
```

The resolver coefficient is already factored as a constant elliptic weight times the source coefficient:

```lean
resolverTimeCoeff p u k t = intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

So any source coefficient bound immediately gives a resolver coefficient bound.

## Continuity + vanishing at infinity route

This route is logically sound.  The reusable lemma should be independent of PDE content:

```lean
lemma bddAbove_norm_image_Ici_of_tendsto_atTop
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {c : ℝ}
    (hf : ContinuousOn f (Set.Ici c))
    (hlim : Tendsto f atTop (𝓝 0)) :
    BddAbove ((fun t : ℝ => ‖f t‖) '' Set.Ici c) := by
  classical
  -- choose R with ‖f t‖ ≤ 1 on t ≥ R
  -- use compactness on Icc c (max c R)
  -- union compact part and tail part
  sorry
```

A scalar version for absolute values:

```lean
lemma bddAbove_abs_image_Ici_of_tendsto_atTop
    {f : ℝ → ℝ} {c L : ℝ}
    (hf : ContinuousOn f (Set.Ici c))
    (hlim : Tendsto f atTop (𝓝 L)) :
    BddAbove ((fun t : ℝ => |f t|) '' Set.Ici c) := by
  -- apply the norm version to fun t => f t - L, then add |L|
  sorry
```

Then for `k >= 1`, if you prove

```lean
Tendsto
  (fun t => srcTimeCoeff p (conjugatePicardIter p u₀ 0) k t)
  atTop (𝓝 0)
```

and positive-time continuity on `Set.Ici c`, boundedness follows immediately.

For `k = 0`, the target limit should not be `0` in general.  It should be

```text
∫_0^1 ν * mean(u₀)^γ dx = ν * mean(u₀)^γ
```

or its normalized cosine-coefficient version.  But finite limit is enough for boundedness.

## What is missing for the decay route

To prove the `k >= 1` decay theorem, you need a long-time theorem roughly like:

```lean
theorem heatLevel0_tendsto_mean_uniform
    {u₀ : intervalDomainPoint → ℝ} ... :
    Tendsto
      (fun t => fun x => intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
      atTop
      (𝓝 (fun x => mean_u₀))
```

or a coefficient-series version:

```lean
Tendsto
  (fun t => Real.exp (-t * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k)
  atTop (𝓝 0)
```

for `k >= 1`, plus enough summability to pass through the nonlinear map `u ↦ ν*u^γ` and the cosine coefficient. I did not find that in the repo.

For the constant-mode statement, one would also need a lemma that positive cosine modes of a constant vanish:

```lean
lemma cosineCoeffs_const_pos (A : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    cosineCoeffs (fun _ : ℝ => A) k = 0 := by
  -- use cosineCoeffs_eq_factor_mul_integral and ∫ cos(kπx) over 0..1 = 0
  sorry
```

I did not find an existing named theorem for this either.

## Recommended route for the current `BddAbove` goal

For regime 3 (`q.1 > c`, cutoff = 1), avoid the long-time limit unless you specifically need decay.  For boundedness of

```lean
‖iteratedFDeriv ℝ j (cutoffResolverTerm p u c k) q‖
```

it is enough to bound finitely many factors from the Leibniz expansion.

For the zeroth resolver coefficient:

```text
|resolverTimeCoeff_k(t)|
  = |w_k| * |srcTimeCoeff_k(t)|
  ≤ |w_k| * Csrc
```

where `Csrc` comes from a uniform spatial bound on `srcSlice`.

Available theorem:

```lean
theorem intervalFullSemigroupOperator_Linfty_bound {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalFullSemigroupOperator t f x| ≤ M
```

This gives `|S(t)u₀(x)| ≤ U0` for all `t > 0`; then positivity gives `0 ≤ S(t)u₀(x) ≤ U0`; then

```text
|ν*(S(t)u₀(x))^γ| ≤ ν * U0^γ
```

and the existing coefficient-bound lemma gives

```lean
|cosineCoeffs (srcSlice p u t) k| ≤ 2 * (p.ν * U0^p.γ)
```

uniformly in `t >= c`.

For the derivative factors appearing when `j = 1,2`, use the lower-time cutoff `c` in heat multiplier estimates:

```text
λ^m exp(-tλ) ≤ λ^m exp(-cλ),  t >= c
```

This is the same analytic mechanism as the cutoff majorant route. It gives finite half-line envelopes for `D_t^a resolverTimeCoeff_k` without needing an atTop convergence theorem.

## Concrete lemma shape to add now

The following local utility is enough to turn a uniform spatial bound into the half-line coefficient `BddAbove` needed for iSup:

```lean
theorem srcCoeff_bddAbove_Ici_of_uniform_source_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c B : ℝ} (hB : 0 ≤ B)
    (hcont : ∀ t ∈ Set.Ici c,
      ContinuousOn (srcSlice p u t) (Set.Icc (0 : ℝ) 1))
    (hbd : ∀ t ∈ Set.Ici c, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |srcSlice p u t x| ≤ B)
    (k : ℕ) :
    BddAbove ((fun t : ℝ => |srcTimeCoeff p u k t|) '' Set.Ici c) := by
  refine ⟨2 * B, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  rw [srcTimeCoeff_eq_cosineCoeffs]
  exact cosineCoeffs_abs_le_of_continuous_bounded (hcont t ht) hB (hbd t ht) k
```

Then the resolver version is one line after `resolverTimeCoeff_eq_weight_smul`:

```lean
theorem resolverCoeff_bddAbove_Ici_of_srcCoeff_bddAbove
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {c B : ℝ}
    (hsrc : ∀ t ∈ Set.Ici c, |srcTimeCoeff p u k t| ≤ B) :
    BddAbove ((fun t : ℝ => |resolverTimeCoeff p u k t|) '' Set.Ici c) := by
  refine ⟨|ShenWork.PDE.intervalNeumannResolverWeight p k| * B, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  rw [resolverTimeCoeff_eq_weight_smul]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hsrc t ht) (abs_nonneg _)
```

## Final verdict

* No existing `srcTimeCoeff` decay-at-infinity theorem found.
* No existing `S(t)u₀ → mean(u₀)` theorem found.
* Yes, continuity on `[c,∞)` plus finite limit/vanishing at infinity gives `BddAbove`; this is a valid generic lemma.
* But for the current iSup majorant, do not depend on atTop decay unless necessary. Use heat-semigroup `L∞` contraction for coefficient boundedness and heat multiplier estimates for coefficient derivative boundedness.
