# Q787 (cron2) — `heatTerm_iteratedFDeriv_global_bound` / resolver value-term reuse

Static repo inspection only; I did not run a Lean build.

## Short answer

Yes: the repo has essentially the exact separated-product computation for resolver value terms.

The two most relevant implementations are:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
  boundedWeightJointTerm_iteratedFDeriv_le
```

and

```text
ShenWork/PDE/IntervalResolverSpectralJointC2CutoffBounds.lean
  cutoffValueTerm_leibniz_bound
  norm_iteratedFDeriv_comp_fst_le
  norm_iteratedFDeriv_comp_snd_le
```

with the concrete cutoff/value bound assembled in:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
  cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
  cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound
  shiftedLocalRestartCoeff_valueWeight_le_core
  cosineMode_iteratedFDeriv_bound
  valueCosWeight
```

So the computation exists, but it is packaged as a **Leibniz-sum majorant**, not as a sharp one-line bound with no finite combinatorial constant.

## Important correction for the current heat lemma

The current target in `IntervalHeatSemigroupHighRegularity.lean`:

```lean
private theorem heatTerm_iteratedFDeriv_global_bound
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (_hc : 0 < c) (j n : ℕ) (q : ℝ × ℝ)
    (hj : (j : ℕ∞) ≤ 2) :
    ‖iteratedFDeriv ℝ j (heatTerm u₀ n) q‖ ≤
      (1 + unitIntervalCosineEigenvalue n) ^ j * M₀ *
        Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n) := by
  sorry
```

is **not true globally in `q`** for `heatTerm` alone.  For `j = 0`, `n > 0`, `q.1` very negative, and a nonzero coefficient, the factor

```lean
Real.exp (-q.1 * unitIntervalCosineEigenvalue n)
```

blows up, while the RHS is fixed at

```lean
M₀ * Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)
```

So this theorem needs either:

```lean
(hq : c / 2 ≤ q.1)
```

or it should be replaced by a bound for the **cutoff** heat term, with a left-side zero branch.

This matches the comment in the file saying the estimate is only used where the cutoff is nonzero.  The formal proof should reflect that by splitting on `q.1 < c / 2` vs `c / 2 ≤ q.1`.

## Exact resolver analogue: generic separated product

In `IntervalResolverJointC2Physical.lean` the repo has the clean reusable theorem for exactly the shape

```lean
(t, x) ↦ c n t * cosineMode n x
```

Definitions:

```lean
def boundedWeightJointTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * cosineMode n q.2

def boundedWeightJointMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * valueCosWeight (k - i) n
```

The theorem:

```lean
theorem boundedWeightJointTerm_iteratedFDeriv_le
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hc : ContDiff ℝ (2 : ℕ∞) (c n)) (hk : (k : ℕ∞) ≤ (2 : ℕ∞))
    (hBt : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) q.1‖ ≤ Bt i n) :
    ‖iteratedFDeriv ℝ k (boundedWeightJointTerm c n) q‖ ≤
      boundedWeightJointMajorant Bt k n := by
  ...
```

The proof uses exactly the desired ingredients:

```lean
norm_iteratedFDeriv_mul_le
norm_iteratedFDeriv_comp_fst_le
norm_iteratedFDeriv_comp_snd_le
cosineMode_iteratedFDeriv_bound
```

This is probably the best reusable skeleton for `heatTerm`, because `heatTerm u₀ n` is definitionally the same pattern with

```lean
c n t = Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n
```

## Exact resolver analogue: cutoff value term

In `IntervalResolverSpectralJointC2CutoffBounds.lean` there is also the value-side cutoff Leibniz split:

```lean
theorem cutoffValueTerm_leibniz_bound
    {φ : ℝ → ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    {offset : ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hG : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ =>
        φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n))
    (hH : ContDiff ℝ (2 : ℕ∞) (fun q : ℝ × ℝ => cosineMode n q.2))
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k (cutoffValueTerm φ a₀ a offset n) q‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i
          (fun q : ℝ × ℝ =>
            φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n) q‖ *
        ‖iteratedFDeriv ℝ (k - i)
          (fun q : ℝ × ℝ => cosineMode n q.2) q‖ := by
  ...
```

That file also proves the projection helpers:

```lean
theorem norm_iteratedFDeriv_comp_fst_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.1) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.1‖

theorem norm_iteratedFDeriv_comp_snd_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.2) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.2‖
```

These are exactly the projection lemmas you named.

## Fully assembled resolver value bound

The concrete value-side version is in `IntervalResolverSpectralJointC2Concrete.lean`:

```lean
theorem cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a)
    {n k : ℕ} {q : ℝ × ℝ}
    (hL : restartCutoffLeftOuter offset s ≤ q.1)
    (hR : q.1 ≤ restartCutoffRightOuter offset s)
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ‖iteratedFDeriv ℝ k
      (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n) q‖ ≤
      concreteRestartValueMajorant a₀ src offset s hτ k n := by
  ...
```

and the global version:

```lean
theorem cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s : ℝ}
    (hτ : 0 < s - offset) (src : DuhamelSourceTimeC2Coeff a) :
    ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
      ‖iteratedFDeriv ℝ k
        (cutoffValueTerm (restartSmoothCutoff offset s) a₀ a offset n)
          q‖ ≤
        concreteRestartValueMajorant a₀ src offset s hτ k n := by
  ...
```

The proof pattern is exactly what the heat cutoff proof should imitate:

1. Outside the cutoff slab, prove the iterated derivative is zero by local eventual equality to zero.
2. Inside the slab, apply `cutoffValueTerm_leibniz_bound`.
3. Use `norm_iteratedFDeriv_comp_fst_le` and `norm_iteratedFDeriv_comp_snd_le`.
4. Use cosine bounds:

```lean
def valueCosWeight (m n : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => |(n : ℝ) * Real.pi|
  | _ => unitIntervalCosineEigenvalue n

theorem cosineMode_iteratedFDeriv_bound
    (n m : ℕ) (y : ℝ) (hm : m ≤ 2) :
    ‖iteratedFDeriv ℝ m (cosineMode n) y‖ ≤ valueCosWeight m n
```

5. Use a coefficient-times-spatial-weight bound:

```lean
theorem shiftedLocalRestartCoeff_valueWeight_le_core
    ... :
    ‖iteratedFDeriv ℝ r
      (fun u : ℝ => localRestartCoeff a₀ a (u - offset) n) t‖ *
        valueCosWeight m n ≤
      restartCoeffCoreMajorant a₀ src τmin τmax n
```

For the heat file, the corresponding coefficient lemma is the missing scalar part:

```lean
‖iteratedFDeriv ℝ i
  (fun t : ℝ => Real.exp (-t * λ_n) * â_n) q.1‖
  ≤ λ_n ^ i * M₀ * Real.exp (-(c / 2) * λ_n)
```

under `c / 2 ≤ q.1`.

## Recommended heat proof route

Do not try to finish the existing `heatTerm_iteratedFDeriv_global_bound` as stated.  Add a time-lower-bound version, or replace the downstream proof with a direct cutoff split.

A direct reusable route:

```lean
open ShenWork.IntervalResolverJointC2Physical
open ShenWork.IntervalResolverSpectralJointC2Concrete
  (valueCosWeight valueCosWeight_nonneg cosineMode_iteratedFDeriv_bound)
```

Define the scalar coefficient family:

```lean
private def heatCoeff (u₀ : intervalDomainPoint → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n
```

Then identify:

```lean
have hterm : heatTerm u₀ n =
    ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm
      (fun n t => heatCoeff u₀ n t) n := by
  funext q
  simp [heatTerm, heatCoeff,
    ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm]
```

Use:

```lean
boundedWeightJointTerm_iteratedFDeriv_le
```

with a time derivative bound such as:

```lean
private def heatCoeffBt (c M₀ : ℝ) (i n : ℕ) : ℝ :=
  unitIntervalCosineEigenvalue n ^ i * M₀ *
    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)
```

and prove, for `c / 2 ≤ t`:

```lean
‖iteratedFDeriv ℝ i (heatCoeff u₀ n) t‖ ≤ heatCoeffBt c M₀ i n
```

For `i ≤ 2`, this can be discharged by `interval_cases i`:

```text
i = 0:  |exp(-tλ) â| ≤ M₀ exp(-(c/2)λ)
i = 1:  |-λ exp(-tλ) â| ≤ λ M₀ exp(-(c/2)λ)
i = 2:  |λ² exp(-tλ) â| ≤ λ² M₀ exp(-(c/2)λ)
```

The exponential comparison is:

```lean
Real.exp (-t * λ) ≤ Real.exp (-(c / 2) * λ)
```

from `c / 2 ≤ t` and `0 ≤ λ`.

Then the generic resolver theorem gives the natural heat bound:

```lean
‖iteratedFDeriv ℝ j (heatTerm u₀ n) q‖ ≤
  boundedWeightJointMajorant (heatCoeffBt c M₀) j n
```

This is the repo-native formulation.

If the file really wants the RHS

```lean
(1 + λ_n)^j * M₀ * exp(-(c / 2) * λ_n)
```

then one more finite collapse lemma is needed from the Leibniz sum.  The existing resolver proofs generally **do not** collapse this way; they package the finite Leibniz constants into a majorant, e.g.

```lean
concreteRestartValueLeibnizConstant
concreteRestartValueMajorant
```

So the easiest and most repo-aligned fix is to allow a finite `j`-dependent constant/Leibniz-sum majorant for heat as well.  This is fully sufficient for `contDiff_tsum`, because multiplying a summable exponential-polynomial majorant by a finite constant preserves summability.

## Practical patch shape

Recommended replacement architecture in `IntervalHeatSemigroupHighRegularity.lean`:

```text
1. Replace/rename heatTerm_iteratedFDeriv_global_bound with:

   heatTerm_iteratedFDeriv_bound_of_ge
     ... (hq : c / 2 ≤ q.1) ...

   returning either:
     boundedWeightJointMajorant (heatCoeffBt c M₀) j n
   or:
     C_j * (1 + λ_n)^j * M₀ * exp(-(c/2)λ_n)

2. In cutoffHeatTerm_iteratedFDeriv_bound, split:

   by_cases hleft : q.1 < c / 2

   left branch:
     prove cutoffHeatTerm =ᶠ[𝓝 q] 0 using smoothRightCutoff_eq_zero_of_le,
     then use EventuallyEq.iteratedFDeriv and norm_zero.

   right branch:
     have hge : c / 2 ≤ q.1 := le_of_not_gt hleft
     apply norm_iteratedFDeriv_mul_le for cutoff * heatTerm
     use smoothRightCutoffDerivBound_spec for cutoff derivatives
     use heatTerm_iteratedFDeriv_bound_of_ge for heatTerm derivatives.

3. Keep the summability proof unchanged in spirit:

   one_add_eigenvalue_pow_mul_exp_summable

   still handles the heat majorant, even with finite Leibniz constants.
```

## Verdict

The exact computation exists in the resolver infrastructure.  The closest drop-in theorem is:

```lean
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm_iteratedFDeriv_le
```

The fully assembled cutoff-value model to imitate is:

```lean
ShenWork.IntervalResolverSpectralJointC2Concrete
  .cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound_of_mem_slab

ShenWork.IntervalResolverSpectralJointC2Concrete
  .cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound
```

But the heat lemma should not remain “global” for `heatTerm` without a lower time bound.  The correct proof should either add `c / 2 ≤ q.1`, or move the global statement to `cutoffHeatTerm` and split off the left zero region, exactly as the resolver cutoff proof does.
