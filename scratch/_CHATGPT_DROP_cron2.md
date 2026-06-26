# Q766 (cron2): projection bounds for `iteratedFDeriv` of `fst`/`snd` factors

Static repo inspection only; I did not run a Lean build.

## Answer

Yes.  The repo already has exactly the projection lemmas you want.

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2CutoffBounds.lean
```

Namespace:

```lean
ShenWork.IntervalResolverSpectralJointC2CutoffBounds
```

The names are:

```lean
norm_iteratedFDeriv_comp_fst_le
norm_iteratedFDeriv_comp_snd_le
```

Exact shapes:

```lean
/-- Projection bound for functions depending only on the first coordinate. -/
theorem norm_iteratedFDeriv_comp_fst_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.1) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.1‖
```

and

```lean
/-- Projection bound for functions depending only on the second coordinate. -/
theorem norm_iteratedFDeriv_comp_snd_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.2) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.2‖
```

Implementation detail: both lemmas are proved by composing with the continuous linear projections

```lean
ContinuousLinearMap.fst ℝ ℝ ℝ
ContinuousLinearMap.snd ℝ ℝ ℝ
```

then using:

```lean
L.iteratedFDeriv_comp_right hg q hk
ContinuousMultilinearMap.norm_compContinuousLinearMap_le
```

and finally simplifying with:

```lean
ContinuousLinearMap.norm_fst
ContinuousLinearMap.norm_snd
```

## Existing use patterns

The lemmas are already used in the resolver bounded-weight and cutoff proofs.

Example value-side resolver pattern:

```lean
have hcoeffNorm :
    ‖iteratedFDeriv ℝ (i - j)
      (fun q : ℝ × ℝ =>
        localRestartCoeff a₀ a (q.1 - offset) n) q‖ ≤
    ‖iteratedFDeriv ℝ (i - j)
      (fun t : ℝ => localRestartCoeff a₀ a (t - offset) n) q.1‖ :=
  norm_iteratedFDeriv_comp_fst_le hcoeff₀ hijTop q
```

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

Example cosine/space pattern:

```lean
have hcosNorm :
    ‖iteratedFDeriv ℝ (k - i)
      (fun q : ℝ × ℝ => cosineMode n q.2) q‖ ≤
    valueCosWeight (k - i) n := by
  exact (norm_iteratedFDeriv_comp_snd_le hcos₀ hkiTop q).trans
    (cosineMode_iteratedFDeriv_bound n (k - i) q.2 (by omega))
```

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

There is also a generic bounded-weight mode-term use:

```lean
have htime :
    ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => c n q.1) q‖ ≤ Bt i n :=
  (norm_iteratedFDeriv_comp_fst_le hc hiTop q).trans (hBt i (le_trans hik hkNat))

have hspace :
    ‖iteratedFDeriv ℝ (k - i) (fun q : ℝ × ℝ => cosineMode n q.2) q‖ ≤
      valueCosWeight (k - i) n :=
  (norm_iteratedFDeriv_comp_snd_le hcos₀ hkiTop q).trans
    (cosineMode_iteratedFDeriv_bound n (k - i) q.2 (by omega))
```

File:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

## Relevance to `heatTerm`

For the heat term split, these are the right tools for the one-coordinate factors:

```lean
fun q : ℝ × ℝ => Real.exp (-q.1 * unitIntervalCosineEigenvalue n)
```

via `norm_iteratedFDeriv_comp_fst_le`, and

```lean
fun q : ℝ × ℝ => cosineMode n q.2
```

via `norm_iteratedFDeriv_comp_snd_le` plus the already-existing:

```lean
cosineMode_iteratedFDeriv_bound
```

from:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

So the repository does have the projection-bound infrastructure needed to reduce the mixed `ℝ²` derivative bounds to one-dimensional `t` and `x` derivative bounds.
