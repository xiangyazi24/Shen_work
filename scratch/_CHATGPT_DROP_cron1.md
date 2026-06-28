# Q1541 (cron1) -- finite-sum cutoff resolver majorant

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Short answer

Yes. The right `cutoffResolverMajorant` should be a **finite Leibniz sum**. In fact it should be a two-layer finite sum:

1. Leibniz for the scalar time factor

```text
smoothRightCutoff(t) * resolverTimeCoeff_k(t)
```

2. Leibniz for multiplying that scalar time factor by the spatial mode

```text
cos(k*pi*x)
```

The source/resolver coefficient envelope only needs to hold on `Set.Ici (c/2)`, because for `t < c/2` the cutoff term is locally zero, and for `t >= c/2` we are away from `0`.

The important design point: do **not** define the final majorant only as an opaque `Classical.choice`. Define it from explicit ingredients:

```text
cutoff derivative bounds
source coefficient derivative envelope on [c/2, infinity)
resolver weight abs value
spatial cosine derivative powers
```

Then summability is transparent from quartic source coefficient decay plus the elliptic resolver weight.

## Repo context

The current direct file already defines

```lean
def cutoffResolverTerm ... :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * cosineMode k q.2)
```

and has a placeholder `cutoffResolverMajorant` plus sorry lemmas for nonnegativity, summability, and the derivative bound.

The existing `cutoffValueTerm_leibniz_bound` in `IntervalResolverSpectralJointC2CutoffBounds.lean` is exactly the pattern to reuse: it bounds the iterated derivative of a product by a finite sum over `Finset.range (k + 1)` with binomial coefficients.

## Concrete Lean code: reusable finite-sum majorant

This is the definition I would add near the current placeholder in `IntervalHeatResolverJointC2.lean` or in a small helper file imported by it.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalResolverSpectralJointC2CutoffBounds
import ShenWork.PDE.IntervalSourceDecayQuantitative

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete (srcTimeCoeff)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- A noncomputable global bound for the `r`-th time derivative of the cutoff
`φ(t) = smoothRightCutoff (c/2) c t`.

For proofs, show this really bounds all `t` by splitting:
* `t <= c/2`: the cutoff is locally zero;
* `c/2 <= t <= c`: compactness/continuity;
* `c <= t`: the cutoff is locally one, so higher derivatives vanish and order `0`
  is bounded by `1`.

The `max 1` handles the zeroth derivative on `[c, infinity)`. -/
noncomputable def smoothRightCutoffDerivBound (c : ℝ) (r : ℕ) : ℝ :=
  max 1
    (sSup ((fun t : ℝ =>
      ‖iteratedFDeriv ℝ r (smoothRightCutoff (c / 2) c) t‖) ''
        Set.Icc (c / 2) c))

/-- A noncomputable envelope for the `r`-th time derivative of the source
coefficient on the positive-time half-line `[c/2, infinity)`.  This is the
formal version of “source coefficient envelope on `[c/2, infinity)`”.

For the actual summability proof, one should prove this envelope has quartic mode
decay for `r <= 2`, using positive-time heat smoothing + H4 Neumann/IBP. -/
noncomputable def srcTimeCoeffIciEnvelope
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (c : ℝ)
    (r k : ℕ) : ℝ :=
  max 0
    (sSup ((fun t : ℝ =>
      ‖iteratedFDeriv ℝ r
        (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖) ''
          Set.Ici (c / 2)))

/-- Spatial derivative bound for the value mode `cos(k*pi*x)`.
The `r`-th spatial derivative is bounded by `(k*pi)^r` in absolute value. -/
def cosineModeDerivMajorant (r k : ℕ) : ℝ :=
  ((k : ℝ) * |Real.pi|) ^ r

/-- Spatial derivative bound for the gradient mode.  Since the gradient already
contains one `x`-derivative, the `r`-th extra derivative costs `(k*pi)^(r+1)`. -/
def cosineGradModeDerivMajorant (r k : ℕ) : ℝ :=
  ((k : ℝ) * |Real.pi|) ^ (r + 1)

/-- Majorant for the `m`-th derivative of the scalar time coefficient

`φ(t) * resolverTimeCoeff_k(t)`.

This is the first Leibniz finite sum.  The resolver coefficient is
`w_k * srcTimeCoeff_k`, so its envelope is
`|w_k| * srcTimeCoeffIciEnvelope`. -/
noncomputable def cutoffResolverCoeffMajorant
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (c : ℝ)
    (m k : ℕ) : ℝ :=
  ∑ a in Finset.range (m + 1),
    (m.choose a : ℝ) *
      smoothRightCutoffDerivBound c a *
      (|ShenWork.PDE.intervalNeumannResolverWeight p k| *
        srcTimeCoeffIciEnvelope p u₀ c (m - a) k)

/-- Value-side majorant for the full cutoff resolver term

`φ(t) * resolverTimeCoeff_k(t) * cos(k*pi*x)`.

This is the second Leibniz finite sum, splitting total joint order `j` between the
scalar time coefficient and the spatial cosine mode. -/
noncomputable def cutoffResolverValueMajorant
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (M₀ c : ℝ)
    (_hc : 0 < c) (j k : ℕ) : ℝ :=
  let _ := M₀
  ∑ b in Finset.range (j + 1),
    (j.choose b : ℝ) *
      cutoffResolverCoeffMajorant p u₀ c b k *
      cosineModeDerivMajorant (j - b) k

/-- Gradient-side majorant.  Same scalar coefficient part, but the spatial factor
has one extra `k*pi`. -/
noncomputable def cutoffResolverGradMajorant
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (M₀ c : ℝ)
    (_hc : 0 < c) (j k : ℕ) : ℝ :=
  let _ := M₀
  ∑ b in Finset.range (j + 1),
    (j.choose b : ℝ) *
      cutoffResolverCoeffMajorant p u₀ c b k *
      cosineGradModeDerivMajorant (j - b) k

/-- If the current file wants the existing single name `cutoffResolverMajorant`,
use the value-side majorant as the drop-in replacement. -/
noncomputable def cutoffResolverMajorant
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (M₀ c : ℝ)
    (hc : 0 < c) (j k : ℕ) : ℝ :=
  cutoffResolverValueMajorant p u₀ M₀ c hc j k

end ShenWork.Paper2.HeatResolverJointC2Direct
```

## Variant: better proof interface with an explicit envelope structure

The `sSup` definitions above are concrete but may be annoying to prove summable from directly.  The cleaner proof-facing API is to parameterize the finite sum by an envelope record:

```lean
structure SrcCoeffIciEnvelope
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (c : ℝ) : Prop where
  E : ℕ → ℕ → ℝ
  nonneg : ∀ r k, 0 ≤ E r k
  bound : ∀ r k t, (r : ℕ∞) ≤ (2 : ℕ∞) → c / 2 ≤ t →
    ‖iteratedFDeriv ℝ r
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ ≤ E r k
  quartic : ∀ r, (r : ℕ∞) ≤ (2 : ℕ∞) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      E r k ≤ C / ((k : ℝ) * Real.pi) ^ 4
```

Then define the majorant from `H.E` instead of from `srcTimeCoeffIciEnvelope`:

```lean
noncomputable def cutoffResolverCoeffMajorantOfEnvelope
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {c : ℝ}
    (H : SrcCoeffIciEnvelope p u₀ c) (m k : ℕ) : ℝ :=
  ∑ a in Finset.range (m + 1),
    (m.choose a : ℝ) *
      smoothRightCutoffDerivBound c a *
      (|ShenWork.PDE.intervalNeumannResolverWeight p k| * H.E (m - a) k)

noncomputable def cutoffResolverValueMajorantOfEnvelope
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {c : ℝ}
    (H : SrcCoeffIciEnvelope p u₀ c) (j k : ℕ) : ℝ :=
  ∑ b in Finset.range (j + 1),
    (j.choose b : ℝ) *
      cutoffResolverCoeffMajorantOfEnvelope H b k *
      cosineModeDerivMajorant (j - b) k

noncomputable def cutoffResolverGradMajorantOfEnvelope
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {c : ℝ}
    (H : SrcCoeffIciEnvelope p u₀ c) (j k : ℕ) : ℝ :=
  ∑ b in Finset.range (j + 1),
    (j.choose b : ℝ) *
      cutoffResolverCoeffMajorantOfEnvelope H b k *
      cosineGradModeDerivMajorant (j - b) k
```

This version is usually better for Lean: first prove `SrcCoeffIciEnvelope` from heat smoothing on `[c/2, infinity)`, then the majorant proof is mostly algebraic.

## Why this is summable

For `r <= 2`, the intended envelope proof gives

```text
src envelope E r k = O(k^-4)
```

The resolver weight contributes

```text
|w_k| = 1 / (mu + lambda_k) = O(k^-2)
```

so the scalar resolver coefficient envelope is

```text
O(k^-6)
```

For value-side joint order `j <= 2`, the spatial cosine derivative contributes at worst

```text
(k*pi)^j = O(k^j)
```

so the value majorant is

```text
O(k^(j-6))
```

which is summable for `j <= 2`.  For the gradient side there is one extra spatial factor, so it is

```text
O(k^(j-5))
```

also summable for `j <= 2`.

The mode `k = 0` should be handled separately by `summable_nat_add_iff` / finite-prefix splitting / direct finite singleton handling; the asymptotic proof is for `k >= 1`.

## Proof outline for `cutoffResolverTerm_iteratedFDeriv_bound`

1. Rewrite

```lean
cutoffResolverTerm p u c k =
  fun q =>
    (smoothRightCutoff (c/2) c q.1 * resolverTimeCoeff p u k q.1) *
      cosineMode k q.2
```

2. Apply `norm_iteratedFDeriv_mul_le` or mimic `cutoffValueTerm_leibniz_bound` to get the outer finite sum over `b <= j`.

3. Bound the scalar time coefficient derivative by another `norm_iteratedFDeriv_mul_le` over `a <= b`.

4. For `q.1 < c/2`, use local zero of the cutoff term.  For `q.1 >= c/2`, use the source envelope on `Set.Ici (c/2)` and the constant resolver factorization.

5. Use

```lean
‖D^r (cos(k*pi*x))‖ ≤ ((k : ℝ) * |Real.pi|)^r
```

and for the gradient version use exponent `r+1`.

## Recommended replacement

Replace the placeholder

```lean
noncomputable def cutoffResolverMajorant ... := Classical.choice inferInstance
```

with the finite value-side definition above.  If the direct route later needs both value and gradient regularity, keep both:

```lean
cutoffResolverValueMajorant
cutoffResolverGradMajorant
```

and feed the correct one to the corresponding `contDiff_tsum` call.

This is compatible with the existing cutoff route: the cutoff term is already `φ(t) * resolverTimeCoeff(t) * cos(kπx)`, and the repo already has the product-derivative finite-sum pattern in `cutoffValueTerm_leibniz_bound`.
