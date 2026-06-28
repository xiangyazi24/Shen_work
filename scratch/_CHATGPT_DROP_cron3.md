# Q2116 (cron3): cron1 `/tmp/codex_summability.md`

## Status

I could not read the local file `/tmp/codex_summability.md` through the GitHub connector. The connector can read and write repository files, but it cannot access the Codex runner's local `/tmp` filesystem. I therefore grounded this response in the `chatgpt-scratch` branch of `xiangyazi24/Shen_work` and searched the repository for `codex_summability` / `summability`.

No repository file named `codex_summability` was found. The relevant landed repository-side summability implementation is:

```text
ShenWork/Paper2/IntervalEigenCubeSummability.lean
```

## Bottom line

The eigen-cube summability step is already landed and should be treated as the current non-circular producer:

```lean
ShenWork.Paper2.EigenCubeSummability.sourceEigenCubeTailFields_of_sourceC8
```

It converts honest source spatial `C⁸`-Neumann regularity into the `SourceEigenCubeTailFields` package by deriving the summable eigen-cube envelopes required by the older weight-three input theorem:

```lean
ShenWork.Paper2.SourceC6Representative.sourceEigenCubeTailFields_of_weightThree
```

So the correct downstream move is **not** to re-prove eigen-cube summability from scratch. Use `sourceEigenCubeTailFields_of_sourceC8` as the bridge from concrete source `C⁸` data to the tail fields.

## Minimal check block

```lean
import ShenWork.Paper2.IntervalEigenCubeSummability

open ShenWork.Paper2.EigenCubeSummability

#check cubeEnvelope
#check cubeEnvelope_nonneg
#check cubeEnvelope_summable
#check eigenCube_envelope_bound_of_tower
#check eigenCube_envelope_full
#check sourceEigenCubeTailFields_of_sourceC8
```

## Exact analytic structure

For the unit-interval cosine eigenvalue

```lean
λ n = unitIntervalCosineEigenvalue n = ((n : ℝ) * Real.pi) ^ 2
```

the required source tail is an eigen-cube weighted bound:

```lean
λ n * (λ n * (λ n * |a s n|))
```

When `a s n` is represented as a cosine coefficient,

```lean
a s n = cosineCoeffs (f s) n
```

this is morally

```text
(nπ)^6 · |cosineCoeffs (f s) n|.
```

The depth-`4` Neumann tower, supplied by global spatial `C⁸` regularity plus odd Neumann boundary vanishing, feeds the committed generic IBP coefficient decay at `j = 4`:

```text
|cosineCoeffs f n| ≤ 2M / (nπ)^8       for n ≥ 1.
```

Multiplying by `(nπ)^6` gives

```text
(nπ)^6 · |cosineCoeffs f n| ≤ 2M / (nπ)^2.
```

Therefore the summable envelope is exactly:

```lean
def cubeEnvelope (M : ℝ) (n : ℕ) : ℝ :=
  2 * M / ((n : ℝ) * Real.pi) ^ 2
```

The zero mode is harmless because `unitIntervalCosineEigenvalue 0 = 0`, so the cube-weighted expression is zero at `n = 0`. For `n ≥ 1`, `cubeEnvelope M n` is a scalar multiple of `1 / n^2`; hence `cubeEnvelope_summable` closes the summability side using `Real.summable_one_div_nat_pow` with exponent `2`.

## The landed theorem chain

The implemented chain in `IntervalEigenCubeSummability.lean` is:

```text
C⁸ spatial representative + depth-4 Neumann boundary data
  -> neumannTower_four_of_contDiff_eight
  -> cosineCoeffs_decay at j = 4
  -> eigenCube_envelope_bound_of_tower
  -> eigenCube_envelope_full
  -> cubeEnvelope_summable
  -> sourceEigenCubeTailFields_of_weightThree
  -> sourceEigenCubeTailFields_of_sourceC8
```

The key theorem to call downstream is:

```lean
theorem sourceEigenCubeTailFields_of_sourceC8
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : LocalRestart p u T σ)
    {fSrc fAdot : ℝ → ℝ → ℝ} {M Mdot : ℝ}
    (hM : 0 ≤ M) (hMdot : 0 ≤ Mdot)
    -- source: C⁸ representative, cosine-coeff identification, Neumann data, top bound:
    (hSrcCoeff : ∀ s, 0 ≤ s → ∀ n, L.aC s n = cosineCoeffs (fSrc s) n)
    (hSrcCD8 : ∀ s, 0 ≤ s → ContDiff ℝ (8 : ℕ) (fSrc s))
    (hSrcN0 : ∀ s, 0 ≤ s → ∀ i, i < 4 → deriv (gTower (fSrc s) i) 0 = 0)
    (hSrcN1 : ∀ s, 0 ≤ s → ∀ i, i < 4 → deriv (gTower (fSrc s) i) 1 = 0)
    (hSrcTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gTower (fSrc s) 4)| ≤ M)
    -- time derivative: C⁸ representative, identification, Neumann data, top bound:
    (hAdotCoeff : ∀ s, 0 ≤ s → ∀ n, L.srcC.adot s n = cosineCoeffs (fAdot s) n)
    (hAdotCD8 : ∀ s, 0 ≤ s → ContDiff ℝ (8 : ℕ) (fAdot s))
    (hAdotN0 : ∀ s, 0 ≤ s → ∀ i, i < 4 → deriv (gTower (fAdot s) i) 0 = 0)
    (hAdotN1 : ∀ s, 0 ≤ s → ∀ i, i < 4 → deriv (gTower (fAdot s) i) 1 = 0)
    (hAdotTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gTower (fAdot s) 4)| ≤ Mdot)
    -- zero-mode bounds:
    {C0 C0dot : ℝ} (hC0 : 0 ≤ C0) (hC0dot : 0 ≤ C0dot)
    (hSrcZero : ∀ s, 0 ≤ s → |L.aC s 0| ≤ C0)
    (hAdotZero : ∀ s, 0 ≤ s → |L.srcC.adot s 0| ≤ C0dot) :
    ShenWork.Paper2.ChiNegSourceTail.SourceEigenCubeTailFields
      L C0 (2 * (∑' m, cubeEnvelope M m)) C0dot (2 * (∑' m, cubeEnvelope Mdot m))
```

## Non-circularity check

This is non-circular only if the hypotheses `hSrcCD8`, `hAdotCD8`, the odd-boundary Neumann chains, and the top raw-coefficient bounds are produced from the iterate-climb / source regularity side.

Do **not** produce those hypotheses by first invoking the `C⁶` cosine-series representative built from eigen-cube summability. That older route is useful once the weight-three summability input is already known, but it is circular if used to prove the weight-three summability itself.

So the separation is:

```text
sourceEigenCubeTailFields_of_weightThree
  = consumer of already-known eigen-cube envelopes;

sourceEigenCubeTailFields_of_sourceC8
  = producer of those envelopes from honest C⁸-Neumann source data.
```

## What remains downstream

The remaining proof obligation is not the p-series / IBP summability lemma. The remaining obligation is to connect the concrete χ<0 source construction to the hypotheses of `sourceEigenCubeTailFields_of_sourceC8`:

1. produce global `C⁸` representatives `fSrc` and `fAdot` for `L.aC` and `L.srcC.adot`;
2. prove their coefficient-identification lemmas against `cosineCoeffs`;
3. prove the odd Neumann boundary chains for `gTower` levels `i < 4`;
4. produce uniform top raw-coefficient bounds `M` and `Mdot` for level `4`;
5. supply zero-mode bounds `C0` and `C0dot`.

Once those are available, the call is direct:

```lean
exact ShenWork.Paper2.EigenCubeSummability.sourceEigenCubeTailFields_of_sourceC8 L
  hM hMdot
  hSrcCoeff hSrcCD8 hSrcN0 hSrcN1 hSrcTop
  hAdotCoeff hAdotCD8 hAdotN0 hAdotN1 hAdotTop
  hC0 hC0dot hSrcZero hAdotZero
```

## Practical guidance

Treat `ShenWork/Paper2/IntervalEigenCubeSummability.lean` as the summability bridge file. The correct next patch should wire the concrete source-regularity producer into `sourceEigenCubeTailFields_of_sourceC8`; it should not duplicate the `cubeEnvelope` p-series argument or the depth-`4` IBP decay argument.
