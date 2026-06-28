# Q1590 (cron2) — direct IBP route for `cutoffResolverMajorant_summable`

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

The no-`PhysicalResolverJointC2Data` route is viable, but the decay cannot be extracted from `cutoffResolverCoeff_contDiff_two` as a black box.

`cutoffResolverCoeff_contDiff_two` proves time regularity of the scalar coefficient

```lean
fun t => smoothRightCutoff (c / 2) c t *
  resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

This is a `t`-only `ContDiff ℝ 2` statement. It does not imply spatial `IntervalWeakH2Neumann` for

```lean
fun x => p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ^ p.γ
```

Scalar time smoothness for each `k` carries no uniform-in-`k` decay information.

The correct direct route is:

```text
spatial C2 of source slice + Neumann endpoint data
  -> IntervalWeakH2Neumann
  -> quadratic cosine coefficient decay
  -> resolver weight w_k = O(k^-2)
  -> summable cutoff majorant for joint orders j <= 2.
```

## Existing API to use

The repo already has the needed H2 package:

```lean
IntervalWeakH2Neumann
intervalWeakH2Neumann_of_contDiffOn
intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
```

The constructor `intervalWeakH2Neumann_of_contDiffOn` needs spatial `ContDiffOn ℝ 2` on `[0,1]` plus first-derivative Neumann endpoint data. Then `intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound` gives

```text
|cosineCoeffs f k| <= 2 B / (k*pi)^2,  k >= 1.
```

This is the IBP decay you want.

## What direct data is needed

For `D^j(cutoffResolverTerm_k)` with `j <= 2`, Leibniz terms use time derivatives of the source coefficient up to order `2`. So the direct replacement for `PhysicalResolverJointC2Data` should prove H2 Neumann, uniformly for `t >= c/2`, for the three source time slices:

```text
m = 0: srcSlice  p u t
m = 1: srcSlice1 p u (heatDu u0) t
m = 2: srcSlice2 p u (heatDu u0) (heatD2u u0) t
```

More explicitly, add three lemmas of this form:

```text
exists Bm >= 0 such that for all t >= c/2,
there is Hm : IntervalWeakH2Neumann(sourceSlice_m t)
and integral |Hm.secondDeriv| <= Bm.
```

Then apply the quadratic-decay theorem to get envelopes

```text
E_m(k) = O(k^-2)
```

for all three source coefficient time slices.

## Why H2 is enough

The resolver coefficient has the elliptic weight

```text
w_k = 1/(mu + lambda_k) = O(k^-2).
```

The spatial part of a joint derivative contributes at worst order `2` in the cosine mode:

```text
valueCosWeight 0 k = O(1)
valueCosWeight 1 k = O(k)
valueCosWeight 2 k = O(k^2)
```

Combining with H2 decay gives, in the worst case,

```text
O(k^2) * O(k^-2) * O(k^-2) = O(k^-2),
```

which is summable. The zero mode is handled separately as a finite term.

So H2 is enough for the bounded-weight value `C2` majorant. H4 is not needed for this specific value-series `cutoffResolverMajorant_summable`; H4 is needed for stronger spectral/eigenvalue-weighted routes such as resolver `C4` or `lambda_k * |sourceCoeff_k|` summability.

## Minimal lemma chain

Use this implementation order:

1. Prove spatial H2 Neumann certificates for `srcSlice`, `srcSlice1`, and `srcSlice2` on `t >= c/2`.
2. Prove uniform `L1` bounds on their weak second derivatives on the same halfline.
3. Apply `intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound` to get direct coefficient envelopes `E_m(k)`.
4. Prove time-derivative bounds for the cutoff resolver coefficient by Leibniz: derivatives can hit the cutoff and the source coefficient; each term is bounded by `cutoffDerivBound * w_k * E_m(k)`.
5. Prove the `iSup` majorant is bounded by a concrete finite sum of `valueCosWeight ell k * w_k * E_m(k)` with `ell <= 2`.
6. Prove summability term-by-term using the `O(k^-2)` worst-case estimate.

## Final answer

Do not try to derive IBP decay from `cutoffResolverCoeff_contDiff_two`. Instead, extract the spatial regularity facts that underlie the source slices directly: spatial `C2`, Neumann endpoint data, and uniform `L1` bounds. That gives `IntervalWeakH2Neumann` and the quadratic IBP decay without `PhysicalResolverJointC2Data`. This is the right direct replacement for the majorant summability proof.
