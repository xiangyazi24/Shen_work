# Q1286 (cron3): eigenvalue summability tools

## Repo-state note

This note is committed to the requested branch `chatgpt-scratch`.  The code containing the target sorry in `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean` is not present on the current `chatgpt-scratch` tree: that path 404s there.  The searched/default tree is `main` at `4745b057cf50749ed0945007f178b54c2b5178a3`; `chatgpt-scratch` is at `d496dddd0e5438dccbf350f69faafecf284b7a93` and is diverged from `main`.  The exact locations below are therefore for the default/indexed tree containing the line-1088 target.

## `intervalWeakH4Neumann_eigenvalue_L1_summable`

File:

```text
ShenWork/PDE/IntervalSourceDecayQuantitative.lean
```

Starts at line 221 in the default/indexed tree.

Namespace:

```lean
namespace ShenWork.IntervalSourceDecayQuantitative
```

Full name:

```lean
ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
```

Exact signature:

```lean
theorem intervalWeakH4Neumann_eigenvalue_L1_summable
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|) := by
```

Adjacent input theorem in the same file:

```lean
theorem intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv)
    {B₂ : ℝ} (hB₂ : (∫ x in (0:ℝ)..1, |hf''.secondDeriv x|) ≤ B₂) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B₂ / ((k : ℝ) * Real.pi) ^ 4 := by
```

## `resolverSourceCoeff_re_eq_cosineCoeffs`

File:

```text
ShenWork/Paper2/IntervalDomainLogisticWeakH2Adapter.lean
```

Starts at line 185 in the default/indexed tree.

Namespace:

```lean
namespace ShenWork.IntervalDomainLogisticWeakH2Adapter
```

Full name:

```lean
ShenWork.IntervalDomainLogisticWeakH2Adapter.resolverSourceCoeff_re_eq_cosineCoeffs
```

Exact signature:

```lean
theorem resolverSourceCoeff_re_eq_cosineCoeffs
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    (ShenWork.PDE.intervalNeumannResolverSourceCoeff p u k).re
      = cosineCoeffs (fun x => p.ν * intervalDomainLift u x ^ p.γ) k := by
  simp only [ShenWork.PDE.intervalNeumannResolverSourceCoeff, cosineCoeffs,
    Complex.ofReal_re]
```

## Import note

`IntervalConjugateLevel0BFormSourceOn.lean` already imports `IntervalResolverHighRegularity`, which provides the consumer theorem `intervalResolverLiftR_contDiff_four`.  The two searched lemmas above are in separate modules.  If they are not already available transitively, add:

```lean
import ShenWork.PDE.IntervalSourceDecayQuantitative
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
```

## Use at the line-1088 gap

After

```lean
have hV_C4 : ContDiff ℝ 4 V_cos := by
  apply intervalResolverLiftR_contDiff_four
```

the remaining goal is the source eigenvalue L1 summability:

```lean
Summable (fun k : ℕ =>
  unitIntervalCosineEigenvalue k *
    |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p
        (conjugatePicardIter p u₀ 0 r) k).re|)
```

If the H4 certificates are for the lifted source itself, use:

```lean
have hsrc_cos : Summable (fun k : ℕ =>
    unitIntervalCosineEigenvalue k *
      |cosineCoeffs
        (fun x : ℝ =>
          p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 r) x ^ p.γ) k|) := by
  exact
    ShenWork.IntervalSourceDecayQuantitative
      .intervalWeakH4Neumann_eigenvalue_L1_summable hsrcH2 hsrcH2_second

simpa [
  ShenWork.IntervalDomainLogisticWeakH2Adapter.resolverSourceCoeff_re_eq_cosineCoeffs
] using hsrc_cos
```

Here the expected certificate types are:

```lean
hsrcH2 :
  IntervalWeakH2Neumann
    (fun x : ℝ => p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 r) x ^ p.γ)

hsrcH2_second : IntervalWeakH2Neumann hsrcH2.secondDeriv
```

If the smooth H4 certificate is instead built for `fun x => p.ν * U_cos x ^ p.γ`, the bridge lemma above is not enough by itself.  It rewrites only to the source built from `intervalDomainLift`.  You still need a coefficient-congruence lemma using `hU_agree` on `[0,1]` to identify the cosine coefficients of `intervalDomainLift ...` and `U_cos` before applying the resolver-source bridge.
