# Q1287 / cron1 — exact `intervalResolverLiftR_contDiff_four` signature and line-1087 argument

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Search result

The theorem is in:

```text
ShenWork/Paper2/IntervalResolverHighRegularity.lean
```

Namespace:

```lean
namespace ShenWork.Paper2.IntervalResolverHighRegularity
```

The target caller is in:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

around the block:

```lean
have hV_C4 : ContDiff ℝ 4 V_cos := by
  apply intervalResolverLiftR_contDiff_four
  ...
  sorry
```

## Exact signature

```lean
/-- **The lifted resolver cosine series is C⁴** when the source coefficients
have eigenvalue-weighted ℓ¹ summability.

Route: eigenvalue-weighted ℓ¹ of source ⟹ eigenvalue-squared summability
of resolver (via `resolverCoeff_eigenSq_summable_of_sourceEigenL1`) ⟹ C⁴
(via `cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable`).

The C⁴ engine (`contDiff_tsum_of_eventually` with eigenvalue⁴ majorant) is
the standard cosine-series smoothing tool from
`IntervalParabolicDuhamelGainNonCircular`. -/
theorem intervalResolverLiftR_contDiff_four
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 4 (intervalResolverLiftR p u) := by
  unfold intervalResolverLiftR
  exact ShenWork.Paper2.ParabolicDuhamelGainNonCircular.cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
    (resolverCoeff_eigenSq_summable_of_sourceEigenL1 hsrc)
```

So it has exactly one explicit hypothesis:

```lean
hsrc : Summable (fun k : ℕ =>
  unitIntervalCosineEigenvalue k *
    |(intervalNeumannResolverSourceCoeff p u k).re|)
```

No positivity, continuity, or C⁴ hypothesis is passed directly to `intervalResolverLiftR_contDiff_four`.  Those are only used upstream to prove `hsrc`.

## What goal remains after `apply intervalResolverLiftR_contDiff_four`

At line ~1087, local variables are effectively:

```lean
r : ℝ
hr_pos' : 0 < r
U_cos : ℝ → ℝ
hU_C4 : ContDiff ℝ 4 U_cos
hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
  intervalDomainLift (conjugatePicardIter p u₀ 0 r) x = U_cos x
V_cos := intervalResolverLiftR p (conjugatePicardIter p u₀ 0 r)
```

After:

```lean
apply intervalResolverLiftR_contDiff_four
```

the goal is:

```lean
⊢ Summable (fun k : ℕ =>
    unitIntervalCosineEigenvalue k *
      |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p
          (conjugatePicardIter p u₀ 0 r) k).re|)
```

The current target file already starts the right reduction:

```lean
rw [show (fun k => unitIntervalCosineEigenvalue k *
  |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p
    (conjugatePicardIter p u₀ 0 r) k).re|) =
  (fun k => unitIntervalCosineEigenvalue k *
    |cosineCoeffs (fun x => p.ν * intervalDomainLift
      (conjugatePicardIter p u₀ 0 r) x ^ p.γ) k|) from by
  funext k; congr 1; congr 1
  exact ShenWork.IntervalDomainLogisticWeakH2Adapter.resolverSourceCoeff_re_eq_cosineCoeffs
    p (conjugatePicardIter p u₀ 0 r) k]
```

After that `rw`, the goal is exactly:

```lean
⊢ Summable (fun k : ℕ =>
    unitIntervalCosineEigenvalue k *
      |cosineCoeffs
        (fun x => p.ν * intervalDomainLift
          (conjugatePicardIter p u₀ 0 r) x ^ p.γ) k|)
```

## Exact bridge signature used in the target block

File:

```text
ShenWork/Paper2/IntervalDomainLogisticWeakH2Adapter.lean
```

Signature:

```lean
/-- The resolver source coefficient's real part IS the cosine coefficient of the
power source `ν·u^γ` (both are `unitIntervalNeumannCosineCoeff` of the same lifted
function). -/
theorem resolverSourceCoeff_re_eq_cosineCoeffs
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    (ShenWork.PDE.intervalNeumannResolverSourceCoeff p u k).re
      = cosineCoeffs (fun x => p.ν * intervalDomainLift u x ^ p.γ) k := by
  simp only [ShenWork.PDE.intervalNeumannResolverSourceCoeff, cosineCoeffs,
    Complex.ofReal_re]
```

## The argument that fills the sorry

The argument is a proof of eigenvalue-weighted L¹ summability of the power-source coefficients.  Once you have the depth-2 weak-H² tower

```lean
hf_H2 :
  ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
    (fun x : ℝ => p.ν * intervalDomainLift
      (conjugatePicardIter p u₀ 0 r) x ^ p.γ)

hf''_H2 :
  ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
    hf_H2.secondDeriv
```

the exact argument is:

```lean
exact ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
  hf_H2 hf''_H2
```

This is the whole argument **after** the existing `rw [show ... resolverSourceCoeff_re_eq_cosineCoeffs ...]` in the target file.

## Exact summability theorem used

File:

```text
ShenWork/PDE/IntervalSourceDecayQuantitative.lean
```

Signature:

```lean
/-- **Eigenvalue-weighted L¹ summability** from depth-2 weak H² Neumann tower.
Feeds `resolverCoeff_eigenSq_summable_of_sourceEigenL1` for resolver C⁴. -/
theorem intervalWeakH4Neumann_eigenvalue_L1_summable
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|) := by
  obtain ⟨B₂, _, hB₂⟩ := hf''.second_abs_integral_bound
  have hdecay := intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound hf hf'' hB₂
  -- ... p-series comparison ...
```

## Minimal replacement pattern at line 1087

If the target block already has `hf_H2` and `hf''_H2` in scope, replace the sorry by:

```lean
        exact ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
          hf_H2 hf''_H2
```

In full local shape:

```lean
      have hV_C4 : ContDiff ℝ 4 V_cos := by
        apply intervalResolverLiftR_contDiff_four
        rw [show (fun k => unitIntervalCosineEigenvalue k *
          |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p
            (conjugatePicardIter p u₀ 0 r) k).re|) =
          (fun k => unitIntervalCosineEigenvalue k *
            |cosineCoeffs (fun x => p.ν * intervalDomainLift
              (conjugatePicardIter p u₀ 0 r) x ^ p.γ) k|) from by
          funext k
          congr 1
          congr 1
          exact ShenWork.IntervalDomainLogisticWeakH2Adapter.resolverSourceCoeff_re_eq_cosineCoeffs
            p (conjugatePicardIter p u₀ 0 r) k]
        exact ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
          hf_H2 hf''_H2
```

## What supplies `hf_H2`

The first weak-H² certificate can be built from the heat cosine representation using the existing power-source adapter in:

```text
ShenWork/PDE/IntervalMildSourceDecayHelper.lean
```

Exact signature:

```lean
/-- Construct `IntervalWeakH2Neumann` for a source `g = ν * u ^ γ` from
eigenvalue-summable cosine coefficients of the profile `u` and strict
positivity.  Route: `cosineCoeffSeries_contDiff_two` → `ContDiffOn ℝ 2` of `u`
→ chain rule (`rpow_const_of_ne` for positivity) → `ContDiffOn ℝ 2` of `g`
→ Neumann limits from the cosine series derivatives at endpoints
→ `intervalWeakH2Neumann_of_contDiffOn`. -/
noncomputable def intervalWeakH2Neumann_of_eigenvalue_summable
    {ν γ : ℝ} (hν : 0 < ν) (hγ : 0 < γ)
    {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    IntervalWeakH2Neumann (fun x : ℝ => ν * intervalDomainLift w x ^ γ)
```

At line ~1087 instantiate it with:

```lean
let b : ℕ → ℝ := fun k => Real.exp (-r * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k
let w : intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0 r

have hbc_sum : Summable (fun n : ℕ => unitIntervalCosineEigenvalue n * |b n|) := by
  simpa [b] using
    ShenWork.IntervalSemigroupNeumann.heatCoeff_eigenvalue_summable
      hr_pos' _hu₀_bound

have hagree_w : Set.EqOn (intervalDomainLift w)
    (fun x => ∑' n : ℕ, b n * cosineMode n x) (Icc (0 : ℝ) 1) := by
  intro x hx
  simpa [w, b] using hU_agree x hx

have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1, 0 < intervalDomainLift w x := by
  -- This is the positivity input.  In this line-1087 block, the comment says to
  -- derive it from `_hu₀_nonneg` + positive-somewhere via
  -- `intervalFullSemigroupOperator_pos`, valid for all `r > 0`.
  -- If a heat-floor/strict-positivity lemma is already in scope, use it here.
  sorry

have hf_H2 : ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann
    (fun x : ℝ => p.ν * intervalDomainLift w x ^ p.γ) :=
  ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_eigenvalue_summable
    p.hν p.hγ hbc_sum hagree_w hpos_w
```

## What supplies `hf''_H2`

This is the actual depth-2 part.  The intended construction is:

1. Use `hU_C4` plus strict positivity of `U_cos` to define

```lean
g_smooth : ℝ → ℝ := fun x => p.ν * U_cos x ^ p.γ
```

and prove

```lean
hg_C4 : ContDiff ℝ 4 g_smooth
```

by

```lean
contDiff_const.mul (hU_C4.rpow_const_of_ne hU_ne)
```

2. Use evenness and reflection symmetry of `U_cos` to prove odd derivatives of `g_smooth` vanish at `0` and `1`, giving an `IntervalWeakH2Neumann` certificate for `deriv (deriv g_smooth)`.

3. Transfer that certificate to `hf_H2.secondDeriv` by reusing the same fourth-derivative integrability and proving the weak cosine Laplacian identity from:

```lean
hf_H2.weak_cosine_laplacian k
h_smooth_H2.weak_cosine_laplacian k
intervalCosineLaplacianCoeff_eq_of_contDiffOn k ... g_smooth ...
```

There is already a long block doing exactly this earlier in the same file around the previous `hV_data` branch.  The line-1087 hole should be filled by factoring that block into a local helper that returns:

```lean
hf_H2 : IntervalWeakH2Neumann (fun x => p.ν * intervalDomainLift w x ^ p.γ)
hf''_H2 : IntervalWeakH2Neumann hf_H2.secondDeriv
```

Then the `intervalResolverLiftR_contDiff_four` argument is one line, as above.

## Concise answer

`intervalResolverLiftR_contDiff_four` needs only:

```lean
Summable (fun k => unitIntervalCosineEigenvalue k *
  |(intervalNeumannResolverSourceCoeff p u k).re|)
```

At `IntervalConjugateLevel0BFormSourceOn.lean` line ~1087, after rewriting by
`resolverSourceCoeff_re_eq_cosineCoeffs`, fill the sorry with:

```lean
exact ShenWork.IntervalSourceDecayQuantitative.intervalWeakH4Neumann_eigenvalue_L1_summable
  hf_H2 hf''_H2
```

where `hf_H2` is the weak-H² certificate for `ν · lift(w)^γ`, and `hf''_H2` is the depth-2 weak-H² certificate for `hf_H2.secondDeriv`.

No local `lake build` was run; this drop was produced through the GitHub connector only.
