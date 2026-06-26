# Q666 (cron2): `chemDivSource_weakH2_of_cosineRep` positivity hypothesis

Static repo inspection only; I did not run a Lean build.

## Executive verdict

The simplest fix is **not** to modify `V_cos` by `max`, and probably not to rewrite the whole proof to a genuinely local `ContDiffOn` version.

Instead, weaken the public hypothesis of

```lean
chemDivSource_weakH2_of_cosineRep
```

from global positivity

```lean
(hv_cos_pos : ∀ x, (0 : ℝ) < 1 + V_cos x)
```

to interval positivity

```lean
(hv_cos_pos_Icc : ∀ x ∈ Icc (0 : ℝ) 1, (0 : ℝ) < 1 + V_cos x)
```

**but then immediately recover the old global `hv_cos_pos` inside the proof using the already-required symmetry hypotheses**

```lean
(hv_even : ∀ x, V_cos (-x) = V_cos x)
(hv_symm1 : ∀ x, V_cos (2 - x) = V_cos x)
```

Those hypotheses imply period `2` and fold every `x : ℝ` into `[0,1]`.  So for the theorem as currently shaped, `[0,1]` positivity plus symmetry is enough to supply the old global positivity proof term and leave the rest of the proof essentially unchanged.

In particular, if `V_cos = intervalResolverLiftR p u`, the concern “it may go below `-1` outside `[0,1]`” should not happen once it is known nonnegative on `[0,1]`: `intervalResolverLiftR` is a cosine-series extension with period `2` and reflection symmetry.

## Why not `max(resolver, 0)` outside `[0,1]`?

Do **not** use

```lean
max (intervalResolverLiftR p u x) 0
```

as the global `V_cos` replacement.  It is not a good Lean/analysis fix here:

1. It will generally not be `C⁴` at the gluing/contact set.
2. It may fail the even/reflection hypotheses unless the modification is built symmetrically and periodically.
3. Even if made symmetric, a `max` clamp creates only low regularity.  The theorem needs `hv_cos : ContDiff ℝ 4 V_cos`.
4. A smooth cutoff/gluing construction preserving agreement, positivity, `C⁴`, evenness, and reflection is far more work than needed.

## Why not fully localize the ContDiff proof?

It is mathematically true that the flux only needs positivity on `[0,1]` if the target is only `ContDiffOn`/weak-`H²` on `[0,1]`.  But the current proof is not written that way.

Current code in `ShenWork/Paper2/IntervalChemDivSpatialC2.lean` has:

```lean
theorem chemFlux_contDiff_three
    {β : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hv : ContDiff ℝ 4 v)
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x)
    (hβnn : 0 ≤ β) :
    ContDiff ℝ 3 (chemFluxFun β u v)
```

and then:

```lean
theorem chemFluxDeriv_contDiff_two
    ...
    (hv_pos : ∀ x, (0 : ℝ) < 1 + v x) ... :
    ContDiff ℝ 2 (deriv (chemFluxFun β u v))
```

`chemDivSource_weakH2_of_cosineRep` uses those global facts to get:

```lean
have hF_C2 : ContDiff ℝ 2 F := ...
have hF_C2on : ContDiffOn ℝ 2 F (Icc (0 : ℝ) 1) := hF_C2.contDiffOn
have hF'_cont : Continuous (deriv F) := ...
```

and it also uses global C¹ parity helpers to prove the endpoint Neumann facts.

A true local rewrite would require replacing those global facts with `ContDiffOn`/`ContinuousOn` statements and reworking the endpoint parity arguments locally near `0` and `1`.  That is doable but more invasive.

## Minimal patch shape

Add a small folding lemma, either generic or `intervalResolverLiftR`-specific.

### Generic lemma shape

Something like:

```lean
lemma pos_global_of_pos_Icc_of_even_reflect_one
    {V : ℝ → ℝ}
    (hposI : ∀ x ∈ Icc (0 : ℝ) 1, (0 : ℝ) < 1 + V x)
    (heven : ∀ x, V (-x) = V x)
    (hreflect : ∀ x, V (2 - x) = V x) :
    ∀ x, (0 : ℝ) < 1 + V x := by
  -- 1. derive period 2:
  --    V (x + 2) = V x, from `hreflect (-x)` and `heven x`.
  -- 2. fold arbitrary x modulo period 2 to y ∈ [0,2].
  -- 3. if y ≤ 1, use hposI y.
  -- 4. if 1 ≤ y ≤ 2, use `hreflect y` to replace y by 2-y ∈ [0,1].
```

Then modify `chemDivSource_weakH2_of_cosineRep` like this:

```lean
noncomputable def chemDivSource_weakH2_of_cosineRep
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    {U_cos V_cos : ℝ → ℝ}
    (hu_cos : ContDiff ℝ 4 U_cos)
    (hv_cos : ContDiff ℝ 4 V_cos)
    (hv_cos_pos_Icc : ∀ x ∈ Icc (0 : ℝ) 1, (0 : ℝ) < 1 + V_cos x)
    (h_agree_u : ∀ x ∈ Icc (0 : ℝ) 1, intervalDomainLift u x = U_cos x)
    (h_agree_v : ∀ x ∈ Icc (0 : ℝ) 1, intervalDomainLift v x = V_cos x)
    (hu_even : ∀ x, U_cos (-x) = U_cos x)
    (hv_even : ∀ x, V_cos (-x) = V_cos x)
    (hu_symm1 : ∀ x, U_cos (2 - x) = U_cos x)
    (hv_symm1 : ∀ x, V_cos (2 - x) = V_cos x) :
    IntervalWeakH2Neumann (chemDivLift p u v) := by
  have hv_cos_pos : ∀ x, (0 : ℝ) < 1 + V_cos x :=
    pos_global_of_pos_Icc_of_even_reflect_one hv_cos_pos_Icc hv_even hv_symm1
  -- rest of the existing proof remains the same
```

This changes the caller obligation from impossible/global to the natural interval-domain fact, while preserving the existing global proof downstream.

### `intervalResolverLiftR`-specific route

If you do not want to touch `chemDivSource_weakH2_of_cosineRep`, prove the global `hv_cos_pos` at the call site for

```lean
V_cos := intervalResolverLiftR p u
```

from these facts already in the repo:

```lean
theorem intervalResolverLiftR_even
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (-x) = intervalResolverLiftR p u x

theorem intervalResolverLiftR_reflect_one
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (2 - x) = intervalResolverLiftR p u x

theorem intervalResolverLiftR_periodic
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    intervalResolverLiftR p u (x + 2) = intervalResolverLiftR p u x
```

and the interval-domain positivity theorem:

```lean
theorem intervalNeumannResolverR_nonneg_of_nonneg_source ...
    (xp : intervalDomainPoint) :
    0 ≤ intervalNeumannResolverR p u xp
```

You will also likely want the missing thin bridge lemma:

```lean
lemma intervalResolverLiftR_eq_intervalNeumannResolverR_on_Icc
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalResolverLiftR p u x = intervalNeumannResolverR p u ⟨x, hx⟩ := by
  unfold intervalResolverLiftR intervalNeumannResolverR
  -- should be `tsum_congr`; `cosineMode` and `unitIntervalCosineMode` are the same cos mode.
```

Then:

```lean
have hposI : ∀ x ∈ Icc (0 : ℝ) 1,
    (0 : ℝ) < 1 + intervalResolverLiftR p u x := by
  intro x hx
  rw [intervalResolverLiftR_eq_intervalNeumannResolverR_on_Icc hx]
  have hR : 0 ≤ intervalNeumannResolverR p u ⟨x, hx⟩ :=
    intervalNeumannResolverR_nonneg_of_nonneg_source hf_cont hf_nonneg hf_coeff hâ ⟨x, hx⟩
  linarith

have hpos_global : ∀ x, (0 : ℝ) < 1 + intervalResolverLiftR p u x :=
  pos_global_of_pos_Icc_of_even_reflect_one hposI
    (intervalResolverLiftR_even p u)
    (intervalResolverLiftR_reflect_one p u)
```

## Recommended answer

**Best/simple fix:** weaken the `chemDivSource_weakH2_of_cosineRep` API to interval positivity, but internally reconstruct the old global positivity from `hv_even` + `hv_symm1`.  This avoids the impossible caller obligation while avoiding a large proof rewrite.

**Second-best:** keep the API and prove global positivity at the `intervalResolverLiftR` call site using `intervalResolverLiftR_even`, `intervalResolverLiftR_reflect_one`, `intervalResolverLiftR_periodic`, and the bridge to `intervalNeumannResolverR_nonneg_of_nonneg_source` on `[0,1]`.

**Do not clamp with `max` outside `[0,1]`.**  It breaks the high-regularity/symmetry route and creates a harder smooth-extension problem than the one you are trying to solve.
