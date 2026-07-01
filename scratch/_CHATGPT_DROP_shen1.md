# Q2853 (shen1) — endpoint/a.e. bridge for full-window integrated relative Moser

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

Off-limits producer file, not touched:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`

## Visibility note

The GitHub connector-visible branch I inspected still does **not** show the newest local names:

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne_const
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne
relativeMoser_hrelInt_strictInterior
```

The connector-visible `P3MoserIntegratedClosure.lean` does show the older strict-interior relative-Moser lemmas and the key integrability/nonnegativity helpers:

```lean
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
Icc_subset_uIcc_zero_T_of_endpoint_memberships
intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
intervalIntegrable_max_one_of_intervalIntegrable
intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
```

So the route below is written against your local compiled names plus these verified surrounding APIs.

## Verdict

The full closed-window `hrelInt` should be derivable from pointwise

```lean
RelativeMoserInterpolationBefore D u T rho p0
```

plus

```lean
IntegratedMoserFirstCrossingRegularity D u T p0
```

by an endpoint/a.e. argument. This is better than using an approximation/limit argument on `[a+δ,b-δ]`.

The key observation is that for `a ≤ b`, interval integrals over `a..b` are set integrals over `Set.Ioc a b`. If

```lean
a ∈ Set.Icc 0 T
b ∈ Set.Icc a T
```

then almost every `s ∈ Set.Ioc a b` satisfies `0 < s ∧ s < T`: the left endpoint is excluded by `Ioc`, and the only possible right-endpoint failure is the singleton `{T}`.

## Lemmas to grep/use

Likely Mathlib/Repo names to try first:

```lean
intervalIntegral.integral_of_le
intervalIntegrable_iff_integrableOn_Ioc_of_le
MeasureTheory.integral_mono_ae
intervalIntegral.integral_mono_ae        -- try this first if present
MeasureTheory.ae_restrict_iff'          -- in repo used as `ae_restrict_iff'`
measurableSet_Ioc
measure_mono_null
Real.volume_singleton                   -- or `by simp` for singleton null
intervalIntegral.integral_add
intervalIntegral.integral_const_mul
```

The repo already uses this endpoint-null pattern in `IntervalAgmonInterpolation.lean`:

```lean
rw [Set.uIoc_of_le ...]
refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
```

Use the same pattern with `{T}` instead of `{1}`.

## Step 1: endpoint/null-set lemma

Put this in `ShenWork/PDE/P3MoserIntegratedClosure.lean` near `Icc_subset_uIcc_zero_T_of_endpoint_memberships`.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- On a closed Moser window `[a,b] ⊆ [0,T]`, almost every point of the interval
integral domain `Ioc a b` is a strict interior time.  The left endpoint is
excluded by `Ioc`; the only possible right endpoint failure is the singleton
`{T}`. -/
theorem ae_restrict_Ioc_strictInterior_of_Icc_endpoints
    {T a b : ℝ}
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), 0 < s ∧ s < T := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  refine (MeasureTheory.ae_iff).2 ?_
  have hbad_subset :
      {s : ℝ | s ∈ Set.Ioc a b ∧ ¬ (0 < s ∧ s < T)} ⊆ ({T} : Set ℝ) := by
    intro s hs
    rcases hs with ⟨hsIoc, hbad⟩
    have hs_pos : 0 < s := lt_of_le_of_lt haT.1 hsIoc.1
    have hs_le_T : s ≤ T := le_trans hsIoc.2 hbT.2
    push_neg at hbad
    rcases hbad with hs_nonpos | hT_le_s
    · exact False.elim ((not_le_of_gt hs_pos) hs_nonpos)
    · exact le_antisymm hs_le_T hT_le_s
  exact measure_mono_null hbad_subset (by simp)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

If Lean complains about namespace resolution, try fully qualified names:

```lean
Set.Ioc
MeasureTheory.volume
MeasureTheory.ae_restrict_iff'
MeasureTheory.measure_mono_null
```

The theorem should also work when `a = b` or `a = T`; then `Ioc a b` is empty and the proof still goes through.

## Step 2: an a.e. interval-integral monotonicity helper

If `intervalIntegral.integral_mono_ae` exists in this Mathlib version, use it directly. If not, add a local helper reducing interval integrals to set integrals over `Ioc`.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Monotonicity of interval integrals from an a.e. inequality on the `Ioc`
interval-integral domain.  This is a local fallback if
`intervalIntegral.integral_mono_ae` is not available under that name. -/
theorem intervalIntegral_integral_mono_ae_Ioc
    {a b : ℝ} {F R : ℝ → ℝ}
    (hab : a ≤ b)
    (hF_int : IntervalIntegrable F volume a b)
    (hR_int : IntervalIntegrable R volume a b)
    (hFR_ae : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), F s ≤ R s) :
    ∫ s in a..b, F s ≤ ∫ s in a..b, R s := by
  rw [intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_of_le hab]
  have hF_on : IntegrableOn F (Set.Ioc a b) volume := by
    rwa [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hR_on : IntegrableOn R (Set.Ioc a b) volume := by
    rwa [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact MeasureTheory.integral_mono_ae hF_on hR_on hFR_ae

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

If the final line fails because `integral_mono_ae` wants `AEStronglyMeasurable`/`Integrable` rather than `IntegrableOn`, rewrite the two set integrals as integrals against `volume.restrict (Set.Ioc a b)` and use:

```lean
exact MeasureTheory.integral_mono_ae hF_on.integrable hR_on.integrable hFR_ae
```

or inspect the exact expected type with:

```lean
#check MeasureTheory.integral_mono_ae
#check intervalIntegral.integral_mono_ae
#check intervalIntegral.integral_of_le
#check intervalIntegrable_iff_integrableOn_Ioc_of_le
```

## Step 3: closed-window integrated relative Moser with `∫max(1,Y)`

This is the main bridge. It should be put in `P3MoserIntegratedClosure.lean`, after the strict-interior relative lemmas and after the two helpers above.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Full closed-window integrated relative-Moser estimate.  Endpoint failures are
ignored by the interval-integral `Ioc` domain: the relative-Moser pointwise
estimate is needed only a.e. on the window. -/
theorem relativeMoser_hrelInt_closedWindow_of_regular
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hrho_nonneg : 0 ≤ rho) :
    ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
      ∃ Ceps, 0 ≤ Ceps ∧
        ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          (∫ s in t1..t2,
            integratedMoserEnergy D u (p + rho) s) ≤
          eps * (∫ s in t1..t2,
            integratedMoserGradientEnergy D u p s) +
          Ceps * (∫ s in t1..t2,
            max 1 (integratedMoserEnergy D u p s)) := by
  intro p hp eps heps
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hpoint⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  intro t1 ht1 t2 ht2
  have hab : t1 ≤ t2 := ht2.1
  have hp_rho : p0 ≤ p + rho := le_trans hp (le_add_of_nonneg_right hrho_nonneg)
  have hsub : Set.Icc t1 t2 ⊆ Set.uIcc (0 : ℝ) T :=
    Icc_subset_uIcc_zero_T_of_endpoint_memberships ht1 ht2
  have hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s)
        volume t1 t2 :=
    hreg.power_intervalIntegrable_of_Icc hp_rho hab hsub
  have hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s)
        volume t1 t2 :=
    hreg.gradient_intervalIntegrable_of_Icc hp hab hsub
  have hYmax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
        volume t1 t2 :=
    hreg.maxOneEnergy_intervalIntegrable_of_Icc hp hab hsub
  let R : ℝ → ℝ := fun s =>
    eps * integratedMoserGradientEnergy D u p s +
      Ceps * max (1 : ℝ) (integratedMoserEnergy D u p s)
  have hR_int : IntervalIntegrable R volume t1 t2 := by
    dsimp [R]
    exact (hG_int.const_mul eps).add (hYmax_int.const_mul Ceps)
  have hae_strict := ae_restrict_Ioc_strictInterior_of_Icc_endpoints ht1 ht2
  have hpoint_ae :
      ∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)),
        integratedMoserEnergy D u (p + rho) s ≤ R s := by
    filter_upwards [hae_strict] with s hs
    rcases hs with ⟨hs0, hsT⟩
    have hrel_s := hpoint s hs0 hsT
    have hY_le_max :
        integratedMoserEnergy D u p s ≤
          max (1 : ℝ) (integratedMoserEnergy D u p s) :=
      le_max_right _ _
    have hCY_le :
        Ceps * integratedMoserEnergy D u p s ≤
          Ceps * max (1 : ℝ) (integratedMoserEnergy D u p s) :=
      mul_le_mul_of_nonneg_left hY_le_max hCeps_nonneg
    dsimp [R, integratedMoserEnergy, integratedMoserGradientEnergy] at hrel_s ⊢
    linarith
  have hmono :
      ∫ s in t1..t2, integratedMoserEnergy D u (p + rho) s ≤
        ∫ s in t1..t2, R s :=
    intervalIntegral_integral_mono_ae_Ioc hab hZ_int hR_int hpoint_ae
  have hR_eq :
      (∫ s in t1..t2, R s) =
        eps * (∫ s in t1..t2,
          integratedMoserGradientEnergy D u p s) +
        Ceps * (∫ s in t1..t2,
          max 1 (integratedMoserEnergy D u p s)) := by
    dsimp [R]
    rw [intervalIntegral.integral_add
      (hG_int.const_mul eps) (hYmax_int.const_mul Ceps)]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
  exact le_trans hmono (by rw [hR_eq])

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

If your local lemma `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_maxOne` already has almost this target but strict windows, do **not** try to call it directly at endpoints. The a.e. proof above avoids strict-window hypotheses by integrating the original pointwise `hrel` on `Ioc`.

## Step 4: package as the `hrelInt` frontier consumed by the coefficient wrapper

If your coefficient wrapper expects exactly a named full-window `hrelInt` predicate, add an abbreviation rather than repeating the long quantifiers at every call site.

```lean
def IntegratedRelativeMoserFullWindow
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
    ∃ Ceps, 0 ≤ Ceps ∧
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        (∫ s in t1..t2,
          integratedMoserEnergy D u (p + rho) s) ≤
        eps * (∫ s in t1..t2,
          integratedMoserGradientEnergy D u p s) +
        Ceps * (∫ s in t1..t2,
          max 1 (integratedMoserEnergy D u p s))

theorem integratedRelativeMoserFullWindow_of_regular_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hrho_nonneg : 0 ≤ rho) :
    IntegratedRelativeMoserFullWindow D u T rho p0 :=
  relativeMoser_hrelInt_closedWindow_of_regular hreg hrel hrho_nonneg
```

Then the coefficient wrapper call can consume:

```lean
(hrelInt := integratedRelativeMoserFullWindow_of_regular_relative hreg hrel hrho_nonneg)
```

or just pass the theorem output directly if no predicate abbreviation is used.

## If `MeasureTheory.integral_mono_ae` is too painful

The smallest honest frontier predicate is exactly `IntegratedRelativeMoserFullWindow` above. It is not mathematically suspicious: it says the pointwise relative-Moser estimate has already been integrated over closed windows. It cleanly feeds your existing coefficient absorption wrapper and avoids polluting producer-side files.

But I would try the a.e. bridge first. It is local, uses no producer file, and the only real Mathlib friction is the exact monotonicity theorem name/signature.

## Hidden pitfalls

1. **Do not use strict-window lemmas at endpoints.**  Applying a strict lemma with `a = 0` or `b = T` is false at the type level. Use a.e. on `Ioc` or keep a full-window frontier.

2. **Need `rho ≥ 0`.**  To get power integrability for `p+rho` from `hreg.powerTimeIntegrable`, the proof needs `p0 ≤ p+rho`. From `p0 ≤ p`, this follows from `0 ≤ rho`. In bootstrap contexts you likely have `0 < rho`; pass `hrho.le`.

3. **The right endpoint `T` is the only exceptional point.**  For `s ∈ Ioc t1 t2`, `s > t1 ≥ 0`, so `0 < s` is automatic. Since `s ≤ t2 ≤ T`, the only way to fail `s < T` is `s = T`, a null singleton.

4. **Use `max 1 Y`, not raw `Y`, for the coefficient wrapper.**  The full-window relative estimate with `Ceps * ∫max(1,Y)` is stronger/easier to feed downstream than one with `Ceps * ∫Y`, and it does not need energy nonnegativity.

5. **Do not edit `P3MoserHighExcursionProducer.lean`.**  This endpoint/a.e. bridge belongs in closure/plumbing, not in Zinan-owned producer code.

## Bottom line

The closed-window `hrelInt` should be provable now from:

```lean
IntegratedMoserFirstCrossingRegularity D u T p0
RelativeMoserInterpolationBefore D u T rho p0
0 ≤ rho
```

via `Ioc`/a.e. endpoint removal. Add the small `ae_restrict_Ioc_strictInterior_of_Icc_endpoints` helper, then either use `intervalIntegral.integral_mono_ae` if available, or use `intervalIntegral.integral_of_le` plus `MeasureTheory.integral_mono_ae` on `volume.restrict (Set.Ioc t1 t2)`. If Mathlib monotonicity friction is too high, introduce `IntegratedRelativeMoserFullWindow` as the honest temporary frontier and feed that into the coefficient absorption wrapper.
