# Q1507 (cron2) — bridge from heat cosine series to `intervalDomainLift (conjugatePicardIter … 0 t)`

Static GitHub-connector response only. I did **not** run Lean locally, and I did **not** use Python, code-interpreter, sandbox, or `/mnt/data`.

## Bottom line

The bridge already exists. For the level-0 heat slice, use:

```lean
ShenWork.IntervalPicardLevel0SourceTimeC1On.heatSlice_profile_eq_heatValue
```

It states, on `x ∈ Icc 0 1`, that the lifted level-0 heat iterate equals the cosine heat value:

```lean
intervalDomainLift (picardIter p u₀ 0 σ) x =
  unitIntervalCosineHeatValue σ (heatCoeff u₀) x
```

where

```lean
heatCoeff u₀ = cosineCoeffs (intervalDomainLift u₀)
```

Internally this theorem uses the better subtype-continuity bridge:

```lean
ShenWork.IntervalSpectralSubtypeAdapter
  .intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
```

That is the right theorem for positive initial data on `[0,1]`, because it avoids requiring global continuity of the zero extension `intervalDomainLift u₀`.

For `conjugatePicardIter p u₀ 0`, the level-0 definition is the same heat semigroup slice: `conjugatePicardIter p u₀ 0` is definitionally the pure heat semigroup, and the repo explicitly records the level-0 conjugate/nonconjugate coefficient equalities by `rfl` in `IntervalConjugateLevel0BFormSourceOn.lean`.

So the route is:

```text
intervalDomainLift (conjugatePicardIter p u₀ 0 t)
  = intervalFullSemigroupOperator t (intervalDomainLift u₀)       -- by level-0 definition, on Icc
  = unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift u₀))
                                                                  -- subtype adapter / heatSlice_profile_eq_heatValue
  = the cosine series used by heatSemigroup_contDiff_four          -- definitional unfolding
```

## Exact lemmas found

### 1. Subtype-continuity bridge, closed interval version

File:

```text
ShenWork/PDE/IntervalSpectralSubtypeAdapter.lean
```

The theorem is:

```lean
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
    {t : ℝ} (ht : 0 < t) {f : intervalDomainPoint → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs (intervalDomainLift f) n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t (intervalDomainLift f) x =
      unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x
```

This is the safest low-level bridge. It was added precisely because the older closed-interval spectral identity requires `Continuous (intervalDomainLift f)`, which is false for positive boundary data. The adapter proves the identity by passing through `intervalDomainConstExtend f`, which is globally continuous and agrees with `intervalDomainLift f` on `[0,1]`.

### 2. Underlying full-kernel clean identity

File:

```text
ShenWork/PDE/IntervalFullKernelSpectralClean.lean
```

The lower-level theorem is:

```lean
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

Do **not** use this directly with `f = intervalDomainLift u₀` unless you actually have global continuity of that lift. For positive boundary data, use the subtype adapter above.

### 3. Already-packaged level-0 heat profile bridge

File:

```text
ShenWork/Paper2/IntervalPicardLevel0SourceTimeC1On.lean
```

The theorem is:

```lean
theorem heatSlice_profile_eq_heatValue
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {σ x M₀ : ℝ} (hσ : 0 < σ) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (picardIter p u₀ 0 σ) x =
      unitIntervalCosineHeatValue σ (heatCoeff u₀) x
```

Its proof is exactly the bridge you want:

```lean
have hlift : intervalDomainLift (picardIter p u₀ 0 σ) x =
    intervalFullSemigroupOperator σ (intervalDomainLift u₀) x := by
  simp only [intervalDomainLift, picardIter, dif_pos hx]
rw [hlift]
exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
  hσ hu₀_cont hu₀_bound hx
```

This is the best theorem to reuse if your target has `picardIter p u₀ 0`.

### 4. Conjugate level-0 is definitionally the same base heat slice

File:

```text
ShenWork/Paper2/IntervalConjugatePicard.lean
```

Definition:

```lean
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x
```

File:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

The file comments and theorems record the important fact:

```lean
conjugatePicardIter p u₀ 0
```

is definitionally the level-0 heat slice, and several level-0 coefficient equalities close by `rfl`, for example:

```lean
theorem conjChemDivCoeffs_level0_eq (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s : ℝ) (k : ℕ) :
    coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s k =
    coupledChemDivSourceCoeffs p (picardIter p u₀ 0) s k := by
  rfl
```

So if your goal mentions `conjugatePicardIter p u₀ 0`, either unfold it directly or `simpa` through the packaged `picardIter` lemma if Lean accepts the definitional equality.

## How this plugs into `hsliceC2`

For the profile component, the proof should not try to reason from the kernel directly. First build a global `ContDiff` fact for the cosine series, then transfer it to the lifted profile by equality on `Icc 0 1`.

Skeleton:

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalSpectralSubtypeAdapter
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff heatSlice_profile_eq_heatValue)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.Paper2.HeatSemigroupHighRegularity (heatSemigroup_contDiff_four)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupProfileBridge

/-- Bridge `heatSemigroup_contDiff_four` to the lifted level-0 conjugate heat profile.
This is the profile part needed before applying the `rpow`/product chain for
`srcSlice`, `srcSlice1`, `srcSlice2`. -/
theorem conjugateLevel0_profile_contDiffOn_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ t : ℝ}
    (ht : 0 < t)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀) :
    ContDiffOn ℝ 2
      (fun x : ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
      (Icc (0 : ℝ) 1) := by
  -- 1. The cosine heat series is globally C⁴, hence globally C².
  have hseries4 : ContDiff ℝ 4
      (fun x => ∑' k,
        (Real.exp (-t * unitIntervalCosineEigenvalue k) *
          cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x) :=
    heatSemigroup_contDiff_four hu₀_bound ht

  have hseries2 : ContDiff ℝ 2
      (fun x => unitIntervalCosineHeatValue t (heatCoeff u₀) x) := by
    -- `unitIntervalCosineHeatValue` is definitionally the same cosine series.
    -- The exact simp set may need the local imports/namespaces in your file.
    simpa [heatCoeff, unitIntervalCosineHeatValue,
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineHeatPointWeight,
      unitIntervalCosineEigenvalue, cosineMode] using
      hseries4.of_le (by norm_num : (2 : ℕ∞) ≤ 4)

  -- 2. On `[0,1]`, the lifted conjugate level-0 profile is the heat value.
  have heq : Set.EqOn
      (fun x : ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
      (fun x : ℝ => unitIntervalCosineHeatValue t (heatCoeff u₀) x)
      (Icc (0 : ℝ) 1) := by
    intro x hx
    -- Either use direct unfolding of `conjugatePicardIter`, or route through
    -- `heatSlice_profile_eq_heatValue` if the target has `picardIter`.
    have hlift : intervalDomainLift (conjugatePicardIter p u₀ 0 t) x =
        intervalFullSemigroupOperator t (intervalDomainLift u₀) x := by
      simp [conjugatePicardIter, intervalDomainLift, hx]
    rw [hlift]
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      ht hu₀_cont hu₀_bound hx

  -- 3. Transfer `ContDiffOn` across equality on the target set.
  exact hseries2.contDiffOn.congr (fun x hx => (heq x hx).symm)

end ShenWork.Paper2.HeatSemigroupProfileBridge
```

If Lean has trouble simplifying `unitIntervalCosineHeatValue`, avoid the definitional unfold and use the already-proved C² theorem for heat values instead:

```lean
have hseries2 : ContDiff ℝ 2
    (fun x => unitIntervalCosineHeatValue t (heatCoeff u₀) x) :=
  (ShenWork.IntervalDomainRegularityBootstrap
    .unitIntervalCosineHeatValue_contDiff_two ht hu₀_bound)
```

This gives only `C²`, but `hsliceC2` only asks for `ContDiffOn ℝ 2`, so it is enough for the profile. Use `heatSemigroup_contDiff_four` only when you actually need the fourth-spatial-derivative/H4 tower.

## Existing proof pattern to copy

The closest already-written pattern is in:

```text
ShenWork/Paper2/IntervalHomogeneousG2Base.lean
```

Inside `hG2base_of_gate`, the proof constructs a local equality:

```lean
have hEq : intervalDomainLift (picardIter p u₀ 0 σ) =ᶠ[nhds x]
    (fun y => unitIntervalCosineHeatValue σ a y) := by
  filter_upwards [hmem] with y hy
  have hyIcc : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
  have hlift : intervalDomainLift (picardIter p u₀ 0 σ) y
      = intervalFullSemigroupOperator σ (intervalDomainLift u₀) y := by
    simp only [intervalDomainLift, picardIter, dif_pos hyIcc]
  rw [hlift]
  exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
    hσ hu₀_cont hu₀_bound hyIcc
```

Then it differentiates through that local equality:

```lean
have hd2 : deriv (deriv (intervalDomainLift (picardIter p u₀ 0 σ))) x
    = deriv (deriv (fun y => unitIntervalCosineHeatValue σ a y)) x :=
  (hEq.deriv).deriv_eq
```

For `hsliceC2`, you do not need the local derivative-transfer version if you are proving `ContDiffOn`; use `Set.EqOn` on `Icc` and `ContDiffOn.congr` instead.

## What not to use

There is an older/diagnostic file:

```text
ShenWork/PDE/IntervalSemigroupSpectralForm.lean
```

It warns that a literal bridge for the two-term `normalizedZerothReflectionKernel` is false. That warning is about the older two-term kernel route, not the current full-kernel route. For the present goal, use:

```lean
IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
```

or, better for subtype data:

```lean
IntervalSpectralSubtypeAdapter.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
```

and the packaged level-0 theorem:

```lean
IntervalPicardLevel0SourceTimeC1On.heatSlice_profile_eq_heatValue
```

## Answer to the concrete question

Yes: the bridge exists. The highest-level bridge is `heatSlice_profile_eq_heatValue`; the lower-level bridge is `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont`. There does not need to be a separate theorem named `unitIntervalCosineHeatValue_eq_cosineCoeffSeries`, because `unitIntervalCosineHeatValue` is already the cosine series expression by definition. Use equality on `Icc 0 1` to transport `ContDiffOn` from the cosine heat value/series to `intervalDomainLift (conjugatePicardIter p u₀ 0 t)`.
