# Q1903 (cron1) — `ContinuousOn` response for `/tmp/q_cron1_continuouson.txt`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt references:

```text
Q1903 (cron1): cron1 /tmp/q_cron1_continuouson.txt
```

That local `/tmp/...` file is not readable through the GitHub connector, and the delivery rules prohibit using the sandbox, Python/code-interpreter, `/mnt/data`, or any sandbox file. I therefore used only the GitHub connector and inspected the current repository state.

The likely target is the `ContinuousOn` subgoal inside the remaining `hBsrc` sorry in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

Current local context around the hole is:

```lean
have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
    |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
  -- Same pattern as i=0: cosineCoeffs_abs_le_of_continuous_bounded
  -- Need: ContinuousOn + pointwise bound of srcSlice1 on [0,1]
  sorry
```

The `ContinuousOn` part should **not** be rebuilt manually by expanding `srcSlice1`. The repository already proves exactly the needed slab continuity in `heatSemigroup_d0`:

```lean
ContinuousOn
  (Function.uncurry (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)))
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
```

At a fixed positive time `t`, compose that slab result with the map `x ↦ (t, x)`.

## Drop-in helper lemma

Add this helper in namespace `ShenWork.Paper2.HeatResolverJointC2Direct`, near the other utility lemmas in `IntervalHeatResolverJointC2.lean`.

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param)
open ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  (cosineCoeffs_continuousOn_of_jointContinuousOn_Icc)
open ShenWork.IntervalResolverJointC2Physical
  (boundedWeightJointTerm boundedWeightJointMajorant
   boundedWeightJointTerm_contDiff boundedWeightJointTerm_iteratedFDeriv_le)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data)
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
  (norm_iteratedFDeriv_comp_fst_le)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatD2u heatSemigroup_d0 heatSemigroup_d1)
open ShenWork.IntervalResolverSpectralJointC2Cutoff (smoothRightCutoff
  smoothRightCutoff_contDiff smoothRightCutoff_eq_zero_of_le
  smoothRightCutoff_eq_one_of_ge smoothRightCutoff_eventually_eq_one)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Fixed-time continuity on `[0,1]` of the first source time-derivative slice
for the heat semigroup base iterate.

This packages the standard move: obtain the joint slab continuity from
`heatSemigroup_d0`, then restrict it to the fixed-time slice by composing with
`x ↦ (t, x)`. -/
private theorem heatLevel0_srcSlice1_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) :
    ContinuousOn
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
      (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨δ, hδ, _hsrc, _hderiv, hsrc1_joint⟩ :=
    heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor t ht
  have ht_mem : t ∈ Set.Icc (t - δ) (t + δ) := by
    exact ⟨by linarith, by linarith⟩
  simpa [Function.uncurry] using
    hsrc1_joint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mem_prod.mpr ⟨ht_mem, hx⟩)

end ShenWork.Paper2.HeatResolverJointC2Direct

end -- noncomputable section
```

## If `prodMk` does not elaborate in this file

Some files in this repository use `continuousOn_const.prodMk continuousOn_id`, but if this exact form does not elaborate under the local namespace/import state, replace the last four lines by the explicit `prod` version:

```lean
  have hmap : ContinuousOn (fun x : ℝ => (t, x)) (Set.Icc (0 : ℝ) 1) := by
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => t) (Set.Icc (0 : ℝ) 1)).prod
      continuousOn_id
  have hmaps : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (t, x) ∈ Set.Icc (t - δ) (t + δ) ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact Set.mem_prod.mpr ⟨ht_mem, hx⟩
  simpa [Function.uncurry] using hsrc1_joint.comp hmap hmaps
```

This is definitionally the same proof; it merely avoids relying on the `prodMk` projection helper.

## Use inside `hBsrc`

Inside the `hBsrc` proof, once the local branch has:

```lean
have ht_pos : 0 < t := by linarith
```

replace the continuity subproof with:

```lean
have hsrc_cont : ContinuousOn
    (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
    (Set.Icc (0 : ℝ) 1) :=
  heatLevel0_srcSlice1_continuousOn_Icc
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor ht_pos
```

Then `hsrc_cont` is exactly the continuity input wanted by:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
```

## Direct inline version

If you do not want to add a helper lemma, this inline block is the same proof:

```lean
have hsrc_cont : ContinuousOn
    (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
    (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨δt, hδt, _hsrc, _hderiv, hsrc1_joint⟩ :=
    heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor t ht_pos
  have ht_mem : t ∈ Set.Icc (t - δt) (t + δt) := by
    exact ⟨by linarith, by linarith⟩
  simpa [Function.uncurry] using
    hsrc1_joint.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mem_prod.mpr ⟨ht_mem, hx⟩)
```

And the fallback inline version is:

```lean
have hsrc_cont : ContinuousOn
    (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
    (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨δt, hδt, _hsrc, _hderiv, hsrc1_joint⟩ :=
    heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor t ht_pos
  have ht_mem : t ∈ Set.Icc (t - δt) (t + δt) := by
    exact ⟨by linarith, by linarith⟩
  have hmap : ContinuousOn (fun x : ℝ => (t, x)) (Set.Icc (0 : ℝ) 1) := by
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => t) (Set.Icc (0 : ℝ) 1)).prod
      continuousOn_id
  have hmaps : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (t, x) ∈ Set.Icc (t - δt) (t + δt) ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact Set.mem_prod.mpr ⟨ht_mem, hx⟩
  simpa [Function.uncurry] using hsrc1_joint.comp hmap hmaps
```

## Why this is the right proof

The local continuity goal is a fixed-time slice of a two-variable function. The repository already has the stronger statement from `heatSemigroup_d0`: joint `ContinuousOn` of `Function.uncurry srcSlice1` on a positive time slab. Once `t > 0`, the slab returned by `heatSemigroup_d0` contains `(t, x)` for every `x ∈ [0,1]`; composing with `x ↦ (t,x)` is the cleanest way to obtain the fixed-time `ContinuousOn` fact.

This also avoids duplicating the fragile product/rpow continuity proof for

```lean
p.ν * p.γ * u(t,x)^(p.γ - 1) * heatDu(t,x)
```

and it keeps the `hBsrc` proof aligned with the already build-verified `d0` infrastructure.
