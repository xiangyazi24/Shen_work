# Q1885 (cron1) — `sorry2` response for `/tmp/q_cron1_sorry2.txt`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt references:

```text
Q1885 (cron1): cron1 /tmp/q_cron1_sorry2.txt
```

That local `/tmp/...` file is not readable through the GitHub connector, and the delivery rules prohibit using the sandbox, Python/code-interpreter, `/mnt/data`, or any sandbox file. I therefore used only the GitHub connector and inspected the current repository state.

The most likely target is the second local `sorry` in the `hA1_tail` block of:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

namely:

```lean
have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
    |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
  -- srcSlice1(t,x) = νγ * u^{γ-1} * heatDu
  -- |srcSlice1| ≤ νγ * M_sup^{γ-1} * CΔ on [0,1]
  -- ContinuousOn of srcSlice1 on [0,1] from joint continuity
  -- cosineCoeffs_abs_le_of_continuous_bounded → Bsrc = 2 * νγ * M_sup^{γ-1} * CΔ
  sorry
```

This answer is for that hole.

## Important correction

Do **not** prove the pointwise bound with only

```lean
M_sup ^ (p.γ - 1)
```

unless the local context also has `1 ≤ p.γ`. The global `CM2Params` hypothesis is only:

```lean
p.hγ : 0 < p.γ
```

so `p.γ - 1` may be negative. In that case, an upper bound on `u` does **not** give an upper bound on `u^(γ-1)`; one also needs a uniform positive lower bound for `u`.

For the heat semigroup level-0 iterate this lower bound is available from the same compact-minimum + heat-semigroup lower-bound argument used by `heatSemigroup_pos_of_pos`. The robust proof is:

1. choose `m0 = min u₀` on `intervalDomainPoint`, with `0 < m0`;
2. choose `M0 = max ‖u₀‖`, with `m0 ≤ M0`;
3. prove, for every `t > 0` and `x ∈ [0,1]`,
   ```lean
   m0 ≤ intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
   ```
   using `intervalFullSemigroupOperator_lower_bound`;
4. prove the upper bound by the existing `intervalFullSemigroupOperator_Linfty_bound`;
5. bound `y ↦ y^(p.γ - 1)` on the compact interval `[m0, M0]` by compactness;
6. combine that power bound with the already-produced `hDu` bound;
7. pass from a uniform pointwise bound to a cosine-coefficient bound with
   `IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded`.

## Drop-in replacement for `hBsrc`

Paste this in place of the `sorry` body for `hBsrc`. It deliberately recomputes the lower/upper datum bounds locally, so it does not rely on variables introduced in a different `interval_cases` branch.

```lean
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
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

-- This is the replacement body for the local `have hBsrc : ... := by`.
-- It assumes the surrounding context of `IntervalHeatResolverJointC2.lean`, in
-- particular `p u₀ M₀ c hu₀_bound hu₀_cont hu₀_pos hfloor CΔ hCΔ_nn hDu k`.
have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
    |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
  classical
  set u := conjugatePicardIter p u₀ 0

  -- Compact min/max of the positive initial datum.
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, Set.left_mem_Icc.mpr (by norm_num)⟩⟩

  obtain ⟨xmin, _, hmin⟩ := IsCompact.exists_isMinOn isCompact_univ
    Set.univ_nonempty hu₀_cont.continuousOn
  set m0 : ℝ := u₀ xmin
  have hm0_pos : 0 < m0 := hu₀_pos xmin
  have hm0_nonneg : 0 ≤ m0 := le_of_lt hm0_pos

  obtain ⟨xmax, _, hmax⟩ := IsCompact.exists_isMaxOn isCompact_univ
    Set.univ_nonempty hu₀_cont.norm.continuousOn
  set M0 : ℝ := ‖u₀ xmax‖
  have hM0_nonneg : 0 ≤ M0 := norm_nonneg _

  have hu₀_norm_le : ∀ x : intervalDomainPoint, ‖u₀ x‖ ≤ M0 := by
    intro x
    exact hmax (Set.mem_univ x)

  have hlift_abs_le : ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ M0 := by
    intro y
    unfold intervalDomainLift
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · rw [dif_pos hy]
      simpa [Real.norm_eq_abs] using hu₀_norm_le ⟨y, hy⟩
    · rw [dif_neg hy]
      simpa [abs_of_nonneg hM0_nonneg]

  have hlift_lower : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
      m0 ≤ intervalDomainLift u₀ y := by
    intro y hy
    let ypt : intervalDomainPoint := ⟨y, hy⟩
    unfold intervalDomainLift
    rw [dif_pos hy]
    exact hmin (Set.mem_univ ypt)

  have hm0_le_M0 : m0 ≤ M0 := by
    have hx_lift : intervalDomainLift u₀ xmin.1 = u₀ xmin := by
      simp [intervalDomainLift, xmin.2]
    calc
      m0 = intervalDomainLift u₀ xmin.1 := by rw [hx_lift]
      _ ≤ |intervalDomainLift u₀ xmin.1| := le_abs_self _
      _ ≤ M0 := hlift_abs_le xmin.1

  have hlift_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀_cont

  -- Uniform lower and upper bounds for the heat semigroup profile on `[0,1]`.
  have hprofile_lower : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      m0 ≤ intervalDomainLift (u t) x := by
    intro t ht x hx
    have hlower :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_lower_bound
        ht hm0_nonneg hm0_le_M0 hlift_meas hlift_lower hlift_abs_le x
    have hdef : intervalDomainLift (u t) x =
        intervalFullSemigroupOperator t (intervalDomainLift u₀) x := by
      unfold intervalDomainLift
      rw [dif_pos hx]
      simp only [u]
      rfl
    rwa [hdef]

  have hprofile_upper_abs : ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      |intervalFullSemigroupOperator t (intervalDomainLift u₀) x| ≤ M0 :=
    fun t ht x =>
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        ht hM0_nonneg hlift_abs_le x

  have hprofile_upper : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x ≤ M0 := by
    intro t ht x hx
    have hdef : intervalDomainLift (u t) x =
        intervalFullSemigroupOperator t (intervalDomainLift u₀) x := by
      unfold intervalDomainLift
      rw [dif_pos hx]
      simp only [u]
      rfl
    rw [hdef]
    exact le_of_abs_le (hprofile_upper_abs t ht x)

  -- Bound the possibly negative-exponent power `y ↦ y^(γ-1)` on `[m0,M0]`.
  have hpow_cont : ContinuousOn (fun y : ℝ => y ^ (p.γ - 1))
      (Set.Icc m0 M0) := by
    exact continuousOn_id.rpow_const_of_ne (fun y hy =>
      Or.inl (ne_of_gt (lt_of_lt_of_le hm0_pos hy.1)))

  obtain ⟨Bpow0, hBpow0⟩ :=
    (isCompact_Icc (a := m0) (b := M0)).exists_bound_of_continuousOn hpow_cont
  set Bpow : ℝ := max 0 Bpow0
  have hBpow_nonneg : 0 ≤ Bpow := le_max_left _ _

  have hpow_le : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (intervalDomainLift (u t) x) ^ (p.γ - 1) ≤ Bpow := by
    intro t ht x hx
    have hy_mem : intervalDomainLift (u t) x ∈ Set.Icc m0 M0 :=
      ⟨hprofile_lower t ht x hx, hprofile_upper t ht x hx⟩
    have hy_pos : 0 < intervalDomainLift (u t) x :=
      lt_of_lt_of_le hm0_pos (hprofile_lower t ht x hx)
    have hnn : 0 ≤ (intervalDomainLift (u t) x) ^ (p.γ - 1) :=
      Real.rpow_nonneg hy_pos.le _
    have hnorm := hBpow0 (intervalDomainLift (u t) x) hy_mem
    have hle0 : (intervalDomainLift (u t) x) ^ (p.γ - 1) ≤ Bpow0 := by
      rw [← abs_of_nonneg hnn, ← Real.norm_eq_abs]
      exact hnorm
    exact hle0.trans (le_max_right 0 Bpow0)

  -- The pointwise bound for `srcSlice1`.
  set Bpt : ℝ := p.ν * p.γ * Bpow * CΔ
  have hBpt_nonneg : 0 ≤ Bpt := by
    unfold Bpt
    positivity

  refine ⟨2 * Bpt, fun t ht_tail => ?_⟩
  have ht_pos : 0 < t := by linarith

  -- Continuity of the slice comes from `heatSemigroup_d0`'s joint continuity of `srcSlice1`.
  have hsrc_cont : ContinuousOn
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t)
      (Set.Icc (0 : ℝ) 1) := by
    obtain ⟨δ, hδ, _hcont0, _hdiff0, hcd⟩ :=
      heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hfloor t ht_pos
    have ht_mem : t ∈ Set.Icc (t - δ) (t + δ) :=
      ⟨by linarith, by linarith⟩
    simpa [Function.uncurry] using
      hcd.comp (continuousOn_const.prod continuousOn_id)
        (fun x hx => Set.mk_mem_prod ht_mem hx)

  have hsrc_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t x| ≤ Bpt := by
    intro x hx
    have hu_pos : 0 < intervalDomainLift (u t) x :=
      lt_of_lt_of_le hm0_pos (hprofile_lower t ht_pos x hx)
    have hpow_nonneg : 0 ≤ (intervalDomainLift (u t) x) ^ (p.γ - 1) :=
      Real.rpow_nonneg hu_pos.le _
    have hsmall :
        (intervalDomainLift (u t) x) ^ (p.γ - 1) * |heatDu u₀ t x| ≤
          Bpow * CΔ := by
      exact mul_le_mul (hpow_le t ht_pos x hx) (hDu t ht_tail x)
        hCΔ_nn hpow_nonneg
    unfold srcSlice1
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_pos p.hν, abs_of_pos p.hγ,
      abs_of_nonneg hpow_nonneg]
    calc
      p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * |heatDu u₀ t x|
          = (p.ν * p.γ) *
              ((intervalDomainLift (u t) x) ^ (p.γ - 1) * |heatDu u₀ t x|) := by
              ring
      _ ≤ (p.ν * p.γ) * (Bpow * CΔ) := by
              exact mul_le_mul_of_nonneg_left hsmall
                (mul_nonneg (le_of_lt p.hν) (le_of_lt p.hγ))
      _ = Bpt := by
              unfold Bpt
              ring

  -- Convert the uniform pointwise bound to a cosine coefficient bound.
  simpa [Bpt] using
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hsrc_cont hBpt_nonneg hsrc_bound k

end ShenWork.Paper2.HeatResolverJointC2Direct

end -- noncomputable section
```

## If this fails at the final `simpa`

The only API uncertainty is the exact conclusion of

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
```

The current file already calls it in the same style in the zeroth-derivative tail proof, so the theorem is in scope. If the final goal after applying it is syntactically one of these variants, use the corresponding closing line:

```lean
-- If the lemma returns exactly `≤ 2 * Bpt`:
simpa [Bpt] using
  ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
    hsrc_cont hBpt_nonneg hsrc_bound k

-- If the lemma returns `≤ (if k = 0 then 1 else 2) * Bpt`:
exact (ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
  hsrc_cont hBpt_nonneg hsrc_bound k).trans (by
    by_cases hk0 : k = 0 <;> simp [hk0, Bpt])

-- If the lemma returns `≤ Bpt` for `k = 0` and `≤ 2*Bpt` for positive modes:
exact (ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
  hsrc_cont hBpt_nonneg hsrc_bound k).trans (by positivity)
```

## Why this is the right local proof

The key mathematical point is the exponent `p.γ - 1`. The naive intended proof in the comment works only in a hidden `γ ≥ 1` subcase. The robust proof above works under the actual `CM2Params` field `p.hγ : 0 < p.γ` by bounding `u` from both sides:

```lean
m0 ≤ u(t,x) ≤ M0
```

and then using compactness of `[m0, M0]` to get a uniform bound for `u^(γ-1)`. That makes `hBsrc` independent of any unstated gamma-lower-bound hypothesis and keeps the direct-tail argument faithful to the current parameter structure.

## Relation to the previous Q1866 recommendation

If Q1866's recommendation is adopted, the whole direct-tail `BddAbove` section is removed or bypassed in favor of the existing `PhysicalResolverJointC2Data` explicit-majorant path. In that case this `hBsrc` proof is unnecessary. But if the current direct route is retained, this is the correct way to close the second local sorry without smuggling in `1 ≤ p.γ`.
