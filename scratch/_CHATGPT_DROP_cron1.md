# Q2117 (cron1/cron2) — gradient/derivative response for `/tmp/codex_gradient.md`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt references a local file:

```text
/tmp/codex_gradient.md
```

That path is not part of the GitHub repository and is not readable through the GitHub connector. The delivery rules explicitly prohibit using Python, code-interpreter, the sandbox, `/mnt/data`, or any local-file fallback. I therefore used only the GitHub connector.

A connector search for `codex_gradient` found no repository file with that name or content. The repository-visible context for `gradient`/derivative work points to:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

especially the tail part of `cutoffResolverMajorant_bddAbove_direct`, where the proof tries to bound the `i = 1` and `i = 2` time derivatives of

```lean
A t = smoothRightCutoff (c / 2) c t *
  resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

for `t > c + 1`.

## Main point

Do **not** try to solve this as a spatial-gradient estimate. In this file, the derivative being bounded is the **time derivative** of the resolver coefficient. The correct chain is:

```text
A = φ · R
R t = w_k · srcTimeCoeff p u k t
```

For `t > c + 1`, the cutoff is locally `1`, so `A =ᶠ[𝓝 t] R`. Thus the tail bounds reduce to derivative bounds for `R`.

The right identities are:

```text
deriv R t
  = w_k · cosineCoeffs (srcSlice1 p u heatDu t) k

iteratedDeriv 2 R t
  = w_k · cosineCoeffs (srcSlice2 p u heatDu heatD2u t) k
```

where `u = conjugatePicardIter p u₀ 0`. Analytically:

```text
srcSlice  = ν · u^γ
srcSlice1 = ν · γ · u^(γ-1) · u_t
srcSlice2 = ν · γ · (γ-1) · u^(γ-2) · u_t^2
          + ν · γ · u^(γ-1) · u_tt
```

and for the heat semigroup base iterate:

```text
u_t  = heatDu u₀
u_tt = heatD2u u₀
```

So the derivative tail proof needs only:

1. a uniform positive lower bound and upper bound for `u` on `[0,1]`, obtained from positivity of `u₀`, compactness, and heat semigroup lower/L∞ bounds;
2. a uniform bound on `heatDu` for `t > c + 1`;
3. a uniform bound on `heatD2u` for `t > c + 1`;
4. `cosineCoeffs_abs_le_of_continuous_bounded` to convert pointwise source-slice bounds into coefficient bounds.

The previous `summability` fix should be reused twice: once for `heatDu`, and once for `heatD2u`. Use named majorants so Lean does not have to infer the `Summable` sequence.

## File-level imports for the local block

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
```

## Robust local helper: `heatDu` tail bound

This is the first helper needed by the gradient/time-derivative proof. Prefer the `CΔ := ∑' maj` witness to avoid any final `tsum_mul_left` orientation issue.

```lean
have hDu_bound : ∃ CΔ : ℝ, 0 ≤ CΔ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
    |heatDu u₀ t x| ≤ CΔ := by
  have hc1 : 0 < c + 1 := by
    linarith

  let base : ℕ → ℝ := fun n =>
    unitIntervalCosineEigenvalue n *
      Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)
  let maj : ℕ → ℝ := fun n => M₀ * base n
  let CΔ : ℝ := ∑' n : ℕ, maj n

  have hM₀_nonneg : 0 ≤ M₀ :=
    le_trans (abs_nonneg _) (hu₀_bound 0)

  have hbase_summable : Summable base := by
    simpa [base] using
      ShenWork.IntervalMildRegularityBootstrap.unitIntervalCosineEigenvalue_mul_exp_summable
        hc1

  have hmaj_summable : Summable maj := by
    simpa [maj, base, mul_assoc] using hbase_summable.mul_left M₀

  have hbase_nonneg : ∀ n : ℕ, 0 ≤ base n := by
    intro n
    dsimp [base]
    exact mul_nonneg
      (by unfold unitIntervalCosineEigenvalue; positivity)
      (Real.exp_nonneg _)

  have hmaj_nonneg : ∀ n : ℕ, 0 ≤ maj n := by
    intro n
    dsimp [maj]
    exact mul_nonneg hM₀_nonneg (hbase_nonneg n)

  refine ⟨CΔ, by dsimp [CΔ]; exact tsum_nonneg hmaj_nonneg, fun t ht x => ?_⟩

  have ht_pos : 0 < t := by
    linarith

  simp only [heatDu, if_pos ht_pos]
  unfold ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue

  let term : ℕ → ℝ := fun n =>
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight t x n *
      cosineCoeffs (intervalDomainLift u₀) n

  change |∑' n : ℕ, term n| ≤ CΔ

  have hterm_le : ∀ n : ℕ, |term n| ≤ maj n := by
    intro n
    dsimp [term, maj, base]
    unfold ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianPointWeight
    rw [abs_mul, abs_mul, abs_neg]

    have heig_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity

    have hpw_le : |unitIntervalCosineHeatPointWeight t x n| ≤
        Real.exp (-t * unitIntervalCosineEigenvalue n) := by
      unfold unitIntervalCosineHeatPointWeight
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _)

    have hexp_le : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
        Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) := by
      apply Real.exp_le_exp.mpr
      have hmul : (c + 1) * unitIntervalCosineEigenvalue n ≤
          t * unitIntervalCosineEigenvalue n :=
        mul_le_mul_of_nonneg_right (le_of_lt ht) heig_nn
      linarith

    have hcoeff_le : |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀ :=
      hu₀_bound n

    calc
      |unitIntervalCosineEigenvalue n| *
          |unitIntervalCosineHeatPointWeight t x n| *
          |cosineCoeffs (intervalDomainLift u₀) n|
          ≤ unitIntervalCosineEigenvalue n *
              Real.exp (-t * unitIntervalCosineEigenvalue n) * M₀ := by
              rw [abs_of_nonneg heig_nn]
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left hpw_le heig_nn)
                hcoeff_le
                (abs_nonneg _)
                (mul_nonneg heig_nn (Real.exp_nonneg _))
      _ ≤ unitIntervalCosineEigenvalue n *
              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) * M₀ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hexp_le heig_nn)
                hM₀_nonneg
      _ = M₀ *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)) := by
              ring

  exact abs_tsum_le_tsum_of_abs_le
    (f := term) (g := maj) hterm_le hmaj_summable
```

## Robust local helper: `heatD2u` tail bound

Use the same pattern. This is the helper needed for `srcSlice2`.

```lean
have hD2u_bound : ∃ CΔ₂ : ℝ, 0 ≤ CΔ₂ ∧ ∀ t : ℝ, c + 1 < t → ∀ x : ℝ,
    |heatD2u u₀ t x| ≤ CΔ₂ := by
  have hc1 : 0 < c + 1 := by
    linarith

  let base₂ : ℕ → ℝ := fun n =>
    unitIntervalCosineEigenvalue n ^ 2 *
      Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)
  let maj₂ : ℕ → ℝ := fun n => M₀ * base₂ n
  let CΔ₂ : ℝ := ∑' n : ℕ, maj₂ n

  have hM₀_nonneg : 0 ≤ M₀ :=
    le_trans (abs_nonneg _) (hu₀_bound 0)

  have hbase₂_summable : Summable base₂ := by
    simpa [base₂] using
      ShenWork.Paper2.HeatSemigroupJointRegularity.eigenvalue_pow_mul_exp_summable
        2 hc1

  have hmaj₂_summable : Summable maj₂ := by
    simpa [maj₂, base₂, mul_assoc] using hbase₂_summable.mul_left M₀

  have hbase₂_nonneg : ∀ n : ℕ, 0 ≤ base₂ n := by
    intro n
    dsimp [base₂]
    exact mul_nonneg
      (pow_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) _)
      (Real.exp_nonneg _)

  have hmaj₂_nonneg : ∀ n : ℕ, 0 ≤ maj₂ n := by
    intro n
    dsimp [maj₂]
    exact mul_nonneg hM₀_nonneg (hbase₂_nonneg n)

  refine ⟨CΔ₂, by dsimp [CΔ₂]; exact tsum_nonneg hmaj₂_nonneg, fun t ht x => ?_⟩

  have ht_pos : 0 < t := by
    linarith

  simp only [heatD2u, if_pos ht_pos]

  let term₂ : ℕ → ℝ := fun n =>
    unitIntervalCosineEigenvalue n ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue n) *
        cosineCoeffs (intervalDomainLift u₀) n) *
      ShenWork.CosineSpectrum.cosineMode n x

  change |∑' n : ℕ, term₂ n| ≤ CΔ₂

  have hterm₂_le : ∀ n : ℕ, |term₂ n| ≤ maj₂ n := by
    intro n
    dsimp [term₂, maj₂, base₂]
    rw [show unitIntervalCosineEigenvalue n ^ 2 *
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) *
        ShenWork.CosineSpectrum.cosineMode n x =
        unitIntervalCosineEigenvalue n ^ 2 *
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          ShenWork.CosineSpectrum.cosineMode n x) *
        cosineCoeffs (intervalDomainLift u₀) n from by ring]
    rw [abs_mul]

    have heig_nn : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    have heig2_nn : 0 ≤ unitIntervalCosineEigenvalue n ^ 2 :=
      pow_nonneg heig_nn _

    have hexp_cos_le : |Real.exp (-t * unitIntervalCosineEigenvalue n) *
        ShenWork.CosineSpectrum.cosineMode n x| ≤
        Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) := by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have hcos_le : |ShenWork.CosineSpectrum.cosineMode n x| ≤ 1 := by
        unfold ShenWork.CosineSpectrum.cosineMode
        exact Real.abs_cos_le_one _
      have hexp_le : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) := by
        apply Real.exp_le_exp.mpr
        have hmul : (c + 1) * unitIntervalCosineEigenvalue n ≤
            t * unitIntervalCosineEigenvalue n :=
          mul_le_mul_of_nonneg_right (le_of_lt ht) heig_nn
        linarith
      calc
        Real.exp (-t * unitIntervalCosineEigenvalue n) *
            |ShenWork.CosineSpectrum.cosineMode n x|
            ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) * 1 := by
              exact mul_le_mul_of_nonneg_left hcos_le (Real.exp_nonneg _)
        _ = Real.exp (-t * unitIntervalCosineEigenvalue n) := by ring
        _ ≤ Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n) := hexp_le

    calc
      |unitIntervalCosineEigenvalue n ^ 2 *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            ShenWork.CosineSpectrum.cosineMode n x)| *
          |cosineCoeffs (intervalDomainLift u₀) n|
          ≤ (unitIntervalCosineEigenvalue n ^ 2 *
              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)) * M₀ := by
              rw [abs_mul, abs_of_nonneg heig2_nn]
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left hexp_cos_le heig2_nn)
                (hu₀_bound n)
                (abs_nonneg _)
                (mul_nonneg heig2_nn (Real.exp_nonneg _))
      _ = M₀ *
            (unitIntervalCosineEigenvalue n ^ 2 *
              Real.exp (-(c + 1) * unitIntervalCosineEigenvalue n)) := by
              ring

  exact abs_tsum_le_tsum_of_abs_le
    (f := term₂) (g := maj₂) hterm₂_le hmaj₂_summable
```

## How this feeds the gradient/time-derivative tail

After obtaining

```lean
obtain ⟨CΔ, hCΔ_nn, hDu⟩ := hDu_bound
obtain ⟨CΔ₂, hCΔ₂_nn, hD2u⟩ := hD2u_bound
```

use compactness and positivity of `u₀` to get constants bounding the powers `u^(γ-1)` and `u^(γ-2)` on the invariant interval. Then set:

```lean
set B₁ := |p.ν * p.γ * (p.γ - 1)| * R₂ * CΔ ^ 2
set B₂ := p.ν * p.γ * R₁ * CΔ₂
```

and prove:

```lean
|srcSlice2 p u (heatDu u₀) (heatD2u u₀) t x| ≤ B₁ + B₂
```

by `abs_add_le` and the two termwise estimates:

```text
|νγ(γ-1) u^(γ-2) (heatDu)^2| ≤ |νγ(γ-1)| R₂ CΔ^2
|νγ u^(γ-1) heatD2u|          ≤ νγ R₁ CΔ₂
```

For `srcSlice1`, only the first derivative bound is needed:

```text
|νγ u^(γ-1) heatDu| ≤ νγ R₁ CΔ
```

Then apply:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
```

with the corresponding `ContinuousOn` proof from `heatSemigroup_d1`.

## Derivative identities for `R`

For the first derivative, the repository already has the intended theorem:

```lean
rw [heatLevel0_resolverTimeCoeff_deriv_eq hu₀_bound hu₀_cont hfloor ht_pos k]
```

so the proof should look like:

```lean
set R := resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k
set w_k := ShenWork.PDE.intervalNeumannResolverWeight p k

have hR_deriv_bounded : ∃ B_R' : ℝ, ∀ t : ℝ, c + 1 < t →
    |deriv R t| ≤ B_R' := by
  -- after proving hBsrc for srcSlice1 coefficients:
  obtain ⟨Bsrc, hBsrc⟩ := hBsrc
  refine ⟨|w_k| * Bsrc, fun t ht => ?_⟩
  have ht_pos : 0 < t := by linarith
  rw [show deriv R t = deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t from rfl]
  rw [heatLevel0_resolverTimeCoeff_deriv_eq hu₀_bound hu₀_cont hfloor ht_pos k]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hBsrc t ht) (abs_nonneg _)
```

For the second derivative, avoid a spatial-gradient lemma. Differentiate the coefficient identity one more time:

```lean
have hid2 : ∀ t : ℝ, 0 < t → iteratedDeriv 2 R t =
    w_k * cosineCoeffs
      (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀) t) k := by
  intro t ht_pos
  have hRfun : R = fun s =>
      w_k * srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
    funext s
    exact resolverTimeCoeff_eq_weight_smul p (conjugatePicardIter p u₀ 0) k s
  rw [hRfun, iteratedDeriv_const_mul_field]
  congr 1
  rw [iteratedDeriv_succ]
  have hnear :
      (fun s => iteratedDeriv 1
        (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) s) =ᶠ[𝓝 t]
      fun s => cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) s) k := by
    filter_upwards [Ioi_mem_nhds ht_pos] with s hs
    rw [iteratedDeriv_one]
    exact (heatLevel0_srcTimeCoeff_hasDerivAt hu₀_bound hu₀_cont hfloor hs k).deriv
  rw [Filter.EventuallyEq.deriv_eq hnear]
  obtain ⟨δ₁, hδ₁, hcont_s1, hdiff_s1, hcd_s2⟩ :=
    heatSemigroup_d1 hu₀_bound hu₀_cont hfloor t ht_pos
  have hint : ∀ᶠ r in 𝓝 t, IntervalIntegrable
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) r)
      MeasureTheory.volume (0 : ℝ) 1 :=
    hcont_s1.mono fun r hr =>
      (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
  exact (cosineCoeffs_hasDerivAt_of_smooth_param hδ₁ hint hdiff_s1 hcd_s2).deriv
```

Then the bound is just:

```lean
have hR_deriv2_bounded : ∃ B_R'' : ℝ, ∀ t : ℝ, c + 1 < t →
    |iteratedDeriv 2 R t| ≤ B_R'' := by
  -- after proving hBsrc for srcSlice2 coefficients:
  obtain ⟨Bsrc, hBsrc⟩ := hBsrc
  refine ⟨|w_k| * Bsrc, fun t ht => ?_⟩
  rw [hid2 t (by linarith : 0 < t), abs_mul]
  exact mul_le_mul_of_nonneg_left (hBsrc t ht) (abs_nonneg _)
```

## How to transfer from `R` back to `A`

For `t > c + 1`, use the cutoff-local equality:

```lean
have hev : A =ᶠ[𝓝 t] R := by
  filter_upwards [Ioi_mem_nhds (show c < t by linarith)] with s hs
  show smoothRightCutoff (c / 2) c s * R s = R s
  rw [smoothRightCutoff_eq_one_of_ge (by linarith : c / 2 < c) (le_of_lt hs)]
  exact one_mul _
```

Then:

```lean
-- i = 1
rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
simp only [iteratedDeriv_succ', iteratedDeriv_zero, Real.norm_eq_abs]
rw [Filter.EventuallyEq.deriv_eq hev]
exact hB_R' t ht
```

and:

```lean
-- i = 2
have hev2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 2).eq_of_nhds
rw [show ‖iteratedFDeriv ℝ 2 A t‖ = ‖iteratedFDeriv ℝ 2 R t‖ from congr_arg _ hev2]
rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
exact hB_R'' t ht
```

## Possible local elaboration pitfalls

1. If `Real.exp_le_exp.mpr` is unavailable in the local Mathlib snapshot, replace it with `Real.exp_le_exp_of_le` and keep the explicit `hmul` proof.

2. If `change |∑' n, term n| ≤ CΔ` fails, first write the full unfolded `change`, then introduce `let term := ...`, and then `change` to the named term. This is the same workaround as in the summability note.

3. If `iteratedDeriv_const_mul_field` does not rewrite in the intended direction, use `rw [hRfun]` first, then inspect the goal. The mathematical target is just that the second derivative of `fun s => w_k * f s` is `w_k * iteratedDeriv 2 f s`.

4. Do not introduce a new spatial-gradient abstraction unless another file already needs it. For this proof, the required estimate is entirely controlled by time derivatives of the heat semigroup series.

## Bottom line

The gradient/derivative tail should be closed by the source-slice chain rule plus the same named-majorant summability pattern as Q2114. Bound `heatDu` and `heatD2u` uniformly for `t > c + 1`; use compact positivity of the heat iterate to bound the `u^(γ-1)` and `u^(γ-2)` factors; convert pointwise `srcSlice1`/`srcSlice2` bounds into coefficient bounds; then use `A =ᶠ[𝓝 t] R` because the cutoff is locally `1` in the tail.
