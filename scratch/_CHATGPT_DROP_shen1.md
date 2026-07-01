# Q2881 (shen1) — positive-start continuity of the logistic Lp term

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

The logistic component is the easiest of the three.  It should be provable no-sorry from `IsPaper2GlobalClassicalSolution` by the same compact-slab dominated-continuity pattern already used for `intervalDomainPowerEnergyDerivIntegral_continuousOn_strictWindow`.

The key point is to avoid trying to prove continuity of the opaque scalar integral directly.  Instead define the lifted logistic integrand on `[a,b] × [0,1]` as

```lean
F s y = U(s,y)^(q-2) * U(s,y) * (U(s,y) * (params.a - params.b * U(s,y)^params.α))
```

where

```lean
U(s,y) = intervalDomainLift (u s) y.
```

On a positive-start window `0 < a`, global classical regularity gives positivity of `U`, so the real powers are continuous.  Compactness gives a uniform constant bound, and `intervalIntegral.continuousWithinAt_of_dominated_interval` gives continuity of `s ↦ ∫₀¹ F s y dy`.  Finally, this integral is equal to `intervalDomainLpLogisticIntegral params q u s` by unfolding and using `abs_of_pos`.

## Code to add

Put this in `ShenWork/PDE/P3MoserEnergyContinuity.lean`, after the existing residual definitions.  The theorem only proves the logistic component; diffusion and chemotaxis still need their own joint-continuity producers.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Tactic

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Positive-start continuity of the logistic scalar term in the Lp PDE energy
identity.

This is the easy component: it only uses the joint continuity and positivity of
`u` on a strict compact time slab, plus dominated continuity of interval
integrals. -/
theorem intervalDomain_lpLogisticIntegral_continuousOn_positiveStart_of_global_classical
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T) :
    ContinuousOn
      (fun s => q * intervalDomainLpLogisticIntegral params q u s)
      (Set.Icc a b) := by
  classical
  set I : Set ℝ := Set.Icc a b with hIdef
  have hTpos : 0 < T := lt_of_lt_of_le ha (le_trans hab hbT)
  have hTplus : 0 < T + 1 := by linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain params (T + 1) u v :=
    hglobal.classical hTplus

  have htime_sub : I ⊆ Set.Ioo (0 : ℝ) (T + 1) := by
    intro s hs
    rw [hIdef] at hs
    exact ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt (le_trans hs.2 hbT) (by linarith)⟩

  -- Explicit lifted logistic integrand.
  set F : ℝ → ℝ → ℝ := fun s y =>
    (intervalDomainLift (u s) y) ^ (q - 2) *
      intervalDomainLift (u s) y *
        (intervalDomainLift (u s) y *
          (params.a - params.b * (intervalDomainLift (u s) y) ^ params.α))
    with hFdef

  have hU :
      ContinuousOn
        (fun z : ℝ × ℝ => intervalDomainLift (u z.1) z.2)
        (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hUopen := intervalDomain_solution_jointContinuousOn hsol
    simpa [Function.uncurry] using
      hUopen.mono (Set.prod_mono htime_sub Subset.rfl)

  have hpow_qm2 :
      ContinuousOn
        (fun z : ℝ × ℝ => (intervalDomainLift (u z.1) z.2) ^ (q - 2))
        (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hpow_open :=
      intervalDomain_power_jointContinuousOn
        (T := T + 1) (p := q - 2) (u := u) (v := v) hsol
    simpa [Function.uncurry] using
      hpow_open.mono (Set.prod_mono htime_sub Subset.rfl)

  have hpow_alpha :
      ContinuousOn
        (fun z : ℝ × ℝ => (intervalDomainLift (u z.1) z.2) ^ params.α)
        (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hpow_open :=
      intervalDomain_power_jointContinuousOn
        (T := T + 1) (p := params.α) (u := u) (v := v) hsol
    simpa [Function.uncurry] using
      hpow_open.mono (Set.prod_mono htime_sub Subset.rfl)

  have htest :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          (intervalDomainLift (u z.1) z.2) ^ (q - 2) *
            intervalDomainLift (u z.1) z.2)
        (I ×ˢ Set.Icc (0 : ℝ) 1) :=
    hpow_qm2.mul hU

  have hreact :
      ContinuousOn
        (fun z : ℝ × ℝ =>
          intervalDomainLift (u z.1) z.2 *
            (params.a - params.b *
              (intervalDomainLift (u z.1) z.2) ^ params.α))
        (I ×ˢ Set.Icc (0 : ℝ) 1) :=
    hU.mul (continuousOn_const.sub (continuousOn_const.mul hpow_alpha))

  have hFcont :
      ContinuousOn (Function.uncurry F) (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    simpa [F, Function.uncurry] using htest.mul hreact

  have hKcompact : IsCompact (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [hIdef]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcont.norm
  set B' : ℝ := max B 0 with hB'def

  have hFbd : ∀ s ∈ I, ∀ y ∈ Set.Icc (0 : ℝ) 1, ‖F s y‖ ≤ B' := by
    intro s hs y hy
    have hBy : ‖Function.uncurry F (s, y)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hs, hy⟩))
    exact le_trans hBy (le_max_left _ _)

  have hslice_cont : ∀ s ∈ I, ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    exact hFcont.comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun y hy => Set.mem_prod.mpr ⟨hs, hy⟩)

  -- On the strict positive-start slab, the named logistic integral is exactly
  -- the interval integral of `F`.
  have hlog_eq :
      ∀ s ∈ I,
        intervalDomainLpLogisticIntegral params q u s =
          ∫ y in (0 : ℝ)..1, F s y := by
    intro s hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) (T + 1) := htime_sub hs
    unfold intervalDomainLpLogisticIntegral
    change intervalDomainIntegral
        (fun x =>
          intervalDomainLpDiffusionTest q u s x *
            (u s x * (params.a - params.b * (u s x) ^ params.α))) =
      ∫ y in (0 : ℝ)..1, F s y
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (zero_le_one)] at hy
    have hpos : 0 < u s (⟨y, hy⟩ : intervalDomain.Point) :=
      hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomain.Point)) hsIoo.1 hsIoo.2
    simp [F, intervalDomainLift, intervalDomainLpDiffusionTest, hy, abs_of_pos hpos]

  -- Continuity of the explicit interval integral by dominated continuity.
  have hint_cont :
      ContinuousOn (fun s => ∫ y in (0 : ℝ)..1, F s y) I := by
    intro s₀ hs₀
    have hInhds : I ∈ 𝓝[I] s₀ := self_mem_nhdsWithin
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _y : ℝ => B') ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hInhds] with s hs
      have hs_cont_uIcc : ContinuousOn (F s) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le (zero_le_one)]
        exact hslice_cont s hs
      exact
        (hs_cont_uIcc.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
    · filter_upwards [hInhds] with s hs
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.uIoc_of_le (zero_le_one)] at hy
      exact hFbd s hs y ⟨hy.1.le, hy.2⟩
    · refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.uIoc_of_le (zero_le_one)] at hy
      have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
      have hparam_cont : ContinuousWithinAt (fun s => F s y) I s₀ :=
        (hFcont.comp
          (continuousOn_id.prodMk continuousOn_const)
          (fun s hs => Set.mem_prod.mpr ⟨hs, hyIcc⟩)).continuousWithinAt hs₀
      simpa [F, Function.uncurry] using hparam_cont

  have hlog_cont :
      ContinuousOn (fun s => intervalDomainLpLogisticIntegral params q u s) I :=
    hint_cont.congr (fun s hs => (hlog_eq s hs).symm)

  have hscaled :
      ContinuousOn
        (fun s => q * intervalDomainLpLogisticIntegral params q u s) I :=
    continuousOn_const.mul hlog_cont

  simpa [I, hIdef] using hscaled

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

## How this plugs into the existing residual split

This proves the third component of

```lean
IntervalDomainLpPDETermPositiveStartWindowContinuity params u v T p0
```

from global classical regularity.  The first two components still need analogous producers:

```lean
ContinuousOn (fun s => q * intervalDomainLpDiffusionIntegral q u s) (Set.Icc a b)
ContinuousOn (fun s => q * (params.χ₀ * intervalDomainLpChemotaxisIntegral params q u v s)) (Set.Icc a b)
```

The logistic proof uses only joint continuity of `u`, positivity of `u`, and compact dominated convergence.  The diffusion and chemotaxis components are harder because they require joint continuity/bounds for lifted `laplacian (u s)` and `chemotaxisDiv params (u s) (v s)` on the slab, not just the fixed-time spatial integrability lemmas.

## If a local elaboration issue appears

The most likely minor adjustment is the final `ContinuousOn.congr` orientation.  If Lean reports the equality is reversed, replace

```lean
hint_cont.congr (fun s hs => (hlog_eq s hs).symm)
```

by an explicit within-neighborhood rewrite:

```lean
  have hlog_cont :
      ContinuousOn (fun s => intervalDomainLpLogisticIntegral params q u s) I := by
    intro s₀ hs₀
    have heq :
        (fun s => intervalDomainLpLogisticIntegral params q u s) =ᶠ[𝓝[I] s₀]
          fun s => ∫ y in (0 : ℝ)..1, F s y := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hlog_eq s hs
    exact heq.continuousWithinAt_iff.mpr (hint_cont s₀ hs₀)
```

The mathematical content is unchanged.
