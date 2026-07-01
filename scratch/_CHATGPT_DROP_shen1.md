# Q2873 (shen1) — no-sorry strict-window continuity of the power-derivative integral

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

Yes: the strict-window continuity theorem should be provable with the existing Mathlib 4.29.1 API using the same dominated-continuity pattern already present in the repo, especially the proof of `powerCoeff_continuousOn_of_inputs` in `ShenWork/Wiener/EWA/SourcePowerCoeffDerivComplete.lean`.

The key Mathlib theorem shape is:

```lean
intervalIntegral.continuousWithinAt_of_dominated_interval
  (bound := bound) hF_meas h_bound hbound_int h_cont
```

where:

* `hF_meas` is eventual a.e.-strong measurability of spatial slices;
* `h_bound` is an eventual-in-parameter, a.e.-in-space domination by an interval-integrable bound;
* `hbound_int` is `IntervalIntegrable bound volume 0 1`;
* `h_cont` is a.e.-in-space continuity of the parameter slice.

For the current target, the bound can be a constant `B'` obtained from compactness of

```lean
Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1
```

and joint continuity of

```lean
Function.uncurry (intervalDomainPowerDeriv q u)
```

on that strict slab.

I cannot run Lean from the GitHub connector, but the proof below is a direct no-`sorry` adaptation of an existing compiled repo pattern.  It does not introduce axioms and does not use endpoint-time regularity.

## Exact theorem to add

Put this in `ShenWork/PDE/P3MoserEnergyContinuity.lean`, after the existing definition

```lean
def intervalDomainPowerEnergyDerivIntegral
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u s y
```

If that definition is in a new derivative-integrability file instead, put the theorem in the same namespace and import `ShenWork.PDE.P3MoserEnergyContinuity`.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- On a strict time window, the explicit interval-domain power-energy derivative
profile is continuous.

The proof is a direct dominated-continuity argument over the fixed spatial
interval `[0,1]`.  The strict hypotheses `0 < a` and `b < T` are exactly what
let us restrict the already-proved joint continuity of
`intervalDomainPowerDeriv` from `(0,T) × [0,1]` to the compact slab
`[a,b] × [0,1]`. -/
theorem intervalDomainPowerEnergyDerivIntegral_continuousOn_strictWindow
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hb : b < T) :
    ContinuousOn
      (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
      (Set.Icc a b) := by
  intro s₀ hs₀
  set I : Set ℝ := Set.Icc a b with hIdef
  set F : ℝ → ℝ → ℝ := fun s y => intervalDomainPowerDeriv q u s y with hFdef

  have htime_sub : I ⊆ Set.Ioo (0 : ℝ) T := by
    rw [hIdef]
    exact Icc_subset_Ioo ha hb

  have hjoint_open :
      ContinuousOn
        (Function.uncurry (intervalDomainPowerDeriv q u))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    intervalDomainPowerDeriv_continuousOn (q := q) hsol

  have hFcont :
      ContinuousOn
        (Function.uncurry F)
        (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    dsimp [F]
    exact hjoint_open.mono (Set.prod_mono htime_sub Subset.rfl)

  -- Compactness gives a uniform bound for the norm of the joint integrand on the
  -- strict time-space slab.
  have hKcompact : IsCompact (I ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [hIdef]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcont.norm
  set B' : ℝ := max B 0 with hB'def

  have hFbd : ∀ s ∈ I, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖F s x‖ ≤ B' := by
    intro s hs x hx
    have hBx : ‖Function.uncurry F (s, x)‖ ≤ B :=
      hB (Set.mem_image_of_mem _ (Set.mem_prod.mpr ⟨hs, hx⟩))
    exact le_trans hBx (le_max_left _ _)

  have hslice_cont : ∀ s ∈ I, ContinuousOn (F s) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    exact hFcont.comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => Set.mem_prod.mpr ⟨hs, hx⟩)

  have hInhds : I ∈ 𝓝[I] s₀ := self_mem_nhdsWithin

  have hint_cont :
      ContinuousWithinAt
        (fun s => ∫ x in (0 : ℝ)..1, F s x)
        I s₀ := by
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _x : ℝ => B') ?_ ?_ intervalIntegrable_const ?_
    · -- Eventual a.e.-strong measurability of the spatial slices, from slice
      -- continuity on `[0,1]`.
      filter_upwards [hInhds] with s hs
      have hs_cont_uIcc : ContinuousOn (F s) (Set.uIcc (0 : ℝ) 1) := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact hslice_cont s hs
      exact
        (hs_cont_uIcc.mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc
    · -- Uniform domination by the compact-slab constant bound.
      filter_upwards [hInhds] with s hs
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact hFbd s hs x ⟨hx.1.le, hx.2⟩
    · -- For a.e. spatial `x`, the parameter slice is continuous within the time
      -- window.  In fact this holds for every `x ∈ uIoc 0 1`.
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hparam_cont :
          ContinuousWithinAt (fun s => F s x) I s₀ :=
        (hFcont.comp
          (continuousOn_id.prodMk continuousOn_const)
          (fun s hs => Set.mem_prod.mpr ⟨hs, hxIcc⟩)).continuousWithinAt hs₀
      simpa [F, Function.uncurry] using hparam_cont

  simpa [intervalDomainPowerEnergyDerivIntegral, F, hIdef] using hint_cont

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

## Notes on why this should elaborate

The proof intentionally mirrors the compiled pattern:

```lean
powerCoeff_continuousOn_of_inputs
```

from `ShenWork/Wiener/EWA/SourcePowerCoeffDerivComplete.lean`.  The central block is the same:

```lean
refine intervalIntegral.continuousWithinAt_of_dominated_interval
  (bound := fun _ => B') ?_ ?_ intervalIntegrable_const ?_
```

with the same three subgoals:

```lean
-- hF_meas
filter_upwards [hInhds] with s hs
...
exact (this.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc

-- h_bound
filter_upwards [hInhds] with s hs
refine Filter.Eventually.of_forall (fun x hx => ?_)
...

-- h_cont
refine Filter.Eventually.of_forall (fun x hx => ?_)
...
```

The only adaptation is that the integrand has no cosine prefactor and no coefficient normalization.  The target is definitionally just the interval integral of `F s`.

## If Lean complains about `hs₀` after `set I`

In the existing repo pattern, Lean accepts `hs₀` after

```lean
set I : Set ℝ := Set.Icc a b with hIdef
```

as a proof of `s₀ ∈ I`.  If local elaboration is stricter, insert:

```lean
  have hs₀I : s₀ ∈ I := by
    rwa [hIdef]
```

and replace:

```lean
.continuousWithinAt hs₀
```

by:

```lean
.continuousWithinAt hs₀I
```

No mathematics changes.

## If Lean wants a named nonempty bound instead of `bddAbove_image`

The existing repo proof uses:

```lean
obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcont.norm
```

so the theorem above uses the same call.  If the local pretty-printer unfolds the normed function differently, this alternative usually elaborates:

```lean
  have hFcont_norm :
      ContinuousOn
        (fun z : ℝ × ℝ => ‖Function.uncurry F z‖)
        (I ×ˢ Set.Icc (0 : ℝ) 1) :=
    hFcont.norm
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hFcont_norm
```

and the rest of the proof is unchanged.

## Downstream strict-window derivative integrability

Once the theorem above is in place, the strict-window derivative-integrability theorem from Q2871 becomes no-sorry by composing it with the derivative-identification lemma:

```lean
theorem intervalDomain_integratedMoserEnergy_deriv_intervalIntegrable_of_strictWindow
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s)
      volume a b :=
  intervalDomain_integratedMoserEnergy_deriv_intervalIntegrable_of_strictWindow_of_powerDerivIntegral_continuousOn
    (params := params) (T := T) (q := q) (a := a) (b := b)
    (u := u) (v := v) hsol ha hab hb
    (intervalDomainPowerEnergyDerivIntegral_continuousOn_strictWindow
      (params := params) (T := T) (q := q) (a := a) (b := b)
      (u := u) (v := v) hsol ha hab hb)
```

This still does **not** prove closed endpoint derivative integrability.  It only closes the strict-interior parametric-continuity part, which is the right no-fake next frontier.
