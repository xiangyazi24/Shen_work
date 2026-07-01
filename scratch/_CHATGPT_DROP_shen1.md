# Q2871 (shen1) — strict-window derivative integrability frontier

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

The next honest theorem should **not** try to prove the full

```lean
IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0
```

because that structure quantifies windows touching `0` and `T`.  The current classical-solution/time-Leibniz APIs are strict-interior APIs: they give the derivative for `0 < t < T`, not an integrable derivative trace down to `0`.

The smallest high-signal next step is a **strict-window theorem**:

```lean
0 < a → a ≤ b → b < T →
IntervalIntegrable
  (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s)
  volume a b
```

The clean proof split is:

1. Define the explicit RHS derivative profile
   `s ↦ ∫ y in 0..1, intervalDomainPowerDeriv q u s y`.
2. Prove it is `ContinuousOn` on `Icc a b`, using
   `intervalDomainPowerDeriv_continuousOn` restricted from
   `Ioo 0 T ×ˢ Icc 0 1` to `Icc a b ×ˢ Icc 0 1`, plus a Mathlib parametric-integral continuity lemma.
3. Convert `ContinuousOn` to `IntervalIntegrable` using
   `ContinuousOn.intervalIntegrable` after rewriting `uIcc a b = Icc a b` with `Set.uIcc_of_le hab`.
4. Use `IntervalIntegrable.congr` and `intervalDomainPowerEnergy_hasDerivAt` to identify that explicit RHS with
   `deriv (fun τ => integratedMoserEnergy intervalDomain u q τ)` at every `s ∈ Icc a b`.

This reduces the remaining analytic input to closed-endpoint derivative integrability only; it does not fake it.

## Placement

Best placement is `ShenWork/PDE/P3MoserEnergyContinuity.lean`, after the current energy-continuity/endpoint-continuity block.  That file already imports exactly the two relevant layers:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz
```

If you prefer to keep the file smaller, create:

```lean
ShenWork/PDE/P3MoserEnergyDerivativeIntegrability.lean
```

with imports:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic
```

## Recommended declarations

### 1. Name the explicit derivative profile

This avoids repeatedly writing the spatial interval integral.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

open MeasureTheory Set Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Explicit RHS derivative profile for the interval-domain power energy. -/
def intervalDomainPowerEnergyDerivIntegral
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u s y
```

### 2. Pointwise identification with `deriv integratedMoserEnergy`

This is the key congruence lemma.  It uses only the existing strict-time theorem
`intervalDomainPowerEnergy_hasDerivAt`.

```lean
/-- At strict interior times, the derivative of the abstract Moser energy is the
explicit interval-domain power-derivative integral. -/
theorem intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral
    {params : CM2Params} {T q s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hs0 : 0 < s) (hsT : s < T) :
    deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s =
      intervalDomainPowerEnergyDerivIntegral q u s := by
  have hpow :=
    intervalDomainPowerEnergy_hasDerivAt
      (p := params) (T := T) (q := q) (u := u) (v := v)
      hsol ⟨hs0, hsT⟩
  have hYeq :
      (fun τ : ℝ => integratedMoserEnergy intervalDomain u q τ) =
        fun τ : ℝ => intervalDomainPowerEnergy q u τ := by
    funext τ
    unfold integratedMoserEnergy intervalDomainPowerEnergy
    change intervalDomainIntegral (fun x => (u τ x) ^ q) =
      ∫ y in (0 : ℝ)..1, (intervalDomainLift (u τ) y) ^ q
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hy
    simp [intervalDomainLift, hy]
  simpa [intervalDomainPowerEnergyDerivIntegral, hYeq] using hpow.deriv
```

If `simp [hYeq]` does not rewrite under `deriv` in the local build, replace the last line by an eventual-equality step:

```lean
  have hYeventually :
      (fun τ : ℝ => integratedMoserEnergy intervalDomain u q τ) =ᶠ[𝓝 s]
        fun τ : ℝ => intervalDomainPowerEnergy q u τ := by
    exact Filter.Eventually.of_forall (fun τ => congrFun hYeq τ)
  exact (hYeventually.deriv_eq).trans hpow.deriv
```

The direction may need `.symm.trans` depending on the exact generated goal, but this is a local rewrite issue, not a mathematical frontier.

### 3. Strict-window integrability from continuity of the explicit RHS

This is the smallest theorem I would land first.  It is independent of the harder parametric-integral continuity proof and isolates the easy `ContinuousOn.intervalIntegrable + congr` part.

```lean
/-- Strict-window derivative integrability for the Moser energy, reduced to
continuity of the explicit power-derivative integral profile.

This is deliberately strict: `0 < a` and `b < T` ensure every point of
`Icc a b` is an interior time, including the endpoints `a` and `b`. -/
theorem intervalDomain_integratedMoserEnergy_deriv_intervalIntegrable_of_strictWindow_of_powerDerivIntegral_continuousOn
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T)
    (hF_cont :
      ContinuousOn
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        (Set.Icc a b)) :
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s)
      volume a b := by
  have hF_int :
      IntervalIntegrable
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]

  -- Use `IntervalIntegrable.congr` on `uIcc a b`.  Since `a ≤ b`, this is
  -- just `Icc a b`.  On this strict window, every `s ∈ Icc a b` satisfies
  -- `0 < s` and `s < T`, so the time-Leibniz derivative applies everywhere
  -- needed for interval-integrability congruence.
  refine hF_int.congr ?_
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have hsT : s < T := lt_of_le_of_lt hs.2 hb
  -- Depending on the orientation expected by `.congr`, use either this equality
  -- or its `.symm`.
  exact (intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral
    (params := params) (T := T) (q := q) (u := u) (v := v)
    hsol hs0 hsT).symm
```

If the final `exact ... .symm` has the wrong orientation, remove `.symm`.  In the current repo style, compare `intervalIntegrable_max_one_of_intervalIntegrable`, which uses the same `.congr` pattern.

## The continuity producer for the explicit RHS

The next theorem after the conditional strict-window theorem is:

```lean
/-- On a strict time window, the explicit power-energy derivative profile is
continuous. -/
theorem intervalDomainPowerEnergyDerivIntegral_continuousOn_strictWindow
    {params : CM2Params} {T q a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    ContinuousOn
      (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
      (Set.Icc a b) := by
  -- 1. Joint continuity of the derivative integrand is already present:
  have hjoint_open :
      ContinuousOn
        (Function.uncurry (intervalDomainPowerDeriv q u))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    intervalDomainPowerDeriv_continuousOn (q := q) hsol

  -- 2. Restrict to the compact strict slab.
  have htime_sub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T :=
    Icc_subset_Ioo ha hb
  have hjoint_slab :
      ContinuousOn
        (Function.uncurry (intervalDomainPowerDeriv q u))
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    hjoint_open.mono (Set.prod_mono htime_sub Subset.rfl)

  -- 3. Apply Mathlib parametric interval-integral continuity.
  -- Preferred route:
  --   * use `intervalIntegral.continuousWithinAt_of_dominated_interval`
  --     pointwise for each `s ∈ Icc a b`;
  --   * the local dominating constant comes from compact-slab boundedness of
  --     `hjoint_slab`, or from a small local slab around `s` if that is easier;
  --   * spatial slice integrability follows from
  --     `(hjoint_slab ...).intervalIntegrable` / `ContinuousOn.intervalIntegrable`.
  --
  -- If Mathlib exposes a direct theorem of the shape
  --   ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d) →
  --   ContinuousOn (fun s => ∫ y in c..d, F s y) (Icc a b),
  -- use that here.  Otherwise prove this local helper once from
  -- `intervalIntegral.continuousWithinAt_of_dominated_interval`.
  --
  -- Skeleton:
  -- rw [ContinuousOn]
  -- intro s hs
  -- have hsIoo : s ∈ Set.Ioo (0 : ℝ) T := htime_sub hs
  -- obtain ⟨δ, hδ, hδsub⟩ := exists_closedSlab_subset hsIoo
  -- have hlocal_slab : ContinuousOn ... (Set.Icc (s - δ) (s + δ) ×ˢ Set.Icc 0 1) := ...
  -- obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hlocal_slab
  -- exact intervalIntegral.continuousWithinAt_of_dominated_interval ...
  --
  -- This is the only nontrivial Mathlib-name-sensitive part of the proof.
  -- The theorem is honest and local: no endpoint-time regularity is used.
  sorry
```

I included the `sorry` only to mark the Mathlib-name-sensitive parametric-continuity block in this answer; do not land it with `sorry`.  If a no-`sorry` PR is desired immediately, land theorem 3 first with `hF_cont` as an input, then land the continuity producer after confirming the exact `intervalIntegral.continuousWithinAt_of_dominated_interval` signature in the local Mathlib version.

## Fully packaged strict-window theorem

Once `intervalDomainPowerEnergyDerivIntegral_continuousOn_strictWindow` is proved, the user-facing strict theorem is just:

```lean
/-- Strict-window derivative integrability for interval-domain Moser energies. -/
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

A useful named strict package is also possible:

```lean
/-- Strict-interior version of `IntegratedMoserEnergyDerivativeWindowIntegrability`.
It intentionally does not include windows touching `0` or `T`. -/
def IntegratedMoserEnergyDerivativeStrictWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q → ∀ a b, 0 < a → a ≤ b → b < T →
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy D u q τ) s)
      volume a b

/-- A classical interval-domain solution supplies strict-window derivative
integrability of every Moser energy. -/
theorem intervalDomain_integratedMoserEnergyDerivativeStrictWindowIntegrability_of_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntegratedMoserEnergyDerivativeStrictWindowIntegrability
      intervalDomain u T p0 := by
  intro q _hq a b ha hab hb
  exact intervalDomain_integratedMoserEnergy_deriv_intervalIntegrable_of_strictWindow
    (params := params) (T := T) (q := q) (a := a) (b := b)
    (u := u) (v := v) hsol ha hab hb
```

## Why this does not solve the closed-window residual

The strict theorem proves integrability on `[a,b]` only when `0 < a` and `b < T`.  It cannot be used directly for a full `IntegratedMoserEnergyDerivativeWindowIntegrability` field because that field asks for every

```lean
t1 ∈ Set.Icc 0 T, t2 ∈ Set.Icc t1 T
```

including `t1 = 0` and `t2 = T`.  The existing classical solution gives strict interior differentiability and joint continuity of `intervalDomainPowerDeriv` on

```lean
Set.Ioo 0 T ×ˢ Set.Icc 0 1
```

not endpoint-time derivative integrability.  A later closed-window theorem needs an explicit endpoint residual, for example an integrability statement on `[0,ε]` and `[T-ε,T]`, or an absolute-continuity/trace theorem for `Y_q` on `[0,T]`.

So the honest frontier after this step becomes:

```lean
strict windows: supplied by classical solution
endpoint windows: still explicit residual
```

That is the right shape for the next PR: it removes the easy interior part of `IntegratedMoserEnergyDerivativeWindowIntegrability` without hiding the endpoint analytic work.

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
