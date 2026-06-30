# Q2475 shen1 — corrected precrossing interval skeleton against current APIs

Repo: `xiangyazi24/Shen_work`

Target namespace:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

I re-audited the currently visible `main` copy of `ShenWork/PDE/P3MoserIntegratedClosure.lean`.  It now contains the helper signatures needed for this question, including the two signature details that made the Q2461 drop too stale:

1. `integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound` takes not only `hab` and the Icc bound on `Y_p`, but also

```lean
hYmax_int :
  IntervalIntegrable
    (fun s => max (1 : ℝ) (D.integral (fun x => (u s x) ^ p)))
    volume a b
```

2. `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound` has the current shape

```lean
{T rho p0 p a b M eps Gbound : ℝ}
(hrel : RelativeMoserInterpolationBefore D u T rho p0)
(hp : p0 ≤ p)
(heps : 0 < eps)
(hab : a ≤ b)
(ha : 0 < a)
(hb : b < T)
(hZ_int : IntervalIntegrable (fun s => D.integral (fun x => (u s x) ^ (p + rho))) volume a b)
(hG_int : IntervalIntegrable (fun s => D.integral (fun x =>
  (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) volume a b)
(hY_le : ∀ s ∈ Set.Icc a b, D.integral (fun x => (u s x) ^ p) ≤ M)
(hG_le : ∫ s in a..b, D.integral (fun x =>
  (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤ Gbound)
```

and returns `∃ Ceps, 0 ≤ Ceps ∧ ∫ Z ≤ eps * Gbound + (b - a) * (Ceps * M)`.

So the Q2461 data structure was missing one real field: max-one time integrability.  Also, the Q2461 wrapper that took an arbitrary `hhigher` argument and concluded exactly the same higher-power time-integral existence is not worth committing; it is just eta-expansion of an input.  The corrected patch below calls the current relative-Moser helper directly.

## Compile-oriented patch

If this is pasted into `ShenWork/PDE/P3MoserIntegratedClosure.lean`, insert only the section beginning at `/-! ### Honest precrossing... -/`, after the current helper

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

and before `moser_iteration_chain_of_integrated_first_crossing_step`.

For standalone scratch checking in a new file, use the full block with imports/open statements:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-! ### Honest precrossing interval skeleton

This section packages only interval-level information.  It does not turn a
time-integral or average estimate for `Y_{p+rho}` into
`LpPowerBoundedBefore D (p + rho) T u`.
-/

section PrecrossingInterval

/-- Data available on a genuine precrossing interval.

The extra `maxOneEnergy_intervalIntegrable` field is required by the current
signature of `integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound`.
The two ordinary interval-integrability fields are required by the current
relative-Moser time-integral helper.
-/
structure IntegratedMoserPrecrossingIntervalData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p a b M : ℝ) : Prop where
  hp : p0 ≤ p
  hp_nonneg : 0 ≤ p
  hab : a < b
  ha_pos : 0 < a
  hb_lt : b < T
  haT : a ∈ Set.Icc (0 : ℝ) T
  hbT : b ∈ Set.Icc a T
  currentEnergy_le_Icc :
    ∀ s ∈ Set.Icc a b,
      D.integral (fun x => (u s x) ^ p) ≤ M
  right_currentEnergy_nonneg :
    0 ≤ D.integral (fun x => (u b x) ^ p)
  maxOneEnergy_intervalIntegrable :
    IntervalIntegrable
      (fun s => max (1 : ℝ)
        (D.integral (fun x => (u s x) ^ p)))
      volume a b
  higherPower_intervalIntegrable :
    IntervalIntegrable
      (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
      volume a b
  gradient_intervalIntegrable :
    IntervalIntegrable
      (fun s =>
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
      volume a b

namespace IntegratedMoserPrecrossingIntervalData

/-- Left-end current-energy bound extracted from the Icc precrossing bound. -/
theorem left_currentEnergy_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    D.integral (fun x => (u a x) ^ p) ≤ M :=
  hI.currentEnergy_le_Icc a ⟨le_rfl, hI.hab.le⟩

/-- Max-one time-integral control from the current-energy Icc bound. -/
theorem maxOneEnergy_timeIntegral_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    (∫ s in a..b,
      max (1 : ℝ) (D.integral (fun x => (u s x) ^ p))) ≤
        (b - a) * max (1 : ℝ) M := by
  exact
    integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
      (D := D) (u := u) (a := a) (b := b) (M := M) (p := p)
      hI.hab.le hI.maxOneEnergy_intervalIntegrable hI.currentEnergy_le_Icc

end IntegratedMoserPrecrossingIntervalData

/-- Integrated Moser extraction on a precrossing interval.

This is the signature-sensitive call.  It matches the current extraction lemma:
`hinteg`, `hp`, `hp_nonneg`, `haT`, `hbT`, `hYa`, `hYb_nonneg`, `hmaxInt`.
-/
theorem integratedMoser_precrossing_gradientIntegral_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    ∃ C, 0 ≤ C ∧
      2 *
        (∫ s in a..b,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤
          M + C * p * ((b - a) * max (1 : ℝ) M) := by
  exact
    integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      (H := (b - a) * max (1 : ℝ) M)
      hinteg hI.hp hI.hp_nonneg hI.haT hI.hbT
      (IntegratedMoserPrecrossingIntervalData.left_currentEnergy_le hI)
      hI.right_currentEnergy_nonneg
      (IntegratedMoserPrecrossingIntervalData.maxOneEnergy_timeIntegral_le hI)

/-- A one-sided bound for the integrated Moser-gradient term. -/
theorem integratedMoser_precrossing_gradientIntegral_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    ∃ Gbound,
      (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbound := by
  rcases integratedMoser_precrossing_gradientIntegral_le hinteg hI with
    ⟨C, _hC_nonneg, hgrad⟩
  refine ⟨(M + C * p * ((b - a) * max (1 : ℝ) M)) / 2, ?_⟩
  linarith

/-- Honest higher-power time-integral output on a precrossing interval.

This directly consumes the current local helper
`relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`.
It concludes only an interval integral bound, not `LpPowerBoundedBefore`.
-/
theorem integratedMoser_precrossing_higherPower_timeIntegral_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M)
    (heps : 0 < eps) :
    ∃ Gbound,
      (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbound ∧
      ∃ Ceps, 0 ≤ Ceps ∧
        (∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho))) ≤
          eps * Gbound + (b - a) * (Ceps * M) := by
  rcases integratedMoser_precrossing_gradientIntegral_bound hinteg hI with
    ⟨Gbound, hGbound⟩
  refine ⟨Gbound, hGbound, ?_⟩
  exact
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      (eps := eps) (Gbound := Gbound)
      hrel hI.hp heps hI.hab.le hI.ha_pos hI.hb_lt
      hI.higherPower_intervalIntegrable
      hI.gradient_intervalIntegrable
      hI.currentEnergy_le_Icc
      hGbound

/-- Average form of the same honest higher-power estimate.

This is still only an average/time-integral consequence.  It deliberately does
not assert any pointwise-in-time `Y_{p+rho}` bound.
-/
theorem integratedMoser_precrossing_higherPower_average_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M)
    (heps : 0 < eps) :
    ∃ Gbound,
      (∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbound ∧
      ∃ Ceps, 0 ≤ Ceps ∧
        (1 / (b - a)) *
          (∫ s in a..b,
            D.integral (fun x => (u s x) ^ (p + rho))) ≤
          (1 / (b - a)) *
            (eps * Gbound + (b - a) * (Ceps * M)) := by
  rcases integratedMoser_precrossing_higherPower_timeIntegral_le
      hinteg hrel hI heps with
    ⟨Gbound, hGbound, Ceps, hCeps_nonneg, hZ⟩
  refine ⟨Gbound, hGbound, Ceps, hCeps_nonneg, ?_⟩
  have hscale_nonneg : 0 ≤ 1 / (b - a) := by
    exact div_nonneg zero_le_one (sub_nonneg.mpr hI.hab.le)
  exact mul_le_mul_of_nonneg_left hZ hscale_nonneg

end PrecrossingInterval

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

## In-place insertion version

Inside `P3MoserIntegratedClosure.lean`, do **not** add the final namespace-closing line from the standalone block.  Insert this section before the existing theorem

```lean
moser_iteration_chain_of_integrated_first_crossing_step
```

because that is where the helper family ends and the old pointwise first-crossing skeleton begins.

## Why the extra field is needed

The Q2461 data structure only had integrability of `Y_{p+rho}` and the gradient profile.  Against the current helper signatures, that is insufficient: `integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound` requires integrability of the function

```lean
fun s => max (1 : ℝ) (D.integral (fun x => (u s x) ^ p))
```

on `a..b`.  This can often be derived from regularity/time-integrability in a later patch, but it is not a purely algebraic consequence of the Icc upper bound in the abstract `BoundedDomainData` API.  Keeping it as a field is the honest compile-oriented move.

## The Q2461 theorem not worth committing

Do not commit the Q2461 theorem named approximately

```lean
integratedMoser_precrossing_higherPower_timeIntegral_le_of_integrated_relative
```

in the form where it takes an argument

```lean
hhigher : ∀ Gbar, (∫ G ≤ Gbar) → ∃ Zbar, ∫ Z ≤ Zbar
```

and returns

```lean
∃ Zbar, ∫ Z ≤ Zbar
```

That wrapper adds no useful interface: after the gradient-bound theorem, it merely applies an argument that already has the desired conclusion.  The corrected patch above is better because it directly calls the actual local relative-Moser helper and records the produced constants `Gbound` and `Ceps`.

## Honest boundary of this patch

This patch still does not prove, and should not try to prove,

```lean
LpPowerBoundedBefore D (p + rho) T u
```

from the higher-power time-integral or average estimate.  A later pointwise extraction theorem would need additional analytic input, such as a genuine first-crossing/continuity argument converting interval average control into endpoint or uniform-in-time control.  That is not present in these helper APIs.
