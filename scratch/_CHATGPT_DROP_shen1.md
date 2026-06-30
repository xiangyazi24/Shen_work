# Q2497 shen1 — no-sorry precrossing/window plumbing plan at commit 9d9250e6

Repo: `xiangyazi24/Shen_work`

Audited commit: `9d9250e6fbc8e0efb30a61130cd0b6e471ed4321` (`Factor integrated-step Moser residual route`).

Target file:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Target namespace:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

## Current source facts

At commit `9d9250e6`, `P3MoserIntegratedClosure.lean` already has these fixed-window helpers and consumers:

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
moser_iteration_chain_of_integrated_first_crossing_step
all_exponents_of_integrated_first_crossing_step_lpmono
intervalDomain_boundedBefore_of_integrated_first_crossing_step
```

The file does **not** yet have the honest precrossing/window data layer.  The next no-sorry plumbing commit should add only that layer, before the theorem

```lean
moser_iteration_chain_of_integrated_first_crossing_step
```

and after

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

No high-excursion or pointwise extraction theorem should be added in this patch.

## Main compile-risk notes

The snippets below are intended to be pasted into the current file.  They use only existing imports/open namespaces already present in `P3MoserIntegratedClosure.lean`:

```lean
import ShenWork.PDE.P3MoserDissipationShape

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval
```

The only Mathlib API name I would flag as potentially version-sensitive is closure of interval/on-set integrability under `max`.  The snippet below uses the standard method notation

```lean
hconst.max hY
```

where `hconst hY : IntegrableOn ...`.  If this fails, the genuinely missing/renamed Mathlib lemma is the `IntegrableOn.max` closure lemma.  Everything else uses APIs already seen in the repo: `intervalIntegrable_iff_integrableOn_Ioc_of_le`, `IntegrableOn.mono_set`, `Set.Ioc_subset_Icc_self`, `Set.uIcc_of_le`, `.const_mul`, `.add`, and existing integrated-Moser helper names.

## Patch block

Insert the following block after `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`.

```lean
/-! ### Honest precrossing/window plumbing before the first-crossing frontier -/

section PrecrossingWindowPlumbing

/-- Short name for the current Moser energy `Y_p(t)`. -/
def integratedMoserEnergy
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (p t : ℝ) : ℝ :=
  D.integral (fun x => (u t x) ^ p)

/-- Short name for the Moser gradient energy `G_p(t)`. -/
def integratedMoserGradientEnergy
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (p t : ℝ) : ℝ :=
  D.integral (fun x =>
    (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)

/-- Restrict an `IntegrableOn` hypothesis on `uIcc 0 T` to an
`IntervalIntegrable` statement on a non-reversed interval `a..b`.

This is pure Lean plumbing.  The proof route is already used elsewhere in the
repo: rewrite `IntervalIntegrable` to integrability on `Ioc`, then use
`IntegrableOn.mono_set`. -/
theorem intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    {f : ℝ → ℝ} {T a b : ℝ}
    (hab : a ≤ b)
    (hint : IntegrableOn f (Set.uIcc (0 : ℝ) T) volume)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact hint.mono_set (Set.Ioc_subset_Icc_self.trans hsub)

/-- Endpoint hypotheses used by the integrated Moser extraction give the
corresponding set inclusion for every point of the closed window. -/
theorem Icc_subset_uIcc_zero_T_of_endpoint_memberships
    {T a b : ℝ}
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T) :
    Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T := by
  intro s hs
  have h0T : (0 : ℝ) ≤ T := le_trans haT.1 haT.2
  rw [Set.uIcc_of_le h0T]
  exact ⟨le_trans haT.1 hs.1, le_trans hs.2 hbT.2⟩

/-- Power-profile interval integrability from the first-crossing regularity
package. -/
theorem IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable (fun s => integratedMoserEnergy D u p s) volume a b := by
  exact intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    hab (hreg.powerTimeIntegrable p hp) hsub

/-- Gradient-profile interval integrability from the first-crossing regularity
package. -/
theorem IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s => integratedMoserGradientEnergy D u p s) volume a b := by
  exact intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    hab (hreg.gradientTimeIntegrable p hp) hsub

/-- If `Y` is interval-integrable on a non-reversed interval, so is
`max 1 Y`.

API-risk note: this uses the standard `IntegrableOn.max` method as
`hconst.max hY`.  If the local Mathlib spelling differs, this is the only
likely name that needs adjustment. -/
theorem intervalIntegrable_max_one_of_intervalIntegrable
    {Y : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hY : IntervalIntegrable Y volume a b) :
    IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hY ⊢
  have hconstII : IntervalIntegrable (fun _s : ℝ => (1 : ℝ)) volume a b :=
    intervalIntegrable_const
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hconstII
  exact hconstII.max hY

/-- Max-one current-energy interval integrability from the regularity package. -/
theorem IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
      volume a b := by
  exact intervalIntegrable_max_one_of_intervalIntegrable hab
    (hreg.power_intervalIntegrable_of_Icc hp hab hsub)

/-- Abstract nonnegativity of Moser energies on the closed finite horizon.

This should stay explicit at the abstract `BoundedDomainData` level.  Concrete
`intervalDomain` producers may later prove it from positivity of classical
solutions and interval-integral monotonicity. -/
def IntegratedMoserEnergyNonnegativity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → 0 ≤ p → ∀ t, t ∈ Set.Icc (0 : ℝ) T →
    0 ≤ integratedMoserEnergy D u p t

/-- Extract an Icc current-energy bound from `LpPowerBoundedBefore`. -/
theorem currentEnergy_Icc_bound_of_LpPowerBoundedBefore
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p a b : ℝ}
    (hLp : LpPowerBoundedBefore D p T u)
    (ha : 0 < a) (hb : b < T) :
    ∃ Cp, ∀ s ∈ Set.Icc a b, integratedMoserEnergy D u p s ≤ Cp := by
  rcases hLp with ⟨Cp, hCp⟩
  refine ⟨Cp, ?_⟩
  intro s hs
  exact hCp s (lt_of_lt_of_le ha hs.1) (lt_of_le_of_lt hs.2 hb)

/-- Data available on an honest precrossing/window interval.  This record only
packages fixed-window hypotheses; it does not assert any pointwise bound for the
next exponent. -/
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
      integratedMoserEnergy D u p s ≤ M
  right_currentEnergy_nonneg :
    0 ≤ integratedMoserEnergy D u p b
  maxOneEnergy_intervalIntegrable :
    IntervalIntegrable
      (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
      volume a b
  higherPower_intervalIntegrable :
    IntervalIntegrable
      (fun s => integratedMoserEnergy D u (p + rho) s)
      volume a b
  gradient_intervalIntegrable :
    IntervalIntegrable
      (fun s => integratedMoserGradientEnergy D u p s)
      volume a b

namespace IntegratedMoserPrecrossingIntervalData

/-- Left-end current-energy bound extracted from the Icc current-energy field. -/
theorem left_currentEnergy_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    integratedMoserEnergy D u p a ≤ M :=
  hI.currentEnergy_le_Icc a ⟨le_rfl, hI.hab.le⟩

/-- Max-one time-integral control in the exact form needed by the integrated
Moser extraction lemma. -/
theorem maxOneEnergy_timeIntegral_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M) :
    (∫ s in a..b,
      max (1 : ℝ) (integratedMoserEnergy D u p s)) ≤
        (b - a) * max (1 : ℝ) M := by
  exact
    integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
      (D := D) (u := u) (a := a) (b := b) (M := M) (p := p)
      hI.hab.le hI.maxOneEnergy_intervalIntegrable hI.currentEnergy_le_Icc

end IntegratedMoserPrecrossingIntervalData

/-- Build the precrossing/window data from first-crossing regularity,
energy-nonnegativity, and a current-exponent Icc bound. -/
theorem integratedMoserPrecrossingIntervalData_of_regular_window
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hrho_nonneg : 0 ≤ rho)
    (hab : a < b)
    (ha_pos : 0 < a)
    (hb_lt : b < T)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        integratedMoserEnergy D u p s ≤ M) :
    IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M := by
  have hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T :=
    Icc_subset_uIcc_zero_T_of_endpoint_memberships haT hbT
  have hp_rho : p0 ≤ p + rho := by linarith
  have hbT0 : b ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_trans haT.1 hbT.1, hbT.2⟩
  refine
    { hp := hp
      hp_nonneg := hp_nonneg
      hab := hab
      ha_pos := ha_pos
      hb_lt := hb_lt
      haT := haT
      hbT := hbT
      currentEnergy_le_Icc := hY_le
      right_currentEnergy_nonneg := hnonneg p hp hp_nonneg b hbT0
      maxOneEnergy_intervalIntegrable := ?_
      higherPower_intervalIntegrable := ?_
      gradient_intervalIntegrable := ?_ }
  · exact hreg.maxOneEnergy_intervalIntegrable_of_Icc hp hab.le hsub
  · exact hreg.power_intervalIntegrable_of_Icc hp_rho hab.le hsub
  · exact hreg.gradient_intervalIntegrable_of_Icc hp hab.le hsub

/-- Constants and estimates produced by the fixed-window integrated Moser
upper-bound calculation. -/
structure IntegratedMoserWindowUpperBoundData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M eps : ℝ) : Prop where
  Gbound : ℝ
  Ceps : ℝ
  Ceps_nonneg : 0 ≤ Ceps
  gradient_bound :
    (∫ s in a..b, integratedMoserGradientEnergy D u p s) ≤ Gbound
  higherPower_timeIntegral_bound :
    (∫ s in a..b, integratedMoserEnergy D u (p + rho) s) ≤
      eps * Gbound + (b - a) * (Ceps * M)

/-- Package the existing fixed-window integrated-Moser and relative-Moser helpers
into a reusable upper-bound record.  This is still only a time-integral theorem,
not a pointwise extraction theorem. -/
theorem integratedMoser_windowUpperBoundData_of_precrossing
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M)
    (heps : 0 < eps) :
    IntegratedMoserWindowUpperBoundData D u rho p a b M eps := by
  rcases
    integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      (H := (b - a) * max (1 : ℝ) M)
      hinteg hI.hp hI.hp_nonneg hI.haT hI.hbT
      (IntegratedMoserPrecrossingIntervalData.left_currentEnergy_le hI)
      hI.right_currentEnergy_nonneg
      (IntegratedMoserPrecrossingIntervalData.maxOneEnergy_timeIntegral_le hI) with
    ⟨C, _hC_nonneg, hgrad_two⟩
  let Gbound : ℝ := (M + C * p * ((b - a) * max (1 : ℝ) M)) / 2
  have hGbound :
      (∫ s in a..b, integratedMoserGradientEnergy D u p s) ≤ Gbound := by
    dsimp [Gbound, integratedMoserGradientEnergy] at hgrad_two ⊢
    linarith
  rcases
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      (eps := eps) (Gbound := Gbound)
      hrel hI.hp heps hI.hab.le hI.ha_pos hI.hb_lt
      hI.higherPower_intervalIntegrable
      hI.gradient_intervalIntegrable
      hI.currentEnergy_le_Icc
      hGbound with
    ⟨Ceps, hCeps_nonneg, hZ⟩
  exact
    { Gbound := Gbound
      Ceps := Ceps
      Ceps_nonneg := hCeps_nonneg
      gradient_bound := hGbound
      higherPower_timeIntegral_bound := hZ }

#print axioms intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
#print axioms Icc_subset_uIcc_zero_T_of_endpoint_memberships
#print axioms IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
#print axioms IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
#print axioms intervalIntegrable_max_one_of_intervalIntegrable
#print axioms IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
#print axioms currentEnergy_Icc_bound_of_LpPowerBoundedBefore
#print axioms integratedMoserPrecrossingIntervalData_of_regular_window
#print axioms integratedMoser_windowUpperBoundData_of_precrossing

end PrecrossingWindowPlumbing
```

## Why this is the right stopping point

The patch above only packages interval/window-level facts:

* interval-integrability restrictions from `IntegrableOn` on `uIcc 0 T`,
* max-one interval-integrability,
* regularity producers for the current, higher, and gradient profiles,
* extraction of a current-energy Icc bound from `LpPowerBoundedBefore`,
* construction of the honest precrossing/window data record,
* and packaging of the existing fixed-window upper estimate into `IntegratedMoserWindowUpperBoundData`.

It does not add any fake theorem of the form

```lean
∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤ K
  → LpPowerBoundedBefore D (p + rho) T u
```

and it does not introduce `IntegratedMoserFirstCrossingStep`.  The high-excursion/pointwise extraction theorem remains a real analytic frontier for a later patch.

## If the max-closure method name fails

If Lean rejects

```lean
exact hconstII.max hY
```

in `intervalIntegrable_max_one_of_intervalIntegrable`, the only missing local adjustment is the Mathlib spelling for integrability under max.  Search candidates are likely named around:

```lean
IntegrableOn.max
Integrable.max
AEStronglyMeasurable.max
```

A fallback proof can rewrite `max 1 Y = (1 + Y + |1 - Y|) / 2`, but that needs integrability of `abs (1 - Y)`, so it still depends on the local names for closure under `abs` and arithmetic.  The direct `IntegrableOn.max` route is the minimal intended one.
