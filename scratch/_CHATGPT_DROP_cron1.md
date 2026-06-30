# Q2565 (cron1) — integrated first-crossing Moser high-excursion roadmap

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Executive answer

The two missing sub-frontiers should be split, but the split must use the correct quantifier order.

* `LowerAverageWindow` chooses a real time window around a high-excursion time and supplies a **quantitative positive time average** for the next exponent:

  ```text
  Z(s) := Y_{p+rho}(s) = ∫ u(s)^(p+rho)
  Y(s) := Y_p(s)       = ∫ u(s)^p
  G(s) := G_p(s)       = ∫ |∇(u(s)^(p/2))|^2
  ```

  From `Z(t) > Cnext`, choose a thickness window `[a,b]` on which

  ```text
  κ * Cnext ≤ Z(s)     for all s ∈ [a,b]
  Y(s) ≤ M             for all s ∈ [a,b]
  ```

  with `0 < κ < 1`, usually `κ = 1/2`. Then set

  ```text
  lowerBound := (b - a) * (κ * Cnext).
  ```

* `UpperGapWitness` should **not** be proved by saying “take eps small”. That is false as a proof strategy unless one also controls how `Ceps` depends on `eps`. The Lean-safe standard choice is: fix a positive `eps★` first, get the corresponding relative-Moser constant `Ceps★`, then choose `Cnext` large enough so that the lower average beats both upper terms.

  For a fixed window length lower bound `ell0 ≤ b-a`, a drop constant `Cdrop`, current bound `M ≥ 1`, and

  ```text
  Gbar := (M + Cdrop * p * T * M) / 2,
  ```

  choose, for example,

  ```text
  eps★  := 1,
  Cnext := 1 + max (4 * eps★ * Gbar / (κ * ell0))
                   (4 * Ceps★ * M / κ).
  ```

  Then every lower window with `ell0 ≤ b-a` satisfies

  ```text
  eps★ * Gbound + (b-a) * Ceps★ * M < lowerBound.
  ```

This is the key correction: **the threshold `Cnext` is chosen after the interpolation constant for a fixed epsilon is known**. The lower-window producer must either provide a uniform thickness `ell0`, or the upper-gap frontier must remain an analytic frontier. A mere continuity window with no quantitative lower length is enough to populate the current `IntegratedMoserHighExcursionLowerAverageWindow`, but it is not enough to prove the strict gap uniformly.

## Existing source facts to consume

Current `ShenWork/PDE/P3MoserIntegratedClosure.lean` already has the right fixed-window plumbing:

```lean
integratedMoserEnergy
integratedMoserGradientEnergy
currentEnergy_Icc_bound_of_LpPowerBoundedBefore
IntegratedMoserPrecrossingIntervalData
integratedMoserPrecrossingIntervalData_of_regular_window
IntegratedMoserWindowUpperBoundWitness
IntegratedMoserWindowUpperBoundData
integratedMoser_windowUpperBoundData_of_precrossing
IntegratedMoserHighExcursionLowerAverageWindow
IntegratedMoserHighExcursionLowerAverageWindowFrontier
IntegratedMoserWindowUpperGapWitness
IntegratedMoserWindowUpperGapWitnessFrontier
IntegratedMoserLowerUpperWindowFrontiers
integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
```

The integrated dissipation API has exactly the right shape:

```lean
def IntegratedMoserDissipationDropBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        2 * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))
```

and the existing extraction lemma consumes it with the actual signature:

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
  (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
  (hp : p0 ≤ p)
  (hp_nonneg : 0 ≤ p)
  (haT : a ∈ Set.Icc (0 : ℝ) T)
  (hbT : b ∈ Set.Icc a T)
  (hYa : D.integral (fun x => (u a x) ^ p) ≤ M)
  (hYb_nonneg : 0 ≤ D.integral (fun x => (u b x) ^ p))
  (hmaxInt :
    ∫ s in a..b, max 1 (D.integral (fun x => (u s x) ^ p)) ≤ H) :
  ∃ C, 0 ≤ C ∧
    2 * ∫ s in a..b,
      D.integral (fun x =>
        (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      M + C * p * H
```

The upper-bound helper then sets, internally,

```text
Gbound = (M + C * p * ((b-a) * max 1 M)) / 2.
```

For the strict gap, however, the current existential upper-bound helper is slightly too opaque: to choose `Cnext` against `Ceps`, the proof should use an explicit-constant wrapper rather than hiding `Cdrop`, `Gbound`, and `Ceps` behind an existential.

## Frontier 1: LowerAverageWindow

### Mathematical construction

Fix an exponent `p ≥ p0`, `0 ≤ p`, and write

```text
Y(s) = integratedMoserEnergy D u p s,
Z(s) = integratedMoserEnergy D u (p + rho) s.
```

Assume the current induction hypothesis

```lean
hLp : LpPowerBoundedBefore D p T u
```

and choose its witness once:

```text
hLp = ⟨M0, hM0⟩,
M  := max 1 M0.
```

Then for every interior time,

```text
Y(s) ≤ M0 ≤ M.
```

This is the `M` that must be stored in the lower window. Do not let a later helper choose a different existential `M`.

Now suppose `0 < t < T` and

```text
Cnext < Z(t).
```

The standard time-thickness input is one of the following two forms.

#### Minimal continuity version

If all you need is the current `IntegratedMoserHighExcursionLowerAverageWindow` structure, continuity of `Z` on `[0,T]` suffices.

Choose `κ = 1/2`. Since `Cnext < Z(t)` and `0 < Cnext`, we have `κ*Cnext < Z(t)`. By continuity, choose `r_cont > 0` so that

```text
|s - t| < r_cont  ⇒  κ*Cnext ≤ Z(s).
```

Choose the endpoint-safe radius

```text
r_edge := min (t/2) ((T - t)/2),
δ      := min r_edge r_cont,
a      := t - δ,
b      := t + δ.
```

Then

```text
0 < a,
b < T,
a < b,
[a,b] ⊆ (0,T),
κ*Cnext ≤ Z(s) for all s ∈ [a,b].
```

Set

```text
lowerBound := (b - a) * (κ * Cnext).
```

Using interval integrability of `Z`, prove

```text
lowerBound ≤ ∫ s in a..b, Z(s).
```

This version is mathematically correct but gives no uniform lower bound on `b-a`. It is therefore not enough, by itself, to prove a uniform upper gap.

#### Quantitative thickness version needed for the actual first-crossing contradiction

For the full first-crossing step, the lower-window frontier should supply an additional length lower bound:

```text
ell0 > 0,
ell0 ≤ b - a,
κ*Cnext ≤ Z(s) on [a,b].
```

This is the real De Giorgi/Moser thickness input. It can come from a parabolic time-modulus estimate for the higher energy, or from a genuine first-crossing/high-excursion lemma. In Lean, keep it explicit; do not smuggle it into continuity.

The lower window is then exactly:

```text
a, b       := thickness-window endpoints,
M          := max 1 M0,
lowerBound := (b - a) * (κ * Cnext).
```

### Lean-friendly statement shape

Add the quantitative thickness as a separate analytic record. This avoids changing the existing lower-window record while still giving the upper-gap proof the length information it needs.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Quantitative high-excursion time thickness for the next Moser energy.
This is the genuine analytic lower-window frontier. -/
structure IntegratedMoserHighExcursionThickness
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p Cnext kappa ell0 : ℝ) : Prop where
  Cnext_pos : 0 < Cnext
  kappa_pos : 0 < kappa
  kappa_lt_one : kappa < 1
  ell0_pos : 0 < ell0
  produce :
    ∀ t, 0 < t → t < T →
      Cnext < integratedMoserEnergy D u (p + rho) t →
        ∃ a b : ℝ,
          a < b ∧
          0 < a ∧ b < T ∧
          a ∈ Set.Icc (0 : ℝ) T ∧
          b ∈ Set.Icc a T ∧
          ell0 ≤ b - a ∧
          (∀ s ∈ Set.Icc a b,
            kappa * Cnext ≤
              integratedMoserEnergy D u (p + rho) s)

/-- Quantitative lower window plus the already-chosen current-exponent bound. -/
structure IntegratedMoserQuantLowerAverageWindow
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p Cnext kappa ell0 t : ℝ) where
  base : IntegratedMoserHighExcursionLowerAverageWindow
    D u T rho p0 p Cnext t
  lower_eq : base.lowerBound =
    (base.b - base.a) * (kappa * Cnext)
  length_ge : ell0 ≤ base.b - base.a
  kappa_pos : 0 < kappa
  Cnext_pos : 0 < Cnext
  ell0_pos : 0 < ell0

/-- Build the lower-average window from a quantitative thickness frontier.
The proof is routine interval-integral monotonicity. -/
theorem lowerAverageWindow_of_highExcursionThickness
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p Cnext kappa ell0 t M : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hrho_nonneg : 0 ≤ rho)
    (hY_le_all :
      ∀ s, 0 < s → s < T →
        integratedMoserEnergy D u p s ≤ M)
    (hthick : IntegratedMoserHighExcursionThickness
      D u T rho p0 p Cnext kappa ell0)
    (ht0 : 0 < t) (htT : t < T)
    (hhigh : Cnext < integratedMoserEnergy D u (p + rho) t) :
    IntegratedMoserQuantLowerAverageWindow
      D u T rho p0 p Cnext kappa ell0 t := by
  /-
  Roadmap:
  1. Use `hthick.produce t ht0 htT hhigh` to obtain `a b`.
  2. Define `lowerBound := (b-a) * (kappa*Cnext)`.
  3. Current bound: for `s ∈ Icc a b`, use `0<a`, `b<T` to call `hY_le_all`.
  4. Higher-energy integrability: use
     `hreg.power_intervalIntegrable_of_Icc` at exponent `p+rho`.
  5. Lower integral: compare constant function `kappa*Cnext` to `Z(s)` on `Icc a b`.
  6. Package the existing `IntegratedMoserHighExcursionLowerAverageWindow` plus
     `lower_eq` and `length_ge`.
  -/
  sorry

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

The continuity-only lemma can also be useful, but should be named honestly:

```lean
/-- Continuity gives a positive window, but not a uniform length bound. -/
theorem lowerAverageWindow_of_highExcursion_continuity
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p Cnext t M : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hrho_nonneg : 0 ≤ rho)
    (hCnext_pos : 0 < Cnext)
    (hY_le_all :
      ∀ s, 0 < s → s < T →
        integratedMoserEnergy D u p s ≤ M)
    (ht0 : 0 < t) (htT : t < T)
    (hhigh : Cnext < integratedMoserEnergy D u (p + rho) t) :
    IntegratedMoserHighExcursionLowerAverageWindow
      D u T rho p0 p Cnext t := by
  /-
  Choose κ = 1/2 and δ = min edge-radius continuity-radius.
  This proves the current lower-window record, but not the strict upper gap.
  -/
  sorry
```

## Frontier 2: UpperGapWitness

### Mathematical construction

Assume a lower window with the strengthened data

```text
ell0 ≤ b-a,
lowerBound = (b-a) * (κ*Cnext),
M ≥ 1.
```

From `hinteg p hp`, choose the drop constant

```text
Cdrop ≥ 0.
```

For the actual window, the integrated dissipation gives

```text
∫_a^b G(s) ds ≤ Gbound
```

where

```text
Gbound := (M + Cdrop * p * ((b-a) * max 1 M)) / 2.
```

Since `M ≥ 1`, this is

```text
Gbound = (M + Cdrop * p * (b-a) * M) / 2.
```

Also `b-a ≤ T`, so define the uniform bound

```text
Gbar := (M + Cdrop * p * T * M) / 2,
```

and prove

```text
Gbound ≤ Gbar.
```

Now fix epsilon before choosing the threshold. The simplest choice is

```text
eps★ := 1.
```

Use relative Moser interpolation at this epsilon:

```text
Z(s) ≤ eps★ * G(s) + Ceps★ * Y(s),
```

with `Ceps★ ≥ 0`. After integration and the current bound `Y(s) ≤ M`,

```text
∫_a^b Z(s) ds ≤ eps★ * Gbound + (b-a) * Ceps★ * M.
```

Choose the next threshold after `Ceps★` is known:

```text
Cnext := 1 + max (4 * eps★ * Gbar / (κ * ell0))
                 (4 * Ceps★ * M / κ).
```

Then:

```text
eps★ * Gbound
  ≤ eps★ * Gbar
  < (κ*Cnext*ell0)/4
  ≤ (κ*Cnext*(b-a))/4
  = lowerBound/4,
```

and

```text
(b-a) * Ceps★ * M
  < (b-a) * (κ*Cnext/4)
  = lowerBound/4.
```

Therefore

```text
eps★ * Gbound + (b-a) * Ceps★ * M < lowerBound.
```

This is the strict gap.

### Why not choose epsilon after seeing the window?

For a fixed lower window, one might try

```text
eps < lowerBound / (4 * (Gbound + 1)).
```

That controls the gradient term. It does **not** control

```text
(b-a) * Ceps * M,
```

because `Ceps` may increase as `eps` decreases. Hence the following is not a valid theorem from the current hypotheses:

```lean
∀ hwin, ∃ eps Gbound Ceps,
  eps * Gbound + (hwin.b - hwin.a) * (Ceps * hwin.M) < hwin.lowerBound
```

unless the lower-window hypothesis already includes enough quantitative size to dominate the selected `Ceps`. The Lean implementation should reflect this by either:

1. choosing `eps★`, `Ceps★`, and `Cnext` before producing lower windows, or
2. keeping `UpperGapWitness` as an explicit analytic frontier.

### Lean-friendly statement shapes

First add explicit-constant wrappers. The current existential theorem is fine for upper bounds, but for a threshold proof we need the exact constants used in `Cnext`.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Explicit drop constant on windows, unpacked from
`IntegratedMoserDissipationDropBefore`. -/
def IntegratedMoserDropConstant
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p Cdrop : ℝ) : Prop :=
  0 ≤ Cdrop ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      integratedMoserEnergy D u p t2 -
          integratedMoserEnergy D u p t1 +
        2 * ∫ s in t1..t2,
          integratedMoserGradientEnergy D u p s ≤
      Cdrop * p * ∫ s in t1..t2,
        max 1 (integratedMoserEnergy D u p s)

/-- Explicit relative-Moser interpolation constant for one epsilon. -/
def RelativeMoserInterpolationConstant
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p eps Ceps : ℝ) : Prop :=
  0 ≤ Ceps ∧
    ∀ t, 0 < t → t < T →
      integratedMoserEnergy D u (p + rho) t ≤
        eps * integratedMoserGradientEnergy D u p t +
        Ceps * integratedMoserEnergy D u p t

/-- Explicit version of the gradient extraction lemma. -/
theorem integratedMoser_gradientIntegral_le_with_constant
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p a b M H Cdrop : ℝ}
    (hdropC : IntegratedMoserDropConstant D u T p Cdrop)
    (hp_nonneg : 0 ≤ p)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hYa : integratedMoserEnergy D u p a ≤ M)
    (hYb_nonneg : 0 ≤ integratedMoserEnergy D u p b)
    (hmaxInt :
      ∫ s in a..b, max 1 (integratedMoserEnergy D u p s) ≤ H) :
    2 * ∫ s in a..b, integratedMoserGradientEnergy D u p s ≤
      M + Cdrop * p * H := by
  /-
  Same proof as `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds`,
  except `Cdrop` is supplied explicitly instead of obtained existentially.
  -/
  sorry

/-- Explicit fixed-window upper witness with the constants that were used to
choose `Cnext`. -/
theorem integratedMoser_windowUpperBoundWitness_of_precrossing_with_constants
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps Cdrop Ceps : ℝ}
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M)
    (hdropC : IntegratedMoserDropConstant D u T p Cdrop)
    (hrelC : RelativeMoserInterpolationConstant D u T rho p eps Ceps)
    (heps : 0 < eps) :
    IntegratedMoserWindowUpperBoundWitness
      D u rho p a b M eps
      ((M + Cdrop * p * ((b - a) * max (1 : ℝ) M)) / 2)
      Ceps := by
  /-
  Roadmap:
  1. `H := (b-a) * max 1 M` from
     `IntegratedMoserPrecrossingIntervalData.maxOneEnergy_timeIntegral_le`.
  2. Use `integratedMoser_gradientIntegral_le_with_constant` to get the displayed
     `Gbound`.
  3. Integrate `hrelC` over `[a,b]` using
     `intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on`.
  4. Replace `∫G` by `Gbound` and `Y` by `M` on the window.
  -/
  sorry

/-- Numeric threshold that makes the fixed-window upper bound strictly smaller
than the lower average. -/
def integratedMoserGapThreshold
    (kappa ell0 eps Gbar Ceps M : ℝ) : ℝ :=
  1 + max (4 * eps * Gbar / (kappa * ell0))
          (4 * Ceps * M / kappa)

/-- Pure arithmetic gap lemma. -/
theorem upperGap_lt_lower_of_threshold
    {kappa ell0 eps Gbar Gbound Ceps M Cnext a b lowerBound : ℝ}
    (hkappa : 0 < kappa)
    (hell0 : 0 < ell0)
    (heps : 0 < eps)
    (hM_nonneg : 0 ≤ M)
    (hCeps_nonneg : 0 ≤ Ceps)
    (hGbound_le : Gbound ≤ Gbar)
    (hlength : ell0 ≤ b - a)
    (hlower_eq : lowerBound = (b - a) * (kappa * Cnext))
    (hCnext_ge : integratedMoserGapThreshold kappa ell0 eps Gbar Ceps M ≤ Cnext) :
    eps * Gbound + (b - a) * (Ceps * M) < lowerBound := by
  /-
  Arithmetic only.
  From `hCnext_ge` and the `+1`, derive strict inequalities:
    eps*Gbar < (kappa*Cnext*ell0)/4,
    Ceps*M   < (kappa*Cnext)/4.
  Then use `ell0 ≤ b-a` and `lower_eq`.
  -/
  sorry

/-- Package a fixed explicit upper witness and numeric gap as the existing
`IntegratedMoserWindowUpperGapWitness`. -/
theorem upperGapWitness_of_explicit_upper_and_threshold
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {rho p a b M lowerBound eps Gbound Ceps : ℝ}
    (heps : 0 < eps)
    (hupper : IntegratedMoserWindowUpperBoundWitness
      D u rho p a b M eps Gbound Ceps)
    (hgap : eps * Gbound + (b - a) * (Ceps * M) < lowerBound) :
    IntegratedMoserWindowUpperGapWitness
      D u rho p a b M lowerBound :=
  { eps := eps
    Gbound := Gbound
    Ceps := Ceps
    eps_pos := heps
    upperWitness := hupper
    upper_lt_lower := hgap }

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

## Full per-exponent construction order

For a theorem building `IntegratedMoserLowerUpperWindowFrontiers D u T rho p0 p`, use this order.

### Inputs

```text
hp             : p0 ≤ p
hp_nonneg       : 0 ≤ p
hrho_nonneg     : 0 ≤ rho
hLp             : LpPowerBoundedBefore D p T u
hreg            : IntegratedMoserFirstCrossingRegularity D u T p0
hnonneg         : IntegratedMoserEnergyNonnegativity D u T p0
hinteg          : IntegratedMoserDissipationDropBefore D u T rho p0
hrel            : RelativeMoserInterpolationBefore D u T rho p0
hthicknessData  : supplies κ, ell0 and high-excursion thickness
```

### Choices

1. Unpack the current exponent bound once:

   ```text
   hLp = ⟨M0, hM0⟩,
   M  = max 1 M0.
   ```

2. Unpack the integrated drop constant once:

   ```text
   hinteg p hp = ⟨Cdrop, hCdrop_nonneg, hCdrop⟩.
   ```

3. Fix epsilon before choosing the threshold:

   ```text
   eps★ = 1.
   ```

   Then unpack relative interpolation once:

   ```text
   hrel p hp eps★ eps★_pos = ⟨Ceps★, hCeps★_nonneg, hrel_eps★⟩.
   ```

4. Choose thickness constants from the high-excursion thickness frontier:

   ```text
   κ    = 1/2       -- or whatever the analytic thickness theorem supplies
   ell0 > 0.
   ```

5. Define the safe uniform gradient upper bound:

   ```text
   Gbar := (M + Cdrop * p * T * M) / 2.
   ```

6. Define the next threshold:

   ```text
   Cnext := integratedMoserGapThreshold κ ell0 eps★ Gbar Ceps★ M.
   ```

   i.e.

   ```text
   Cnext = 1 + max (4 * eps★ * Gbar / (κ * ell0))
                   (4 * Ceps★ * M / κ).
   ```

7. Define the lower frontier at this `Cnext`. For any high point `t`, the lower-window construction returns `[a,b]`, with

   ```text
   lowerBound = (b-a) * (κ*Cnext),
   ell0 ≤ b-a,
   Y(s) ≤ M on [a,b].
   ```

8. Define the upper-gap frontier by using the same explicit constants `eps★`, `Ceps★`, and `Cdrop`, building the fixed-window upper witness, proving `Gbound ≤ Gbar`, and applying the arithmetic gap lemma.

### Lean skeleton for the final builder

```lean
/-- Build the split lower/upper frontier for one exponent from quantitative
high-excursion thickness and the existing integrated Moser estimates. -/
theorem integratedMoserLowerUpperWindowFrontiers_of_quantThickness
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p kappa ell0 : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hrho_nonneg : 0 ≤ rho)
    (hT_pos : 0 < T)
    (hLp : LpPowerBoundedBefore D p T u)
    -- analytic input: for the Cnext chosen in the proof, high excursions have
    -- thickness with these `kappa` and `ell0`.
    (hthick_for_all_Cnext :
      ∀ Cnext,
        0 < Cnext →
          IntegratedMoserHighExcursionThickness
            D u T rho p0 p Cnext kappa ell0) :
    IntegratedMoserLowerUpperWindowFrontiers D u T rho p0 p := by
  classical
  /-
  1. Unpack `hLp` as `M0`, set `M := max 1 M0`.
  2. Unpack `hinteg p hp` as `Cdrop`.
  3. Set `eps★ := 1` and unpack `hrel p hp eps★` as `Ceps★`.
  4. Set `Gbar := (M + Cdrop*p*T*M)/2`.
  5. Set `Cnext := integratedMoserGapThreshold kappa ell0 eps★ Gbar Ceps★ M`.
  6. `lowerAverage.produce` uses
       `lowerAverageWindow_of_highExcursionThickness` with
       `hthick_for_all_Cnext Cnext Cnext_pos` and the same `M`.
  7. `upperGap.produce hwin`:
       a. build `IntegratedMoserPrecrossingIntervalData` via
          `integratedMoserPrecrossingIntervalData_of_regular_window`;
       b. build explicit upper witness via
          `integratedMoser_windowUpperBoundWitness_of_precrossing_with_constants`;
       c. prove `Gbound ≤ Gbar` using `b-a ≤ T`, `0≤Cdrop`, `0≤p`, `M≥1`;
       d. prove numeric gap using `upperGap_lt_lower_of_threshold`;
       e. package with `upperGapWitness_of_explicit_upper_and_threshold`.
  -/
  sorry
```

This is the compile-oriented shape I would add after `P3MoserIntegratedClosure.lean`, likely in a new file such as:

```text
ShenWork/PDE/P3MoserHighExcursionFrontiers.lean
```

with only

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

at the top. That avoids cycles: the new file consumes the structures and fixed-window helpers already defined in `P3MoserIntegratedClosure`; statement assembly can import the new file only when it is ready to expose the strengthened frontier.

## The exact no-go routes

1. **Do not prove `UpperGapWitness` by `eps → 0` alone.**  The term `Ceps*M` is not monotone small in `eps`; in ordinary Young/GN estimates it usually grows as `eps` shrinks.

2. **Do not rely on the current existential `integratedMoser_windowUpperBoundData_of_precrossing` when choosing `Cnext`.**  It hides the `Ceps` witness. For threshold selection, use an explicit-constant wrapper.

3. **Do not claim a quantitative strict gap from mere continuity of `Z`.**  Continuity gives a positive window but not a uniform lower length. Without either a length lower bound or an equivalent lowerBound-size condition, a pointwise spike can be too narrow for the integrated upper estimate to contradict it.

4. **Do not let `M` be chosen twice.**  The same `M := max 1 M0` extracted from `hLp` must be used in `Cnext`, in the lower window, and in the upper bound.

## Minimal theorem DAG

```text
Existing:
  IntegratedMoserDissipationDropBefore
  RelativeMoserInterpolationBefore
  IntegratedMoserFirstCrossingRegularity
  IntegratedMoserEnergyNonnegativity
  LpPowerBoundedBefore

New arithmetic/constant wrappers:
  IntegratedMoserDropConstant
  RelativeMoserInterpolationConstant
  integratedMoser_gradientIntegral_le_with_constant
  integratedMoser_windowUpperBoundWitness_of_precrossing_with_constants
  integratedMoserGapThreshold
  upperGap_lt_lower_of_threshold
  upperGapWitness_of_explicit_upper_and_threshold

New lower-window frontier:
  IntegratedMoserHighExcursionThickness
  IntegratedMoserQuantLowerAverageWindow
  lowerAverageWindow_of_highExcursionThickness
  optional: lowerAverageWindow_of_highExcursion_continuity

New assembly:
  integratedMoserLowerUpperWindowFrontiers_of_quantThickness
    → IntegratedMoserLowerUpperWindowFrontiers.to_contradictionWindowFrontier
    → integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
    → moser_iteration_chain_of_integrated_first_crossing_step
    → intervalDomain_boundedBefore_of_integrated_first_crossing_step
```

## Bottom line

The honest construction is:

```text
M          := max 1 M0, where hLp = ⟨M0, hM0⟩
a,b        := high-excursion thickness window for Z = Y_{p+rho}
lowerBound := (b-a) * (κ*Cnext)
eps        := fixed eps★, e.g. 1
Ceps       := relative-Moser constant for eps★
Gbound     := (M + Cdrop*p*((b-a)*max 1 M))/2
Gbar       := (M + Cdrop*p*T*M)/2
Cnext      := 1 + max (4*eps★*Gbar/(κ*ell0)) (4*Ceps*M/κ)
```

Then the lower average and upper estimate are incompatible. This is the standard DGNM/Moser threshold argument in Lean-friendly quantifier order.