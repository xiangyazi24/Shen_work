# Q2857 shen2: EnergyStep pointwise-to-window audit

Repo target: `xiangyazi24/Shen_work`, Lean 4, default branch `main`.

Files inspected directly:

```text
ShenWork/Paper2/IntervalDomainEnergyStep.lean
ShenWork/Paper2/IntervalDomainChain.lean
ShenWork/Paper2/IntervalDomainBootstrap.lean
ShenWork/Paper2/IntervalDomainStructuredMoserData.lean
ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/PDE/P3MoserDissipationShape.lean
ShenWork/PDE/P3MoserEnergyContinuity.lean
```

No proposed edits touch:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
```

## Bottom line

The existing `IntervalDomainEnergyStep.lean` wrappers around the requested region **do not already produce** the integrated full-window higher-power energy input needed by the local `integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative`-style absorption wrapper.

What they do produce is strict-time Moser-chain data: pointwise or per-exponent inequalities on `0 < t < T`, plus wrappers that reduce these pointwise inequalities to `LpPowerBoundedBefore` by the old single-step Moser chain. They do **not** integrate the full pointwise inequality over closed windows, and they do **not** package a general-p FTC/absolute-continuity theorem for

```lean
Y_p(t) = D.integral (fun x => (u t x) ^ p)
```

or

```lean
Y_p(t) = integratedMoserEnergy D u p t.
```

Thus the smallest useful new theorem is a wrapper that consumes an explicit window-FTC/AC assumption and converts `LpBootstrapEnergyInequality` into the desired window inequality. The genuine missing producer-side piece is the FTC/AC assumption, not the scalar integration algebra.

## Grep/check plan and expected results

A concrete Codex check plan:

```bash
grep -R "def LpBootstrapEnergyInequality\|LpBootstrapEnergyInequality" \
  ShenWork/Paper2/IntervalDomainBootstrap.lean \
  ShenWork/Paper2/IntervalDomainEnergyStep.lean \
  ShenWork/Paper2/IntervalDomainStructuredMoserData.lean \
  ShenWork/PDE/P3MoserIntegratedClosure.lean

grep -R "IntegratedMoserDissipationDropBeforeCoeff\|integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative" \
  ShenWork/PDE ShenWork/Paper2

grep -R "integratedMoserEnergy\|integratedMoserGradientEnergy" \
  ShenWork/PDE/P3MoserIntegratedClosure.lean

grep -R "intervalDomain_lp_energy_hLpTime\|intervalDomainPowerEnergy_hasDerivAt\|HasDerivAt.*intervalDomainLpEnergy" \
  ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean \
  ShenWork/PDE/P3MoserEnergyContinuity.lean

grep -R "FTC\|WindowFTC\|integral.*deriv.*integratedMoserEnergy\|absolute" \
  ShenWork/PDE ShenWork/Paper2
```

Expected current results from origin/main:

* `LpBootstrapEnergyInequality` is heavily consumed by EnergyStep wrappers, but only in strict-time Moser-chain form.
* `IntegratedMoserDissipationDropBeforeCoeff` / `integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative` were not found on `main` in this audit; they appear to be local/newer concepts. The audit below targets the needed shape.
* `integratedMoserEnergy` and `integratedMoserGradientEnergy` are defined in `P3MoserIntegratedClosure.lean`.
* `IntervalDomainLpTimeLeibniz.lean` provides pointwise `HasDerivAt` and `deriv` equalities on strict interior times.
* No existing theorem was found that packages the full general-p window FTC
  ```lean
  ∫ deriv Y = Y t2 - Y t1
  ```
  for `integratedMoserEnergy` on arbitrary windows.

## Existing EnergyStep wrappers near lines 1850--3230

The relevant existing wrappers are strict-time/per-exponent chain wrappers:

```lean
moser_step_family_of_energy_dissipation_interpolation
moser_interpolation_of_relative_interpolation_and_lp_bound
moser_step_of_energy_dissipation_relative_interpolation
moser_iteration_chain_of_energy_dissipation_relative_interpolation
all_exponents_of_energy_dissipation_relative_interpolation_lpmono
moser_relative_eps_absorption_family_of_mass_gradient_estimate
moser_iteration_chain_of_energy_dissipation_mass_gradient_relative
all_exponents_of_energy_dissipation_mass_gradient_relative_lpmono
intervalDomain_all_exponents_of_energy_dissipation_mass_gradient_relative
intervalDomain_all_exponents_of_energy_dissipation_relative_interpolation
intervalDomain_all_exponents_of_energy_dissipation_interpolation_inside_nonneg
intervalDomain_all_exponents_of_energy_dissipation_mass_gradient_inside_nonneg
intervalDomain_all_exponents_of_energy_dissipation_mass_gradient_relative_inside_nonneg
moserClosure_dissipationDropBefore_of_raw
moserClosure_relativeInterpolationBefore_of_raw
moserClosure_relativeInterpolationBefore_of_mass_gradient_estimate
intervalDomain_moserClosure_relativeInterpolationBefore_of_mass_gradient_estimate
intervalDomain_moserClosure_relativeInterpolationBefore_of_Lemma_4_1
intervalDomain_relativeMoserEndpointComponents_of_energy_interfaces
intervalDomain_relativeMoserEndpointComponents_of_raw_energy_relative
intervalDomain_relativeMoserEndpointComponents_of_crossDiffusion_energy_interfaces
```

The important one for this audit is:

```lean
theorem moser_step_family_of_energy_dissipation_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hdiss : ...)
    (hinterp : ...) :
    ∀ p, p0 ≤ p →
      ∃ A > 0, ∃ K > 0, ∃ L_const,
        (∀ t, 0 < t → t < T →
          A * D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
          K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) ∧
        ...
```

It consumes the derivative/dissipation predicate to **drop** the derivative and `B*Y` terms, then returns the old pointwise Moser step. This is useful for `LpPowerBoundedBefore`, but it is not the integrated window producer now needed.

The lower-level source `LpBootstrapEnergyInequality` itself has the full pointwise inequality:

```lean
(1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t
  + A * D.integral (fun x =>
      (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)
  + B * D.integral (fun x => (u t x) ^ p)
≤ K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const
```

This is the correct source for the desired window inequality; the existing wrappers just do not integrate it.

## Existing FTC/regularity support

`IntervalDomainLpTimeLeibniz.lean` proves strict-time derivative identities:

```lean
intervalDomainPowerEnergy_hasDerivAt
intervalDomain_lp_timeLeibniz
intervalDomain_lp_energy_hLpTime
intervalDomain_lp_energy_hLpTime_frontier
```

The endpoint/continuity support in `P3MoserEnergyContinuity.lean` includes:

```lean
intervalDomain_energyContinuousOn_Ioo
IntervalDomainPowerEnergyEndpointContinuity
IntervalDomainInitialPowerEnergyContinuityAtZero
intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
```

These are not yet a full window FTC package. They prove continuity and pointwise differentiability on the interior, but they do not currently produce:

```lean
IntervalIntegrable (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
  volume t1 t2

∫ s in t1..t2, deriv (fun τ => integratedMoserEnergy D u p τ) s =
  integratedMoserEnergy D u p t2 - integratedMoserEnergy D u p t1
```

That is the missing regularity/FTC frontier.

## Smallest useful new wrapper: strict-window form

This theorem is the smallest wrapper that should be provable once a strict-window FTC assumption is supplied. It belongs in `P3MoserIntegratedClosure.lean`, because that file owns `integratedMoserEnergy`, `integratedMoserGradientEnergy`, and the window plumbing.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainEnergyStep

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

/-- Strict-window FTC package for Moser energies.  This is the missing bridge
from strict-time Leibniz/derivative facts to window-integrated energy estimates. -/
def IntegratedMoserEnergyWindowFTCStrict
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ a b, a ≤ b → 0 < a → b < T →
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
      volume a b ∧
    ∫ s in a..b,
        deriv (fun τ => integratedMoserEnergy D u p τ) s =
      integratedMoserEnergy D u p b - integratedMoserEnergy D u p a

/-- Nonnegative time integral for current Moser energy on strict windows.  For
`intervalDomain` this should follow from positivity/nonnegativity plus interval
integral monotonicity, but at the abstract wrapper level it is best kept as a
small explicit hypothesis. -/
def IntegratedMoserEnergyTimeIntegralNonnegStrict
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ a b, a ≤ b → 0 < a → b < T →
    0 ≤ ∫ s in a..b, integratedMoserEnergy D u p s

/-- Strict-window integration of `LpBootstrapEnergyInequality` into the
higher-power integrated input shape. -/
theorem integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_strict
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTCStrict D u T p0)
    (hYnonneg : IntegratedMoserEnergyTimeIntegralNonnegStrict D u T p0)
    (hp : p0 ≤ p) (hp_pos : 0 < p)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < T)
    (hDeriv_int :
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s) volume a b)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s) volume a b)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s) volume a b) :
    ∃ Awin Kwin C0 Lwin : ℝ,
      0 < Awin ∧ 0 ≤ Kwin ∧ 0 ≤ C0 ∧ 0 ≤ Lwin ∧
      integratedMoserEnergy D u p b - integratedMoserEnergy D u p a +
        Awin * ∫ s in a..b, integratedMoserGradientEnergy D u p s ≤
        C0 * p *
            (∫ s in a..b, max (1 : ℝ) (integratedMoserEnergy D u p s)) +
          Kwin *
            (∫ s in a..b, integratedMoserEnergy D u (p + rho) s) +
          Lwin *
            (∫ s in a..b, max (1 : ℝ) (integratedMoserEnergy D u p s)) := by
  rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hpoint⟩
  let Awin : ℝ := p * A
  let Kwin : ℝ := p * K
  let C0 : ℝ := 0
  let Lwin : ℝ := max 0 (p * L_const)
  refine ⟨Awin, Kwin, C0, Lwin, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_pos hp_pos hA
  · exact mul_nonneg hp_pos.le hK.le
  · norm_num [C0]
  · exact le_max_left _ _
  ·
    -- Proof plan:
    -- 1. Use `hpoint s` on `s ∈ Icc a b`; strictness follows from `ha`, `hb`.
    -- 2. Multiply by `p > 0` to get
    --      deriv Y + Awin*G + p*B*Y ≤ Kwin*Z + p*L_const.
    -- 3. Integrate over `a..b` with `intervalIntegral.integral_mono_on`.
    -- 4. Rewrite `∫ deriv Y` using `(hFTC p hp a b hab ha hb).2`.
    -- 5. Drop `(p*B) * ∫Y` from the left using `hYnonneg` and `hB`.
    -- 6. Bound `(p*L_const)*(b-a)` by `Lwin * ∫ max 1 Y` using
    --      `intervalIntegrable_max_one_of_intervalIntegrable hY_int` and
    --      pointwise `1 ≤ max 1 Y`.
    -- Expected tactics: `intervalIntegral.integral_mono_on`,
    -- `intervalIntegral.integral_add`, `intervalIntegral.integral_const_mul`,
    -- `intervalIntegral.integral_const`, then `linarith`/`nlinarith`.
    sorry
```

The final `sorry` in the sketch is not a recommendation to land a sorry; it marks the routine proof body. The signature is the important part: the only non-routine input is `hFTC` plus simple nonnegativity/integrability hypotheses.

### Why `hDeriv_int` is listed separately although `hFTC` includes it

A compile-oriented version should either remove `hDeriv_int` and use `(hFTC p hp a b hab ha hb).1`, or keep it explicit for readability. The cleaner final theorem should use the `hFTC` pair and omit `hDeriv_int`.

## Closed-window version

For closed windows of the form required by `IntegratedMoserDissipationDropBefore` / coefficient variants,

```lean
∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T, ...
```

there is an endpoint issue: `LpBootstrapEnergyInequality` only gives the pointwise inequality for strict times `0 < t < T`. The closed theorem therefore needs an a.e. endpoint bridge.

Recommended closed-window support predicates/helpers:

```lean
/-- Closed-window FTC package for Moser energies. -/
def IntegratedMoserEnergyWindowFTC
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
      volume t1 t2 ∧
    ∫ s in t1..t2,
        deriv (fun τ => integratedMoserEnergy D u p τ) s =
      integratedMoserEnergy D u p t2 - integratedMoserEnergy D u p t1

/-- A.e. monotonicity for interval integrals. -/
theorem intervalIntegral_integral_mono_on_ae
    {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hle : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), f s ≤ g s) :
    ∫ s in a..b, f s ≤ ∫ s in a..b, g s := by
  -- Use the Ioc representation of interval integrals and Lebesgue integral
  -- monotonicity for a.e. ordered integrable functions.
  sorry

/-- On a closed window contained in `[0,T]`, almost every integration point is
in the strict interior `(0,T)`. -/
theorem ae_strictInterior_of_closed_window
    {T t1 t2 : ℝ}
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) T)
    (ht2 : t2 ∈ Set.Icc t1 T) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)), 0 < s ∧ s < T := by
  -- `0 < s` follows from `t1 < s` and `0 ≤ t1`.
  -- `s < T` follows from `s ≤ t2 ≤ T` after discarding possible `s = T`,
  -- a singleton-null endpoint.
  sorry
```

Then the closed theorem is the same as the strict theorem, but the proof uses `intervalIntegral_integral_mono_on_ae` and `ae_strictInterior_of_closed_window` instead of pointwise `intervalIntegral.integral_mono_on` on `Set.Icc t1 t2`.

## What existing theorem names are usable now

Directly usable as sources:

```lean
-- Pointwise full energy source
LpBootstrapEnergyInequality
intervalDomain_LpBootstrapEnergyInequality_of_regularity

-- Strict-time derivative/Leibniz source
intervalDomainPowerEnergy_hasDerivAt
intervalDomain_lp_timeLeibniz
intervalDomain_lp_energy_hLpTime
intervalDomain_lp_energy_hLpTime_frontier

-- Continuity support, not FTC
intervalDomain_energyContinuousOn_Ioo
intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity

-- Existing strict-time Moser-chain wrappers, not window producers
moser_step_family_of_energy_dissipation_interpolation
moser_step_of_energy_dissipation_relative_interpolation
moser_iteration_chain_of_energy_dissipation_relative_interpolation
all_exponents_of_energy_dissipation_relative_interpolation_lpmono
moserClosure_dissipationDropBefore_of_raw
moserClosure_relativeInterpolationBefore_of_raw
```

Usable from `P3MoserIntegratedClosure.lean`:

```lean
integratedMoserEnergy
integratedMoserGradientEnergy
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
intervalIntegrable_max_one_of_intervalIntegrable
integratedMoserGradientEnergy_intervalIntegral_nonneg_of_package
intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
```

## What is genuinely missing

1. **General-p window FTC/absolute continuity** for `integratedMoserEnergy`.  Existing time-Leibniz gives pointwise derivatives, but not the window identity.

2. **A.e. closed-window endpoint bridge** if the final theorem must quantify over closed windows containing `0` or `T`.

3. **Coefficient surplus for fixed `theta`**. `LpBootstrapEnergyInequality` gives `A > 0` and `K > 0`; it does not imply `theta < p*A` or `K*eps ≤ p*A - theta`. For fixed coefficient absorption, a surplus condition must be carried explicitly, or the integrated dissipation predicate must remain coefficient-parameterized.

## Best wrapper shape to feed coefficient absorption

Because matching existential constants across separate theorems is painful in Lean, use a bundled structure rather than a loose tuple.

```lean
structure IntegratedHigherPowerEnergyWindowInput
    (theta : ℝ) (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  produce : ∀ p, p0 ≤ p →
    ∃ Awin Kwin C0 Lwin : ℝ,
      0 < Awin ∧ 0 ≤ Kwin ∧ 0 ≤ C0 ∧ 0 ≤ Lwin ∧
      -- optional but needed for fixed-theta absorption:
      theta < Awin ∧
      (∀ eps, 0 < eps → Kwin * eps ≤ Awin - theta →
        ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          integratedMoserEnergy D u p t2 - integratedMoserEnergy D u p t1 +
            Awin * ∫ s in t1..t2, integratedMoserGradientEnergy D u p s ≤
          C0 * p *
              (∫ s in t1..t2,
                max (1 : ℝ) (integratedMoserEnergy D u p s)) +
            Kwin *
              (∫ s in t1..t2, integratedMoserEnergy D u (p + rho) s) +
            Lwin *
              (∫ s in t1..t2,
                max (1 : ℝ) (integratedMoserEnergy D u p s)))
```

A producer from `LpBootstrapEnergyInequality` cannot fill `theta < Awin` unless an explicit surplus hypothesis is added:

```lean
(hsurplus : ∀ p, p0 ≤ p → 0 < p →
  -- after unwrapping henergy's A, K, require theta < p*A
  ...)
```

The more Lean-friendly alternative is to omit `theta < Awin` from the energy-window producer and let the downstream absorption wrapper require an `eps` plus `Kwin * eps ≤ Awin - theta` at the call site.

## Recommended implementation order

1. Add `IntegratedMoserEnergyWindowFTCStrict` as a frontier/predicate.
2. Add strict wrapper:
   ```lean
   integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_strict
   ```
   consuming `hFTC`, integrability, and nonnegativity.
3. Add closed-window a.e. helpers:
   ```lean
   intervalIntegral_integral_mono_on_ae
   ae_strictInterior_of_closed_window
   ```
4. Add closed wrapper:
   ```lean
   integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_closed
   ```
5. Only then wire to `integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative`, with surplus as an explicit input or using a coefficient-parameterized target.

## Conclusion

Existing `IntervalDomainEnergyStep.lean` wrappers do **not** already give the full-window integrated energy inequality. They stop at pointwise strict-time Moser-chain wrappers. The smallest new wrapper should consume a window FTC/AC theorem and integrate `LpBootstrapEnergyInequality`. The true missing theorem is the general-p FTC/absolute-continuity producer for `Y_p`; endpoint/a.e. handling is a second, mostly measure-theoretic bridge for closed windows.
