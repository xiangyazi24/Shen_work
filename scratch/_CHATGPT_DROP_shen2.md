# Q2854 shen2: pointwise-to-window energy input for integrated Moser absorption

Repo target: `xiangyazi24/Shen_work`, Lean 4, default branch `main`.

Files inspected directly:

```text
ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean
ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean
ShenWork/Paper2/IntervalDomainEnergyStep.lean
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/PDE/P3MoserDissipationShape.lean
ShenWork/PDE/P3MoserEnergyContinuity.lean
```

I did not propose edits to:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
```

## Executive audit

The existing pointwise theorem

```lean
intervalDomain_LpBootstrapEnergyInequality_of_regularity
```

already gives the strict-time pointwise energy inequality in the form needed for later integration:

```lean
henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0
```

For each `p ≥ p0`, this exposes constants

```lean
A > 0, B > 0, K > 0, L_const : ℝ
```

and a strict-interior pointwise estimate

```lean
(1 / p) * deriv (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t
  + A * G_p(t) + B * Y_p(t)
≤ K * Z_(p+rho)(t) + L_const
```

for `0 < t < T`.

However, turning this into the closed-window input

```lean
Y_p(t2) - Y_p(t1) + Awin * ∫ G_p ≤
  C0 * p * ∫ max(1, Y_p) + Kwin * ∫ Z_(p+rho) + Lwin * ∫ max(1, Y_p)
```

requires two producer-side ingredients that are **not currently provided by** `IntervalDomainLpTimeLeibniz.lean` alone:

1. an FTC/absolute-continuity theorem for the power energy `Y_p`; and
2. an endpoint/a.e. integration bridge, because the pointwise estimate only holds on `0 < t < T`, while the target windows are closed and may include `0` or `T`.

The scalar bookkeeping and constant exposure are provable once those two inputs are supplied. The coefficient surplus

```lean
Kwin * eps ≤ Awin - theta
```

is **not** guaranteed by the existing `LpBootstrapEnergyInequality` type; it must be exposed as a separate surplus hypothesis/frontier, or the coefficient `theta` must be chosen after seeing the produced constants.

## Existing names that matter

### `IntervalDomainLpTimeLeibniz.lean`

This file proves pointwise time differentiability on strict interior times:

```lean
intervalDomain_lp_timeLeibniz
intervalDomain_lp_timeLeibniz_intervalIntegral
intervalDomain_lp_energy_hLpTime
intervalDomain_lp_energy_hLpTime_frontier
```

The main output is:

```lean
theorem intervalDomain_lp_energy_hLpTime_frontier
    {p : CM2Params} {T q : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    ∀ s, 0 < s → s < T →
      deriv (fun τ => intervalDomainLpEnergy q u τ) s =
        q * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm q u s)
```

This is a pointwise derivative identity. It does **not** state that `Y_p` is absolutely continuous on every window, that `deriv Y_p` is interval-integrable, or that

```lean
∫ s in t1..t2, deriv Y_p s = Y_p t2 - Y_p t1
```

### `P3MoserEnergyContinuity.lean`

This file supplies continuity, not FTC:

```lean
intervalDomain_energyContinuousOn_Ioo
IntervalDomainPowerEnergyEndpointContinuity
IntervalDomainInitialPowerEnergyContinuityAtZero
intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
```

It is useful support for a future FTC proof, but continuity alone does not give the window identity for `∫ deriv Y_p`.

### `P3MoserIntegratedClosure.lean`

This file already contains the time-window infrastructure:

```lean
integratedMoserEnergy
integratedMoserGradientEnergy
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
intervalIntegrable_max_one_of_intervalIntegrable
integratedMoserGradientEnergy_intervalIntegral_nonneg_of_package
```

It also already records the strict-window design pattern: windows used by the high-excursion route carry

```lean
ha_pos : 0 < a
hb_lt : b < T
```

because many pointwise PDE estimates are strict-interior only.

## Minimal theorem layer 1: FTC/AC frontier for `Y_p`

Add this frontier in `P3MoserIntegratedClosure.lean`, near the definitions of `integratedMoserEnergy` and `integratedMoserGradientEnergy`, or put the interval-domain producer in `P3MoserEnergyContinuity.lean` and import it.

```lean
/-- Window FTC data for the Moser energy.  This is the missing bridge from the
strict-time derivative identity to a closed-window energy difference.

The derivative identity itself is supplied by `IntervalDomainLpTimeLeibniz`; this
predicate asks for the stronger absolute-continuity/FTC consequence. -/
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
```

A strict-window variant is easier and more faithful to current APIs:

```lean
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
```

### Can this be proved now from `IntervalDomainLpTimeLeibniz`?

Not as a one-line wrapper. `IntervalDomainLpTimeLeibniz` gives `HasDerivAt`/`deriv` equalities on strict times. To prove `IntegratedMoserEnergyWindowFTCStrict`, Codex still needs to package one of the following:

```lean
-- either a standard FTC theorem application:
∀ p hp a b, a ≤ b → 0 < a → b < T →
  IntervalIntegrable (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s)
    volume a b ∧
  (∀ s ∈ Set.Icc a b,
    HasDerivAt (fun τ => integratedMoserEnergy intervalDomain u p τ)
      (deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s) s)
```

or a stronger absolute-continuity statement for `Y_p`. The derivative equality is present; the window FTC/absolute-continuity package is not.

So: `intervalDomain_lp_energy_hLpTime_frontier` is already proved; `IntegratedMoserEnergyWindowFTCStrict` remains the next producer-side theorem/frontier.

## Minimal theorem layer 2: pure strict-window integration of `LpBootstrapEnergyInequality`

Once `IntegratedMoserEnergyWindowFTCStrict` is available, the following theorem is pure algebra/integration and should live in `P3MoserIntegratedClosure.lean`.

```lean
/-- Strict-window integration of `LpBootstrapEnergyInequality` into the
higher-power integrated input shape.

This theorem does not prove the FTC; it consumes `hFTC`.  It also does not prove
coefficient surplus for a fixed `theta`; it exposes the produced coefficients. -/
theorem integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_strict
    {T rho p0 p a b : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hp : p0 ≤ p) (hp_pos : 0 < p)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < T)
    (hFTC :
      ∫ s in a..b,
          deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s =
        integratedMoserEnergy intervalDomain u p b -
          integratedMoserEnergy intervalDomain u p a)
    (hDeriv_int :
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s)
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy intervalDomain u p s)
        volume a b)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy intervalDomain u p s)
        volume a b)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy intervalDomain u (p + rho) s)
        volume a b)
    (hY_nonneg :
      ∀ s ∈ Set.Icc a b, 0 ≤ integratedMoserEnergy intervalDomain u p s) :
    ∃ Awin Kwin C0 Lwin : ℝ,
      0 < Awin ∧ 0 ≤ Kwin ∧ 0 ≤ C0 ∧ 0 ≤ Lwin ∧
      integratedMoserEnergy intervalDomain u p b -
          integratedMoserEnergy intervalDomain u p a +
        Awin * ∫ s in a..b, integratedMoserGradientEnergy intervalDomain u p s ≤
        C0 * p *
            (∫ s in a..b,
              max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s)) +
          Kwin *
            (∫ s in a..b, integratedMoserEnergy intervalDomain u (p + rho) s) +
          Lwin *
            (∫ s in a..b,
              max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s))
```

### Constants

Unwrap the pointwise energy inequality:

```lean
rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hpoint⟩
```

Use

```lean
Awin := p * A
Kwin := p * K
C0 := 0
Lwin := max 0 (p * L_const)
```

Then:

* `0 < Awin` follows from `hp_pos` and `hA`;
* `0 ≤ Kwin` follows from `hp_pos.le` and `hK.le`;
* `0 ≤ C0` is trivial;
* `0 ≤ Lwin` is `le_max_left`.

### Proof sketch

1. For `s ∈ Icc a b`, strictness follows from `ha` and `hb`:
   ```lean
   have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
   have hsT : s < T := lt_of_le_of_lt hs.2 hb
   ```
2. Use `hpoint s hs0 hsT` and multiply by `p > 0` to get the pointwise inequality
   ```lean
   deriv Y s + (p*A) * G s + (p*B) * Y s ≤ (p*K) * Z s + p*L_const
   ```
3. Integrate this pointwise inequality over `a..b` using `intervalIntegral.integral_mono_on`.  Required interval-integrability hypotheses are exactly `hDeriv_int`, `hG_int`, `hY_int`, `hZ_int`, plus constants.
4. Rewrite
   ```lean
   ∫ deriv Y = Y b - Y a
   ```
   with `hFTC`.
5. Drop `(p*B) * ∫Y` from the left using `hY_nonneg`, `hY_int`, `hab`, and `hB`.
6. Bound the constant term by the max-one integral:
   ```lean
   (b - a) ≤ ∫ s in a..b, max 1 (Y s)
   ```
   from `intervalIntegral.integral_mono_on hab intervalIntegrable_const hYmax_int` and the pointwise inequality `1 ≤ max 1 (Y s)`.  The file already has `intervalIntegrable_max_one_of_intervalIntegrable`, so `hYmax_int` follows from `hY_int`.
7. `p*L_const*(b-a) ≤ Lwin * ∫max` follows by cases on the sign of `p*L_const`, using `Lwin = max 0 (p*L_const)`.

This theorem is a good Codex target after `IntegratedMoserEnergyWindowFTCStrict` exists. It does not touch high-excursion producers.

## Minimal theorem layer 3: closed-window version

The closed-window version needs endpoint/a.e. transport, because `henergy` only applies at strict times. The clean closed-window theorem should not use `intervalIntegral.integral_mono_on` directly with a pointwise proof on `Set.Icc t1 t2`; it should use an a.e. monotonicity helper.

First add a local measure-theory helper if Mathlib does not expose a convenient name:

```lean
/-- A.e. version of interval-integral monotonicity over a non-reversed interval. -/
theorem intervalIntegral_integral_mono_on_ae
    {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hle : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), f s ≤ g s) :
    ∫ s in a..b, f s ≤ ∫ s in a..b, g s := by
  -- unfold interval integrals to `volume.restrict (Set.Ioc a b)` via
  -- `intervalIntegrable_iff_integrableOn_Ioc_of_le hab` and
  -- `intervalIntegral.integral_of_le`, then use integral monotonicity for
  -- a.e. ordered integrable functions.
  ...
```

Then add the endpoint-a.e. strictness lemma:

```lean
/-- On any closed window inside `[0,T]`, almost every point of the interval
integral lies in the strict interior `(0,T)`. -/
theorem ae_strictInterior_of_closed_window
    {T t1 t2 : ℝ}
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) T)
    (ht2 : t2 ∈ Set.Icc t1 T) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)), 0 < s ∧ s < T := by
  -- From `s ∈ Ioc t1 t2`, get `t1 < s`; with `0 ≤ t1`, get `0 < s`.
  -- For `s < T`, use `s ≤ t2 ≤ T` and discard the possible singleton `s = T`.
  -- The only failure is at `T`, a volume-null singleton.
  ...
```

Now the closed theorem has the same shape as the strict theorem, but consumes a closed-window FTC frontier:

```lean
theorem integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_closed
    {T rho p0 p t1 t2 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hp : p0 ≤ p) (hp_pos : 0 < p)
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) T)
    (ht2 : t2 ∈ Set.Icc t1 T)
    (hFTC :
      ∫ s in t1..t2,
          deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s =
        integratedMoserEnergy intervalDomain u p t2 -
          integratedMoserEnergy intervalDomain u p t1)
    (hDeriv_int :
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s)
        volume t1 t2)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy intervalDomain u p s)
        volume t1 t2)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy intervalDomain u p s)
        volume t1 t2)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy intervalDomain u (p + rho) s)
        volume t1 t2)
    (hY_nonneg_ae :
      ∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)),
        0 ≤ integratedMoserEnergy intervalDomain u p s) :
    ∃ Awin Kwin C0 Lwin : ℝ,
      0 < Awin ∧ 0 ≤ Kwin ∧ 0 ≤ C0 ∧ 0 ≤ Lwin ∧
      integratedMoserEnergy intervalDomain u p t2 -
          integratedMoserEnergy intervalDomain u p t1 +
        Awin * ∫ s in t1..t2,
          integratedMoserGradientEnergy intervalDomain u p s ≤
        C0 * p *
            (∫ s in t1..t2,
              max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s)) +
          Kwin *
            (∫ s in t1..t2,
              integratedMoserEnergy intervalDomain u (p + rho) s) +
          Lwin *
            (∫ s in t1..t2,
              max (1 : ℝ) (integratedMoserEnergy intervalDomain u p s))
```

This is the theorem shape needed to feed a closed-window wrapper.

### What remains frontier in the closed theorem?

The closed theorem still needs `hFTC`. Current `IntervalDomainLpTimeLeibniz` gives strict-time derivative identities, but not closed-window absolute continuity. The endpoint/a.e. strictness and a.e. monotonicity are pure measure-theory wrappers and should be provable; the general-p FTC/AC package remains the real producer-side frontier.

## Surplus exposure for `K * eps ≤ A - theta`

The pointwise-to-window theorem above exposes `Awin` and `Kwin`, but it cannot prove the surplus for fixed `theta`.

The right separate predicate is:

```lean
/-- Coefficient surplus needed to use a relative-Moser epsilon in the integrated
absorption theorem. -/
def IntegratedHigherPowerEnergySurplus
    (theta : ℝ) (T rho p0 : ℝ)
    (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ∃ Awin Kwin : ℝ,
      0 < Awin ∧ 0 ≤ Kwin ∧
      theta < Awin ∧
      -- optional: identify these with the constants chosen by the window energy
      -- theorem, or bundle them in the same structure.
      True
```

Better, avoid matching independent existential witnesses by bundling constants and the window inequality together:

```lean
structure IntegratedHigherPowerEnergyWindowInput
    (theta : ℝ) (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  input : ∀ p, p0 ≤ p →
    ∃ Awin Kwin C0 Lwin : ℝ,
      0 < Awin ∧ 0 ≤ Kwin ∧ 0 ≤ C0 ∧ 0 ≤ Lwin ∧
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

If `theta < Awin`, the wrapper can choose

```lean
eps := (Awin - theta) / (2 * (Kwin + 1))
```

and prove `Kwin * eps ≤ Awin - theta` from `0 ≤ Kwin`. This is the same scalar surplus logic as Q2839.

### Can the surplus be proved from `intervalDomain_LpBootstrapEnergyInequality_of_regularity`?

Not from the public type alone. `LpBootstrapEnergyInequality` only gives some `A > 0`; it does not guarantee `theta < A`, and for the fixed current target `theta = 2`, `A > 0` is insufficient. If the particular interval-domain construction has a larger explicit `Awin`, that requires a stronger theorem exposing the constructed constants, not merely the abstract `LpBootstrapEnergyInequality` existential.

## Recommended implementation order

1. **Pure helper** in `P3MoserIntegratedClosure.lean`:
   ```lean
   intervalIntegral_length_le_integral_max_one
   ```
   from `hY_int` using `max ≥ 1`.

2. **FTC frontier**:
   ```lean
   IntegratedMoserEnergyWindowFTCStrict
   IntegratedMoserEnergyWindowFTC
   ```
   The strict version is the immediate target. The closed version needs endpoint compatibility.

3. **Strict pointwise-to-window theorem**:
   ```lean
   integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_strict
   ```
   This is pure once the strict FTC data is supplied.

4. **Closed-window endpoint/a.e. bridge**:
   ```lean
   intervalIntegral_integral_mono_on_ae
   ae_strictInterior_of_closed_window
   integratedHigherPowerEnergyWindow_of_LpBootstrapEnergyInequality_closed
   ```

5. **Surplus-aware bundled input** for the local wrapper:
   ```lean
   IntegratedHigherPowerEnergyWindowInput
   ```
   Bundle constants with the window inequality so the later absorption wrapper does not have to match unrelated existential choices.

## Classification

| Piece | Status from current repo APIs |
|---|---|
| Pointwise derivative identity for `Y_p` on `0<t<T` | Already proved: `intervalDomain_lp_energy_hLpTime_frontier`. |
| Pointwise `LpBootstrapEnergyInequality` from regularity | Already proved: `intervalDomain_LpBootstrapEnergyInequality_of_regularity`. |
| Interior energy continuity | Already proved: `intervalDomain_energyContinuousOn_Ioo`. |
| Closed energy continuity | Proved only with endpoint residual: `IntervalDomainPowerEnergyEndpointContinuity`. |
| General-p FTC/absolute continuity for `Y_p` on windows | Not currently packaged; real next producer-side frontier. |
| Strict-window integration of pointwise inequality after FTC | Pure wrapper; should be provable now once FTC data is an input. |
| Closed-window integration from strict pointwise inequality | Needs pure a.e./endpoint integration bridge plus FTC. |
| Surplus `K*eps ≤ A-theta` for fixed `theta` | Not implied by `LpBootstrapEnergyInequality`; must be an exposed coefficient/surplus assumption or use a coefficient-parameterized predicate. |

## Bottom line

The minimal next theorem is **not** another PDE estimate. It is a window FTC/absolute-continuity producer for `Y_p`, using the strict-time derivative identity already proved in `IntervalDomainLpTimeLeibniz`. Once that is available, Codex can add a pure `P3MoserIntegratedClosure` theorem integrating `LpBootstrapEnergyInequality` over strict windows. The closed-window version additionally needs an a.e. endpoint bridge. The fixed-coefficient absorption wrapper still needs surplus exposed explicitly; it cannot be recovered from the abstract pointwise energy inequality alone.
