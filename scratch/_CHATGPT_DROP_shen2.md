# Q2862 shen2: minimal closed-window bridge to `IntegratedHigherPowerEnergyWindowCoeffFrontier`

Repo target: `xiangyazi24/Shen_work`, Lean 4.

Files inspected on `main` through the GitHub connector:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/PDE/P3MoserDissipationShape.lean
ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean
ShenWork/Paper2/IntervalDomainEnergyStep.lean
ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean
```

Note: the connector-visible `main` file does not yet contain the local declarations named in the prompt (`IntegratedMoserEnergyWindowFTC`, `IntegratedHigherPowerEnergyWindowCoeffFrontier`, `intervalIntegral_length_le_integral_max_one`, `integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative`). I treat those as current local compiled context and ground the proposal in the visible upstream APIs that must feed them.

## Verdict

The smallest honest next theorem is a **closed-window integration wrapper** that consumes:

1. `henergy : LpBootstrapEnergyInequality D u T rho p0`;
2. the already-local `hFTC : IntegratedMoserEnergyWindowFTC D u T p0` for the energy difference;
3. explicit closed-window interval-integrability of `G_p`, `Y_p`, `Y_(p+rho)`, and `max 1 Y_p`;
4. an explicit nonnegativity hypothesis for `∫Y_p` on the window, used to drop the positive `B∫Y_p` term from the left;
5. a pure endpoint/a.e. bridge for applying the strict-time pointwise inequality on closed windows; and
6. coefficient-surplus handling either as a caller-side premise `K * eps ≤ A - theta` or, if the local frontier stores an actual chosen epsilon, as an explicit `theta < A`/epsilon chooser assumption.

Do **not** claim FTC follows from continuity. Current `IntervalDomainLpTimeLeibniz` provides strict-time derivative identities, and `P3MoserEnergyContinuity` provides continuity support, but the closed-window FTC/AC package is a separate input here.

## Existing source theorem shape

`LpBootstrapEnergyInequality` is the right source. It is consumed throughout `IntervalDomainEnergyStep.lean`; unwrapping gives, for each `p ≥ p0`, witnesses

```lean
A, B, K, L_const : ℝ
hA : 0 < A
hB : 0 < B
hK : 0 < K
hfull : ∀ t, 0 < t → t < T →
  (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
    A * D.integral (fun x =>
      (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
    B * D.integral (fun x => (u t x) ^ p) ≤
  K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const
```

For the coefficient-frontier target, multiply this inequality by `p > 0` and set

```lean
Awin := p * A
Kwin := p * K
C0   := 0
Lwin := max 0 (p * L_const)
```

The raw window inequality then follows after integrating, using FTC, dropping `p*B*∫Y`, and bounding the constant term by `Lwin * ∫max(1,Y)`.

## Pure endpoint/a.e. helper needed for closed windows

Because `hfull` is strict-time only, a closed-window theorem must not use `intervalIntegral.integral_mono_on` with a pointwise proof over all of `Set.Icc t1 t2`. It needs an a.e. monotonicity helper. If not already local, add this near the other interval-integral helper lemmas in `P3MoserIntegratedClosure.lean`.

```lean
/-- A.e. interval-integral monotonicity on a non-reversed interval.  This is the
endpoint bridge needed when the pointwise estimate is only known away from
closed-window endpoints. -/
theorem intervalIntegral_integral_mono_on_ae
    {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hle : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), f s ≤ g s) :
    ∫ s in a..b, f s ≤ ∫ s in a..b, g s
```

Proof plan: rewrite interval integrals over `a..b` using the `Ioc` representation for `a ≤ b`, obtain integrability on `volume.restrict (Set.Ioc a b)` from the `IntervalIntegrable` hypotheses, and apply the Lebesgue integral monotonicity theorem for a.e.-ordered integrable functions. This is pure measure theory, not PDE.

Also add or reuse:

```lean
/-- On a closed window inside `[0,T]`, almost every interval-integration point is
strictly inside `(0,T)`. -/
theorem ae_strictInterior_of_closed_window
    {T t1 t2 : ℝ}
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) T)
    (ht2 : t2 ∈ Set.Icc t1 T) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc t1 t2)), 0 < s ∧ s < T
```

Proof plan: for `s ∈ Ioc t1 t2`, `t1 < s`, so `0 < s` follows from `0 ≤ t1`. For `s < T`, use `s ≤ t2 ≤ T` and discard the possible singleton `s = T`. The singleton is volume-null.

If Codex wants the smallest theorem without proving these two helpers first, make the a.e. pointwise inequality an explicit hypothesis. That is less reusable but entirely honest.

## Minimal theorem statement: helper-consuming version

Assuming the local `IntegratedHigherPowerEnergyWindowCoeffFrontier` has the natural shape “for each `p ≥ p0`, produce coefficients and, for every `eps` with `K*eps ≤ A-theta`, give the closed-window raw inequality”, the smallest bridge should be:

```lean
/-- Closed-window integrated higher-power energy frontier from the strict-time
`LpBootstrapEnergyInequality`, assuming the separate window FTC and time
integrability data.

This is an honest wrapper: it does not derive FTC from continuity and it does not
hide endpoint/a.e. transport. -/
theorem integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    (hFTC : IntegratedMoserEnergyWindowFTC D u T p0)
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (hG_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserGradientEnergy D u p s) volume t1 t2)
    (hY_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserEnergy D u p s) volume t1 t2)
    (hZ_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => integratedMoserEnergy D u (p + rho) s) volume t1 t2)
    (hMax_int :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        IntervalIntegrable
          (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
          volume t1 t2)
    (hY_integral_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2, integratedMoserEnergy D u p s) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier theta D u T rho p0
```

The proof should not take an independent surplus hypothesis if the frontier’s method is of the form:

```lean
∀ eps, 0 < eps → Kwin * eps ≤ Awin - theta → window_ineq
```

In that case the theorem simply introduces `eps heps hsurplus` and proves `window_ineq`; it does not need to prove `hsurplus`. If your local definition instead stores an actual selected epsilon with a proof of surplus, add a separate hypothesis:

```lean
(hsurplus_exists :
  ∀ p, p0 ≤ p →
    -- after unwrapping `henergy p hp` and choosing `A,K`,
    -- there exists `eps > 0` such that `(p*K)*eps ≤ (p*A) - theta`)
```

or better require a visible coefficient gap after unwrapping:

```lean
htheta_gap : theta < p * A
```

and choose `eps := (p*A - theta) / (2 * (p*K + 1))`.

## More compile-oriented per-window lemma

If matching the global frontier is awkward due to existential choices, first add a per-window theorem. This is easier to compile and then the frontier theorem can just iterate over `p,t1,t2`.

```lean
/-- Per-window version: integrate one exponent's pointwise
`LpBootstrapEnergyInequality` witnesses over one closed window. -/
theorem integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p theta A B K L_const t1 t2 : ℝ}
    (hp : p0 ≤ p) (hp_pos : 0 < p)
    (hA : 0 < A) (hB : 0 < B) (hK : 0 < K)
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) T)
    (ht2 : t2 ∈ Set.Icc t1 T)
    (hfull : ∀ t, 0 < t → t < T →
      (1 / p) * deriv (fun τ => integratedMoserEnergy D u p τ) t +
        A * integratedMoserGradientEnergy D u p t +
        B * integratedMoserEnergy D u p t ≤
      K * integratedMoserEnergy D u (p + rho) t + L_const)
    (hFTC :
      (∫ s in t1..t2,
          deriv (fun τ => integratedMoserEnergy D u p τ) s) =
        integratedMoserEnergy D u p t2 -
          integratedMoserEnergy D u p t1)
    (hDeriv_int :
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u p τ) s)
        volume t1 t2)
    (hG_int :
      IntervalIntegrable
        (fun s => integratedMoserGradientEnergy D u p s) volume t1 t2)
    (hY_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u p s) volume t1 t2)
    (hZ_int :
      IntervalIntegrable
        (fun s => integratedMoserEnergy D u (p + rho) s) volume t1 t2)
    (hMax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s)) volume t1 t2)
    (hY_integral_nonneg :
      0 ≤ ∫ s in t1..t2, integratedMoserEnergy D u p s) :
    let Awin : ℝ := p * A
    let Kwin : ℝ := p * K
    let C0 : ℝ := 0
    let Lwin : ℝ := max 0 (p * L_const)
    0 < Awin ∧ 0 ≤ Kwin ∧ 0 ≤ C0 ∧ 0 ≤ Lwin ∧
      (∀ eps, 0 < eps → Kwin * eps ≤ Awin - theta →
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

This theorem is often the best first Codex patch. It keeps the `LpBootstrapEnergyInequality` existential-unwrapping outside the statement and therefore avoids fighting structure-field elaboration.

## Proof plan for the per-window lemma

1. Define
   ```lean
   Y s := integratedMoserEnergy D u p s
   G s := integratedMoserGradientEnergy D u p s
   Z s := integratedMoserEnergy D u (p + rho) s
   dY s := deriv (fun τ => integratedMoserEnergy D u p τ) s
   ```

2. Build an a.e. strict-interior pointwise inequality on `volume.restrict (Set.Ioc t1 t2)`:
   ```lean
   ∀ᵐ s, dY s + (p*A)*G s + (p*B)*Y s ≤ (p*K)*Z s + p*L_const
   ```
   using `ae_strictInterior_of_closed_window ht1 ht2`, `hfull`, and multiplication by `p > 0`.

3. Integrate that a.e. inequality with `intervalIntegral_integral_mono_on_ae`. Required integrability comes from `hDeriv_int`, `hG_int`, `hY_int`, `hZ_int`, and constants.

4. Rewrite the left by linearity of interval integrals:
   ```lean
   ∫ dY + (p*A) * ∫G + (p*B) * ∫Y
   ```
   and rewrite `∫dY` using `hFTC`.

5. Drop the nonnegative term `(p*B)*∫Y` from the left using:
   ```lean
   mul_nonneg (mul_nonneg hp_pos.le hB.le) hY_integral_nonneg
   ```

6. Bound the constant term:
   * use the local theorem `intervalIntegral_length_le_integral_max_one` to get
     ```lean
     t2 - t1 ≤ ∫ s in t1..t2, max 1 (Y s)
     ```
   * with `Lwin := max 0 (p*L_const)`, prove
     ```lean
     p * L_const * (t2 - t1) ≤ Lwin * ∫max
     ```
     by cases on `p*L_const ≤ 0` or simply via `le_max_right` plus nonnegativity of `∫max`.

7. The `eps` and surplus hypotheses are introduced but unused in the raw window inequality. They are present only to match the coefficient-frontier consumer.

## How to derive the theorem from `LpBootstrapEnergyInequality`

Once the per-window lemma compiles, the global frontier wrapper is short:

```lean
rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hfull⟩
apply integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
  (hp := hp) (hp_pos := hp_pos p hp)
  (hA := hA) (hB := hB) (hK := hK)
  (ht1 := ht1) (ht2 := ht2)
  -- hfull must be rewritten/simpa'd to `integratedMoserEnergy` and
  -- `integratedMoserGradientEnergy`.
```

For generic `D`, `hfull` already uses exactly `D.integral` and `D.gradNorm`, so `simpa [integratedMoserEnergy, integratedMoserGradientEnergy]` should align it. For `intervalDomain`, this is also direct.

## Nonnegativity and integrability inputs

The theorem should not try to infer every regularity fact from `LpBootstrapEnergyInequality`. Use explicit hypotheses or existing package accessors:

* `hFTC : IntegratedMoserEnergyWindowFTC D u T p0` gives derivative interval integrability and the window FTC identity.
* `hG_int`, `hY_int`, `hZ_int`, `hMax_int` can come from `IntegratedMoserFirstCrossingRegularity`:
  ```lean
  IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
  IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
  IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
  ```
* `hY_integral_nonneg` can be derived for `intervalDomain` from positivity/nonnegativity of `u`, but at the abstract `D` level it should be explicit.
* `intervalIntegral_length_le_integral_max_one` is the right local tool for the constant term.

## Import-cycle placement

Best placement: `ShenWork/PDE/P3MoserIntegratedClosure.lean`, after the local definitions/theorems:

```lean
integratedMoserEnergy
integratedMoserGradientEnergy
IntegratedMoserEnergyWindowFTC
intervalIntegral_length_le_integral_max_one
IntegratedHigherPowerEnergyWindowCoeffFrontier
```

and before:

```lean
integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
```

if that consumer depends on the frontier.

This should not create an import cycle. `P3MoserIntegratedClosure.lean` already imports `P3MoserDissipationShape.lean`, and `P3MoserDissipationShape.lean` imports `IntervalDomainLpBootstrapEnergyInequality.lean`, so `LpBootstrapEnergyInequality` should already be in scope. If Lean cannot see the name, add a direct import:

```lean
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
```

above `import ShenWork.PDE.P3MoserDissipationShape`; this is still acyclic because `IntervalDomainLpBootstrapEnergyInequality` does not import `P3MoserIntegratedClosure`.

Avoid placing this theorem in `IntervalDomainEnergyStep.lean`: that would require importing the integrated-Moser file to see `IntegratedHigherPowerEnergyWindowCoeffFrontier`, likely creating an undesirable Paper2→PDE assembly dependency/cycle. Keep it on the PDE integrated-closure side.

## What not to claim

* Do not claim `IntegratedMoserEnergyWindowFTC` follows from `intervalDomain_energyContinuousOn_Ioo` or closed continuity. It is an FTC/AC statement, stronger than continuity.
* Do not claim `LpBootstrapEnergyInequality` by itself provides a fixed positive surplus for arbitrary `theta`. It only gives `A > 0`, `K > 0`. If the local consumer needs a chosen epsilon satisfying `K*eps ≤ A-theta`, either use the coefficient-parametric frontier or add a separate `theta < Awin`/epsilon-selection assumption.
* Do not use the old pointwise `MoserDissipationDropBefore` route for this bridge. The whole point is to retain the derivative term and integrate the full inequality over windows.

## Short answer

The next smallest honest theorem is the per-window lemma

```lean
integratedHigherPowerEnergyWindowCoeff_of_pointwise_witness
```

followed by the global wrapper

```lean
integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality
```

in `P3MoserIntegratedClosure.lean`. Both consume `IntegratedMoserEnergyWindowFTC` and explicit window integrability/nonnegativity. The endpoint/a.e. helper is the only measure-theory bridge needed for closed windows; the actual FTC remains an explicit assumption and should not be derived from continuity.
