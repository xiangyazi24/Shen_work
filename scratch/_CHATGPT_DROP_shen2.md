# Q2839 shen2: scalar absorption frontier for integrated Moser dissipation

Repo target: `xiangyazi24/Shen_work`, default branch `main`.

Files inspected directly:

```text
ShenWork/PDE/P3MoserDissipationShape.lean
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean
ShenWork/Paper2/IntervalDomainMoserClosure.lean
```

Scope honored: no suggested edits to Zinan-owned files:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

## Executive answer

A scalar/abstract absorption theorem **is provable**, but only if the already-integrated inequality has enough gradient coefficient left after absorbing the higher-power term. The fixed target

```lean
Y_p(t₂) - Y_p(t₁) + 2 * ∫ G_p ≤ C * p * ∫ max 1 Y_p
```

cannot be obtained from an arbitrary positive gradient coefficient. If the integrated PDE inequality has coefficient `A` in front of `∫G`, and the relative interpolation absorption costs `K * eps * ∫G`, then the fixed `2 * ∫G` target requires

```lean
2 ≤ A - K * eps
```

for the chosen `eps > 0`. Thus a theorem targeting the existing

```lean
IntegratedMoserDissipationDropBefore
```

should require either `2 < A` with a suitable `eps`, or more directly a coefficient-surplus hypothesis such as `K * eps ≤ A - 2`.

If the PDE front can only produce `A > 0`, then the current fixed-coefficient predicate is too rigid. The clean repair is to add a coefficient-parameterized predicate and later specialize to coefficient `2` only when a surplus is available.

## Current relevant APIs

### Existing fixed-coefficient target

In `P3MoserDissipationShape.lean`:

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

`integratedMoserDissipationDropBefore_of_integrated_energy` is just the packaging theorem for exactly this shape.

### Existing integrated relative-Moser support

In `P3MoserIntegratedClosure.lean`:

```lean
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
```

proves an integrated estimate of the form

```lean
∫ Z ≤ eps * ∫ G + (b - a) * (Ceps * M)
```

under a uniform pointwise current-exponent bound `Y_p(s) ≤ M` on the window. This is useful for the first-crossing step, but for the `IntegratedMoserDissipationDropBefore` shape it is more natural to avoid the pointwise `M` and keep the output as

```lean
∫ Z ≤ eps * ∫ G + Ceps * ∫ Y
```

then use `∫Y ≤ ∫ max 1 Y`.

### Existing energy inequality is pointwise, not integrated

In `IntervalDomainLpBootstrapEnergyInequality.lean`,

```lean
intervalDomain_LpBootstrapEnergyInequality_of_regularity
```

produces the pointwise `LpBootstrapEnergyInequality` shape. It already has a positive Moser-gradient coefficient `Acoef`, but this file does not integrate the inequality over a time window and does not produce the fixed integrated Moser shape directly.

## Recommended new predicate: coefficient-parameterized integrated drop

Add this in `ShenWork/PDE/P3MoserDissipationShape.lean`, immediately after `IntegratedMoserDissipationDropBefore`.

```lean
/-- Coefficient-parameterized integrated Moser energy-drop shape.

This is the flexible version of `IntegratedMoserDissipationDropBefore`.  The
fixed predicate is the special case `theta = 2`.  It is needed because scalar
absorption of a higher-power term generally leaves a coefficient
`A - K * eps`, not definitionally `2`. -/
def IntegratedMoserDissipationDropBeforeCoeff
    (theta : ℝ) (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        theta * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))

/-- The coefficient-parametric integrated drop specializes to the current fixed
coefficient predicate at `theta = 2`. -/
theorem integratedMoserDissipationDropBefore_of_coeff_two
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (h : IntegratedMoserDissipationDropBeforeCoeff 2 D u T rho p0) :
    IntegratedMoserDissipationDropBefore D u T rho p0 := by
  intro p hp
  exact h p hp
```

A further monotonicity projection is also useful, but only with a nonnegativity input for the gradient time integral, because `BoundedDomainData.integral` is abstract:

```lean
theorem integratedMoserDissipationDropBefore_of_coeff_ge_two
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 theta : ℝ}
    (htheta : 2 ≤ theta)
    (hG_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
    (h : IntegratedMoserDissipationDropBeforeCoeff theta D u T rho p0) :
    IntegratedMoserDissipationDropBefore D u T rho p0 := by
  intro p hp
  rcases h p hp with ⟨C, hC, hineq⟩
  refine ⟨C, hC, ?_⟩
  intro t1 ht1 t2 ht2
  have hG := hG_nonneg p hp t1 ht1 t2 ht2
  have hthetaG :
      2 * (∫ s in t1..t2,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤
      theta * (∫ s in t1..t2,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) :=
    mul_le_mul_of_nonneg_right htheta hG
  have hmain := hineq t1 ht1 t2 ht2
  linarith
```

This is small and useful even if the fixed predicate is retained as the public API.

## Recommended integrated relative lemma without a pointwise `M`

Add this in `ShenWork/PDE/P3MoserIntegratedClosure.lean`, near the existing `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound`.

```lean
/-- Integrate the relative Moser interpolation inequality over a fixed time
window, keeping the lower-order term as the time integral of the current energy.

This is the right form for absorbing a higher-power time integral into an
already-integrated energy inequality. -/
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_integral
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b eps : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
        volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
        volume a b)
    (hY_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ p))
        volume a b) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * (∫ s in a..b,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) +
        Ceps * (∫ s in a..b,
          D.integral (fun x => (u s x) ^ p))
```

Proof sketch: same as `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound`, but integrate the pointwise right side

```lean
fun s => eps * G s + Ceps * Y s
```

rather than bounding `Y s` by a constant `M`. The final algebra uses

```lean
intervalIntegral.integral_add
intervalIntegral.integral_const_mul
```

No new analysis is involved; this is a pure integration wrapper around `RelativeMoserInterpolationBefore`.

Then add a small wrapper to replace `∫Y` by `∫ max 1 Y` when the abstract integral/interval API can prove it, or keep it as an explicit hypothesis in the absorption theorem. For abstract `BoundedDomainData`, I recommend keeping the `∫Y ≤ ∫max` comparison as an explicit scalar/window hypothesis unless the code is specialized to `intervalDomain`.

## Core scalar absorption theorem

This is the smallest genuinely provable scalar lemma. It should live in `P3MoserIntegratedClosure.lean`, because it combines the integrated inequality with the relative/interpolation time-integral shape.

```lean
/-- Scalar absorption for one time window.

Interpretation:
* `Ydiff` is `Y_p(t₂) - Y_p(t₁)`;
* `Gint` is `∫ G_p`;
* `Zint` is `∫ Z_{p+rho}`;
* `Hint` is `∫ max 1 Y_p`.

If the already-integrated inequality contains `A * Gint` and `K * Zint`, and
relative interpolation gives `Zint ≤ eps * Gint + Ceps * Hint`, then any surplus
`K * eps ≤ A - theta` yields the coefficient-`theta` integrated shape. -/
theorem scalar_absorb_higherPower_window
    {Ydiff Gint Zint Hint A K C0 L p eps Ceps theta : ℝ}
    (hp : 0 < p)
    (hG : 0 ≤ Gint)
    (hC0 : 0 ≤ C0)
    (hK : 0 ≤ K)
    (hL : 0 ≤ L)
    (hCeps : 0 ≤ Ceps)
    (henergy :
      Ydiff + A * Gint ≤ C0 * p * Hint + K * Zint + L * Hint)
    (hrel : Zint ≤ eps * Gint + Ceps * Hint)
    (habsorb : K * eps ≤ A - theta) :
    ∃ Cfinal, 0 ≤ Cfinal ∧
      Ydiff + theta * Gint ≤ Cfinal * p * Hint
```

Use

```lean
Cfinal = C0 + (K * Ceps + L) / p
```

Proof sketch:

1. Multiply `hrel` by `K ≥ 0`:
   ```lean
   K * Zint ≤ K * (eps * Gint + Ceps * Hint)
   ```
2. Combine with `henergy`:
   ```lean
   Ydiff + A * Gint ≤ C0*p*Hint + K*eps*Gint + (K*Ceps + L)*Hint
   ```
3. Move the absorbed gradient cost to the left:
   ```lean
   Ydiff + (A - K*eps) * Gint ≤ C0*p*Hint + (K*Ceps + L)*Hint
   ```
4. Since `theta ≤ A - K*eps` and `0 ≤ Gint`, weaken the left side to
   ```lean
   Ydiff + theta * Gint
   ```
5. Rewrite
   ```lean
   C0*p*Hint + (K*Ceps + L)*Hint
     = (C0 + (K*Ceps + L)/p) * p * Hint
   ```
   using `0 < p`.
6. Nonnegativity of `Cfinal` follows from `hC0`, `hK`, `hCeps`, `hL`, and `hp`.

This theorem is completely scalar; proof should be `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`, `field_simp [ne_of_gt hp]`, and `nlinarith`/`linarith` after ring normalization.

## Window-level absorption to the coefficient-parameterized predicate

A useful next wrapper is the following. It assumes the time-window higher-power estimate and the already-integrated relative estimate in the exact form needed by the scalar lemma.

```lean
/-- Convert an already-integrated higher-power inequality plus an integrated
relative-Moser bound into the coefficient-parameterized integrated dissipation
shape. -/
theorem integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 theta : ℝ}
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (henergy :
      ∀ p, p0 ≤ p →
        ∃ A K C0 L, 0 ≤ K ∧ 0 ≤ C0 ∧ 0 ≤ L ∧
          (∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            let Ydiff :=
              D.integral (fun x => (u t2 x) ^ p) -
                D.integral (fun x => (u t1 x) ^ p)
            let Gint :=
              ∫ s in t1..t2,
                D.integral (fun x =>
                  (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)
            let Zint :=
              ∫ s in t1..t2,
                D.integral (fun x => (u s x) ^ (p + rho))
            let Hint :=
              ∫ s in t1..t2,
                max 1 (D.integral (fun x => (u s x) ^ p))
            Ydiff + A * Gint ≤ C0 * p * Hint + K * Zint + L * Hint) ∧
          (∀ eps, 0 < eps → K * eps ≤ A - theta))
    (hrelInt :
      ∀ p, p0 ≤ p → ∀ eps, 0 < eps →
        ∃ Ceps, 0 ≤ Ceps ∧
          ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
            let Zint :=
              ∫ s in t1..t2,
                D.integral (fun x => (u s x) ^ (p + rho))
            let Gint :=
              ∫ s in t1..t2,
                D.integral (fun x =>
                  (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)
            let Hint :=
              ∫ s in t1..t2,
                max 1 (D.integral (fun x => (u s x) ^ p))
            Zint ≤ eps * Gint + Ceps * Hint)
    (hG_nonneg :
      ∀ p, p0 ≤ p → ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        0 ≤ ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) :
    IntegratedMoserDissipationDropBeforeCoeff theta D u T rho p0
```

For the fixed current predicate, instantiate `theta = 2`:

```lean
theorem integratedMoserDissipationDropBefore_of_higherPower_and_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (hp_pos : ∀ p, p0 ≤ p → 0 < p)
    (henergy : ... same as above with `theta := 2` surplus ...)
    (hrelInt : ...)
    (hG_nonneg : ...) :
    IntegratedMoserDissipationDropBefore D u T rho p0 :=
  integratedMoserDissipationDropBefore_of_coeff_two
    (integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
      (theta := 2) hp_pos henergy hrelInt hG_nonneg)
```

### More ergonomic surplus assumption

The `∀ eps, K * eps ≤ A - theta` field above is too strong if read literally, but it is convenient for a pure wrapper. A more practical version is:

```lean
2 < A
```

when targeting `theta = 2`. Then choose

```lean
eps := (A - 2) / (2 * (K + 1))
```

This works for all `K ≥ 0`, including `K = 0`, and gives

```lean
0 < eps
K * eps ≤ (A - 2) / 2 ≤ A - 2
```

So the more natural fixed-coefficient theorem should phrase the energy package as:

```lean
∃ A K C0 L, 2 < A ∧ 0 ≤ K ∧ 0 ≤ C0 ∧ 0 ≤ L ∧ higherPowerIneq
```

and internally choose `eps` as above before calling the scalar lemma.

## Why fixed coefficient `2` can be impossible

If the integrated PDE estimate only gives

```lean
Ydiff + A * Gint ≤ RHS
```

with `A ≤ 2`, there is no scalar way to conclude

```lean
Ydiff + 2 * Gint ≤ RHS'
```

with the same `Ydiff` and no additional information. For example, take `Gint = 1`, `Ydiff = -A`, `Zint = 0`, and `Hint = 0`. Then the premise can hold with right side `0`, but the fixed target requires

```lean
-A + 2 ≤ 0
```

which fails when `A < 2`. Even `A = 2` leaves no room to absorb a positive `K * eps * Gint` cost from the relative interpolation unless `K = 0` or a different argument removes the higher-power term.

Therefore the fixed coefficient is safe only if the already-integrated inequality has surplus, e.g.

```lean
2 < A
```

or if the predicate is parameterized by the actual leftover coefficient.

## Where the declarations should live

### `P3MoserDissipationShape.lean`

Put predicate-shape declarations here:

```lean
IntegratedMoserDissipationDropBeforeCoeff
integratedMoserDissipationDropBefore_of_coeff_two
integratedMoserDissipationDropBefore_of_coeff_ge_two
```

This file already owns the diagnostic distinction between false pointwise drop and faithful integrated drop.

### `P3MoserIntegratedClosure.lean`

Put time-window/integration and absorption wrappers here:

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentEnergy_integral
scalar_absorb_higherPower_window
integratedMoserDissipationDropBeforeCoeff_of_higherPower_and_relative
integratedMoserDissipationDropBefore_of_higherPower_and_relative
```

This file already contains `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds` and the integrated relative-Moser lemmas, so the new absorption wrapper belongs naturally there.

## Bottom line

The next smallest provable sub-frontier is not the PDE proof of `IntegratedMoserDissipationDropBefore`; it is the scalar/integrated absorption layer:

1. add a coefficient-parameterized integrated drop predicate;
2. add an integrated relative-Moser lemma with `∫Y` rather than a pointwise `M`;
3. add a scalar absorption theorem;
4. add a wrapper that targets the current fixed coefficient `2` only under `2 < A` surplus.

This cleanly separates the remaining PDE frontier from the provable algebraic absorption layer and avoids strengthening the false pointwise-drop path.
