ANSWER Q4321 cceaa80d

# Q4321 — Stampacchia truncation chain rule for 1D weak-energy arguments

## Verdict

I would not plan on a turnkey Mathlib theorem that says exactly:

```lean
u ∈ H¹(0,1) → positivePart u ∈ H¹(0,1) ∧
  weakDeriv (positivePart u) =ᵐ[μ] indicator {x | 0 < u x} * weakDeriv u
```

or the analogous negative-part theorem.

For this project, the best route is a **1D absolutely-continuous representative lemma**, not a full Sobolev-truncation theory. It is a small, local analytic build compared with the rest of the PDE stack. The weak-energy producers only need the a.e. derivative formula and the resulting integral identities, not a general `W^{1,p}` truncation API.

## 1. Mathlib status

I do not know of a Mathlib theorem, under the current usual names, that packages the Stampacchia truncation chain rule for Sobolev spaces. Searches under names such as:

```text
Sobolev truncation
HasWeakDeriv positivePart
weak derivative max
posPart / negPart derivative
Stampacchia
```

do not point to a reusable theorem of the exact needed shape.

What Mathlib does have, and what is worth using, is the lower-level real-analysis infrastructure:

```lean
AbsolutelyContinuousOn
HasDerivAt
deriv
Continuous.max
LipschitzWith
AEStronglyMeasurable
intervalIntegral.integral_eq_sub_of_hasDerivAt
```

plus the usual a.e. and interval-integral tools. So the feasible plan is to prove a 1D lemma for absolutely continuous representatives and use that as the local replacement for a Sobolev truncation theorem.

## 2. 1D absolutely-continuous route

In one dimension, use the standard chain:

```text
u ∈ H¹(0,1)
  ⇒ u has an absolutely continuous representative U on [0,1]
  ⇒ U₊ := max U 0 is absolutely continuous
  ⇒ (U₊)' = 1_{U>0} U' a.e.
```

and similarly:

```text
U₋ := max (-U) 0
(U₋)' = -1_{U<0} U' a.e.
```

### Core lemma to build

The most useful local theorem is not stated with `H¹`; state it for an AC representative:

```lean
theorem absolutelyContinuousOn_posPart_deriv_ae
    {u u' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hu_ac : AbsolutelyContinuousOn u (Set.Icc a b))
    (hu_deriv : ∀ᵐ x ∂volume.restrict (Set.Ioo a b),
        HasDerivAt u (u' x) x) :
    AbsolutelyContinuousOn (fun x => max (u x) 0) (Set.Icc a b) ∧
      (∀ᵐ x ∂volume.restrict (Set.Ioo a b),
        HasDerivAt (fun y => max (u y) 0)
          ((if 0 < u x then 1 else 0) * u' x) x) := by
  ...
```

For the negative part:

```lean
theorem absolutelyContinuousOn_negPart_deriv_ae
    {u u' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hu_ac : AbsolutelyContinuousOn u (Set.Icc a b))
    (hu_deriv : ∀ᵐ x ∂volume.restrict (Set.Ioo a b),
        HasDerivAt u (u' x) x) :
    AbsolutelyContinuousOn (fun x => max (-(u x)) 0) (Set.Icc a b) ∧
      (∀ᵐ x ∂volume.restrict (Set.Ioo a b),
        HasDerivAt (fun y => max (-(u y)) 0)
          (-(if u x < 0 then 1 else 0) * u' x) x) := by
  ...
```

The exact indicator can be written using `Set.indicator` later, but the `if` form is easier for Lean rewriting.

### The only subtle point

At points where `u x ≠ 0`, the formula is ordinary chain rule:

```text
max(u,0)' = u'       if u x > 0
max(u,0)' = 0        if u x < 0
max(-u,0)' = -u'     if u x < 0
max(-u,0)' = 0       if u x > 0
```

At points where `u x = 0`, the outer function `max · 0` is not differentiable. The standard fact needed is:

```text
if u is absolutely continuous, then u' = 0 a.e. on the level set {x | u x = c}.
```

For this project, only `c = 0` is needed:

```lean
theorem absolutelyContinuousOn_deriv_eq_zero_ae_on_level_zero
    {u u' : ℝ → ℝ} {a b : ℝ}
    (hu_ac : AbsolutelyContinuousOn u (Set.Icc a b))
    (hu_deriv : ∀ᵐ x ∂volume.restrict (Set.Ioo a b),
        HasDerivAt u (u' x) x) :
    ∀ᵐ x ∂volume.restrict ({x | x ∈ Set.Ioo a b ∧ u x = 0}),
      u' x = 0 := by
  ...
```

With that lemma, the zero-level case is harmless: the desired derivative is `0`, and the difference quotient of the positive/negative part also has derivative `0` a.e. on the zero level.

This level-set derivative-zero lemma is the only genuinely nontrivial analytic sublemma in the 1D route, but it is much smaller than building a Sobolev chain-rule library.

## 3. Minimal statements needed by the weak-energy arguments

The energy proofs do not need a polished theorem saying `u₊ ∈ H¹`. They need the following concrete consequences.

### Negative-part energy

Let:

```lean
uMinus x := max (-(u x)) 0
phi x := -uMinus x
```

The needed a.e. identities are:

```lean
-- negative part derivative
HasDerivAt uMinus (-(if u x < 0 then 1 else 0) * ux x) x

-- test derivative
HasDerivAt phi ((if u x < 0 then 1 else 0) * ux x) x
```

From these, the diffusion pairing becomes:

```text
-ν ∫ u_x * phi_x
  = -ν ∫ 1_{u<0} * u_x^2
  ≤ 0.
```

Lean-friendly statement:

```lean
theorem negPart_diffusion_pairing_nonpos
    {u ux : ℝ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν)
    (hux_sq_int : Integrable (fun x => ux x ^ 2) (intervalMeasure 1))
    (hphi_deriv_ae : ∀ᵐ x ∂intervalMeasure 1,
      deriv (fun y => - max (-(u y)) 0) x =
        (if u x < 0 then 1 else 0) * ux x) :
    -ν * (∫ x, ux x * deriv (fun y => - max (-(u y)) 0) x ∂intervalMeasure 1) ≤ 0 := by
  -- rewrite by hphi_deriv_ae
  -- integrand = indicator {u<0} * ux^2
  -- nonnegative integral, then multiply by -ν
  ...
```

The algebraic identity to expose is:

```lean
ux x * ((if u x < 0 then 1 else 0) * ux x)
  = (if u x < 0 then 1 else 0) * ux x ^ 2
```

### Jensen/barrier comparison

For `z := w - u`, test with:

```lean
zPlus x := max (z x) 0
```

The needed identities are:

```text
(z₊)' = 1_{z>0} z' a.e.
```

and hence, on `{z > 0}`:

```text
z = z₊,
∂x z₊ = ∂x z,
```

which gives the drift estimate:

```text
|∫ z g ∂x z₊| = |∫ z₊ g ∂x z₊|
≤ ‖g‖∞ ‖z₊‖₂ ‖∂x z₊‖₂
≤ (ν/2) ‖∂x z₊‖₂² + C ‖z₊‖₂².
```

Lean-friendly local lemma:

```lean
theorem posPart_drift_pairing_young
    {z zx g : ℝ → ℝ} {ν A : ℝ}
    (hν : 0 < ν)
    (hg : ∀ x, |g x| ≤ A)
    (hA : 0 ≤ A)
    (hzp_deriv_ae : ∀ᵐ x ∂intervalMeasure 1,
      deriv (fun y => max (z y) 0) x =
        (if 0 < z x then 1 else 0) * zx x) :
    |∫ x, z x * g x * deriv (fun y => max (z y) 0) x ∂intervalMeasure 1|
      ≤ (ν / 2) * ∫ x, (deriv (fun y => max (z y) 0) x)^2 ∂intervalMeasure 1
        + (A^2 / (2 * ν)) * ∫ x, (max (z x) 0)^2 ∂intervalMeasure 1 := by
  -- rewrite z * indicator_{z>0} as zPlus
  -- Cauchy-Schwarz + Young
  ...
```

This is the exact content needed for the weak comparison proof. It does not need pointwise `z_xx`, nor a full Sobolev truncation API.

## 4. Suggested build order

Build these small lemmas in a dedicated file, for example:

```text
ShenWork/PDE/IntervalStampacchiaTruncation1D.lean
```

### Layer A: scalar real lemmas

```lean
lemma deriv_max_zero_of_pos {u u' x} ...
lemma deriv_max_zero_of_neg {u u' x} ...
lemma deriv_negPart_of_neg {u u' x} ...
lemma deriv_negPart_of_pos {u u' x} ...
```

These are ordinary `HasDerivAt` chain-rule lemmas under sign hypotheses.

### Layer B: AC level-set lemma

```lean
lemma ac_deriv_zero_ae_on_level
    (hu_ac : AbsolutelyContinuousOn u (Icc a b))
    (hu_deriv : ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt u (u' x) x) :
    ∀ᵐ x ∂volume.restrict ({x | x ∈ Ioo a b ∧ u x = c}), u' x = 0
```

This is the main local analytic lemma.

### Layer C: positive/negative part AC derivative formulas

```lean
lemma posPart_deriv_ae_of_ac ...
lemma negPart_deriv_ae_of_ac ...
```

### Layer D: energy-ready corollaries

Expose exactly the integral identities and inequalities used by the two producers:

```lean
lemma negPart_test_deriv_ae ...
lemma negPart_diffusion_pairing_eq ...
lemma negPart_diffusion_pairing_nonpos ...

lemma posPart_test_deriv_ae ...
lemma posPart_diffusion_pairing_eq ...
lemma posPart_drift_pairing_young ...
```

## 5. Formalization cost estimate

This is a **small 1D build**, not a fundamental PDE infrastructure gap.

The only nontrivial piece is the AC level-set derivative-zero lemma. Everything else is sign case-splitting, composition with `max`, a.e. rewriting, Cauchy-Schwarz/Young, and interval integrability.

Avoid building a general `SobolevSpace`/`HasWeakDeriv` truncation theorem unless you specifically want a reusable Mathlib contribution. For the chemotaxis proof, the AC-representative route is narrower and much more likely to close in Lean.

## Bottom line

The weak-energy arguments need only the 1D Stampacchia consequences:

```text
(u₋)' = -1_{u<0} u' a.e.
(z₊)' =  1_{z>0} z' a.e.
```

and the resulting diffusion/drift energy estimates. These can be built from absolutely continuous representatives. Do not block the PDE proof on a full Sobolev truncation library.