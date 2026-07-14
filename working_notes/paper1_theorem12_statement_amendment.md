# Paper 1, Theorems 1.2–1.3 — Statement Amendment

## Source checked

This note concerns Wenxian Shen, *Existence, uniqueness, stability, and
monotonicity of traveling waves for repulsion/attraction chemotaxis models
with logistic type source*, arXiv:2605.04401v1 (6 May 2026).  The source
checked is the archived local copy `paper1.pdf`.

## Four independent defects

### 1. The root comparison in (5.35) has the wrong direction

The coefficient obtained in (5.31) is

```text
q(eta) = eta^2 - (c-A) eta + (1+B),
```

where the displayed definitions (5.32)–(5.33) give `A ≥ 0` and, for
`chi ≠ 0`, `B > 0`.  Since the unperturbed tail exponent `kappa` satisfies

```text
kappa^2 - c kappa + 1 = 0,
```

one has `q(kappa) = A kappa + B > 0`.  Thus `kappa` is not between the two
roots of `q`; under the speed condition used by the paper it lies strictly
below the perturbed lower root.  Consequently the energy calculation does
not prove decay for every `eta > kappa`.  Its direct conclusion requires
`eta` to lie above the perturbed lower root.

### 2. Formula (1.21) uses the wrong spatial coordinate

Section 5 works after changing to the coordinate `z=x-ct` and estimates

```text
E_move(t) = integral exp(2 eta z)
                     |u(t,z+ct)-U(z)|^2 dz.
```

The printed (1.21) instead uses the laboratory-coordinate weight

```text
E_lab(t) = integral exp(2 eta x)
                    |u(t,x)-U(x-ct)|^2 dx.
```

The exact relation is

```text
E_lab(t) = exp(2 eta c t) E_move(t).
```

Therefore decay of the energy actually estimated in Section 5 does not imply
the printed formula.  The weight must move with the wave, equivalently it
must be `exp(2 eta (x-ct))` in laboratory coordinates.

### 3. The exponential factor after (5.35) has the wrong sign

The paper defines the quadratic coefficient `lambda` to be negative and then
writes `exp(-lambda t) → 0`.  For `lambda < 0` this factor grows.  The decaying
factor is `exp(lambda t)`, or, after defining the positive rate
`rho := -lambda`, `exp(-rho t)`.

### 4. Equation (5.18) has two wrong chemotactic signs

The elliptic equation is `v_xx-v+u^gamma=0`. Put `w=u-U` and `z=v-V`.
The zero-order part of the chemotactic flux difference is

```text
(v a_m - a_(m+gamma)) w + U^m z.
```

Consequently the perturbation equation contains

```text
-chi (v a_m - a_(m+gamma) + b_2) w - chi b_4 z.
```

The printed (5.18), and hence (5.19), reverse both the `a_(m+gamma)` sign
and the `b_4 z` sign. This does not force a larger conservative budget in
(5.31): for both signs of `chi`,

```text
|v a_m - a_(m+gamma)|
  <= (2m+gamma) M^(m+gamma-1),
```

and the `b_4` term is estimated by absolute value. The displayed (5.33)
already retains the `(2m+gamma)` contribution.

## Recommended amended statement

Use the paper's limiting error budgets in (5.32)–(5.33), evaluated at the
asymptotic bound `M_chi`, and write them as `A_chi` and `B_chi`.  Define

```text
Delta = (c-A_chi)^2 - 4(1+B_chi),
kappa_minus = ((c-A_chi)-sqrt(Delta))/2,
kappa_plus  = ((c-A_chi)+sqrt(Delta))/2.
```

Choose the speed threshold so that `Delta>0` and

```text
kappa_minus < 1/(1+|chi|^(1/6)) < kappa_plus.
```

Then replace the weight interval in Theorem 1.2 by

```text
kappa_minus < eta < 1/(1+|chi|^(1/6)),
```

and replace (1.21) by the co-moving conclusion

```text
lim_{t→∞} integral exp(2 eta z)
                   |u(t,z+ct;u0)-U(z)|^2 dz = 0.
```

The uniform conclusion (1.22) is retained, subject to the compactness and
far-left rigidity argument in Step 4.  With the paper's sign convention for
the quadratic coefficient, the energy bound uses `exp(lambda t)`; with a
positive decay rate it uses `exp(-rho t)`.

For Theorem 1.3, the common tail exponent must also leave room for the
corrected stability weight: the hypothesis should require a common
`kappa_1 > kappa_minus`, not merely `kappa_1 > kappa`.  The waves constructed
in Theorem 1.1 have the stronger family of tail estimates needed to choose
such a `kappa_1` once the corrected root lies below the construction's tail
cap.

## What would be needed to retain the original interval

The algebraic obstruction concerns the global coefficient estimate used in
(5.31).  It does not disprove stability for weights immediately above
`kappa`: the perturbation coefficients may decay in the right tail.  Retaining
the full interval `kappa < eta` would require a new spatially localized
coercivity or weighted spectral argument.  No such argument appears in
Section 5, so it must not be presented as a formalization of the written
proof.

## Lean certificates and present proof boundary

The repository contains zero-`sorry`, standard-axiom certificates for all
four defects:

- `paper531_kappa_not_between_perturbed_roots`,
  `paper531_kappa_lt_rootMinus`, and
  `paper531_positive_inside_stated_weight_window` in
  `ShenWork/Paper1/Theorem12RootObstruction.lean`;
- `laboratoryWeightedL2Energy_eq_exp_mul_coMoving` and the non-vacuous
  coordinate witness in
  `ShenWork/Paper1/Theorem12CoordinateAudit.lean`;
- `paper531_printed_decay_factor_tendsto_atTop` and
  `paper531_corrected_decay_factor_tendsto_zero` in
  `ShenWork/Paper1/Theorem12RootObstruction.lean`;
- `paper5ChemFluxDifference_expansion_corrected` and
  `paper5CorrectedChemZeroCoefficient_abs_le` in
  `ShenWork/Paper1/Theorem12MeanCoefficients.lean`.

`ShenWork/Paper1/Theorem12Corrected.lean` currently proves the scalar
Gronwall and moving-frame localization wiring, but its general-data PDE
energy/compactness input remains explicit.  Thus the repository does not yet
claim that the full amended stability theorem is proved.  The corrected
Theorem 1.3 structural reduction is in
`ShenWork/Paper1/Theorem13Corrected.lean`; its remaining analytic input is the
same genuine bounded-solution stability theorem.
