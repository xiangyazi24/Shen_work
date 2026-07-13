# Paper 1 Theorem 1.2 stability audit (2026-07-13)

Two independent issues block a faithful proof of the literal headline as
currently stated.

## 1. The root comparison in (5.35) has the wrong direction

Equation (5.31) has coefficient

```text
q(eta) = eta^2 - (c - A) eta + (1 + B),
A = |chi|^(1-3 sigma) D',  B = |chi|^(1-3 sigma) D''.
```

The displayed definitions (5.32)--(5.33) make `A >= 0`; when `chi != 0`,
the final summand in (5.33) makes `B > 0`. Since
`kappa^2 - c kappa + 1 = 0`, one has

```text
q(kappa) = A kappa + B > 0.
```

Therefore `kappa` cannot lie between the two roots of `q`. In fact, by
continuity there are weights strictly above `kappa` for which `q` is still
positive. Thus (5.35)'s printed comparison `kappa^- <= kappa < kappa^+`
does not follow and is algebraically false for `chi != 0` under the displayed
signs. The direct correction for this energy estimate is to require
`eta > kappa^-` (the perturbed lower root), not merely `eta > kappa`.

Lean certificates:

- `paper531_kappa_not_between_perturbed_roots`
- `paper531_positive_inside_stated_weight_window`
- `paper531_actual_correction_pos`
- `paper531_numeric_sanity_root_window_impossible`

in `Theorem12RootObstruction.lean`.

This is a gap in the displayed proof, not by itself a counterexample to the
stability theorem: a sharper spatially localized coercivity argument might
retain the full open interval `eta > kappa` because the perturbation
coefficients vanish in the right tail.

## 2. The weighted norm is written in the wrong coordinate

Section 5 estimates the stationary-wave/moving-coordinate energy

```text
E_move(t) = integral exp(2 eta z) |u_lab(t,z+ct)-U(z)|^2 dz.
```

The literal formula (1.21), and the previous Lean definition
`WeightedL2MovingFrameConvergence`, instead use

```text
E_lab(t) = integral exp(2 eta x) |u_lab(t,x)-U(x-ct)|^2 dx.
```

The exact change of variables is

```text
E_lab(t) = exp(2 eta c t) E_move(t).
```

Hence decay of the energy actually estimated in Section 5 does not imply the
literal (1.21) unless its decay rate is strictly larger than `2 eta c`.
The paper's rate does not supply that condition. The natural correction is
to put the weight in the moving coordinate, equivalently use
`exp(2 eta (x-ct))` in laboratory coordinates.

Lean certificates:

- `laboratoryWeightedL2Energy_eq_exp_mul_coMoving`
- `WeightedL2MovingFrameConvergence.of_coMoving_exponential_decay`
- `coordinate_weight_mismatch_nonvacuous`

in `Theorem12CoordinateAudit.lean`.

The last theorem is deliberately a function-level coordinate sanity witness,
not a claimed PDE counterexample.

## Formalization consequence

The literal Paper 1 Theorem 1.2 must not be marked complete through the
current (5.31)--(5.35) route. A faithful continuation has two possible
targets:

1. an amended moving-coordinate theorem with the perturbed-root lower weight;
2. the full moving-coordinate interval `eta > kappa`, but only after replacing
   the false global root comparison by a new localized coercivity proof.

The whole-line Cauchy construction and nonlinear perturbation identity remain
separate analytic frontiers after this audit.

