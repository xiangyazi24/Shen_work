# Far-left stability of the chemotaxis front: sharp threshold χ=4

The standalone mathematical write-up is
[`FARLEFT_CHI4_MATHEMATICAL.pdf`](FARLEFT_CHI4_MATHEMATICAL.pdf), with source
in [`FARLEFT_CHI4_MATHEMATICAL.tex`](FARLEFT_CHI4_MATHEMATICAL.tex).

The formalization companion is
[`FARLEFT_CHI4_RESOLUTION.pdf`](FARLEFT_CHI4_RESOLUTION.pdf), with source in
[`FARLEFT_CHI4_RESOLUTION.tex`](FARLEFT_CHI4_RESOLUTION.tex).

**Status:** theorem and delimiting counterexample formalized in Lean 4.30.0 /
Mathlib v4.30.0. The cited headline theorems are `sorry`-free and use only
`[propext, Classical.choice, Quot.sound]`.

## Result

For the normalized co-moving system

```text
u_t = u_zz + (c − χv_z)u_z + u(1 − χv + (χ−1)u),
−v_zz + v = u,
```

the plateau `(u,v)=(1,1)` has dispersion relation

```text
dχ(s) = −1 − s + χs/(1+s),   s=k²≥0.
```

For `0≤χ≤1`, its maximum is `−1` at `s=0`. For `χ>1`, its maximum is
`χ−2√χ` at `s=√χ−1`. Hence every mode is strictly stable exactly for `χ<4`;
at `χ=4`, the mode `k²=1` is neutral; above `4`, an unstable mode exists.
The general threshold is `χγ < (1+√α)²`.

Lean:

- `dispersion_le_of_lt_turing`
- `dispersion_pos_of_gt_turing`
- `dispersion_attains_at_sqrt`

in `Paper1/WholeLineChiPosDispersionSharp.lean`.

## Sharp nonlinear entropy

With `h(u)=u−1−log u`, `A=u_z/u`, `W=u−1`, and `r=v−1`, the periodic
calculation gives

```text
d/dt ∫h(u) = −∫A² + χ∫A r_z − ∫W²
           ≤ −(1−χ²/16)∫W²,
```

using the sharp resolver estimate `∫r_z² ≤ 1/4 ∫W²`.

The whole-line localization preserves the leading coefficient with a positive
slowly varying weight and keeps every weight and endpoint error explicit.
Lean:

- `sharp_entropy_production_le`
- `weighted_resolver_le`
- `weighted_sharp_entropy_production_le`
- `wholeLineCauchyGlobalU_weighted_sharp_dissipation`

## Optimal convergence theorem

For every `0≤χ<4`, a global orbit converges uniformly to `u=1` on the moving
far left if it has:

1. a persistent positive far-left band `EventualCoMovingLeftBand`; and
2. the stated translated derivative compactness.

Lean:
`uniformCoMovingLeftEquilibriumConvergence_chiPos_upto_four_basinConditional`.

The basin floor is structural. If a genuine wave of laboratory speed `s` is
viewed in a faster frame `c>s`, then

```text
q(t,z)=U(z+(c−s)t).
```

Every fixed time slice tends to `1` as `z→−∞`, but every fixed frame point
tends to `0` as `t→∞`. Thus no positive lower floor is uniform in late time.
The repository constructs and verifies this PDE counterexample already at
`χ=0`, `s=3`, `c=4`.

Lean:

- `convectiveEscapeProfile_no_uniform_left_floor`
- `IsTravelingWave.convectiveEscape_quantifier_obstruction`
- `exists_genuine_convectiveEscape_counterexample_chi_zero`

This counterexample rules out an unconditional theorem for broad front-like
data in an arbitrary frame. It does not contradict stability from weighted
closeness to a fixed wave, which pins the phase and speed.

The PDF gives the full entropy derivation, localization errors, compactness
argument, quantifier obstruction, and audited failures of the localized
`L¹`, bare `L²`, deep-hole refill, front-anchor, and Harnack routes.
