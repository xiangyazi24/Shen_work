# General-m minimal-equilibrium stability

The rigorous write-up is
[`GENERAL_M_STABILITY_RESOLUTION.pdf`](GENERAL_M_STABILITY_RESOLUTION.pdf),
with source in
[`GENERAL_M_STABILITY_RESOLUTION.tex`](GENERAL_M_STABILITY_RESOLUTION.tex).

**Status:** the sufficient stability regions and the exact `m=3` false-side
counterexample are formalized in Lean 4.30.0 / Mathlib v4.30.0. The
bifurcation-direction curve is an explicit weakly nonlinear calculation,
cross-checked by finite-difference and pseudo-arclength continuation.

## Exact formalized results

| Range | Hypotheses | Conclusion |
|---|---|---|
| `1≤m<2` | either disjunct of the explicit full-m stability formula | mass-constrained global sup convergence and orbitwise eventual exponential `C¹` convergence |
| `m=2` | same formula plus the explicit critical endpoint admissibility | same conclusion |
| every `m>1` | linear stability plus the explicit small-sensitivity inequality associated with a certified local basin radius | same conclusion |
| `m=3`, `β=γ=μ=ν=u*=1` | some `0<χ₀<χ_lin` | global attraction is false: an exact nonconstant positive steady orbit exists |

Principal theorems:

- `intervalDomainM_Theorem_2_5_EventualGlobalStabilityFormula`
- `intervalDomainM_Theorem_2_5_critical_EventualGlobalStabilityFormula`
- `intervalDomainM_Theorem_2_5_supercritical_smallSensitivity`
- `exists_nonconstant_minimal_steady_below_threshold_m3`
- `minimal_equilibrium_global_stability_false_m3`

The all-`m>1` route uses good times for

```text
G(t)=∫u^(-2m)u_x²
```

and the oscillation identity

```text
|u(x)^(1−m)−u(z)^(1−m)| ≤ (m−1)√G(t).
```

For a local basin radius `0<δ<u*`, this yields the explicit sufficient
condition

```text
χ₀ < r_m(u*,δ) / ((m−1)√μ σ_β),
```

where `r_m` is the negative-power basin radius and `σ_β` is the sharp
signal-saturation factor.

## Bifurcation boundary

In the normalized family `β=γ=μ=ν=1`, write

```text
u = U + ε cos(πx) + ε² a₂ cos(2πx) + …
χ = χ_lin + ε² χ₂ + …
```

The explicit Lyapunov–Schmidt coefficient changes sign at:

- `U=0.5`: `m_c=2.866754572143`
- `U=1`: `m_c=2.936658202934`
- `U=2`: `m_c=3.005668668328`

For `m>m_c(U)`, the weakly nonlinear coefficient predicts that the first
steady branch is backward. The repository promotes that prediction to an
actual local obstruction below the linear threshold for the fixed
`m=3, U=1` tuple, by proving the branch exactly in a Wiener algebra:

```text
χ_lin = 2(1+π²),
χ′(0)=0,
χ″(0)=−(6π⁴+37π²+25)/(24π²(π²+1)) < 0.
```

It then proves positivity, Neumann boundary conditions, mass one,
nonconstancy, both classical steady equations, and failure of global
attraction.

The direction curve is not a complete necessary-and-sufficient global
stability diagram. In particular, `m<m_c(U)` only makes this coefficient
positive; it does not prove stability for every `χ₀<χ_lin`, and the note does
not assert an all-`m` local branch theorem. The PDF states the remaining
unclassified region explicitly.

The reproducible calculation and continuation code is
[`m_supercritical_bifurcation_probe.py`](m_supercritical_bifurcation_probe.py).
