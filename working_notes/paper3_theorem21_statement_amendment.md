# Paper 3 Theorem 2.1 — Statement and Interface Amendment

Date: 2026-07-14

## Source checked

This note checks the original source rather than a repository paraphrase:

- Le Chen, Ian Ruau, and Wenxian Shen, *Chemotaxis models with
  signal-dependent sensitivity and a logistic-type source, II: Persistence and
  stabilization*, arXiv:2604.02599v1, 3 April 2026.
- Theorem 2.1 is titled “Uniform persistence.”
- Section 4.1 contains the proof of part (1); Section 4.4 contains the proof of
  part (4).

Two separate amendments are needed. The first is a genuine parameter omission
in the printed theorem. The second is not an error in the paper: it corrects
the way the paper's initial mass was represented by the Lean trajectory API.

## 1. The omitted pure-decay regime in part (1)

The printed part (1) assumes only `m >= 1` and claims that every globally
defined, bounded, positive solution satisfies

```text
liminf_{t -> infinity} inf_x u(t,x) > 0.
```

However, Section 4.1 divides its proof into exactly two cases:

1. `a = b = 0`;
2. `a > 0` and `b > 0`.

It never treats the allowed regime `a = 0 < b`. In that regime the conclusion
is false.

### Concrete counterexample

On any bounded Neumann domain, take a spatially constant solution. For
`a = 0`, `b > 0`, and initial value `c > 0`, set

```text
u(t,x) = (c^{-alpha} + alpha b t)^{-1/alpha},
v(t,x) = (nu/mu) u(t,x)^gamma.
```

All spatial derivatives vanish. Thus the chemotaxis divergence and Neumann
terms vanish, the elliptic equation holds identically, and the parabolic
equation reduces to

```text
u_t = -b u^{1+alpha}.
```

The solution is classical, strictly positive for every finite positive time,
global, and bounded by `c`, but

```text
lim_{t -> infinity} inf_x u(t,x) = 0.
```

The simplest concrete instance, used by the Lean proof, is
`alpha = gamma = m = mu = nu = b = 1`, `a = chi0 = 0`, for which
`u(t,x) = v(t,x) = 1/(1+t)` on positive time.

### Corrected part (1)

The paper-faithful correction is to add the parameter split actually used in
Section 4.1:

> Assume `m >= 1` and either `a = b = 0` or `a > 0, b > 0`. Then every
> globally defined, bounded, positive solution has a strictly positive
> asymptotic spatial lower bound for `u`, and the displayed elliptic lower
> bound for `v` follows.

The remaining nonnegative-parameter regime `a > 0, b = 0` does not supply a
counterexample of the preceding type: integrating the equation gives
`M'(t) = a M(t)`, because the Neumann diffusion and chemotaxis divergences
integrate to zero. A positive solution therefore has exponentially growing
mass and cannot be globally bounded. The persistence implication is vacuous
there. For statement fidelity, the recommended theorem states the two regimes
proved in the paper rather than silently adding a vacuous third branch.

## 2. The positive-time mass interface in part (4)

Part (4) is a minimal-model statement (`a = b = 0`, `m = 1`). The paper starts
from an initial datum `u0`, constructs its solution, and imposes the mass
condition on that datum. In the paper this is unambiguous because
`u(t) -> u0` as `t -> 0+`; mass conservation then identifies every positive
time slice with the initial mass.

The original Lean formalization used

```text
HasInitialMass D u uStar := D.integral (u 0) = D.volume * uStar.
```

But `IsPaper2GlobalClassicalSolution` constrains the trajectory only on strict
positive time intervals. Its stored value `u 0` is free. Replacing only that
zero-time slice preserves the entire classical positive-time orbit, positivity,
and boundedness, while changing `HasInitialMass` arbitrarily. Consequently the
old Lean version of part (4) is false for every admissible constants package.

The correct formal interface is the physical conserved mass:

```text
HasEquilibriumMassOnPositiveTimes D u uStar :=
  forall t > 0, D.integral (u t) = D.volume * uStar.
```

Equivalently, one may quantify over an initial datum `u0`, require an actual
initial-trace relation between `u0` and `u`, and place the mass condition on
`u0`. The positive-time formulation is the shorter interface for the
persistence proof and exactly states the invariant it consumes.

This is a Lean-interface amendment, not a claim that the paper's mathematical
part (4) is false.

## Lean realization

The concrete, `sorry`-free results are:

```text
ShenWork.Paper3.not_Theorem_2_1_part1_intervalDomain_pureDecay
```

in
`ShenWork/Paper3/IntervalDomainPersistencePart1StatementObstruction.lean`.
It constructs the genuine interval-domain pure-decay solution, proves global
classical solvability and boundedness, computes the lower-envelope liminf as
zero, and refutes the unguarded part (1). The same file defines
`Theorem_2_1_part1_corrected` with the Section 4.1 parameter split.

For part (4),

```text
ShenWork.Paper3.not_intervalDomain_Theorem_2_1_part4_anyConstants
```

in
`ShenWork/Paper3/IntervalDomainPersistenceMinimalMassInterfaceObstruction.lean`
proves that the old zero-slice formulation fails for every `Paper3Constants`
package. The corrected theorem is

```text
ShenWork.Paper3.Theorem_2_1_part4_intervalDomainM_physicalMass_proven
```

in
`ShenWork/Paper3/IntervalDomainPersistenceMinimalPhysicalMass.lean`.
It uses the paper-faithful `u^m` domain, the conserved positive-time mass, the
proved eventual upper bound, and the quantitative Neumann-resolver mass gap.

All three capstones print only the standard Lean/Mathlib axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Recommended amendment

1. Amend Theorem 2.1(1) by adding
   `(a = b = 0) or (a > 0 and b > 0)`.
2. Retain the mathematical mass hypothesis of Theorem 2.1(4), but in the Lean
   statement attach it to the initial datum plus initial trace, or state the
   equivalent conserved positive-time mass.
3. Do not treat an axiom-clean proof of the old statements as sufficient:
   both failures are semantic and can be proved without introducing any
   nonstandard axiom.

