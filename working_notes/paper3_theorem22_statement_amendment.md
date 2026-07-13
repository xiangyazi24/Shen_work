# Paper 3 Theorem 2.2 — Statement Amendment

Date: 2026-07-12

## Source checked

This note checks the original source, not the repository paraphrase:

- Le Chen, Ian Ruau, and Wenxian Shen, *Chemotaxis models with
  signal-dependent sensitivity and a logistic-type source, II: Persistence and
  stabilization*, arXiv:2604.02599v1, 3 April 2026.
- Theorem 2.2 there is titled "Linear stability and instability."

Theorem 2.2 concerns the positive constant equilibrium `(u*, v*)`,
`u* = (a/b)^{1/alpha}`, of the bounded-domain Neumann problem.  Part (1) states,
for `a, b > 0`:

1. if `chi0 < chi*_{a,b,beta}(u*)` the equilibrium is **linearly stable**;
2. if `chi0 > chi*` it is **linearly unstable**;
3. moreover, in the stable regime there exist `C, delta, lambda > 0` such that
   every `u0` satisfying the initial-data condition (1.8) **and** a smallness
   condition obeys the exponential estimate (2.12) **for all `t >= 0`** in the
   `C^1` norm.

Part (2) is the corresponding minimal-model statement (`a = b = 0`), with the
mass constraint added.

The initial-data hypothesis (1.8) requires only `u0 in C(bar Omega)` (continuous,
positive).  Proposition 1.1 supplies convergence to `u0` in `L^infinity` as
`t -> 0+`, and classical spatial regularity only for **positive** time.  There
is **no** `C^1`, Sobolev, or fractional-power smallness hypothesis on `u0` in
the statement of Theorem 2.2.

## The over-statement in the published (2.12)

The printed nonlinear clause asserts, for data small only in `L^infinity`, a
`C^1` exponential estimate that holds **at every `t >= 0`, including `t = 0`**:

```text
|| u(t) - u* ||_{C^1}  <=  C e^{-delta t} (...),   for all t >= 0.
```

This clause is not well-posed under the theorem's own initial-data hypothesis:

- `u0` is only required to lie in `C(bar Omega)`, so `|| u0 - u* ||_{C^1}` need
  not be finite; the `t = 0` instance of (2.12) can be meaningless.
- Even restricting to `C^1` data, an `L^infinity`-ball contains functions of
  arbitrarily large `C^1` norm, so no single constant `C` can control the
  `t = 0` (or `t -> 0+`) `C^1` size uniformly over the admitted class.

Concretely, on the unit interval `(0,1)` with Neumann conditions take

```text
u0,N (x) = u* + N^{-1/2} cos(N pi x).
```

For large `N` this satisfies (1.8), is positive, has
`|| u0,N - u* ||_infinity = N^{-1/2} -> 0` (and, in the minimal model, exact
mass `u*`), yet `|| u0,N - u* ||_{C^1} = N^{1/2} pi -> infinity`.  So no
uniform-in-data `t = 0` `C^1` estimate of the form (2.12) can hold.  The
smallness is `L^infinity`; the conclusion is measured in `C^1`; the two are
unrelated at `t = 0`.

## What the published proof actually establishes

Section 5.1 proves the result in two distinct stages, both correct:

- **Stage A (strong-norm, all-time).**  For data small in the fractional-power
  space `X^alpha = D((I - L)^alpha)` (which, in one dimension, embeds into `C^1`
  for `alpha > 3/4`), the standard sectorial nonlinear-stability theorem
  (Henry, *Geometric Theory of Semilinear Parabolic Equations*, Ch. 5-6) gives
  exponential decay in `X^alpha` **for all `t >= 0`**.  This is instantaneous
  and correct.

- **Stage B (`L^infinity`-small, eventual).**  For data small only in
  `L^infinity`, the proof first evolves to a **positive** time `T0`, at which the
  analytic-semigroup smoothing places the solution in a small `X^alpha`
  neighbourhood, and then applies Stage A.  This yields exponential decay
  **for `t >= T0`** — an *eventual* estimate, not a `t = 0` estimate.

Thus the mechanism proves (A) an all-time estimate in the strong norm and (B)
an eventual estimate in `C^1` for `L^infinity`-small data.  It does **not**
prove the printed (2.12) at `t = 0` from `L^infinity` data; that conjunction is
the over-statement.

## Correct statement

The faithful correction splits the printed clause into the two statements the
proof supports:

1. **Strong-norm, all-time:** there is `alpha in (3/4, 1)` and `rho, C, delta > 0`
   such that if `|| u0 - u* ||_{X^alpha} <= rho` then
   `|| u(t) - u* ||_{X^alpha} <= C e^{-delta t} || u0 - u* ||_{X^alpha}` for all
   `t >= 0`.

2. **`L^infinity`-small, eventual:** there is `eps, C', delta' > 0` and, for each
   admissible datum, a time `t0 = t0(u0) > 0` such that if
   `|| u0 - u* ||_infinity <= eps` then `|| u(t) - u* ||_{C^1} <= C' e^{-delta'(t - t0)}`
   for all `t >= t0`.

The linear stability/instability dichotomy of Theorem 2.2 is unaffected and
correct; only the nonlinear clause (2.12) needs the `t = 0`-versus-eventual and
`L^infinity`-versus-`X^alpha` distinctions made explicit.

## A companion parameter-fidelity point

The sufficient stability bound `kappa < (sqrt(mu) + sqrt(a alpha))^2` (with
`kappa = chi0 gamma nu u*^gamma (1 + v*)^{-beta}`) is the *continuous* minimum of
`(lambda + mu)(lambda + a alpha) / lambda` over `lambda > 0`.  On a bounded
domain the Neumann spectrum is discrete (`lambda_n = n^2 pi^2` on `(0,1)`), so
the exact stable half of Theorem 2.2 is governed by the **discrete** infimum
`min_{n >= 1} sigma_n < 0`, which the continuous bound only implies (and can be
strictly stronger than needed).  A faithful formalization should clear the
discrete mode condition, not stop at the continuous sufficient bound.

## Lean amendment

The repository records the formal refutation of the literal sup-norm `C^1`
clause: in the Paper 3 development,

```text
Paper3.not_LinearStabilityInstabilityNonminimalRaw_constant_c1Distance
```

proves that the raw sup-norm local-stability branch is false when `L^infinity`
closeness and `C^1` distance are unrelated (the `u0,N` family above is the
witness).  The corrected targets used in the repository are the eventual,
equilibrium-specific, full-mode orbit bound

```text
IntervalDomainSpectralSemigroupOrbitBoundEventualEquilibriumWithoutMass
```

(full linearized multiplier `exp(-d_k t)`, `d_k = a alpha + lambda_k -
kappa lambda_k / (lambda_k + mu)` for every mode `k` including `k = 0`, with a
uniform positive delay `t0`), together with `LocallyExponentiallyStableFromSup`
for the positive equilibrium (no mass constraint, which is needed only in the
minimal `a = b = 0` model).  The over-stated `...Raw` frontier — the pure
Neumann heat multiplier quantified over all `t >= 0` — is not the correct
analytic object and is refuted for a genuine `C^1` distance from `L^infinity`
data.

## Relation to Paper 1 (arXiv:2512.14858) Theorem 1.2

This is the **second** statement-level issue found during formalization of the
Chen-Ruau-Shen series.  The first, recorded in
`paper2_theorem12_statement_amendment.md`, is a genuine *parameter* error:
Theorem 1.2 of Part I omits the guard excluding `a > 0, b = 0`, a branch in
which the solution is provably unbounded (`M'(t) = a M(t)`).  The present issue
is a *statement over-statement*: the intended stability result of Part II holds
in the corrected two-stage form above, but the printed `(2.12)` — a `t = 0`
`C^1` estimate from `L^infinity`-small data — is not well-posed as written.
