# Paper 2 Theorem 1.2 — Statement Amendment

Date: 2026-07-12

## Source checked

This note checks the original source, not the repository paraphrase:

- Le Chen, Ian Ruau, and Wenxian Shen, *Chemotaxis models with
  signal-dependent sensitivity and a logistic-type source, I: Boundedness and
  global existence*, arXiv:2512.14858v1, 16 December 2025.
- Local archival copies: `paper2.pdf` and
  `.tmp/arxiv/2512.14858.tar` (`11-15-2025-CRS-1.tex`).

Theorem 1.2 in the submitted source assumes

> `a, b >= 0` and `beta >= 1`.

It claims boundedness for `0 < m < 1`, and boundedness plus global existence
for `m = 1` under the displayed smallness condition on `chi0`.  Remark 1.4(2)
also says that `a` and `b` can be zero.  There is no earlier convention that
excludes the mixed case `a > 0`, `b = 0`.

## Counterexample to the published statement

Let `a > 0`, `b = 0`, and take any positive constant initial datum `u0 = c`.
On any smooth bounded Neumann domain, define the spatially constant functions

```text
u(t,x) = c exp(a t),
v(t,x) = (nu/mu) u(t,x)^gamma.
```

All spatial derivatives and the chemotaxis divergence vanish.  The elliptic
equation for `v` holds at every time, and the parabolic equation reduces to

```text
u_t = a u.
```

Thus this is a positive global classical solution, for every `m > 0`, every
`beta >= 0`, and every `chi0`.  Nevertheless,

```text
||u(t)||_infinity = c exp(a t) -> infinity.
```

Consequently:

- Theorem 1.2(1) is false in the mixed branch `a > 0`, `b = 0`.
- Theorem 1.2(2) is already false with
  `m = 1`, `beta = 1`, and `chi0 = 0`, since the smallness hypothesis is then
  satisfied.

The same contradiction can be stated without constructing the preferred
solution.  For every positive classical solution with `b = 0`, the Neumann
mass identity gives

```text
M'(t) = a M(t),  where M(t) = integral u(t,x) dx.
```

Positivity gives `M(t) > 0`, so `a > 0` forces unbounded mass.  On a bounded
unit-volume domain, mass is bounded above by the supremum norm.  Hence no
eventually bounded global positive solution can exist in this branch.

## Where the published proof loses the hypothesis

The issue occurs in both parts of Section 4.

1. Proposition 2.4 supplies a uniform mass bound only in the two cases

   ```text
   a = b = 0,  or  a > 0 and b > 0.
   ```

2. In Section 4.2, the proof of Theorem 1.2(1) drops the nonpositive term
   `-b integral u^(p+alpha)`, and later invokes Lemma 4.1 together with
   Proposition 2.4 to replace a mass-dependent term by a time-independent
   constant.  Proposition 2.4 does not provide that constant when
   `a > 0`, `b = 0`.

3. In Section 4.3, the proof of Theorem 1.2(2) says that, because the result is
   intended for all `b >= 0`, one may assume `b = 0`.  Step 1 derives

   ```text
   (1/p) d/dt integral u^p
     <= - integral u^p + C (integral u)^p
   ```

   and then claims a uniform-in-time `L^p` bound by Gronwall.  This conclusion
   requires a uniform mass bound.  In the omitted mixed branch the forcing
   mass grows like `exp(a t)`, so Gronwall gives growth rather than a uniform
   bound.

4. The appeal to Theorem 1.1 for `chi0 <= 0` does not repair this case:
   Theorem 1.1 itself treats only `a = b = 0` and `a > 0, b > 0`.

## Correct parameter statement

The exact correction directly supported by the written proof is

```text
(a = b = 0) or (a > 0 and b > 0).
```

A slightly stronger and mathematically natural correction is

```text
a = 0 or b > 0.
```

Under the standing assumptions `a, b >= 0`, this is equivalent to excluding
exactly the false branch

```text
not (a > 0 and b = 0).
```

The stronger correction needs only the elementary missing mass case:
if `a = 0` and `b > 0`, then

```text
M'(t) = -b integral u^(1+alpha) <= 0,
```

so the same uniform mass input used by the Section 4 proof is available.

Recommended amended wording:

> Assume `beta >= 1` and either `a = 0` or `b > 0`.  If `0 < m < 1`, then
> (1.23) holds.  If `m = 1` and
> `chi0 < 2(2 beta - 1) / max{2, gamma N}`, then (1.23) holds and
> `Tmax(u0) = infinity`.

If no new mass subcase is to be added, replace “either `a = 0` or `b > 0`” by
“either `a = b = 0` or `a, b > 0`”.  Remark 1.4(2) should then say that both
parameters may vanish simultaneously, rather than suggesting all mixed
nonnegative cases.

## Lean amendment

The repository now contains a concrete and a general interval-domain
refutation in
`ShenWork/Paper2/IntervalDomainTheorem12Refutation.lean`:

```text
not_Theorem_1_2_intervalDomain_when_a_pos_b_zero
not_Theorem_1_2_intervalDomain_of_a_pos_b_zero
```

Both are `sorry`-free and use only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.

The existing Lean definition has a second, independent fidelity problem in
part (1).  It asks only for the existence of some bounded local solution on
some positive finite horizon.  The paper instead fixes the unique maximal
solution and asserts boundedness on its entire maximal interval.  A faithful
replacement should use the already defined continuation objects in
`ShenWork/PDE/IntervalDomainExistence.lean`:

```text
ReachableClassicalHorizon
ReachableArbitrarilyLong
FiniteContinuationAlternativeBranch
StandardContinuationAlternative
```

In particular, a bare existential local witness is not an adequate
formalization of (1.23).  The corrected headline must quantify over the
maximal-continuation branch, with a finite `Tmax` alternative only when the
reachable horizons are bounded above, and a genuine global/glued branch when
they are unbounded.

Theorem 1.3 is not affected by this particular `a > 0, b = 0`
counterexample, because it explicitly assumes `a, b > 0`.  A separate
exponent-domain defect in the proof of Theorem 1.3(iv) is documented in
`paper2_theorem13_case_iv_amendment.md`.
