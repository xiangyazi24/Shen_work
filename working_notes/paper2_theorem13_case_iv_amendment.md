# Paper 2 Theorem 1.3(iv) — Exponent-Domain Amendment

Date: 2026-07-13

## Source checked

This note concerns the original submission:

- Le Chen, Ian Ruau, and Wenxian Shen, *Chemotaxis models with
  signal-dependent sensitivity and a logistic-type source, I: Boundedness and
  global existence*, arXiv:2512.14858v1, 16 December 2025.
- Local archival copy: `paper2.pdf`.

Theorem 1.3(iv) assumes

```text
beta >= 1/2,
alpha = 2m + gamma - 2,
```

together with the smallness alternative (1.25).  The theorem is stated for
all positive `m`, `gamma`, and `alpha`.

## Missing exponent-domain condition

Section 5.4 invokes Proposition 2.2 with

```text
s(P) = (P + alpha) / gamma.
```

Proposition 2.2 requires `s(P) > 1`.  Under the critical identity in
Theorem 1.3(iv), this requirement is exactly

```text
P > 2 - 2m.
```

The proof chooses a seed exponent immediately to the right of

```text
q_* = max{1, N alpha / 2}.
```

It therefore needs the additional strict condition

```text
q_* > 2 - 2m,
```

equivalently

```text
1 < (q_* + alpha) / gamma.
```

This condition is not a consequence of the hypotheses printed in alternative
(iv).  The sentence in Section 5.4 asserting that the Proposition 2.2
exponent is above one for all seed powers is false in the uncovered range.

## Concrete admitted parameter wedge

On the interval, take

```text
N = 1,  m = 1/4,  gamma = 7/2,  alpha = 2,  beta = 1.
```

Then

```text
alpha = 2m + gamma - 2,
q_* = max{1, alpha/2} = 1,
s(q_*) = (1 + 2)/(7/2) = 6/7 < 1.
```

Moreover, `positivePart(N alpha - 2) = 0`.  Hence the first disjunct in
(1.25) holds automatically, so the printed theorem imposes no smallness
restriction on `chi_0`.  But Proposition 2.2 cannot be applied until
`P > 3/2`.  At such powers the squared-chemotaxis coefficient is nonzero, and
the automatically true first disjunct of (1.25) supplies no estimate that
creates the required low seed.  Thus the written proof does not cover these
parameters.

This is a proof gap, not a counterexample to the boundedness conclusion.  A
different estimate might eventually recover some or all of the missing
wedge.  The current argument does not.

## Corrected theorem supported by the proof

For the route used in Section 5.4, add

```text
max{1, N alpha/2} > 2 - 2m.
```

On the one-dimensional interval this becomes

```text
max{1, alpha/2} > 2 - 2m.
```

With this hypothesis, the literal profile in (1.19) is continuous at `q_*`,
the threshold (1.25) produces a power `p_0 > q_*` with strict damping, and
the one-dimensional fixed-target interpolation is valid because
`alpha < 2p_0`.  One finite target power above `m` and `gamma` then feeds the
restarted Neumann-semigroup endpoint.  No infinite Moser iteration is needed.

## Lean status

The formalization deliberately keeps the missing condition visible.

- `IntervalDomainTheorem13CriticalConstants.lean` defines the literal
  `M^*`, `q_*`, and right-sided `liminf K`.  Construction of the paper
  constant requires `1 < (q_* + alpha)/gamma`.
- `IntervalDomainTheorem13CriticalSeed.lean` proves the case-(iv) energy
  estimate with the explicit hypothesis `2 - 2m < P`.
- `IntervalDomainTheorem13CriticalThreshold.lean` turns (1.25) into a genuine
  low-power seed under `q_* > 2 - 2m`.
- `IntervalDomainTheorem13CriticalBootstrap.lean` proves
  `boundedBefore_critical_case_iv_corrected` on the faithful general-`m`
  interval model.  It uses the real weighted-gradient estimate, a single
  fixed-target Agmon/Gagliardo--Nirenberg absorption, and the proved restarted
  finite-`L^P` to `L^infinity` endpoint.

All exported capstones are `sorry`-free and their `#print axioms` output is
exactly `propext`, `Classical.choice`, and `Quot.sound`.

The original alternative (iii) does not have this defect.  Under
`alpha = m + gamma - 1`, one has

```text
(q_* + alpha)/gamma > 1
```

from `q_* >= 1` and `m > 0`; the formalization proves its original threshold
without an extra exponent-domain assumption.
