# UNDERSTANDING.md — Shen_work current state

This repository is now theorem-driven rather than `sorry`-driven.

The current Lean invariant is:

```bash
rg -n "\bsorry\b|axiom|admit" ShenWork --glob '*.lean'
```

should return no proof holes.  This invariant is necessary but not sufficient:
the three paper main theorems are not yet formalized as proved Lean theorems.

Use `THEOREM_STATUS.md` as the source of truth for paper-theorem status.

## What is genuinely present

- Whole-line chemotaxis and traveling-wave predicates in `ShenWork/Defs.lean`.
- Basic elliptic-resolvent facts for `Psi`.
- Heat-kernel and `L∞` estimates.
- A proved weak parabolic maximum principle and comparison principle.
- True logistic profile/barrier facts; these are not traveling waves.
- Traveling-wave phase-shift infrastructure.
- ODE local existence, equilibria, Jacobian/eigenvector facts, and local
  shooting-segment lemmas.
- Pointwise mild/Duhamel contraction estimates and an abstract Banach fixed-point
  wrapper.
- For Paper1, positive-sensitivity Shen upper bounds imply the strict upper-tail
  bound used in the stability/uniqueness layer.  The negative-sensitivity bound
  stated as `U < max 1 exp(-κx)` does **not** imply the strict `min` tail bound;
  do not use it as a stability-tail bridge without an additional right-tail
  estimate.

## What is intentionally not claimed

- Paper main theorems now have Lean `Prop` statement targets in
  `ShenWork/Paper1/Statements.lean`, `ShenWork/Paper2/Statements.lean`, and
  `ShenWork/Paper3/Statements.lean`.
- These are not proved paper theorems.
- Several statement targets still use abstract packages for bounded domains,
  spectral data, constants, regularity, and convergence norms.  Those packages
  must be refined into exact definitions before the statements can be marked
  `accurately stated`.

Several old theorem-shaped placeholders were removed because they were toy
statements: constant solutions ignoring initial data, unsupported shooting
claims, undernormalized uniqueness, or local mild existence without an actual
complete metric self-map.

## Main next target

Rebuild the theorem layer accurately:

1. Use `PAPER_INVENTORY.md` to formalize every numbered definition, proposition,
   lemma, corollary, theorem, and named estimate that later results depend on.
2. Replace Paper2/Paper3 abstract bounded-domain packages with genuine smooth
   bounded-domain PDE objects.
3. For the traveling-wave paper, formalize Shen's fixed-point/comparison route:
   elliptic resolvent, moving-frame frozen equation, barriers, invariant sets,
   compact/continuous Schauder map, asymptotic normalization, then stability and
   uniqueness.
4. For new theorem layers it is acceptable to introduce `sorry` only when the
   statement is mathematically honest and represents real paper work, not a fake
   shortcut or toy theorem.

## Reference notes

The `ref/` directory now includes travelling-wave background material:

- Wang, *Mathematics of traveling waves in chemotaxis* (2013), a review focused
  on logarithmic-sensitivity chemotaxis waves, including existence, wave speed,
  decay, stability, and diffusion limits.
- Li--Park, *Traveling waves in a chemotaxis model with logistic growth* (2019),
  which proves a heteroclinic travelling wave for a different chemotaxis model by
  constructing a positively invariant set in a three-dimensional phase space.

These references are useful for comparison and for general travelling-wave
infrastructure, but Shen 2026 should still be formalized along its own route:
parabolic fixed point, comparison, barriers, local-uniform compactness, weighted
stability, and uniqueness via stability.  Do not replace Shen's construction by
an unsupported shooting/phase-plane theorem.

## Build policy

Do not run local Lean builds.  Use uisai1 only:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh shen_work
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh shen_work --file <path.lean>
```
