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

## What is intentionally not claimed

- No paper-level traveling-wave existence theorem is currently stated.
- No paper-level traveling-wave stability or uniqueness theorem is currently
  stated.
- No Paper2 bounded-domain global existence theorem is currently stated.
- No Paper3 persistence or stabilization theorem is currently stated.

Several old theorem-shaped placeholders were removed because they were toy
statements: constant solutions ignoring initial data, unsupported shooting
claims, undernormalized uniqueness, or local mild existence without an actual
complete metric self-map.

## Main next target

Rebuild the theorem layer accurately:

1. Replace Paper2/Paper3 toy solution predicates with genuine bounded-domain PDE
   predicates.
2. For the traveling-wave paper, formalize Shen's fixed-point/comparison route:
   elliptic resolvent, moving-frame frozen equation, barriers, invariant sets,
   compact/continuous Schauder map, asymptotic normalization, then stability and
   uniqueness.
3. Keep `0 sorry`; unproved paper theorem goals should live in documentation or
   dependency matrices until their statements are accurate and provable.

## Build policy

Do not run local Lean builds.  Use uisai1 only:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh shen_work
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh shen_work --file <path.lean>
```
