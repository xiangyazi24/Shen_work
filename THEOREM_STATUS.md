# Shen_work theorem status

This file is the source of truth for whether a paper theorem has actually been
formalized.  The current invariant is:

- `rg -n "\bsorry\b|axiom|admit" ShenWork --glob '*.lean'` should return no Lean
  proof holes.
- `0 sorry` does not mean the paper main theorems are proved.
- Paper-level theorems must not be represented by toy witnesses, constant
  solutions that ignore initial data, or placeholder PDE predicates.

## Status labels

- `not stated`: no Lean theorem currently claims this paper theorem.
- `toy only`: current definitions are too weak or intentionally fake, so the
  theorem is not meaningful as a paper formalization.
- `accurately stated`: theorem statement matches the intended mathematical
  theorem, but proof infrastructure may still be missing.
- `proved`: theorem is proved from non-toy definitions.

## Paper A: traveling waves for chemotaxis-logistic systems

File header reference: `ShenWork/Defs.lean`, arXiv `2605.04401`.

| Paper theorem area | Current Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| PDE and traveling-wave definitions | `CMParams`, `IsClassicalSolution`, `IsGlobalClassicalSolution`, `IsTravelingWave`, `IsMonotoneTravelingWave` | partially stated | Basic whole-line PDE and TW ODE predicates exist. They do not yet encode all regularity/asymptotic normalizations needed for the paper proofs. |
| Global Cauchy existence, boundedness, stabilization | none | not stated | Removed former `cm_global_exist_*`, `cm_stabilize_*`, and wrapper theorems because they used the constant solution and ignored the initial datum. |
| Traveling-wave existence | none | not stated | `TravelingWaves.lean` contains true logistic profile/barrier facts only; it does not produce `IsTravelingWave`. |
| Traveling-wave stability | none | not stated | Removed the former stability wrapper because it only constructed the traveling wave as its own global solution. |
| Traveling-wave uniqueness | none | not stated | Removed the undernormalized uniqueness theorem; right shifts preserve the old hypotheses, so that statement could not be correct. |
| Traveling-wave phase-shift facts | `IsTravelingWave.shift`, `IsMonotoneTravelingWave.shift`, `shift_right_with_exp_bound` | proved | Useful infrastructure for future phase normalization and uniqueness. |
| Maximum/comparison principle | `weak_maximum_principle_linear`, `comparison_principle`, related lemmas | proved | This is real PDE infrastructure, not a paper main theorem by itself. |
| Local ODE shooting segment | `local_shooting_segment_from_E1_*` | proved | Kept as local ODE infrastructure. Removed unsupported global shooting theorem. |
| Heteroclinic to wave projection | `travelingWave_of_heteroclinic` | proved | Converts a supplied global heteroclinic into a wave; does not prove existence. |

Next accurate theorem work:

1. Define the elliptic resolvent layer and moving-frame frozen equation needed by
   Shen's fixed-point construction.
2. Define the invariant sets and barrier predicates used for the Schauder map.
3. State traveling-wave existence only after the map, compactness, continuity,
   and asymptotic normalization are represented.
4. State stability/uniqueness only after the weighted stability theorem and
   right-tail phase normalization are represented.

## Paper B: boundedness/global existence on bounded domains

File header reference: `ShenWork/Paper2/Defs.lean`, arXiv `2512.14858`.

| Paper theorem area | Current Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Bounded-domain PDE solution predicate | `IsClassicalSolution2` | toy only | `pde_satisfied : True`; no domain, boundary condition, PDE, elliptic equation for `v`, or regularity beyond positivity. |
| Boundedness/global existence main theorems | none | not stated | Removed former `cm2_thm*` names because they returned a constant solution independent of the initial datum. |
| Constant equilibrium under toy definition | `cm2_constant_solution_under_current_solution_def` | proved, toy only | Useful only as a sanity check for the current toy predicate. |
| Persistence counterexample under toy definition | `persistence_property_false_under_current_solution_def` | proved, toy only | Documents why Paper3-style persistence cannot follow from the current Paper2 predicate. |

Next accurate theorem work:

1. Replace `IsClassicalSolution2` with a genuine bounded-domain
   parabolic-elliptic solution predicate.
2. Add domain/boundary data, likely Neumann boundary conditions, regularity,
   positivity, and the exact PDE fields.
3. Only then state Paper2 boundedness/global-existence theorems.

## Paper C: persistence and stabilization

File header reference: `ShenWork/Paper3/Defs.lean`, arXiv `2604.02599`.

| Paper theorem area | Current Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Positive equilibrium | `equilibrium` | stated | Algebraic target only; depends on Paper2 parameters. |
| Global asymptotic stability predicate | `IsGloballyAsymptoticallyStable` | toy dependent | Quantifies over `IsGlobalClassicalSolution2`, so it inherits the toy PDE issue. |
| Persistence theorem | none | not stated | Current file proves the old persistence shape false under the toy definition. |
| Negative-sensitivity global stability | none | not stated | Current file proves the old stability shape false under the toy definition. |

Next accurate theorem work:

1. Wait for the real Paper2 solution predicate.
2. Restate persistence and stabilization against that predicate.
3. Add comparison/energy/compactness dependencies from the papers before proving
   any main theorem.

## Current non-paper infrastructure that is useful

- `ShenWork/PDE/ParabolicMaxPrinciple.lean`: weak maximum principle and
  comparison principle.
- `ShenWork/PDE/HeatSemigroup.lean`: heat-kernel and `L∞` bounds.
- `ShenWork/PDE/MildSolution.lean`: pointwise Duhamel/contraction estimates and
  `abstract_mild_fixed_point`.
- `ShenWork/PDE/TravelingWaveConstruction.lean`: true logistic profile facts.
- `ShenWork/PDE/TravelingWaveODE.lean`: finite-dimensional ODE local existence,
  equilibria, Jacobian/eigenvector facts, and local shooting segment.

## Build policy

All Lean validation must use the remote uisai1 script:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh shen_work
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh shen_work --file ShenWork/Defs.lean
```

Do not run local `lake build` or local `lake env lean`.
