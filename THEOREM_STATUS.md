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
- `statement target`: theorem statement is represented as a Lean `Prop` target,
  but is not yet proved.
- `accurately stated`: theorem statement matches the intended mathematical
  theorem and is ready to prove.
- `proved`: theorem is proved from non-toy definitions.

## Paper A: traveling waves for chemotaxis-logistic systems

File header reference: `ShenWork/Defs.lean`, arXiv `2605.04401`.

| Paper theorem area | Current Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| PDE and traveling-wave definitions | `CMParams`, `IsClassicalSolution`, `IsGlobalClassicalSolution`, `IsTravelingWave`, `IsMonotoneTravelingWave` | partially stated | Basic whole-line PDE and TW ODE predicates exist. They do not yet encode all regularity/asymptotic normalizations needed for the paper proofs. |
| Proposition 1.1 global Cauchy existence/bounds | `Paper1.Proposition_1_1` | statement target | Stated from `paper1.pdf`; proof infrastructure still missing. |
| Proposition 1.2 constant-solution stability | `Paper1.Proposition_1_2` | statement target | Stated from `paper1.pdf`; proof infrastructure still missing. |
| Theorem 1.1 traveling-wave existence | `Paper1.Theorem_1_1` | statement target | Stated as existence of actual `IsTravelingWave`/`IsMonotoneTravelingWave`; no explicit fake ansatz. |
| Theorem 1.2 traveling-wave stability | `Paper1.Theorem_1_2` | statement target | Uses weighted `L2` closeness/convergence predicates. Constants are represented abstractly by existence of `cStarStar`. |
| Theorem 1.3 traveling-wave uniqueness | `Paper1.Theorem_1_3` | statement target | Includes shared right-tail asymptotic normalization; avoids the old shift-invariant false statement. |
| Paper1 fixed-point trap-set infrastructure | `upperBarrier`, `InWaveTrapSet`, `InMonotoneWaveTrapSet`, `HasWaveUpperTailBound` | partial | Ordinary/monotone trap sets now have nonemptiness, convexity, zero/upper-barrier membership, and tail-bound-to-trap-set bridge lemmas. Generic tail-bound power estimates are proved. Closedness/compactness and Schauder-map invariance remain analytic work. |
| Traveling-wave phase-shift facts | `IsTravelingWave.shift`, `IsMonotoneTravelingWave.shift`, `shift_right_with_exp_bound` | proved | Useful infrastructure for future phase normalization and uniqueness. |
| Maximum/comparison principle | `weak_maximum_principle_linear`, `comparison_principle`, related lemmas | proved | This is real PDE infrastructure, not a paper main theorem by itself. |
| Local ODE shooting segment | `local_shooting_segment_from_E1_*` | proved | Kept as local ODE infrastructure. Removed unsupported global shooting theorem. |
| Heteroclinic to wave projection | `travelingWave_of_heteroclinic` | proved | Converts a supplied global heteroclinic into a wave; does not prove existence. |

Next accurate theorem work:

1. Make a complete inventory of every Definition/Proposition/Lemma/Theorem in
   `paper1.pdf` and add Lean statement targets for the ones used downstream.
2. Define the elliptic resolvent layer and moving-frame frozen equation needed by
   Shen's fixed-point construction.
3. Define the invariant sets and barrier predicates used for the Schauder map.
4. Replace abstract weighted/stability predicates with the exact paper
   estimates as the energy infrastructure is added.

## Paper B: boundedness/global existence on bounded domains

File header reference: `ShenWork/Paper2/Defs.lean`, arXiv `2512.14858`.

| Paper theorem area | Current Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Bounded-domain PDE solution predicate | `IsToyClassicalSolution2` | toy only | `pde_satisfied : True`; no domain, boundary condition, PDE, elliptic equation for `v`, or regularity beyond positivity. |
| Bounded-domain PDE statement interface | `Paper2.BoundedDomainData`, `Paper2.IsPaper2ClassicalSolution`, `Paper2.IsPaper2GlobalClassicalSolution` | statement target | Abstract domain/operator interface for the bounded smooth Neumann problem. It is not yet an instantiated smooth-domain theory. |
| Proposition 1.1 local existence/blow-up alternative | `Paper2.Proposition_1_1` | statement target | Stated from `paper2.pdf` against the non-toy PDE interface. |
| Theorem 1.1 negative sensitivity boundedness/global existence | `Paper2.Theorem_1_1` | statement target | Stated from `paper2.pdf`. |
| Theorem 1.2 weak nonlinear cross diffusion | `Paper2.Theorem_1_2` | statement target | Stated from `paper2.pdf`. |
| Theorem 1.3 relatively strong logistic source | `Paper2.Theorem_1_3` | statement target | Stated with a `Paper2Constants` package for the paper constants. |
| Constant equilibrium under toy definition | `cm2_constant_solution_under_current_solution_def` | proved, toy only | Useful only as a sanity check for the current toy predicate. |
| Persistence counterexample under toy definition | `persistence_property_false_under_current_solution_def` | proved, toy only | Documents why Paper3-style persistence cannot follow from the current Paper2 predicate. |

Next accurate theorem work:

1. Make a complete inventory of every Definition/Proposition/Lemma/Theorem in
   `paper2.pdf`.
2. Refine `BoundedDomainData` into an instantiated smooth bounded-domain API:
   domain, Neumann boundary, Sobolev/Hölder spaces, Laplacian, divergence,
   gradient estimates, and semigroup constants.
3. Replace packaged constants by their exact definitions once the required
   elliptic estimates are available.

## Paper C: persistence and stabilization

File header reference: `ShenWork/Paper3/Defs.lean`, arXiv `2604.02599`.

| Paper theorem area | Current Lean artifact | Status | Notes |
| --- | --- | --- | --- |
| Positive equilibrium | `equilibrium` | stated | Algebraic target only; depends on Paper2 parameters. |
| Global asymptotic stability predicate | `IsToyGloballyAsymptoticallyStable` | toy dependent | Quantifies over `IsToyGlobalClassicalSolution2`, so it inherits the toy PDE issue. |
| Non-toy bounded positive solution/stability predicates | `Paper3.PositiveGlobalBoundedSolution`, `Paper3.GloballyAsymptoticallyStableNonminimal`, `Paper3.GloballyAsymptoticallyStableMinimal` | statement target | Built on `Paper2.IsPaper2GlobalClassicalSolution`, not the toy predicate. |
| Theorem 2.1 uniform persistence | `Paper3.Theorem_2_1` | statement target | Stated from `paper3.pdf`, split into four parts. |
| Theorem 2.2 linear stability/instability | `Paper3.Theorem_2_2` | statement target | Uses spectral data and packaged paper thresholds. |
| Theorem 2.3 negative-sensitivity global stability | `Paper3.Theorem_2_3` | statement target | Stated from `paper3.pdf`. |
| Theorem 2.4 strong logistic-source global stability | `Paper3.Theorem_2_4`, `chiStrong1Formula`--`chiStrong4Formula` | partial | Stated from `paper3.pdf`; exact threshold formulas `(2.13)`, `(2.15)`--`(2.19)` are now represented, with positivity facts for all four `χ**` formulas and their auxiliary thresholds. |
| Theorem 2.5 minimal-model global stability | `Paper3.Theorem_2_5`, `minimalUpperBoundFormula`, `minimalVLowerFormula`, `GammaMinimalFormula`, `chiMinimal1Formula`, `chiMinimal2Formula` | partial | Stated from `paper3.pdf`; exact auxiliary formulas around `(2.21)`--`(2.22)` are represented, with positivity facts. |

Next accurate theorem work:

1. Make a complete inventory of every Definition/Proposition/Lemma/Theorem in
   `paper3.pdf`.
2. Replace packaged spectral/stability constants with exact definitions.
3. Add the comparison, persistence, Hopf lemma, energy, and semigroup
   dependencies before proving main theorems.

## Next phase: full-paper statement inventory

The main theorem statement layer is now only the top level.  The next phase is a
full inventory pass over `paper1.pdf`, `paper2.pdf`, and `paper3.pdf`:

1. Extract every numbered Definition, Proposition, Lemma, Corollary, Theorem,
   and named estimate into an inventory table.
2. For each item, record whether it is already `proved`, a `statement target`,
   `toy only`, or `not stated`.
3. Add Lean statement targets for all items that are dependencies of later paper
   results, even if their proofs will initially be `sorry`.
4. Then proceed section by section proving the targets and replacing abstract
   constant/operator packages by exact definitions.

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
