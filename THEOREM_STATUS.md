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
| Theorem 1.2 traveling-wave stability | `Paper1.Theorem_1_2`, `stabilitySpeedBaseline` | statement target | Uses weighted `L2` closeness/convergence predicates; the existential `cStarStar` now carries the paper's explicit lower bound `1 + |χ|^(1/6) + (1+|χ|^(1/6))⁻¹`, with positivity and `> 1` projections proved. |
| Theorem 1.3 traveling-wave uniqueness | `Paper1.Theorem_1_3`, `stabilitySpeedBaseline` | statement target | Includes shared right-tail asymptotic normalization and the same explicit lower bound on `cStarStar`; avoids the old shift-invariant false statement. |
| Paper1 fixed-point trap-set infrastructure | `expDecay`, `upperBarrier`, `WaveTrapSet`, `MonotoneWaveTrapSet`, `LocallyUniformConverges`, `FrozenAuxiliarySolutionFrom`, `FrozenAuxiliaryLimitOutput`, `FrozenWaveMapConstruction`, `HasWaveUpperTailBound` | partial | Ordinary/monotone trap sets now have names, nonemptiness, convexity, monotonicity in `M`, zero/upper-barrier membership, and tail-bound-to-trap-set bridge lemmas. Smooth exponential branch positivity, monotonicity, limits, derivative identities, linear-part identities, generic power estimates, and the Section 4 frozen auxiliary parabolic limit-map/Schauder statement layer are represented; generic and negative/positive fixed-limit projection lemmas are proved. Closedness/compactness and Schauder-map invariance remain analytic work. |
| Traveling-wave phase-shift facts | `IsTravelingWave.shift`, `IsMonotoneTravelingWave.shift`, `shift_right_with_exp_bound` | proved | Useful infrastructure for future phase normalization and uniqueness. |
| Maximum/comparison principle | `weak_maximum_principle_linear`, `weak_maximum_principle_linear_Ico`, `comparison_principle`, `comparison_principle_Ico`, related lemmas | proved | This is real PDE infrastructure, not a paper main theorem by itself; local time-horizon restriction for linear subsolutions and open-terminal corollaries are also proved. |
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
| Theorem 1.1 negative sensitivity boundedness/global existence | `Paper2.Theorem_1_1` | statement target | Stated from `paper2.pdf`; finite-horizon boundedness is separated from the `m ≥ 1` global-existence conclusion. |
| Theorem 1.2 weak nonlinear cross diffusion | `Paper2.Theorem_1_2` | statement target | Stated from `paper2.pdf`; the `0 < m < 1` branch uses boundedness before `Tmax`, the `m = 1` branch gives global boundedness, and both keep the initial trace. |
| Theorem 1.3 relatively strong logistic source | `Paper2.Theorem_1_3` | statement target | Stated with a `Paper2Constants` package for the paper constants; boundedness and `m ≥ 1` global existence are represented separately and both keep the initial trace. |
| Lemma 2.6 abstract bootstrap | `Paper2.Lemma_2_6`, `LpBootstrapEnergyInequality` | statement target | Stated with dimension separated from domain volume and with the differential energy inequality retained; basic bootstrap-hypothesis projections are proved. |
| Corollary 2.1 cross-term bootstrap | `Paper2.Corollary_2_1`, `CrossDiffusionBootstrapEstimate` | statement target | Stated with the paper's small-`ε` chemotaxis cross-term estimate before deriving all `L^p` bounds; pointwise estimate projection is proved. |
| Lemma 2.7 damping inequality | `Paper2.Lemma_2_7` | statement target | Stated as the paper's integral differential inequality with `d/dt ∫u^p` and the two damping powers, not as a pointwise scalar inequality. |
| Proposition 2.2 gradient estimate | `Paper2.Proposition_2_2`, `WeightedGradientEstimate` | statement target | Stated as the paper's weighted `∇v` estimate in terms of `u^(γp)`, not as an `L^p(u)` boundedness theorem; projection lemmas for both inequalities are proved. |
| Proposition 2.3 signal estimate | `Paper2.Proposition_2_3`, `WeightedSignalEstimate` | statement target | Stated as the paper's weighted `v` estimate with the small `ε` term and integral-power remainder; the pointwise-in-time projection lemma is proved. |
| Proposition 2.4 mass comparison | `Paper2.Proposition_2_4`, `MassConservedBefore`, `LogisticMassUpperBoundBefore` | statement target | Stated as the paper's mass conservation in the minimal case and logistic mass upper bound in the nonminimal case; pointwise projection lemmas are proved. |
| Proposition 2.5 boundedness criterion | `Paper2.Proposition_2_5`, `LpPowerBoundedBefore` | statement target | Stated as a finite-horizon `L^p`-to-`L∞` boundedness criterion, matching its role before the blow-up alternative; boundedness projection lemmas are proved. |
| Lemma 3.1 upper-envelope monotonicity | `Paper2.Lemma_3_1`, `SupNormNonincreasingOn` | statement target | Corrected from a false all-time `supNorm ≤ initial supNorm` statement to the paper's conditional upper-envelope monotonicity result. |
| Lemma 4.1 interpolation estimate | `Paper2.Lemma_4_1`, `LpMassGradientInterpolationEstimate` | statement target | Corrected to the paper's Ehrling/interpolation inequality `∫u^p ≤ ε∫u^(p-2)|∇u|² + C(∫u)^p`; pointwise estimate projection is proved. |
| Constant equilibrium under toy definition | `cm2_constant_solution_under_current_solution_def` | proved, toy only | Useful only as a sanity check for the current toy predicate. |
| Persistence counterexample under toy definition | `persistence_property_false_under_current_solution_def` | proved, toy only | Documents why Paper3-style persistence cannot follow from the current Paper2 predicate. |

Next accurate theorem work:

1. Audit exact statement fidelity for the numbered Paper2 items already listed
   in `PAPER_INVENTORY.md`, especially the abstract `BoundedDomainData` fields
   and the packaged constants in `Paper2Constants`.
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
| Theorem 2.1 uniform persistence | `Paper3.Theorem_2_1`, `minimalVLowerFormula` | statement target | Stated from `paper3.pdf`, split into four parts; the minimal-model `v` lower bound uses the explicit Gaussian-lower-bound formula from (2.9), and its positivity projection is proved. |
| Theorem 2.2 linear stability/instability | `Paper3.Theorem_2_2` | statement target | Uses spectral data and packaged paper thresholds; local exponential stability is stated with a small `supNorm` perturbation and, in the minimal case, the paper's mass constraint. |
| Theorem 2.3 negative-sensitivity global stability | `Paper3.Theorem_2_3` | statement target | Stated from `paper3.pdf`; exponential constants are quantified uniformly over the relevant solution class. |
| Theorem 2.4 strong logistic-source global stability | `Paper3.Theorem_2_4`, `chiStrong1Formula`--`chiStrong4Formula` | partial | Stated from `paper3.pdf`; exact threshold formulas `(2.13)`, `(2.15)`--`(2.19)` are now represented, with positivity facts for all four `χ**` formulas and their auxiliary thresholds; exponential constants are uniform over the solution class. |
| Theorem 2.5 minimal-model global stability | `Paper3.Theorem_2_5`, `minimalUpperBoundFormula`, `minimalVLowerFormula`, `GammaMinimalFormula`, `chiMinimal1Formula`, `chiMinimal2Formula` | partial | Stated from `paper3.pdf`; exact auxiliary formulas around `(2.21)`--`(2.22)` are represented, with positivity facts; exponential constants are uniform over mass-constrained solutions. |
| Lemma 3.3 initial-data continuity | `Paper3.Lemma_3_3`, `InitialContinuityConclusion` | statement target | Corrected from an underdetermined arbitrary-function statement to a comparison of two classical solutions at the same positive time `T₀`. |
| Lemma 3.4 upper-envelope monotonicity | `Paper3.Lemma_3_4`, `UpperEnvelopeMonotonicityConclusion` | statement target | Corrected to the paper's nonincreasing direction: if `0 < t₁ ≤ t₂ ≤ t₀`, then the upper envelope at `t₂` is bounded by that at `t₁`; nonminimal/minimal projection lemmas are proved. |

Next accurate theorem work:

1. Audit exact statement fidelity for the numbered Paper3 items already listed
   in `PAPER_INVENTORY.md`, especially Definition 2.1, Theorems 2.1--2.5,
   and Appendix Lemmas A.1--A.8.
2. Replace packaged spectral/stability constants with exact definitions.
3. Add the comparison, persistence, Hopf lemma, energy, and semigroup
   dependencies before proving main theorems.

## Next phase: full-paper statement inventory

The main theorem statement layer is no longer only the top level.  The initial
numbered-item inventory for Paper2/Paper3 is in `PAPER_INVENTORY.md`; Paper1
still needs a careful full-paper pass for the statements used in the fixed-point
and stability proofs.  The next phase is:

1. Finish the Paper1 numbered-item/named-estimate inventory beyond the current
   top-level and Lemma 2/4/5 rows.
2. For each item, record whether it is already `proved`, a `statement target`,
   `toy only`, or `not stated`.
3. Add or refine Lean statement targets for all items that are dependencies of later paper
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
