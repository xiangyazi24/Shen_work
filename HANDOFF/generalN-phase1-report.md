# General-N Phase 1 Report

Date: 2026-07-19  
Toolchain: Lean 4.29.1 / the vendored Mathlib in this repository

## Result and central caveat

Phase 1 now has two concrete modules:

- `ShenWork/PDE/EuclideanDomainData.lean`
- `ShenWork/PDE/EuclideanDomainBasic.lean`

They construct a `Paper2.BoundedDomainData` value from a bounded open set
`Ω : Set (EuclideanSpace ℝ (Fin N))`, positive Lebesgue volume, and a bundled
unit vector field on `frontier Ω`.  Both modules build without `sorry` or new
axioms.

The central audit result is that constructing this value does **not** by itself
transfer the substantive Paper2/Paper3 headlines.  The current
`BoundedDomainData` (`ShenWork/PDE/BoundedDomainData.lean:13-28`) is a record of
raw functions and predicates; it has no laws saying that its integral is
linear, that its Laplacian is compatible with its gradient, that its normal
derivative is outward, or that Green's formula holds.  The statement-assembly
files consequently assume branch-data records which already contain the
desired analytic conclusions.  This distinction is essential when describing
what is immediate.

## G1: concrete domain data

### Why `Point = ↥(closure Ω)`

The point type is the closure, not the open subtype.

1. The existing interval model uses `Icc 0 1`, with `Ioo 0 1` as `inside` and
   the endpoints as `boundary` (`ShenWork/PDE/IntervalDomain.lean`, declarations
   `intervalDomainPoint` and `intervalDomain`).
2. `IsPaper2ClassicalSolution` asks for positivity at every `D.Point` and for a
   Neumann condition on `D.boundary`
   (`ShenWork/Paper2/Statements.lean:70-100`).
3. If `Point` were `↥Ω` for open `Ω`, `frontier Ω` would have no points in the
   subtype, so the Neumann condition would become vacuous.

The implementation therefore uses

```lean
Point    := ↥(closure Ω)
inside   := {x | x.1 ∈ Ω}
boundary := {x | x.1 ∈ frontier Ω}
```

while integration remains Lebesgue integration restricted to `Ω`.

### Field inventory

| `BoundedDomainData` field | Concrete implementation | Phase-1 status |
|---|---|---|
| `Point` | `↥(closure Ω)` | Constructed; `closure Ω` is proved compact. |
| `inside` | preimage of `Ω` under subtype coercion | Constructed and proved open. |
| `boundary` | preimage of `frontier Ω` | Constructed and proved closed. |
| `volume` | `(volume Ω).toReal` | Positive by input; finite from boundedness. |
| `integral` | integral of the zero extension against `volume.restrict Ω` | Constructed; basic laws are in G2. |
| `supNorm` | `sSup (range fun x => |f x|)` | Constructed.  No finiteness law is claimed for an arbitrary, possibly discontinuous `f`. |
| `infValue` | `sInf (range f)` | Constructed with the same qualification. |
| `gradNorm` | norm of the ambient Fréchet derivative of the zero extension | Constructed.  Its intended interior meaning requires differentiability of an ambient representative. |
| `timeDeriv` | scalar `deriv` at fixed `x` | Constructed. |
| `laplacian` | Mathlib's whole-space `Δ` applied to the zero extension | Constructed. |
| `chemotaxisDiv` | coordinate divergence of the paper-faithful flux | Constructed. |
| `crossDiffusionEnergyTerm` | restricted Lebesgue integral of the absolute cross term | Constructed. |
| `normalDeriv` | `fderivWithin` on `closure Ω`, applied to the bundled boundary vector | Type-correct, but geometric outwardness and trace compatibility are **not** proved. |
| `initialAdmissible` | bounded range plus continuity on the closed point space | Constructed as a predicate; existence is not asserted. |
| `classicalRegularity` | interior spatial `C²` plus pointwise time `C¹` | Constructed as a predicate; boundary regularity and existence are not asserted. |

The extra input `boundaryNormal` has only the law `‖boundaryNormal x hx‖ = 1`.
It is deliberately not called an outward normal in any theorem.  A unit vector
chosen at each frontier point is not a substitute for a smooth-boundary
normal field.

Thus all record fields are filled, but the differential and boundary fields
are definitions, not an analytic compatibility theorem.  In particular, the
zero extension is locally harmless at an interior point, whereas its ambient
derivative at the boundary is not automatically the physical boundary
derivative.

### Structural facts discharged

`EuclideanDomainData.lean` proves:

- exact membership characterizations for `inside` and `boundary`;
- openness of `inside` and closedness of `boundary`;
- compactness of `closure Ω` from finite dimensionality and boundedness;
- positivity of the abstract volume;
- finiteness of `volume Ω` and of `domainMeasure Set.univ`;
- an `IsFiniteMeasure domainMeasure` instance;
- unit norm of `normalVector` on the boundary.

It does not prove smoothness of `frontier Ω`, outwardness or regularity of the
normal, existence of traces, Green identities, or any Neumann PDE result.

## G2: measure and integral laws

`EuclideanDomainBasic.lean` proves the following facts for the concrete
restricted measure:

- evaluation of the zero extension on `closure Ω`, on `Ω`, and outside the
  closure;
- compatibility of the extension with zero, addition, negation, subtraction,
  and multiplication by a constant;
- total restricted measure and its real value;
- integrability of constants;
- integral of zero and
  `integral (fun _ => c) = euclideanDomain.volume * c`;
- addition, negation, subtraction, and constant-multiplication laws;
- monotonicity from a pointwise inequality on `inside`;
- nonnegativity from either an inside-only or an all-points hypothesis.

Addition, subtraction, and monotonicity correctly retain integrability
hypotheses.  Mathlib's Bochner integral is defined to be zero for a
non-integrable function, so unconditional versions of those laws would be
false.

No new Cauchy--Schwarz or Hölder wrapper was added.  The audit found no current
Paper2/Paper3 abstract headline consumer of such a `BoundedDomainData` law.
When a concrete proof needs it, Mathlib already provides
`MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` for `MemLp` functions; the
Cauchy--Schwarz specialization uses `Real.HolderConjugate.two_two`.

The all-points nonnegativity theorem can immediately discharge the explicit
`hintegral_nonneg` argument in these dimension-independent Paper3 utilities:

- `chemotaxisEntropyFunctional_nonneg_of_integral_nonneg`;
- `chemotaxisThetaDissipation_nonneg_of_integral_nonneg`;
- `chemotaxisSignalEnergy_nonneg_of_integral_nonneg`;
- `chemotaxisSignalGradientDissipation_nonneg_of_integral_nonneg`.

These are useful low-level transfers, but they are not the Paper3 headline
stability or persistence results.

## What becomes available immediately

### Substantive theorem already generic

The only substantive named Paper2/Paper3 theorem found which closes for every
`BoundedDomainData` without a branch-data package is
`Paper3.Lemma_3_1_proved`
(`ShenWork/Paper3/Statements.lean:11069`).  It proves `Lemma_3_1 D p` by
unpacking the regularity already included in `PositiveGlobalBoundedSolution`.
It therefore specializes immediately to `D.euclideanDomain`.

Generic accessors for `IsPaper2ClassicalSolution` and
`PositiveGlobalBoundedSolution` also specialize immediately.  They merely
project hypotheses already stored in those predicates.

Paper2's `Lemma_2_1_zero_data` through `Lemma_2_4_zero_data`, and Paper3's
zero-data Appendix lemmas, are explicitly documented in the source as
impostor/vacuous interfaces (zero semigroup and zero norms).  They are not
counted as General-N transfers.

### No substantive Paper2 headline is immediate

This is not just an absence of a proof search result.  The repository contains
counterexamples to unrestricted abstract versions, including:

- `not_forall_Lemma_2_6`
  (`ShenWork/Paper2/Statements.lean:2706`);
- `not_forall_Proposition_2_2`
  (`ShenWork/Paper2/Statements.lean:2880`);
- `not_forall_Theorem_1_1`, `not_forall_Theorem_1_2`, and
  `not_forall_Theorem_1_3`
  (`ShenWork/Paper2/Statements.lean:4506,4557,4616`).

The instance-facing assembly wrappers do not change this conclusion.
`Paper2BootstrapEstimateBranchData`
(`ShenWork/Paper2/Statements.lean:4882`) already contains Lemmas 2.6--2.7 and
Propositions 2.2--2.5 as fields.  `Paper2MainSolutionBranchData`
(`ShenWork/Paper2/Statements.lean:5208`) similarly carries the main solution
conclusions.  The wrappers in `Paper2/StatementAssembly.lean` unpack those
records; the Euclidean instance does not construct them.

## Evidence-based cost map

### Paper2

| Target | What G1/G2 provide | Remaining cost |
|---|---|---|
| Lemmas 2.1--2.4 | Domain, finite measure, typed Laplacian | A real Neumann heat semigroup and its kernel/smoothing bounds.  `SemigroupEstimateData` is currently arbitrary raw data, not constructed from `Ω`. |
| Lemma 2.6 | Integral algebra and a concrete gradient norm | Energy/chain-rule identities, no-flux integration by parts, mass control, and general-N Sobolev/Gagliardo--Nirenberg/Moser estimates.  The current original statement also has the documented terminal-window/initial-exponent defects in `IntervalDomainLem26ConcreteTerminal.lean`. |
| Proposition 2.2 | Integral monotonicity/linearity | Green's identity, Neumann elliptic regularity, a positive resolvent/maximum principle, and the weighted/log-gradient estimate.  The interval proof uses endpoint Neumann conditions and one-dimensional integration by parts in `IntervalDomainWeightedGradientEstimate.lean`. |
| Propositions 2.3--2.4 | Integral algebra | Signal-energy identities and the mass derivative/comparison principle.  Proposition 2.4 specifically needs integration of the PDE and cancellation of the boundary flux. |
| Proposition 2.5 | Finite volume and integral laws | General-N Sobolev/Gagliardo--Nirenberg and Moser iteration; the existing route is one-dimensional Agmon/Moser. |
| Proposition 1.1 | A regularity predicate only | Local classical existence, initial trace, uniqueness/positivity as required by the encoding, and the blow-up alternative. |
| Theorems 1.1--1.3 | A domain value on which the targets can be stated | The preceding estimates plus local-to-global continuation and long-time analysis.  Their current generic proofs are conditional assembly from already-complete branch data. |

### Paper3

| Target | Immediate part | Remaining cost |
|---|---|---|
| Propositions 1.2--1.4 | Target statements instantiate | They depend on the Paper2 main estimates/solutions and do not follow from the domain record. |
| Theorem 2.1 | Integral nonnegativity utilities transfer | Positive-time Neumann heat-kernel lower bounds, elliptic comparison, mass identities, and the minimal-signal floor.  Parts 1--3 also have unrestricted counterexamples at `Paper3/Statements.lean:5294,5387,5496`.  The original interval statement has separate reaction-guard and zero-time-mass obstructions; only the corrected interval headline is closed. |
| Theorem 2.2 | Some finite-dimensional spectral algebra is already generic once `HasNeumannSpectrum S` is assumed | A domain-linked Neumann Laplacian, compact resolvent, eigenbasis, and proof that `S` is the spectrum of this `Ω`.  Current `HasNeumannSpectrum` (`Paper3/Statements.lean:287`) does not mention `D`, so it supplies no such link. |
| Theorems 2.3--2.5 | Target statements instantiate | Nonlinear stability, regularity, semigroup, and decay estimates.  `Paper3Stability23To25BranchData` carries the completed branches rather than deriving them. |
| Lemma 3.1 | **Immediate:** `Lemma_3_1_proved` | Nothing beyond the regularity bundled in a positive global bounded solution. |
| Lemmas 3.2--3.5 and 7.1 | Target statements instantiate | Time-translate compactness, parabolic regularization, envelope/minimal-bound results, and Neumann resolvent facts. |

`Paper3MainlineData` (`ShenWork/Paper3/StatementAssembly.lean:601`) confirms
the frontier: it requires five packages for propositions, persistence,
Theorem 2.2, compactness/regularization, and stability.  G1/G2 constructs none
of these packages.

### The “structural fields only” category

At the headline level this category is currently empty.  The concrete module
has discharged volume positivity, compactness, finite measure, and the basic
integral laws, but the abstract `BoundedDomainData` does not expose those laws,
and the headline assembly does not ask for them individually.  It asks for
records containing complete analytic conclusions.

There is a small, genuine structural/wiring layer below the headlines:

- the four Paper3 nonnegativity utilities listed above now accept the concrete
  integral theorem directly;
- constant integrals can discharge static mass calculations;
- future abstract proofs could consume these facts through a separate law
  structure or explicit hypotheses.

Adding such a law layer would improve reuse, but it would not remove the
boundary, elliptic, semigroup, or regularity obligations in the tables above.

## Exact missing boundary/PDE API

The following are the concrete missing interfaces needed to turn the typed
operators into the paper's Neumann operators.  Names in code font below are
descriptive signatures that do not currently exist in the vendored Mathlib.

### Smooth domain and trace layer

1. A predicate/structure such as `SmoothBoundedDomain Ω` connecting a concrete
   subset of Euclidean space and `closure Ω` to a smooth manifold with boundary.
2. An `outwardUnitNormal Ω : frontier Ω → E` with unit length, smoothness, and
   a theorem characterizing **outwardness**.
3. A boundary/surface measure `surfaceMeasure Ω`.
4. A trace operator `trace Ω f` with continuity and compatibility with smooth
   restrictions.
5. A boundary normal derivative tied to the trace and outward normal, not just
   an arbitrary directional derivative.

Mathlib has the category-level manifold notions `ModelWithCorners.boundary`
and `ModelWithCorners.IsBoundaryPoint`, but
`Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean:64-70` still lists
“boundary is a submanifold” and finite-dimensional boundary measure zero as
TODOs.  There is no bridge from a smooth Euclidean subset to the five objects
above.

### Divergence and Green identities on an arbitrary smooth `Ω`

The required statements have the shapes

```text
∫ x in Ω, div F x
  = ∫ x ∂(surfaceMeasure Ω), ⟪F x, outwardUnitNormal Ω x⟫

∫ x in Ω, g x * Δ f x
  = - ∫ x in Ω, ⟪∇g x, ∇f x⟫
    + ∫ x ∂(surfaceMeasure Ω), trace g x * normalDeriv f x
```

together with corollaries eliminating the boundary term under homogeneous
Neumann/no-flux hypotheses.

The current Mathlib divergence theorems are box theorems:

- `BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt`;
- `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`;
- `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`.

They live in `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean` and express
the boundary integral as signed integrals over rectangular faces.  They do not
provide an arbitrary-smooth-domain theorem, an outward normal, or a surface
trace.  Mathlib does provide the whole-space `Laplacian.laplacian` and
`InnerProductSpace.laplacianWithin`; the latter's coordinate formula requires
`UniqueDiffOn`.  Those differential definitions do not supply Green's formula.

### Neumann elliptic and spectral layer

The exact missing constructions/results are:

- a closed, self-adjoint `NeumannLaplacian Ω` on `L²(Ω)` with its domain
  characterized by a trace-level Neumann condition;
- existence/uniqueness and positivity of the Neumann elliptic resolvent;
- weak/strong maximum principles and the resolver gradient/log-gradient
  estimates used by Proposition 2.2;
- compact resolvent, discrete eigenvalues, and a complete orthonormal
  eigenbasis linked to `Ω`;
- `neumannHeatSemigroup Ω`, a heat kernel, mass preservation, positivity,
  positive-time lower bounds, and `Lᵖ → Lᑫ`/gradient smoothing estimates.

Repository-wide searches of this Mathlib checkout found abstract compact
self-adjoint spectral infrastructure, but no construction connecting it to an
elliptic Neumann operator on a bounded Euclidean domain.

### Further genuinely analytic costs

Even after the boundary API exists, the main headlines still require
domain-dependent Sobolev/Gagliardo--Nirenberg inequalities, Moser iteration,
elliptic/parabolic regularity, compactness, maximum principles, local
well-posedness, and continuation.  These are not structural record fields and
should not be described as automatic consequences of the General-N instance.

## Bottom line

G1/G2 complete the honest topology/measure instance and provide explicit
whole-space differential placeholders with a non-vacuous boundary point type.
They also isolate the first reusable integral laws.  The next load-bearing
step is not another `BoundedDomainData` instantiation: it is a smooth-domain
trace/Green layer, followed by a domain-linked Neumann elliptic/semigroup
theory.  Until those exist, only `Paper3.Lemma_3_1_proved` and low-level
algebraic/measure utilities transfer without already assuming the desired
headline conclusions.
