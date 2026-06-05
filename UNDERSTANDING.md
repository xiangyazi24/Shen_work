# UNDERSTANDING.md — Shen_work current state (updated 2026-06-04)

## Build invariant

```bash
lake build  # 8395+ jobs, 0 sorry, 0 admit, 0 custom axiom
```

## Architecture: three layers

### Layer 1: PDE infrastructure (COMPLETE, 0 sorry)
All spectral, semigroup, kernel, Duhamel, resolver, energy, IBP, and
measurability infrastructure is proved. Key files:
- IntervalNeumannFullKernel, IntervalFullKernel*, IntervalDuhamel*
- IntervalResolverPositivity (O1: heat-Laplace nonneg, unconditional)
- IntervalChemFluxLipschitz (glue1+glue2: contraction estimates)
- IntervalGradDuhamelBound (Atom D: gradient sqrt-T estimates)
- IntervalLogisticLipschitz (Atom C: logistic Lipschitz)

### Layer 2: Mild solution + regularity bootstrap (COMPLETE, 0 sorry)
- IntervalMildPicard: Picard iteration → GradientMildSolutionData (mild FP)
- IntervalMildSourceDecay: SourceCoeffQuadraticDecay (unconditional)
- IntervalMildToClassical: all 9 regularity conjuncts (unconditional)
- IntervalMildRegularityBootstrap: half-step restart C² + Neumann
- IntervalSemigroupNeumann: semigroup conjuncts 3/6/7/8/9 + composition
- IntervalMildPicardRegularity: Picard iterate induction (base + step)
- IntervalMildSourceDecayHelper: Sobolev chain rule / weak H² Neumann
- IntervalWeakCosineIBP: cosine coefficient decay infrastructure
- IntervalMildToLocalExistence: bridge to localExistence

### Layer 3: Paper-level theorem assembly (PARTIAL)
- Paper1/Statements: paper1_main_results (Thm1.1∧1.2∧1.3 from hypotheses)
- Paper2/Statements: paper2_main_results (from solution branch data)
- Paper3/Statements: paper3 stability/compactness/persistence assemblies
- IntervalDomainTheorem11Umbrella: Paper2 Thm1.1 wired
- IntervalDomainStatementAssembly: Paper3 assembly

## Remaining gaps to unconditional paper theorems

### Gap 1: Picard limit regularity (CLOSEST TO CLOSURE)
The Picard induction base case and step are proved
(IntervalMildPicardRegularity.lean). What remains:
- Prove DuhamelSourceTimeC1 for the Picard LIMIT (not just iterates)
- This requires: uniform convergence of iterate coefficients preserves
  the ℓ¹ summability + time-C¹ properties in the limit
- Once done: unconditional HasRestartCosineRepresentations for the mild
  solution → unconditional RegularityBootstrap → unconditional
  localExistence → gluing (already proved axiom-clean) → Paper2 Thm 1.1

### Gap 2: Paper1 Theorem 1.1 (traveling wave existence)
Requires Schauder fixed point on the whole line (not interval domain).
The fixed-point-construction bridge reduces it to: frozen-profile
stationarity + endpoint limits + monotonicity/tail data + upper barrier.
The Schauder proof producing these profile fields is the open work.

### Gap 3: Paper1 Thm 1.2/1.3 (stability/uniqueness)
Bridge theorems reduce to: per-instance weighted stability + Cauchy
uniqueness + resolvent identification. The general near-data weighted
stability proof is the open work.

### Gap 4: Paper2/Paper3 semigroup estimates (Lemma 2.1-2.4)
Abstract bounded-domain package fields remain externalized. Zero-data
branches are proved; general branches need the concrete interval-domain
semigroup theory instantiated.

## Priority order
1. Gap 1 (Picard limit → Paper2 Thm 1.1): ~2-3 lemmas away
2. Gap 4 (semigroup estimates): mechanical but large
3. Gap 2 (whole-line Schauder): mathematically hardest
4. Gap 3 (weighted stability): depends on Gap 2

## Collaboration model
- Opus 4.6: architect (route design, scaffold, mathematical analysis)
- Codex GPT-5.5: builder (sorry closure, Lean code, build-fix cycles)
- ChatGPT Pro: mathematical audit (Sobolev composition verified R1)

## Build
On uisai1: `PATH=$HOME/.elan/bin:$PATH lake build`
