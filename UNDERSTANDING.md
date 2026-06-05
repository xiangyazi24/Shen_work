# UNDERSTANDING.md — Shen_work current state (updated 2026-06-05)

## Build invariant

```bash
lake build  # 8409 jobs, 0 sorry, 0 admit, 0 custom axiom
```

## Architecture: three layers

### Layer 1: PDE infrastructure (COMPLETE, 0 sorry)
All spectral, semigroup, kernel, Duhamel, resolver, energy, IBP, and
measurability infrastructure is proved. Key files:
- IntervalNeumannFullKernel, IntervalFullKernel*, IntervalDuhamel*
- IntervalResolverPositivity (O1: heat-Laplace nonneg, unconditional)
- IntervalChemFluxLipschitz (glue1+glue2: contraction estimates)
- IntervalGradDuhamelBound (Atom D: gradient sqrt-T estimates)
- IntervalLogisticLipschitz (Atom C: logistic Lipschitz, one-sided α>0)
- IntervalSourceCoefficientTimeC1 (G3: DuhamelSourceTimeC1 algebra)
- IntervalResolverSpatialC2 (G4q: resolver C² + Neumann + weight summability)

### Layer 2: Mild solution + regularity bootstrap (COMPLETE, 0 sorry)
- IntervalMildPicard: Picard iteration → GradientMildSolutionData (mild FP)
- IntervalMildSourceDecay: SourceCoeffQuadraticDecay (unconditional)
- IntervalMildToClassical: all 9 regularity conjuncts (unconditional)
- IntervalMildRegularityBootstrap: half-step restart C² + Neumann
- IntervalSemigroupNeumann: semigroup conjuncts 3/6/7/8/9 + composition
- IntervalMildPicardRegularity: Picard iterate induction (base + step)
- IntervalMildPicardLimitRegularity (G2.5): DuhamelSourceTimeC1 limit passage
- IntervalMildTimeRegularity (G4j): time DifferentiableAt from spectral
- IntervalMildTimeDerivContinuity (G4 fields): HasDerivAt + joint continuity
- IntervalMildFrontierFromSpectral (G4r): closed-slab joint continuity
- IntervalMildRegularityFrontierAssembly: u-side frontier field wiring
- IntervalResolverTimeRegularity: v-side frontier field wiring
- IntervalResolverDirectTimeRegularity (F2): resolver direct time regularity
- IntervalMildSourceDecayHelper: Sobolev chain rule / weak H² Neumann
- IntervalWeakCosineIBP: cosine coefficient decay infrastructure
- IntervalMildToLocalExistence: bridge to localExistence

### Layer 3: Paper-level theorem assembly (NEAR COMPLETE)
- IntervalDomainTheorem11Umbrella: γ≥1 umbrella (hposWit eliminated, G6)
- IntervalDomainThm11Assembly: final wiring, 15/15 frontier fields proved
- IntervalDomainStatementAssembly: Paper2 Thm 1.1/1.2/1.3 targets
- Paper1/Statements, Paper2/Statements, Paper3/Statements

## G0–G7 + G2.5 status (all committed, 0 sorry)

| Gap | Description | Status | Commits |
|-----|-------------|--------|---------|
| G0 | Continuous u₀ in initialAdmissible | ✓ DONE | 5343c18 |
| G1a | One-sided logistic Lipschitz α>0 | ✓ DONE | 5f94ba0 |
| G2a+G2b | Spatial IBP for Duhamel source | ✓ DONE | 5bf3fb5 |
| G2.5 | DuhamelSourceTimeC1 limit passage | ✓ DONE | e5da4dc |
| G3 | Total-source DuhamelSourceTimeC1 | ✓ DONE | b2b4b66+ |
| G4a–G4i | Spectral time derivatives (ODE→series) | ✓ DONE | 355f14d–356dd4e |
| G4j | Time DifferentiableAt of mild solution | ✓ DONE | e138bfa |
| G4k–G4m | Joint continuity (Duhamel+hom+restart) | ✓ DONE | cfa96ab–665367d |
| G4n–G4p | Spectral PDE identity + Laplacian | ✓ DONE | a1ce482–c7db735 |
| G4q | Resolver spatial C² + weight summability | ✓ DONE | 7c0dd7b |
| G4r | Closed-slab joint continuity | ✓ DONE | 8e8b1ae |
| G5 | Uniform S(t)u₀→u₀ for continuous u₀ | ✓ DONE | 809f1ac |
| G6 | PID-gate L² chain + eliminate hposWit | ✓ DONE | 25da5b3+2d8cdcf |
| G7 | ReachableArbitrarilyLong from hlocal+hUniform | ✓ DONE | 625fa56 |
| F2 | Resolver direct time regularity | ✓ DONE | a32f923 |

## Remaining frontier for unconditional Paper 2 Theorem 1.1

### Proved chain (axiom-clean)
```
Picard FP → iterate C² induction → DuhamelSourceTimeC1 limit (G2.5)
→ regularity bootstrap → localExistence
→ γ≥1 umbrella (no hposWit, G6) → L² uniqueness (PID-gated)
→ δ-iteration (G7) → Theorem_1_1
```

### Assembly theorem
```lean
paper2_theorem_1_1_of_frontier:
  hUniform + hMildLocal → Theorem_1_1 intervalDomain p
```

### Regularity frontier data: 15/15 fields proved
- 12 unconditional (u-side time + spatial, v-side spatial, sup-norm)
- 3 from ResolverHasSpectralAgreement (v-side time, constructible from F2)

### Two genuine remaining hypotheses

**F1: IntervalDomainUniformLocalExistence** (textbook continuation δ(M))
- For every M>0, ∃ δ>0 such that any classical solution with |u₀|≤M extends by δ
- Standard PDE (Henry/Amann); requires restart-before-end + overlap glue
- Estimated ~200 lines

**F2 (partially resolved): DuhamelSourceTimeC1 for the Picard limit**
- G2.5 reduces to uniform convergence of iterate source coefficient derivatives
- F2 direct resolver regularity proved (IntervalResolverDirectTimeRegularity)
- Remaining: instantiate the uniform convergence hypothesis from Picard data
- Estimated ~150 lines

## Other paper theorems

### Gap 2: Paper1 Theorem 1.1 (traveling wave existence)
Requires Schauder fixed point on the whole line (not interval domain).
Mathematically hardest gap.

### Gap 3: Paper1 Thm 1.2/1.3 (stability/uniqueness)
Depends on Gap 2.

### Gap 4: Paper2/Paper3 semigroup estimates (Lemma 2.1-2.4)
Mechanical but large. Zero-data branches proved.

## Priority order
1. F1 + F2 instantiation → Paper2 Thm 1.1 unconditional (~350 lines)
2. Gap 4 (semigroup estimates): mechanical
3. Gap 2 (whole-line Schauder): mathematically hardest
4. Gap 3 (weighted stability): depends on Gap 2

## Build
On uisai1: `PATH=$HOME/.elan/bin:$PATH lake build`
