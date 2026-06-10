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

## 2026-06-06 night update — hQuant driven to a single shared residual

The "Two genuine remaining hypotheses" section above is STALE. Current map:

### hQuant (uniform δ(M) local existence) — Session B campaign, all green/axiom-clean
- **χ₀ = 0 (cone route, COMPLETE modulo one hypothesis):**
  `ConeQuantBridge.quantitativeLocalExistence_chiZero` — Picard contraction
  AND positivity proved (exponential cone invariance, uniform δ(p,M),
  no inf-threshold). Residual: `PicardLimitRestartFrontier` only.
  End-to-end: `paper2_theorem_1_1_chiZero_of_frontier` (+ hlocal).
- **General χ₀ ≤ 0 (threshold route, conditional):**
  `QuantFromThreshold` + `ThresholdQuantBridge`: hQuant ⟸ proved-δ(M,c)
  threshold Picard + `ClassicalMinPersistence` (min principle, open) +
  `PicardLimitRestartFrontier` + hlocal.
- **Key new infrastructure** (axiom-clean): Chapman–Kolmogorov
  `IntervalSemigroupComposition` (S(s)S(t)=S(s+t) via S1 spectral identity),
  cone atoms (mono/Duhamel-eval/kernel strict positivity), generic
  `gradientMildSolutionData_initialApproach` (hInitialApproach is no longer
  part of any per-datum frontier for continuous data).

### Unified residual
`PicardLimitRestartFrontier p` (ConeQuantBridge): restart source data +
frontier core for every packaged D with `D.u = picardLimit p u₀ D.T`.
One S-construction discharge (Session A's M-line, in flight) closes
hQuant(χ₀=0), the threshold route's Picard half, and hlocal(χ₀=0).

## 2026-06-09 — Thm 1.1 chain compilation green

### Chain status (ContinuousExtension → … → Provider)
Full 7-file chain compiles end-to-end on uisai2 (lake build green):
```
IntervalDomainContinuousExtension (0 sorry)
→ IntervalPicardLimitRestartWeak (0 sorry, eigenvalue summability proved)
→ IntervalDomainConstExtendAdapter (1 sorry: adapter body)
→ IntervalDomainMildLocalChi0 (1 sorry: restartData_of_inputs)
→ IntervalDomainThm11ChiZeroFinal (0 sorry)
→ IntervalDomainLedgerSweep (2 sorry: time-quantified → global adapters)
→ IntervalDomainThm11ChiZeroCoreProvider (17 sorry: analytic estimates)
```

### Key fix: namespace opens for `intervalLogisticSource` / `cosineMode`
Six files needed `open ShenWork.IntervalDomainExistence (intervalLogisticSource)`
and `open ShenWork.CosineSpectrum (cosineMode)`. Without these, all definitions
using these names silently became autoImplicit variables, cascading "Function
expected" errors.

### RestartWeak eigenvalue summability (NEW, 0 sorry)
`summable_eigenvalue_mul_abs_limitCoeff_weak`: proved via FTC envelope
computation + triangle split + `Summable.of_nonneg_of_le`. The proof handles:
`abs_add` → `abs_add_le` rename, `gcongr` → explicit `add_le_add` /
`mul_le_mul_of_nonneg_left`, `continuous_const` domain inference in tactic mode,
`-(t-s)*λ_k` parse order, `neg_zero` in simp set.

### Provider sorry inventory (17 items)
- G1, G2 — gradient/Hessian bound VALUES
- hG1t, hG2t — gradient/Hessian bound PROOFS
- adott family (5) + adotS family (5) — K1 time-C¹ data
- hpde_u, Hvsrc, Hvpos — PDE/resolver residuals
- hsrc0 (×2 in final wiring) — DuhamelSourceL1Cont

### LedgerSweep interface gap — RESOLVED 2026-06-09 night (horizon localization)
See HANDOFF/horizon-localization-design.md + HANDOFF/horizon-retype-status.md.
Landed (all green, 8521 jobs): C¹ soft clamp (IntervalTimeSoftClamp) +
clamped-witness TimeC1 producer (IntervalDomainClampedSourceRepresentation) +
weak-chain horizon retype (DuhamelSourceL1ContOn) + Hu_of_restart_localized
(0 sorry) + ledger V2 (per-compact hG1t/hG2t/hMdott, (0,T) K1, 5 shifted-K1
fields deleted, hsrc0 field) + K2 gradient producers wired + Hvpos proved
(mildChemicalConcentration_pos) + hpde_u producer (IntervalDomainPdeUProducer).

Sorry inventory after the campaign (10, all satisfiable types):
- Provider 7: hsrc0F + K1 quadruple (F2: iterate-derivative uniform
  convergence into duhamelSourceTimeC1_of_uniform_limit), hpde_u (data
  wiring), Hvsrc (power-source analogue)
- Hu_of_reduced 1 (subtype-continuity variant of the localized restart)
- restartData_of_inputs 1 + hasRestartData_of_subtypeCont 1 (restart packaging)
