# ShenWork Closure Map — precise remaining frontier (2026-05-25)

State after the Claude-subagent round (codex usage exhausted). Whole project
builds integrated: `lake build ShenWork` green, 8326 jobs, 0 sorry / 0 axiom
(every key theorem `#print axioms` = [propext, Classical.choice, Quot.sound]).
PDE direction confirmed by Liang: classical solution = joint C^{2,1}.

## PROVEN this round (deep machinery, all axiom-clean, committed)

- Kernel↔spectral: `intervalNeumannFullKernel_eq_cosineKernel`, `intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional`, `..._contDiff_two_unconditional` (full Neumann kernel semigroup = cosine spectral heat value, spatially C²). Files: PDE/IntervalNeumannFullKernel.lean, PDE/IntervalFullKernelInterchange.lean.
- Poisson/theta: `gaussianLatticeSum_poisson(_complex)` (Mathlib Complex.tsum_exp_neg_quadratic).
- Heat smoothing C²: `unitIntervalCosineHeatValue_contDiff_two`. Parabolic gain: `parabolicGain_le_one` (kills s→t singularity). File: PDE/IntervalDuhamelRegularity.lean.
- IBP engine: `intervalCosineLaplacianCoeff_eq` (⟨Δg,eₙ⟩=−λₙ⟨g,eₙ⟩ for genuine-Neumann C² g). File: PDE/IntervalSolutionCoeffDeriv.lean.
- Spectral generator: `intervalFullSemigroupOperator_hasTimeDerivAt_spectral`. Duhamel rep assembly: `intervalDuhamelRepresentation_of`. File: PDE/IntervalDuhamelRepresentation.lean.
- Approximate identity: `intervalFullSemigroup_tendsto_id_at_zero` (Tannery). File: PDE/IntervalSemigroupApproxIdentity.lean.
- Regularity def completed to joint C^{2,1} (commit 754ee06 spatial C², 69176a5 time-diff).
- Neumann BC / sup IBP enablers; resolver R + L²/sup/grad Lipschitz; L2 uniqueness Gronwall core + certificate (cond. on frontiers); ball-estimates (hchem/hint/hlift_int over R); logistic Lipschitz.

## DEFINITION FAITHFULNESS GAPS (classical-solution def incomplete)

1. DONE: spatial interior C² added; timeDeriv made genuine (joint C^{2,1}).
2. OPEN — Neumann BC VACUOUS: `intervalDomainNormalDeriv f x := if x.1=0∨x.1=1 then 0 else deriv...` is hardcoded 0 at boundary → the `normalDeriv (u t)=0` conjunct of `IsPaper2ClassicalSolution` (Paper2/Statements.lean:70) asserts nothing about u. Need genuine one-sided derivative = 0; then re-prove the ~24 users. (Caught by the IBP work; the IBP needs genuine g'(0)=g'(1)=0.)
3. NOTE: S(0)=id is FALSE here (`heatKernel 0 = 0`); use the proven approximate-identity limit instead (da16507 documents).

## REMAINING ANALYTIC OBLIGATIONS (named, reachable, real theorems)

A. Pointwise cosine inversion `∑ₙ f̂ₙ cos(nπx) = f x` at interior x (repo has only L² totality `unitIntervalCosine_nat_total_ae_zero`) + ℓ¹ coeffs `Summable |f̂ₙ|`. → closes approximate-identity hypotheses (`hrecon`, `hl1`).
B. `CoeffTimeDerivUnderIntegral`: d/ds⟨u s,eₙ⟩=⟨∂ₛu s,eₙ⟩ (differentiate inner product under integral; needs uniform integrable envelope — joint-time-regularity class). `SpectralSeriesTermwiseDeriv`: termwise s-deriv of the cosine tsum.
C. Re-assemble `intervalDuhamelRepresentation_of` using the approximate-identity limit (proven) instead of the false `IntervalSemigroupIdentityAtZero`.
D. Genuine-Neumann regularity input for `IntervalSolutionFourierCoeffDeriv` (depends on gap #2).
E. Energy differential inequality `E′ τ ≤ K·E τ` for w=u₁−u₂ → `IntervalDomainL2DifferenceEnergyFrontier` → gluing (needs the under-integral Leibniz D1 ball-diff + D2 envelope, same joint-time class as B).
F. ASSEMBLE: representation + DuhamelTermInteriorC2 (needs DuhamelHeatValueRepresentation Fubini, blocked on the representation) + boundedness (proven) → `IntervalDomainGlobalSolutionExists` → `Theorem_1_1_intervalDomain` unconditional; gluing → uniqueness; Paper3 Theorem 2.x + Paper1 Theorem 1.2/1.3 follow (already reduced to existence).

## Honest summary
All deep mechanisms proven + integrated-verified. Theorem 1.1 NOT closed.
Remaining = complete the faithful def (genuine Neumann, #2) + standard analysis
(pointwise cosine inversion A; under-integral coeff/energy regularity B,E;
representation reassembly C) + final assembly F. Each reachable, real,
multi-step. No Mathlib gap identified — all repo-side / standard parabolic theory.
