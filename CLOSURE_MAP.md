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

---

## ROUND-2 UPDATE (2026-05-25, after Claude-subagent push — 22 commits)

### Faithful definition COMPLETE
`intervalDomainClassicalRegularity` now has 6 conjuncts = genuine joint C^{2,1} + genuine Neumann:
`.1/.2` sup-mono; `.2.2.1` interior spatial ContDiffOn ℝ 2; `.2.2.2.1` per-x time DifferentiableAt + ∂ₜ ContinuousOn; `.2.2.2.2.1` JOINT (t,x) continuity of ∂ₜ on Ioo×Ioo; `.2.2.2.2.2` genuine one-sided Neumann. All constructors (constant/equilibrium/bad-tail) discharge. Full build green 8326.

### Additionally PROVEN this round (axiom-clean, committed)
- Obligation A CLOSED: `intervalCosine_hasSum_pointwise` + `intervalCosineCoeff_summable_abs` (pointwise cosine inversion + ℓ¹) — e40efab.
- Localized under-integral Leibniz `intervalIntegral_hasDerivAt_time_of_local` + `exists_bound_of_continuousOn_slab` (D1 fixed; D2 from closed-slab continuity) — 90db85f.
- Energy Leibniz machinery `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous` (energy time-derivative reduced to one closed-slab-continuity hypothesis) — 0614724.
- Genuine-Neumann (d20173a), continuous-∂ₜ (3fb3c1d), joint-continuity (c972404).

### THE RECURSIVE-DEEPENING FINDING (honest)
Each regularity level revealed the next: spatial-C² → genuine-Neumann → time-DifferentiableAt → time-ContinuousOn → JOINT continuity → now BOUNDARY regularity. The current blocker for E (gluing): `exists_bound_of_continuousOn_slab` needs continuity on the CLOSED slab `Icc(τ−δ,τ+δ) ×ˢ Icc 0 1`, but the def gives only OPEN `Ioo×Ioo` — i.e. a τ-uniform INTEGRABLE bound on ∂ₜw up to spatial endpoints x→0⁺,1⁻ (where the zero-extension lift branches). This is genuine PARABOLIC BOUNDARY REGULARITY — a real classical PDE theorem, not bookkeeping, not a Mathlib gap.

### REMAINING (genuine deep tail, each a real theorem)
1. Parabolic boundary regularity: ∂ₜu (and ∂ₓ,∂ₓₓ) continuous/integrable UP TO the spatial endpoints → closes the closed-slab envelope → E (gluing).
2. `Eprime ≤ K·E` IBP step (PDE substitution + Neumann IBP with genuine boundary w'(0)=w'(1)=0 + Lipschitz absorption).
3. localExistence genuine constructor: full-kernel mild solution satisfies the complete 6-conjunct regularity (needs joint Weierstrass `continuous_tsum` for −∑λₙe^{−tλₙ}f̂ₙcos) + the Duhamel term (DuhamelTermInteriorC2 / DuhamelHeatValueRepresentation).
4. Representation reassembly with the approximate-identity limit (C); final assembly (F) → Theorem 1.1.

### Honest status
Faithful def + all reachable deep machinery proven & verified & integrated (8326 green). Theorem 1.1 NOT closed; the remaining is genuine boundary parabolic-regularity theory — a sustained expert-level effort, not in-session subagent-grindable. No Mathlib gap identified.
