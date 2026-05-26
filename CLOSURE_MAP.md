# ShenWork Closure Map — precise remaining frontier (2026-05-26)

State after the Claude-subagent round (codex usage exhausted). Whole project
builds integrated: `lake build ShenWork` green, 8343 jobs, 0 sorry / 0 axiom
(every key theorem `#print axioms` = [propext, Classical.choice, Quot.sound]).
PDE direction confirmed by Liang: classical solution = joint C^{2,1}.

## ROUND-10 FINAL (2026-05-26, HEAD 66e6e90, self-verified) — GLUING CLOSED IN TWO FORMS

Two coexisting fully-verified gluing theorems (both axiom-clean):

### (A) γ≥1: FULLY UNCONDITIONAL (modulo regime + positive datum)
`GlobalSolutionGluingFromReachability_of_regime_gammaGeOne (p) (hχ : χ₀≤0) (ha : 0<a) (hb : 0<b) (hγ_ge_one : 1 ≤ γ) (hpos : ∀ pair, PositiveInitialDatum)`
covers paper2 formula (1.3)'s standard KS regime (γ=m=α=1). `L_γ = γ·M^(γ-1)` via
MVT on `[0,M]` (no `δ` needed since `x^{γ-1}` bounded when `γ≥1`).
File `Paper2/IntervalDomainL2UEnergyUniformGammaGeOne.lean`.

### (B) general γ>0: unconditional modulo δ>0 lower bound
`GlobalSolutionGluingFromReachability_of_regimeAndLowerBound (p) (hχ) (ha) (hb) (hpos) (hlower : ∃ δ>0, …)`
covers all `γ>0`; needs the `δ>0` lower bound only because `x↦x^γ` Lipschitz
constant on `[δ,M]` is `γ(δ^{γ-1}+M^{γ-1})` and `δ^{γ-1}` blows up at 0 for `γ<1`.
The `δ>0` is the strong-maximum-principle-style content (uniform positivity of
the solution on `(0,T)×[0,1]`); proving it is a separate genuine PDE theorem
(not in repo, not a Lean gap).

### Faithful def state
`intervalDomain.initialAdmissible := BddAbove (Set.range fun x => |u₀ x|)`
(strengthened from `True`; faithful PDE-classical-solution datum requirement).
`IsPaper2ClassicalSolution` carries closed-domain `0 < u`, `0 ≤ v`, closed-`Icc`
C² + endpoint Neumann (values), joint continuity, closed-slab ∂ₜ continuity,
endpoint time-differentiability — a genuine positive classical-solution predicate.

### Entire u-only uniqueness analytic machinery PROVED unconditional + axiom-clean
PDE substitution → dissipation `−∫(∂ₓw)²` (`intervalEnergyByParts`) → chemotaxis
IBP (`intervalFluxByParts`) → Young absorption → reaction Lipschitz → energy
inequality `∫integrandDeriv ≤ K·E_u` (`intervalDomainL2U_energy_diffIneq_bound`).
Full frontier (Leibniz HasDerivAt, cont, initial_vanishes, zero_pointwise where
v=V via resolver characterization). Static v-control (value+grad) by E_u.
Elliptic characterization `solution_v_resolverCoeff_eq` (coefficient-level
unconditional). Cosine coefficient decay `|f̂ₙ|≤M/(nπ)²` for C²-Neumann.
Resolver gradient bridge `resolverR_hasDerivAt_grad` (Weierstrass M-test).
Quantitative resolver sup bounds `F(M)=(ℓ²-weight)·2νM^γ`. Flux closed-Icc C¹.
Upper bound M derived from proven Lemma 3.1 (`uniform_lift_upper_bound_of_regime`).

### Commits this stretch
~18 verified commits 8561490 → 66e6e90, every one self-verified
(`lake build ShenWork` green + `#print axioms` = the three core only).

## ROUND-8 CONSOLIDATED (2026-05-26, HEAD 5a34322, self-verified) — GLUING ≈ CLOSED

The ENTIRE u-only uniqueness/gluing analytic body is now PROVED unconditional +
axiom-clean. Gluing `GlobalSolutionGluingFromReachability p` reduces to ONE
boundedness obligation `IntervalDomainL2UBoundedDatumUniform p`
(file Paper2/IntervalDomainL2UFrontierAssembly.lean), via
`GlobalSolutionGluingFromReachability_of_boundedDatumUniform`.

PROVED unconditional this stretch (commits 9c9778d…5a34322, all axiom-clean):
- Energy inequality CORE `intervalDomainL2U_energy_diffIneq_bound`
  (`∫ integrandDeriv ≤ K·E_u`, K=χ₀²Cflux+2L): PDE substitution + dissipation
  `−∫(∂ₓw)²` + chemotaxis IBP + Young `2χ₀∫∂ₓw·g ≤ ∫(∂ₓw)²+χ₀²∫g²` + reaction
  Lipschitz. File Paper2/IntervalDomainL2UEnergyCombine.lean.
- Full frontier assembled unconditional (Paper2/IntervalDomainL2UFrontierAssembly.lean):
  Leibniz `intervalDomainL2UEnergy_hasDerivAt_of_solution`, `cont`,
  `initial_vanishes`, `zero_pointwise` (E_u=0⟹u=U; v=V via static_v_value).
- Faithful def repairs (interior→closed / missing conjuncts): endpoint
  time-differentiability (conjunct 4 → closed), v≥0 (concentration), u>0,
  closed-Icc C² + Neumann, joint continuity. IsPaper2ClassicalSolution now a
  genuine positive classical-solution predicate.
- Static v-control (value+grad) by E_u, flux IBP, flux closed-Icc C¹, flux L²
  bound, elliptic characterization, coeff decay, gradient bridge — all earlier,
  all unconditional.

REMAINING = `IntervalDomainL2UBoundedDatumUniform p`: (bdd₀) shared initial
datum bounded + (Kunif) a τ-uniform Grönwall constant. KEY: this is a
BOUNDEDNESS obligation, NOT a new analytic gap — `Theorem_1_1_intervalDomain_conditional`
(Paper2/IntervalDomainChain.lean) ALREADY proves the uniform sup-norm bound
`supNorm(u t) ≤ max(supNorm u₀, (a/b)^{1/α})` (via Lemma_3_1 + initialSupNormApproach)
and constructs `IsPaper2BoundedBefore`. The per-time K(τ)=χ₀²Cflux+2L is bounded
once `supNorm(uᵢ τ) ≤ M` uniformly ⇒ Kunif; u₀ bounded ⇒ bdd₀. CAVEAT: Lemma_3_1's
bound holds under Theorem 1.1's parameter regime (hχ neg-sensitivity, a,b>0, m≥1),
so the honest resting point may be "gluing unconditional modulo boundedness, which
holds in the Theorem 1.1 regime" — matching paper2's own "bounded ⇒ global"
structure.

## ROUND-9 FINAL STATE (2026-05-26, HEAD ccb926a, self-verified, build 8342)

Discharge outcome: full-unconditional is FALSE (uniform M needs Thm 1.1 regime
χ₀≤0,a,b>0 via Lemma 3.1). Delivered the FAITHFUL reduction — gluing is now
`GlobalSolutionGluingFromReachability_of_uniformSupBound` (axiom-clean), taking the
NATURAL hypothesis `IntervalDomainUniformLiftBound p` (every solution-pair sharing
a trace is uniformly `lift(uᵢ τ) ∈ [δ,M]` on (0,minT)×[0,1]) + datum boundedness.
The ad-hoc Grönwall K is now DERIVED, not assumed: quantitative resolver sup bounds
`resolverValue/Grad_sup_le_of_ub` (`F(M)=(ℓ²-weight)·2νM^γ`) ⇒ `CfluxQuant(δ,M)` ⇒
uniform K. Files Paper2/IntervalDomainResolverSupQuantitative.lean,
Paper2/IntervalDomainL2UEnergyUniform.lean.

NET: the ENTIRE u-only uniqueness/gluing ANALYTIC machinery is proved unconditional
& axiom-clean. Gluing holds modulo exactly: (i) uniform sup bound `M` on solutions
(= `IsPaper2BoundedBefore`, which Theorem_1_1_intervalDomain_conditional ALREADY
proves under the regime); (ii) uniform positive lower bound `δ>0` (needed only for
`γ<1`; a strong-max-principle quantitative positivity — NOT yet in repo); (iii)
datum boundedness `bdd₀` (intervalDomain `initialAdmissible=True` is too weak — a
faithful-def question). All three are boundedness/positivity inputs matching paper2's
own structure, NOT analytic gaps. REMAINING WORK = formulation/architecture (connect
(i) to Lemma 3.1 under the regime; decide datum-admissibility def; prove uniform δ>0)
— best done with Xiang/Liang, not autonomously.

## ROUNDS 5–7 CONSOLIDATED (2026-05-26, HEAD 31c4df3, self-verified)

The ENTIRE analytic infrastructure for u-only uniqueness is now UNCONDITIONAL
(no hypotheses). Gluing closes via the chain
`IntervalDomainL2UDiffIneqResidual p` → `intervalDomainL2UJointTimeRegularity_of_residual`
→ `intervalDomainClassicalUniquenessL2EnergyMethod_of_uJointTimeRegularity`
→ `..._of_uFrontier` → `GlobalSolutionGluingFromReachability_of_l2EnergyMethod`,
and the ONLY remaining open obligation is the single residual structure
`IntervalDomainL2UDiffIneqResidual p` = the nonlinear parabolic energy
inequality `E_u'(τ) ≤ K·E_u(τ)` itself.

PROVED unconditional + axiom-clean this stretch (commits fc0f5c3, a67c952,
d1f581f, 4c3ee88, 31c4df3):
- Elliptic characterization `solution_v_resolverCoeff_eq` (v cosine-coeffs =
  resolver coeffs; coefficient-level, no hyps) + supporting eigenfunction-IBP
  `intervalCosineLaplacianCoeff_eq_of_contDiffOn`. File PDE/IntervalEllipticCharacterization.lean.
- Coefficient decay `cosineCoeff_decay` (|f̂ₙ|≤M/(nπ)² for C²-Neumann) +
  ℓ¹ value reconstruction `fourierCoeff_reflCircle_summable`. File PDE/IntervalCosineCoeffDecay.lean.
- Termwise-diff bridge `resolverR_hasDerivAt_grad` (deriv of value series =
  resolver gradient series, Weierstrass M-test). File PDE/IntervalResolverGradientBridge.lean.
- FAITHFUL POSITIVITY: `IsPaper2ClassicalSolution` positivity strengthened
  interior-conditional → closed-domain `0 < u t x` (positive classical solution,
  Chen–Ruau–Shen + strong max principle); ~30 sites re-discharged across 11
  files; Paper3 counterexample `proposition12Counter` given a positive profile
  (content preserved: u=t unbounded for t≥1, Thm1.1⇏Prop1.2 holds; the old
  version had exploited the vacuous empty-interior positivity).
- `sourceCoeffQuadraticDecay_of_solution` PROVED unconditional (positive lower
  bound + rpow C² on positives + Neumann endpoints + cosineCoeff_decay).
- `solution_resolver_grad_hasDerivAt` (static ∂ₓ(v−V) control) unconditional.
- Resolver-Lipschitz pointwise-reconstruction side-hyps discharged for solutions:
  `solution_resolver_(cosine|sine)Series_summable`. File Paper2/IntervalDomainL2UStaticVControl.lean.
- u-only track (E_u=∫(u−U)²) + Leibniz half + bridges (rounds 4): files
  Paper2/IntervalDomainL2UEnergy.lean, Paper2/IntervalDomainL2UEnergyInequality.lean.

REMAINING = `IntervalDomainL2UDiffIneqResidual p`, a 5-step nonlinear combine,
all inputs now unconditional:
1. Pointwise elliptic rep `lift(v t) = resolverR(u t)` unconditional for
   solutions (discharge `solution_v_eq_resolver_pointwise` F/hFcont/hFcoeff/
   hFsum/hFeq by constructing the continuous even-reflection representative;
   hFsum from `fourierCoeff_reflCircle_summable`, hRsum from the new summability).
2. Static L² control `∫ (lift(v₁−v₂))² + (∂ₓlift(v₁−v₂))² ≤ C·E_u`
   (per-point sup bounds + L∞ via conjunct-7 compactness).
3. Chemotaxis IBP lemma `∫ w·∂ₓ(F) = −∫ ∂ₓw·F` (Neumann kills boundary), analogue
   of proven `intervalEnergyByParts`.
4. Flux-difference pointwise bound `|flux₁−flux₂| ≤ C(|w|+|v-diff|+|∂ₓ v-diff|)`
   (product/quotient rule on `u·∂ₓv/(1+v)^β`, using `1+v≥1` from v>0).
5. Combine: `pde_u` substitution into `½E_u'=∫w·∂ₜw` + dissipation `−∫(∂ₓw)²`
   (`intervalEnergyByParts`) + reaction `intervalLogisticSource_lipschitz` +
   Young (sign-free `|χ₀|`, ε∫(∂ₓw)² absorbed) ⇒ `E_u'≤K·E_u`.
No Mathlib gap; pure repo-side nonlinear parabolic-elliptic energy estimate.

## ROUND-3 UPDATE (2026-05-26, commit 8561490, self-verified build+axioms)

R1 and R2 — the two pieces scoped as closeable — are DONE and clean:
- R1: conjunct (9) of `intervalDomainClassicalRegularity` = joint continuity of
  the solution field `(t,x)↦intervalDomainLift(u t)x` on `Ioo 0 T ×ˢ Icc 0 1`
  (+ for v). All 6 build-path constructors/transfer lemmas re-discharged.
- R2: `ShenWork.IntervalSolutionCoeffDeriv.intervalEnergyByParts`:
  `∫₀¹ w·w'' = −∫₀¹ (w')²` via closed-`Icc` `HasDerivAt` + endpoint Neumann
  values (conjunct 7), one `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`.

KEY SHIFT: because conjunct (7) now ASSERTS closed-Icc C² + endpoint Neumann in
the def, the remaining residual is NO LONGER "prove Schauder boundary
regularity" — that regularity is now hypothesised by the faithful def. The
single residual `IntervalDomainL2JointTimeRegularity p` is the nonlinear ENERGY
ESTIMATE assembly: substitute the pointwise PDE identity into E′, IBP via R2,
absorb chemotaxis/reaction differences by `intervalLogisticSource_lipschitz` +
resolver Lipschitz + the L∞ bound (now available: conjunct-7 `ContDiffOn (Icc 0
1)` ⇒ bounded on compact). Multi-lemma but reachable, repo-side, no Mathlib gap.

## ROUND-4 UPDATE (2026-05-26, commit 2b8a8b8, self-verified build 8328 + axioms)

FINDING: the bundled energy `∫₀¹ (u−U)²+(v−V)²` is the WRONG functional for a
parabolic-elliptic system. Differentiating `(v−V)²` forces `∫ z·∂ₜz` (z=v−V),
but z solves an ELLIPTIC relation (`0=∂ₓₓz−μz+ν(u₁^γ−u₂^γ)`) — no time-equation
among hypotheses ⇒ dead-end. Artifact of the energy choice, not a Mathlib gap.

FIX (standard parabolic-elliptic uniqueness; new file
`ShenWork/Paper2/IntervalDomainL2UEnergy.lean`, in build graph): u-only energy
`E_u=∫₀¹ (u−U)²`; z controlled STATICALLY (`‖z‖,‖∂ₓz‖≤C‖w‖` via proven
`intervalNeumannResolverR_(sup|grad_sup)_lipschitz`); `E_u=0⇒u=U⇒v=V` by
elliptic uniqueness. PROVED + axiom-clean: `…L2DifferenceEnergyU(+_nonneg)`,
`IntervalDomainClassicalOverlapL2UEnergyCertificate`,
`…overlap_unique_of_l2UEnergyCertificate` (genuine Grönwall on E_u),
`IntervalDomainL2UDifferenceEnergyFrontier(+_of_diffIneqFrontier)`,
`intervalDomainClassicalUniquenessL2EnergyMethod_of_uFrontier` (THE bridge ⇒
full joint method ⇒ `GlobalSolutionGluingFromReachability`),
`IntervalDomainL2UJointTimeRegularity`(+builder+`_of_uJointTimeRegularity`).

REMAINING (single obligation, strictly WEAKER — v-difference time-derivative
GONE): construct `IntervalDomainL2UJointTimeRegularity p` = standard parabolic
`E_u′≤K·E_u`. Leibniz half from conjuncts (8)(9)+slab machinery; dissipation
`−2∫(∂ₓw)²≤0` from proven `intervalEnergyByParts`. Open part = chemotaxis/
reaction Lipschitz absorption assembly + reconciling abstract `chemotaxisDiv`/
`laplacian` derivs with resolver-Lipschitz summability (may need a lemma that
the abstract solution's v IS the resolver of u).

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
