# Paper 2 — gradient mild map: output-derivative vs conjugate-kernel (DESIGN DECISION for Xiang)

Found 2026-06-19 (overnight /automode), verified against source + ChatGPT-grounded.

## The finding (verified)
`intervalGradientDuhamelMap` (IntervalGradientDuhamelMap.lean:58) defines the chemotaxis term as the
OUTPUT derivative of the Neumann semigroup applied to the C⁰ flux Q:
  (−χ₀) ∫₀ᵗ deriv(z ↦ S_N(t−s)(Q(u(s)))(z))(x) ds      [verified: `deriv (fun z => intervalFullSemigroupOperator (t-s) (chemFluxLifted) z) x.1`]
On [0,1] with the Neumann cosine semigroup S_N (modes cos(nπx)), ∂x S_N maps cosₙ ↦ −nπ sinₙ — so this
gradient term is a SINE (Dirichlet) series: it vanishes at x=0,1 but its x-derivative does NOT.

## Why it matters
For the mild fixed point u=Φ(u) to be a CLASSICAL NEUMANN solution (∂xu=0 at endpoints, satisfying
u_t=u_xx−χ₀·chemDiv+L), the chemotaxis term must be the NEUMANN-COSINE source form
  −χ₀ ∫₀ᵗ S_N(t−s)(chemDiv(s)) ds,  chemDiv = ∂x(flux) = Q_x,
i.e. the CONJUGATE-KERNEL operator B_N(r)Q := −∫₀¹ ∂_yK_N(r,x,y)Q(y)dy = S_N(r)(Q_x), which IS a cosine
(Neumann) series. The KEY: B_N Q (cosine) ≠ ∂x(S_N Q) (sine) on the interval (they only coincide on the
whole line, by translation invariance). The boundary term in the IBP B_N vs output-deriv vanishes BECAUSE
Q(0)=Q(1)=0 (PROVED: chemFluxLifted_endpoint_zero/one — Q=u^m S(v) v_x, v_x=0 by v Neumann), but the two
operators are still NOT equal (∫∂xK_N·Q ≠ −∫∂yK_N·Q for the cos·cos kernel).

## The decision (Xiang's call — NOT self-authorized)
The slice agreement CoupledDuhamelT6SliceAgreement (needed for the mild-to-classical pde_u → localExistence)
is only FAITHFUL if the gradient mild map is the conjugate-kernel form B_N, not the output-derivative form.
Options:
  (A) CORRECT the core map: redefine the chemotaxis term as −χ₀∫S_N(t−s)(B_N-form / S_N(Q_x)). Ripples through
      the entire existence construction (Banach FP / Picard, the bounds, the contraction) — they'd need re-checking
      against the corrected map. Big, but faithful.
  (B) Add a RECONCILIATION lemma: prove the output-deriv fixed point and the conjugate-kernel solution coincide
      (UNLIKELY — ChatGPT shows they differ; would need a special structural cancellation).
  (C) Verify whether the existing framework ALREADY reconciles this elsewhere (the weak→classical bridge may
      handle it) — audit before concluding the map is non-faithful.
RECOMMENDATION: (C) first (audit — don't over-claim a bug in audited work), then (A) if genuinely needed.
The endpoint-zero lemmas + the diagnosis are banked (IntervalCoupledDuhamelT6SliceAgreement.lean). hagree is
BLOCKED on this decision; the other Paper-2 frontier (hsrc) + avenue-c (Paper-1 parabolic) are NOT blocked.

## ⛔ SUPERSEDED — 2026-06-19 ADVERSARIAL RE-AUDIT (opus, independent, verified by hand)
The (C)-audit conclusion below is HALF RIGHT and was MIS-TARGETED. Corrections:
1. hagree (CoupledDuhamelT6SliceAgreement) IS unsatisfiable for χ₀≠0 — TRUE, and the repo's own
   `gradient_source_bridge_forces_*_endpoint_zero` (IntervalGeneralChiFrontier.lean:154-170) is the obstruction
   lemma admitting it. BUT this cluster is DEAD/abandoned parallel code.
2. The actual headline `paper2_theorem_1_1_of_frontier` (IntervalDomainThm11Assembly.lean:80) does NOT carry
   hagree. It carries hUniform (F1, IntervalDomainUniformLocalExistence) + hMildLocal. Its chemotaxis content is
   `hpde_u` = the INTERIOR (Ioo 0 1) spectral PDE identity, marked ✓ proved (G4n-p). The endpoint sine/cosine
   mismatch is defined AT x=0,1; on the open interior IBP ∫∂_xK_N·Q = −∫∂_yK_N·Q + [K_N Q]₀¹ agrees POINTWISE
   (only boundary values differ), so the obstruction cannot reach the interior identity. ⟹ the headline is NOT
   vacuous. My "general-χ vacuous via hagree" claim was a MIS-FIRE on dead code (did not check whether the
   headline depends on hagree before concluding).
3. Option (A) as written is ALSO flawed: (i) "B_N Q = S_N(Q_x)" needs W^{1,1} Q (defeats the C⁰-flux point;
   Lean's deriv of non-diff silently = 0); (ii) the boundary vanishing it relies on (flux_endpoint_zero,
   IntervalDomainL2UEnergyCombine.lean:919) takes hsol : IsPaper2ClassicalSolution and derives Q(0)=Q(1)=0 from
   the SOLUTION's Neumann BC — circular (smuggles the conclusion into the construction). The √T contraction half
   of (A) is sound (reflected-image sign flip changes boundary behavior, not integrability — heat kernels at
   t>0 are smooth, no new singularity).
VERDICT: DO NOT pursue (A). Paper-2 general-χ real status = conditional-faithful; genuine open frontiers are
F1 (uniform continuation, textbook) + F2 (limit-source DuhamelSourceTimeC1), both satisfiable, actively
discharging. hagree cluster is dead code (could be deleted, but harmless). The real next work for general-χ is
F1/F2, NOT a map rebuild.

## PRECISE general-χ target (2026-06-19, from reading the χ₀=0 unconditional discharge)
`intervalDomain_theorem_1_1_chiZero_unconditional` (IntervalDomainTheorem11ChiZeroUnconditional.lean:48)
discharges BOTH hUniform (F1) and hMildLocal at χ₀=0. The ONLY χ₀=0-specific pieces are:
  • `Thm11ChiZeroCoreProvider.quantitativeLocalExistence_chiZero_datum` (the Picard contraction — trivial at
    χ₀=0 since chemotaxis term carries factor (-χ₀)=0);
  • `Thm11ChiZeroCoreProvider.hMildLocal_chi0_zero_of_datum` + `chiZeroDatumProviderSupply`.
Everything else is ALREADY general-χ≤0: `SupNormBridge.interiorSupNorm_le_regimeBound` and
`uniformLiftBoundZeroM_of_regime` both take χ₀≤0 (used here via le_of_eq hχ0), and `RestartAndGlueWorks`
(GlueExtension + TimeShift + PiecewiseClassical + L2-energy uniqueness) is χ≤0-general.
⟹ The real general-χ frontier = extend `quantitativeLocalExistence_chiZero_datum` + `hMildLocal_chi0_zero_of_datum`
from χ₀=0 to χ₀<0. NOT just "add √T contraction" — verified by reading the provider internals
(IntervalDomainThm11ChiZeroCoreProvider.lean): `hχ0 : p.χ₀ = 0` threads through MULTIPLE pieces, giving a
TWO-PART frontier:
  PART 1 (existence): `coneGradientMildSolutionData_exists_with_data p hχ0` (line 812) — the cone-invariant
    Picard fixed point. At χ₀=0 the chemotaxis term vanishes so the cone [c,M] is trivially preserved; at χ₀<0
    cone invariance needs the chemotaxis term controlled (the EXISTING √T bound `gradDuhamel_diff_sup_bound`,
    IntervalGradDuhamelBound.lean:227, |χ₀|·C_grad·2√T·C_Q, supplies the smallness). Tractable.
  PART 2 (FAITHFULNESS — the real content): `mildSolution_pde_u_of_spectral` (IntervalDomainPdeUProducer.lean:126)
    is EXPLICITLY the χ₀=0 regime producer (file docstring line 4,16: "With p.χ₀=0 the chemotaxis term
    vanishes"). So `hpde_u` — the interior (Ioo 0 1) spectral PDE identity that carries faithfulness — is ONLY
    PROVED FOR χ₀=0. For χ₀<0 the interior spectral identity WITH the chemotaxis term −χ₀·chemotaxisDiv is the
    genuine OPEN frontier. The adversarial auditor's "hpde_u ✓ proved" was reading the χ₀=0 status table; it is
    NOT proved for χ₀<0. PROVABLE (the endpoint sine/cosine mismatch does not reach the open interior — IBP
    agrees pointwise in the bulk), but it is real work: establish that the output-deriv mild map's interior PDE
    equals the divergence form on Ioo(0,1) for the chemotaxis term, generalizing mildSolution_pde_u_of_spectral
    off χ₀=0.
THIS two-part extension is the next Paper-2 dispatch (codex), NOT (A). Part 2 (interior spectral identity for
the chemotaxis term) is the faithfulness frontier — the genuine analytic content the paper proves.

## CRUX RESOLVED (2026-06-19) — the output-deriv map IS interior-faithful (PART 2 is provable)
Worry: the output-deriv chemotaxis ∂x(S_N Q) is a SINE series, the faithful divergence −χ₀Q_x relates to a
COSINE series; since sin⊥cos on [0,1], they differ on POSITIVE measure in (0,1), not just at endpoints. Does
the output-deriv mild solution then solve the WRONG interior PDE for χ₀≠0?
RESOLUTION (Duhamel time-boundary mechanism — the chemotaxis PDE term does NOT come from the operator's spatial
form): let w(t,x)=∫₀ᵗ ∂x[S_N(t−s)Q(s)](x) ds (the output-deriv chemotaxis integral). Leibniz in t:
  w_t = [∂x S_N(0)Q(t)] + ∫₀ᵗ ∂_t{∂x S_N(t−s)Q(s)} ds = ∂xQ(t) + ∫₀ᵗ ∂x Δ_N S_N(t−s)Q(s) ds = ∂xQ(t) + Δw,
using S_N(0)=id and ∂x Δ_N g = ∂_xxx g = Δ(∂x g) pointwise. So with u = S_N(t)u₀ − χ₀ w + (reaction Duhamel),
pointwise on the interior u_t = Δu − χ₀·∂xQ(t) + reaction = Δu − χ₀·Q_x + reaction = the FAITHFUL PDE. The
chemotaxis term −χ₀Q_x enters as the Duhamel TIME-BOUNDARY term ∂xQ(t) (the s=t Leibniz term), NOT from the
operator's sine spatial profile (which only affects w's shape, irrelevant to the interior PDE). ⟹ the
output-deriv mild map is interior-faithful for ALL χ₀; PART 2 is genuinely provable. The endpoint sine/cosine
mismatch only kills the SLICE/endpoint form (the dead hagree cluster), never the interior PDE. (Cross-check
fired to ChatGPT cron channel /tmp/gpt_interior_crux.txt; verify before final banking.) For the Lean PART 2:
hpde_u_core (IntervalDomainPdeUChiZero.lean:39) already has −χ₀·chemotaxisDiv in its conclusion; generalize off
χ₀=0 by carrying the chemDiv source coefficients (coupledChemDivSourceCoeffs) so hreact becomes the FULL source
identity (reaction − χ₀·chemotaxisDiv via the cosine Fourier series of chemDiv converging on the interior).

## (C) AUDIT CONCLUSION — 2026-06-19 (CONFIRMED: hagree is unsatisfiable for χ₀≠0; (A) is necessary)  [MIS-TARGETED — see SUPERSEDED block above]
Traced the ACTUAL existence fixed point. `intervalGradientDuhamelMap` (IntervalGradientDuhamelMap.lean:60-64)
is the iterated map, and its chemotaxis term is literally
  (−χ₀) ∫ deriv(z ↦ intervalFullSemigroupOperator(t−s)(chemFluxLifted(u s)) z)(x) ds  =  −χ₀ ∫ ∂x(S_N(t−s) Q) ds,
i.e. the OUTPUT-DERIVATIVE (sine) form on the C⁰ flux Q. The slice target
`CoupledDuhamelT6SliceAgreement` (IntervalCoupledRegularityBanked.lean:19) is
  u t =EqOn= ∫ unitIntervalCosineHeatValue(t−s)(coupledChemicalSourceCoeffs p u s),
and coupledChemicalSourceCoeffs = cosineCoeffs(intervalCoupledSource) which uses `intervalDomainChemotaxisDiv`
(= Q_x, the divergence), so the target = S_N(Q_x) (cosine). PROOF they differ on [0,1]: with K_N the Neumann
heat kernel, ∂x(S_N Q)(x) = ∫∂_xK_N·Q has spectral shape sinₙ(x)cosₙ(y); S_N(Q_x)(x) = −∫∂_yK_N·Q (boundary
[K_N Q]₀¹=0 since Q(0)=Q(1)=0) has shape cosₙ(x)sinₙ(y). sin⊗cos ≠ cos⊗sin ⟹ UNEQUAL (equal only on ℝ by
translation invariance). hagree is NEVER discharged (no producer in tree) and is unsatisfiable for χ₀≠0 ⟹ the
general-χ headline carries a vacuous hypothesis (§3.3 violation). χ₀=0 unaffected (term vanishes; 986e7d1 stays
faithful). VERDICT: option (B) impossible; option (A) (rebuild the Picard map with the faithful cosine
S_N(chemDiv) form, making hagree definitional) is the honest fix. The cosine form's regularity infrastructure
already exists (coupledChemDivSourceCoeffs + IntervalWeakH2Neumann decay lemmas); the cost is the contraction
must be redone against the chemDiv (one-higher-derivative) source — that IS the paper's real local-existence
content, not a shortcut. Secondary flag: the slice target omits the S_N(t)u₀ homogeneous term — verify it is
separately handled (instant smoothing for t>0) and not a second gap.

## Paper-1 margin route (2026-06-20, ChatGPT cron): crude |F|≤C·U⁺ with C<1 is FALSE
The global weighted-margin route is false: best global constant ≥1 even at χ=0 (right-tail logistic coeff=1);
small t₀ doesn't help (ρ_t~min(1,λ)t competes with Ct). Unconditional margin needs a SHARPER super-solution:
spatially-resolved tail/core using the exact semigroup tail action with λ=1+κc−κ²>1 (needs c>κ), or F₊ not |F|,
or a modified barrier. DO NOT dispatch the crude route. The conditional aux-flow discharge (margin CARRIED,
commit 1fa12a7) stands as honest; unconditional margin is deferred genuine work, NOT blocking the conditional
formalization.

## Paper-2 B-form positivity route (2026-06-20, ChatGPT cron2 + verified)
The relative multiplicative-cone route FAILS for the conjugate kernel B_N: ∫∫|∂_yK_N|·h_s^m does NOT give
o(1)·h_t (derivative kernel "bridge drift" interior→boundary gives O(1) relative correction, even m=1). codex's
stall was CORRECT. Two valid routes:
- GENERAL nonneg (boundary-vanishing data): truncate the nonlinearity + weak negative-part estimate, key
  cancellation (u₊)^m(u₋)_x=0 a.e. (= Q vanishes at u=0); then strong max principle for interior strict pos.
- PID LOCAL EXISTENCE (the spectral-provider hpost: 0<u on CLOSED [0,1]): the ABSOLUTE inf-threshold suffices —
  S_N(t)u₀ ≥ inf u₀ (>0 for PID), chemotaxis correction ≤ |χ₀|Cg·2√t·M^m, react ≤ t‖L‖, so
  u_{n+1} ≥ inf u₀ − |χ₀|Cg2√t·M^m − t‖L‖ ≥ inf u₀/2 > 0 for small t, uniformly in x (incl. boundary). This is
  the route for the local-existence spectral provider (NOT the relative cone, NOT the negative-part route which
  is for general boundary-vanishing data).

## ⛔ FAKE WIRING CAUGHT (2026-06-20) — GradientMildSolutionData bakes in the output-deriv map
codex's IntervalBFormEndToEnd.lean wired the B-form into the headline via conjugateAsGradientMildSolutionData,
which BRIDGES the B-form solution into GradientMildSolutionData. But GradientMildSolutionData (IntervalMildPicard.lean:1396)
has field hmild : IntervalMildSolution = the OUTPUT-DERIV fixed-point equation (u = intervalGradientDuhamelMap u).
The bridge carries hGradientBridge : IntervalMildSolution p T u₀ (conjugatePicardLimit) — i.e. "the B-form solution
ALSO satisfies the output-deriv map equation". For χ₀≠0 this is UNSATISFIABLE: the conjugate map (cosine chemotaxis)
≠ the output-deriv map (sine chemotaxis), so the same u cannot satisfy both fixed-point equations. ⟹
paper2_theorem_1_1_general_chi_via_bform is VACUOUS for χ₀≠0. REJECTED, NOT banked. Build EXIT=0 does not save a
vacuous conditional (§3.3).
GENUINE FIX: bypass GradientMildSolutionData. The B-form solution satisfies IsPaper2ClassicalSolution
(Statements.lean:70) DIRECTLY: interior PDE (intervalConjugateMildSolution_pde_u), Neumann BC
(intervalConjugate_normalDeriv_zero, from cosine rep), positivity (conjugatePicardLimit_pos_of_PID), C² regularity
(from cosine rep), + the resolver v-side (χ-general). Assemble these directly into IsPaper2ClassicalSolution →
Theorem_1_1 (+ F1 hUniform restart/gluing, the genuine satisfiable frontier). NO output-deriv bridge.

## Paper-2 negative-part positivity ROUTE (2026-06-20, ChatGPT cron2) — the deep-PDE ceiling
The B-form general-χ headline's hlocal reduces to BFormNegativePartPositivityRoute (negativePart_zero / strictPos
/ hpde_u). hpde_u = banked (bform_negpart_hpde_u_of_bank from intervalConjugateMildSolution_pde_u). The other two
are genuine DEEP PDE formalizations (no tree producers), per cron2's verified route:
- NONNEG (u≥0): truncate Q→Q(u₊); B_N-duality (∫B_N(τ)g·ψ = −∫g·∂xS_N(τ)ψ); mild-to-weak (⟨u_t,φ⟩+∫u_xφ_x =
  χ₀∫b(u₊)^m φ_x + ∫L̃(u)φ); negative-part energy ½d/dt‖u₋‖²+‖(u₋)_x‖² ≤ ℓ‖u₋‖² with u₋(0)=0 ⟹ u≥0; remove
  truncation. The LOCAL ∂x gives the disjoint-support cancellation the nonlocal B_N lacks — must go through the
  weak LOCAL PDE, not the mild level.
- STRICTPOS (0<u): plain S_N heat-kernel positivity is INSUFFICIENT (signed nonlocal chemotaxis, no u≥c·S_N(t)u₀).
  Needs the linearized operator's positive fundamental solution / SMP / Harnack — "essentially the strong maximum
  principle". A sub-solution comparison (w=e^{−Ct}S_N(t)u₀, hbarrier u≥w) is an alternative but needs a genuine
  Neumann-interval comparison principle (tree only has whole-line scalar ParabolicMaxPrinciple.comparison_principle).
These are the honest-conditional ceiling — satisfiable but heavy (weak negative-part energy + SMP/Harnack), the
same F2-level analytic frontier the χ₀=0 case and the other Shen headlines carry.

## §3.3 CATCH (2026-06-20, codex): NeumannLinearDriftComparison was MIS-STATED (bare-deriv ⟹ FALSE)
The strictPos squared-sub-solution (IntervalBFormSquareHeatSubsolution.lean, commit 18) carried
NeumannLinearDriftComparison stated with BARE `deriv` residuals + no continuity/differentiability/boundedness.
codex found a COUNTEREXAMPLE: zero coefficients, zero solution, a single-point spike has bare-deriv residual 0,
satisfies the initial + Neumann-endpoint conditions, yet violates the comparison at the spike ⟹ the interface is
FALSE/unsatisfiable ⟹ the squared-sub-solution lemma is VACUOUS as carried. (codex documented it in
IntervalBFormSquareHeatSubsolutionComparisonStall.lean — refused to fake the discharge.) This is a real §3.3
catch in a banked file. FIX: re-state NeumannLinearDriftComparison WITH the proper regularity (IsClassicalSub/
SuperSolution shape — boundedness + classical regularity + Lipschitz, matching the tree's
ParabolicMaxPrinciple.comparison_principle), which the actual B-form solution satisfies (cosine-rep C²), then prove
it from the tree's whole-line comparison via Neumann even-reflection. The regularity-hypothesized version is
satisfiable + dischargeable; the bare-deriv one is not.

## §3.3 FIX + new finding (2026-06-20, opus audit): vacuity fixed, but tree comparison is DRIFT-FREE
The bare-deriv vacuity is FIXED: NeumannLinearDriftComparisonRegular (IntervalBFormLinearDriftComparisonRegular.lean)
uses genuine HasDerivAt + boundedness + Neumann ⟹ the spike counterexample is EXCLUDED (a spike isn't HasDerivAt-
differentiable), the interface is SATISFIABLE, and the corrected strict_pos_..._regular / bform_strictPos_..._regular
(IntervalBFormSquareHeatSubsolutionRegular.lean) are NON-VACUOUS conditionals. BUT the opus auditor found the
reflection route of_evenReflectionTreeData is BLOCKED for nonzero drift: the tree's ParabolicMaxPrinciple.comparison_
principle is PURE-REACTION whole-line (u_t=u_xx+g(u), value-only g, NO drift slot), and the interval equation has a
genuine drift B·w_x (slope-dependent) that no g(value) can carry — codex's own no_reaction_absorbs_nonzero_drift_at_
fixed_value PROVES the obstruction. So strictPos is honestly-conditional on a DRIFT comparison principle the tree
LACKS (the tree only has drift-free). The genuine remaining strictPos piece = a 1D Neumann-interval comparison/max
principle WITH first-order drift (a real PDE lemma, not in tree). The reflection-to-pure-reaction route is dead.

## §3.3 — drift comparison PROVED (genuine), strictPos "unconditional" label OVERSTATED (2026-06-20 opus audit)
neumann_interval_comparison_with_drift (IntervalBFormLinearDriftComparisonRegularDischarge.lean:758, ~290-line
proof) GENUINELY proves NeumannLinearDriftComparisonRegular UNCONDITIONALLY, axiom-clean [propext,Classical.choice,
Quot.sound]. The max-principle proof is VALID (audit-verified): drift B·z_x killed at the interior max via z_x=0
(space_deriv_eq_zero_at_Icc_interior_max), Neumann boundary maxima excluded by the ε·intervalBump (x(1-x)) perturbation
+ hsub/hsuper.neumann (deriv +ε>0 at x=0, −ε<0 at x=1), fixed-small-ε contradiction (no ε→0 gap). This is the real
advance — the drift comparison (which the tree lacked, pure-reaction only) is now a genuine unconditional theorem.
HONEST CORRECTION (codex over-labeled): bform_strictPos_..._unconditional (:1086) is NOT bare-unconditional — it still
CARRIES satisfiable-but-unassembled hyps: hbarrier_reg (NeumannLinearDriftSubSolutionRegularity for the squared
barrier — HasDerivAt dt/dx/dxx witnesses), hcalc (SquareHeatSubsolutionCalculus), hsuper (u classical super-solution),
hcoeff/hM/hseed. These are SATISFIABLE (the residual≤0 + endpoint-Neumann lemmas exist: squareHeatBarrier_subsolution_
residual_nonpos, intervalFullSemigroupOperator_neumann_at_zero/_at_one), NOT vacuous — but the barrier's full
regularity/calculus package is never ASSEMBLED. So strictPos = "closed modulo assembling hbarrier_reg+hcalc+hsuper for
the actual barrier/B-form solution" — genuine remaining work, the satisfiable regularity assembly. NOT vacuous, NOT
unconditional.

## §3.3 catch (2026-06-20 codex): the squared barrier is DEGENERATE at t=0 (semigroup S_N(0)=0, not id)
codex PROVED squareHeatBarrier M f 0 x = 0 (intervalFullSemigroupOperator 0 f = 0 — the heat kernel at EXACTLY
t=0 is degenerate; S_N(0)=id is only the t→0+ LIMIT). But SquareHeatSubsolutionCalculus.initial_eq required
= f² ⟹ forces f=0, contradicting the positive seed. So the barrier w=exp(-Mt)(S_N t f)² is DISCONTINUOUS at
t=0 (jumps 0→f² as t→0+) ⟹ NOT a classical sub-solution on the CLOSED [0,T]; the calculus initial_eq is
mis-framed. codex refused to fake it. FIX: apply the PROVED drift comparison neumann_interval_comparison_with_drift
on [t₀,T] for small t₀>0 (where w is regular and w(t₀)≈f² ≤ u(t₀)≈u₀ by continuity + the seed f²≤u₀), giving
w≤u on [t₀,T], hence strictPos u≥w>0 on [t₀,T]; then t₀→0 covers all t>0. (Equivalently: w(0)=0≤u₀ trivially
holds, but the barrier's t=0 DISCONTINUITY breaks the closed-strip classical-sub-solution regularity, so the
comparison must start at t₀>0.) The drift comparison itself is unaffected (proved for any regular sub/super on
the strip); only the initial-condition framing needs the t₀-restart.

## §3.3 CATCH #6 (2026-06-20 opus audit): hlocal bundle REGRESSED to the unsatisfiable LINEAR barrier
codex's IntervalBFormPositiveDatumLocalExistence.lean reduced the general-χ headline to PositiveDatumBFormLocalHyp =
(∀ datum, Nonempty PositiveDatumBFormLocalComponents) + hUniform. But the bundle's heat_lower_barrier field requires
exp(-Ct)·S_N(t)u₀ ≤ conjugatePicardLimit (the u₀-LINEAR lower bound), via bform_strictPos_of_semigroup_lower_barrier.
This is the UNSATISFIABLE linear barrier cron2 already rejected: the B-form Duhamel = S(t)u₀ − χ₀∫S(t−s)·chemDiv +…,
the signed nonlocal chemotaxis correction can push u below exp(-Ct)S_N u₀; exp(-Ct)S_N u₀ is NOT a sub-solution (no
−Cv absorbs the v_x-gradient drift — completing-the-square needs v², not v). No lemma derives it anywhere; it is
carried as an unproved hypothesis ⟹ the bundle is UNINHABITED ⟹ PositiveDatumBFormLocalHyp is FALSE ⟹ the headline
reduction is VACUOUS. REJECTED, NOT banked. FIX: rebuild the bundle using the banked SQUARED-barrier route
(bform_strictPos_of_square_heat_subsolution + the squared barrier squareHeatBarrier M f ≤ u PROVED from the drift
comparison + completing-the-square, seed-based + satisfiable) instead of the linear heat_lower_barrier. The other
bundle fields (Hpde, Henergy, regularity, hpde_v, neumann, initialTrace) are satisfiable. The squared-barrier route is
the genuine non-vacuous one - it is what I built (drift comparison PROVED, IntervalBFormStrictPosClosed.lean).

## §3.3 CATCH #7 (2026-06-20, ChatGPT cron + I OVERCLAIMED first): BNDualityAvailable (universal) is FALSE
The bundle's HbN field is BNDualityAvailable (IntervalBFormNegativePartCron2.lean:92) = the B_N-duality quantified
over ALL g,ψ : ℝ→ℝ (no integrability). I initially (wrongly) argued it is TRUE via a non-L¹-both-sides-0 case-split.
codex correctly objected (∂K bounded + sign-changing ⟹ ∂K·g can be integrable even for non-L¹ g, so B_N g need not
be 0), and ChatGPT cron gave an explicit COUNTEREXAMPLE: g smooth integrable, ψ=|w−1/2|^{−3/2} (non-L¹). Then
S_N(t)ψ=0 (non-integrable→Lean 0) so RHS=0; but B_N(t)g·ψ ~ C|x−1/2|^{−1/2} near 1/2 is integrable & positive so
LHS>0 ≠ RHS. ⟹ BNDualityAvailable is FALSE. Therefore the bundle carrying HbN:BNDualityAvailable is UNINHABITED ⟹
the banked headline (c071bb5, audit-claimed non-vacuous) is actually VACUOUS via HbN. The prior non-vacuity audit
MISSED the universal quantification of HbN (it scrutinized the linear barrier + main fields, assumed BNDualityAvailable
was a "standard duality"). LESSON: verify-don't-transcribe applies to MY OWN analysis — I overclaimed "it's true";
firing the ChatGPT cross-check is what caught it. FIX: restrict HbN to the regular duality bN_duality_regular (needs
IntegrableOn g, IntegrableOn ψ — TRUE, proved), applied to the SPECIFIC chemotaxis flux Q (bounded/integrable on
[0,1]) + the negative-part test (bounded). Re-thread through the energy core + the bundle. The regular duality is the
genuine non-vacuous one.

## §3.3 NON-CATCH #8 (2026-06-20, ChatGPT cron3 + verify-don't-transcribe SAVED IT): Neumann BC is FAITHFUL
ChatGPT cron3 raised the most dangerous-looking concern of the campaign: the time-integrated B-Duhamel chemotaxis leg
W_B(t,x) = (-χ₀)∫₀ᵗ B_N(t-s) F(s) (x) ds (intervalConjugateDuhamelMap, IntervalConjugateDuhamelMap.lean:298). Per-lag,
B_N(r)F is a cosine series → ∂ₓ=0 at the boundary (intervalConjugate_normalDeriv_zero, carries SATISFIABLE DifferentiableAt
hyps, smooth for r>0). BUT ∂ₓ and ∫₀ᵗds do NOT commute across the singular lag r=t-s↓0. ChatGPT's decisive example Q≡1:
each lag has zero boundary derivative, yet ∫ limit = ½-|x| has a CORNER at x=0 (one-sided deriv -1≠0). General formula:
W_{B,x}(t,0) = -Q(t,0); homogeneous Neumann holds only if Q|∂ = 0. ChatGPT (wrongly) assumed B_N acts on raw Q=u^m
(boundary-NONZERO → corner → BC FAILS). RESOLUTION via source: B_N actually acts on chemFluxLifted = u·v_x/(1+v)^β
(IntervalGradientDuhamelMap.lean:47), NOT u^m. The resolver gradient v_x = resolverGradReal is a SINE series
Σ coeff·(-kπ sin(kπx)) (IntervalDomainL2StaticVDifference.lean:748) and resolverGradReal_zero PROVES it vanishes at x=0,1
(IntervalDomainL2UEnergyCombine.lean:71,81), C¹ (line 387). ⟹ chemFlux(t,0)=chemFlux(t,1)=0 — EXACTLY the Q|∂=0
compatibility ChatGPT's own §7 flagged as required. Corner absent ⟹ Neumann BC genuinely holds. Two more confirmations:
(a) normalDeriv = derivWithin (Ici 0 / Iic 1) one-sided physical derivative (IntervalDomain.lean:2943), NOT vacuous-at-corner
two-sided Mathlib deriv — the field is HONEST. (b) Interior PDE source is ∂ₓ(flux) = B_N's zero-time trace, so Correction-1
(forcing-shape) doesn't bite either. VERDICT: NOT a faithfulness bug; construction faithful; ChatGPT's general warning is
correct but used the wrong Q. GENUINE TAKEAWAY: the bundle's `neumann` field (IntervalBFormPositiveDatumLocalExistenceSqRegular.lean:79)
is CARRIED, satisfiable ONLY because chemFlux|∂=0 (resolverGradReal_zero) — a generic-Q audit would call it unsatisfiable.
Non-vacuity audits MUST cite resolverGradReal_zero as the witness for this field. Remaining real atom: DISCHARGE the neumann
field as a theorem (prove ∂ₓ∫₀ᵗB_N(t-s)F ds = 0 at boundary FROM F|∂=0, justifying the ∂ₓ/∫ds interchange via DCT — the
boundary-vanishing is exactly what kills the r↓0 obstruction). Dispatched to cron3. LESSON: verify-don't-transcribe against
the ACTUAL flux definition — ChatGPT's abstract Q=u^m would have condemned a faithful construction.

## §3.3 CATCH #9 (2026-06-20, opus adversarial audit + I MISSED IT in 5f8ed35): Hbridge UNSATISFIABLE ⟹ headline VACUOUS
SAME SHAPE AS CATCH #7. The general-chi headline paper2_theorem_1_1_general_chi_bformSq_regular (banked 5f8ed35, which I
REPORTED as "audit-confirmed non-vacuous via 20-field enumeration") is ACTUALLY VACUOUS. The bundle
PositiveDatumBFormLocalComponentsSqRegular (IntervalBFormPositiveDatumLocalExistenceSqRegular.lean:44) carries
Hbridge : TruncatedConjugateLimitBridge (IntervalBFormCron2Concrete.lean:26) which asserts POINTWISE EQUALITY
conjugatePicardLimit p u₀ DB.T = truncatedConjugatePicardLimit p u₀ DT.T. BUT: conjugatePicardLimit is the fixed point of
intervalConjugateDuhamelMap (IntervalConjugateDuhamelMap.lean:295) propagating the TRUE cell flux chemFluxLifted =
u·v_x/(1+v)^β (IntervalGradientDuhamelMap.lean:47, v-DEPENDENT); truncatedConjugatePicardLimit is the fixed point of
truncatedConjugateDuhamelMap (IntervalBFormNegativePartCron2.lean:101) propagating truncatedChemFluxLifted = (u_+)^m
(NegativePartCron2.lean:32, NO v-dependence). Two DIFFERENT fluxes ⟹ two DIFFERENT fixed points ⟹ Hbridge (their equality)
is UNSATISFIABLE (would need u·v_x/(1+v)^β = (u_+)^m, i.e. v_x/(1+v)^β = u^{m-1}, a non-generic algebraic constraint).
EVIDENCE: grep TruncatedConjugateLimitBridge = 8 occurrences, ALL consumer/hypothesis positions, ZERO producers (never
constructed/proven). Independent hostile opus audit (default-assume-bug) verified all 5 tasks against source → BUG CONFIRMED.
The nonnegativity (negativePart_zero → bform_negativePart_zero_of_concrete_truncated_regular_energyCore, RegularNegativePartEnergy.lean:240,
uses Hbridge to transfer U_T≥0 to U) is the dependency path. The prior "exhaustive 20-field" audit (ae18fdbc) MISSED Hbridge's
unsatisfiability exactly as the pre-catch-7 audit missed HbN — it checked each field's TYPE, not whether the carried
EQUALITY/quantification is SATISFIABLE. FIX: the FAITHFUL truncation is truncatedChemFluxLifted := u_+·v_x/(1+v)^β (truncate
the u-FACTOR of the cell flux), NOT (u_+)^m. It (a) vanishes on {u<0} (u_+=0 ⟹ negative-part cancellation still holds) AND
(b) EQUALS the full cell flux on {u≥0} (u_+=u ⟹ Hbridge dischargeable: once U≥0, U solves the truncated eq too). The code's
(u_+)^m has property (a) but NOT (b), which is why the bridge is broken. META-LESSON (bake into playbook §3.3): a "field-by-field
non-vacuity audit" MUST, for every carried field that is an EQUALITY or a ∀-statement, exhibit a SATISFYING WITNESS (or cite a
producer theorem), not merely confirm the field's type is inhabited-in-principle. Two catches (#7 HbN universal-false, #9 Hbridge
equality-unsatisfiable) had this identical miss. Enumerating field TYPES ≠ enumerating field SATISFIABILITY.

### CATCH #9 RESOLVED (2026-06-20, commit 9a2b056, build+axioms+opus verified)
codex implemented the fix: truncatedChemFluxLifted := positivePart(u)·v_x/(1+v)^β (NegativePartCron2.lean:31).
NEW producer truncatedConjugateLimitBridge_of_faithful_truncation (FaithfulBridgeProducer.lean:133) DERIVES the bridge
from TruncatedConjugateLimitBridgeProducerData via: truncated limit nonneg → maps agree on nonneg
(truncatedConjugateDuhamelMap_eq_intervalConjugateDuhamelMap_of_nonneg, PROVED, uses positivePart(u)=u on {u≥0} for BOTH
chemotaxis and logistic) → uT is a full-map fixed point → full Picard uniqueness (IntervalConjugatePicardUniqueness.lean,
contraction K^n→0, PROVED) → uT = conjugatePicardLimit. Bundle now carries HbridgeData (SATISFIABLE) not raw Hbridge.
THE FLIP: the carried hypothesis went UNSATISFIABLE → SATISFIABLE, so the headline went VACUOUS → NON-VACUOUS. Build clean
(8415 jobs RC=0), #print axioms = [propext, Classical.choice, Quot.sound]. Independent hostile opus audit confirmed all
machinery PROVED (no sorry); it flagged truncated_nonneg as "carried not produced" and called it "vacuity moved down" —
DISPOSITION (Fable disposes): that framing is WRONG. truncated_nonneg (truncatedConjugatePicardLimit ≥ 0) is a SATISFIABLE
TRUE fact (the negative-part estimate endpoint; faithful flux vanishes on {u<0} so the cancellation gives nonneg, self-
contained no circularity), so it is CONDITIONALITY (like every other carried bundle field Hpde/Henergy/neumann/...), NOT
vacuity. Unsatisfiable-carried = vacuous (#9); satisfiable-but-undischarged = conditional (normal). REMAINING ATOM toward
UNCONDITIONAL: a producer truncatedConjugateLimitBridgeProducerData_of_energyCore constructing HbridgeData (incl.
truncated_nonneg) from the negative-part energy core — the pieces (cancellation) are proved, the assembly is the work.
