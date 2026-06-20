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
