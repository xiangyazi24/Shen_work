# Paper 2 (Chen–Ruau–Shen, bounded-domain boundedness) — formalization atom board

Headline: `paper2_theorem_1_1_general_chi_bformSq_regular`
(ShenWork/Paper2/IntervalBFormPositiveDatumLocalExistenceSqRegular.lean:244,
namespace `ShenWork.Paper2.BFormPositiveDatumLocalSq`).

Status: **NON-VACUOUS, axiom-clean** (`[propext, Classical.choice, Quot.sound]`), conditional on the bundle
`PositiveDatumBFormLocalComponentsSqRegular` (all fields SATISFIABLE) + `hUniform` (F1). Build clean (8415 jobs).
Faithfulness anchor: `IsPaper2ClassicalSolution` (Statements.lean:70) — full cell-flux PDE + Neumann BC.

Markers: ✅ discharged sorry-free & axiom-clean · 🟡 carried-SATISFIABLE (witness known, not yet a producer theorem)
· ⬜ open/unaudited · ❌ was unsatisfiable (fixed).

## Cross-cutting (proved, reusable)
- ✅ Conjugate-kernel B-form map + Neumann cosine-evenness per-lag (IntervalConjugateDuhamelMap.lean)
- ✅ Drift-comparison max-principle `neumann_interval_comparison_with_drift` (the GOLD, axiom-clean)
- ✅ Squared-barrier strictPos route (completing-the-square, t0-restart)
- ✅ Negative-part disjoint-support cancellation (now on faithful flux, IntervalBFormCron2NegativePartEnergy.lean)
- ✅ Coefficient bounds A/Dbar/M + resolver positivity (4d02208)
- ✅ `resolverGradReal_zero` (flux vanishes at boundary — Neumann faithfulness witness, catch #8)
- ✅ Full Picard uniqueness (contraction K^n→0, IntervalConjugatePicardUniqueness.lean, catch #9 fix)
- ✅ Faithful truncation + maps-agree-on-nonneg + bridge PRODUCER (9a2b056, catch #9 fix)
- ✅ `bN_duality_regular` (restricted, integrable inputs) — the genuine non-vacuous duality (catch #7 fix)
- ❌→✅ catch #7 (HbN universal duality FALSE), catch #9 (Hbridge equality unsatisfiable) — both FIXED

## Bundle fields = the atoms (toward UNCONDITIONAL)
- 🟡 `DB` ConjugateMildExistenceData — local Picard existence/contraction data
- 🟡 `Hinf` ConjugatePicardInfThresholdData — inf-threshold for strictPos floor
- 🟡 `hsmall` — smallness/threshold hyp
- ✅ `Hpde` HasBFormSpectralPdeAgreement — interior PDE faithfulness GENUINELY discharged (aefd8fb, opus GENUINE-DISCHARGE after v1 re-wrapper REJECTED): exists_data derived via real construction (bForm_restart_of_global_cosine + coeff bounds + eigenvalue summability) from the carried reconstruction implication whose premises are the 4 load-bearing analytic facts (cosine-series convergence, zero-time trace, Duhamel-deriv identity, semigroup generator). Honest Mathlib-gap bottom.
- 🟡 `DT` TruncatedConjugateMildExistenceData — truncated Picard existence
- ✅→🟡 `HbridgeData`/`HtruncatedEnergy` — bridge DISCHARGED via producer (9a2b056); `truncated_nonneg` DISCHARGED from the standard negative-part energy core via Gronwall (5db37e7, opus-verified GENUINE). Now carries the DEEPER `TruncatedNegativePartEnergyCoreRegularData`; its `semigroup_weak` field = the next atom (**codex grinding now**, duhamel skeleton). Remaining sub-fields: weak energy estimate, Sobolev plumbing (energy_cont/has_deriv/integrable), zero-energy→nonneg — standard parabolic facts approaching Mathlib gaps.
- ✅ `A/Dbar/M/hM` coefficient bounds — now CONCRETE (bformConcrete* from DB), free fields removed (09da672)
- ✅(partial) `hstrip` — GENUINELY discharged to minimal hLinearStripCore (09da672, opus GENUINE-PARTIAL): free A/Dbar/M/drift/react/hstrip fields REMOVED, replaced with concrete bformConcrete* + proven bounds; carries only hLinearStripCore (concrete coeff regularity + IsClassicalNeumannLinearDriftSuperSolution). Honest carried gap = the super-solution residual≥0 (TRUE, but nonlinear→linear residual bridge is a Mathlib/library gap — logistic-only react can't cancel the flux-derivative term). Non-redundant. Bonus: removed HbN escape hatch from banked-concrete.
- ✅(redundant) `regularity` classical C² — GENUINE reduction to BFormDirectFrontier (21e2882, opus GENUINE-REDUCTION): field removed, derived via existing 7-component lemma intervalConjugatePicardLimit_classicalRegularity_direct. DEFECT (opus-flagged §2.6): regularityFrontier.bank/hTimeNhd/hResolverData DUPLICATE the spectral substrate in HpdeFacts + neumannFacts. Not unsound/unfaithful — minimality only.
- ✅ `hpde_v` elliptic resolver — GENUINELY discharged + FIELD REMOVED (e922ec2, opus GENUINE-DISCHARGE HIGH + proof-term): elliptic identity 0=Δv−μv+νu^γ derived on-the-fly (obtain source-decay → resolver Laplacian bridge + coefficient-form elliptic identity + cosine source reconstruction → rw+ring). Only carried fact = SourceCoeffQuadraticDecay (satisfiable + dischargeable via sourceCoeffQuadraticDecay_of_solution).
- ✅ `neumann` normalDeriv u = normalDeriv v = 0 — GENUINELY discharged (148ccca, opus GENUINE-DISCHARGE + proof-term read): u via 3-leg assembly (chemFlux-vanishing from resolverGradReal_zero → interchange license → ring), v via HasDerivWithinAt from resolverGradReal_zero/_one. Only carried Mathlib-gap fact = the DCT interchange license (load-bearing).
- 🟡 `initialTrace` InitialTrace — B-form initial approach as t→0
- ✅ `semigroup_weak` (TruncatedMildSemigroupWeakAfterBNDualityOn) — DISCHARGED to NAMED standard heat-semigroup facts pack (e0d9038, opus HONEST-BOTTOM): t^{-1/2} gradient bound, Lebesgue endpoint, DCT majorant, semigroup form identity, Duhamel differentiation (chemotaxis gated on restricted duality). Honest Mathlib-gap bottom.
- 🟡 `hUniform` (F1) IntervalDomainUniformLocalExistence — textbook uniform continuation

## Scoreboard
Non-vacuous headline: ✅ (conditional). Discharged cross-cutting cores: ~9 ✅.
Bundle fields toward unconditional: 0/13 fully discharged, 1 in progress (HbridgeData), 3 with ChatGPT skeletons ready.
Distance = the 13 bundle atoms above (each may expand 1–2 sub-layers when pushed), NOT a time estimate.

## Cleanup TODO (minimality, not faithfulness)
- **Unify the carried spectral/resolver substrate**: regularityFrontier (Type-level bank/hTimeNhd/hResolverData) duplicates
  the spectral cosine-agreement reconstructible from HpdeFacts + the resolver data in neumannFacts. Carry the Type-level
  frontier ONCE and derive HpdeFacts/hpde_u + hpde_v + regularity from it. Orthogonal to faithfulness (headline already
  non-vacuous + axiom-clean); do as a minimization pass after the remaining atoms (DB/Hinf/hstrip/F1) are discharged.

Last verified: 2026-06-20, headline build 8426 jobs RC=0, axioms [propext,Classical.choice,Quot.sound].
Genuine discharges banked this run: truncated_nonneg, semigroup_weak, Hpde (after re-wrapper bounce), neumann, hpde_v
(field removed), regularity (genuine but redundant). Remaining bundle atoms: DB, Hinf, hstrip, energy-core Sobolev fields, F1.
