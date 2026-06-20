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
- 🟡→IN PROGRESS `Hpde` HasBFormSpectralPdeAgreement — interior PDE faithfulness; **codex grinding now** (discharge to named standard heat-semigroup facts, zero-time-trace route, no circularity)
- 🟡 `DT` TruncatedConjugateMildExistenceData — truncated Picard existence
- ✅→🟡 `HbridgeData`/`HtruncatedEnergy` — bridge DISCHARGED via producer (9a2b056); `truncated_nonneg` DISCHARGED from the standard negative-part energy core via Gronwall (5db37e7, opus-verified GENUINE). Now carries the DEEPER `TruncatedNegativePartEnergyCoreRegularData`; its `semigroup_weak` field = the next atom (**codex grinding now**, duhamel skeleton). Remaining sub-fields: weak energy estimate, Sobolev plumbing (energy_cont/has_deriv/integrable), zero-energy→nonneg — standard parabolic facts approaching Mathlib gaps.
- ✅ `A/Dbar/M/hM` coefficient bounds
- 🟡 `hstrip` SquareHeatRestartStripData — coefficient regularity + hsuper for strictPos
- 🟡 `regularity` classical C² — from cosine representation
- 🟡 `hpde_v` elliptic resolver (chemical v) — resolver machinery
- 🟡 `neumann` normalDeriv u = normalDeriv v = 0 — satisfiable via `resolverGradReal_zero` (flux|∂=0); **skeleton ready** (/tmp/gpt_neudis.txt: F|∂=0 → ∂ₓ/∫ds interchange)
- 🟡 `initialTrace` InitialTrace — B-form initial approach as t→0
- ✅ `semigroup_weak` (TruncatedMildSemigroupWeakAfterBNDualityOn) — DISCHARGED to NAMED standard heat-semigroup facts pack (e0d9038, opus HONEST-BOTTOM): t^{-1/2} gradient bound, Lebesgue endpoint, DCT majorant, semigroup form identity, Duhamel differentiation (chemotaxis gated on restricted duality). Honest Mathlib-gap bottom.
- 🟡 `hUniform` (F1) IntervalDomainUniformLocalExistence — textbook uniform continuation

## Scoreboard
Non-vacuous headline: ✅ (conditional). Discharged cross-cutting cores: ~9 ✅.
Bundle fields toward unconditional: 0/13 fully discharged, 1 in progress (HbridgeData), 3 with ChatGPT skeletons ready.
Distance = the 13 bundle atoms above (each may expand 1–2 sub-layers when pushed), NOT a time estimate.

Last verified: 2026-06-20, headline build 8415 jobs RC=0, axioms clean. codex grinding HbridgeData/truncated_nonneg.
