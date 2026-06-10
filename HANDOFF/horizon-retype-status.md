# ===================================================================
# FINAL WIRING COMPLETE 2026-06-10 — capstone sorryAx ELIMINATED.
# ===================================================================
#
# Both capstones now depend on EXACTLY [propext, Classical.choice, Quot.sound]
# — NO sorryAx — verified by remote `#print axioms` on uisai2:/dev/shm/shen_work:
#
#   ShenWork.Paper2.Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_unconditional
#       depends on axioms: [propext, Classical.choice, Quot.sound]
#   ShenWork.IntervalPicardTowerSupply.paper2_theorem_1_1_chiZero_from_coneSupply
#       depends on axioms: [propext, Classical.choice, Quot.sound]
#
# Full remote `lake build ShenWork` = 8547 jobs, EXIT 0.  0 sorry / 0 admit /
# 0 custom axiom / 0 native_decide in the edited files (only doc-comment mentions).
#
# WIRING ROUTE (the broken call site at CoreProvider:724 is now closed):
#   The grown `picardIterateResidualData_of_core` (hsrc0 + hu₀_bound params) is now
#   fed a REAL `hsrc0`, built NON-circularly at the call site via the new helper
#   `HresWiring.duhamelSourceBddOn_of_core` (spatial Stage-A `hcontP` route —
#   `patchedSource_coeff_continuousOn_of_iterate_data` — which NEVER appeals to the
#   patched-slice sup-norm time continuity `hsliceTC`, so feeding the result into
#   `hsliceTC_of_mild_restart` is non-circular).  `hu₀_bound` is the D-side
#   `u₀_cosineCoeff_bound hu₀.admissible.2` (no new hypothesis).
#
# HYPOTHESIS GROWTH (smallest honest growth, all discharged):
#   * NEW helper `HresWiring.duhamelSourceBddOn_of_core` (IntervalDomainHresWiring.lean):
#     PicardIterateResidualCore + hiter_cont (cosine-coeff TIME continuity) → hsrc0.
#     Ingredients: datum bound (datum_source_coeff_bound), n-uniform envelope
#     (source_coeff_window_uniform C.Wdata, via .choose since target is Type),
#     hconv (picardIter_logisticCoeff_tendsto_limit_of_facts C.hFacts), Stage-A hcontP
#     (patched ball/nn from D + hiter_cont).  → duhamelSourceBddOn_of_iterates.
#   * `reducedLimitRegularityInputs_of_wdata` / `restartAndFrontierCore_of_wdata`
#     (CoreProvider) gained ONE param `hiter_cont` (the cosine-coeff time continuity),
#     and build hsrc0/hu₀_bound inline.
#   * NEW provider type `IterCoeffTimeContProvider p` (CoreProvider): the per-datum
#     cosine-coeff TIME continuity — the SINGLE ingredient the spatial cone does not
#     return.  The capstone `paper2_theorem_1_1_chiZero_unconditional` and both feeders
#     (`quantitativeLocalExistence_chiZero_wdata`, `hMildLocal_chi0_zero_of_wdata`)
#     gained a `Hiter : IterCoeffTimeContProvider p` hypothesis BEFORE `HWdata`.
#   * DISCHARGE in `from_coneSupply` (TowerSupply, signature UNCHANGED): new
#     `iterCoeffTimeCont_of_coneSupply` builds `Hiter` from `HCone` via
#     `coneTowerSupply` (→ TowerInputs) + `hiter_cont_of_tower` (reads time continuity
#     off the tower's canonical logistic-source C¹ packages `H.hsrc0 n`).  NO new field
#     of TowerConeAnalyticResidual was needed — the tower bundle already carries hsrc0.
#
# RESIDUAL FIELD LIST (from_coneSupply's HCone bundle, UNCHANGED):
#   Σ' M A₂, (0≤M) ×' (D.T≤1) ×' (0≤A₂) ×' GateCondition ×' Continuous u₀ ×'
#   hu₀_bound ×' hpos ×' hcontSlice ×' hball ×' TowerConeAnalyticResidual.
#   TowerConeAnalyticResidual fields: hsrc0, hL_cont, hG1all, hG2base,
#   adot/hadot_deriv/hadot_cont/adotBound/hadot_bound.
#
# FILES TOUCHED: IntervalDomainHresWiring.lean (new helper + 3 imports),
#   IntervalDomainThm11ChiZeroCoreProvider.lean (provider type + 3 threaded sigs +
#   capstone), IntervalPicardTowerSupply.lean (discharge helper + from_coneSupply).
#   No just-landed slice/tower files needed signature changes.
#
# ===================================================================
#
# hinterior CLOSED 2026-06-10 — spectral restart route, 0 sorry in slice chain.
#
# The last `sorry` (hinterior inside mildSlice_restart_bound,
# IntervalPicardLimitSliceTimeContinuity.lean:241) is GONE — replaced by a real
# proof via the now-non-circular spectral restart route.
#
# NEW FILES (both 0-sorry, lake env lean EXIT 0 on uisai2):
#  1. ShenWork/Paper2/IntervalRestartSeriesLipschitz.lean
#     The analytic engine: restartSeries_sup_diff_le proves
#       |∑ₙ (restartDuhamelCoeff a₀ a x − …(y)) · cosineMode n z| ≤ |x−y|·C
#     uniformly in z, via: MVT exp diff (abs_exp_diff_le), λ-cancelling Duhamel
#     bound (abs_duhamelSpectralCoeff_diff_le, 2|x−y|env), heat-damped homogeneous
#     sum (∑λe^{-λm} via unitIntervalCosineEigenvalue_mul_exp_summable), and
#     per-horizon summability (restartCosineSeries_summable via
#     exp_neg_eigenvalue_summable).
#  2. ShenWork/Paper2/IntervalRestartSliceLipschitz.lean
#     The wiring: restartSlice_sup_lipschitz takes hsrc0 (DuhamelSourceBddOn),
#     runs picardLimitRestart_general_of_subtypeCont at fixed base τ=s₀/2 for
#     horizons s and s₀, subtracts the two cosine series, applies the engine →
#     sup_y|D.u s y − D.u s₀ y| ≤ |s−s₀|·C in the interior regime s ≥ 3s₀/4.
#     hinterior_of_src0 packages it as the exact hinterior existential (δ₀ =
#     min(s₀/4, ε/(C+1))).
#
# GROWN SIGNATURES (iterate-side hypotheses, per Signature policy):
#   mildSlice_restart_bound, patchedSlice_timeContinuousAt_pos,
#   hsliceTC_of_mild_restart, and HresWiring.picardIterateResidualData_of_core
#   all gained TWO params:
#     hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ D.u) D.T   [iterate-side]
#     hu₀_bound : ∀ k, |cosineCoeffs (lift u₀) k| ≤ M₀          [D-side, satisfiable
#                 from Continuous u₀ via u₀_cosineCoeff_bound]
#
# REMAINING WIRING (in the FORBIDDEN capstone file — STOPPED at layer below):
#   IntervalDomainThm11ChiZeroCoreProvider.lean:724, inside
#   reducedLimitRegularityInputs_of_wdata, the call
#     picardIterateResidualData_of_core hχ0 hu₀.admissible.2 hDu (core…)
#   now needs hsrc0 and hu₀_bound inserted between hDu and the core arg.
#   PRODUCER for hsrc0: IntervalPicardLimitBddBootstrap.duhamelSourceBddOn_of_iterates,
#   fed by Stage-A hcontP (IntervalPicardLimitCoeffTimeCont.
#   patchedSource_coeff_continuousOn_of_iterate_data) + the tower-produced
#   hiter_cont (cosine-coeff TIME continuity) and henv_iter (n-uniform envelope) —
#   these two are NOT carried by the spatial HasContinuousSlices core; they come
#   from IntervalPicardTowerProjection (other agent). hconv from hconv_of_residual.
#   PRODUCER for hu₀_bound: u₀_cosineCoeff_bound hu₀.admissible.2 (or .1/.2 fields).
#   Once the capstone supplies these two args (threading hsrc0 from the tower via
#   duhamelSourceBddOn_of_iterates), the slice chain's sorryAx vanishes capstone-wide.
#
# ---- prior status below ----
# TOWER LANDED 2026-06-10 ~17:10 (latest = 3aaeab2 + self-feeding pass in flight)
#
# Stage 1 (lemma layer, 4 files) + Stage 2 (tower zero/succ/all + projections)
# + ENDGAME (towerInputs_of_cone, axiom-clean) ALL COMMITTED.
# New corollary paper2_theorem_1_1_chiZero_from_coneSupply:
#   regime constants + ONE named package TowerConeAnalyticResidual
#   (= hub/hsrc0/hL_cont/hG1all/hG2base/witness/hM1/adot-K1 legs).
# towerInputs_of_cone: [propext, Classical.choice, Quot.sound] — CLEAN.
# Capstone sorryAx = inherited hinterior only. Full build 8544 green.
#
# IN FLIGHT: the self-feeding strengthening (tower_succ derives the
# per-level witness/source/K1 data from L.srcWin per the original verdict
# design, instead of taking them as inputs) — expected to shrink
# TowerConeAnalyticResidual to the truly-external legs (homogeneous G2
# base + kernel-G1 integrability inputs + ball, mostly cone-returned).
#
# REMAINING AFTER THAT: hinterior (the fixed-base restart bound in
# IntervalPicardLimitSliceTimeContinuity — route: the spectral restart via
# limit-side BddOn inputs projected from the tower, see
# chatgpt-hslicetc-verdict.md + the bonus item limitBddOn_inputs_of_tower
# which stage 2 did NOT deliver — still open).
#
# ---- earlier snapshots below ----
# CAMPAIGN STATE 2026-06-10 ~15:00 (latest = df91175, build 8544 green)
#
# Capstone paper2_theorem_1_1_chiZero_unconditional final form:
#   regime constants (chi0=0, a>0, b>0, alpha>=1, gamma>=1) + HresCore
#   axioms: [propext, sorryAx, Classical.choice, Quot.sound]
#
# HresCore = {hFacts (cone-returned, round 2), hcont_iter (cone-returned,
# round 2), Wdata (OPEN)}. hsliceTC + hLcont_lim discharged universally;
# GateCondition fully SOLVED (exists_gate_solution, explicit numerics) and
# cone round 4 returns it discharged; strict iterate positivity (round 3);
# hprofile_joint DISCHARGED; hDu threading exact (cone-internal horizon
# shrink, no EqOn needed).
#
# THE ONE ROOT that remains (two visible holes, same root):
# 1. Wdata — the per-level UniformWiring analytic stack (per-iterate
#    source packages hsrc0/srcsigma/hdecay/hsigcont + K1 quadruples +
#    joint measurability, mutually recursive with representation triples).
#    Route: IntervalDomainHresWiring header.
# 2. hinterior (inside mildSlice_restart_bound) — the interior-regime slice
#    continuity, blocked on the SAME stack: either the semigroup-out-of-
#    integral interchange tower (absent from the repo) or the limit-side
#    BddOn producer (= the iterate bootstrap inputs = Wdata-class).
# NEXT CAMPAIGN: build the per-level source-package production tower once;
# both holes close together; then sorryAx vanishes and the capstone carries
# regime constants + nothing.
#
# ---- earlier snapshots below ----
# CAMPAIGN CLOSED 2026-06-10 ~13:00 — sorryAx ELIMINATED (commit ee8fd7e).
#
# paper2_theorem_1_1_chiZero_unconditional depends on
# [propext, Classical.choice, Quot.sound] — independently verified.
# Repo-wide Paper2: 0 sorry / 0 admit / 0 custom axiom / 0 native_decide.
# Full build 8540 jobs green. 40+ commits, all pushed.
#
# The honest residue: the capstone carries ONE explicitly-typed hypothesis
# Hres : PicardIterateResidualData p u₀ D (IntervalDomainThm11ChiZeroResidual)
# bundling iterate-side facts about the canonical Picard limit:
# MildExistenceData + iterate/limit [0,1]-continuity (feeds hconv),
# per-window IterateWindowC2Data (feeds the source envelope), and hsliceTC
# (patched-slice sup-norm time continuity). All fields are TRUE of the cone
# construction's Picard limit; discharge routes documented in the file.
# NEXT CAMPAIGN: discharge Hres from the cone construction's internal
# iterate data (IntervalMildPicard / cone files / picardIterateUniformData_all
# UniformWiring).
#
# ---- earlier ledger snapshots below ----
# UPDATE 2026-06-10 ~12:10 — both walls dissolved; 7 routed residuals.
#
# hsrc0F: FILLED via the iterate-side bootstrap producer (ce2ba39) — the
# Provider circularity broken (hM direct from D fields; env via le_of_tendsto
# from n-uniform iterate envelopes). Residuals: R-src0F-1a/1b (trivial datum
# bounds), R-src0F-2 (n-uniform iterate window envelope — THE analytic core),
# R-src0F-3 (D.u = picardLimit mild-uniqueness bridge; coefficient convergence
# ALREADY PROVED in IntervalPicardLimitCoeffConv), R-src0F-4 (hcontP — proof
# sketch in chatgpt-hvsrc-and-inclusive-verdicts.md).
# Hvsrc: field retyped per-t0 (HasResolverDirectSpectralData exists-inside-
# forall, 6 consumers re-proved) + clamped power-source witness wired
# (e2211ee). Residuals: R-Hvsrc-1 (window power decay), R-Hvsrc-2 (power K1,
# clone of the logistic spine, HasDerivAt.rpow_const Or.inl positivity).
#
# ZERO unsatisfiable-typed sorries remain anywhere in the chain.
# Full build 8535 jobs green, pushed through e2211ee.
#
# UPDATE 2026-06-10 ~00:20 — NIGHT FINAL: sorry 21 → 2. Build 8530 jobs green.
#
# Closed since the 00:15 note: restart packaging BOTH killed (2069c27 —
# the target structure was per-t₀ all along; only the old producer was
# global-diseased); Hvsrc resolved as a documented FINDING (2f96ba3 — the
# ledger field demands global TimeC1, but picardLimit is junk 0 off (0,T]
# so hderiv at s=T is FALSE; the would-be filler + the DuhamelSourceTimeC1On
# retype plan are in IntervalResolverSourceTimeC1.lean's header).
#
# THE LAST 2 (both Provider, both with complete designs):
# 1. hsrc0F — BddOn patched-family migration (producer 0-sorry in
#    IntervalPicardLimitBddProducer; design hsrc0-splitenv-design.md;
#    work: patched↔canonical adapter + ledger field swap + weak-chain
#    consumer entry swap to the Bdd lemmas)
# 2. Hvsrc — DuhamelSourceTimeC1On retype through the resolver consumer
#    chain (IntervalResolverDirectTimeRegularity →
#    IntervalMildRegularityFrontierAssembly → ledgers), then apply the
#    existing producer via the soft-clamp witness.
#
# ---- earlier ledger snapshots ----
# UPDATE 2026-06-10 ~00:15 — FINAL ledger: sorry 21 → 4.
#
# K1 CLOSED: k1_quadruple_weak (BddOn spine, fixed-split majorant) +
# _of_subtypeCont variant, wired into the Provider's four K1 fields AND the
# hpde_u bundle (commits 55a52c0, 0417630). Full build 8528 jobs green.
#
# Remaining 4:
# 1. Provider hsrc0F — BddOn patched-family migration (design:
#    hsrc0-splitenv-design.md; producer DONE in IntervalPicardLimitBddProducer;
#    remaining: adapter patched↔canonical + ledger field/consumer swap)
# 2. Provider Hvsrc — resolver power-source TimeC1
#    (powerSource_intervalWeakH2Neumann is the base)
# 3. restartData_of_inputs (MildLocalChi0)
# 4. hasRestartData_of_subtypeCont (ConstExtendAdapter)
#
# ---- earlier same-night notes ----
# UPDATE 2026-06-09 ~23:45 — sorry 21 → 8, all satisfiable types.
#
# Additional commits: 84dc5ff Hu_of_reduced via subtype variant (-1),
# 206f604 DuhamelSourceBddOn + K1 R2 plan, b051d20 hpde_u wired,
# c71ea2b BddOn producer (patched family, 0s), 38b45eb PdeU surrogate
# retype (killed the false lift-continuity field), bed2dff K1 machinery
# (WARNING: k1_quadruple circular — input hypotheses = conclusion; weak-spine
# fix agent dispatched: c_k' = −λc_k + A_k from the weak package via
# product rule + FTC, envelope via Bdd split + windowEnv).
#
# Remaining 8: Provider hsrc0F (BddOn migration pass: ledger field
# DuhamelSourceL1ContOn → DuhamelSourceBddOn patched family + adapter
# patched↔canonical on (0,τ] + weak-chain consumer entry swap — design in
# hsrc0-splitenv-design.md; the Bdd file already has consumer lemmas);
# K1 quadruple ×4 (weak-spine fix in flight) + the K1 bundle in PdeUWiring's
# hpde_u (same data, wire adottOf once weak spine lands);
# Hvsrc (powerSource_intervalWeakH2Neumann base); restartData_of_inputs +
# hasRestartData_of_subtypeCont (restart packaging via ConstExtendAdapter).
#
# ---- earlier notes ----
# Horizon retype — COMPLETE (2026-06-09 ~22:45). Sections below are the
# historical resume notes; current state:
#
# Committed (all build-green, 8521 jobs): c9b3f6b horizon retype,
# 440ebc6 Hu_of_restart_localized, 583b6b5 SpectralSubtypeAdapter,
# 9d93703 K2 producers, 3d3afd0 ledger V2 (-10 sorry), 15a550b K2 wiring (-2).
#
# Remaining sorries (10 total, ALL satisfiable types now):
# Provider (7): hsrc0F + adott/hderivt/hadotcontt/hMdott (K1/F2 campaign:
#   instantiate uniform convergence of iterate source-coeff derivatives into
#   duhamelSourceTimeC1_of_uniform_limit, then window-restrict);
#   hpde_u (wire HasSpectralPdeAgreement data — mirrors the localized Hu
#   witness construction + IntervalDomainPdeUProducer); Hvsrc (power-source
#   analogue; powerSource_intervalWeakH2Neumann exists as base).
# LedgerSweep (1): Hu_of_reduced — needs subtype-continuity variant of
#   Hu_of_restart_localized (replace limit_lift_eq_cosineSeries_weak inside
#   picardLimitRestart_general with the _of_subtypeCont adapter; same surgery
#   pattern as the existing adapter theorem).
# MildLocalChi0 (1): restartData_of_inputs (restart packaging via
#   ConstExtendAdapter). ConstExtendAdapter (1): hasRestartData_of_subtypeCont.
#
# ---- historical notes below ----

Design: HANDOFF/horizon-localization-design.md. Committed so far (main):
- a484556 wave 1: IntervalTimeSoftClamp (0s), IntervalDomainPdeUProducer (0s),
  IntervalResolverStrictPositivity (0s)
- d3d99d2 IntervalDomainClampedSourceRepresentation (0s)

## Working tree (UNCOMMITTED, partially-retyped, likely does NOT compile)

`git status`: M IntervalDuhamelClosedC2.lean, M IntervalPicardLimitRestartWeak.lean,
?? IntervalCompactSliceGradientBounds.lean (broken orphan, see below).

### Retype agent progress (Step 2 of 5, half done)
DONE (claimed 0-sorry, NOT remotely verified):
- IntervalDuhamelClosedC2.lean: NEW `duhamelMode_integralNorm_summable_on`,
  `duhamelValue_adot_eq_tsum_on` (horizon t ≤ T, ContinuousOn Icc 0 T) — needed
  because `duhamelSpectral_eq_cosineSeries_weak` feeds `src.hcont` wholesale into
  `duhamelValue_adot_eq_tsum` (global Continuous), a consumption point the spec
  missed.
- IntervalPicardLimitRestartWeak.lean: `DuhamelSourceL1ContOn` structure +
  `DuhamelSourceL1Cont.toOn`; retyped: abs_duhamelSpectralCoeff_le_weak,
  duhamelSpectral_eq_cosineSeries_weak, summable_abs_limitCoeff_weak,
  limit_lift_eq_cosineSeries_weak (hfix → ∀ s, 0<s→s≤t→…),
  cosineCoeffs_halfstep_eq_limitCoeff_weak.

IN PROGRESS at death: `picardLimitRestart_cosineIdentity_weak` — its body uses
hsrc0.hcont (global) to feed `duhamelSpectralCoeff_halfstep_split`
(IntervalPicardIterateRestart.lean, demands global Continuous). Needs an
On-variant of the halfstep split (same pattern as the ClosedC2 On-variants).

REMAINING:
- Step 2 rest: picardLimitRestart_cosineIdentity_weak,
  picardLimitRestart_cosineIdentity_of_iterateData,
  limit_lift_eq_cosineSeries_of_subtypeCont,
  eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope,
  summable_eigenvalue_mul_abs_limitCoeff_weak
- Step 3: TimeNhd — duhamelSpectralCoeff_general_split (global ha_cont → On),
  limitCoeff_eq_restartDuhamelCoeff_general, picardLimitRestart_general,
  Hu_of_restart (hfix strict-<T form; K2/K1 hypotheses untouched this pass)
- Step 4 call sites: IntervalPicardLimitCoeffConv.lean (calls
  picardLimitRestart_cosineIdentity_of_iterateData — survey found this, spec
  missed it), LedgerSweep weakSource_of_reduced result type → On D.T,
  Provider hsrc0 hypothesis + 2 sorried lets + threading at the
  summable/limit_lift call sites (hσT.le in context).
- Step 5: remote verify per file (rsync each file, lake env lean), then remote
  lake build of Provider target.

### K2 agent file (IntervalCompactSliceGradientBounds.lean)
Half-written, references undefined `summable_eig_abs_bc` — does NOT compile.
At resume: either repair (the intended content is deliverables 1-3 of its brief:
σ-uniform envelope on Ici τa via monotone exp; summable envelope; G1/G2 via
term-wise series derivative + junk-deriv endpoints) or delete and re-brief.

## Wave 3 (after retype lands)
`Hu_of_restart_localized`: clamped TimeC1 witness via
`clampedSource_duhamelSourceTimeC1` (window [c',d']=[τ/2,(t₀+3T)/4], id-zone
[c,d]=[τ,(t₀+T)/2]) + `clampedFamily_eq_on` to transfer localRestartCoeff via
intervalIntegral.integral_congr + the retyped picardLimitRestart_general.
Then ledger V2 (delete 5 shifted-K1 fields; K1/K2 per-compact) + LedgerSweep
adapters + Provider refill (hpde_u via HasSpectralPdeAgreement producer,
Hvpos via mildChemicalConcentration_pos — both committed).

## Frontier remaining after all that
K1 producer (adott on (0,T) for the Picard limit): F2 instantiation —
uniform convergence of iterate source-coefficient derivatives into
`duhamelSourceTimeC1_of_uniform_limit` (IntervalMildPicardLimitRegularity).
Iterate-side files: IntervalPicardIterateSourceC1/TimeC1/Uniform (Paper2/).
