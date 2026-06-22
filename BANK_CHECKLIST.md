# χ₀<0 Bank Producer Checklist — `BFormBankedInputs p DB`

The single remaining floor to make Paper 2 boundedness UNCONDITIONAL for χ₀<0
(repulsive chemotaxis). χ₀=0 is ALREADY unconditional (`from_cone_construction`);
the chemotaxis-divergence source vanishes there. Target: a producer
`bFormBankedInputs_of_conjugate_core_negChi (p)(hχ:χ₀≤0)(DB) : BFormBankedInputs p DB`.
Structure def: `IntervalBFormDirectClassical.lean:62` (13 fields). Mapped 2026-06-22.

## The 13 fields (a=trivial/data · b=one-wire from landed brick · c=genuine gap)

- [a] 1  `huPaper`     — datum hypothesis (upstream per-datum)
- [b] 2  `Hinf`        — abs source bounds; ← `conjugatePicardInfThresholdData_of_picard_bounds` + `IntervalConjugateChemFluxIntegrable.*_of_ball`   [subagent C]
- [a] 3  `hsmall`      — scalar smallness; CLOSES via min-horizon (cron2 verified: floor=closed-interval inf, no T→0 decay)
- [a] 4  `MInit`       — u₀ coeff bound witness
- [b] 5  `haInit`      — mechanical from #4
- [b] 6  `hlogSrc`     — logistic timeC1; ← `logisticSource_duhamelSourceTimeC1_of_representation`   [subagent C]
- [c] 7  `hchemSrc`    — chemDiv source timeC1; ← `coupledChemDivSource_timeC1_of_fields` + produce `CoupledChemDivTimeC1Fields`   [subagent B]
- [c] 8  `hB_global`   — global cosine repr; ← landed `conjugatePicardLimit_cosineSeries` + landed `hfix`, MISSING `hsource_bridge` (downstream of #10,#12)
- [b] 9  `hlogCont`    — logistic slice continuity; ← `intervalLogisticSource_continuous`   [subagent A]
- [c] 10 `hlogFourier` — logistic Fourier summability; ← quadratic-decay repr (`logisticSource_cosineCoeff_quadratic_decay_of_representation`)   [subagent A]
- [c] 11 `hchemCont`   — chemDiv slice continuity; ← `ChemMildHolderBootstrap.holderLeg_chemotaxis`   [subagent A]
- [c] 12 `hchemFourier`— chemDiv Fourier summability — DEEPEST; ← `CrossDiffusionBootstrap` + `resolver_memHSigmaPlus2_of_memHSigma`; needs σ>3/2 for Q (cron2b analytic route)   [HELD for cron2b]

## Scoreboard: 4 (a) ✓ · 3 (b) in flight · 5 (c) gaps — 0/5 gaps landed

## Genuine-gap theorems (dependency-ordered)
1. `coupledLogistic_fourierCoeff_summable_of_limit`  (field 10)   [A]
2. `coupledChemDiv_fourierCoeff_summable_of_limit`   (field 12, HEART)  [cron2b→codex/me]
3. `coupledChemDiv_constExtend_continuous_of_limit`  (field 11)   [A]
4. `coupledChemDivSource_timeC1_of_limit`            (field 7)    [B]
5. `conjugatePicardLimit_sourceBridge`              (field 8, downstream of 1,2) [HELD]
→ final mechanical `BFormBankedInputs.of_limit_analytics` wiring all 13.

## Sign-sensitivity (cron1): smoothing/Fourier sign-blind; only the FRONTIER
`hSupNormDeriv` (sup-norm max principle) uses χ₀≤0 essentially [cron1b].
Bank → BFormSpectralFrontier (6 fields) → hPerDatum → unconditional P2 → P3 cascade.

Last verified: 2026-06-22 (mapper a261b373, canonical d7659d9/c516590).

## ⚠️ FRONTIER IMPOSTOR (cron1b + source-verified 2026-06-22) — GATING
`BFormSpectralFrontier.hSupNormDeriv : IntervalDomainSupNormDerivativeNonposOn (limit) (Ioo 0 T)`
(IntervalBFormEndToEnd.lean:213) is the repo's OWN documented-FALSE field
(IntervalHsupNormProof.lean: flat datum 0<ε<K=(a/b)^{1/α} ⟹ logistic ODE ⟹ supNorm INCREASES,
deriv>0, contradicts deriv_nonpos). It is UNSATISFIABLE for admissible small data ⟹ frontier
uninhabitable ⟹ hPerDatum undischargeable ⟹ paper2_theorem_1_1_general_chi_via_bform vacuously
conditional (IMPOSTOR). BUT it is UNUSED downstream: IntervalDomainEndToEnd.lean:158 destructures
it as `_hSupNormDeriv` (discarded). FIX: drop the field (or replace w/ the conditional above-capacity
+ pure-heat true pieces, mirroring HsupNormConsumers.Lemma31CarrierTarget which the cone route uses).
Strict improvement — removes an unsatisfiable hypothesis without weakening the theorem. [me, next]

## Field 12 hchemFourier — COMPLETE analytic route (cron2b, Q275)
u(t)∈H^{3/2+} ⟹ v∈H^{σ+2}, Q=u^m(1+v)^{-β}v_x∈H^σ ⟹ S=Q_x∈H^{σ-1}, σ-1>1/2 ⟹ ℓ¹.
Iteration: 4 half-steps from H^0 (k=4: u∈H^2 → Q∈H^2 → S∈H^1 → ℓ¹). k=3 FAILS (S∈H^{1/2} endpoint).
Caveats handled: (a) H^{1/2} not an algebra → cross first step via L^∞∩H^s Moser (limit has L^∞);
(b) u^m noninteger m → keystone hmapsTo_pos positive floor on slice. Lemma: hchemFourier_of_u_H2.
PREREQ to verify: is u∈H^2 (4-half-step bootstrap) of the limit reachable from landed HSigma bricks
(IntervalBFormHSigmaSmoothing rate (1-σ)/2)? If not, the bootstrap-to-H^2 is the true sub-residual.

Updated: 2026-06-22 (cron1b Q274 impostor, cron2b Q275 route).
