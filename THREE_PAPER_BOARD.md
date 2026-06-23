# THREE-PAPER FORMALIZATION BOARD (Chen-Ruau-Shen) — honest cross-paper status
Last verified: full-closure 8862 jobs; 7 real sorry tactics repo-wide (all P2 χ₀<0 analytic).
Audit standard (playbook §3.3): headline UNCONDITIONAL on satisfiable CMParams, no sorry/admit/
native_decide/custom-axiom, no carried-hard/unsatisfiable hypothesis, faithful to paper.

## P1 — Remark 1.3.2 / Theorem 1.1 (traveling-wave existence)
Headline: paper1_Theorem_1_1_of_mainResultsData (Paper1/StatementAssembly.lean:34) — CONDITIONAL on
`Paper1MainResultsData cStarStarFn`. Landed: left-floor, per-step Green solve + existence + max-principle,
order-layer, chemo-monotone, hLU. OPEN: discharge Paper1MainResultsData = the localExistence constructor
(T6/T7 per-datum existence) + order-layer hsign from trap bounds + Rothe limit. STATUS: 🔨 bundle open.

## P2 — Theorem 1.1 (bounded-domain boundedness), two regimes
χ₀=0: ✅ UNCONDITIONAL — from_cone_construction (IntervalPicardTowerSupply.lean:336, "unconditional bridge
  from the strengthened cone"). [confirm #print axioms clean at audit.]
χ₀<0: chiNeg_theorem_1_1 (Wiener/EWA/SourceChiNegTheorem11.lean:127) (p)(hchi:χ₀<0)(ha,hb,hα,hγ) — CONDITIONAL
  on the SINGLE bundle `ChiNegDatumUniformConstruction p` (the per-datum classical local existence). This
  bundle traces to the regularity chain: R1 trajectory envelope → SliceMildStepData → UniformBootstrapStep →
  MemHSigma 1 → H¹ field → H1-hom/src/chem weak identities → boundedness. STATUS: 🔨 see χ₀<0 detail below.

## P3 — persistence (Thm 2.1) + stability (Thm 2.2)
T10/persistence + stability-of-positive-equilibrium: paper3_T10_positiveEquilibriumStable_of_chi_nonpos
  (PaperOne/WholeLineLeftTail.lean:64) (p3)(hχ:χ₀≤0) — appears UNCONDITIONAL (only satisfiable param). [confirm.]
T2.2 (full stability): paper3_unitInterval_T22_with_fractionalPowerEmbedding (PDE/FractionalPowerSpace.lean:555)
  — CONDITIONAL on Paper3Constants + the fractional-power-embedding neighborhood frontier. STATUS: 🟡 T10 likely
  done, T2.2 frontier open (cascades from P2 once χ₀≤0 boundedness lands).

## χ₀<0 DETAIL (the main remaining engine — this run's focus)
✅ H1-grad (t^{-1/2} L² bound, real sine-Parseval). ✅ keystone B step (UniformBootstrapStep mild-only, non-
circular by test). ✅ trajectory propagator + genv/glenv wiring + σ-ladder step (trajLadder_step). ✅ 4 false
fields fixed. ⚠️ 1 overclaim caught+corrected.
OPEN (the residual, converged + precisely named):
 R1a. τ-uniform flux factor-envelope from Uσ — the FIXED-POINT bootstrap (flux Q built from the u being
      enveloped). Elliptic relay (v_x via resolver_memHSigmaPlus2) LANDED. The genuine hard core. → codex.
 R1b. hdecomp τ-lift: ∀τ∈[0,t] version of the landed per-endpoint IntervalBootstrapDecomp identity. Tractable.
 + per-τ ∀k fields at the joint-continuity interface (k=0 mode included).
 + 7 named sorries (P2 χ₀<0 analytic): trajectory joint measurability (IntervalMildPicardThreshold:2005,
   IntervalMildPicard:2644 — same), R-src0F-2/hCwin_ex (IntervalPicardWeightedC2Bootstrap), Lemma_3_1 closure
   (IntervalLemma31Closure), mildSlice_restart_bound restart identity (IntervalPicardLimitSliceTimeContinuity).

## DISTANCE (atom inventory, not time): discharge {P1: Paper1MainResultsData} + {P2 χ₀<0: R1a+R1b+per-τ
fields+7 sorries → ChiNegDatumUniformConstruction} + {P3 T2.2: fractional-power frontier}. χ₀=0 + P3 T10 done.
Genuine multi-session PDE. R1a is the hard fixed-point core (codex Jun 26); R1b + several sorries are tractable.
