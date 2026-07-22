# Outstanding map — what's left to make every headline unconditional

Source-verified 2026-07-21. **Rule (Xiang):** a theorem that carries a condition which
*smuggles in the hard content* is NOT proved — it stays outstanding until the condition is
discharged. A condition that is *inherent to the statement* (e.g. "the initial data is
close to the wave" for a stability theorem) is legitimate and stays. Correcting a *wrong*
paper statement with a new correct one COUNTS as done. Don't reinvent — 800K LOC already
exist; build on the proved pieces below.

Effort tiers: 🔧 **wiring** (compose existing proved pieces) · 🧱 **hard PDE** (discharge
an assumed analytic package = real estimate work) · 🔬 **research** (beyond the paper).

---

## DONE — genuinely proved, do NOT reinvent

- **P1 Thm 1.1 (existence):** `Theorem_1_1.unconditional` — unconditional, non-vacuous. ✅
- **P1 Prop 1.2:** `Proposition_1_2.unconditional` — unconditional. ✅
- **P1 Lem 2.1–2.5:** resolvent/heat-kernel estimates. ✅
- **P1 Lem 4.1, 4.2, Rmk 4.2:** original paper statements **refuted**; **corrected** versions
  proved — counts as done (paper was wrong). ✅
- **P2 Thm 1.1 (χ₀≤0 global existence) on `intervalDomain`:** `paper2_chiNonpos` — unconditional. ✅
- **P2 Lem 2.5 (entropy inequality):** `Lemma_2_5_direct` + full range. ✅
- **P3 concrete `intervalDomainM` eventual forms of Thm 2.1–2.5:** genuine unconditional
  proofs (2.3/χ₀≤0 strongest). ✅ *(eventual, not all-time — see O-P3-1)*
- **P3 linear/spectral stability, critical-χ\* formula (2.10), Lem A.6, A.7–A.8 algebra.** ✅
- The wave's own `TravelingWaveRegularity` + tail bounds ARE proved for the constructed
  wave (`WavePositiveConstruction.lean:318,371`, `WaveNegativeRotheCore.lean`). ✅

---

## OUTSTANDING — Paper 1

**O-P1-1 ✅ (positive branch) DONE / 🧱 (χ≤0 branch) = O-P1-1b.**
`paper1_Theorem_1_2_chi_pos_unconditional` (`Paper1Theorem12ChiPosUnconditional.lean`,
clean-3) composes `paper1_positiveConstruction_selfStep` into the χ>0 stability, so the wave
is CONSTRUCTED not assumed, for `0<χ<min(½,chiStar)`; only inherent `WeightedL2InitialCloseness`
remains. **O-P1-1b [CRUX SOLVED 2026-07-21].** `paper1_negativeConstruction_selfStep_reg`
(`Paper1Theorem12ChiNonposUnconditional.lean`, clean-3, root 10007) exposes
`TravelingWaveRegularity` for the Rothe wave via route (1) (transport step-level ContDiff 2).
Remaining to fully unconditionalize Thm 1.2 for χ≤0:
- **χ=0: DONE** (`paper1_Theorem_1_2_chi_zero_unconditional`, clean-3, root 10008) via `paper1_Theorem_1_2_chi_zero_unconditional` (regularity above +
  χ=0 strict barrier `positiveStationary_strict_upperBarrier` (covers 0≤χ) + chi_nonpos stability;
  handle speed via `max(cStarStar, cStarLower)`). [dispatched]
- **χ<0: SOLVED 2026-07-21** (`paper1_Theorem_1_2_chi_neg_unconditional`, clean-3, root 10014) — strong-max-principle wall cleared via new strict Green bound `frozenElliptic_lt_one_of_le_one_tendsto`. [OLD: NEW-ANALYSIS WALL] chi_nonpos stability needs `HasStrictWaveUpperTailBound` (min-form,
  strict at every x); the negative construction gives only `ShenUpperBoundNegative` (max-form,
  strictly weaker, no bridge). Building the min-form for χ<0 needs (a) a strict χ≤0 exp-region
  operator sign (only non-strict exists) + (b) a χ<0 coupled strictly-below-one strong-maximum-
  principle (only χ=0 version exists). Genuine new strong-max-principle analysis. [class B, deep]

(superseded scoping below)
**O-P1-1b [OLD scoping — crux precisely located].** The χ≤0/χ=0 branches need
`TravelingWaveRegularity`, which the generic producer
`FrozenStationaryWaveProfile.travelingWaveRegularity_of_green_step` builds from
(profile + `PaperStepAnalytic` + `InWaveTrapSet` + `ContDiff 2 U` + `ContDiff 2 V`). All are
available for the negative wave EXCEPT `ContDiff 2 U`: `ContDiff 2` exists at the Rothe *step*
level (`PaperLocalFixedStepData.contDiff_two`, `WaveNegativeSelfStepClosedGraph:110`) but the
*stationary* producer `paperNegativePinned_fixed_stationary_of_selfStep` only outputs
`Differentiable U` + `Differentiable (deriv U)`, not `ContDiff 2`.
**The exact remaining lemma:** bootstrap `ContDiff ℝ 2 U` for the stationary negative wave from
`stationary_eq` (`iteratedDeriv 2 U = −(c·deriv U − χ·flux(U,V) + reaction(U))`, whose RHS is
continuous once `U, deriv U, V, deriv V` are, giving `deriv (deriv U)` continuous) — for the
*general* `(m,γ,α)` `frozenWaveOperator`. Then feed trap/analytic-step + `ContDiff 2 V`
(frozen Green-conv C², `WavePaperRotheProducer:4142`) into `travelingWaveRegularity_of_green_step`.
Real analysis (the general-parameter flux terms `W^{m-1}` etc.), not wiring.

**O-P1-2 ✅ DONE (reclassified 2026-07-21).** `Theorem_1_3_amended_of_chi_lt_half`'s
hypotheses (both waves are regular traveling waves sharing a right-tail rate) are
*inherent* to a uniqueness statement — you are comparing waves within the regular class —
not smuggled hard content, and it uses the *proved* stability (no assumed Cauchy-uniqueness).
So it is a genuine proof with legitimate conditions. Nice-to-have (not required): a
combined `∃! regular wave` capstone = O-P1-1's constructed wave + this uniqueness.

**O-P1-3 🔬 Close the stability window [½, chiStar).** Full stability is proved only for
0<χ<½; the far-left ingredient alone reaches `chiStar`. Lift the whole stability assembly
from ½ to `chiStar`. (The positive branch's ½ is inherited from Prop 1.2's positive branch —
start there.)

**O-P1-4 ◐ Prop 1.1 — χ≤0 half DONE (2026-07-21).** `paper1_Prop_1_1_first_conjunct` (clean-3) proves the entire χ≤0 half unconditionally; positive cores landed (`_second_conjunct_critical_subwindow`, `_supercritical_core`, `_of_second_conjunct`). The frontier-RECORD route is dead (fields quantify over arbitrary sol → needs absent Cauchy uniqueness; the `existence` field is itself FALSE: u₀≡0⟹u≡0). Residuals for FULL Prop 1.1: (1) supercritical χ<1 scalar root-location lemma [Class B, elementary → Codex], (2) critical 1≤χ window Lᵖ local iteration [Class C frontier].

**O-P1-4 UPDATE 2026-07-21 (Codex):** Prop 1.1 positive conjunct for 0<χ<1 proved clean-3 (`paper1_Prop_1_1_second_conjunct_supercritical_full` via `chiPosEquilibriumCeiling_le_supercritical_bound`, + `_critical_subwindow`). Capstone `paper1_Proposition_1_1_of_chi_lt_one : Proposition_1_1` is CONDITIONAL on an arithmetic hypothesis (critical window ≤1, true iff γ≤m). GENUINE unconditional coverage now: **χ≤0 half + 0<χ<1 positive (and all χ<1 when γ≤m)**. Sole residual: the **1≤χ critical window** (γ>m corner) needing Lᵖ local existence/iteration — Class C, `paper1_Proposition_1_1_of_large_chi_critical_residual` isolates it.
 OLD: **Prop 1.1 (general Cauchy existence + a-priori bounds).** Currently the existence,
max-principle bound (≤max 1 M), and limsup≤1 are carried as assumed frontier fields
(`Paper1PropositionFrontierData`); only `u₀≡1` is unconditional. **Task:** prove global
existence + bounds for arbitrary nonneg data. This is general well-posedness — real PDE.

**O-P1-5 ✅ effectively DONE (bookkeeping).** The natural route (used by O-P1-1) is already
the `hcore`-free headline — it *discharges* the Henry smoothing internally. The
`…_of_wholeLineCauchyEnergyStep4` route that carries `hcore` is just an inferior alternative;
nothing depends on it. No proof gap; at most delete the redundant hcore route for tidiness.

**O-P1-6 ✅ DONE 2026-07-21.** Lem 5.1/5.2/5.3 arbitrary-wave cases proved clean-3 (Lemma_5_1_arbitrary_wave, Lemma_5_2_arbitrary_monotone_wave, Lemma_5_3_arbitrary_profiles); inherent hypotheses only. ~~OLD: Lem 5.1/5.2/5.3 arbitrary-wave** (currently branch-only: signal bound,
log-derivative, weighted elliptic perturbation). Needed if the arbitrary-wave (non-fixed-
point) statements are wanted.

## OUTSTANDING — Paper 2  (real proofs live on `intervalDomain`; ∀-domain forms are deliberately obstructed, not a target)

**O-P2-1 ✅ DONE 2026-07-21.** `Theorem_1_2_intervalDomain_unconditional (p) (a=0∨0<b) : Theorem_1_2 intervalDomain p` — slow-branch residual discharged unconditionally (`IntervalDomainTheorem12SlowBranchResidual_unconditional`, trace-aware finite-horizon + continuation); only the corrected `a=0∨0<b` guard (done+good). ~~OLD: Thm 1.2 slow branch~~ Only m=1 is genuine
(`…critical_branch_unconditional`). The slow branch `Theorem_1_2_intervalDomain_of_slowBranchResidual`
*assumes* `IntervalDomainTheorem12SlowBranchResidual` (= its own conclusion). **Task:**
discharge that residual (the 0<m<1 Lᵖ bootstrap). *(Also keep the corrected guard
`a=0 ∨ 0<b` — the raw stmt is refuted for a>0,b=0; that correction is done+good.)*

**O-P2-2 ◐ Thm 1.3 — frontier REFUTED + minimal-residual DONE 2026-07-21.** The old FrontierData is NOT constructible (`not_IntervalDomainTheorem13FrontierData_of_real_regime`: hGN/hglobalExtension are FALSE). `Theorem_1_3_intervalDomainM_from_minimal_honest_residual` carries ONLY the paper's case-(iv) proof gap (no energy assumption); the actual solution's all-positive-time uniform bound IS proved. Residual = case-(iv) critical-constant correspondence. **UPDATE: case-iv CLOSED for m≥1** (`Theorem_1_3_intervalDomainM_caseIV_with_paperConstants`, clean-3, algebraic scale>1 binding); remaining corner = m<1 audited boundary. ~~OLD: Thm 1.3 strong logistic~~ Only the χ₀≤0/m=1
max-principle slice is genuine. The real regime `Theorem_1_3_intervalDomain_of_…` assumes a
stack of frontier packages: `hGN, cGrad, hdiss, hgrad, hmass, hpow_int,
hEnergyFromCrossDiffusion, hProp25, hlocal, hglobalExtension, hstrongBootstrap,
hstrongEventualSupBound`. **Task:** discharge these — this decomposes into O-P2-3.

**O-P2-3 🧱 The Paper-2 analytic lemma stack** (the actual content behind O-P2-1/2).
**RECONCILED 2026-07-21 (audit understated the concrete layer):** on `intervalDomain`,
**Props 2.2, 2.3, 2.4, 2.5 are ALREADY PROVED UNCONDITIONALLY** (`intervalDomain_Proposition_2_2`
WeightedGradientEstimate:817, `_2_3` Proposition23:879, `_2_4` Mass:888, `Proposition_2_5
intervalDomain p` LPI:103 / others) — do NOT reinvent. Genuinely OUTSTANDING (each appears only
as a carried hypothesis, no unconditional concrete proof): **Prop 2.1 (signal Lᵖ), **Lem 2.1-2.4: DONE in FULL-Q** (q=2 spectral 85 thms + full-q heat/integer kernel + full-q FRACTIONAL via subordination `intervalFractionalNeumannLp_norm_le`; the H-inf/Marcinkiewicz 'wall' was bypassable).  Lem 2.6 (Lᵖ bootstrap — carries frontier `hdiss`),
Lem 2.7 (damping), Lem 3.1 (sup-norm max principle), Lem 4.1 (mass–gradient interp), Cor 2.1**.
That semigroup/energy set is the real P2 spine; knock it off → O-P2-1/O-P2-2 fall.

**O-P2 Lem 2.6/2.7 UPDATE 2026-07-21:** Lemma 2.7 as literally stated is FALSE (`not_Lemma_2_7_intervalDomain`, clean-3 counterexample u=t⁻¹); faithful form `Lemma_2_7_intervalDomain_from_continuous_bound` DONE. Lemma 2.6 faithful form `Lemma_2_6_intervalDomain_from_continuous_lp_bounds` DONE (carries legitimate closed-[0,T] Lᵖ-mass continuity, not the L∞ bound). The abstract Lᵖ-bootstrap `hgrad`/`hdiss` are genuinely circular with the L∞ bound for arbitrary u ⟹ the fully-abstract Lemma 2.6 needs the real energy method (class B/C, and its all-time form fails for rough data — same short-time issue as O-P3-1). Correct-the-paper: DONE for the faithful targets.


## OUTSTANDING — Paper 3  (real proofs live on `intervalDomainM`; abstract nonlinear conclusions are assumed via "TAUTOLOGY" bridges — not a target)

**O-P3-1 ✅ RESOLVED 2026-07-21 (correct-the-paper).** ChatGPT (grounded, cusp counterexample + parabolic t^-1/2 smoothing) shows the printed ALL-TIME C¹ decay is a short-time regularity OVERSTATEMENT — FALSE for the paper's data class (u₀∈C(Ω̄), inf>0, NOT C¹). The concrete EVENTUAL forms (from t₀>0) are the faithful correct renderings; all-time must NOT be pursued. Per Xiang's rule (correct a wrong paper statement = done), the eventual Thms 2.1–2.5 ARE the headlines. Only O-P3-2 (non-vacuity) remains on P3.  ~~[OLD] Eventual → all-time for Thm 2.1–2.5.** The concrete proofs establish faithful
*eventual* forms (asymptotics from some t₀>0). **Task:** upgrade to the printed all-time
statements (`EventualGlobalStability.lean:70` marks them as untouched). Needs the short-time
/ uniform-in-t control that bridges [0,t₀].

**O-P3-2 🧱 Broaden non-vacuity.** Concrete theorems are non-vacuous only where small-data
global existence holds (`…smallData…_of_linearlyStable`). **Task:** existence for general
admissible data, so the stability theorems aren't empty outside the small-data cone.

**O-P3-3 🧱 Discharge the assumed analytic lemmas on the concrete domain:** Lem 3.2
(time-translate compactness), Lem 3.3 (continuity in initial data), Lem 3.4 (upper-envelope
monotonicity), Lem 3.5 (eventual minimal upper bound), Lem 7.1 (Neumann resolvent gradient),
Lem A.1 / `SectorialLocalExponentialRaw` (sectorial local exponential stability — the input
to Thm 2.2's nonlinear half). These are carried as fields + obstruction lemmas.

**O-P3-4 🧱 Thm 2.1 corrected-vs-printed.** `Theorem_2_1_corrected_intervalDomainM` proves a
*corrected* Part-1 (adds a reaction guard the printed Part 1 omits) + physical positive-time
mass for Part 4. Confirm the correction is faithful / decide if the printed form is wanted.

---


## GENERAL-m (Fable framework) — added 2026-07-22 per Xiang; RECONCILED

Xiang recalled a Fable-drafted framework; recon (`HANDOFF/general-N-recon.md`, mini cron) clarified it is
**general-m** (diffusion exponent m≥1, `intervalDomain` m=1 → `intervalDomainM` paper-faithful uᵐ flux, dropping
`hm:p.m=1`), NOT general-N/N-species. Three Fable doctrines target P3 Thm 2.2/2.3/2.4 general-m. **Verified actual
status (verify-don't-transcribe — recon was stale on 2.3):**
- **Thm 2.2 general-m** — ✅ DONE (`DOCTRINE_thm22_fable.md`, HEADLINE CLOSED 2026-07-16; `intervalDomainM_Theorem_2_2_Eventual…`).
- **Thm 2.4 general-m** — ✅ DONE (`DOCTRINE_thm24_fable.md`, UNCONDITIONAL 2026-07-16).
- **Thm 2.3 general-m** — ✅ DONE via the EVENTUAL route (`intervalDomainM_Theorem_2_3_EventualGlobalStability`,
  clean-3 verified 2026-07-22; + all-data non-vacuity O-P3-2). The recon's "7-file plan / not started" refers to the
  never-written Fable *plan file* `DOCTRINE_thm23_fable.md` (confirmed absent) — the THEOREM was proved by a
  different route. Since all-time is a paper overstatement (O-P3-1), the eventual form is the faithful maximal form.
**⇒ the general-m framework is essentially COMPLETE (all three theorems proven, intervalDomainM, clean-3).** If the
specific Fable 7-file *route* for Thm 2.3 is wanted (vs the eventual route already proven), that is re-doing done
work — flag to Xiang before spending on it.

## Suggested knock-off order (cheap → hard)

1. **O-P1-1, O-P1-2** (🔧 wiring): compose Thm 1.1 into Thm 1.2/1.3 → Paper 1's trilogy
   becomes unconditional (modulo the inherent data-closeness). Biggest credibility win per
   unit effort; pieces all exist.
2. **O-P1-5** (🔧): make the natural route the headline, drop the `hcore` assumption.
3. **O-P3-1** (🧱 medium): eventual→all-time on `intervalDomainM` — turns 5 assumed-looking
   headlines into genuinely-proved printed statements.
4. **O-P3-3, O-P2-3** (🧱): the analytic lemma stacks — the real PDE estimate work; each
   lemma discharged removes assumptions from multiple headlines. Do these as a shared pool.
5. **O-P2-1 → O-P2-2, O-P3-2** (🧱): once the lemma stacks land, the cross-diffusion / strong-
   logistic / non-vacuity headlines fall.
6. **O-P1-4** (🧱): Prop 1.1 general well-posedness.
7. **O-P1-3, then far-left past chiStar → (1+√α)²** (🔬): the threshold frontier — hardest,
   beyond the paper; needs the time-dependent parabolic Bernstein estimate (see
   `INJECTION_PLAN.md` / `RESEARCH_TODO.md`).

Deepest single obstacle recurring across P2/P3: **real Neumann-semigroup / sectorial /
energy-bootstrap estimates on the interval domain** (O-P2-3, O-P3-3). That pool is the spine
of the remaining analytic work.
