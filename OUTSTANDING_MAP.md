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

**O-P1-1 🔧 Unconditionalize Thm 1.2 (stability).** The "natural" stability theorems
(`…_chi_{neg,zero,pos}_natural`, `paper1_Theorem_1_2_paperDatum_of_chi_lt_half`) assume
`IsTravelingWave`, `TravelingWaveRegularity`, `HasStrictWaveUpperTailBound`,
`HasWaveRightTailAsymptotic`. These are all *proved for the wave that `Theorem_1_1.unconditional`
constructs*, but no composed theorem feeds them in. **Task:** compose Thm 1.1 → Thm 1.2 for
the whole regime, producing an unconditional stability theorem whose only remaining
hypothesis is the *inherent* `WeightedL2InitialCloseness` (data close to the wave). Pieces
exist; this is wiring + parameter-range alignment (c > cStarLower vs the η-window).

**O-P1-2 🔧 Unconditionalize Thm 1.3 (uniqueness).** Same composition:
`Theorem_1_3_amended_of_chi_lt_half` assumes two waves + regularity + tails; feed the
constructed wave. Wiring.

**O-P1-3 🔬 Close the stability window [½, chiStar).** Full stability is proved only for
0<χ<½; the far-left ingredient alone reaches `chiStar`. Lift the whole stability assembly
from ½ to `chiStar`. (The positive branch's ½ is inherited from Prop 1.2's positive branch —
start there.)

**O-P1-4 🧱 Prop 1.1 (general Cauchy existence + a-priori bounds).** Currently the existence,
max-principle bound (≤max 1 M), and limsup≤1 are carried as assumed frontier fields
(`Paper1PropositionFrontierData`); only `u₀≡1` is unconditional. **Task:** prove global
existence + bounds for arbitrary nonneg data. This is general well-posedness — real PDE.

**O-P1-5 🧱 Retire the `hcore` route.** The literal `Theorem_1_2_amended` via
`…_of_wholeLineCauchyEnergyStep4` carries `hcore` = Henry semigroup smoothing as an
assumption. The natural route (O-P1-1) *discharges* it — so either make the natural route
the sole headline (preferred) or discharge `hcore` directly.

**O-P1-6 ◐ Lem 5.1/5.2/5.3 arbitrary-wave cases** (currently branch-only: signal bound,
log-derivative, weighted elliptic perturbation). Needed if the arbitrary-wave (non-fixed-
point) statements are wanted.

## OUTSTANDING — Paper 2  (real proofs live on `intervalDomain`; ∀-domain forms are deliberately obstructed, not a target)

**O-P2-1 🧱 Thm 1.2 (weak cross-diffusion), slow branch 0<m<1.** Only m=1 is genuine
(`…critical_branch_unconditional`). The slow branch `Theorem_1_2_intervalDomain_of_slowBranchResidual`
*assumes* `IntervalDomainTheorem12SlowBranchResidual` (= its own conclusion). **Task:**
discharge that residual (the 0<m<1 Lᵖ bootstrap). *(Also keep the corrected guard
`a=0 ∨ 0<b` — the raw stmt is refuted for a>0,b=0; that correction is done+good.)*

**O-P2-2 🧱 Thm 1.3 (strong logistic), real regime a,b>0, χ>0.** Only the χ₀≤0/m=1
max-principle slice is genuine. The real regime `Theorem_1_3_intervalDomain_of_…` assumes a
stack of frontier packages: `hGN, cGrad, hdiss, hgrad, hmass, hpow_int,
hEnergyFromCrossDiffusion, hProp25, hlocal, hglobalExtension, hstrongBootstrap,
hstrongEventualSupBound`. **Task:** discharge these — this decomposes into O-P2-3.

**O-P2-3 🧱 The Paper-2 analytic lemma stack** (the actual content behind O-P2-1/2), all
currently assumed/obstructed: Lem 2.1–2.4 (Neumann semigroup / fractional-power estimates),
Lem 2.6 (Lᵖ bootstrap), Lem 2.7 (damping), Lem 3.1 (sup-norm max principle), Lem 4.1
(mass–gradient interpolation), Prop 2.1 (signal Lᵖ), Prop 2.2–2.5 (gradient/signal/mass/
boundedness). These are the standard Chen–Ruau–Shen energy machinery on the interval domain.
Knock these off → O-P2-1 and O-P2-2 fall.

## OUTSTANDING — Paper 3  (real proofs live on `intervalDomainM`; abstract nonlinear conclusions are assumed via "TAUTOLOGY" bridges — not a target)

**O-P3-1 🧱 Eventual → all-time for Thm 2.1–2.5.** The concrete proofs establish faithful
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
