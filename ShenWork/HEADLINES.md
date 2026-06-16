# Shen_work — HEADLINE THEOREM 清单 (authoritative 按图索骥 map, 2026-06-15)

Chen–Ruau–Shen TRILOGY on one chemotaxis-growth system. Models: `CMParams` (traveling waves, Paper1);
`CM2Params`+`BoundedDomainData` (bounded-domain, Paper2 existence & Paper3 long-time dynamics).

## BOTTOM LINE (verified)
**0 of 28 headline Props are UNCONDITIONAL.** All are conditional. But they are NOT all equal — there's a
gradient of how much real mechanism stands behind each. 0 sorry / 0 axiom / 0 native_decide everywhere; the
gap is unfilled assumed-branches, not sorries. Many closers are honest reductions; several are tautologies
(`:= hexist`, source-tagged "IMPOSTOR/TAUTOLOGICAL") that assume the conclusion (no math).

Status legend:
- 🟢 **REAL MECHANISM** — reduced to a small number of NAMED, well-defined obligations; most of the construction is committed & axiom-clean.
- 🟡 **SCAFFOLDED** — the architecture/assembly is wired, but the math content sits as an assumed branch with little/no mechanism behind it.
- 🔴 **STUB / TAUTOLOGY** — closer assumes the conclusion, or the section is a placeholder.
- ✦ **statement faithfulness-FIXED today** (the *statement* now matches the paper; the proof is still owed).

---

## PAPER 2 — bounded-domain classical solutions (existence/boundedness). CLOSEST paper.
| # | Theorem | status | the ONE remaining thing |
|---|---|---|---|
| P2-T11 | **Theorem_1_1** (χ₀≤0 positive classical soln + InitialTrace + sup-bound + m≥1 global) | 🟢✦ | χ₀=0 wired (mod `PicardLimitRestartFrontier`). χ₀<0 = **`hQuant`** (datum-uniform local classical existence = the EWA real-PDE source-regularity floor: ResolverSourceSummable + Fourier-ℓ¹ surrogate + realizes↔Duhamel) + `hMildLocal`. The deepest real-analysis floor. |
| P2-T12 | Theorem_1_2 (slow/critical-regime time-decay) | 🟡✦ | Lp-energy / eventual-sup-bound frontier (feeds the decay) |
| P2-T13 | Theorem_1_3 (m-regime decay) | 🟡✦ | Lp / mass-gradient frontier |
| P2-P11 | Proposition_1_1 (per-datum local classical soln + finite-horizon alt) | 🟡✦ | the local-existence engine (closer is a tautology) |
| P2-P21 | Proposition_2_1 (Lᵖ signal-vs-source resolvent estimate) | 🔴 | tautology closer → real Lᵖ resolvent estimate |
| P2-P22 | Proposition_2_2 (weighted gradient estimate) | 🔴 | tautology / real estimate |
| P2-P23 | Proposition_2_3 (weighted signal estimate, ε-Young) | 🔴 | tautology / real estimate |
| P2-P24 | Proposition_2_4 (mass conservation / logistic mass bound) | 🔴 | tautology / real estimate |
| P2-P25 | Proposition_2_5 (Moser iteration Lᵖ⇒L∞) | 🔴 | tautology / the Moser bootstrap |

## PAPER 1 — traveling waves. Theorem_1_1 has TWO branches (χ≤0 AND χ≥0).
| # | Theorem | status | the ONE remaining thing |
|---|---|---|---|
| P1-T11neg | **Theorem_1_1 χ≤0** (monotone wave existence + Shen bound + tail) | 🟢 | **TODAY**: whole Rothe parabolic-orbit construction built & axiom-clean → reduced to **G1** `LocalUniformSchauderFixedPointPrinciple` (= n-D Brouwer, gated on **R3** Freudenthal model rebuild) + committed profile lemmas. |
| P1-T11pos | **Theorem_1_1 χ≥0** (0≤χ<min(½,chiStar), positive sensitivity) | 🟡 | UNTOUCHED branch — the positive-sensitivity wave construction (its own barriers/trap; analogous Rothe/Schauder but different signs) |
| P1-T12 | Theorem_1_2 (nonlinear orbital STABILITY of the wave) | 🔴 | Section-5 weighted-L²+uniform moving-frame convergence — essentially stubbed (`StabilityUniqueness.lean`) |
| P1-T13 | Theorem_1_3 (profile UNIQUENESS) | 🟡 | reduces to Theorem_1_2 + Cauchy-unique + resolvent + tail |
| P1-P11 | Proposition_1_1 (global existence + sup/limsup bounds) | 🔴 | Section-3 global Cauchy existence — essentially stubbed (`GlobalExistence.lean`); `constant_one_branch` only covers u₀≡1 |
| P1-P12 | Proposition_1_2 (global existence + long-time convergence) | 🔴 | same Section-3 global existence |

## PAPER 3 — long-time dynamics (stability / persistence / critical sensitivity). Sits ON Paper2's existence.
| # | Theorem | status | the ONE remaining thing |
|---|---|---|---|
| P3-P12 | Proposition_1_2 (χ₀≤0,m≥1 global bounded) | 🟡✦ | global bounded existence (inherits Paper2's floor) |
| P3-P13 | Proposition_1_3 (strong-logistic global) | 🟡✦ | same |
| P3-P14 | Proposition_1_4 (m=1 global) | 🟡✦ | same |
| P3-T21 | Theorem_2_1 (+parts 1-4) (uniform PERSISTENCE / lower-envelope) | 🟡 | persistence lower bounds; + the per-time spatial-floor positivity (deferred: needs a `BoundedDomainData` topology/`infValue=⨅` interface upgrade) |
| P3-T22 | Theorem_2_2 (nonlinear local exp C¹ convergence) | 🟡 | the nonlinear half (linear dichotomy IS unconditional) |
| P3-T23 | Theorem_2_3 (neg-sensitivity convergence-rate, sectorial) | 🟡 | sectorial-operator stability analysis |
| P3-T24 | Theorem_2_4 (full nonlinear stability + critical-sensitivity threshold) | 🟡 | full nonlinear stability (linear formula carries a condition) |
| P3-T25 | Theorem_2_5 (full nonlinear stability, companion regime) | 🟡 | same |

---

## SHARED INFRASTRUCTURE (the genuine unconditional proven base — reused across papers)
`ShenWork.PDE.Interval*` (Neumann resolver / Green-kernel regularity / cosine-spectral Duhamel / semigroup),
the `Wiener/EWA` weighted-ℓ¹ algebra (the χ₀<0 hQuant engine), and now the whole **B1 Rothe + Brouwer-Sperner
stack** (Paper1). Paper3 imports Paper2's solution objects directly.

## GRIND ORDER (按图索骥)
1. **P1-T11neg** (closest to a genuine headline): finish **R3** (Freudenthal model — Codex Jun 18) → G1 Schauder
   principle → B1 χ≤0 UNCONDITIONAL. The entire analytic edifice is already committed & axiom-clean.
2. **P2-T11 χ₀<0** (the other near-headline): discharge **`hQuant`** (the EWA real-PDE source-regularity floor).
   Deep but well-localized; unlocks Paper3's existence base.
3. **P1-T11pos**: the positive-sensitivity wave branch (reuse the Rothe/Schauder machinery, flip signs).
4. **P1-T13** (uniqueness, rides on T12) · **P2-T12/T13** (decay frontiers) · **P3-P12/13/14** (global, on Paper2 floor).
5. **P3-T21..25** (persistence/stability/sectorial — the deepest paper-level analysis) + the `BoundedDomainData`
   topology interface upgrade (unblocks P3 per-time-floor positivity).
6. The 🔴 a-priori-estimate Props (P2-P21..25, P1-P11/12) + the stubbed Sections (P1 §3 global, P1 §5 stability).

## TODAY'S DELTAS (2026-06-15)
- Statement-faithfulness sweep: P2-T11/T12/T13 + P3-P12/13/14 fixed to `PaperPositiveInitialDatum` (paper eq 1.11
  uniform floor); was open-interior positivity admitting paper-excluded inf=0 data. Verified 8671 jobs.
- P1-T11neg: built the entire Rothe parabolic-orbit construction from scratch (no Mathlib parabolic theory;
  no Mathlib Brouwer) → reduced to G1/R3. ~26 commits.

## P2-T11 χ₀<0 hQuant — cron Wiener-route verdict (2026-06-15)
Obstruction (b) positivity floor: DISCHARGED (HeatFloorIcc, from the faithfulness floor). Obstruction (a)
Wiener-ℓ¹: the SOUND route is to make the Wiener bound an OUTPUT of parabolic smoothing, NOT a datum hyp.
Faithful route = STANDARD PARABOLIC-SEMIGROUP local existence from C(Ω̄)+floor data (NOT EWA-from-Wiener;
EWA is a convenience tool that should be FED by a short C-compatible first leg). 3 bricks:
- **brick 1 (the deep core)**: faithful χ₀<0 local existence from C(Ω̄)+floor via parabolic semigroup —
  the chemotaxis-term parabolic IVP local existence (Mathlib lacks the framework; substantial, analogous
  to B1's construction). The χ₀=0 cone/Duhamel route does NOT carry the chemotaxis term.
- brick 2: positive-time smoothing (cData_solution_C2_smoothing, u(t₀) is C²).
- brick 3: C²⇒Wiener (wienerNorm f ≤ C_W(C)) — makes the Wiener bound an output; feeds EWA.
Option A (smoothing prelude at every restart) closes the continuation-reentry gap; m≥1 blow-up alternative +
global L∞ bound gives global continuation w/o a uniform floor. ⟹ P2-T11 χ₀<0 core = brick 1 (deep parabolic
local existence). Density route rejected (approximant Wiener norms blow up).

## P2-T11 brick-1 ROUTE (cron, 2026-06-16) — mild-solution contraction, heat-gradient smoothing
Faithful χ₀<0 local existence from C(Ω̄)+floor = standard MILD-SOLUTION CONTRACTION: u(t)=S(t)u₀ +
∫₀ᵗ S(t−s)[−χ₀∂ₓ(flux) + reaction] ds, chemotaxis in DIVERGENCE Duhamel form estimated by the heat-gradient
bound ‖∂ₓS(t)g‖∞ ≤ C∇·t^{−1/2}‖g‖∞ ⟹ ∫₀ᵗ(t−s)^{−1/2}ds=2√t→0 short-time contraction (ContractingWith) in
the order box [r,R]. REUSES: committed χ₀=0 cone/Picard infra (GradientMildSolutionData), IntervalResolver
WeakBounds (value/gradient sup bounds for 0≤u≤M ~committed), power-Lipschitz on [r,R]. NEW bricks:
(1) the heat-gradient bound t^{−1/2} L∞→L∞ [a14c058d in flight — committed layer may only give spectral t^{−1};
    the t^{−1/2} needs the Gaussian-kernel-derivative route ∫|∂ₓp_t|~t^{−1/2}], (2) chemMildLocal_orderBox_exists
(the contraction), (3) mild→classical regularity with the chemotaxis Duhamel source + floor preservation.

## P2-T11 hregularize — route-(c) TERMINAL VERDICT (opus audit, 2026-06-16, HEAD ea68a4e)
Route (c) "derive u(t₀)∈C² at a single positive time from the merely-continuous mild fixed point using COMMITTED
estimates" is **DEAD** — and the committed code already proves WHY (IntervalDuhamelRegularity.lean:199-236):
- Leg 1  S(t₀)u₀         : ✅ C^∞ via intervalFullSemigroupOperator_contDiff_two_unconditional (IntervalFullKernelInterchange.lean:392).
- Leg 2  reaction value-Duhamel ∫S(t−s)L(u(s))ds : ❌ positive-time C² is FALSE for a merely-bounded source —
  the bounded-coeff heat-value rep forces bₙ=cₙe^{τλₙ} UNBOUNDED at the s=t singularity (parabolicGain only
  gives |cₙ|~1/n² ⟹ H^{s<3/2}, C⁰ not C²). This is classical Schauder: bounded source → C^{1,α}, need Hölder source for C².
- Leg 3  chemotaxis grad-Duhamel : ❌ a 2nd x-deriv needs ∂ₓₓS, kernel ~(t−s)^{−3/2} NON-integrable at s=t.
FIRST missing estimate = positive-time C²/H² smoothing of the inhomogeneous Duhamel term of a bounded source
(the s≈t time-singularity). Only two honest routes, BOTH coupled back to the solution's own regularity (anti-circular):
  (i) source spatial-regularity (decaying cosine coeffs of L(u),Q(u)) — = brick-3 conclusion C²⇒Wiener;
      the committed bootstrap IntervalCoupledRegularityBootstrap.lean:60 TAKES hC2:ContDiffOn ℝ 2 u as hypothesis (circular).
  (ii) TIME integration-by-parts moving a deriv onto ∂_s g_s — needs s↦L(u(s)) C¹-in-s, = the deep brick-1 content.
⟹ P2-T11 χ₀<0 has NO committed-estimate shortcut; the mild solution is faithful but mild→classical = brick-1
(deep parabolic local existence producing a time-C¹ source, enabling the time-IBP). Codex-scale; analogous to B1's Rothe.
DO NOT re-attempt route (c) C²-from-bounded-source — it is mathematically false, not just hard.
