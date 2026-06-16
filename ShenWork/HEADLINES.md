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
| P1-T11neg | **Theorem_1_1 χ≤0** (monotone wave existence + Shen bound + tail) | 🟢 | Whole Rothe parabolic-orbit construction built & axiom-clean → reduced to **G1** `LocalUniformSchauderFixedPointPrinciple` (= n-D Brouwer, gated on **R3** Freudenthal rebuild) + the **satisfiable** named per-step producer + profile lemmas. **06-16: TWO vacuity bugs found & CORRECTLY fixed** (the carried obligations were unsatisfiable, vacuously carried — caught by satisfiability audit, NOT by sorries; all stayed axiom-clean). See vacuity-fix log below. Reduction is now genuinely NON-VACUOUS. |
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

## P2-T11 hregularize — CORRECTION + LIVE ROUTE (ChatGPT cron RUN#517, 2026-06-16)
The opus terminal verdict above OVERSTATED. "Bounded source → C² in ONE heat application" is indeed false ((t−s)^{−3/2}
non-integrable). BUT route (c) is NOT dead — the standard parabolic HÖLDER BOOTSTRAP (which the opus pass missed) closes it,
and it is NON-circular: the first pass gains only a FRACTIONAL derivative (θ/2<1), so it needs no pre-existing C².
LIVE 2-pass stack (ChatGPT, verified sound):
  pass 1 (L∞ → C^θ, non-circular): heat Hölder-smoothing  ‖S(t)f‖_{C^θ} ≤ C t^{−θ/2}‖f‖∞  and
        ‖∂ₓS(t)f‖_{C^θ} ≤ C t^{−(1+θ)/2}‖f‖∞  (pure INTERPOLATION of the committed sup-bound (θ=0) and the
        committed t^{−1/2} gradient bound (θ=1)) ⟹ ∫₀ᵗ(t−s)^{−θ/2}‖f‖∞ ds converges ⟹ u(t,·)∈C^θ for t≥τ>0.
  pass 2 (C^θ → C²): u∈C^θ ⟹ V[u]∈C^{2+θ} (elliptic resolver, resolverR already C²) ⟹ chemFlux/reaction source ∈ C^θ
        ⟹ the Duhamel slice ∫S(t−s)[C^θ source] is C² — the (t−s)^{−3/2} kernel is now tamed by the source's Hölder
        modulus to an INTEGRABLE (t−s)^{−1+θ/2}. THE one genuinely hard lemma = neumannDuhamel_positiveTime_C2_slice.
The key distinction the opus pass conflated: BOUNDED source → C² is FALSE (non-integrable); C^θ source → C² is TRUE
(integrable). The bootstrap manufactures the C^θ that the agent assumed had to come from circular C².
Named brick stack (ChatGPT, by feasibility):
  EASIEST  : neumannHeat_Linf_to_Ctheta, neumannHeatGradient_Linf_to_Ctheta (interpolation of 2 committed bounds).
  MODERATE : mild_orderBox_positiveTime_holder (u∈C^θ at t≥τ); intervalResolver_Ctheta_to_C2theta (elliptic gain);
             chemFlux_Ctheta_of_holder_orderBox, reaction_Ctheta_of_holder_orderBox.
  HARDEST  : neumannDuhamel_positiveTime_C2_slice (the single s=t-endpoint Schauder Duhamel lemma; route (c) / Wiener).
             neumannDuhamel_classical_regularize (the full C^{1,2} bridge = natural extension of the same lemma).
⟹ P2-T11 route (c) is a WELL-LOCALIZED stack of mostly-easy interpolation/elliptic bricks + ONE hard endpoint lemma —
NOT a full brick-1 Rothe rebuild. This UNBLOCKS P2-T11 at Opus/Codex scale. Pursue this, not the "dead" framing above.

## B1 χ≤0 VACUITY-FIX LOG (2026-06-16) — the satisfiability discipline at work
Two carried obligations in the Rothe reduction were UNSATISFIABLE (vacuously carried) — both caught by satisfiability
audit, NOT by sorries (everything stayed 0-sorry / axiom-clean throughout). A 0-sorry CONDITIONAL theorem whose carried
hypothesis is unsatisfiable is VACUOUS; we do not ship that. Both now CORRECTLY fixed:
- **Bug #1 (BC2-everywhere)** [ea68a4e]: produce demanded `∀y, ContDiffAt 2 (upperBarrier κ M) y` — FALSE at the
  e^{−κx}=M kink. Fix = weaken to BC2-AT-MAX (the max-principle only consumes it at its internally-chosen max, which is
  never the kink), witnessed by `upperBarrier_BC2_atMax_dischargeable`. Barrier Ū is FIXED, so at-max is provable.
- **Bug #2 (descent-Z supersolution)** [d644070]: produce carried `∀x, F_u(Z) x ≤ 0` as an OUTPUT conjunct for the
  ∀-quantified trapped antitone Z — false for non-supersolution Z (e.g. ½Ū); and `RotheStepProducer.le_old` (W≤Z) is
  likewise false there (the implicit step of a non-supersolution overshoots). An at-max weakening does NOT fix this
  (unlike #1, Z is ∀-quantified and F_u(Z)(x₀)=λ(W−Z)(x₀)>0 at a positive max for large λ — a first agent attempt took
  the at-max dodge and was REJECTED as still-vacuous). Correct fix = supersolution ORBIT INVARIANT: input precond
  F_u(Z)≤0 on produce + output field F_u(W)≤0 on RotheStepFacts (PROVED via F_u(W)=λ(W−Z) and W≤Z), threaded
  inductively from the Ū base (whole_line_super_barrier) so it's internal — public statements byte-identical.
LESSON: "0-sorry + green build + a single-instance witness" ≠ "proves the theorem". A carried hypothesis must be shown
INHABITED (satisfiable for ALL inputs it quantifies over), not just non-contradictory at one seed. Audit carried
obligations for ∀-quantified properties that hold only for a sub-class (supersolutions/iterates), not all inputs.

## P2-T11 endpoint route — SHORTCUT (ChatGPT cron RUN#527, 2026-06-16): stop at C^{1+η}, skip full C²
ChatGPT confirmed the pass-1 scaling (∫|∂ₓₓp_σ||z|^θ = C_θ σ^{−1+θ/2}; Neumann ∫₀¹∂ₓₓK_N dy=0 EXACT since the
semigroup preserves constants — no boundary correction; double-DUI via the integrable (t₀−s)^{−1+θ/2} dominator) AND
flagged a shortcut that AVOIDS the one hard lemma:
- The chemotaxis DIVERGENCE leg needs Q∈C^{1+θ} (NOT just C^θ) for full C²: rewrite ∂ₓS(t−s)Q = S(t−s)(Q_x) using
  Q=0 at the Neumann boundary, then the value-source C^θ→C² lemma on Q_x. That extra derivative is a whole rung.
- BUT P2-T11's downstream need is the WIENER ℓ¹ output, and **C^{1+η} ⟹ summable cosine coefficients** (Neumann BC +
  one IBP ⟹ c_n ~ n^{−(1+η)}, summable). So the MINIMAL route stops at **u(t₀)∈C^{1+η}** — ONE Hölder rung past pass-1
  (apply the committed gradient Hölder smoothing to the mild solution) — sidestepping the hard full-C² endpoint lemma
  neumannDuhamel_positiveTime_C2_slice AND the C^{1+θ}-chemotaxis complication.
REVISED pass-2 minimal stack (for the Wiener output; full C²/classical is a SEPARATE later goal for Prop 1.1):
  (i) mild_orderBox_positiveTime_holder : u(t)∈C^θ, t≥τ  [a55eb09 in flight].
  (ii) mild_orderBox_positiveTime_C1theta : u(t)∈C^{1+η}, t≥τ  (one more rung: gradient Hölder smoothing of the mild rep;
       chemotaxis leg via the gradient-of-gradient = the committed t^{−1} second-deriv bound, value leg via t^{−1/2}).
  (iii) C1theta_implies_wiener_l1 : f∈C^{1+η} ⟹ Σ|cosineCoeff f n| < ∞ ⟹ wienerNorm bound. Feeds the EWA hQuant engine.
This makes P2-T11 χ₀<0 a stack of Hölder-smoothing rungs + one cosine-coefficient-decay lemma — no full-C² endpoint
needed for the headline. (Keep neumannDuhamel_positiveTime_C2_slice on the board for the separate full-classical Prop 1.1.)
