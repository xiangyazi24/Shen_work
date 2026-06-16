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

## P2-T11 step (ii) ROUTE (ChatGPT cron PID64540, 2026-06-16): divergence-form Schauder, C^θ-cancellation
Getting u∈C^{1+η} from u∈C^θ: the chemotaxis leg of u_x is ∫∂_xx S(t-s)Q ds. The naive sup bound (t-s)^{-1}‖Q‖∞ is
NON-integrable and the WRONG estimate. CORRECT: test ∂_xx S against the HÖLDER MODULUS [Q]_{C^θ} (we HAVE Q∈C^θ since
u∈C^θ ⟹ Q=u·V_x∈C^θ), using the mean-zero cancellation ∫∂_xx K_σ(x,·)=0 (exact — Neumann semigroup preserves
constants): ∂_xx S(σ)h(x)=∫∂_xx K_σ(x,y)[h(y)-h(x)]dy ⟹ ‖∂_xx S(σ)h‖∞ ≤ Cσ^{-1+θ/2}[h]_{C^θ} (integrable for θ>0)
and [∂_xx S(σ)h]_{C^η} ≤ Cσ^{-1+(θ-η)/2}[h]_{C^θ} (integrable for 0<η<θ). u_x(t_0)=∂_xS(t_0-τ)u(τ)−χ_0∫∂_xx S(t_0-s)Q
+∫∂_xS(t_0-s)L, each leg C^η. NO singular Gronwall, NO Q_x rewrite, NO circularity — the C^θ from step (i) is exactly
the regularity the cancellation estimate consumes. Same mechanism as the endpoint lemma (∫|∂_xx p_σ||z|^θ=Cσ^{-1+θ/2}).
6-brick stack [a410f837 in flight]: (1) ∫∂_xx K_σ=0 mean-zero; (2) |z|^θ-weighted mass Cσ^{-1+θ/2}; (3) C^θ→L∞ op
bound; (4) C^θ→C^η op bound [the hard one — split |Δx|≷√σ, needs ∂_xxx K]; (5) chemFlux_Ctheta (Q=u·V_x∈C^θ);
(6) assembly chemMild_positiveTime_C1eta_slice. Composes with HolderCosineDecay (step iii) ⟹ Wiener ℓ¹.

## P2-T11 ROUTE STATUS (2026-06-16) — 3 of 4 rungs committed
pass-1 value+gradient Hölder smoothing [f697610,706e34b unconditional] ✓ · step (i) u∈C^θ [2d28cb8] ✓ ·
step (iii) C^{1+η}⟹Wiener ℓ¹ [9e91dee] ✓ · step (ii) u∈C^θ→C^{1+η} [a410f837 IN FLIGHT, divergence-form Schauder].
When step (ii) lands, the chain composes: mild fixed point → C^θ → C^{1+η} → Wiener ℓ¹ → feeds the EWA hQuant engine ⟹
P2-T11 χ₀<0 local classical existence. Remaining after that = wiring C1eta_slice+HolderCosineDecay into hQuant + the
hMildLocal restart plumbing.

## P1-T11pos (χ≥0 positive-sensitivity branch) — SCOPED next-frontier target (2026-06-16)
Theorem_1_1 = hneg (χ≤0, NOW non-vacuous via B1) + hpos (χ≥0). The positive branch is carried as
`PositiveSensitivityWaveFixedPointConstruction` (Statements:9020) — the EXACT analog of what B1 χ≤0 discharged for
the negative branch — and combined in `Theorem_1_1.of_assumed_frozenStationaryProfile_branches` (Statements:16304,
takes hneg + hpos with hχ_nonneg + hχ<chiStar). Scaffolding present: positiveSensitivityExtendedThreshold (:202),
chiStar / MChi positivity lemmas (:8948+), the construction structure (:9020) + chi_nonneg field (:9202).
⟹ P1-T11pos = discharge PositiveSensitivityWaveFixedPointConstruction by building the positive-sensitivity Rothe
+ Schauder construction (REUSE the whole B1 machinery — Rothe orbit, supersolution-invariant producer, max-principle,
Schauder — with the χ≥0 barriers/trap, different signs; the paper's 0≤χ<min(½,chiStar) barrier is the new input).
This is a FULL parallel construction (~B1 scale), NOT a quick brick — a dedicated-context job. Hold until P2-T11
step (ii) lands + fresh context. When taken: first scope the paper's positive-sensitivity upper/lower barriers, prove
the analog super-barrier (whole_line_super_barrier for χ≥0), then transcribe the orbit/producer/Schauder chain.

## P2-T11 hQuant WIRING MAP (2026-06-16) — the post-step-(ii) chain into the EWA engine
Once step (ii) lands (chemMild_positiveTime_C1eta_slice: u(t_0)∈C^{1+η} ⟹ Summable |cosineCoeffs u(t_0)|), the wiring to
the committed χ₀<0 spatial-existence engine is:
  Summable |cosineCoeffs u(t_0)|  [HolderCosineDecay.holderCosineCoeff_summable, committed 9e91dee]
   → reflected-circle Fourier summability  [fourierCoeff_reflCircle_summable_of_cosineCoeff_abs,
                                            ShenWork/Paper2/IntervalDomainPdeUWiring.lean:93, COMMITTED]
   → ResolverSourceSummable p u  [ShenWork/Wiener/EWA/ResolverEvalBridge.lean:99, the EWA source-summability Prop]
   → sourceClassical_spatial_existence_chi0_neg / _of_fixedPoint / _clean
                                  [ShenWork/Wiener/EWA/SourceClassicalExistence.lean:193,247 + Clean.lean:44]
   → the χ₀<0 positive-time C² source-regularity floor that P2-T11 Theorem_1_1's hQuant branch needs.
CAVEAT to check at wiring time: ResolverSourceSummable is about the SOURCE coefficient envelope (u^γ / chemflux), so the
C^{1+η} of u must be pushed through the source map (u ↦ u^γ preserves C^{1+η} on the floor r≤u≤R via the power-rule
Hölder algebra; chemflux Q=u·V_x already handled by chemFlux_Ctheta). Plus the hMildLocal restart plumbing (the per-restart
C(Ω̄)+floor → mild → C^{1+η} → summable re-entry; IntervalDomainRestartPackaging is the per-t structure). These two are the
remaining wiring after step (ii) closes — NOT new analytic content.

## P2-T11 step (ii) STATUS (2026-06-16, ebde809) — analytically complete MODULO the interchange
The whole Hölder-bootstrap is now built + committed + axiom-clean, with the chemotaxis-leg Hölder GENUINELY DISCHARGED:
- bricks 1-3 [17c6093] C^θ-cancellation kernel estimates · brick 4 [8efb838] C^θ→C^η via spectral commutation ·
  Ioo→Icc [ebde809] · chemFlux_Ctheta [ebde809] · chemLeg_holder_of_brick4 [ebde809] = the chemotaxis Duhamel leg is
  η-Hölder, PROVED by applying brick 4 per-slice + integral-Minkowski (NOT carried — a prior attempt carried it as a free
  chem_holder field and FALSELY claimed complete+green; caught, rejected, re-dispatched, discharged) ·
  differentiatedMildSlice_of_brick4_chem [ebde809] discharges chem_holder · chemMild_positiveTime_C1eta_slice +
  _wiener_l1 [ebde809] chain to HolderCosineDecay.
ONLY REMAINING CARRIED HYPOTHESIS = the deriv-under-the-integral INTERCHANGE (hasDeriv w (Dw x) + deriv_split
Dw = initLeg − χ₀·chemDuhamelLeg + reactLeg): the derivative of the mild rep EXISTS and EQUALS the leg sum (Leibniz
under the singular Duhamel integral). A representation fact, never a regularity conclusion. To make step (ii)
UNCONDITIONAL for the concrete mild solution, remaining: (a) prove the interchange for the concrete mild u (differentiation
under the integral via the committed DUI + dominated convergence, dominators t^{−1/2} / t^{−1+(θ−η)/2}); (b) wire Q =
chemFluxLifted u(s) properties from chemFlux_Ctheta + concrete u; (c) wire gradient-leg Hölder from gradLeg_holder_global.
(b)(c) are wiring; (a) is the last analytic brick. Then the mapped hQuant chain ⟹ P2-T11 χ₀<0.
NOTE on verification: BOTH stale-olean directions bit us — a99909856 claimed green from a stale build (false positive),
and the orchestrator's first re-check hit a stale-olean false NEGATIVE (266/290 phantom). LESSON: clear the module's
oleans before trusting a build verdict, in BOTH directions.

## P2-T11 step (ii) FINAL STATE (a5e1584) + the DifferentiableOn closing route
PROVED + committed: whole Hölder bootstrap, chem_holder discharged, AND the INTERIOR interchange
(chemLeg_interior_hasDerivAt, on (0,1), real Mathlib-DUI + brick-3 integrable dominator). SINGLE residual = the
chemotaxis leg's differentiability AT/ACROSS the endpoints {0,1}. The global-ℝ route is hard/likely-false (the leg's
spectral coeffs b_n ≤ M don't decay ⟹ not globally C¹). CLEANER ROUTE (the closing plan): HolderCosineDecay's IBP only
integrates over [0,1], so it needs only DifferentiableOn (Icc 0 1), NOT Differentiable ℝ. Close step (ii) by:
  (1) extend chemLeg_interior_hasDerivAt to the endpoints: the derivative value chemLitLeg₂ = ∫∂ₓₓS(t₀−s)Q is CONTINUOUS
      on [0,1] (dominated convergence, brick-3 dominator), so it extends continuously to {0,1}; HasDerivWithinAt at the
      endpoints from the one-sided limit ⟹ DifferentiableOn ℝ (chemLitLeg) (Icc 0 1) + continuous deriv on [0,1] +
      Neumann endpoint values 0 (no-flux / cosine deriv-zero).
  (2) prove holderCosineCoeff_summable_of_differentiableOn : a DifferentiableOn(Icc 0 1) + [0,1]-Neumann + [0,1]-Hölder-
      derivative variant of HolderCosineDecay (the IBP ∫₀¹ f cos = −1/(nπ)∫₀¹ f' sin only needs f differentiable ON [0,1]).
  (3) assemble chemMild_C1eta_unconditional over [0,1] feeding (1)(2) + the committed gradient legs + chemFlux_Ctheta.
This avoids the global-ℝ differentiability entirely. ⟹ then step (ii) is UNCONDITIONAL → mapped hQuant chain → P2-T11 χ₀<0.

## P2-T11 step (ii) — chem_holder DISCHARGED (cef9af2); abstract content COMPLETE
ALL abstract analytic content of step (ii) proved + committed + axiom-clean:
brick 4 C^θ→C^η Schauder [8efb838] · interior interchange [a5e1584] · DifferentiableOn [0,1] extension [45a77d2] ·
DifferentiableOn cosine decay [cfbb50a] · literal=spectral bridge chemLitLeg₂=chemDuhamelLeg on Icc + chem_holder
DISCHARGED [cef9af2]. chemMild_C1eta_slice_diffOn now carries ONLY representation/realizable items (NOT regularity
conclusions): (a) w_split (differentiated mild representation; interior = committed chemLeg_interior_hasDerivAt),
(b) Q-data (realizable from chemFlux_Ctheta + mild_orderBox_positiveTime_holder), (c) init/react gradient-leg Hölder
(realizable from gradLeg_holder_global). The chemotaxis-Hölder conclusion was re-carried 3× across attempts (a99909856,
ac2041be, ad951994-input) and each time caught + finally discharged. REMAINING = the concrete GradientMildSolutionData
instantiation: feed (a)(b)(c) from the committed lemmas to get a fully unconditional chemMild_C1eta over the concrete u
⟹ Summable cosineCoeffs ⟹ the mapped hQuant chain ⟹ P2-T11 χ₀<0. This is multi-file ENGINEERING (no new analytic
content); it has resisted ~5 one-shot agent dispatches (each defers it) — likely a Codex-Jun-18 patient-wiring task.

## P2-T11 step (ii) concrete instantiation — CORRECTION (a124c25, source-verified): NOT pure wiring
My "concrete instantiation = wiring, all committed" premise was WRONG (a124c25 read the source). Two genuine analytic
bricks are NOT committed:
- **Gap 1 (substantive): resolverGradReal spatial θ-Hölder on [0,1], i.e. V_x ∈ C^{1+θ}.** chemFlux_Ctheta
  (ChemMildC1etaAssembly:73) is an ABSTRACT product-algebra lemma TAKING the g-factor Hölder modulus Hg as a hypothesis;
  the repo has only resolverGrad_sup_le_of_bounded (sup) + Lipschitz-in-u, NO spatial θ-Hölder-in-y. V solves -V''+V=u^γ
  (Neumann); u∈C^θ (committed mild_orderBox) ⟹ u^γ∈C^θ ⟹ V∈C^{2+θ} (elliptic) ⟹ V_x∈C^{1+θ}⊂C^θ. The elliptic gain
  (Green-kernel ½e^{-|x-y|} derivative Hölder) is the missing brick. Needed at ChemMildC1etaUncond:144 (chemData arg).
- **Gap 2 (bounded): reaction-leg gradient Hölder** [∫₀^{t₀}∂ₓS(t₀-s)L ds]_η — analogous to the committed chemotaxis
  discharge chemLeg_holder_of_brick4 (integrate neumannHeatGradient_Linf_to_Ctheta over s, ∫(t₀-s)^{-(1+η)/2}<∞ for η<1).
- Gap 3 (easy): init_diff = Differentiable initLeg from the committed DUI.
⟹ concrete chemMild_C1eta_concrete = Gap 1 (elliptic V_x∈C^θ brick) + Gap 2 (reaction Duhamel discharge) + Gap 3 + the
instantiation. NOT multi-day, but NOT wiring either — a few bricks, Gap 1 the real one. Repo has 74 git stashes (heavy
parallel-work residue — ask Xiang re uisai1 coordination).
