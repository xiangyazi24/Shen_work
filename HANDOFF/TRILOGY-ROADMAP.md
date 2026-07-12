# TRILOGY ROADMAP (agreed with Xiang 2026-07-11)

The path we follow for the Chen–Ruau–Shen chemotaxis-growth trilogy Lean formalization.
Goal (standing): all Paper 1–3 headline theorems UNCONDITIONAL (axiom-clean, 0 sorry).

## Phase 0 — FINISH χ<0 (Paper 2 Thm 1.1 χ₀<0) — current, converging
- energy → u≥0 : DONE (commit efdb6090).
- Jensen (u>0) : matched-DIVERGENCE weak (w−u)₊ comparison, closes at u≥0, confirmed
  NON-CIRCULAR (seed cqM, comparison cqH, mass all at u≥0; must NOT import δ-floor/HSpectral). Codex building.
- HSpectral crux `SourceFromSolutionEnvelopePass` : all atomic pieces committed/existing —
  divergence IBP (8c316b51), Nemytskii/logistic C² (04b4d047/52dcc138), flux C² (17618add/c602454e),
  flux C³ (53e65078, CONFIRMED needed for the final source pass), elliptic multiplier (existing
  elliptic_multiplier_le), C²→O(k⁻²) decay (existing), heat +2 pass (proved ladder_pass_gain_envelope).
  Remaining = Codex WIRING: assemble + thread R∈C⁴/u∈C³ for the HasDerivAt towers + finite alternating ladder.
- mapCertificate : ~trivial. Final assembly paper2_chiNeg_v6 → Theorem_1_1 : ~2 payloads.
- Then χ₀≤0 = trivial split (χ=0 ∨ χ<0), IntervalDomainChiNonposHeadline already does it.
- Key spec: /tmp/shen-collab/codex-crux-spec.md (convention μ+λ, order ledger, C³-needed, δ-floor acyclicity).

## Phase 1 — NEXT TARGET: Paper 3 P3.1 (global existence) — the LEVERAGE play
Rationale: P3.1 is the ONE Paper 3 floor that directly REUSES Paper 2's energy+mild+spectral existence
machinery. Fastest path to another unconditional headline with the least new tooling. Start here after χ<0.

## Pre-plan in parallel (keep GPT busy; scout before committing) — the three OFF-LINE mountains
1. **Paper 3 dynamical floors** (P3.2 persistence / P3.3 stability dichotomy Thm 2.2 / P3.4 sectorial decay /
   P3.6 global stability) — the "special Paper 3" skills: sectorial/analytic-semigroup decay, principal-eigenvalue
   sign conditions, Lyapunov/LaSalle, ω-limit compactness. **THIS IS THE LONGEST POLE of the whole trilogy** —
   scout hardest, earliest. (planning Q: plan-P3route, plan-P3special)
2. **Paper 2 Lᵖ mountain** (Thm 1.2 0<m≤1 β≥1, Thm 1.3 regimes i-iv) — OFF the L²-energy line, needs Lᵖ estimates.
   Abstract version REFUTED; is the bounded-interval version provable (what boundedness buys)? (planning Q: plan-P2Lp)
3. **Paper 1 Rothe** — hprodAll (per-step) + the step+tail continuous-dependence ("no mechanism yet") + the
   Route-A paramCore vacuity fix (u≡0 in the trap). Separate time-semidiscretization construction. (planning Q: plan-P1rothe)

## ★ DEFINITIVE ATTACK ORDER (Q4388 synthesis, 2026-07-11) — THIS is the path
The TRUE long pole is neither P3.1 nor Paper 1 — it is the **Paper 3 spectral-dynamical engine** (principal
eigenvalue / spectral gap / sectorial semigroup decay / compactness / ω-limit / Lyapunov-LaSalle). Everything
hard in Paper 3 reduces to that ecosystem, so it is front-loaded as shared infrastructure. Sequence:

  0. **Freeze Paper 2 χ₀≤0 core + expose theorem-level APIs** (packaging, not research):
     globalExistence / initialTrace / nonneg / boundedness / regularity / spectralBootstrap _interval_chiNeg.
     Why first: every later reuse then depends on STABLE theorem facts, not Picard/truncation producer internals.
  1. **Paper 3 P3.1 global existence** — direct Paper 2 reuse (cheapest floor).
     Shape: paper3_globalExistence_of_paper2_chiNeg : Paper2GlobalExistence → P3_1_GlobalExistence.
  2. **Paper 2 Thm 1.2/1.3 Lᵖ mountain** — BEFORE the Paper 3 dynamics (unlocks P3 Props 1.3/1.4 via existing bridges).
  3. **Build the shared Paper 3 spectral-dynamical ENGINE** — the true long pole, as reusable infrastructure.
  4. Paper 3 compactness / regularization.
  5. Paper 3 uniform persistence.
  6. Paper 3 threshold / stability dichotomy (Thm 2.2).
  7. Paper 3 global stability (Thm 2.3-2.5).
  8. Small-threshold tails.
  9. **Paper 1 Rothe LAST** (or in parallel with a separate worker) — least leveraged, separate construction.

(Earlier tentative order — P3.1 then scout — is SUPERSEDED by the above. Key change: Lᵖ before dynamics; and
step-0 packaging + step-3 engine front-loading are the two moves that make the rest cheap.)

Planning answers land in /tmp/gpt_Q*.md; synthesize into a concrete attack order per mountain when they return.

## Paper 3 floor breakdown (Q4381, 2026-07-11) — reuse vs genuinely-new
- **P3.1 global existence** — MAIN direct reuse of Paper 2 (classical global solution, nonneg, trace,
  mild/classical agreement, boundedness). Cheap once Paper 2 exposed in the right target shape. → PHASE 1 target.
- **P3.5 compactness** — PARTIAL reuse: Paper 2 positive-time smoothing is the substrate, but P3.5 needs
  UNIFORM-IN-TAIL / eventual estimates (not Paper 2's finite-window bootstraps).
- **P3.2 uniform persistence** — BASE-level reuse only (nonneg/mass/boundedness are prerequisites); the
  persistence lower bound is a NEW dynamical argument.
- **P3.3 stability dichotomy (Thm 2.2)** — GENUINELY NEW: threshold + linearization + spectral + Lyapunov/dichotomy.
  "First serious Paper 3 dynamical-systems theorem."
- **P3.4 sectorial decay** — GENUINELY NEW analytic-semigroup infra (sectoriality, spectral gap, resolvent est).
- **P3.6 global stability (Thm 2.3-2.5)** — builds on P3.3/P3.4 (the dynamical engine).
- **CROSS-PAPER BRIDGE (already in repo)**: Paper 2 Thm 1.3 → Paper 3 Prop 1.3, Paper 2 Thm 1.2 → Paper 3 Prop 1.4.
  ⇒ the Paper 2 Lᵖ theorems are NOT purely off-line — they UNLOCK Paper 3 props. (Paper 3 Prop 1.2 /
  NegativeSensitivityGlobalEventualBound is kept INDEPENDENT of Paper 2 Thm 1.1.)
- **Longest pole = the dynamical engine** (principal eigenvalue / spectral gap shared by P3.2/P3.3/P3.6). Scout first.
- Still pending: plan-P2Lp, plan-P3special answers → append their synthesis when they land.

## Paper 1 Rothe route (Q4382, 2026-07-11)
Mechanism for the open hprodAll / step+tail block = a priori estimates + COMPACTNESS + continuous-dependence/
closed-graph stability. **NOT Minty** (chemotaxis drift/resolver coupling is not monotone in natural variables).
Standard path: Aubin-Lions compact embedding → strong L²_loc convergence of u^τ → convergence of u₊^τ + reaction
terms → elliptic resolver continuity R[u^τ₊]→R[u₊]. Discrete Gronwall only as a SUPPORT tool (finite-step
continuous dependence, time-translate stability), not sufficient alone for the passage to the limit.
Paper 1's ACTUAL machinery is whole-line frozen-profile fixed-point/Green-operator (WaveRothePos.lean), so replace
"Aubin-Lions only" with locally-uniform/GREEN-KERNEL compactness + TAIL control. Lean target = a compactness/
closed-graph statement for the Rothe orbit + a uniform-tail statement. Full analysis /tmp/gpt_Q4382.md.

## Paper 3 dynamical machinery — detail (Q4384, 2026-07-11) — sharpens steps 3/6/7
CHEAP ENTRY (do first in the dynamical block): **Thm 2.2 LINEAR dichotomy is a DIAGONAL Neumann-MODE calculation**
for the constant equilibria — NOT Krein–Rutman / principal-eigenvalue. Reuse Paper 2's cosine diagonalization →
a concrete weighted-coefficient stability theorem. Do NOT start with Henry's abstract sectorial-operator theory
(build that only if a reusable general-domain endpoint is wanted). Unstable side of Thm 2.2 = LINEAR instability
only → no unstable-manifold theorem needed.
REAL LONG POLE: Thm 2.2 nonlinear local exp. stability + Thm 2.3–2.5 GLOBAL stability need a stable semigroup in a
genuine (fractional/Sobolev) phase space + nonlinear Duhamel estimates + asymptotic compactness + Lyapunov/rectangle
→ orbit into local stable basin. For Thm 2.2 alone the long pole is the nonlinear orbit estimate in the fractional
phase space (modal threshold algebra is the easy part).
REPO STATE (concrete): LyapunovFunction.lean already has scalar entropy positivity/derivatives/nonneg — MISSING
layer = the PDE identity (interchange ∂ₜ & spatial ∫, use the PDE). IntervalDomainStabilityChain.lean lists the
unresolved global inputs: time-translate compactness, Lyapunov moment decay, moment→uniform convergence, C¹ exp
upgrade. Full analysis /tmp/gpt_Q4384.md. (Bibliographic note: source is Part II "Persistence and stabilization".)

## Paper 2 Lᵖ mountain — detail (Q4383, 2026-07-11) — sharpens step 2
ACHIEVABLE & ACYCLIC, but a SUBSTANTIAL new analytic development — does NOT follow from the χ₀≤0 mild/L²/spectral
route. THE GENUINELY-NEW HEART = one concrete WEIGHTED Lᵖ chemotaxis energy estimate + branch-specific ABSORPTION
(NOT the generic Moser bookkeeping, which the repo already has). Conclusion is boundedness before Tmax (not global
classical existence).
What bounded-interval buys (why abstract-refuted but interval-OK): finite measure, mass bounds, Ehrling/Gagliardo–
Nirenberg, elliptic estimates, semigroup smoothing. (Poincaré controls only mean-zero part; zero mode via mass
conservation / logistic mass inequality.)
Core: master weighted Lᵖ identity → FINITE-p bootstrap (NOT full Alikakos to ∞); Prop 2.5 converts one large finite
exponent to L∞ via mild formula + analytic-semigroup. Thm 1.2 branches differ: 0<m<1 central new result = finite
cross-term descent (paper eqs 4.1–4.5), not generic Moser.
REPO REUSE: IntervalDomainMoserActualAtoms.lean + IntervalDomainMoserLadderAtoms.lean (generic Moser), root-tower
algebra, IntervalDomainTheorem12/13.lean, Corollary21, EnergyStep — substantial transfer, but mostly BELOW/AFTER
the decisive Lᵖ estimate. The one new lemma to build = the weighted Lᵖ energy estimate + absorption. Full: /tmp/gpt_Q4383.md.

## SCOUTING COMPLETE (2026-07-11)
All mountains scouted: attack order (Q4388), P3 floors (Q4381), P3 dynamics (Q4384), P1 Rothe (Q4382), P2 Lᵖ (Q4383).
Each step now has a concrete "genuinely-new heart" + repo-reuse map. Execute in the DEFINITIVE ATTACK ORDER above
once χ<0 lands. The single new lemma per mountain: P2-Lᵖ = weighted Lᵖ energy+absorption; P3-engine = diagonal
cosine-mode dichotomy (reuse Paper 2, not Krein–Rutman); P3-global = nonlinear stable semigroup + Lyapunov PDE
identity; P1 = Green-kernel compactness + tail.

## Paper 2 Lᵖ weighted-energy step — the target lemma (Q4409/rm2, 2026-07-11)
The ONE genuinely-new Lᵖ lemma, concretized (see /tmp/gpt_Q4409.md for the full derivation): the weighted finite-p
energy differential inequality for the bounded-interval Neumann chemotaxis-growth system — d/dt∫u^p ≤ (diffusion
−c∫|∇u^{p/2}|²) + (chemotaxis cross-term, absorbed via Young + elliptic ∇v bound) + (logistic), yielding
y'(t) ≤ C·y(t)+C' for y=∫u^p, then Prop 2.5 lifts one large finite p to L∞ via the mild formula. This is the target
for IntervalDomainEnergyStep / the Lᵖ producer when step 2 executes.
