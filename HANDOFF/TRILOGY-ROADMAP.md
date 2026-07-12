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

## Order of attack
finish χ<0 → Paper 3 P3.1 (leverage) → then commit to one of the three off-line mountains based on the
scouting answers (bias: Paper 3 dynamics = biggest new investment, so its scouting must start now).

Planning answers land in /tmp/gpt_Q*.md; synthesize into a concrete attack order per mountain when they return.
