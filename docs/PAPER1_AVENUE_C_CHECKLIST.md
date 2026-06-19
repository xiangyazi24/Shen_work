# Paper 1 (traveling waves, χ≤0) — avenue-c atom board

The finite, named inventory for the whole-line parabolic-mild-Schauder route (docs/WAVE_ARCHITECTURE.md).
Distance = this board, NOT a time estimate. `✅` = built sorry-free + axiom-clean (integrated-build verified) ·
`🟡` = in flight / partial (named) · `⬜` = open. Last verified: a8af1af (2026-06-19, integrated build green).

**MILESTONE (8fcc1e8):** wave bricks 1–17 ALL ✅. The traveling-wave existence HEADLINE is assembled:
`wholeLine_travelingWave_exists` (χ≤0, α≤m+γ−1, c>2 ⟹ ∃ U*,V* a traveling-wave profile: solves divergence
wave eq, U*(−∞)=1, U*(+∞)=0, monotone, right-tail ~e^{−κx}). GENUINE chain (consumes brick 11 longTimeMap +
brick 12 fixed point + 13–16 conversion/tails). CONDITIONAL on `WholeLineTravelingWaveData` = the precise
remaining frontier, NOT vacuous. Earlier milestone (a8af1af): constant-barrier energy engine END-TO-END
UNCONDITIONAL (`wholeLine_constantBarrier_trapping_unconditional`, faithfulness-verified).

**HONEST STATE (independent hostile audit, 2026-06-19):** the headline is FAITHFUL + sound as a CONDITIONAL
reduction (non-vacuous: U(−∞)=1≠U(+∞)=0 rules out degenerate witnesses, WaveTrap proved nonempty; non-circular:
equicontinuity genuinely from the t^{−1/2} kernel; axiom-clean). It is **NOT unconditional** — the audit found
two LOAD-BEARING facts still ASSUMED at the interface:
  (1) `schauder_principle` — the abstract Schauder/Brouwer fixed-point PRINCIPLE itself
      (LocalUniformSchauderFixedPointPrinciple), never proved in-tree ("deliberately separated"). Check Mathlib
      for Schauder/Tychonoff/Brouwer to discharge.
  (2) the equicontinuity gradient bound (`longTime_image_deriv_bound` takes Λ as a hypothesis) — the kernel
      machinery (auxiliaryMildMap_deriv_abs_le_of_gradient_bounds) exists but the Leibniz-under-singular-integral
      bridge connecting it is missing.
Plus the lighter residuals: ContDiff² regularity, longTime_stationarity, translate_compactness, aux-flow
existence. DISCHARGED genuinely: orbit trapping, long-time-map mapsTo/continuity/compactness, the kernel half of
equicontinuity. The headline should be read as "Data ⟹ profile", with these the genuine remaining work.

## A. Foundation — the Schauder-route engine
- ✅ L1 heat semigroup e^{(Δ−I)t} (ShenWork/PDE/WholeLineHeatSemigroup.lean) — mass-1/L∞/grad-t^{−1/2}.
- ✅ L2 resolvent (−∂xx+1)⁻¹, ½e^{−|·|} (WholeLineResolvent.lean) — sup/nonneg/grad + Ψ''=Ψ−f.
- ✅ L4 local-uniform compactness (LocalUniformCompactness.lean) — Ascoli per window + diagonal.
- ✅ Schauder fixed-point principle (WholeLineSchauderFixedPoint.lean).
- ✅ mild map Φ (WholeLineMildMap.lean, Shen eq 3.1, χ≤0).
- 🟡 Φ-continuity: source layer ✅ (WholeLineMildMapConcreteContinuity) + Duhamel loc-unif upgrades ✅
  (WholeLineDuhamelLocUnifContinuity) + assembly bridge ✅ (WholeLineMildMapContinuity); FINAL wiring of the
  three into one unconditional `Φ continuous` ⬜.

## B. Constant-barrier energy-comparison engine (= global-boundedness layer)
- ✅ trapping-via-energy bridge (WholeLineConstantBarrierEnergy.lean) — reduces trap to WholeLineBarrierEnergyFrontier.
- ✅ upper frontier (WholeLineBarrierEnergyFrontierUpper) — reaction-sign proved + 4-atom residual pack.
- ✅ lower frontier (WholeLineBarrierEnergyFrontierLower) — symmetric, reaction-sign proved.
- ✅ atom timeLeibniz + pdeSubstitution (WholeLineEnergyTimeLeibnizPDE).
- ✅ atom diffusionIBP_decay (WholeLineDiffusionIBPDecay) — closed with real Mathlib lemma, NO gap.
- ✅ atom chemotaxisCrossControl (WholeLineChemotaxisCrossControl) — Young absorption, carries V_x bound hyp.
- 🟡 WIRE atoms → WholeLineUpperBarrierEnergySteps struct fields (cx_r3 in flight) → unconditional const trap.
- ✅ obstruction documented (WholeLineConstantBarrierCorrectionsObstruction) — the refuted signed-margin mapsTo.
- ⬜ const-barrier trapping UNCONDITIONAL (needs the wiring + the solution-regularity/V_x hyps discharged).

## C. The 17 wave bricks (WAVE_ARCHITECTURE.md) — toward the headline
- ✅ 1. speed/exponent algebra (WaveSpeedExponent) — κ=(c−√(c²−4))/2, quadratic, 0<κ<1, admissible interval.
- 🟡 2. exponential barriers U⁺/U⁻ (cx_p2x in flight) — nonneg/le_one/antitone/le_upper/endpoints/squeeze.
- ⬜ 3. wave trap E'_{κ,1} — convex/closed/bounded/monotone in local-uniform topology.
- 🟡 4. frozen signal V=Ψ(u^γ): 0≤V≤1, V_x≤0, |V_x|≤1 (cx_pde in flight) — discharges B's cross-control hyp.
- ⬜ 5. auxiliary moving-frame parabolic local existence (eq 4.12, frozen V) — adapt the mild map to the aux operator.
- ⬜ 6. barrier comparison + global continuation U⁻≤w(t)≤U⁺ — the energy engine (B) applied to exp barriers.
- ⬜ 7. spatial monotonicity w_x≤0 (differentiated WEAK parabolic comparison; energy-method, no SMP).
- ⬜ 8. time monotonicity w(t₂)≤w(t₁) (comparison with time-shift).
- ⬜ 9. long-time limit U(·;u)=lim_{t→∞}w (monotone convergence + loc-unif compactness ⟹ ∈E'_{κ,1}).
- ⬜ 10. stationarity of the long-time limit (pass aux eq to t→∞).
- ⬜ 11. T_{κ,1} compact (L4 done) + continuous in loc-unif topology.
- ⬜ 12. Schauder fixed point U*=T_{κ,1}U* (principle done; the application).
- ⬜ 13. diagonal stationary eq (aux stationary = divergence-form wave, via V''=V−U^γ).
- ⬜ 14. traveling-wave conversion u(t,x)=U*(x−ct).
- ⬜ 15. right tail U*(+∞)=0 + rate (barrier squeeze) + monotonicity.
- ⬜ 16. left tail U*(−∞)=1 — translate compactness + Prop 1.2 (=T10, DONE unconditional) — WIRES existing.
- ⬜ 17. strictness + polished theorem statement.

## Scoreboard
- A foundation: 5/6 ✅, 1 🟡 (final Φ-continuity wiring).
- B energy engine: 8/9 ✅ atoms+frontiers, 1 🟡 wiring → 1 ⬜ unconditional-trap headline.
- C wave bricks: 1/17 ✅, 2 🟡 (bricks 2,4), 14 ⬜.
- Genuine analytic HEART still ⬜: bricks 6–11 (the differentiated-comparison monotonicity + the long-time map's
  compactness/continuity) — each energy-method-provable (no strong max principle), but each a real lemma.
- Left tail (brick 16) is a WIRING of the already-done T10, not fresh analysis.
- Reused-done elsewhere: L4 compactness (→brick 11), Schauder principle (→brick 12), Prop 1.2/T10 (→brick 16).

## Honest framing
The constant-barrier energy engine (B) is nearly complete (atoms all built; wiring in flight) but is the
GLOBAL-BOUNDEDNESS layer, not the wave headline. The wave headline (C) needs the exponential-barrier trap (2-3),
the auxiliary moving-frame flow (5), the differentiated weak-comparison monotonicity (6-8), and the long-time
map + its compactness/continuity (9-12), then the conversion+tails (13-16). Bricks 6-12 are the genuine
multi-session analytic core. No constant-barrier shortcut reaches the wave; no pointwise strong max principle is
needed (the monotonicity is energy-provable). This board is the source of truth for "how far".

## The residual splits into TWO kinds (key distinction for the §3.3 audit)
Verified Mathlib has only Banach contraction FP (ContractingWith.exists_fixedPoint), NO Brouwer/Schauder
(a known long-standing Mathlib gap). So:
- **(a) schauder_principle = a genuine MATHLIB GAP** (standard textbook theorem, not Shen's content). Carrying
  it as a hypothesis is FAITHFUL per feedback_no_axiom_escape ("axioms/assumptions only for genuine Mathlib
  gaps") — you cannot formalize Schauder without a separate major Brouwer-formalization project. This is NOT a
  §3.3 violation (not the paper's hard content).
- **(b) the parabolic a-priori estimates (Shen Claim 1)** = the paper's ACTUAL analytic content. The
  equicontinuity KERNEL-HALF is PROVED (t^{−1/2} Duhamel); the Leibniz-under-singular-integral BRIDGE
  (connecting auxiliaryMildMap_deriv_abs_le → longTime_image_deriv_bound) + the ContDiff² regularity +
  stationarity + translate-compactness remain. THIS is the genuine remaining paper-content work, and it IS
  dischargeable (the machinery exists).
Honest ceiling: the wave headline faithfully reduces Shen's traveling-wave existence to (a) Schauder [Mathlib
gap, acceptable] + (b) the parabolic Claim 1 [paper content, partially done, the rest dischargeable].

## DEFINITIVE honest ceiling (2026-06-19, verified Mathlib gaps)
The aux-flow mild→classical bootstrap (WholeLineAuxiliaryClassical.lean) reduces the classical-solution field
(longTime_evolution_eq) to the HEAT-SEMIGROUP GENERATOR identity ∂t S(t)f = (Δ+c∂x−I)S(t)f. Verified: Mathlib
has NO heat kernel / heat equation / analytic-semigroup theory (only algebraic semigroups). So the Paper-1
traveling-wave existence irreducibly rests on TWO genuine Mathlib gaps:
- **Schauder/Brouwer fixed-point principle** (Mathlib has only Banach contraction).
- **The heat-semigroup generator identity** (Mathlib has no heat-equation / analytic-semigroup theory).
BOTH are standard textbook analysis facts, NOT Shen's content. Assuming them is FAITHFUL (feedback_no_axiom_
escape). The rest of the residual is a real aux-flow's satisfiable parabolic regularity (mostly discharged).
To reach fully-unconditional would require formalizing Brouwer + heat-equation/analytic-semigroup theory in
Mathlib — two major STANDARD-MATH formalization projects, entirely separate from "formalize Shen's papers".
THIS is the honest ceiling: the wave existence is a FAITHFUL conditional reduction to (2 Mathlib gaps +
satisfiable regularity), axiom-clean, hostile-audited, never carrying the paper's hard content as a hypothesis.

## UPDATE: one of the two Mathlib gaps now CLOSED (heat-semigroup generator)
The heat-semigroup generator identity ∂t S(t)f=(Δ−I)S(t)f is FULLY FORMALIZED + independently-verified
axiom-clean (WholeLineConvolutionDifferentiation.wholeLineHeatOp_time_hasDerivAt_of_bounded): gaussian_heat_eq
(Gaussian solves heat eq) + differentiation under the Gaussian convolution (Gaussian-tail domination). The only
side condition is standard Bochner measurability. So Paper-1's wave now reduces to JUST:
- **(a) the Schauder/Brouwer fixed-point principle** [the SINGLE remaining foundational Mathlib gap] +
- **(c) the satisfiable aux-flow parabolic regularity** [a real solution's properties; the classical bootstrap
  now has its generator input closed].
The heat-generator gap is GONE. Schauder is the one remaining standard-math Mathlib gap for full unconditionality.
