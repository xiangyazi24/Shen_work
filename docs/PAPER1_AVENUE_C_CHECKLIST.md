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
