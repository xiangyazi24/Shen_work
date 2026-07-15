# CODEX SPEC — Paper 2 Lᵖ frontier (Lemma 2.6 / Corollary 2.1 → Thm 1.2/1.3 main unconditional)

## Goal
Discharge the Lᵖ-energy / eventual-sup frontier so `Theorem_1_2_intervalDomain` and
`Theorem_1_3_intervalDomain` become unconditional (for the regimes the route covers: χ₀≤0 local
existence available; m≥1 globality). Build the missing producers; carry only genuinely-regime-specific
residuals. NO sorry/admit/custom axiom.

## Already proved (reuse by exact grepped name — do NOT rebuild)
Props 2.1 (Lᵖ resolvent), 2.2 (weighted gradient), 2.3 (ε-Young signal), 2.4 (mass), 2.5 (Moser Lᵖ⇒L∞ on
`intervalDomainM`), and χ₀≤0 local existence (via Theorem 1.1 machinery). Files per the audit:
`IntervalDomainProposition21/23`, `IntervalDomainWeightedGradientEstimate`, `IntervalDomainMass`,
`IntervalDomainMRestartedLpLinfGeneral`. The FrontierData bundle is at
`IntervalDomainStatementAssembly.lean:3300–3374` (fields: solutionInterpolation, dissipation, gradientChain,
massControl, powerIntegrability, energyFromCrossDiffusion, localExistence, globalExtension, {slow,critical,
strong}Bootstrap, eventualSupBound).

## The route (ChatGPT-designed, source-grounded DAG)
uniform L1 mass M1 (Prop 2.4)
 → regime-specific SEED inequality at p0: `p0 > max(1, ρ/2)` and `sup_t ∫ u^p0 < ∞`
 → [ `CrossDiffusionBootstrapEstimate ρ` (signed cross-diffusion, from Props 2.2+2.3 ε-Young) +
     `Lemma_2_6` GN arithmetic (Gagliardo–Nirenberg interpolation, `u^p ≤ 1 + u^{p+ρ}`) ]
 → all finite Lᵖ bounds
 → choose `P > max(1,m,γ)`
 → `Proposition_2_5` (Moser): bounded-before in L∞
 → for `m ≥ 1`: maximal-time alternative + no floor loss ⇒ `Tmax = ∞` (globality)
Uniformity: `ρ` fixed → `p` fixed → `ε` fixed → `C(ε,p)` works for the whole horizon.
Base building block: base energy equality + signed cross estimate + `u^p ≤ 1 + u^{p+ρ}` + abstract Lemma 2.6.

## Build order (each a green single-file check, then next)
1. `Lemma_2_6` abstract GN arithmetic lemma (the `∫u^p ≤ …` interpolation closing the energy inequality) →
   `Corollary_2_1`.
2. `CrossDiffusionBootstrapEstimate ρ` from Props 2.2 + 2.3 (signed cross-diffusion ε-Young absorption).
3. the regime seed `∃ p0 > max(1,ρ/2), sup_t ∫u^p0 < ∞` (from mass M1 + the seed inequality).
4. wire 1–3 → all-Lᵖ → `Proposition_2_5` → bounded-before; then `globalExtension` (m≥1 maximal-time
   no-floor-loss alternative).
5. discharge the FrontierData fields → `Theorem_1_2_intervalDomain` / `Theorem_1_3_intervalDomain` for the
   covered regimes. Carry genuinely regime-specific residuals (0<m<1 finite-Tmax floor-loss) as NAMED hyps.

## Constraints
- New files under `ShenWork/Paper2/` (e.g. `IntervalDomainLp*`). Do NOT edit `Statements.lean`.
- **NO git commands** (only write .lean); orchestrator commits.
- Verify ONLY `env LAKE_NO_UPDATE=1 lake env lean <file>` + `lake build ShenWork.Paper2.<Module>`. No full-tree build.
- No sorry/admit/native_decide/custom axiom. ≤100 cols. Reuse existing lemmas by exact name.
- If a sub-step walls, STOP + report precise goal file:line + missing fact. Do NOT fake.

## Report
Theorem names + `#print axioms`, which of steps 1–5 closed, and whether Thm 1.2/1.3 main are now
unconditional (for which regimes) or the precise carried residual.
