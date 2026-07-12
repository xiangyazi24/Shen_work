# DOCTRINE — Paper 2 Lᵖ mountain (Theorem 1.2/1.3) — 2026-07-12 (Xiang: do it, don't wait)

## Main goal
Make `Theorem_1_2 intervalDomain p` UNCONDITIONAL for the m=1 critical branch (χ₀<chiBeta),
by discharging the carried Lᵖ frontiers — chiefly the genuinely-new heart.

## Ground truth (verified 2026-07-12) — the Q4409 chain is ALREADY built conditionally
- IntervalDomainEnergyStep.lean: full finite-p energy chain of_frontiers (balance → gradient
  inequality → cross bootstrap → Young → closed derivative bound →
  intervalDomain_lp_energy_derivative_le_constant_of_explicit_cross_bound = the finite-p Gronwall).
- intervalDomain_structuredMoserBootstrapData_of_regularity CARRIES exactly 6 frontiers:
  1. **hcross : CrossDiffusionBootstrapEstimate** ← THE genuinely-new analytic heart (Q4383/Q4409).
  2. hboot : AbstractLpBootstrapHypothesis
  3. hdiss : MoserDissipationDropBefore
  4. hrel  : RelativeMoserInterpolationBefore
  5. hLpMono: LpPower monotonicity
  6. hEndpoint: Moser quantitative endpoint
  (2-6 = generic Moser bookkeeping — roadmap says repo already has generic Moser; likely dischargeable.)
- Moser closure (StructuredMoserBootstrapData.boundedBefore → LpPowerBoundedBefore → L∞) exists.
- CrossDiffusionBootstrapEstimate def (Statements.lean:1126):
  ∀eps>0 ∀pExp>1 ∃Ceps ∀t∈(0,T), crossDiffusionEnergyTerm ≤ eps·∫u^(p-2)|∇u|² + Ceps·∫u^(p+rho).

## Avenue (a) — MAIN: produce CrossDiffusionBootstrapEstimate unconditionally (m=1, rho=0)
Content (Q4409): |χ₀|(p-1)∫u^(p-1)|u_x||A| ≤ eps·G + Ceps·∫u^(p+rho), A=v_x/(1+v)^β.
Uses: (i) |A|≤|v_x| since v≥0,β≥1 ⇒ (1+v)^{-β}≤1; (ii) elliptic ∇v bound (v_xx=μv−νu^γ) → ‖v_x‖
controlled by u; (iii) Young split into eps·gradient + lower order. Needs the repo elliptic/H¹ v-gradient lemma.

## Avenue (b) — discharge the 5 Moser-bookkeeping frontiers (hboot/hdiss/hrel/hLpMono/hEndpoint) from regularity.
## Avenue (c) — wire the regularity-derived PDE/IBP/time-Leibniz frontiers (of_regularity producers exist).

## Do NOT touch Codex-owned χ<0 files. New Lᵖ work in NEW files or the existing 0-sorry Lp files' producers.
## Build: single-file lake env lean; cold gate uisai2 (don't interfere with Codex's χ<0 cold build).

## ⚠️ CORRECTION 2026-07-12 — check-existing catch: the Lᵖ mountain is ~90% ALREADY BUILT
Grep-before-build revealed the scout Q4559 (stale chatgpt-scratch snapshot) proposed REBUILDING
what already exists. Actual repo state (all 0-sorry, mostly committed by Xiang 2026-06-21):
- **HEART DONE**: `intervalDomain_crossDiffusionBootstrapEstimate_of_classical` (IntervalDomainCrossDiffusionBootstrap.lean:591)
  proves CrossDiffusionBootstrapEstimate intervalDomain p T (2γ) u v UNCONDITIONALLY. Already WIRED
  into IntervalDomainL2CrossControl.lean:495. Sub-lemmas (sourceL2_mul_power_le, young_sourceL2,
  bootstrap_bound) all present.
- **Energy chain DONE**: IntervalDomainEnergyStep (finite-p Gronwall of_frontiers) + _of_regularity producers.
- **Moser climb DONE**: intervalDomain_all_exponents_of_moser_iteration_chain (LpMonotonicity) takes seed
  LpPowerBoundedBefore p0 → ∀pExp>1. Moser closure → L∞ done.
- **Seed producer DONE**: intervalDomain_LpPowerBoundedBefore_of_abs_energy_gronwall (LpMonotonicity:519)
  gives LpPowerBoundedBefore p from an energy-Gronwall bound.

### REAL remaining gap for Theorem_1_2 m=1 critical branch = WIRING, not new analysis:
1. Discharge `hcriticalBootstrap`: ∃rho>0, [cross DONE, rho=2γ] ∧ ∃p0>max 1(γN), LpPowerBoundedBefore p0.
   → produce the seed at some p0>γN by applying the finite-p energy chain at p0 + cross estimate +
   the abs_energy_gronwall seed producer + Moser climb. Mostly wiring existing pieces.
2. Discharge `hcriticalGlobalBound` (eventual sup from the Lᵖ bound → IsPaper2Bounded).
3. Discharge `hlocal` / `hglobalExtension` (local existence + bounded-before⇒global — shared w/ existence).
NOTE: cross question lpQ_cross is MOOT (heart done); lpQ_seed / lpQ_abstract still relevant for the wiring.

## WIRING BLUEPRINT (2026-07-12) — Theorem_1_2 m=1 unconditional = thread these existing pieces
1. cross [DONE]: intervalDomain_crossDiffusionBootstrapEstimate_of_classical hsol → CrossDiffusion(rho=2γ).
2. energy Gronwall: intervalDomain_Lp_abs_energy_gronwall_of_neumann_by_parts_bound (LpMonotonicity:308)
   — input = Neumann-by-parts + cross bound (from IntervalDomainEnergyStep + step 1) → deriv∫u^p ≤ C∫u^p+C'.
3. base seed: intervalDomain_LpPowerBoundedBefore_of_abs_energy_gronwall (LpMonotonicity:519) ← step 2.
4. Moser climb: intervalDomain_all_exponents_of_moser_iteration_chain (LpMonotonicity:837)
   ← hbase(step 3) + hstep(cross+energy) + hu_nonneg + hpow_int → ∀pExp>1, LpPowerBoundedBefore.
5. StructuredMoserData: intervalDomain_structuredMoserBootstrapData_of_regularity (6 frontiers:
   hcross[done], hboot=AbstractLpBootstrapHypothesis[?], hdiss[?], hrel[DONE MCL:86], hLpMono[LpMono], hEndpoint[?]).
6. boundedBefore: IntervalDomainStructuredMoserBootstrapData.boundedBefore.
7. hcriticalBootstrap := ⟨2γ, cross, p0, LpPower from 3/4⟩. Cor21/Prop25 producers exist
   (need hEnergyFromCrossDiffusion = intervalDomain_LpBootstrapEnergyInequality_of_regularity).
8. Theorem12 critical branch → Theorem_1_2 intervalDomain p.

### OPEN sub-residuals to verify/discharge (the actual remaining work, all WIRING-level):
- AbstractLpBootstrapHypothesis (hboot), MoserDissipationDropBefore (hdiss), MoserQuantitativeEndpoint (hEndpoint)
  — check for _of_regularity producers; likely generic Moser, dischargeable.
- The Neumann-by-parts bound input to step 2 (confirm produced from EnergyStep + cross).
- hcriticalGlobalBound (Lᵖ bound → IsPaper2Bounded eventual sup).
- hlocal / hglobalExtension (local existence + bounded-before⇒global) — shared with the existence machinery.
This is Codex-scale multi-piece ASSEMBLY (exact signatures), best done fresh-context or by Codex — NOT new analysis.

## ⚠️ REVISED PIN (2026-07-12, after Q4562 + deep trace) — the ONE deep core
Q4562: the L²(p0=2) seed only clears the Moser threshold p0>γN for γ<2, and Theorem_1_2 has no γ<2 hyp.
BUT the interval AVOIDS the Moser γ-threshold via the **1D Sobolev bypass** (P3Moser1DBypassAssembly.lean, 0-sorry):
  1D H¹↪L∞ ⇒ L² bound + H¹ gradient-energy bound → IsPaper2BoundedBefore, FOR ALL γ.
  Chain (intervalDomain_boundedBefore_of_paperPositive_H1local_average): mass (free, Prop 2.4) + L² seed
  frontier (P3MoserLemmas:156) + H¹ sliding-window bounds (hlocal/havg) → boundedBefore.
The H¹ window/averaged/local machinery (IntervalChiNegH1AverageWiring: H1_backward_bound_of_scalarDI_before,
H1Window) is GENERIC — it consumes a scalar DI `deriv(H1energy u τ) ≤ A·H1energy u τ + B` and outputs havg/hlocal.

### THE ONE genuinely-new remaining lemma for Theorem_1_2 critical branch (χ₀<chiBeta, m=1):
  **The H¹ energy scalar differential inequality  deriv(H1energy u τ) ≤ A·H1energy u τ + B  for χ₀ < chiBeta p.**
  χ<0 template: IntervalChiNegH1Bridge.lean (terms (-p.χ₀)·(H1PhysicalTaxisX + H1PhysicalUvxxX)).
  For 0≤χ₀<chiBeta the chemotaxis term is "bad-sign" but absorbed by the smallness χ₀<chiBeta (Cauchy-Schwarz
  H1lapL2Norm·H1gradL2Norm + Young; chiBeta is exactly the absorption threshold). Everything downstream reuses:
  scalar DI → H¹ window machinery → 1D bypass → boundedBefore → Corollary_2_1/hcriticalGlobalBound → Theorem_1_2.
  This is the genuinely-hard heart (NOT the cross estimate, which is done) — Codex-scale, χ<0 H1Bridge is the template.
