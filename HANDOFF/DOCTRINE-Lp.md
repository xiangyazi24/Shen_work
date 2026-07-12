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
