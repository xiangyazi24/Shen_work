# UNCONDITIONAL doctrine — discharge EVERY carried conditional across all 3 Shen papers

Goal (Xiang directive 2026-06-20, voice): the three papers are currently FAITHFUL but CONDITIONAL; discharge ALL
carried conditional hypotheses 挨个证, make every headline FULLY UNCONDITIONAL (zero carried analytic hypotheses,
modulo the genuine paper antecedents like "positive initial datum"). 我不要这些 conditional 的东西.

Method (unchanged, strict): per item — codex grinds → rsync-resync + build headline + ROOT + #print axioms clean →
READ PROOF TERM (consume not project) → independent hostile opus audit → commit only if genuine. ChatGPT (cron) in
parallel for analytic proof skeletons of the foundation facts. No effort cap, no re-wrappers, honest only.

## The inventory (ranked by dependency — prove the foundation first, it is what everything reduces to)

### FOUNDATION F — explicit Neumann heat-semigroup standard facts (P2 HpdeFacts + energy-core + neumann ALL reduce here)
Prove from the concrete cosine kernel K_N(t,x,y)=Σ_k e^{-(kπ)²t} φ_k(x)φ_k(y), φ_k=cos(kπ·):
- F1. t^{-1/2} gradient smoothing bound  ‖∂ₓ S_N(t) f‖₂ ≤ C t^{-1/2} ‖f‖₂  (NeumannHeatGradientTMinusHalfBound)
- F2. differentiated cosine-series uniform convergence on r≥ε (Weierstrass M-test, e^{-(kπ)²r} dominates)
- F3. interior zero-time trace  lim_{r↓0} B_N(r)F = ∂ₓF  locally uniformly (Abel)
- F4. semigroup form identity + generator identity  ∂_r S_N = ∂ₓₓ S_N  (term-by-term)
- F5. Duhamel time-derivative interior PDE identity; L²-Lebesgue endpoint; DCT dominators
- F6. global Duhamel-cosine reconstruction (BFormDuhamelCosineReconstructionData) from F2-F5

### P2 atoms (assemble once F is proven)
- A1. DB  ConjugateMildExistenceData — conjugate-Picard contraction + Banach fixed point (banked √t bound) [codex GRINDING]
- A2. DT  TruncatedConjugateMildExistenceData — truncated Picard contraction (same machinery, faithful flux)
- A3. Hinf ConjugatePicardInfThresholdData — Duhamel integrability constants CQ/CL + hQ_int/hB_int/hL_int (from F + flux bounds)
- A4. hsmall — small-T threshold (choose T; A√T+BT ≤ floor/2)
- A5. HpdeFacts  BFormSpectralPdeAgreementStandardFacts — = F2-F6 (prove them)
- A6. HtruncatedEnergy  TruncatedNegativePartEnergyCoreRegularData — weak energy estimate + F-facts + Sobolev (energy_cont/deriv/integrable)
  **A6 route (ChatGPT, verified):** standard local weak neg-part argument; chemotaxis cancels (disjoint support u_+·(u_-)_x=0, w irrelevant), diffusion=‖(u_-)_x‖², reaction≤ℓ‖u_-‖² (ℓ=0 for truncated logistic). ONE genuine Mathlib GAP: the Lions-Magenes H^1/H^{-1} neg-part chain rule ½d/dt‖u_-‖²=<u_t,-u_-> (Mathlib has posPart/negPart Lipschitz but NOT this energy chain rule) — route: Steklov time-averaging/mollification + pass to limit + a project a.e.-Gronwall lemma (Mathlib Gronwall is right-deriv based). ATTACK via Steklov; skeleton /tmp/gpt_A6.txt.
- A7. hLinearStripCore — IsClassicalNeumannLinearDriftSuperSolution. **RESOLVED (ChatGPT A7, verified):** the naive
  super-solution with reaction C₀=a−bu^α is FALSE — residual L u = −χ₀·u·w_x is SIGN-CHANGING (w_x = (v−u)/(1+v)^β −
  β·v_x²/(1+v)^{β+1}, counterexample u=c+εcos(πx)). FIX: redefine the concrete reaction to absorb the divergence
  remainder: C_exact := a − bu^α − χ₀·w_x (w_x explicit via resolver v_xx=v−u; BOUNDED since v−u,v_x bounded, 1+v≥1).
  Then L_{B,C_exact} u = 0 EXACTLY (u is genuine super+sub-solution). Keep B=−χ₀w. Recompute −C_exact ≤ Dbar' bound
  (w_x bounded). Squared-barrier comparison goes through with the corrected bounded C_exact. CODEX TASK (queued after
  foundation): change bformConcreteReact → C_exact, prove residual≡0, discharge hLinearStripCore unconditionally. Skeleton
  /tmp/gpt_A7.txt.
- A8. regularityFrontier  BFormDirectFrontier — spectral/restart/resolver data (REUSE F + resolver; also fixes the redundancy)
- A9. neumannFacts — chemotaxis interchange DCT license (from F + chemFlux boundary-vanishing resolverGradReal_zero) + heat/logistic leg Neumann
- (huPaper = the paper's positive-initial-datum ANTECEDENT — NOT discharged, it is the theorem's hypothesis)

### P1 frontiers
- B1. LowerPinnedWaveCubeApproxData — finite-cube Brouwer approximate-fixed-point data (from own brouwer_fixedPoint + ε-net + compactness)
- B2. StationaryGreenRepresentationThreadData — explicit Green representation on the interval (cosine/Green kernel)
- B3. C²/C³ bootstrap regularity from the stationary equation

### P3 frontier
- C1. IntervalDomainSectorialMainlineCoreExistence — sectorial semigroup (explicit cosine rep on interval) + small-data
  global existence + uniform persistence parts 1-4 (the hard Section-4 analysis)

## Terminal condition per item
Each carried field REMOVED (or reduced to genuine paper antecedents only); the named "standard fact" PROVEN from the
explicit representation, not carried; build root clean + axioms {propext,Classical.choice,Quot.sound}; opus GENUINE.
Final: every headline carries ONLY the paper's real antecedents (params in admissible region, positive initial datum) —
no analytic Mathlib-gap hypothesis.

## Order
F (foundation, ChatGPT skeletons + codex) → A1/A2 (existence) → A5/A6/A9 (= F-assembly) → A3/A7/A8 → A4 → B → C.
Start: A1 (DB) codex grinding; fire ChatGPT on F1/F2/F3 skeletons in parallel.
