# DOCTRINE — Shen Phase C overnight run (2026-06-14)

## Main goal (one sentence)
Close **Phase C (the join)** of the Shen chemotaxis-growth Lean formalization: build the EWA flux
fixed point and discharge the committed `duhamelSpectral_eigenvalueSummable_of_sourceL1` /
`DuhamelSourceTimeC1On` hypotheses UNCONDITIONALLY, so the from-scratch weighted-Wiener-algebra layer
connects to the committed PDE main theorem.

State at kickoff: Phase A+B complete & audited (149+ commits, HEAD e351e79). Codex usage-limited until
06-18 → Lean grind via **opus subagents**; ChatGPT (cron) for design/audit. ChatGPT route for the
nonlinear-map Lipschitz is back (route B, Laplace-difference, explicit constants) — see /tmp/gpt_lipschitz.out
captured into ROUTE.md.

## Avenues (ranked)

### (a) PRIMARY — the signed-off 12-brick sequence, now fully routed
Brick pipeline (each: opus subagent builds on /dev/shm/shen_C → I hostile-audit → clean-tree verify →
commit+push):
1. **C1 Flux skeleton** [IN FLIGHT, opus ab3b4e1] `EWA/Flux.lean` — realPowEWA, qFactor, chemFluxEWA,
   growthEWA + eval-agreement.
2. **ExpLipschitz** `EWA/ExpLipschitz.lean` — `seg`, `UniformFloor_seg`, `gDeriv_seg_le`,
   `expNeg_sub_expNeg_norm_le` (the ONE new calculus lemma: mean-value on segment + exp derivative).
   Independent of Flux → run in PARALLEL.
3. **FnegLipschitz** `EWA/FnegLipschitz.lean` — `negNormConst`, `negLipConst`, `FnegEWA_norm_le`,
   `FnegEWA_lipschitz` (integrate the t-shifted majorant; mirror `integrable_gammaIntegrandEWA`).
4. **RealPowLipschitz** `EWA/RealPowLipschitz.lean` — `realPowLaplaceEWA` (deterministic, fixed m) +
   `eval_realPowLaplaceEWA`, `pow_nat_lipschitz_on_ball`, `realPowLaplaceEWA_lipschitz`, `PsiBetaEWA`,
   `PsiBetaEWA_lipschitz`.
5. **E8 fixed point** — contraction (Lipschitz × C√T Duhamel small for small T) in EWA + Banach fixed
   point; agreement `eval(Φ_EWA) = intervalGradientDuhamelMap` (Paper2/IntervalGradientDuhamelMap.lean:58).
6. **E10 time-chain** — `B_t` coeffs uniform-in-(n,t) bounded (the WEAK requirement, recon e351e79) for
   `DuhamelSourceTimeC1On.derivBound`. Sublemma realPow_timeDerivative ∂_t(u^γ)=γu^{γ-1}u_t IF needed.
7. **E11 package** `DuhamelSourceTimeC1On` (PDE/IntervalDuhamelSourceTimeC1On.lean:20).
8. **E12 Picard bridge** `eval(u_n^EWA)=picardIter` (Paper2/IntervalMildPicard.lean:863) + cosine-coeff
   align c_k=cosineCoeffs(lift picardIter). MANDATORY, most-likely-forgotten.
Terminal: each brick green+0-sorry/axiom+audit FAITHFUL+committed. Goal success = committed source-ℓ¹ /
DuhamelSourceTimeC1On discharged unconditionally by the EWA layer.

### (b) FALLBACK — if a Lipschitz brick stalls on Mathlib calculus names
The mean-value lemma `norm_image_sub_le_of_norm_deriv_le_segment_01` / Banach-algebra exp Fréchet
derivative may not exist by that exact name. Attack vectors (NOT path switches — same brick):
  (b1) build the θ-derivative from the commutative-algebra one-parameter group `hasDerivAt_exp_smul_const`
       + `NormedSpace.exp_add` (exp(−t·seg θ)=exp(−tg)·exp(−tθ(f−g)), d/dθ of the second factor).
  (b2) power-series term-by-term: ‖exp(−tf)−exp(−tg)‖ ≤ Σ_n ‖(−tf)^n−(−tg)^n‖/n! ≤ t‖f−g‖·(majorant),
       using `pow_nat_lipschitz_on_ball` per term — avoids Mathlib's mean-value API entirely.

### (c) FALLBACK — if E8 agreement structurally blocked
Weakest valid partial: mild local existence in EWA¹ + source VALUE envelopes — a REAL partial theorem,
committed honestly as a FRAGMENT (banner: does NOT discharge joint-C²/adot). Not a downgrade of the goal,
a documented partial while the bridge is reworked.

### (d) FALLBACK — if E10 time-chain stalls
Recon e351e79: `DuhamelSourceTimeC1On.derivBound` is a single uniform-in-(n,t) constant, NOT summable.
Fall back to bounding |adot_n| via the committed `gDeriv` operator norm applied to `B_t ∈ A⁰` directly,
sidestepping a per-mode realPow time-derivative.

## Fallback if ALL avenues fail
Keep every proven brick committed. Write a PRECISE stall report (blocking goal file:line + missing Mathlib
lemma searched). Leave for Xiang. Do NOT fake green, do NOT axiom-escape, do NOT declare "to the limit".

## Anti-patterns to self-check (per /automode)
No time estimates. No A/B/C questions to a sleeping Xiang. No path-switch before a brick's terminal verdict.
No "abstractify difficulty" excuses (show the failing tactic chain). No sorry-and-stop. No 华罗庚 idle-poll
(while a build runs, write the next brick). No method downgrade without Xiang (avenue c is a documented
partial, not a silent weakening).
