# K1 producer — R2 route (verdict: SOUND, non-circular; ChatGPT cron2 2026-06-09)

Raw verdict: HANDOFF/chatgpt-k1-r2-verdict.md.  Dissolves the Provider K1
quadruple (adott/hderivt/hadotcontt/hMdott) with NO new analytic estimates —
pure assembly of already-formalized pieces.

## Dependency chain (acyclic — audited)

    weak source continuity + envelope (DuhamelSourceBddOn, NO derivative fields)
      ⇒ restart identity for u   (picardLimitRestart_general — already proven)
      ⇒ per-mode ODE  c_k' = −λ_k c_k + A_k          (Lemma 2, FTC)
      ⇒ ∂_t u = ∑_k (−λ_k c_k + A_k) cos_k           (Lemma 3, series deriv)
      ⇒ adott(σ,k) = ∫₀¹ f'(u) ∂_t u cos(kπx) dx     (Lemma 4, param integral)

Circularity audit point (PASSED): the compact-uniform λ-weighted bound
∑_k sup_K λ_k|c(σ,k)| < ∞ is `summable_eigenvalue_mul_abs_limitCoeff_bdd`
(IntervalPicardLimitRestartBdd.lean, 0 sorry) — proven from the WEAK package
only, no K1 input.

## ⚠ Adversarial correction (ChatGPT)

Do NOT prove `HasDerivAt (c · k)` from the base-σ restart formula (h ≥ 0 only
⇒ one-sided derivative).  Restart from τ := σ/2: the restart identity then
holds for ALL t in a genuine NEIGHBORHOOD of σ (t > τ), giving the two-sided
`HasDerivAt` directly.  Rewrite `∫_τ^t e^{−λ(t−s)}A_k(s)ds =
e^{−λt}∫_τ^t e^{λs}A_k(s)ds` and FTC the primitive
(`intervalIntegral.integral_hasDerivAt_right`), then
`HasDerivAt.congr_of_eventuallyEq` to transfer to c.

## Lemma sequence (statements in the raw verdict; Mathlib tools per step)

1. `sourceCoeff_continuousOn_limit` — A(·,k) continuous on (0,T).
   [dominated convergence; likely already derivable from slice continuity —
   check existing `hLc`-style lemmas first]
2. `limitCoeff_restart_from` (k-th coefficient of picardLimitRestart_general)
   + `limitCoeff_hasDerivAt`: c_k' = −λ_k c_k + A_k on (0,T).
   [τ = σ/2 trick; intervalIntegral.integral_hasDerivAt_right]
3. `timeDerivSeries_hasDerivAt_eval`: ∂_t u(σ,x) = ∑_j d(σ,j)cos(jπx),
   d := −λc + A.  [hasDerivAt_tsum_of_isPreconnected on Ioo l r ⊃ K;
   summable uniform bound B_j := sup_K λ_j|c| + sup_K |A_j| — both from
   the Bdd package's window envelope + λ-weighted lemma]
   + `timeDerivSeries_continuousOn` [continuousOn_tsum].
4. `sourceCoeff_hasDerivAt_limit`: adott(σ,k) := ∫₀¹ f'(u(σ,x))·v(σ,x)·cos dx,
   HasDerivAt A(·,k) (adott σ k) σ.
   [intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le;
   dominating const L_K·V_K; logistic f' needs strict positivity on K×[0,1]
   for rpow differentiability — available (hpost)]
5. `sourceCoeffDerivLimit_continuousOn` + per-compact bound |adott| ≤ L_K·V_K.
   [intervalIntegral.continuousAt_of_dominated_interval]

⇒ fills Provider's adott/hderivt/hadotcontt/hMdott (V2 per-compact shapes).

## Interplay with the hsrc0 redesign (HANDOFF/hsrc0-splitenv-design.md)

Lemma 3's summable derivative envelope on K = [a,b] ⊂ (0,T) is exactly
`DuhamelSourceBddOn.env a'` + `summable_eigenvalue_mul_abs_limitCoeff_bdd` —
the SAME bricks.  Order of campaigns: finish hsrc0 producer (patched family +
per-target BddOn) first; K1's Lemmas 1-5 then consume it.
