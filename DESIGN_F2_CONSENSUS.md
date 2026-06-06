# F2-core design consensus (2026-06-06, two blind designers + adjudication)

Process: 1.1b blind review. Two independent designers (Opus; codex quota
exhausted till 06-10) given HANDOFF/inbox/f2-design-brief.md; both read the
live repo; reports converged. Designer B's full report:
HANDOFF/outbox/f2-design-reply.md. Designer A's returned inline (adjudicator
archive). Adjudicated by session A with kernel-level verification of the
decisive citation.

## Verdict on the 4 obstructions

1. Logistic-only hagree unsatisfiable for χ₀≠0 — **CONFIRMED** by both.
   Already neutralized (abstract `GradientMildHalfStepRestartData`,
   `paper2_theorem_1_1_from_two_restart`).
2. Two-semigroup mixing (∂ₓS^N = S^D∂ₓ) — **PHANTOM / INERT** (both
   designers). The repo already proves, hypothesis-light and Dirichlet-free:
   `deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral`
   (IntervalFullKernelSourceIBP.lean:69):
   `∂ₓ[S_N(t)Q](x) = −∫₀¹ Q'(y)·K̃(t,x,y) dy`, with `K̃(t,x,0)=K̃(t,x,1)=0`
   (conjugateKernel_at_zero/_at_one) and NO boundary condition on Q.
   The flux therefore enters the Neumann restart as an ordinary C⁰ source
   `−χ₀·Q'`; no cocycle failure, no circularity. [Verified by adjudicator
   against source.]
3. Envelope summability — **CONFIRMED by both as THE genuine frontier**, with
   a decisive refinement: the restart source family needs only the ℓ¹
   envelope of the SOURCE coefficients (1/k², i.e. `IntervalWeakH2Neumann` /
   W^{2,1}-grade of `−χ₀Q′ + L`), NOT the Wiener condition on gradient
   coefficients. Target W^{2,1}/H²ₙ certificates, never C^{2,γ} (the repo has
   zero Hölder infrastructure — both designers checked).
4. S(0)≠id — **CONFIRMED** (forces u≡0;
   intervalSemigroupIdentityAtZero_iff_zero). The chosen route avoids S(0)
   entirely (spectral restart at τ = t/2 > 0). `intervalDuhamelRepresentation_of`
   stays quarantined until restated in ε-restart form (module M0, optional).

## Winning route: R2′ (both designers, modulo naming)

Keep the proved C⁰ gradient-mild base (8.4k jobs) untouched. Add:

- **Phase 0 (go/no-go gate, χ₀=0)**: `PicardIterateUniformData` — the
  S4-strengthened induction predicate carrying EXPLICIT n-uniform constants:
  C² slice bound, source coefficient decay C/(kπ)², time-C¹ derivative bound.
  Must be DERIVED (constants computed from the contraction + fixed parabolic
  gain), never shipped as an opaque hypothesis. If this fails even for χ₀=0,
  escalate before any further investment (R3-Hölder would be the only fallback
  and it is the most expensive route).
- **M1** iterate spectral restart cocycle (`picardIter_restart_cosine_eq`):
  value restart at τ=t/2 in cosine coefficients; uses S1/S1b
  (IntervalFullKernelSpectralClean) + duhamelSpectral_eq_cosineSeries +
  restartDuhamelCoeff split. χ₀≠0 flux via the IBP-conjugate identity.
- **M2** uniform-in-n 1/k² decay of iterate restart source coefficients.
- **M3** uniform-in-n time-C¹ of the source coefficients
  (cosineCoeffs_hasDerivAt_of_smooth_param).
- **M4** limit assembly: M1+M2+M3 → GradientMildHalfStepH2SourceData →
  duhamelSourceTimeC1_of_H2Neumann_timeC1 + G2.5
  (duhamelSourceTimeC1_of_uniform_limit) + cosineCoeff_decay_of_uniform_limit
  → hMildLocal-abstract → paper2_theorem_1_1_from_two_restart.

Rejected: R1 spectral-space Picard (discards the C⁰ base, high unsat-risk in
the weighted space); R2-naive (no Dirichlet machinery needed — phantom);
R3 full Schauder (no Hölder infra, highest cost; fallback only).

## Risk register (top 3)

1. n-uniformity of the C²/decay constants fails to close (the named killer;
   moderate-high). Gate it first, χ₀=0.
2. M1 equality under the σ-integral with the (τ−σ)^{-1/2} singularity
   (Fubini/DCT with singular kernel); mitigated by 1/k² uniform convergence.
3. intervalDomainLift endpoint bookkeeping in Q′ (reuse the
   intervalFullKernel_hGradEq endpoint pattern).

## Corrections to earlier session-A records

- TASK_QUEUE 2026-06-06 roadmap and the F2 brief framed obstruction 2 as a
  genuine two-semigroup failure: **withdrawn** per the above (phantom).
- INTEGRITY_GAPS 2026-06-06 "Wiener-algebra" framing: refined — the envelope
  needed is ℓ¹ of the SOURCE (H²ₙ-grade, 1/k²), not Wiener of the gradient.
