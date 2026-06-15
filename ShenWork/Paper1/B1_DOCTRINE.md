# B1 — traveling-wave existence (χ≤0) — DOCTRINE

Goal: prove the exact monotone wave profile `∀ x, frozenWaveOperator p c U U x = 0` (+ endpoint
limits 1/0, monotone) for `α ≤ m+γ−1, χ ≤ 0, c > cStarLower p` — the ONE missing field that
unlocks the whole B1 χ≤0 existence headline (`Theorem_1_1`, Statements.lean:16285). Everything
bracketing it (logistic barrier, Shen bound, tail, monotone-trap, the reassembly
`mk_auto_limits → of_raw_frozen_stationary_branches`) is committed & unconditional.

## Route (ChatGPT-Pro-designed, cron 2477a9f9): SCHAUDER compact fixed point on the monotone trap set
Monotone iteration is BLOCKED — χ≤0 helps the barrier estimates but does NOT give quasi-monotonicity
(the nonlocal `V' = K'*Uᵞ` has a sign-changing kernel, so `V'` is not order-preserving). Shooting is
worse (the coupling V=frozenElliptic p U is nonlocal — no finite phase plane). Schauder is the sound
route; it is NOT in Mathlib (only Schauder *bases* are), so the one honest new brick is a compact
fixed-point theorem.

## 4 sublemmas (the decomposition)
- **L1** auxiliary map `T : K → K` (K = monotone wave-trap set) well-defined + invariant + locally
  smooth — the Green-kernel/linearized-operator map; uses the committed barriers + `frozenElliptic`
  (Statements:2608) resolver bounds. THE analytic crux.
- **L2** `T` continuous (local-uniform) + `T(K)` relatively compact (Arzelà–Ascoli, via uniform local
  C¹/C² bounds from T's smoothing) + the nonlocal-map continuity under local-uniform convergence
  (dominated convergence with the exponential kernel + uniform trap bound).
- **L3** [FOUNDATIONAL, reusable] local-uniform Schauder/compact fixed point: `T:K→K`, K nonempty
  convex closed, `T(K)` relatively compact, `T` continuous ⟹ `∃ U∈K, T U = U`. Build from Mathlib
  Brouwer + finite-dim (Galerkin) approximation, OR a bespoke local-uniform specialization.
- **L4** fixed point ⟹ `frozenWaveOperator p c U U = 0` — via the COMMITTED
  `paperWaveOperator_eq_frozenWaveOperator_at_fixed_point` (Statements:3077). Then package into
  `FrozenStationaryWaveProfile` (Statements:2736) → `IsMonotoneTravelingWave`.

## Terminal conditions
- success: `frozenWaveOperator = 0` profile constructed → B1 χ≤0 headline unconditional.
- proof-of-failure: a precise Mathlib/infra gap blocking L3 (the topological brick) AND a bespoke
  specialization.

## Plan: L3 first (foundational, self-contained, reusable for B2/B4 too), then L1/L2 (the analytic
core), then L4 (mechanical via the committed bridge). Codex out till Jun 18 → Opus carries.
