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

## VERIFIED ASSEMBLY CHAIN (grep-confirmed 2026-06-15, NOT ChatGPT-named)
The B1 χ≤0 headline = `Theorem_1_1` (def Statements:16285). The COMMITTED bridge that consumes a
constructed fixed point is **`Theorem_1_1.of_assumed_frozenStationaryProfile_trap_branches`**
(Statements:~16345) [NOT cron2's hallucinated `of_assumed_fixed_point_construction_branches`].
Negative branch input it needs: `∀ p (α≤m+γ−1)(χ≤0) c (cStarLower p<c), ∃ U,`
  `InMonotoneWaveTrapSet (kappa c) 1 U  ∧  FrozenStationaryWaveProfile p c U  ∧`
  `ShenUpperBoundNegative c U  ∧  (∀κ₁…, HasWaveRightTailAsymptotic c κ₁ U)`.
- `FrozenStationaryWaveProfile` is built by **`mk_auto_limits`** (3185), hyps (exact):
  `0<c · hU_pos(∀x,0<U x) · IsCUnifBdd U · hstat(∀x frozenWaveOperator p c U U x=0) · U→1 atBot · U→0 atTop`
  (it derives the V endpoint limits internally via `frozenElliptic_tendsto_at{Bot,Top}_of_U_tendsto`).
- `to_monotoneTravelingWave` (3224) additionally needs `hUmono(deriv U≤0)` + `hVmono(deriv V≤0)`.

### The 7 fixed-point properties → who supplies them
1. hstat (frozenWaveOperator=0)  ← L4 GreenIdentity chain — DONE modulo trap decay/C¹ (flux_ibp committed)
2. hUmono (deriv U≤0)            ← ✅ COMMITTED `InMonotoneWaveTrapSet.deriv_nonpos` (Statements:5021)
3. hVmono (deriv V≤0, V'≤0)      ← 🔧 DISPATCHED `frozenElliptic_deriv_nonpos_of_monotone_trap`
                                    (a3ea701b) — route V=G∗Uᵞ, V'=G∗(Uᵞ)'≤0; cron2's "hardest endgame"
4. hU_pos (0<U)                  ← fixedPoint_pos (strict, from lower-barrier/Shen) — PENDING
5. hU_bdd (IsCUnifBdd U)         ← trap bound + T-smoothing — PENDING (near-trivial from trap)
6. hU_lim_neg (U→1 atBot)        ← 🔧 fixedPoint_leftLimit_one, lower-barrier squeeze [cron2 designing]
7. hU_lim_pos (U→0 atTop)        ← construction at-top limit (trap/Shen) — PENDING
+ ShenUpperBoundNegative         ← ✅ committed logistic Shen bound (`logisticProfile_shenUpperBoundNegative`)
+ HasWaveRightTailAsymptotic     ← ✅ committed tail theorem (expose in bridge shape)

### THE GATE: `∃ U` itself = the SCHAUDER FIXED POINT in the trap
needs n-D Brouwer [K2 a18e795a running] + L2 invariance [ChemotaxisSandwich, cron designing] +
L2 compactness [WeightedCompactness]. Everything that assembles FROM such a U is committed.
So the sole remaining constructive game = Schauder fixed point + the PENDING props (4,5,7) + V'≤0(3).

### 统筹 streams (2026-06-15): K2(topological,critical) · V'≤0(a3ea701b,hardest endgame) ·
cron(ChemotaxisSandwich L2 invariance) · cron2(leftLimit_one + bridge verify). Codex out till Jun 18.
