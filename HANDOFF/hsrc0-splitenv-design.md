# hsrc0 producer — split-envelope redesign (2026-06-09 night, Fable 5)

## NEW FINDING: hsrc0 as typed is STILL unfillable (deeper than the endpoints)

`DuhamelSourceL1ContOn (canonical family) D.T` demands a SUMMABLE envelope with
`|a s k| ≤ envelope k` for ALL `s ∈ [0, T]`.  For merely-continuous `u₀` (all a
`PositiveInitialDatum` gives), as `s → 0⁺` the family tends uniformly-in-k to
`coeffs(logistic(lift u₀))` — and a merely continuous function's cosine
coefficients need NOT be ℓ¹.  So `∑_k sup_{s∈(0,T]} |a s k| = ∞` is possible:
**no summable envelope exists near s = 0.**  The horizon retype fixed the
quantifier/continuity layer; the ENVELOPE SHAPE is the next (final) unfillable
layer of this interface.

## Consumer audit (who really needs the summable envelope?)

1. `duhamelSpectral_eq_cosineSeries_weak` (the ∑∫=∫∑ swap): feeds
   `duhamelValue_adot_eq_tsum_on` whose `hbound'` is a CONSTANT `Mdot` — it
   already runs on a k-uniform bound + parabolic gain
   (`duhamelMode_integralNorm_summable_on` divides by λ_k internally).
   → constant M suffices.  NO envelope needed.
2. `abs_duhamelSpectralCoeff_le_weak` (|duh| ≤ t·env_k) + its consumer
   `summable_abs_limitCoeff_weak`: with constant M, replace by the λ-gain bound
   `|duhamelSpectralCoeff a t k| ≤ M/λ_k (k ≥ 1), ≤ t·M (k = 0)` — the FTC
   computation already proven in `eigenvalue_mul_abs_duhamelSpectralCoeff_le_envelope`
   (it shows λ_k·|duh| ≤ env_k where env_k enters only as the pointwise bound on
   [0,t]; instantiate env_k := M constant: λ_k·|duh| ≤ M·(1−e^{−tλ_k}) ≤ M).
   ∑(e^{−tλ}M₀ + M/λ_k) < ∞ for t > 0.  → constant M suffices.
3. `limit_lift_eq_cosineSeries_weak` / `_of_subtypeCont` (hsum_duh): same as 2.
4. `summable_eigenvalue_mul_abs_limitCoeff_weak` (λ-weighted, the `hbsum`
   producer): λ_k|duh| ≤ M is NOT summable — this consumer GENUINELY needs a
   decaying envelope.  Fix inside its proof by the time split at t/2:
   `duhamelSpectralCoeff a t k = e^{−(t/2)λ_k}·duhamelSpectralCoeff a (t/2) k
      + duhamelSpectralCoeff (shifted) (t/2) k`  (general split, ALREADY proven:
   `duhamelSpectralCoeff_general_split_on`)
   - first piece: λ_k e^{−(t/2)λ_k}·(M/λ_k or t·M) ≤ M·λ_k e^{−(t/2)λ_k} → summable
     by `unitIntervalCosineEigenvalue_mul_exp_summable` (parabolic series).
   - second piece: shifted family reads s ∈ [t/2, t] ⋐ (0,T) where the
     PER-COMPACT decaying envelope env([t/2,t]) is available (from V2 per-compact
     K2 + quadratic-decay machinery `2·B_log(M,G1,G2)/(k²+1)`); the existing
     eigenvalue FTC lemma applies verbatim to the shifted family.
   → needs: constant M + per-compact env, NOT a global env.

## Revised engine-facing package

```lean
structure DuhamelSourceBddOn (a : ℝ → ℕ → ℝ) (τ : ℝ) where
  M : ℝ
  hM_nonneg : 0 ≤ M
  hM : ∀ s, 0 ≤ s → s ≤ τ → ∀ k, |a s k| ≤ M
  hcont : ∀ k, ContinuousOn (fun s : ℝ => a s k) (Set.Icc 0 τ)
  env : ℝ → ℕ → ℝ            -- env a' = decaying envelope valid on [a', τ]
  henv_summable : ∀ a', 0 < a' → a' ≤ τ → Summable (env a')
  henv_bound : ∀ a', 0 < a' → ∀ s, a' ≤ s → s ≤ τ → ∀ k, |a s k| ≤ env a' k
```

(Alternative minimal-surgery variant: keep `DuhamelSourceL1ContOn` for generic-a
lemmas, add the Bdd package only for the canonical-family entry points; decide at
implementation time by which touches fewer call sites.)

## Producer (per ChatGPT cron verdict 2026-06-09 + this finding)

- Patched family `aP s k := if s ≤ 0 then coeffs(logistic(lift u₀)) k else
  coeffs(logistic(lift (u s))) k`.
- Per-target horizons: ledger field
  `hsrc0F : ∀ τ, 0 < τ → τ < D.T → DuhamelSourceBddOn aP τ`; consumers at target
  t pick τ := (t + T)/2.
- `hM`: 2·sup-bound of logistic on the M-ball (incl. s = 0 via u₀'s bound; s = τ
  via hbound).  Fillable.
- `hcont`: right-continuity at 0 from `gradientMildSolutionData_initialApproach`
  (uniform u s → u₀) + |coeffs(f)−coeffs(g)| ≤ 2‖f−g‖∞ + logistic locally
  Lipschitz on the ball; on (0, τ] from slice time-continuity (mild/restart).
  The τ < T keeps us away from the T-endpoint data gap.
- `env a'`: quadratic-decay envelope uniform on [a', τ] from per-compact K2
  (V2 fields hG1t/hG2t at the window [a', τ] ⋐ (0,T)) through the
  `B_log(M,G1,G2)` machinery (same producer as the clamped TimeC1 envelope).
- Engines get an agreement adapter (aP = canonical on (0, τ], integral congr via
  `intervalIntegral.integral_congr_Ioo_of_le` / `Set.EqOn.aeEq_restrict`) —
  localized in 1-2 adapter lemmas, NOT threaded through every engine
  (ChatGPT cron design point).

## Execution bricks

1. `DuhamelSourceBddOn` + re-prove the 4 consumer groups (RestartWeak) from
   constant-M (+ split for the λ-weighted one).  Self-contained, hardest.
2. Patched-family producer `hsrc0F_of_data` (initial approach + coefficient
   Lipschitz + per-compact envelope assembly).
3. Adapter lemmas (aP→canonical congruence at each engine conclusion).
4. Ledger field retype `hsrc0` → `hsrc0F` (per-target) + Provider refill.

K1 (F2) campaign is INDEPENDENT and proceeds in parallel (cron2 consultation in
flight: R2 candidate route — per-mode FTC derivative from the restart identity +
term-wise series differentiation with the eigenvalue-weighted envelope — would
dissolve the K1 quadruple with zero new estimates if sound).
