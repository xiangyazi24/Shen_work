# hsrc0 deletion — route break (Fable, 2026-06-11)

## What hsrc0 is
`TowerInputs.hsrc0 : ∀ n, DuhamelSourceTimeC1 (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)`
(IntervalPicardSourceTower.lean:174). `DuhamelSourceTimeC1` (IntervalDuhamelClosedC2.lean:1502) demands:
- `hderiv : ∀ s n, HasDerivAt (fun r => a r n) (adot s n) s` — **two-sided, EVERY s ∈ ℝ**.
- `hadotcont : ∀ n, Continuous (fun s => adot s n)` — **all of ℝ**.
- envelope summable + `henv_bound`/`hderivBound` **only for s ≥ 0**.

## Why it's a residual (the real obstruction)
The adot machinery — BOTH the two-sided `logisticSource_adot_hasDerivAt`
(IterateTimeC1.lean:413) and W9's within-version — **CONSUMES** a level-n
`src : DuhamelSourceTimeC1` to produce the level-(n+1) FIELD source-coeff
derivative. It is the level n→n+1 step, NOT a producer of the level-(n+1)
GLOBAL package. The tower produces only window-local `winAdot` legs (strictly
interior `hi < T`); the global package is an INPUT residual at every level.
The two-sided machinery is gated on **open `U ⊆ Set.Ioi offset` (s > 0) + a
positivity floor** on the window — so s ≤ 0 and s > T are NOT covered.

## Consumers of H.hsrc0 in tower_succ (SourceTower.lean)
- σ<T branches are ALREADY hsrc0-free (winAdot / W3 bricks).
- `hsrcσ` (l.443, shifted pkg) → only σ=T branches of hrepr_sum (l.470) and hG2 (l.538).
- `hrepr_agree` (l.484) via `hagree_succ_of_sourceSubtypeCont` — uses H.hsrc0 n for ALL σ.
- `windowAdotLegs_step` (l.562) — uses H.hsrc0 n for the interior winAdot recursion.

## The fork
**Path A — prove hsrc0 as a THEOREM (global package by induction on n).**
Base: `picardIter … 0 = const in time` → source constant in s → trivial global
DuhamelSourceTimeC1 (adot=0). Step: assemble the level-(n+1) global package.
- PRO: zero consumer changes; drop-in `hsrc0 := canonicalSource_globalTimeC1`;
  makes W7–W9 endpoint route UNNECESSARY for the deletion (honest finding).
- CON/CRUX: needs two-sided HasDerivAt at EVERY s — incl. **s ≤ 0 and s > T**
  where the existing adot machinery's `Ioi offset` + positivity gating fails.
  Per-mode the coeff `b_k(s)=e^{-sλ}ĉ₀+∫₀ˢe^{-(s-r)λ}ĝ(r)dr` is differentiable
  for all real s (Leibniz; bounds only needed s≥0), so it is plausibly TRUE —
  but the existing lemmas don't reach there; new global per-mode differentiation.

**Path B — refactor the field to an `On`-package, re-derive consumers.**
Change `hsrc0` to a closed-window `DuhamelSourceTimeC1On` on [0,T]; re-derive
`hagree_succ`, `hbsum_succ`, `iterate_abs_deriv2_le_of_windowDecay`,
`windowAdotLegs_step` in On-form (this is what W7–W9 was building toward).
- PRO: localizes to [0,T] where positivity + windows hold.
- CON: cascade through 4+ consumers.

## VERDICT (source-verified 2026-06-11) — Path B. Path A rejected.

Two existing lemmas pin the route decisively:
- `picardIterate_source_duhamelSourceTimeC1_of_representation`
  (IntervalPicardIterateSourceRepresentation.lean:128) ALREADY produces the
  global `DuhamelSourceTimeC1` (= hsrc0's type) — but it consumes a FULL global
  K1 quadruple: `hderiv : ∀ σ k, HasDerivAt … σ` (EVERY σ) + `hadotcont`
  (Continuous on all ℝ).
- The only K1 producer, `k1_quadruple_weak_of_subtypeCont`
  (IntervalPicardLimitK1Weak.lean:1418), delivers `hderiv` ONLY on the **open
  interior `0 < σ < T`** (l.1445), `hadotcont` only on `Set.Ioo 0 T` (l.1449),
  `hMdot` only on `[a',b']` with `b' < T` (l.1450).

So the gap between produced (interior `(0,T)`) and required-by-Path-A (all ℝ,
two-sided) is exactly **σ ≤ 0, σ = T, σ > T**. The σ=T two-sided `HasDerivAt`
needs σ>T data the interior machinery is fundamentally gated against; W9's
`logisticSource_adot_hasDerivWithinAt_endpoint` gives the σ=T **within** (one-
sided) derivative — which is the RIGHT object for a closed-window `On` package,
NOT the two-sided global one. ⇒ **Path A's global target is wrong; Path B is
correct, and W7–W9 are precisely its endpoint machinery.**

## Path B — the remaining bricks (codex grind, Fable-specified)
1. `DuhamelSourceTimeC1On`-analogue of the line-128 producer: consume the
   interior-(0,T) K1 quadruple + W9's σ=T within-endpoint adot → produce
   `DuhamelSourceTimeC1On (canonical source) 0 T`.
2. Switch the 4 tower_succ consumers to the On package (the W7–W9 `…On`/
   `…Endpoint` variants): `hagree_succ` → On, `hbsum_succ` → On,
   `iterate_abs_deriv2_le_of_windowDecay` → On, `windowAdotLegs_step` → On.
3. Change `TowerInputs.hsrc0`'s type to the On package (or DELETE it if the
   On package is now in-tower-producible from the cone K1 data); fix the
   `TowerConeAnalyticResidual.hsrc0` + the Σ' projection chain (TowerSupply ~240).
4. Clean-tree verify `from_cone_construction` #print axioms loses the residual.

(ChatGPT Pro fired in background on the same fork as an independent cross-check;
source evidence above is already decisive.)
