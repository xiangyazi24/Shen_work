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

## Consumer triage (source-verified — what each actually pulls from the pkg)
- `hagree_succ_of_sourceSubtypeCont` (IntervalPicardSourceSubtypeCont.lean:138-142):
  `.envelope` + `.henv_bound` ONLY → **no adot** → lighter `L1ContOn`/`BddOn` suffices.
- `windowAdotLegs_step` (IntervalPicardWindowAdot.lean:229): `.hderiv` → **needs adot**.
- `hbsum_succ` / `iterate_abs_deriv2_le_of_windowDecay`: go through the eigenvalue
  IBP (`duhamelSpectralCoeff_eigenvalue_summable` uses `src.adot`) → **need adot**.
⇒ 3 of 4 need adot (fed by W9's σ=T within-endpoint — confirms W9 was the right
investment); only hagree_succ can drop to the lighter package. So brick ① (full
On-producer WITH adot) is genuinely required; the payload-split is a minor win.

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

## ChatGPT Pro cross-check — CONVERGES on Path B (independent), + 2 refinements

1. **Deeper reason Path A is a real wall (stronger than the gating point):** the
   nonlinear `L(u)=u·(a−b·u^α)` differentiates through `Real.rpow`, which NEEDS a
   positivity floor (real powers aren't polynomial). Outside the positive-time
   window there's no positivity ⇒ global two-sided C¹ is a genuine ANALYTIC
   obstruction in the non-integer-α setting, not just missing lemmas. (Also: the
   global envelope `∀ s≥0` exceeds what the finite-horizon construction supplies.)
2. **Payload-splitting refinement for the On interface (do NOT over-size it):**
   - consumers needing only restart-representation / summability / envelope /
     coeff-continuity → the lighter `DuhamelSourceL1ContOn` (NO adot field);
   - only consumers that genuinely need `adot` → full `DuhamelSourceTimeC1On`.
   Mirrors the repo's existing weak-source move (`DuhamelSourceBddOn`/L1ContOn).

## On-infrastructure that already exists (for the brick-① spec)
- `DuhamelSourceTimeC1On a lo hi` (IntervalDuhamelSourceTimeC1On.lean:20):
  `hderiv = HasDerivWithinAt … (Icc lo hi)`, `hadotcont = ContinuousOn (Icc lo hi)`,
  bounds on the window — exactly W9's σ=T within-endpoint shape.
- `DuhamelSourceTimeC1.toOn` (l.33) forgets global→On; we need the REVERSE
  (build On directly from interior-(0,T) K1 + W9 endpoint, since no global exists).
- W9 endpoint adot: `logisticSource_adot_hasDerivWithinAt_endpoint[_window]`
  (IntervalPicardIterateTimeC1EndpointAdot.lean:26/119), namespace
  `ShenWork.IntervalPicardIterateTimeC1Endpoint`.

## UPDATE 2026-06-11 (run 2) — the crux re-hits s=0 at the SOURCE level

W9 (codex xhigh) built genuine clean Path B infrastructure (committed 7856c08):
`limitSource_duhamelSourceTimeC1On_of_representation` (faithful On-mirror of the
line-71 producer) + On-variants of hbsum_succ / iterate_abs_deriv2. But the CRUX —
assembling the adapter's `hderiv` input on [lo,T] — is NOT done, and it re-hits s=0:

- The adapter (correctly, like the global line-71 producer) TAKES `hderiv`/`hadotcont`/
  `hMdot` as inputs. Feeding it requires PRODUCING the window K1 quadruple.
- The σ=T endpoint piece is the committed `logisticSource_adot_hasDerivWithinAt_endpoint`
  (EndpointAdot.lean:26) — which itself REQUIRES `src : DuhamelSourceTimeC1On a 0 W`
  (source-side On-pkg INCLUDING s=0), because it calls W8e
  `restartCosineSeries_hasDerivWithinAt_time_bdd_on` (K1WeakEndpoint.lean:372), whose
  `localRestartCoeff a₀ a τ` carries the restart Duhamel integral ∫₀^τ — pulling in
  source values for s near 0.
- The STRUCTURE `DuhamelSourceTimeC1On a 0 W` has `hderiv`/`hadotcont` as FIELDS on the
  WHOLE [0,W] incl. s=0. So inhabiting it for the canonical source needs source-side
  hderiv at s=0 — exactly the wall (canonical source not C1 at physical 0 for merely-
  continuous u₀; the repo patches the s=0 VALUE for the envelope, not the derivative).

OPEN QUESTION (route decision, → ChatGPT Pro + trace): does W8e genuinely NEED
source-side `hderiv`/`adot` at s=0, or only the ENVELOPE there (patchable via the
established `patchedSource`/`DuhamelSourceBddOn` that already feeds interior k1)? If
only envelope: RE-STATE W9-endpoint + W8e with a lighter source hypothesis (envelope on
[0,W] + C1 on the positive window [a',W] only) — then patchedSource + interior-k1 close
Path B. If genuine s=0 C1 is needed: the patchedSource must be shown C1 at 0 (a const
patch on [0,ε] is), or this is a deeper wall. Trace path: W8e → `derivMajorant src a'` /
`deriv_term_abs_le src` (K1WeakEndpoint.lean ~384-400) — check if they touch src.hderiv/
src.adot at s<a' or only src.derivBound/src.envelope.

## RESOLUTION located (Fable, run 2) — the SHIFTED source closes s=0

Trace confirms W8e's IBP (`duhamelCoeff_eigenvalue_mul_on`, needs `∀ s ∈ Icc lo t`)
DOES use `src.hderiv` over [0,τ₀] incl. s=0 (K1WeakEndpoint.lean:194), and
`src.hderivBound 0` at s=0 (l.173). The bound helpers (derivMajorant/deriv_term_abs_le/
summable_*) use ONLY src.derivBound+src.envelope (patchable), but the IBP genuinely needs
the source DERIVATIVE on [0,τ₀]. The canonical/patched source is NOT C1 at physical s=0
(u₀ merely continuous → L(u₀) coeffs lack the (kπ)² decay, let alone time-C1 at 0).

THE FIX — feed W9-endpoint the SHIFTED source (the tower's existing `hsrcσ` /
`shiftedSource_timeC1` mechanism, SourceTower.lean:443): the shifted source
`fun s => canonical(σ/2 + s)` has physical time `σ/2 + s ∈ [σ/2, σ/2+W]`, BOUNDED BELOW
by σ/2 > 0 — so it IS C1 on its OWN [0,W] (no physical s=0). W9-endpoint already carries
an `offset` parameter (EndpointAdot.lean:26, `localRestartCoeff a₀ a (s-offset)`) exactly
for this. So: build `DuhamelSourceTimeC1On (shiftedSource) 0 W` (inhabitable because
physical-positive), feed W9-endpoint with offset = σ/2 → get the canonical field's σ=T
endpoint derivative. The σ=T branch in tower_succ ALREADY uses `hsrcσ` (the shifted
package); the On-version mirrors it.

⇒ Path B closes. Next brick (codex-specifiable now): build the shifted-source On-package
`DuhamelSourceTimeC1On (fun s k => cosineCoeffs(logisticLifted p (picardIter n (σ/2+s))) k) 0 W`
from the interior k1 on the SHIFTED (positive) window + the shift bookkeeping, then feed
W9's adapter. The s=0 wall was an artifact of targeting the UNSHIFTED source; the tower
never needs that (it always shifts away from 0).
