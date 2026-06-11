# K1 wall battle plan (2026-06-10 19:4x, Zinan hand-written)

## The wall, precisely
`TowerConeAnalyticResidual` is down to 7 fields, all one root:
- `hsrc0 : ∀ n, DuhamelSourceTimeC1 (fun s k => coeff(logistic(picardIter n s)))`
- `hL_cont`, `adot`, `hadot_deriv`, `hadot_cont`, `adotBound`, `hadot_bound`

`DuhamelSourceTimeC1` (IntervalDuhamelClosedC2:1502) demands GLOBAL data:
`hderiv` at every `s : ℝ`, `hadotcont` on ℝ, ℓ¹ `envelope` for ALL `s ≥ 0`
(including `s = 0` — the t→0 disease: no summable envelope at 0 for merely
continuous u₀), `derivBound` on `[0,∞)`.  As typed for the CANONICAL family
this is plausibly unsatisfiable-in-spirit; the honest content lives on
interior windows `[a',b'] ⊂ (0,T]`.

## The key identity (why the wall should fall)
Per-mode FTC on the restart representation: at level `n+1`,

    d/ds bc_{n+1}(s,k) = -λ_k·bc_{n+1}(s,k) + src_n(s,k)        (*)

— the iterate-coefficient time derivative needs only level-`n` source VALUES,
no derivatives.  Then

    ∂_s u_{n+1}(s,x) = Σ' (-λ_k bc + src_n)·cos(kπx)

(differentiate the cosine series term-by-term; domination on windows:
`Σλ|bc| < ∞` is the tower's hrepr_sum, `src_n` has the stage-F windowEnv).
Finally

    adot_{n+1}(s,k) = ∫₀¹ logistic'(u_{n+1})·∂_s u_{n+1}·cos(kπx) dx

(differentiation under the spatial integral, dominated).  Level 0 explicit:
bc_0 = e^{-sλ}û₀, all derivatives in closed form.

So the K1 data should be producible BY INDUCTION over levels — the same
induction shape the tower already runs for hrepr/hG1/hG2/srcWin.

## Attack steps
1. READ `IntervalPicardIterateTimeC1Full.lean` in full: what exactly do
   `picardIterate_K1_full_from_restart_of_representation` (line ~100) and
   `clampedIterateSource_duhamelSourceTimeC1` (line ~241) consume — same-level
   adot (upgrade lemma) or previous-level (induction step)?  Also grep the
   per-mode FTC lemma ("weak restart identity + per-mode FTC" from the
   campaign ledger — likely in IntervalPicardIterateTimeC1.lean /
   IntervalSourceCoefficientTimeC1.lean).
2. If the step lemma is same-level: build the missing inductive step from (*)
   — new file, window-local: `WindowK1 n → WindowK1 (n+1)` where
   `WindowK1 n` = adot data on every compact `[a',b'] ⊂ (0,T]` + window
   envelopes.  Reuse: hasDerivAt_tsum_of_isPreconnected (DuhamelClosedC2),
   stage-F slice decay, tower hrepr/hG1/hG2, logistic chain rule
   (logisticSourceDot machinery in TimeC1Full §D.1 — already there!).
3. Consumers audit: who eats hsrc0's GLOBAL fields?  srcWin_of_levelData,
   shift_nonneg (witness src), hiter_cont_of_tower, hbsum_succ chains.
   Each likely reads only (0,T] windows → retype consumers windowed OR patch
   via the C¹ soft clamp (IntervalTimeSoftClamp) to produce the literal
   global package from window data — clampedIterateSource_duhamelSourceTimeC1
   may BE that upgrade lemma already.
4. Surgery: TowerLevel gains a srcK1 field (window K1 data); tower_zero
   explicit; tower_succ via the new step; residual fields
   hsrc0/adot/hadot_* DELETED (hL_cont may fall too — logistic slice
   continuity from representation + Weierstrass).
5. Verify: remote single-file → full build → #print axioms both theorems
   = [propext, Classical.choice, Quot.sound]; md5; commit+push; TG report.

## Rules
No axiom, no local lake build, no fake satisfaction; remote = rsync (never
--delete) → uisai2:/dev/shm/shen_work; acceptance = #print axioms only.

## REFINED DESIGN (post-recon, 2026-06-10 ~20:00) — the induction CLOSES

Recon findings:
* `picardIterate_K1_full_from_restart_of_representation` (TimeC1Full:100) IS the
  induction step: input = level-n source GLOBAL package `src : DuhamelSourceTimeC1 a`
  + restart representation of iter(n+1) via `localRestartCoeff a₀ a` on open U +
  ball/pos/C0 facts; output = the THREE window legs at level n+1 (hderiv with
  explicit adot = coeff(logisticSourceDot…), window bound, window continuity).
* `clampedIterateSource_duhamelSourceTimeC1` (TimeC1Full:241) is the upgrade:
  window legs (bc repr + ball + G1/G2 + adot legs on [c',d']) → GLOBAL clamped
  `DuhamelSourceTimeC1 asrc` agreeing with canonical on id-zone [lo,hi].
* The tower's `SourceWin` ALREADY carries ⟨asrc, hsrc : DuhamelSourceTimeC1, …⟩
  per window — i.e. the step's `src` input is level-n's srcWin package!
* The residual enters ONLY at SourceTower:274 (H.adot/hadot_deriv/hadot_cont/
  hadot_bound fed to the clamp) and :287 ((H.hsrc0 n).hderiv used ONLY for
  global σ-continuity of the canonical coeff — window continuity from the adot
  legs suffices after a minor retype).

The closing loop:
  winAdot(n) --[clamp, already wired in sourceWin_of_level]--> srcWin(n)
  srcWin(n).hsrc --[K1-full step]--> winAdot(n+1)
  base: winAdot(0) via K1-full with the TRIVIAL ZERO source package
  (level 0 = restart with zero source; a₀ = û₀ damped coeffs).

## Brick spec: new file IntervalPicardWindowAdot.lean
Define `WindowAdot p u₀ n T : Prop` (or structure) =
  ∀ lo hi, 0 < lo → lo ≤ hi → hi < T → ∃ adot : ℝ → ℕ → ℝ,
    (∀ σ ∈ Icc lo hi, ∀ k, HasDerivAt (fun r => cosineCoeffs
       (logisticSourceFun p.a p.b p.α (lift (picardIter p u₀ n r))) k) (adot σ k) σ)
    ∧ (∃ Mdot, ∀ σ ∈ Icc lo hi, ∀ k, |adot σ k| ≤ Mdot)
    ∧ (∀ k, ContinuousOn (fun σ => adot σ k) (Icc lo hi)).
Theorems:
1. `windowAdot_zero` — K1-full with zero source package; hagree from the level-0
   restart form (check localRestartCoeff a₀ 0 = e^{-sλ}a₀; bridge to hagree_zero/
   iterateReprCoeff 0).  hdecay for zero family trivial.
2. `windowAdot_succ` — from TowerLevel n (srcWin at the padded window gives the
   step's src package; window bookkeeping: target [lo,hi], offset := lo/2,
   level-n id-zone ⊇ [offset, hi]); hagree: canonical M1 restart identity
   (picardIterateRestart_cosineIdentity / the hbsum_succ-hagree_succ machinery)
   + congruence canonical↔clamped on the read range (srcWin's agreement);
   hdecay of the clamped family: clamped values = canonical at clamped times
   ∈ id-zone ⊆ (0,T] → stage-F slice decay with window constants (pattern:
   IntervalPicardSliceWitnessSupply.shifted_source_windowDecay).
3. Surgery (after bricks): TowerLevel gains winAdot field (or tower carries it
   via a parallel induction); sourceWin_of_level consumes it instead of
   H.adot/H.hsrc0; delete residual fields hsrc0/adot/hadot_deriv/hadot_cont/
   adotBound/hadot_bound (+audit hL_cont consumers — likely falls too).
   CAUTION: hiter_cont_of_tower (TowerProjection) reads (H.hsrc0 n).hderiv —
   retype to window continuity from winAdot.  hu₀_bound/coeff machinery
   unaffected.

## FINAL BRICK (post-surgery state @786afc4, residual = {hsrc0} ONLY)

`hsrc0 : ∀ n, DuhamelSourceTimeC1 (canonical level-n source coeffs)` survives
because the from-zero restart-base coefficient reads the source on (0,τ) — no
clamp covers it (verified by the WindowAdot builder).  HONESTY FLAG: hsrc0 as
typed demands an ℓ¹ envelope UNIFORM down to s = 0 — the documented "no ℓ¹
envelope at s=0 for merely-continuous u₀" disease suggests it is unprovable or
worse as typed; the consumers must be retyped to a PATCHED package, mirroring
the limit side's solved pattern (DuhamelSourceBddOn + patchedSource +
limit_lift_eq_cosineSeries_of_subtypeCont_patched — all EXISTING machinery).

Plan:
1. Define the patched ITERATE source family (constant below a positive base
   s₀, canonical above — exact mirror of patchedSource for picardIter n).
2. Iterate from-zero representation with the patched family: mirror
   limit_lift_eq_cosineSeries_of_subtypeCont_patched's proof for the iterate
   (u_{n+1} = Φ(u_n), not the fixed point — the Duhamel integral splits at s₀;
   below s₀ the patched family is constant and the heat damping at horizon
   σ − s ≥ σ − s₀ > 0 controls the series; above s₀ canonical).
   Alternatively: BddOn-style bounded package (hM + per-window env) suffices
   for the series manipulations — check which interface the consumers
   (hbsum_succ / hagree chains / windowAdotLegs_step's K1-full src input)
   minimally need; K1-full's src : DuhamelSourceTimeC1 is the hard one — its
   FTC differentiation reads src VALUES on the window only, but its envelope
   legs are global: build the PATCHED DuhamelSourceTimeC1 (patched family IS
   globally time-C¹: constant below s₀ — C¹ across the seam needs the soft
   clamp φ on the time argument, NOT a hard cutoff — reuse IntervalTimeSoftClamp
   exactly as clampedSource_duhamelSourceTimeC1 does; the existing clamp
   producer ALREADY outputs a global package — the only gap is the from-zero
   representation consuming the CLAMPED family below the id-zone).
3. Retype: windowAdotLegs_step's hsrc0_n input → the clamped/patched package
   (level-n, produced from winAdot(n) via clampedIterateSource — ALREADY
   tower-internal!); tower_succ's hsrcσ/hbsum_succ/hagree chains → patched
   variants; TowerProjection.hiter_cont_of_tower → winAdot-derived continuity.
4. Delete hsrc0 from TowerInputs + residual → RESIDUAL EMPTY (or report the
   honest leftover).

## W4 STATUS (@7b424e2 base) — σ=T RESOLVED; hsrc0 IRREDUCIBLE; HONEST MINIMUM

FINAL PASS verdict: **`hsrc0` CANNOT be deleted.**  The residual
`TowerConeAnalyticResidual = { hsrc0 }` is the honest minimum — it is the σ=T
(closed right endpoint) slice, and that slice is genuinely consumed by the FROZEN
limit-side capstone.  No churn landed (re-routing σ<T through W3 while σ=T survives
on hsrc0 changes neither the field type nor the acceptance surface — pure cosmetic
risk).  Tree left GREEN, verified.

### The σ = T question — RESOLVED: σ=T IS genuinely consumed (Option B, not A).

Traced every consumer of the tower facts at σ=T; THREE genuine closed-T demands,
all feeding the FROZEN limit-side capstone, all irreducible:

| consumer | site | demand at σ=T | hsrc0-free route? |
|---|---|---|---|
| `IterateWindowC2Data.hbsum/hagree/hG1/hG2` | WeightedC2Bootstrap:259-272 | `a' ≤ σ ≤ T` CLOSED | NO — fed by `TowerLevel.hrepr_*/hG2` at σ=T |
| `source_coeff_window_uniform`/`henv_iter` | HresWiring:172-176 | iterate src coeff env at `s ≤ D.T` closed | NO — same TowerLevel facts |
| `hiter_cont_of_tower`→`patchedSource_coeff_continuousOn_of_iterate_data` | HresWiring:256, CoeffTimeCont:310-321 | canonical iterate src coeff TIME-continuity on `[a', D.T]` closed (when s₀=D.T it sets a'=D.T/2 and calls hiter_cont a' D.T) | NO — reads `(H.hsrc0 n).hderiv` |

`wdata_of_tower` (TowerProjection:81-98) calls `(tower_all H n).hrepr_sum/hagree σ
… hσT` with `hσT : σ ≤ T` — closed.  So `TowerLevel.hrepr_sum/hrepr_agree/hG2` at
σ=T are genuinely consumed; in `tower_succ` they are produced via `hsrc0` (`hsrcσ` =
`shiftedSource_timeC1 … (H.hsrc0 n)`; `hagree_succ_of_sourceSubtypeCont … (H.hsrc0 n)`).

Why every hsrc0-free route is STRUCTURALLY σ<T STRICT (no T-endpoint reach):
* `WindowAdotLegs` is defined on `[lo,hi]` with `hi < T` STRICT — its builders
  (`windowAdotLegs_zero/_step`) pad to `[lo/2,(hi+T)/2]` / id-zones that need room
  above; both quantify `hi < T`.
* `clampedShiftedSource_duhamelSourceTimeC1` (W3 brick) needs `σ < T` STRICT: the
  soft clamp φ requires id-zone `[σ/2,σ]` STRICTLY inside the pad `[σ/4,(σ+T)/2]`,
  i.e. `d=σ < d'=(σ+T)/2`, which fails at σ=T.  The clamp CANNOT reach σ=T.
* `hagree_succ_of_sourceBdd` (W2 brick) DOES cover σ≤T closed, BUT building its
  `DuhamelSourceBddOn (patchedSource …) T` inside `tower_succ` needs PID pointwise
  data (`0 < M`, patched-slice ball/nn at s=0) NOT in `TowerInputs` (W2 blocker C);
  and it only gives the *agree* leg, not the λ-weighted summability / G2 legs, which
  genuinely need `DuhamelSourceTimeC1` (integration-by-parts/adot), not BddOn.

T-pad escape CLOSED: `from_coneSupply`'s `HCone` is keyed to the datum horizon
`D.T`; `TowerConeAnalyticResidual.hsrc0` is at `D.T`.  The cone returns a datum at
a FIXED `D.T`; there is no mechanism to obtain tower facts at `T' > D.T`, and the
acceptance surface may only SHRINK (HCone may not gain analytic conjuncts).  So a
T-pad above the id-zone is genuinely unavailable.

### FINAL residual state — NOT EMPTY; exact type:

`TowerConeAnalyticResidual p u₀ D M A₂ = { hsrc0 : ∀ n, DuhamelSourceTimeC1
  (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) }`
(unchanged).  Cannot shrink in TYPE either: the σ=T consumers read the global
envelopes (`hbsum_succ`, `shiftedSource_timeC1`, `hagree_succ_of_sourceSubtypeCont`
all consume the full global `DuhamelSourceTimeC1`, not a T-slice fact), and
`hiter_cont_of_tower` reads `(H.hsrc0 n).hderiv s k` at every `s`.  `DuhamelSourceTimeC1`
is the minimal interface those σ=T consumers can read.

The documented honesty flag (HANDOFF "FINAL BRICK") stands: hsrc0 as typed demands an
ℓ¹ envelope UNIFORM down to s=0 — the "no ℓ¹ envelope at s=0 for merely-continuous u₀"
disease.  But note: hsrc0 is consumed ONLY at the σ=T slice now structurally; the
honest fix is the limit-side patched pattern (DuhamelSourceBddOn + patchedSource on a
TowerInputs BddOn field built at the cone site where PID lives) for the *agree* leg,
PLUS a separate σ=T λ-weighted route for hbsum/G2 (the missing T-endpoint
DuhamelSourceTimeC1 of the (T/2)-shifted source — satisfiable in spirit since times
≥ T/2 > 0, but the W3 clamp can't build it; needs a NON-clamp T-endpoint construction
or a BddOn→λ-weighted upgrade lemma).  Neither exists yet → residual survives.

### Files touched: HANDOFF/k1-wall-plan.md ONLY (this W4 STATUS).  No .lean change.

### Verification (verbatim, @7b424e2 + rsync, uisai2:/dev/shm/shen_work):
* root `lake build ShenWork` → `Build completed successfully (8547 jobs).` EXIT 0.
* explicit module targets, all `Build completed successfully`:
  - ShenWork.Paper2.IntervalPicardTowerSupply (3677 jobs)
  - ShenWork.Paper2.IntervalDomainThm11ChiZeroCoreProvider (3657 jobs)
  - ShenWork.Paper2.IntervalPicardTowerProjection (3632 jobs)
  - ShenWork.Paper2.IntervalPicardWindowAdot (3605 jobs)
  - ShenWork.Paper2.IntervalPicardSourceTower (3615 jobs)
* axiom probe BOTH acceptance theorems = `[propext, Classical.choice, Quot.sound]`:
  - ShenWork.Paper2.Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_unconditional
  - ShenWork.IntervalPicardTowerSupply.paper2_theorem_1_1_chiZero_from_coneSupply
* W2/W3 bricks still axiom-clean: hrepr_sum_succ_of_winAdot, hG2_succ_engine_of_winAdot,
  hagree_succ_of_sourceBdd all = [propext, Classical.choice, Quot.sound].

### Honest leftover (the genuine next attack, NOT this session's scope):
Empty the residual requires producing the σ=T slice hsrc0-FREE.  Two pieces:
(i) the *agree* leg via a TowerInputs `bddOn : ∀ n τ, 0<τ→τ≤T→ DuhamelSourceBddOn
    (patchedSource …) τ` field built at `towerInputs_of_cone` (PID lives there) +
    `hagree_succ_of_sourceBdd` — closed-T OK;
(ii) the λ-weighted hbsum/G2 legs + `hiter_cont` at closed T — needs a T-endpoint
    `DuhamelSourceTimeC1` of the (T/2)-shifted source built WITHOUT the soft clamp
    (the clamp structurally can't reach the endpoint), e.g. a one-sided/left-limit
    construction at s=T, or a BddOn→λ-weighted upgrade.  This is the genuine wall;
    until it exists the field is honest and irreducible.

## W3 STATUS (@8df3583 base) — BRICK + CONSUMER VARIANTS + TOWER LEGS LANDED

Three NEW files, tree GREEN on uisai2:/dev/shm/shen_work, all five head theorems
axiom-clean `[propext, Classical.choice, Quot.sound]` (no sorryAx):

1. `IntervalPicardShiftedClampedSupply.clampedShiftedSource_duhamelSourceTimeC1` —
   THE BRICK.  GLOBAL clamped `DuhamelSourceTimeC1 asrc` of the σ/2-shifted level-`n`
   source from `winAdot` data only (NO hsrc0), AGREEING with the canonical shifted
   family `s ↦ coeff(logistic(iter n (σ/2+s)))` on the read window `[0, σ/2]`.
   Instantiates the existing generic producer `clampedSource_duhamelSourceTimeC1`
   with `τ := σ/2`, id-zone `[c,d] := [σ/2, σ]`, pad `[σ/4, (σ+T)/2] ⊂ (0,T)`.
   Window data fed via the `G1win`/`G2win` pattern (mirror `windowAdotLegs_step`);
   `winAdot` legs choice-extracted.  HONEST: needs `σ < T` STRICT (pad room above
   id-zone exists only when `σ < T`); `σ = T` is the (D)-class terminal residual.

2. `IntervalPicardSuccLegsOfWinAdot` — the two CONSUMER VARIANTS:
   * `hbsum_succ_of_window` — variant of `hbsum_succ` (site A).  Reads the clamped
     package `srcC` for `asrc` + the `[0,σ/2]` agreement; transports
     `restartSeries_eigenvalue_summable`'s clamped summability to the canonical
     `iterateReprCoeff (n+1)` via `restartDuhamelCoeff_clamped_eq`
     (`duhamelSpectralCoeff_congr_on_Icc` on `[0,σ/2]`; `restartDuhamelCoeff` ≡
     `localRestartCoeff` definitionally).
   * `iterate_abs_deriv2_le_of_window` — variant of the G2 engine
     `iterate_abs_deriv2_le_of_windowDecay` (site B).  Same `[0,σ/2]` bridge: the
     clamped restart series coincides coefficient-wise with the canonical
     `restartIterateCoeff` series, so their deriv² bounds agree.

3. `IntervalPicardSuccTowerLegs` — DELIVERABLE 2, the assembled `tower_succ`
   replacements (`SuccLegData` bundle = TowerLevel n / TowerInputs facts MINUS hsrc0
   + winAdot legs):
   * `hrepr_sum_succ_of_winAdot` : ∀σ, 0<σ → σ<T → Summable(λ-weighted
     iterateReprCoeff (n+1) σ).  EXACT shape of tower_succ's `hrepr_sum` site.
   * `hG2_succ_engine_of_winAdot` : ∀σ, 0<σ → σ<T → ∀x, the deriv² restart-series
     bound `≤ 2M·eigExpWeight(σ/2) + duhamelGainConst·(σ/2)^{1/4}·Benv` — the EXACT
     `hbound` (with M₁=2M) the G2 interior branch consumes (`duhamelGainConst` =
     `2·(∑'…)/π^{3/2}` by `rfl`, matching the explicit constant).

W4 WIRING (pure pass, scoped): in `tower_succ`, replace
  * `hsrcσ`/`hbsum_succ` → `hrepr_sum_succ_of_winAdot` for `σ < T`;
  * G2 interior `hbound`/`iterate_abs_deriv2_le_of_windowDecay` →
    `hG2_succ_engine_of_winAdot` (after `rw [hgain_eq]`) for `σ < T`.
  Both legs need the `SuccLegData` bundle (L.hrepr_*/H.hpos/H.hub/L.hG1/L.hG2 +
  L.winAdot) — all already in tower_succ's scope.  The `σ = T` slice still needs a
  route (terminal (D) leftover): either carry `σ=T` through the surviving canonical
  `hsrc0` path, or supply level-`n` facts on a horizon `Tpad > T` so the pad fits.

## W2 STATUS (partial, post-recon) — RESIDUAL NOT EMPTIED; honest minimum reported

What landed (tree GREEN, root build 8547 jobs EXIT 0, axiom probe clean
[propext, Classical.choice, Quot.sound] on BOTH acceptance theorems):

1. `IntervalPicardSourceTower.sourceWin_of_level:~301` — the σ-continuity of the
   canonical source coefficient on `[lo,hi]` is now WALL-FREE: derived from the
   `winAdot` legs already in scope (`hlegs.choose_spec.1` → `HasDerivAt` →
   `ContinuousAt` on `[lo,hi] ⊆ [c',d']`, bridged `logisticSourceFun∘lift` →
   `logisticLifted` via `cosineCoeffs_congr_on_Icc`).  This deletes ONE of the four
   `hsrc0` consumptions inside SourceTower (was the only one in `sourceWin_of_level`).

2. NEW file `IntervalPicardShiftedBddSupply.lean` —
   `hagree_succ_of_sourceBdd`: the BddOn mirror of
   `IntervalPicardSourceSubtypeCont.hagree_succ_of_sourceSubtypeCont`.  Produces the
   `(n+1)` representation agreement `EqOn (lift(iter(n+1) σ)) (∑' iterateReprCoeff (n+1)
   σ · cos)` from `DuhamelSourceBddOn (patchedSource …) T` + `hLs_cont` + `σ ≤ T`,
   via the half-step (`τ=σ/2`, `s=σ`) specialisation of
   `picardIterateRestart_general_of_sourceBdd`.  Coefficient bridge is definitional
   (`iterateReprCoeff (n+1) ≡ restartIterateCoeff ≡ restartDuhamelCoeff ≡
   localRestartCoeff`, `σ−σ/2 = σ/2`).  STANDALONE, compiles, axiom-clean — NOT yet
   wired into `tower_succ` (see blocker below).

HONEST MINIMUM — residual `hsrc0` could NOT be deleted this session.  The four
surviving `hsrc0` consumptions and why each resists, AFTER recon:

  (A) `tower_succ` `hsrcσ` → `hbsum_succ` (λ-WEIGHTED summability of
      `iterateReprCoeff (n+1)`).  `hbsum_succ` → `restartSeries_eigenvalue_summable`
      → `duh_eig_summable` → `IntervalDuhamelClosedC2.duhamelSpectralCoeff_eigenvalue_summable`,
      which uses `src.adot` + `src.hderiv` (INTEGRATION-BY-PARTS / `duhamelCoeff_
      eigenvalue_mul`) — the λ-weight genuinely needs the time-DERIVATIVE structure of
      a `DuhamelSourceTimeC1`, NOT the BddOn envelopes.  `summable_abs_duhamelSpectralCoeff_bdd`
      only gives `|·|`-summability, not `λ·|·|`.  BLOCKER: needs a global
      `DuhamelSourceTimeC1` of the σ/2-SHIFTED canonical source.  The shift keeps
      times `≥ σ/2 > 0` (no t→0 disease, so satisfiable in principle), but building it
      requires a CLAMPED-SHIFTED `DuhamelSourceTimeC1` construction from `winAdot` data
      (mirror of `clampedIterateSource_duhamelSourceTimeC1` in the shifted frame).
      That is the missing major brick — a NEW file.

  (B) `tower_succ` G2 line → `iterate_abs_deriv2_le_of_windowDecay` → `restartSeries_
      abs_deriv2_le_on` → `restartDuhamelCoeff_eigenvalue_summable hτ ha₀ src` +
      `duh_eig_summable src` — SAME blocker as (A): full `DuhamelSourceTimeC1` of the
      shifted source (λ-weighted route).  Same clamped-shifted brick unblocks it.

  (C) `tower_succ` `hagree_succ` (`:451`).  HAS a working BddOn mirror now
      (`hagree_succ_of_sourceBdd`, deliverable 2).  But to USE it in `tower_succ` we
      must BUILD the level-n `DuhamelSourceBddOn` package there via
      `iterateBddOn_of_facts`, which needs POINTWISE datum facts NOT in `TowerInputs`:
      `hMpos : 0 < M` (only `hMnn : 0 ≤ M` present) and the patched-slice ball/nn
      `hpball/hpnn : ∀ s ∈ Icc 0 T, ∀ y, |patchedSlice u₀ (iter n) s y| ≤ M ∧ 0 ≤ …`
      (the `s=0` branch needs `|u₀ y| ≤ M`, `0 ≤ u₀ y` — `PositiveInitialDatum`
      pointwise data, available ONLY at the cone site `towerInputs_of_cone`, not in
      `TowerInputs`).  CLEAN NEXT STEP: add a per-level BddOn field to `TowerInputs`
      (shape `∀ n τ, 0<τ → τ<T → DuhamelSourceBddOn (patchedSource …) τ`), built at the
      cone site where `PositiveInitialDatum` lives, replacing `hsrc0` for (C) +
      `windowAdotLegs_step`.  This is the architecturally-correct field swap.

  (D) `TowerProjection.hiter_cont_of_tower` — canonical coeff continuity on the
      CLOSED window `[a', τ]` with τ that can equal `T` (the top call in
      `IntervalDomainHresWiring.duhamelSourceBddOn_of_core:256` passes `τ = D.T`,
      `le_rfl`).  `winAdot` legs are STRICT interior (`hi < T`) and the BddOn package
      `hcont` is on `[0,τ]`, `τ < T` STRICT — NEITHER reaches the closed right
      endpoint `T`.  Continuity AT `s = T` from the left would need a "terminal
      approach" (mirror of the `s=0` initial approach) which the cone does not return
      (`HasContinuousSlices` is SPATIAL only, no joint/temporal slice continuity).
      This is the genuinely hardest leftover; it is the limit-side feed consumed by
      the FROZEN capstone.

NEXT-SESSION PLAN (to actually empty the residual):
  * Brick X: `clampedShiftedSource_duhamelSourceTimeC1` (NEW file) — global clamped
    `DuhamelSourceTimeC1` of the σ/2-shifted level-n source from `winAdot` legs (mirror
    `clampedIterateSource_duhamelSourceTimeC1` in the shifted frame).  Unblocks (A)+(B).
  * Field swap: `TowerInputs.hsrc0` → `bddOn : ∀ n τ, 0<τ → τ<T → DuhamelSourceBddOn
    (patchedSource …) τ`, built at `towerInputs_of_cone` via `iterateBddOn_of_facts`
    (PID pointwise data available there).  Wire `hagree_succ_of_sourceBdd` (deliverable
    2) + `windowAdotLegs_step`'s `picardIterateRestart_general` → `_of_sourceBdd`.
    Unblocks (C).
  * (D): produce a left-continuity-at-`T` leg for the canonical coeff, or retype
    `hiter_cont_of_tower` to τ<T and verify HresWiring tolerates τ<T (it currently
    forces τ=D.T).  This is the honest hard residual; may stay as a shrunken
    `TowerInputs` hypothesis if the terminal approach can't be produced.

## W1 STATUS (@085a3ad)
- W1a DONE (hand-written, IntervalPicardIterateInitialApproach.lean):
  `picardIter_initialApproach` — ∀ n, iterate → u₀ sup-norm as s → 0⁺
  (χ₀ = 0; G5 homogeneous block + Duhamel ≤ t·C_L; level 0 homogeneous only).
- W1b TODO: `patchedIterateSource_coeff_continuousOn` (s=0 via W1a +
  logisticLifted_slice_dist_le + cosineCoeffs_dist_le_of_sup, mirror
  IntervalPicardLimitCoeffTimeCont.patchedSource_continuousWithinAt_zero;
  interior via winAdot legs + patchedSource_eq_of_pos congruence; mind the
  right-endpoint τ < T vs ≤ T per duhamelSourceBddOn_of_slices's horizon
  genericity) + `iterateBddOn_of_tower` (feed duhamelSourceBddOn_of_slices,
  IntervalPicardIterateBddProducer.lean).
- W2 TODO: wire the BddOn package + the _of_sourceBdd chain
  (IntervalPicardIterateBddRepr.lean) into windowAdotLegs_step + the two
  tower_succ sites (hsrcσ / hagree_succ — each needs its own BddOn
  re-derivation of the half-step machinery), retype
  sourceWin_of_level:287 + hiter_cont_of_tower to winAdot-derived continuity,
  delete hsrc0 from TowerInputs + TowerConeAnalyticResidual (→ residual EMPTY),
  fix the HCone Σ' projections, full verify (explicit module targets +
  axiom probe), update docs.

## W5 DESIGN DECISION (@7866720, Zinan 拍板)
Route A ACCEPTED (one-sided/windowed-C¹ endpoint interface; eliminates the
σ=T demand without touching the frozen capstone).  Route B REJECTED (relocates
the closed endpoint into the at-horizon limit-side construction, B1/B2/B3).
Full recon in the W5 agent report (ground truths: G1 final theorem open at
Tmax; G2 W3 bricks are dead code — σ<T wiring undone; G3 Mathlib lacks
hasDerivWithinAt_tsum).

Wave plan:
- W6a (SourceTower): wire the dead W3 bricks into tower_succ with an honest
  σ<T / σ=T case split — hsrc0 consumption shrinks to the literal σ=T branch.
- W6b (TowerSupply): HCone narrowing to the constructed datum (HConeNarrow,
  ~6 signatures, ~250 lines) — makes from_coneSupply instantiable; the ∀-D
  form is gate-unsatisfiable at large horizons.  Independent of σ=T.
- W7: hasDerivWithinAt_tsum port (~250 lines, the bounded Mathlib gap;
  substrate hasDerivWithinAt_of_tendstoUniformlyOn).  STOP-AND-REPORT if it
  balloons; do NOT switch to Route B mid-flight.
- W8: DuhamelSourceTimeC1On interface + one-sided IBP
  (duhamelCoeff_eigenvalue_mul via integral_eq_sub_of_hasDeriv_right_of_le)
  + endpoint winAdot builder (IntervalPicardWindowAdotEndpoint.lean).
- W9: final wiring + hsrc0 deletion + HConeNarrow bridge to the cone
  existence theorem → from_coneSupply actually instantiable → the χ₀=0
  Theorem 1.1 unconditional (interval domain).  χ₀<0 branch remains future.

## W6a STATUS (@421582b base) — DEAD W3 BRICKS WIRED; hsrc0 σ=T-ONLY at SITES A+B

The σ<T / σ=T case split is LIVE in `tower_succ` (IntervalPicardSourceTower).
A level-`n` `SuccLegData` bundle `D` is built once (from `H.hα/ha/hb/hMnn/hA₂nn`,
`L.hrepr_sum/hrepr_agree/hG1/hG2/winAdot`, `H.hpos n`/`H.hub n` — all in scope, NO
hsrc0), feeding the W3 legs on the σ<T branch.  Split tactic: `rcases lt_or_ge σ T`.

| site | location | σ < T branch (hsrc0-FREE) | σ = T branch | hsrc0 now? |
|---|---|---|---|---|
| A `hrepr_sum` | SourceTower ~:460 | `hrepr_sum_succ_of_winAdot p u₀ n D hM₁ σ hσ hσlt` | `hbsum_succ … (hsrcσ σ hσ)` | σ=T ONLY |
| B G2 interior | SourceTower ~:537 (inside `hser`, post-`hgain_eq`) | `hG2_succ_engine_of_winAdot p u₀ n D hM₁ σ hσ hσlt x` | `iterate_abs_deriv2_le_of_windowDecay … (hsrcσ σ hσ) (hdecayW …) x` | σ=T ONLY |
| C `hrepr_agree` | SourceTower ~:475 | (NOT split) `hagree_succ_of_sourceSubtypeCont … (H.hsrc0 n) hLs` | (same) | ALL σ — documented |

W3 brick wiring detail (site B): the W3 `hG2_succ_engine_of_winAdot` produces the
bound in the EXPLICIT-constant form (`2·(∑'…)/π^{3/2}`), i.e. exactly the post-
`rw [hgain_eq]` shape of `hser`, so the split lives inside `hser`'s proof (after the
`hgain_eq` rewrite); the surrounding `hEq` (Ioo agreement) + `lift_deriv2_abs_le_of_
eqOn_Ioo` transport are shared (factored out of the branch).

### Site C (hagree) — left on hsrc0, HONEST REASON (no new TowerInputs fields):
The BddOn mirror `hagree_succ_of_sourceBdd` (IntervalPicardShiftedBddSupply) needs a
`DuhamelSourceBddOn (patchedSource …) T` package.  Building it in-tower via
`iterateBddOn_of_facts` (IntervalPicardIterateBddPackage:320) requires hypotheses NOT
derivable from `TowerInputs`:
  * `hMpos : 0 < M` — TowerInputs has only `hMnn : 0 ≤ M`;
  * `hpball/hpnn : ∀ s ∈ Icc 0 T, ∀ y, |patchedSlice u₀ (iter n) s y| ≤ M ∧ 0 ≤ …` —
    `patchedSlice` at `s ≤ 0` IS `u₀` (verified, IntervalPicardLimitBddHcontP:217), so
    these demand a POINTWISE u₀ sup-ball `|u₀ y| ≤ M` / `0 ≤ u₀ y`.  TowerInputs carries
    only the COEFFICIENT bound `hu₀_bound : |cosineCoeffs (lift u₀) k| ≤ M`, NOT a sup-
    ball.  The PID pointwise data lives at the cone site (`towerInputs_of_cone`), not in
    TowerInputs.
  * `iterateBddOn_of_facts` also needs `τ < T` STRICT — structurally cannot reach σ=T.
Per the W6a brief (DO NOT add TowerInputs fields), hagree stays on hsrc0.  The field
swap (add a per-level `bddOn` field at the cone site) is the W2-STATUS-(C) leftover,
deferred to a later wave.

### Other surviving hsrc0 consumer (out of W4-table scope, unchanged):
`wA1 = windowAdotLegs_step … (H.hsrc0 n) …` (SourceTower ~:556) — the K1 induction
step itself consumes the canonical level-`n` package at all σ.  This is the inductive
producer of `winAdot (n+1)`, not one of the three W4-table consumer sites; it stays on
hsrc0 until the W8/W9 endpoint-winAdot construction lands.

### Verification (verbatim, @421582b + edits, uisai2:/dev/shm/shen_work, rsync no --delete):
* per-file `lake env lean ShenWork/Paper2/IntervalPicardSourceTower.lean` → EXIT 0.
* explicit module targets `lake build ShenWork.Paper2.IntervalPicardSourceTower
  ShenWork.Paper2.IntervalPicardTowerSupply
  ShenWork.Paper2.IntervalDomainThm11ChiZeroCoreProvider` →
  `Build completed successfully (3680 jobs).` EXIT 0
  (`Built ShenWork.Paper2.IntervalPicardSourceTower (5.2s)`).
* root `lake build ShenWork` → `Build completed successfully (8547 jobs).` EXIT 0.
* axiom probe BOTH acceptance theorems = `[propext, Classical.choice, Quot.sound]`:
  - ShenWork.Paper2.Thm11ChiZeroCoreProvider.paper2_theorem_1_1_chiZero_unconditional
  - ShenWork.IntervalPicardTowerSupply.paper2_theorem_1_1_chiZero_from_coneSupply
  UNCHANGED from W4.  No sorryAx, no custom axioms.

### Files touched: ShenWork/Paper2/IntervalPicardSourceTower.lean (import + 2 opens +
`SuccLegData` bundle `D` + site-A split + site-B split inside `hser`);
HANDOFF/k1-wall-plan.md (this section).  TowerInputs signature UNCHANGED (case split is
internal to tower_succ's proof body).  No edit to IntervalPicardTowerSupply.lean.

## W6b STATUS (@421582b base) — HCone NARROWING LANDED; supply now INSTANTIABLE

RESOLUTION PATH TAKEN: (i) — additive NEW capstone theorem alongside the existing ones.
Existing `paper2_theorem_1_1_chiZero_unconditional`, `paper2_theorem_1_1_chiZero_from_
coneSupply` UNCHANGED.  Confirmed by reading the capstone consumers
`quantitativeLocalExistence_chiZero_wdata` (CoreProvider:797-831) and
`hMildLocal_chi0_zero_of_wdata` (:838-862): BOTH obtain the datum from
`coneGradientMildSolutionData_exists_with_data` and call `Hiter`/`HWdata` at THAT `D`
only (lines 827/861).  The providers are `∀ D` at the TYPE level → path (ii) (wrapper
trick) impossible (confirmed).  Hence (i): new capstone consuming a per-constructed-datum
(datum-OWNING) supply.

### New signatures (verbatim):

CoreProvider §W6b (additive, ZERO change to existing decls):
```
def DatumIterLegs (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) : Type :=
  (WdataProvider p u₀ D) ×'
    (∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ), ContinuousOn
      (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) (Set.Icc a' τ))

def DatumProviderSupply (p : CM2Params) : Type :=
  ∀ M_in : ℝ, 0 < M_in → Σ' δ : ℝ, (0 < δ) ×'
    ∀ u₀, PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M_in) →
      Σ' D : GradientMildSolutionData p u₀,
        (D.T = δ) ×' (D.u = picardLimit p u₀ δ) ×'
        (∀ n, HasContinuousSlices D.T (picardIter p u₀ n)) ×'
        (∃ F : PicardConvFacts p u₀, F.T = δ) ×' DatumIterLegs p u₀ D

theorem paper2_theorem_1_1_chiZero_of_datumProviders
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) (Hsupply : DatumProviderSupply p) :
    Theorem_1_1 intervalDomain p
```
(plus helpers `quantitativeLocalExistence_chiZero_datum`, `hMildLocal_chi0_zero_of_datum`
— mirrors of the `_wdata` theorems sourcing the datum+legs from `Hsupply`.)

TowerSupply §5 (additive):
```
structure ResidualAtDatum (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  hT1 : D.T ≤ 1
  hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ D.M
  hball : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T → ∀ y, |picardIter p u₀ n σ y| ≤ D.M
  hAnalytic : TowerConeAnalyticResidual p u₀ D D.M 0

-- THE PRIZE (paper theorem modulo a per-CONSTRUCTED-DATUM residual):
theorem from_cone_construction
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (Hres : ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
      ∀ D : GradientMildSolutionData p u₀,
        D.u = picardLimit p u₀ D.T → ResidualAtDatum p u₀ D) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p

theorem paper2_theorem_1_1_chiZero_from_coneSupplyNarrow
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) (Hsupply : DatumProviderSupply p) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p
```
(plus `datumIterLegs_of_cone` — builds `DatumIterLegs` from a gate-data cone datum +
`ResidualAtDatum`, via `towerInputs_of_cone` at mass `D.M` (`hlim_ball := D.hbound`) +
`wdataProvider_of_tower` + `hiter_cont_of_tower`.)

`from_cone_construction` discharges `DatumProviderSupply` from
`coneGradientMildSolutionData_exists_with_gate_data` (via `Classical.choice` on its Prop
existentials).  The `∀ D` `from_coneSupply` is gate-UNSATISFIABLE at large horizons; the
datum-OWNING supply owes the residual only at the SMALL cone horizon δ → instantiable.

### WHAT REMAINS (HONEST — NOT only hsrc0):
From the gate-data cone, `from_cone_construction` discharges: gate, slice continuity,
strict positivity, LIMIT ball (`D.hbound`), datum continuity, A₂≥0, δ>0.  `ResidualAtDatum`
carries FOUR per-datum legs:
1. `hAnalytic` = `TowerConeAnalyticResidual` (genuine `hsrc0`) — the W4 irreducible.
2. `hT1 : D.T ≤ 1` — cone-internal (`T₀ ≤ ½`) but the `_with_gate_data` return type does
   NOT expose `δ ≤ 1`.
3. `hu₀_bound : |cosineCoeffs (lift u₀) k| ≤ D.M` — true (`D.M ≥ M_in ≥` datum bound) but
   the mass relation is not type-recoverable.
4. `hball : iterate ball ≤ D.M` — cone-RETURNED via `∃ F:PicardConvFacts, F.T=δ`
   (`F.hball` at `F.M`), but the cone HIDES `F.M = D.M` so it is not extractable at the
   gate mass `D.M`.
ROOT CAUSE of legs 2-4: `IntervalMildPicardConeData.lean` is un-editable this mission and
its `_with_gate_data` return type HIDES its internal mass (`D.M = F.M = M` definitionally
but exposes neither `F.M` nor `δ ≤ 1`).  All four bundled honestly; only leg 1 is open.
To shrink to ONLY `hsrc0`: a one-line additive strengthening of the cone return type
(expose `F.M = D.M` and `δ ≤ 1`) — owned by a future wave — then legs 2-4 fall.

### Verification (verbatim, @421582b + W6b edits, uisai2:/dev/shm/shen_work, rsync no --delete):
* per-file `lake env lean` EXIT 0: CoreProvider, TowerSupply.
* module builds EXIT 0: `ShenWork.Paper2.IntervalDomainThm11ChiZeroCoreProvider`
  (3657 jobs), `ShenWork.Paper2.IntervalPicardTowerSupply` (3680 jobs).
* root `lake build ShenWork` → `Build completed successfully (8547 jobs).` EXIT 0.
* axiom probe — ALL five = `[propext, Classical.choice, Quot.sound]` (no sorryAx):
  - FROZEN UNCHANGED: `paper2_theorem_1_1_chiZero_unconditional`,
    `paper2_theorem_1_1_chiZero_from_coneSupply`.
  - NEW: `paper2_theorem_1_1_chiZero_of_datumProviders`, `from_cone_construction`,
    `paper2_theorem_1_1_chiZero_from_coneSupplyNarrow`.
* diffs purely additive: 260 insertions / 0 deletions across the two files;
  `git diff --check` clean.

### Files touched (W6b): ShenWork/Paper2/IntervalDomainThm11ChiZeroCoreProvider.lean
(additive §W6b), ShenWork/Paper2/IntervalPicardTowerSupply.lean (additive §5),
HANDOFF/k1-wall-plan.md (this section).  No edit to IntervalPicardSourceTower.lean.

### Honest leftovers: hsrc0 still consumed at (i) site C hagree — all σ (needs cone-site
BddOn field, no new TowerInputs field permitted this wave); (ii) `windowAdotLegs_step`
— all σ (the K1 inductive producer, W8/W9 scope).  Sites A and B are now σ=T-only, as
required.  The σ=T endpoint itself is the genuine wall (W5 Route A: one-sided/windowed-
C¹ endpoint interface, W7–W9).

## W6c STATUS (@34d1a04 base) — RESIDUAL SHRUNK TO ONLY hsrc0; legs 2-4 EXPOSED

The W6b `ResidualAtDatum` bundled the genuine analytic surface `hAnalytic` (= hsrc0)
together with THREE cone-internal bookkeeping legs (`hT1 : D.T ≤ 1`, `hu₀_bound`, `hball`)
that were TRUE of the cone construction but TYPE-HIDDEN by the original
`coneGradientMildSolutionData_exists_with_gate_data` return.  W6c exposes all three at the
gate mass `D.M` via an ADDITIVE strengthening of the cone return, so the per-datum residual
hypothesis of `from_cone_construction'` shrinks to ONLY the analytic field.  RESOLUTION:
copy (wrap impossible — the three facts are construction-internal, not type-recoverable
from `_with_gate_data`'s return; confirmed) the cone proof body verbatim and add the three
conjuncts at the final record (`hT₀_le_one`; `hMc`+`cosineCoeffs_congr_on_Icc hf₀_eq`+
`2·M_in ≤ M`; `hball`).  ALL existing decls byte-for-byte unchanged; new decls only.

### New signatures (verbatim):

ConeData (additive, ZERO change to existing decls):
```
theorem coneGradientMildSolutionData_exists_with_gate_data' (p : CM2Params)
    (hχ : p.χ₀ = 0) {M_in : ℝ} (hM_in : 0 < M_in) (hα_ge : 1 ≤ p.α) :
    ∃ δ A₂ : ℝ, 0 < δ ∧ 0 ≤ A₂ ∧
      ∀ u₀ : intervalDomainPoint → ℝ,
        Continuous u₀ → (∀ x, |u₀ x| ≤ M_in) → (∀ x, 0 ≤ u₀ x) → (∃ x₀, 0 < u₀ x₀) →
        ∃ D : GradientMildSolutionData p u₀,
          D.T = δ ∧ D.u = picardLimit p u₀ δ ∧
          ShenWork.IntervalPicardIterateUniform.GateCondition p D.M A₂ D.T ∧
          (∀ n, HasContinuousSlices D.T (picardIter p u₀ n)) ∧
          (∃ F : ShenWork.IntervalPicardLimitCoeffConv.PicardConvFacts p u₀, F.T = δ) ∧
          (∀ n σ, 0 < σ → σ ≤ δ → ∀ x ∈ Set.Icc (0 : ℝ) 1,
            0 < intervalDomainLift (picardIter p u₀ n σ) x) ∧
          D.T ≤ 1 ∧
          (∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ D.M) ∧
          (∀ n σ, 0 < σ → σ ≤ D.T → ∀ y : intervalDomainPoint,
            |picardIter p u₀ n σ y| ≤ D.M)
```
(the last three conjuncts are the W6c additions; first six byte-identical to
`_with_gate_data`.)

TowerSupply §6 (additive):
```
structure ResidualAtDatumCore (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  hAnalytic : TowerConeAnalyticResidual p u₀ D D.M 0

theorem from_cone_construction'
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (Hres : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T → ResidualAtDatumCore p u₀ D) :
    ShenWork.Paper2.Theorem_1_1 intervalDomain p
```

### FINAL residual hypothesis of `from_cone_construction'` — EXACTLY hsrc0:
`Hres … → ResidualAtDatumCore p u₀ D`, a single-field structure whose only field is
`hAnalytic : TowerConeAnalyticResidual p u₀ D D.M 0` — i.e. the genuine `hsrc0` analytic
surface (W4 STATUS irreducible), NOTHING else.  Legs `hT1`/`hu₀_bound`/`hball` are now
CONE-RETURNED by `_with_gate_data'` at the gate mass `D.M` and consumed internally; the
caller no longer owes them.  Honest accounting: hsrc0 itself remains the genuine open wall
(W7–W9, σ=T endpoint), unchanged by this wave — W6c only removed the THREE type-hidden
bookkeeping legs, exactly as the mission specified.

### Files touched (W6c): ShenWork/Paper2/IntervalMildPicardConeData.lean (additive
`_with_gate_data'`, +793 lines, copy of `_with_gate_data` body + 3 conjuncts);
ShenWork/Paper2/IntervalPicardTowerSupply.lean (additive `ResidualAtDatumCore` +
`from_cone_construction'`, +83 lines); HANDOFF/k1-wall-plan.md (this section).  Diffs
PURELY additive: 876 insertions / 0 deletions; `git diff --check` clean.  No edit to
IntervalMildPicardConeData's existing theorems, no edit to TowerSupply's frozen/W6b decls.

### Verification (verbatim, @34d1a04 + W6c edits, uisai2:/dev/shm/shen_work, rsync no --delete):
* per-file `lake env lean` EXIT 0: IntervalMildPicardConeData (only pre-existing linter
  warnings), IntervalPicardTowerSupply.
* module builds EXIT 0:
  - `lake build ShenWork.Paper2.IntervalMildPicardConeData` → `Build completed
    successfully (3593 jobs).`
  - `lake build ShenWork.Paper2.IntervalMildPicardConeData
    ShenWork.Paper2.IntervalPicardTowerSupply
    ShenWork.Paper2.IntervalDomainThm11ChiZeroCoreProvider` → `Build completed
    successfully (3680 jobs).`
* root `lake build ShenWork` → `Build completed successfully (8547 jobs).` EXIT 0.
* axiom probe — ALL SEVEN = `[propext, Classical.choice, Quot.sound]` (no sorryAx):
  - FROZEN UNCHANGED: `paper2_theorem_1_1_chiZero_unconditional`,
    `paper2_theorem_1_1_chiZero_from_coneSupply`.
  - W6b UNCHANGED: `from_cone_construction`,
    `paper2_theorem_1_1_chiZero_from_coneSupplyNarrow`,
    `paper2_theorem_1_1_chiZero_of_datumProviders`.
  - W6c NEW: `from_cone_construction'`,
    `coneGradientMildSolutionData_exists_with_gate_data'`.

## W6b ADDENDUM — STATEMENT-FIDELITY AUDIT (playbook pass, post-hoc)

Run AFTER the W6b report, on review demand.  Verdict: every "unconditional"/"prize"
claim in this campaign MUST carry the slice qualifier.  Ledger (Lean `Theorem_1_1`
Prop, Statements.lean:4342, vs what the chiZero chain proves):

| dimension | paper / `Theorem_1_1` Prop | what we actually prove |
|---|---|---|
| sensitivity | premise `p.χ₀ ≤ 0` (the paper's case is NEGATIVE sensitivity) | ONLY `p.χ₀ = 0` — the DEGENERATE slice: the chemotaxis coupling χ₀∇·(u∇v) VANISHES from the u-equation (decoupled heat+logistic).  χ₀ < 0 — the paper's actual content — is untouched by the whole tower/cone campaign. |
| reaction | both branches: `a,b>0` AND `a=b=0` | only `0 < a, 0 < b` hypotheses; for our parameters the `a=b=0` branch is VACUOUSLY true; the paper's claim AT `a=b=0` parameters is not covered. |
| α, γ | `CM2Params` standing assumptions: `0 < α`, `0 < γ` only | EXTRA hypotheses `1 ≤ α`, `1 ≤ γ` — regime narrowing beyond the paper. |
| domain | any `BoundedDomainData` (paper: smooth bounded Ω ⊂ ℝ^N) | `intervalDomain` only (1-D). |
| conditionality | — | conditional on the residual (`Hiter`+`HWdata`, or W6b's `DatumProviderSupply`/`ResidualAtDatum`). |

VACUITY RISK FLAG (playbook "vacuous conditional theorem" class): `hsrc0`
(`TowerConeAnalyticResidual`) carries the DOCUMENTED satisfiability question (W4/FINAL
BRICK: ℓ¹ envelope uniform down to s=0 — "no ℓ¹ envelope at s=0 for merely-continuous
u₀" disease; plausibly unsatisfiable AS TYPED).  If unsatisfiable, every theorem
conditioned on it — including `from_cone_construction` and the existing
`from_coneSupply`/`_unconditional` — is operationally vacuous despite clean axioms.
`#print axioms` cannot detect this.  Resolving hsrc0's satisfiability (or retyping per
the W4 honest-fix sketch) is a PREREQUISITE for any headline claim, not an optional
polish.

Also: the repo contains NO paper source (no PDF/tex), so the audit above aligns the
proofs against the Lean `Theorem_1_1` Prop only; a literal paper-text ↔ Prop
comparison (α/γ/m conditions, exact sup-norm bound shape, domain generality) is STILL
OWED and needs the paper source.  Naming caveat: `paper2_theorem_1_1_chiZero_
unconditional` is conditional (on Hiter+HWdata); "unconditional" refers only to the
other legs' discharge.  Correct headline phrasing: "Paper 2 Theorem 1.1, restricted to
the χ₀=0 / a,b>0 / α≥1 / γ≥1 / interval-domain slice, modulo the per-datum residual
whose satisfiability is open."
