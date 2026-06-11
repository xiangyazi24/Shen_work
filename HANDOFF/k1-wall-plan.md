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
