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
