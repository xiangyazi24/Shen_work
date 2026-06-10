# ChatGPT tower verdict (a25d6360, relayed by Xiang 2026-06-10 ~15:30)

## Executive verdict
NOT a raw global tower (Repr × raw TimeC1 × K2 × K1). The consumers over-ask:
uniformWiring_closure wants GLOBAL packages for raw unshifted+shifted source
families, and the shifted hdecay quantifies all σ ≥ 0 (absolute times beyond
T where cone data gives nothing). The executable tower is a WINDOW/LOCAL-
WITNESS tower + small wrapper variants replacing exact-global consumer points
by "global clamped package + agreement on the read interval" (the proven
limit-side pattern).

## Carrier (minimal)
TowerLevel p u₀ M A₂ T n:
- hrepr_sum/hrepr_agree: iterateReprCoeff repr, horizon-local (0 < σ ≤ T)
- hG1/hG2: profiles G1profile p M σ / G2profile A₂ σ on (0,T]
- srcWin: ∀ lo hi (0<lo≤hi≤T), SourceWin — ∃ a, ∃ src : DuhamelSourceTimeC1 a,
  agreement with the canonical level-n source on [lo,hi] + windowSourceConst
  decay + value-family continuity (cont field explicit — NOT projectable
  from src.hadotcont).
DO NOT carry K1 (derive inside srcWin construction). DO NOT carry raw global
TimeC1 (too strong at n=0 and for shifted half-step decay).

## ShiftedSourceWitness (p u₀ n t): a, src, agreement on σ ∈ [0,t/2] with the
canonical shifted family, decay ≤ 2·Benv p M A₂ t/(kπ)². Add variants:
hbsum_succ_of_shiftedWitness, hagree_succ_of_shiftedWitness,
iterate_abs_deriv2_le_of_shiftedWitness (same proofs + integral/tsum
congruence on [0,t/2]).

## Key traps (9)
1. No raw global TimeC1 in the carrier. 2. The 10-line shift lemma
(DuhamelSourceTimeC1.shift_nonneg) is useful but NOT the whole shifted
solution (G2 needs the half-step window constant Benv(t), not a global
envelope). 3. The shifted source is read ONLY on σ ∈ [0,t/2] — state all
congruences exactly there. 4. No K1 in the tower. 5. ADD the missing K1
continuity wrapper (the restart K1 theorem exposes derivative+bound but NOT
hadotcont — the source producer needs it; prove via joint continuity of
logisticSourceDot on slabs + continuousAt_of_dominated_interval).
6. hagree_succ carries the OLD Continuous (intervalDomainLift u₀) trap —
needs the subtype variant. 7. Keep M₁ ≤ 2M explicit. 8. t vs σ two-time
bookkeeping: absolute time = t/2 + σ, read interval σ ∈ [0,t/2].
9. Wdata's a' index is only for window hypotheses; bcfun ignores it;
degenerate a' > T handled vacuously by wdata_all_of_wiring.

## n = 0 base
Repr: hbsum_zero/hagree_zero ✓ exist. K2: G1 kernel route; G2 homogeneous
heat trace (hG2base shape). Source package level 0: do NOT attempt raw
global from continuous u₀ (s=0 differentiability wall) — sourceWin_zero via
restart at offset := lo/2: S(s)u₀ = S(s−offset)(S(offset)u₀) with ZERO
source; feed the K1-from-restart machinery with the zero source package and
clamp to [lo,hi].

## Missing lemma list (dependency order, 12-16 declarations, 3-5 files)
A. IntervalDuhamelSourceShift.lean: (1) DuhamelSourceTimeC1.shift_nonneg
   (10 lines); (2) duhamelSpectralCoeff_congr_on_Icc; (3)
   localRestartCoeff_congr_on_Icc.
B. IntervalPicardIterateRestartLocal.lean: (4) hbsum_succ_of_shiftedWitness;
   (5) hagree_succ_of_shiftedWitness; (6) hagree_succ_of_subtypeCont.
C. IntervalPicardIterateC2BoundLocal.lean: (7)
   iterate_abs_deriv2_le_of_shiftedWitness; (8 optional) deriv-le variant.
D. IntervalPicardIterateTimeC1Full.lean: (9)
   picardIterate_K1_full_from_restart_of_representation (adds ContinuousOn
   of adot); (10) clampedIterateSource_duhamelSourceTimeC1 (window-local
   inputs → global clamped TimeC1 agreeing on [lo,hi]).
E. IntervalPicardSourceTower.lean: (11) tower_zero; (12) tower_succ
   (outline: half-step witness from L.srcWin (t/2) t + shift; repr n+1 via
   the witness variants; K2 n+1 via deriv2-witness variant + g2_step_closes;
   srcWin n+1: offset lo/2 restart + K1-full + source producer + soft-clamp);
   (13) tower_all.
F. IntervalPicardTowerProjection.lean: (14) wdata_all_of_tower (DIRECT fill
   of IterateWindowC2Data from TowerLevel — cleaner than via
   wdata_all_of_wiring); (15 optional) uniformWiring_of_tower; (16 bonus)
   limitBddOn_inputs_of_tower (closes hinterior via the spectral restart).

## Landing
hresCore_of_tower: hFacts/hFacts_T/hcont_iter cone-returned + Wdata :=
wdata_all_of_tower (tower_all …) → picardIterateResidualData_of_core
(discharges hsliceTC + hLcont_lim) → the capstone's HWdata.
Work estimate: medium campaign; the hard part is quantifier-shape and
agreement-window alignment, not new analysis.
