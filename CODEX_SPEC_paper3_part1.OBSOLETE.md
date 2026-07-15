# ⚠️ OBSOLETE — DO NOT DISPATCH
# Paper 3 Thm 2.1 Part 1 (guarded a>0,b>0,m>=1) is ALREADY CLOSED unconditionally via
# Theorem_2_1_part1_corrected_intervalDomainM (contactSmallCeiling route,
# IntervalDomainPersistenceGeneralMPart1Corrected.lean). The hStrongMaximumPersistence
# 'leaf' in the headline matrix was STALE. Verified 2026-07-15 (ChatGPT Q5050 + repo read).
# This spec's IntervalDomainLogisticULowerFields route would have been a redundant parallel
# proof (zombie/over-build). Kept only as a record.

# CODEX SPEC — Paper 3 Theorem 2.1 Part 1 (guarded a>0, b>0, m≥1) persistence

## Goal
Discharge the remaining hypothesis of `Theorem_2_1_part1_intervalDomain_of_pointwise_persistence`
(ShenWork/Paper3/IntervalDomainTheorem21Part1.lean): `hStrongMaximumPersistence` = the
uniform positive lower envelope `∃ δU>0, δU ≤ liminfInfValue intervalDomain u` for every
`PositiveGlobalBoundedSolution` when `a>0, b>0, 1≤m`. Concretely: prove the `part1` and
`part1Liminf` fields of `IntervalDomainLogisticULowerFields`
(ShenWork/Paper3/IntervalDomainPersistenceDiniFrontier.lean), then instantiate the structure
and feed `.to_persistence` to close Part 1. NO sorry/admit/native_decide/custom axiom.

## The reduction is ALREADY 90% built — find the exact missing piece, do NOT rebuild
The residual reduces to ONE deep lemma: the parabolic lower-Dini estimate at the attained
spatial minimum,
  `RightLowerDiniGE (intervalDomainSpatialMin u) (fun z => a·z − b·z^{1+α} − Cχ·z^m) (Ioi 0)`
i.e. the `LogisticSpatialMinimumDini` predicate. Everything downstream is built:
- SCALAR engine (done, clean-3): `local_logistic_liminf_ge_of_RightLowerDiniGE`
  and `strict_logistic_subsolution_le_of_local_RightLowerDiniGE`
  (ShenWork/Paper3/GeneralMScalarDiniComparison.lean). Its `qη.a = q.a − η` device ABSORBS
  the `−Cχ z^m` cross-diffusion term: pick η dominating `Cχ z^m` on the sub-carrying-capacity
  floor range, so `a·z − b·z^{1+α} − Cχ z^m ≥ (a−η)·z − b·z^{1+α}` there. Reuse verbatim.
- `intervalDomainSpatialMin_attained` (ShenWork/Paper3/IntervalDomainPersistenceDiniAudit2.lean):
  the interval inf IS attained (compact + continuity) — no whole-line translate compactness needed.
- The Dini producers for the OTHER branches are TEMPLATES to mirror:
  `IntervalDomainPersistenceGeneralMDini.lean`, `...GeneralMGrowthDini.lean`,
  `...GeneralMPart3.lean`, `...PersistenceActualLinearPart2.lean`,
  `...PersistenceDiniBridge.lean`, `...GeneralMGrowthBarrier.lean`. Each proves a
  `RightLowerDiniGE (intervalDomainSpatialMin u) …`. Read them, find which case (if any)
  already covers a>0,b>0,m≥1, and what is DIFFERENT for the part1 logistic RHS.
- Packaging: `IntervalDomainLogisticULowerFields.to_inputs` / `.to_persistence` already close
  from the six fields. part2/part2Liminf/part3/part3Liminf are ALREADY PROVED elsewhere —
  reuse those producers by exact grepped name; you only need part1/part1Liminf.

## Task, in order
1. Grep-map: is there an existing producer for `part1`/`part1Liminf` (a>0,b>0,m≥1)? If a
   near-match exists (e.g. a general-m Dini lemma that already yields this floor), wire it.
2. If genuinely missing, prove the part1 spatial-min Dini estimate by mirroring the closest
   template. The mechanism at the attained min x_t (Neumann): `u_x(t,x_t)=0`, `u_xx(t,x_t)≥0`,
   the cross-diffusion `−χ∂_x(u^m ∂_x v)` bounded by `Cχ·(inf u)^m` (v-regularity from the
   bounded solution), reaction `a·u − b·u^{1+α}` at the min ⇒ lower-right Dini derivative of
   `t ↦ inf_x u` ≥ `a·(inf u) − b·(inf u)^{1+α} − Cχ·(inf u)^m`. Same family as the Paper 1
   χ≤0 floor mechanism just closed (ShenWork/Paper1/WholeLineCauchyLongTimeFloor.lean) — but
   here inf is ATTAINED so it's a direct second-derivative test, no approximate-min penalty.
3. Feed the Dini estimate through the scalar engine → `part1`/`part1Liminf`; instantiate
   `IntervalDomainLogisticULowerFields`; close Part 1 via `.to_persistence` +
   `Theorem_2_1_part1_intervalDomain_of_pointwise_persistence` (also needs
   `hEllipticLiminfComparison` — grep for an existing elliptic-liminf producer, likely already
   proved for part2/part3).

## Constraints
New file(s) only under ShenWork/Paper3/. Do NOT edit existing files. No git commands. ≤100
cols. Reuse by exact grepped name. Remote verify per CODEX_OPS_remote_build.md with
STAGING=/dev/shm/lean/Shen_work-p3. #print axioms every headline (expect clean-3), then remove.

## Report
Whether part1/part1Liminf closed and Part 1 is now unconditional (for a>0,b>0,m≥1); every new
theorem's full name + #print axioms; if the spatial-min Dini estimate walls, the exact goal
state, file:line, and the specific missing fact (e.g. a v-gradient bound, a Neumann-min
second-derivative lemma). Do not fake, do not weaken.
