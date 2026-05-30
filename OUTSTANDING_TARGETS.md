# OUTSTANDING TARGETS — 挨个推

Ordered, trackable checklist of remaining work. Main line = Paper1 Theorem 1.1
(traveling-wave existence) via the classical C¹ ball / Duhamel route, plus the
Paper2 Theorem 1.1 (bounded-domain global existence) umbrella.

Status: TODO / WIP / DONE. Each target is a real theorem unless marked textbook.
Invariant throughout: 0 sorry, 0 admit, 0 custom axiom, full build green.

| # | Target | Status | Depends on | Note |
|---|--------|--------|-----------|------|
| T0 | `hChemDiv_joint_meas` measurability frontier | DONE | — | diffQuotLimsup AE surrogate; `_resolver` drops the measurability hypothesis |
| T1 | full-kernel gradient L∞→L∞ estimate (Step 6 tiling) | DONE | T0 | `105aaa0`; unconditional, end-to-end, green 8354 |
| T2 | wire full kernel operator into `_clean/_cleaner/_resolver` hmap chain | WIP (grad core done) | T1 | full-kernel source grad bounds + combiner DONE (`c46e996`, `d5fb043`); remaining: full-kernel initial-data IBP bound + `_clean_full` rebuild discharging `hGradEq` |
| T3 | Neumann BC fidelity fix: `intervalDomainNormalDeriv` genuine one-sided deriv = 0 (replace hardcoded 0), re-prove ~24 users | TODO | — | independent; current BC conjunct is VACUOUS; IBP needs genuine g'(0)=g'(1)=0 |
| T4 | energy IBP: `Eprime ≤ K·E` (PDE substitution + Neumann IBP + Lipschitz absorption) | TODO | T3 | needs genuine boundary from T3 |
| T5 | `hSol` / parabolic boundary regularity: ∂ₜ,∂ₓ,∂ₓₓ continuous/integrable up to spatial endpoints x→0⁺,1⁻ | TODO (deep) | — | real classical PDE theorem; closes the closed-slab envelope → gluing. The big wall. |
| T6 | `localExistence` genuine constructor: full-kernel mild solution satisfies the full 6-conjunct regularity | TODO (deep) | T1, T5 | needs joint Weierstrass `continuous_tsum` + Duhamel term C² |
| T7 | representation reassembly + approximate-identity limit → Paper1 Theorem 1.1 final assembly | TODO | T5, T6 | gluing → Theorem 1.1 |
| T8 | Paper2 Theorem 1.1 (γ≥1): discharge the 2 remaining textbook PDE inputs (`localExistence` + `uniformLocal` parabolic continuation) | TODO (textbook) | — | standard maximal-continuation ingredients Paper2 cites from Henry §3.3 / Amann; umbrella already reduced 4→2 |
| T9 | Paper1 Thm 1.2 (stability) / Thm 1.3 (uniqueness); Paper3 exponential-convergence cores | OPEN (later) | — | not on the current critical path |

## Push order (挨个推)

1. **T2** — wire full operator into `_clean` chain (in progress). Quick payoff: gradient prerequisite closed.
2. **T3** — Neumann BC fidelity fix. Independent, mechanical-ish, unblocks T4. Do next.
3. **T4** — energy IBP `Eprime ≤ K·E`. After T3.
4. **T5** — `hSol` parabolic boundary regularity. The deep wall; the rest of Theorem 1.1 gates on it.
5. **T6 → T7** — localExistence constructor → final assembly → Paper1 Theorem 1.1.
6. **T8** — Paper2 Theorem 1.1 textbook inputs (can run alongside; standard).
7. **T9** — broader paper theorems, later.

Source of truth for paper-theorem status: `THEOREM_STATUS.md`. Round-by-round
detail: `CLOSURE_MAP.md`.

## T2 detail (2026-05-29)

`ShenWork/PDE/IntervalFullKernelGradEstimate.lean` (new) — full-Neumann-kernel
analogues of the zeroth-reflection `intervalCoupledDuhamel_grad_*`, all built on
T1's capstone `intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t`:
- **DONE** `intervalFullCoupledDuhamel_grad_integrand_pointwise_bound` — per-slice
  `|deriv(S_full(t−s)F)x| ≤ Cgrad·(t−s)^(−1/2)·C_source`.
- **DONE** `intervalFullCoupledDuhamel_grad_integral_bound_of_leibniz` — source
  integral gradient `≤ Cgrad·2√T·C_source` (under a Leibniz interchange hypothesis).
- **DONE** `intervalFullCoupledDuhamel_grad_estimate_of_leibniz` — combiner:
  `|deriv(S_full(t)u₀ + ∫…)x| ≤ G_init + Cgrad·2√T·C_source`, taking the
  initial-data gradient bound `hInit_grad` abstractly.

**DONE** `intervalNeumannFullKernel_integral_eq_one` (`84d4664`,
`ShenWork/PDE/IntervalFullKernelMass.lean`): `∫₀¹ K_full(t,x,y) dy = 1` (mass
conservation) — Tonelli + tiling `tsum_cell_integral_eq_integral` (g=heat) +
`heatKernel_integral_eq_one`. The `∫₀¹|K̃| ≤ ∫₀¹ K_full = 1` input for the IBP bound.

Remaining for full T2 (each substantial, T1-scale):
1. **full-kernel initial-data IBP gradient bound** `|deriv(S_full(t)u₀)x| ≤ ‖u₀'‖∞`
   for C¹ `u₀` with `u₀(1)=0`. Needs a **lattice IBP engine** (analogue of the
   zeroth-reflection two-term `intervalSemigroupOperator_deriv_ibp_identity_unit`
   in HeatKernelGradientEstimates.lean:3147, but for the period-2 lattice kernel):
   - `deriv(S_full t u₀) x = ∫₀¹ ∂ₓK_full(t,x,y)·u₀ y dy` from
     `intervalFullSemigroupOperator_hasDerivAt_fst` (6.6 hrepr, f=u₀);
   - `∂ₓK_full = ∂_y K̃`, `K̃ = ∑ₖ(−heat(x−y+2k)+heat(x+y+2k))` — establish `∂_y K̃`
     via `hasDerivAt_tsum` (mirror 6.3) + continuity of `∂_y K̃` on [0,1];
   - IBP in y (`intervalIntegral.integral_deriv_mul_eq_sub` / product-rule), boundary
     `[K̃ u₀]₀¹ = 0` since `K̃(t,x,0)=0` (lattice symmetry) and `u₀(1)=0` ⇒
     `deriv = −∫₀¹ K̃ u₀'`;
   - `|deriv| ≤ ‖u₀'‖∞·∫₀¹|K̃| ≤ ‖u₀'‖∞·∫₀¹ K_full = ‖u₀'‖∞·1` (mass DONE above,
     `|K̃| ≤ K_full` pointwise). Discharges `hInit_grad`.
2. **`_clean_full` chain rebuild** — a parallel `intervalCoupledClassicalC1Ball
   Estimates_hmap_*` on `intervalFullKernelCoupledDuhamelOperator`, discharging the
   `hGradEq` hypothesis via the already-proved `intervalFullKernel_hGradEq`
   (IntervalFullKernelDuhamelGradEq.lean) and using the T2 grad estimates above.
   Large structural mirror of the ~hundreds-of-lines `_clean`/`_cleaner` proofs.

## T3 detail (scoped 2026-05-29) — Neumann BC fidelity fix

`intervalDomainNormalDeriv` (IntervalDomain.lean:2944) currently returns hardcoded
`0` at `{0,1}`, so the BC conjunct `D.normalDeriv (u t) x = 0` (Paper2/Statements.lean
:100,127,209,261) is VACUOUS. Atomic refactor (74 refs, 7 files; build red until all
fixed — must land in ONE commit):
1. Change the def to a genuine one-sided derivative:
   `if x.1=0 then derivWithin (intervalDomainLift f) (Set.Ici 0) 0
    else if x.1=1 then derivWithin (intervalDomainLift f) (Set.Iic 1) 1
    else deriv (intervalDomainLift f) x.1`.
   `intervalDomainNormalDeriv_endpoint` becomes FALSE → delete/replace with a genuine
   characterization lemma.
2. `intervalDomainNormalDeriv_const_zero` (IntervalDomainExistence.lean:293) — re-prove
   genuinely (`derivWithin_const = 0`). MECHANICAL. Covers ~16 uses (constant `c` /
   `ellipticV p c` constructors at lines 504,537,3224,3261,4012,4617).
3. The ABSTRACT-solution uses (IntervalDomainExistence.lean:5196, 6132) construct a
   classical solution from a glued `u,v` and currently get the BC for free. After the
   change they need the GENUINE one-sided `derivWithin (lift (u t)) (Ici 0) 0 = 0`,
   which must be threaded from the underlying solution's regularity — the non-trivial
   part (the abstract solution must carry a genuine Neumann field, or it is derived
   from a stronger regularity conjunct). This is the real content of T3 and gates T4.
NOTE: the `normalDeriv := fun _ _ => 0` instances in Statements.lean (2216,2612,2717,
2788,2860) and Paper3 are DIFFERENT degenerate domains (Unit-point etc.), NOT
`intervalDomain` — leave them; only `intervalDomainNormalDeriv` changes.
