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
| T2 | wire full kernel operator into `_clean/_cleaner/_resolver` hmap chain | WIP | T1 | makes `hGradEq` end-to-end on the full Neumann kernel; closes the gradient prerequisite of the Duhamel ball |
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
