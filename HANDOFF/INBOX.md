# Shen_work — Status (2026-06-01 ~13:00 CDT)

## Build: green (3541 jobs), HEAD = 961dc59

## Sorry: 5 in IntervalMildPicard.lean

### What was proved today (4 commits):
1. kernel_mul_integrable_of_source_integrable (IntervalDuhamelIntegrability.lean)
2. intervalFullSemigroupOperator_diff_Linfty_of_integrable (IntervalDuhamelIntegrability.lean)
3. hV both-integrable case CLOSED (value Duhamel diff bound)
4. C_Q_lip constant refactor (fix constant mismatch)
5. hq_diff_bound PROVED (flux Lipschitz on M-ball, 0 sorry) — 205 lines
6. hgamma_ge : 1 <= p.gamma added as theorem hypothesis

### Remaining 5 sorry (classified):

**Time-measurability blocked (4 sorry):**
- hV not-integrable x2 (L1001/1003)
- hG integral bound (L1227)
- hcont_preserved (L880)

All need: AEStronglyMeasurable (fun s => S(t-s)(r(s)) x) on [0,t].
Mathematically vacuous for Picard iterates (impossible branches).
Architectural fix: add joint-measurability hypothesis or restructure.

**Parabolic max principle (1 sorry):**
- hmapsTo_nn (L868): Phi preserves nonnegativity
Genuinely hard. Needs comparison principle for mild formulation.

### ChatGPT Pro R3 pending
Asked for architectural guidance on the time-measurability fix.

### Key infrastructure (all 0 sorry):
- chemFlux_div_lipschitz + hq_diff_bound (flux Lipschitz)
- Atom B3/B4 bounds
- O1 resolver positivity
- kernel_mul_integrable + semigroup diff L-infty
- valueDuhamel_sup/diff_bound_universal
