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
| T2 | wire full kernel operator into `_clean/_cleaner/_resolver` hmap chain | **DONE (100% closed)** | T1 | full chain `_clean_full→_cleaner_full→_resolver_full` on the full Neumann kernel, `hGradEq` DISCHARGED + grad/sup/Leibniz all discharged (T2-a..m); **per-slice measurability now FULLY DISCHARGED** (T2-n): lattice `s_dependent` measurability proved via `measurable_tsum_int_of_summable` (tsum = pointwise limit of partial sums); `_resolver_full` carries NO `hF_meas`/`hF'_meas` — verbatim mirror of zeroth terminal |
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

**DONE — full-kernel initial-data IBP gradient bound + complete estimate**
(`ShenWork/PDE/IntervalFullKernelInitialIBP.lean`, `…GradEstimateFull.lean`):
- `intervalNeumannConjugateKernel` `K̃ = ∑ₖ(−heat(x−y+2k)+heat(x+y+2k))`, with
  `conjugateKernel_at_zero` (`K̃(·,0)=0`), `abs_conjugateKernel_le` (`|K̃|≤K_full`),
  `conjugateKernel_L1_bound` (`∫₀¹|K̃|≤1`) — T2-d.
- `hasDerivAt_conjugateKernel_snd` (`∂_yK̃ = ∂ₓK_full`, via 6.3 ± `y↦−y`) — T2-e.
- `intervalFullCoupledDuhamel_grad_initial_bound`: `|deriv(S_full(t)u₀)x| ≤ G_init`
  UNIFORM in t — hrepr (6.6) + IBP (`integral_mul_deriv_eq_deriv_mul`, boundary
  vanishes) + `conjugateKernel_L1_bound` — T2-f.
- `intervalFullCoupledDuhamel_grad_estimate_full`: complete `|deriv(S_full(t)u₀ +
  ∫…)x₀| ≤ G_init + Cgrad·2√T·C_source`, NO abstract `hInit_grad` — the
  full-Neumann-kernel analogue of `intervalCoupledDuhamel_grad_estimate_full_dirichlet`
  — T2-g. **The entire analytic gradient prerequisite is now done on the full kernel.**

**DONE — full-kernel sup bound + `_clean_full`:**
- `IntervalFullKernelSupBound.lean` (T2-h): `intervalFullSemigroupOperator_Linfty_bound`
  `|S_full(t)f x| ≤ M` (kernel nonneg/integrable/mass=1 + `integral_mono`).
- `IntervalFullKernelDuhamelSup.lean` (T2-i): `intervalFullKernelDuhamel_lift_abs_le`
  `|full Duhamel image| ≤ H+C·T` (mirror of `intervalFullDuhamelOperator_bound_of
  _source_bound`, `ht:0<t`).
- `IntervalFullKernelCleanFull.lean` (T2-j):
  **`intervalFullKernelClassicalC1BallEstimates_hmap_dirichlet_initial_clean`** —
  the snapshot-preservation hmap on the FULL kernel, with **`hGradEq` DISCHARGED**
  via the proved `intervalFullKernel_hGradEq` + lift-replacement + T2-g grad
  estimate; sup conjunct = T2-i; `hLiftSemigroupEq`/`hDom_int` discharged locally.
  The Leibniz/integrability bridges (`hSplit`/`hLeibniz`/`hGrad_int`) are carried as
  hypotheses (as the zeroth `_clean` carries `hSplit`). **This is the T2 essence:
  `hGradEq` — false at `x=1` for the zeroth kernel — is now discharged end-to-end on
  the full Neumann kernel.** Whole project green 8361; all axiom-clean.

**DONE — full chain `_clean_full → _cleaner_full → _resolver_full`:**
- `IntervalFullKernelLeibniz.lean` (T2-k): `intervalFullCoupledDuhamel_grad_integral
  _hasDerivAt` (source-integral HasDerivAt via `hasDerivAt_integral_of_dominated_loc
  _of_deriv_le` + 6.6 + T2-a + T2-h), `..._grad_leibniz` (= `.deriv`), `..._grad
  _integrand_intervalIntegrable`. Joint `s`-measurability `hF_meas`/`hF'_meas` as hyps.
- `IntervalFullKernelCleanerFull.lean` (T2-l): `_cleaner_full` — discharges `hSplit`
  (`deriv_add`), `hLeibniz`, `hGrad_int` via T2-k, forwarding to `_clean_full`.
- `IntervalFullKernelResolverFull.lean` (T2-m): `_resolver_full` — specialized to
  `R := intervalNeumannResolverR p`. Whole project green 8364; all axiom-clean.

The full chain mirrors the zeroth `_clean/_cleaner/_resolver` on the full kernel,
with `hGradEq` discharged (the decisive T2 content) and `hSplit/hLeibniz/hGrad_int`
discharged.  Difference from the zeroth: the per-slice measurability is carried as
`hF_meas`/`hF'_meas` hypotheses (the zeroth carries `hF_ae` + converts via the proved
`intervalSemigroupOperator_s_dependent_*` lemmas).

**DONE — lattice `s_dependent` measurability (T2-n, the last residual):**
`ShenWork/PDE/IntervalFullKernelSDependentMeasurable.lean` (new):
- `measurable_tsum_int_of_summable` — generic principle: an integer-lattice `tsum`
  of measurable, everywhere-summable functions is measurable (tsum reindexed `ℕ ≃ ℤ`
  = pointwise limit of `Finset.range` partial sums via `HasSum.tendsto_sum_nat`, each
  measurable, limit measurable by `measurable_of_tendsto_metrizable`).  Avoids the
  2-D `continuousOn_tsum` route entirely (no locally-uniform window bound needed).
- `deriv_heatKernel_global` — `deriv (heat t) x = −(x/2t)·heat t x` for ALL `t`
  (both sides `0` for `t ≤ 0`), so the heat kernel and its spatial derivative are
  jointly `(s,y)`-measurable by `fun_prop` on the closed form.
- `intervalNeumannFullKernel_s_dependent_measurable`,
  `deriv_intervalNeumannFullKernel_fst_s_dependent_measurable` — joint measurability
  of `(s,y) ↦ K_full(t−s,x,y)` and `∂ₓK_full(t−s,x,y)`.
- `intervalFullSemigroupOperator_s_dependent_{aestronglyMeasurable_x,
  deriv_…_x₀}` — Fubini (`integral_prod_right'`) ⇒ the `hF_meas`/`hF'_meas` forms.

`_cleaner_full` now takes a single `hF_ae` (joint source-field measurability) and
derives `hF_meas`/`hF'_meas` internally; `_resolver_full` discharges `hF_ae` via the
ROUND-14 `intervalCoupledSource_resolver_lift_aestronglyMeasurable`.  `_resolver_full`
is now a verbatim mirror of the zeroth terminal — **T2 100% closed, axiom-clean,
build 8365.**

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
