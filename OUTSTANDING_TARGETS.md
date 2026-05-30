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
| T3 | Neumann BC fidelity fix: `intervalDomainNormalDeriv` genuine one-sided deriv = 0 (replace hardcoded 0), re-prove ~24 users | **DONE** | — | def now genuine one-sided `derivWithin (Ici 0) 0` / `(Iic 1) 1`; const constructors via `derivWithin_const` (`_const_endpoint_zero`); abstract-solution sites (5194/6130) thread BC from base solution via full function equality; EnergyStep boundary lemmas made conditional on genuine Neumann data, threaded as honest frontier hyps through the (dead) `_of_frontiers` energy scaffolding; build green 8365, axiom-clean |
| T4 | energy IBP: `Eprime ≤ K·E` (PDE substitution + Neumann IBP + Lipschitz absorption) | **Neumann-IBP core DONE; E'≤K·E assembled (cond. on T5)** | T3 | **T4-a** `intervalDomain_spatial_integrationByParts_identity` — genuine spatial IBP `∫test·Δf = boundaryTerm − ∫test'·f'` via Mathlib `_of_hasDeriv_right` (handles the lift endpoint kink) + product-lift/pair bridges; discharges the `hIBP` frontier. **T4-b** `intervalDomain_l2_half_energy_inequality_of_regularity` — L2 `E'(t)+dissipation ≤ χ·(…)+logistic` with `hIBP` (T4-a) + Neumann `hNeuR/hNeuL` (T3 `hsol.neumann`) genuinely discharged. Residual (= ③ honest frontier): C²-up-to-boundary regularity (**T5**) + chain rule `hLpTime` + PDE-substitution `hPDEIntegral`. `IntervalDomainNeumannIBP.lean`, build 8366, axiom-clean |
| T5 | `hSol` / parabolic boundary regularity: ∂ₜ,∂ₓ,∂ₓₓ continuous/integrable up to spatial endpoints x→0⁺,1⁻ | **DONE for abstract classical solutions — full-solution `E'≤K·E` UNCONDITIONAL (T5-u); hrepIoo eliminated**; constructed-solution regularity (conjuncts 7/8/9) → T6 | — | **T5-u (the closer):** `intervalDomain_l2_half_energy_inequality_unconditional` (`IntervalDomainL2CrossControl.lean`) — every `IsPaper2ClassicalSolution` at interior time satisfies `E'(t)+dissipation ≤ \|χ₀\|·(ε·gradDiss+Ceps·∫u^{2+ρ})+logistic`, NO extra hypothesis beyond the (independent textbook) interpolation `hcross`. **hrepIoo / DuhamelHeatValueRepresentation is ELIMINATED**: the cosine rep was only used to supply a global-C² profile for the spatial Neumann IBP, but conjunct (7) closed-C² + genuine Neumann give `deriv(lift u)=derivWithin(lift u)[0,1]` on ALL of `[0,1]` (interior equal; endpoints junk-0 = genuine-Neumann-0 via `derivWithin_congr_set`), so `deriv(lift u)` is continuous on the closed interval and the whole `_of_regularity` package is discharged from `hsol` alone. **T5-s:** `intervalDomain_l2_crossControl_of_regularity` — `hCrossControl` (`-χ₀·∫u·chemDiv ≤ \|χ₀\|·crossTerm`) unconditional via flux IBP (`intervalFluxByParts_open`) + pointwise `\|χ₀\|·\|a\|·\|b\|` bound + `integral_mono_on`. Build 8373, axiom-clean. Earlier reductions retained below. Design: `T5_DESIGN.md`. **Spatial C^{2,1}-up-to-boundary regularity DONE** for any slice represented by a bounded-coeff cosine heat value on `[0,1]` — covers homogeneous semigroup, Duhamel term, full solution `S_t u₀+D_t`. Files: `IntervalFullKernelBoundaryRegularity` (T5-a..e), `IntervalProfileBoundaryRegularity`+`IntervalDomainProfileIBP` (T5-g..i), `IntervalDomainL2HalfEnergyTimeLeibniz` (T5-j). **T5-i (R3)**: `eqOn_Icc_of_eqOn_Ioo_of_continuousOn` density bridge ⇒ energy inequality `_of_cosineProfile_interior` needs only the OPEN-`(0,1)` cosine representation (the natural form of `DuhamelHeatValueRepresentation`) + conjunct-7 closed C²; endpoints free by continuity. **T5-j/k/l (R1 DONE)**: `intervalDomain_l2_half_energy_hL2Time` proves `hL2Time` (`d/dt ½∫u²=∫u·∂ₜu`) **UNCONDITIONALLY** for any classical solution at interior time — closed-slab joint continuity = conjunct 9 × conjunct 8, and the measurability side conditions (`hF_meas`/`hF_int`/`hF'_meas`) follow from time-slice continuity (`ContinuousOn.aestronglyMeasurable`/`.intervalIntegrable`); deriv-field = `lift(u·∂ₜu)` EXACTLY on `[0,1]` (time-deriv ⇒ no spatial-jump a.e. issue). Wired into `intervalDomain_l2_half_energy_inequality_of_cosineProfile_solution` (T5-l), so `hL2Time` is no longer a frontier. **T5-m/n (R2 reduced + hA done)**: `intervalDomain_l2_half_energy_hPDEIntegral_of_integrable` reduces `hPDEIntegral` to interval-integrability of the 3 lifted integrands (integrate proved pointwise PDE + lift-linearity + `integral_{add,sub,const_mul}`); **`hPDEIntegral` (R2) now also UNCONDITIONAL** (`intervalDomain_l2_half_energy_hPDEIntegral_of_regularity`, T5-m..q): all three integrands discharged — `hA` (u·Δu) + `hC` (u²(a−bu^α)) from conjunct 7 + `u>0`; `hB` (u·chemDiv) by factoring the bounded `u` (`continuousOn_mul`) + chemotaxis-flux-divergence integrability `intervalDomainLift_chemDiv_intervalIntegrable_of_regularity` (the closed flux quotient `q̃=(lift u)·(derivWithin(lift v))/(1+lift v)^β` is `C¹` via `ContDiffOn.div`+`Real.contDiffAt_rpow_const_of_ne`+`v_nonneg`; `chemDiv=deriv q ↔ derivWithin q̃` on the interior). **Capstone `intervalDomain_l2_half_energy_inequality_of_cosineProfile_full` (T5-r)**: full-solution `E'≤K·E` with BOTH `hL2Time` (R1) and `hPDEIntegral` (R2) discharged. **Only remaining inputs**: the OPEN-`(0,1)` cosine representation `hrepIoo` (`DuhamelHeatValueRepresentation` body = Fubini+`parabolicGain_le_one`, R3's only gap) + `hCrossControl`. Conjuncts 8/9 for the cosine *constructed* solution (Weierstrass-M) belong to T6. Build 8372, axiom-clean. |
| T6 | `localExistence` genuine constructor: full-kernel mild solution satisfies the full 6-conjunct regularity | **WIP — time-IBP route (Lemmas 1–2 done)** | T1, T5 | **Route CORRECTED: time-IBP, not spectral** (spectral needs `∑\|ĝₙ\|<∞`, mismatched with bootstrap; matches `T5_DESIGN §7.3` B1). Target `intervalDuhamelTerm_closedC2_of_timeC1_source`: time-`C¹` source ⟹ `∂ₓₓD(t)=S(t)g(0)−g(t)+∫₀ᵗS(t−s)∂ₛg(s)ds` (integral kernel `S(t−s)` is derivative-free → bounded, `(t−s)^{−3/2}` gone). **`ShenWork/PDE/IntervalDuhamelClosedC2.lean`:** **Lemma 1** (semigroup endpoint `S(r)f→f` as `r↓0`) = repo's `intervalFullSemigroup_tendsto_id_at_zero` (already proved). **Lemma 2 DONE** (spectral heat identity `∂ₓₓS(r)=∂ᵣS(r)`): `unitIntervalCosineHeatValue_heat_identity` — both `=unitIntervalCosineHeatSecondValue`; new `unitIntervalCosineHeatValue_hasDerivAt_time` (termwise `∂ᵣ` via `hasDerivAt_tsum_of_isPreconnected` on `Ioi(r/2)`) + `secondPointWeight=−λₙ·pointWeight`. **Next (awaiting finer statements):** steps 3–7 — time chain rule, interval FTC `[0,t−ε]` ε↓0, RHS closed continuity, `ContDiffOn ℝ 2 (Icc 0 1)` assembly, Neumann endpoints. (Old spectral file `IntervalDuhamelSpectralC2.lean` kept — commutator split is valid math, just not the chosen route.) Build 8378, axiom-clean. |
| T7 | representation reassembly + approximate-identity limit → Paper1 Theorem 1.1 final assembly | TODO | T5, T6 | gluing → Theorem 1.1 |
| T8 | Paper2 Theorem 1.1 (γ≥1): discharge the 2 remaining textbook PDE inputs (`localExistence` + `uniformLocal` parabolic continuation) | **Gluing/uniqueness HALF PROVEN (axiom-clean); only EXISTENCE remains** | — | **Confirmed 2026-05-30:** `GlobalSolutionGluingFromReachability_of_regime_gammaGeOne` is axiom-clean — the entire gluing/uniqueness/global-from-reachability apparatus is PROVEN from regime (χ₀≤0,a,b>0)+γ≥1+positivity pass-through (the `Kunif` chain is fully discharged: `uniformLiftBoundZeroM_of_regime`→`gronwall_const_of_uniformLiftBoundZeroM`→`boundednessHypothesis_of_uniformSupBoundZeroM`). **Sole remaining frontier = EXISTENCE** (`localExistence` + `IntervalDomainUniformLocalExistence`), i.e. construct a classical solution with the 9-conjunct regularity. Its core is conjunct-7 (D_t∈C²), a genuine deep wall (see T5_DESIGN §7: `DuhamelHeatValueRepresentation` is over-strong/false for a bounded source; honest route is direct ∂ₓₓD_t via heat-eq `∂ₓₓS=∂_rS`+time-IBP onto `∂_s g_s`, needing parabolic-regularity infra absent from Mathlib). |
| T9 | Paper1 Thm 1.2 (stability) / Thm 1.3 (uniqueness); Paper3 exponential-convergence cores | OPEN (later) | — | not on the current critical path |
| T10 | Paper3 Thm 2.2–2.5 linear parts — EXACT explicit-threshold formula upgrades | **DONE (self-contained, no existence)** | — | **Thm 2.4/2.5 (added):** `NonminimalGlobalStabilityFormulaCondition.linearlyStable_of_max_threshold_le_mode_one` + `MinimalGlobalStabilityFormulaCondition.linearlyStable_of_chiBeta_le_mode_one` — linear stability from the EXACT first-mode threshold `max(chiStrong…)/chiBeta ≤ paperFormula(λ₁)=χ\*`, strictly sharper than the existing `…_of_firstNonzero_lower` (crude `A·(μ+firstNonzero)`). Thm 2.3 linear part = `χ₀≤0` (already unconditional). `ShenWork/Paper3/CriticalSensitivityExactValue.lean`: **exact χ\* value** `paperCriticalSensitivity_eq_mode_one_of_firstMode_dominant` — closes the prior crude gap `A·(μ+firstNonzero) ≤ χ\* ≤ paperFormula(λ₁)` with `χ\* = paperFormula(λ₁)` exactly, in the first-mode-dominant regime `aαμ ≤ firstNonzero²` (per-mode threshold's λ-factor is U-shaped, min at √(aαμ), monotone past it; helper `sigmaCriticalChiPaperFormula_le_of_firstMode_dominant`). **Sharp dichotomy** `linearStability_dichotomy_at_mode_one_threshold` (+ `_unitInterval`, +positive/minimal-equilibrium): `χ₀ < paperFormula(λ₁) ⟹ LinearlyStable`, `paperFormula(λ₁) < χ₀ ⟹ LinearlyUnstable`. Genuine spectral notions (∀/∃ mode `sigma(λ_n)≶0`). Formula-level, NO existence dependence; regime is an honest parameter condition (not a smuggled hard half). Build 8374, axiom-clean. Upgrades Thm 2.2's linear branches from abstract-`inf` to explicit first-mode formula. |

## Push order (挨个推)

1. **T2** — wire full operator into `_clean` chain (in progress). Quick payoff: gradient prerequisite closed.
2. ~~**T3** — Neumann BC fidelity fix.~~ **DONE.** Def genuine; constructors + abstract sites + EnergyStep scaffolding all green & honest.
3. ~~**T4** — energy IBP `Eprime ≤ K·E`.~~ **Neumann-IBP core DONE** (T4-a/T4-b). The genuine spatial Neumann IBP is proved and the L2 energy inequality is assembled with `hIBP`+Neumann discharged. Full unconditionality now gates on **T5** (C²-up-to-boundary regularity) + the chain-rule/PDE-substitution frontiers — these supply the regularity package, `hLpTime`, `hPDEIntegral` consumed by T4-b. Lp analogue is symmetric (T4-a applies verbatim with `test = LpDiffusionTest`, `f = u t`).
4. **T5** — `hSol` parabolic boundary regularity. The deep wall; the rest of Theorem 1.1 gates on it. **Now also unblocks T4-b's residual** (regularity package + integrability for `hLpTime`/`hPDEIntegral`).
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

## NEXT TARGET DIAGNOSIS (2026-05-30, after T5-u) — `Kunif` → gluing/uniqueness

The single-solution L² energy inequality is now unconditional (T5-u).  The next
high-value gate on the **gluing/uniqueness critical path** (→ Paper2 Thm 1.1
uniqueness) is `Kunif`, the UNIFORM Grönwall constant in
`IntervalDomainL2UBoundedDatumUniform` (see
`IntervalDomainL2UBoundedDatumUniformOfBounded.lean` header for the honest blocker).

The per-time bound `intervalDomainL2U_energy_diffIneq_bound_uniform_explicit_zeroM`
already proves `∫ integrandDeriv τ ≤ (χ₀²·Cflux(M)+2L)·E_u(τ)` with a *uniform* `M`
(sup bound) and `L` (logistic Lipschitz).  The ONLY missing piece for a τ-uniform
`K` is a **quantitative resolver-gradient sup bound** `‖∂ₓR(νu^γ)‖_∞ ≤ F(M)`
(currently `resolverGradReal_bounded` gives only non-quantitative compactness
existence).

**Reachable path (no Mathlib gap):** `intervalNeumannResolverR_grad_sup_lipschitz`
already gives `|RGrad u₁ − RGrad u₂| ≤ √(∑W_k²)·‖sourceCoeffΔ‖_{L²}`, gated on
per-point summability side-conditions `Summable (k ↦ R̂_k·kπ·sin(kπx))`.  Those ARE
provable: terms `~ Â_k/k`, summable by Cauchy–Schwarz (`∑Â_k/k ≤ √(∑Â_k²)·√(∑1/k²)`,
source `Â ∈ ℓ²` via Bessel).  Steps: (1) sup version of the grad bound (set `u₂=0`);
(2) the summability side-conditions from `Â ∈ ℓ²`; (3) `‖sourceCoeff(u)‖_{L²} ≤
ν·M^γ` from `u ≤ M` (Parseval/Bessel); (4) assemble `G(M)` → uniform `Cflux(M)` →
uniform `K` → `Kunif` → `IntervalDomainL2UBoundedDatumUniform` →
`GlobalSolutionGluingFromReachability` (Thm 1.1 uniqueness).  γ≥1 regime supplies the
uniform `M` via `Lemma_3_1_intervalDomain` (sup-norm monotonicity).  This is a
multi-step elliptic-regularity build, a genuine next sub-project.

## CORRECTION (2026-05-30) — the `Kunif` "next target" above is ALREADY CLOSED

The "NEXT TARGET DIAGNOSIS" section above (resolver-gradient sup bound → `Kunif`)
was written from the OUTDATED blocker note in
`IntervalDomainL2UBoundedDatumUniformOfBounded.lean`.  On inspection the entire
chain is already proved, axiom-clean:
* `resolverGrad_sup_le_of_ub` (`IntervalDomainResolverSupQuantitative.lean`) — the
  quantitative `|RGrad u x| ≤ √(∑W_k²)·2νM^γ` from a uniform upper bound `M` (the
  "Piece 1" file already discharged the per-point summability + cosine-Bessel that
  the blocker note flagged as missing);
* `intervalDomainL2U_energy_diffIneq_bound_uniform_explicit_zeroM` — the fully
  `M`-quantitative per-time bound `∫ ≤ (χ₀²·CfluxQuantZeroM(M)+2L)·E_u`;
* `gronwall_const_of_uniformLiftBoundZeroM` — uniform `K` from a uniform-in-τ lift
  bound (= `Kunif`);
* `uniformLiftBoundZeroM_of_regime` — the uniform lift bound `M=max(‖u₀‖,(a/b)^{1/α})`
  from the Thm-1.1 regime (χ₀≤0,a,b>0) + positive bounded datum;
* `boundednessHypothesis_of_uniformSupBoundZeroM` → `IntervalDomainL2UBoundednessHypothesis`
  → the gluing/uniqueness chain.

So `Kunif` / the gluing-uniqueness obligation is NOT a frontier.  The genuine
remaining critical-path frontier is **T6 / localExistence**: constructing a
full-kernel classical solution that satisfies the regularity conjuncts (7/8/9).
Its core analytic step is exactly `DuhamelHeatValueRepresentation` (the Fubini
`∫₀ᵗ↔∑'ₙ` interchange + `parabolicGain_le_one`), which gives conjunct (7) for the
*constructed* Duhamel term — the same predicate T5-u showed is NOT needed for the
energy inequality but IS needed to exhibit a solution.  Plus `uniformLocal`
(parabolic continuation with uniform δ(M)).
