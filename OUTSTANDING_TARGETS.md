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
| T6 | `localExistence` genuine constructor: full-kernel mild solution satisfies the full 6-conjunct regularity | **time-IBP atom CLOSED (D_t∈C² for time-C¹ source); constructor wiring remains** | T1, T5 | **ATOM FULLY CLOSED 2026-05-30** (`IntervalDuhamelClosedC2.lean`, build 8378 axiom-clean): `intervalDuhamelTerm_closedC2_of_timeC1_source` — given the honest source package `DuhamelSourceTimeC1 a` (time-`C¹` cosine coeffs `s↦a s n` with continuous deriv `adot`, ℓ¹ envelope dominating coeffs uniformly in time, uniform deriv bound), the Duhamel term `x↦∫₀ᵗS(t−s)g(s)(x)ds` is `ContDiff ℝ 2` ∧ Neumann `∂ₓD(t,0)=∂ₓD(t,1)=0` ∧ spectral `∂ₓₓD=∑bₙ(−(nπ)²cos)`. Pieces: **(E)** `cosineCoeffSeries_contDiff_two` (∑λₙ|bₙ|<∞ ⇒ `ContDiff ℝ 2` of ∑bₙcos, via `cosineCoeffSeries_grad_hasDerivAt`/`_grad2_hasDerivAt` × `hasDerivAt_tsum`); **(D)** `duhamelSpectral_eq_cosineSeries` (D=∑bₙcos via ∑∫=∫∑ swap + cos pull-out, `bₙ=duhamelSpectralCoeff a t n`); **(S)** `duhamelSpectralCoeff_eigenvalue_summable` (∑λₙ|bₙ|<∞ via per-mode time IBP `duhamelCoeff_eigenvalue_mul` + ℓ¹ envelope + `duhamelGainIntegral_summable`); **(I/N)** `cosineCoeffSeries_deriv2_eq` + `_deriv_at_zero/_one`. **Remaining for T6:** wire the constructor — show the full-kernel mild solution's Duhamel source satisfies `DuhamelSourceTimeC1`, and assemble the 6-conjunct `localExistence`. The hard analytic atom (∂ₓₓ of a `(t−s)^{−3/2}`-singular Duhamel integral) is now DONE. **Steps 1–4 done** (`IntervalDuhamelClosedC2.lean`): L2 heat identity `∂ₓₓS=∂ᵣS`; **step 3** `duhamelIntegrand_hasDerivAt` (time chain rule `d/ds[S(t−s)g(s)]=−∂ₓₓS(t−s)g(s)+S(t−s)∂ₛg(s)` via termwise product rule + `hasDerivAt_tsum_of_isPreconnected` away from `s=t`); **step 3a/3b** per-mode pieces; **step 4** `duhamelCutoff_FTC` (`∫₀^{t−ε}(…)=S(ε)g(t−ε)−S(t)g(0)`, FTC + continuity-on-compact `unitIntervalCosineHeat{Second,}Value_comp_sub_continuousOn`). **Step 5a DONE** `duhamelCutoff_secondValue_eq` (rearrange: `∫₀^{t−ε}secondValue = value t(a 0) − value ε(a(t−ε)) + ∫₀^{t−ε}value(adot)`). **Step 5 limit-assembly DONE** `duhamelSecondValue_tendsto`: `∫₀^{t−ε}∂ₓₓS(t−s)g → P(t)(x)=value t(a 0)−gt+Ig = S(t)g(0)−g(t)+∫₀ᵗS(t−s)∂ₛg`, GIVEN two explicit analytic-frontier convergences `hconv1` (joint approx-identity `S(ε)g(t−ε)→g(t)`) + `hconv2` (improper→Lebesgue `∫₀^{t−ε}value(adot)→∫₀ᵗ`). **Step 5 FULLY CLOSED (hconv1+hconv2 both proved, axiom-clean):** `duhamelSecondValue_tendsto_closed` — `∫₀^{t−ε}∂ₓₓS(t−s)g → P(t) = S(t)g(0)−g(t)+∫₀ᵗS(t−s)∂ₛg` unconditional under the source-regularity inputs (bounded coeffs+time-deriv, continuous ∂ₛg, uniformly-ℓ¹ coeffs). `hconv2` (`duhamelValue_adot_improper_tendsto`): Tannery + ∑∫=∫∑ swap, per-mode L¹ summable via `parabolicGain_le_one` (`duhamelMode_integralNorm_summable`) — NO operator contraction. `hconv1` (`duhamelValue_a_joint_tendsto`): Tannery joint approx-identity under ℓ¹ source coeffs. **Step 7 STARTED**: per-mode time IBP `duhamelCoeff_eigenvalue_mul` (λ·∫₀ᵗe^{−(t−s)λ}a = a(t)−e^{−tλ}a(0)−∫₀ᵗe^{−(t−s)λ}∂ₛg, FTC, singularity-free) + `cosineCoeff_summable_of_eigenvalue_summable` (∑λₙ|bₙ|<∞ ⇒ ∑(nπ)|bₙ|<∞ ∧ ∑|bₙ|<∞). **Remaining (documented in-file precisely):** cosine-series C² engine `cosineCoeffSeries_contDiff_two` (∑bₙcos C² from ∑λₙ|bₙ|<∞, via hasDerivAt_tsum ×2 — structure clear, needs arg debugging); spectral D form D=∑bₙcos (swap); ∑λₙ|bₙ|<∞ for the actual bₙ (IBP+ℓ¹); ∂ₓₓD=P; Neumann (cosineMode_neumann_left/right); atom assembly. **Steps 1–5 fully closed; step 6–7 doc:** (∂ₓₓD=P via double-cutoff Fubini + space-FTC, singularity-free; + ContDiffOn assembly + Neumann). Build 8378, axiom-clean. ~Earlier note:~ `hconv2` provable WITHOUT operator contraction — per-mode `∫₀ᵗ|fₙ| ≤ Mdot·(1−e^{−tλₙ})/λₙ ≤ Mdot/λₙ` (reuse `intervalExpKernel_time_integral` + `parabolicGain_le_one`), `∑ < ∞` ⟹ `MeasureTheory.integrable_tsum` ⟹ `F` integrable on `[0,t]` ⟹ primitive continuity ⟹ `hconv2`; `hconv1` needs ℓ¹ cosine coeffs of `g(t)` (source spatial regularity) + the joint-split `S(ε)(g(t−ε)−g(t))+S(ε)g(t)` (reuse `intervalFullSemigroup_tendsto_id_at_zero` + `intervalFullSemigroupOperator_Linfty_bound`). Steps 6–7 (ContDiffOn assembly + Neumann) follow. Build 8378, axiom-clean. **Route CORRECTED: time-IBP, not spectral** (spectral needs `∑\|ĝₙ\|<∞`, mismatched with bootstrap; matches `T5_DESIGN §7.3` B1). Target `intervalDuhamelTerm_closedC2_of_timeC1_source`: time-`C¹` source ⟹ `∂ₓₓD(t)=S(t)g(0)−g(t)+∫₀ᵗS(t−s)∂ₛg(s)ds` (integral kernel `S(t−s)` is derivative-free → bounded, `(t−s)^{−3/2}` gone). **`ShenWork/PDE/IntervalDuhamelClosedC2.lean`:** **Lemma 1** (semigroup endpoint `S(r)f→f` as `r↓0`) = repo's `intervalFullSemigroup_tendsto_id_at_zero` (already proved). **Lemma 2 DONE** (spectral heat identity `∂ₓₓS(r)=∂ᵣS(r)`): `unitIntervalCosineHeatValue_heat_identity` — both `=unitIntervalCosineHeatSecondValue`; new `unitIntervalCosineHeatValue_hasDerivAt_time` (termwise `∂ᵣ` via `hasDerivAt_tsum_of_isPreconnected` on `Ioi(r/2)`) + `secondPointWeight=−λₙ·pointWeight`. **Next (awaiting finer statements):** steps 3–7 — time chain rule, interval FTC `[0,t−ε]` ε↓0, RHS closed continuity, `ContDiffOn ℝ 2 (Icc 0 1)` assembly, Neumann endpoints. (Old spectral file `IntervalDuhamelSpectralC2.lean` kept — commutator split is valid math, just not the chosen route.) Build 8378, axiom-clean. |
| T7 | representation reassembly + approximate-identity limit → Paper1 Theorem 1.1 final assembly | **spatial bridges [A][B] DONE; blocked at [D2] fixed-point bootstrap** | T5, T6 | **2026-05-30, `IntervalCosineSliceRegularity.lean` + `T7_DESIGN.md`.** Orientation established the ring atom→Theorem 1.1: a mild-solution slice `S_t u₀+D_t` is a single cosine series `∑cₙcos` with `∑λₙ|cₙ|<∞`, so the generic engine (`cosineCoeffSeries_contDiff_two`) + T6 atom cover the SPATIAL regularity conjuncts. **[A] DONE** `intervalDomainCosineSlice_conjunct7` — cosine-series slice ⟹ conjunct (7) (closed-`Icc` `C²` + endpoint `deriv=0`); endpoint deriv via junk-value non-differentiability of the zero-extension (`intervalDomainLift_deriv_{left,right}_endpoint_zero_of_ne`), nonzero-endpoint hyp faithful for positive solutions. **[B] DONE** `intervalDomainCosineSlice_contDiffOn_Ioo` (conjunct 3) + `..._neumann_limit_{left,right}` (conjunct 6, genuine one-sided Neumann LIMIT via `EventuallyEq.deriv_eq` + `ContDiff.continuous_deriv` + `cosineCoeffSeries_deriv_at_{zero,one}`). **Key reclassification (T5_DESIGN §7.4):** T6's atom IS §7.3's "honest route B1" → the analytic core **[D1] is DONE**; the wall refines to **[D2] = the coupled fixed-point/source-bootstrap circularity** (construct (u,v); prove the source `−χ∇·(u∇v/(1+v)^β)+u(a−bu^α)` is `DuhamelSourceTimeC1` — Banach/Picard + parabolic Schauder, Mathlib-absent). **[C]** = time conjuncts (4)(5)(8)(9), joint Weierstrass-M, also gated on the representation. Build green 8379, axiom-clean. |
| T7e | **existence (`hlocal`) via weak-mild fixed point → post-hoc regularity** (breaks the circularity, avoids parabolic Schauder) | **Atom C DONE; architecture mapped; atoms B/D + divergence-form operator remain** | T6, T7[A][B] | **2026-05-30 route (ChatGPT+Xiang).** 3-layer: `IntervalMildSolution` (weak Duhamel eq, no 9-conjunct) → `IntervalMildRegularity` (T6/T7 source C¹/cosine/positivity) → `toClassical`. **Existing scaffold found** (`IntervalDomainExistence.lean`, ~6.6k lines): `intervalCoupledDuhamelOperator`, closed-ball Banach extraction `intervalCoupledDuhamel_fixed_point_exists_on_closed_ball`, and the reduction `localExistence_of_coupledDuhamel_resolver_estimates_and_regularization` — reduces `hlocal` to `IntervalCoupledResolverBallEstimates` (hmap/hchem/hint/hlift_int) + `hL_lip` (logistic Lipschitz) + `hregularize` (RegularityBootstrap=T6/T7). **`IntervalCoupledBallEstimates.lean`** further reduces all 4 conjuncts to a named C¹-flux Lipschitz hypothesis. **CRITICAL: existing scaffold uses the DIVERGENCE form `intervalDomainChemotaxisDiv` in the source** ⇒ hmap/hchem need `chemDiv` sup/Lipschitz-bounded (the over-strong 坑#2). The route's fix = **divergence-form mild map** (put ∂ₓ on `S(t−s)`, integrate the C⁰ flux against `∂ₓS`, use T1 `intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t` to absorb `(t−s)^{−1/2}`) ⇒ needs a NEW gradient-Duhamel operator (atom D, multi-session). **Atom C DONE** (`IntervalLogisticLipschitz.lean`): `intervalLogisticReaction_lipschitz_on_bounded` — `hL_lip` slot, `L=p.a+p.b(1+α)M^α+1`, MVT, requires explicit `1≤p.α`. **Atom B DONE** (`ShenWork/Paper2/IntervalResolverWeakBounds.lean`, axiom-clean): the resolver C⁰→C¹ bundle for an ARBITRARY bounded continuous ball element (no `hsol`). The existing quantitative bounds (`resolverValue_sup_le_of_ub` etc.) all take `hsol` (post-hoc) — unusable in the weak fixed point. Rebuilt from weak hypotheses: **B1** `resolverSourceCoeff_re_sq_summable_of_continuousOn` (source ℓ² from CONTINUITY alone, cosine-Bessel); **B2** `resolver_{cosine,sine}Series_summable_of_sourceL2` (resolver series abs-summable from â∈ℓ² ALONE via AM-GM against the ℓ² resolvent weight — the circularity-breaker: post-hoc needed `SourceCoeffQuadraticDecay`=solution C², but ℓ² Bessel suffices); **B3** `resolver{Value,Grad}_sup_le_of_bounded` (‖Eu‖∞,‖∂ₓEu‖∞ ≤ C·M^γ via `_sup_lipschitz` vs zero source + weak mass bound `source_coeffL2Norm_le_of_bounded`); **B4** `resolver{Value,Grad}_diff_sup_le_of_bounded` (‖Eu₁−Eu₂‖∞,‖∂ₓ(Eu₁)−∂ₓ(Eu₂)‖∞ ≤ C·2νγM^{γ-1}·D via the continuity-based Bessel-on-difference core `sourceCoeff_diff_energy_le_integral_of_continuousOn` + `rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma`, γ≥1); **B5 Neumann** = existing unconditional `resolverGradReal_zero`/`resolverGradReal_one` (every sine term vanishes at 0,1). **Atom C-flux** (Q(u)=u·∂ₓ(Eu)/(1+Eu)^β Lipschitz+bounded, depends on B), **Atom D** (weak/grad Duhamel √T estimate), **Atom A** (weighted path space completeness) remain. Build green 8381, axiom-clean. **STATE NOTE 2026-05-31:** the purported overnight skeletons (atoms A/D/E/F, `IntervalMildSolution`, commit `c947ba3`) do NOT exist in this repo — `HEAD = origin/main = ec8740a`, only B/C are done; `c947ba3` is not a valid object. **Newly mapped sub-obstructions (route to ChatGPT — these are architecture, not tactic):** **(O1) resolver positivity** `R(u) ≥ 0` for `u ≥ 0` is needed both for Atom C-flux's denominator `(1+Eu)^β ≥ 1` AND for the `hv_nonneg` conjunct. It is NOT reachable via the elliptic max principle for weak ball elements: `intervalNeumannResolverRLap_elliptic_identity` + the resolver's `C²`/`R''` structure all require `SourceCoeffQuadraticDecay` (O(1/k²) = source `C²`), which a weak ℓ²-only element lacks (the `R''` series `∑ âₖ(kπ)²/(μ+λₖ)cos` has terms `~|âₖ|`, only `o(1)`, non-summable). The positivity-preserving route is the semigroup-integral rep `R(u)=∫₀^∞ e^{−μt}S(t)(νu^γ)dt ≥ 0` (heat positivity `heatKernel ≥ 0` EXISTS; the rep `R=∫e^{−μt}S(t)` does NOT — needs the spectral Laplace identity `1/(μ+λₖ)=∫₀^∞e^{−(μ+λₖ)t}dt` + ∑∫ interchange). **(O2)** weak elements are `C¹` not `C²` (same ℓ²-vs-O(1/k²) gap) — the `C²` only re-appears post-fixed-point in the bootstrap (Atom G/H), consistent with the route's design. **Next buildable, positivity-free:** Atom D (linear grad-Duhamel √T, reuses T1 `..._deriv_Linfty_pointwise_sqrt_t`; T2 has `intervalFullCoupledDuhamel_grad_integral_bound_of_leibniz` conditional on a Leibniz interchange). **Atom D — sup bounds DONE 2026-05-31** (`ShenWork/PDE/IntervalGradDuhamelBound.lean`, axiom-clean): **`integral_sub_rpow_neg_half`** `∫₀ᵗ(t−s)^{−1/2}ds = 2√t` (substitute + `integral_rpow`); **`gradDuhamel_sup_bound`** `|∫₀ᵗ ∂ₓS(t−s)q ds| ≤ Cgrad·2√T·Cq` — **divergence form, ∂ₓ INSIDE S so NO Leibniz needed** (key vs T2's gated gradient-of-value form); singular per-slice gradient (T1) absorbed by the √-integral, via `abs_integral_le_integral_abs` + a.e. domination on `[0,t]` ({t} null) + `integral_mono_ae_restrict`; **`valueDuhamel_sup_bound`** `|∫₀ᵗ S(t−s)r ds| ≤ T·Cr` (semigroup L∞-contraction × length). The gradient-field/value-field interval-integrability is a named regularity prerequisite (continuity-derivable; à la T2's `hGrad_int`), NOT the conclusion. **Atom D difference Lipschitz DONE** (same file): `intervalFullSemigroupOperator_sub` (S(τ)(f−g)=S(τ)f−S(τ)g via `integral_sub`) + `valueDuhamel_diff_sup_bound` (`|∫(S(t−s)r₁−S(t−s)r₂)|≤T·D`); `intervalFullSemigroupOperator_deriv_sub` (∂ₓ linearity via `deriv_sub`) + `gradDuhamel_diff_sup_bound` (`|∫(∂ₓS(t−s)q₁−∂ₓS(t−s)q₂)|≤Cgrad·2√T·D`) — linearity rewrites difference-of-two-Duhamels to Duhamel-of-difference (`integral_congr`/`integral_congr_ae`, {t} null) then the sup bound on `r₁−r₂`/`q₁−q₂`. **Atom D COMPLETE** (sup + diff, value + gradient; positivity-free, linear, axiom-clean). Per-slice kernel-integrability / spatial-differentiability are honest named prerequisites (continuity-derivable). **Remaining for the route:** continuity ⟹ integrability (discharge the prerequisites from joint mild-path continuity); then **Atom E** (contraction K<1 from B/C/D constants, small T s.t. `T·LR+√T·|χ₀|·C·LQ<1`) — but E depends on **Atom C-flux** (Q=u·∂ₓR/(1+R)^β Lipschitz), whose denominator `(1+R)^β≥1` needs **O1** (R≥0); so **E is blocked on O1** (awaiting ChatGPT). Then **F/G/H**. **O1 STARTED 2026-05-31** (`ShenWork/PDE/IntervalResolverPositivity.lean`): **O1a `intervalFullSemigroupOperator_nonneg`** (S(t)f≥0 for f≥0, from full kernel nonneg + integral_nonneg). **ROUTE CORRECTION (route to ChatGPT):** ChatGPT's O1 sketch used the zeroth-reflection `intervalSemigroupOperator`, but that two-term kernel is only a small-`t` TRUNCATION (see `IntervalSemigroupSpectralForm` header) — it does NOT have the cosine spectral form `∑e^{−tλₖ}âₖcos`, so its per-mode Laplace coeffs would NOT match the resolver `âₖ/(μ+λₖ)`. **Correct operator = the FULL Neumann propagator `intervalFullSemigroupOperator`** (has BOTH nonneg AND `intervalFullSemigroupOperator_eq_cosineHeatValue`). **O1b DONE 2026-05-31** (same file): `unitIntervalCosineHeatValue_nonneg_of_continuous` — `0≤` heat value of a nonneg continuous source on `(0,1)`, transporting O1a's kernel positivity across the spectral identity. **Plus a repo-wide unblock:** `intervalNeumannFullKernel_cosineKernel_identity` **discharges `hkernel` UNCONDITIONALLY for `t>0`** (previously carried as a hypothesis everywhere) — the three summabilities all from `t>0`: `latticeGaussianSummable`×2 + `summable_spectral_exp_cos`×2, where `summable_spectral_exp` (`∑ₘe^{−t(mπ)²}<∞`) is `latticeExpSummable` at `z=0,s=1/(tπ²)`. No `SourceCoeffQuadraticDecay`/C² used. **O1c step 1 DONE 2026-05-31** (same file): `integral_exp_neg_mul` (`∫₀ᵀe^{−aτ}dτ=(1−e^{−aT})/a`, FTC) + `laplaceTruncation μ T f x := ∫₀ᵀ e^{−μt}S(t)f x dt` (on the FULL propagator) + `laplaceTruncation_nonneg` (`R_T≥0` for `f≥0`, via O1a + `integral_nonneg_of_ae_restrict`, `{0}` null). **O1c step 2 foundation DONE** (same file): `summable_abs_sourceCoeff_mul_weight` (`∑ₙ|âₙ|/(μ+λₙ)<∞` from â∈ℓ²×weight∈ℓ² via AM-GM — the dominating series for both Fubini and the limit). **O1c step 2 (remaining assembly)** Laplace spectral form `R_T x=∑ₖ((1−e^{−(μ+λₖ)T})/(μ+λₖ))âₖcos`: bridge `R_T(operator)=∫₀ᵀe^{−μt}·heatvalue` (via `eq_cosineHeatValue` under the integral, continuous-rep `f=ν·(u∘clamp01)^γ`, x∈(0,1)); pull `e^{−μt}` into the heat-value tsum (`tsum_mul_left`); Fubini swap `∫₀ᵀ↔∑` via `MeasureTheory.integral_tsum` (per-mode meas. + `∑ₙ∫₀ᵀ|Fₙ|≤∑|âₙ|/(μ+λₙ)<∞` from the foundation); per-mode `∫₀ᵀ=integral_exp_neg_mul`. **O1 CORE DONE 2026-05-31** — the full heat-Laplace positivity argument is proven (`IntervalResolverPositivity.lean`, axiom-clean): **O1c step2** `laplaceResolverTrunc_eq_tsum` (Fubini spectral form via `integral_tsum_of_summable_integral_norm` + ℓ¹ majorant + per-mode `integral_laplaceMode`); **O1c nonneg** `laplaceHeatTrunc_nonneg` (via O1b); **O1d** `laplaceHeatTrunc_tendsto` (`∫₀ᵀe^{−μt}heatvalue → ∑ₖâₖcos/(μ+λₖ)` by the uniform squeeze `‖trunc−target‖≤e^{−μT}M`, `squeeze_zero_norm'`); **O1 capstone** `intervalNeumannResolverR_nonneg_interior` — `0≤R(u)x` for `x∈(0,1)`, via reconstruction `R(u)x=∑ₖâₖcos/(μ+λₖ)` (`resolverCoeff_re_eq`+eigenvalue bridge) = the T→∞ limit of nonneg truncations + closed cone `IsClosed.mem_of_tendsto Ici`. NO `SourceCoeffQuadraticDecay`/C²/R''; `â∈ℓ²` is an honest Bessel input. **O1 FULLY CLOSED 2026-05-31** — `intervalNeumannResolverR_nonneg_of_nonneg_source`: `0≤R(u)x` for ALL `x∈[0,1]`. The closed-domain extension: `x↦R(u)x` is a cosine series with ℓ¹ coeffs (`|R̂ₖ|=|âₖ|·weightₖ`), hence continuous (`continuous_tsum` Weierstrass-M); `{x|0≤R(u)x}` is closed (`isClosed_le`), contains the interior `(0,1)`, so contains `closure(Ioo 0 1)=Icc 0 1`. Honest hypotheses: continuous nonneg rep `f` with `cosineCoeffs f=â` (`â∈ℓ²` Bessel). **glue1 foundation DONE** (`IntervalChemFluxLipschitz.lean`): `oneAddRpow_neg_lipschitz` — `(1+r)^{−β}` is `β`-Lipschitz on `[0,∞)` (`|f'|=β(1+r)^{−β−1}≤β`, MVT; `R≥0`⟹base≥1). **glue1 value core DONE** `chemFluxValue_lipschitz`: `|a₁g₁(1+v₁)^{−β}−a₂g₂(1+v₂)^{−β}| ≤ (B_G+M·L_G+M·B_G·β·L_R)·d` — telescoping `a₁g₁w₁−a₂g₂w₂=(a₁−a₂)g₁w₁+a₂(g₁−g₂)w₁+a₂g₂(w₁−w₂)` combining mass/grad bounds + `oneAddRpow_neg_lipschitz` (`0≤(1+v)^{−β}≤1`, `R≥0`). **glue1 DONE** `chemFlux_div_lipschitz`: `|a₁g₁/(1+v₁)^β−a₂g₂/(1+v₂)^β| ≤ (B_G+M·L_G+M·B_G·β·L_R)·d` (the actual flux quotient form via rpow_neg + the value core) — the interface Atom E consumes (caller feeds the pointwise resolver bounds from Atom B + O1). **ALL analytic cores now done: Atom B/C/D + O1 + glue1.** **Remaining = ASSEMBLY phase (needs the divergence-form operator defined — architecture, route to ChatGPT):** **glue2 contraction core DONE** (`IntervalChemFluxLipschitz.lean`): `exists_small_contraction_time` (`∀A,B≥0,∃T>0, A√T+B·T<1`, explicit `T=1/(A+B+1)²` — the 取 T 小 step) + `gradientDuhamel_contraction_pointwise` (`|−χ₀G+V| ≤ (2|χ₀|C·C_Q·√T+C_L·T)·d` combining Atom D's two diff bounds + glue1 `C_Q` + Atom C `C_L`). **Remaining = the operator-assembly phase (architecture, route to ChatGPT):** **Φ + predicate DEFINED** (`IntervalGradientDuhamelMap.lean`): `intervalGradientDuhamelMap` (`Φ = S(t)u₀ − χ₀∫∂ₓS(t−s)Q + ∫S(t−s)L`, S=`intervalFullSemigroupOperator`, Q=`chemFluxLifted`=lift w·resolverGradReal/(1+R)^β, L=`logisticLifted`) + **`IntervalMildSolution`** (the genuine weak-Duhamel fixed-point equation `∀t∈(0,T],∀x, u t x=Φ(u₀,u) t x` — a real proposition, not a shell). **Remaining = the fixed-point assembly (architecture, route to ChatGPT):** (i) the **weighted complete mild metric space** (`MetricSpace`+`IsComplete`/`CompleteSpace` on trajectories `[0,T]×Ī→ℝ`, weighted to control `u(t)−S(t)u₀` at `t→0⁺` since `u₀` need not be continuous) + Atom A; glue2 — `intervalGradientDuhamel_contraction_from_flux_lipschitz` (contraction `2|χ₀|C·C_Q·√T+C_L·T<1` from Atom D `∂ₓS` √T + glue1 + Atom C logistic); then E/F (Banach→IntervalMildSolution) / G/H. Build green 8384, axiom-clean. |
| T8 | Paper2 Theorem 1.1 (γ≥1): discharge the 2 remaining textbook PDE inputs (`localExistence` + `uniformLocal` parabolic continuation) | **Gluing/uniqueness HALF PROVEN (axiom-clean); only EXISTENCE remains** | — | **Confirmed 2026-05-30:** `GlobalSolutionGluingFromReachability_of_regime_gammaGeOne` is axiom-clean — the entire gluing/uniqueness/global-from-reachability apparatus is PROVEN from regime (χ₀≤0,a,b>0)+γ≥1+positivity pass-through (the `Kunif` chain is fully discharged: `uniformLiftBoundZeroM_of_regime`→`gronwall_const_of_uniformLiftBoundZeroM`→`boundednessHypothesis_of_uniformSupBoundZeroM`). **Sole remaining frontier = EXISTENCE** (`localExistence` + `IntervalDomainUniformLocalExistence`), i.e. construct a classical solution with the 9-conjunct regularity. Its core is conjunct-7 (D_t∈C²), a genuine deep wall (see T5_DESIGN §7: `DuhamelHeatValueRepresentation` is over-strong/false for a bounded source; honest route is direct ∂ₓₓD_t via heat-eq `∂ₓₓS=∂_rS`+time-IBP onto `∂_s g_s`, needing parabolic-regularity infra absent from Mathlib). |
| T9 | Paper1/2/3 statement-target bridge assembly | **Bridge phase DONE (2026-06-04)** | — | **Paper1:** `paper1_main_results` (construction+stability→Thm1.1∧1.2∧1.3); `Theorem_1_3.of_Theorem_1_2_cauchy_unique_resolvent_remark43` (sharpest Thm1.2→1.3 bridge, Remark 4.3 internal); `Theorem_1_2_and_1_3.of_stability_cauchy_unique_resolvent_remark43` (combined Thm1.2∧1.3 from per-instance stability); `Theorem_1_3.of_Theorem_1_2_cauchy_unique_resolvent_closeness` (abstract closeness variant); `Theorem_1_3_reflexive_branch`; `Lemma_5_1.of_resolvent_derivative_bounds` (universal closure); `Proposition_1_1.of_global_existence_and_bounds` / `Proposition_1_2.of_global_existence_and_convergence` (separate existence from estimates). **Paper2:** `unitPointDomain.paper2_main_results_from_logistic_nonminimal` (combined Thm1.1∧1.2∧1.3 from logistic ODE). **Paper3:** `unitPointDomain.Theorem_2_1_minimal_chi_nonpos` (non-vacuous Part 1 + vacuous 2-4, a=b=0,χ₀≤0); `unitPointDomain.Theorem_2_1_minimal_beta_lt_one` / `_m_ne_one`; `unitPointDomain.paper3_partial_results_minimal_chi_nonpos` (Thm2.1∧2.4∧2.5). Analytical frontiers (Cauchy uniqueness, resolvent ID, PDE existence) unchanged — these are T7e/T8 gates. |
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

## ★★ T7e DEEPEST-BUNDLE ATOM INVENTORY (2026-06-22, two-source converged: cron1 fdd4cc66 + cron2 8da1dfe2, both read 0a74b0c, both verdict OK, file-cited; key claims verified against tree)
Distance to χ₀<0 Theorem_1_1 = this FINITE named atom set (not a time estimate). The Hσ coefficient
bootstrap engine + mixed Wiener product is CLEAN (cron2: no hidden commutator/interpolation/maximal-
regularity gap). The deepest bundle is genuine PDE production, NOT Lean wiring (both crons converge).

GENUINE HARD ATOMS (real PDE theorems — the per-datum classical local existence frontier):
 H1. semigroup_weak  — weak Neumann Duhamel differentiation identity (TruncatedMildSemigroupWeakAfter
     BNDualityOn, IntervalBFormCron2MildToWeak.lean:97). CENTRAL: both crons name it — feeds DT-side
     mild→weak AND Henergy negative-part. Needs t^{-1/2} Neumann gradient smoothing + endpoint Lebesgue-
     point + DCT dominators + 3 tested weak identities (NegativePartStandardHeatSemigroupDuhamelFacts,
     IntervalBFormCron2SemigroupWeakDuhamel.lean:160). VERIFIED both structs exist in tree.
 H2. DT  — truncated Picard operator estimates (TruncatedConjugateMildExistenceData, IntervalBFormCron2
     TruncatedPicard.lean:346): maps-to / contraction / continuity+measurability preservation + base one-
     step. Consumed by truncatedConjugateMildSolutionData_of_data:472 (VERIFIED consumes-not-produces).
     Needs truncatedConjugateDuhamelMap_{mapsTo,contracts}_ball + 2 preservation lemmas.
 H3. hF1  — quantitative local classical existence: ∀M>0 ∃δ(M)>0, PID(u₀)∧‖u₀‖∞≤M ⇒ classical (u,v) on
     [0,δ(M)]; + RestartAndGlueWorks + interior sup-norm preservation. (IntervalDomainUniformContinuation/
     RestartExtension/GlueLargeCase — δ(M)-extraction from the Picard contraction is the open core.)
 H4. A,Dbar + drift/react/hstrip  — pointwise L∞ drift/reaction bounds (|B|≤A, -C≤Dbar) on every restarted
     strip + classical supersolution structure. NOT Hσ summability (cron2). Consumer bform_strictPos_closed
     is wired; producer is the gap.
 H5. Henergy  — negative-part weak energy producer (NegativePartEnergyCoreData): weak -u_- test + nonsmooth
     chain rules + energy differentiability + initial trace + zero-L²→pointwise upgrade. CONSUMES H1.
     Gronwall-to-zero consumer already wired.

WIRING (assembled or trivial — do NOT bank as new math, §2.6):
 Hbridge (truncatedConjugateLimitBridgeProducerData_of_cores + _of_faithful_truncation — VERIFIED already
   used together in IntervalBFormPositiveDatumLocalExistenceSqRegular.lean:92,99), Test (pick bounded-
   measurable class, not all-tests), bN_fubini_integrable, bN_semigroup_deriv, M:=max 0 (A²/2+Dbar).

NET: χ₀<0 completion = discharge {H1..H5}. H1 is the keystone (two consumers). These are paper-level PDE
theorems (quantitative local existence + negative-part weak energy for a chemotaxis system), genuine multi-
session formalization — the OUTSTANDING T7e/T6 "operator-assembly/fixed-point not done", now named & grounded.

## ★ H1 KEYSTONE DECOMPOSITION (2026-06-22, cron1 f0944027 + cron2 b2019e97, both grounded on 2ced46e, key anchors tree-verified)
H1 = semigroup_weak bottoms out at NegativePartStandardHeatSemigroupDuhamelFacts fields (IntervalBFormCron2
SemigroupWeakDuhamel.lean), all carried satisfiably, consumer chain wired (negativePartMildSemigroupWeak...
_of_standardHeatSemigroupDuhamelFacts:218). The genuine self-lemma gaps, by leg:
 H1-grad ★ NeumannHeatGradientTMinusHalfBound (:91) — L²→L² gradient smoothing ‖∂ₓS_N(τ)f‖₂≤Cτ^{-1/2}‖f‖₂.
   MOST LEVERAGED (DCT dominator for BOTH legs built from it) + MOST SELF-CONTAINED. Tree has only the
   L∞→L∞ pointwise version (intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t); the L² one is a
   gap. Proof = spectral/Bessel: cosine modes → sine deriv → λe^{-2τλ}≤C/τ (x e^{-x}≤e^{-1}) → cosine
   Bessel/Parseval. MIRROR resolverSourceCoeff_re_sq_summable_of_continuousOn (IntervalResolverWeakBounds).
   → DISPATCHED to codex (uisai2), unbounded grind.
 H1-hom  semigroup_form_identity — homogeneous heat weak-generator identity =0. Landed nearby: heat identity
   unitIntervalCosineHeatValue_heat_identity, spatial IBP intervalDomain_spatial_integrationByParts_identity
   (needs generalizing from test=f to arbitrary φ). Mathlib: integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right.
 H1-src  source_duhamel_differentiation — ordinary L² Duhamel weak differentiation. Landed nearby: time-IBP/
   cutoff route in IntervalDuhamelClosedC2 (duhamelIntegrand_hasDerivAt, duhamelCutoff_FTC). Mathlib:
   integral_hasDerivAt_right + tendsto_integral_filter_of_dominated_convergence.
 H1-chem source_endpoint+dct (chemotaxis divergence leg, cron2): ChemotaxisDuhamelEndpointLebesguePointFact
   (:117) + DCTDominatingFunction (:146). B_N duality gives positive-lag only; endpoint limit is the gap.
   Mathlib supplies general DCT (tendsto_integral_filter_of_dominated_convergence) + Vitali (ae_tendsto_
   average, a.e.-only → needs right-interval fixed-t specialization). All consume H1-grad's t^{-1/2} bound.
NET: H1 = {t^{-1/2} L² bound [codex now]} + {3 weak-identity producers, each with landed-nearby machinery +
named Mathlib FTC/DCT/IBP cores}. The t^{-1/2} bound is the shared foundation. Genuine analysis, not wiring.

## ★ H2 (DT) REFINEMENT — DOWNGRADE (2026-06-22, cron1 Q320 3ff7f8a1, field-by-field, all 6 cited full-map lemmas tree-VERIFIED)
Q316 headline said "DT hard". The field-by-field probe REFINES this: DT is NOT a genuine hard PDE atom like
H1 semigroup_weak — it is MIRROR-ASSEMBLY of the landed FULL-map Picard core onto truncated sources. The
full-map (untruncated) versions of all 5 operator estimates are LANDED + reusable (VERIFIED):
 · maps-to:        hPhiB_le inside conjugateMildExistenceCore_exists (IntervalConjugatePicardCoreInhabit)
 · contraction:    ConjugateMildExistenceCore.contraction_from_banked + intervalConjugateDuhamelMap_diff_
                   bound_of_banked (IntervalConjugatePicardCoreInhabit / ...CoreDischarge)
 · continuity:     intervalConjugateDuhamelMap_hasContinuousSlices_of_ball (...CoreInhabit)
 · measurability:  intervalConjugateDuhamelMap_hasJointMeasurability_of_ball (...CoreInhabit)
 · small-time K<1: exists_small_contraction_time_target (Wiener/EWA/SourceFixedPointClean) — K(T)=O(√T)+O(T)<1
DT effort, per field: base-one-step = PURE WIRING; continuity+measurability = SHORT source-wrapper adapts
(need truncatedChemFluxLifted_uncurry_measurable + truncatedLogisticLifted_uncurry_measurable); maps-to +
contraction = SHORT-TO-MEDIUM assembly once truncated flux/logistic pointwise-bound + Lipschitz wrappers
added. K<1 = standard short-time Picard (shrink T), NOT weighted norm. cron1 gave the 6 target def shapes
(truncatedConjugateDuhamelMap_{mapsTo,contracts}_ball etc.) mirroring each landed full-map lemma.
NET REVISION: H2 is MEDIUM mirror-assembly, not a hard analytic frontier. The genuine hard analysis is
concentrated in H1 (semigroup_weak: t^{-1/2} L² + 3 weak-identity producers) + H5 (Henergy, consumes H1) +
H3/H4. This is the test-don't-assert payoff: probing the "DT hard" headline showed it's mirror-work off a
landed core, not new PDE. Honest downgrade.

## ★★ §3.3 AUDIT CATCH #3 — H1-grad def was FALSE as stated (2026-06-22, opus producer, refutation formalized axiom-clean + ChatGPT cross-checked, def tree-verified)
NeumannHeatGradientTMinusHalfBound (IntervalBFormCron2SemigroupWeakDuhamel.lean:91), labeled "SATISFIABLE"
in its own comment, was MATHEMATICALLY FALSE as literally stated: it quantified `∀ f : ℝ → ℝ` with NO L²
hypothesis. Counterexample (opus, formalized as 2 axiom-clean lemmas rhs_eq_zero_of_sq_not_integrable +
gradient_L2_forced_zero_of_bound): for f∈L¹∖L² (e.g. x^{-2/3}), Mathlib integral_undef collapses RHS mass
√(∫f² ∂μ)=0, but S_N(τ)f is a genuine heat image with nonzero n=1 mode so LHS gradient-L² >0 → LHS≤0 false.
The opus producer correctly REFUSED to fake a proof (no sorry/axiom), formalized the refutation, cross-
checked via ChatGPT. THIRD FALSE carried field this campaign (after source-bridge closed-hderiv + bank
hchemCont constExtend) — `#print axioms` cannot detect a false-as-stated carried Prop; only attempting it does.
FIX (landed, same FALSE→satisfiable pattern as the prior two): added `MemLp f 2 (intervalMeasure 1)` to the
def. The only reference is the carried field gradient_tminus_half:163 (never applied concretely), so the fix
is localized + safe; the L²-restricted form is TRUE + provable. Downstream consumers apply it to flux slices
which are bounded/continuous on [0,1] hence L² (witness available).
REMAINING for H1-grad (now provable): the conditional spectral proof. Repo has most of the chain
(unitIntervalCosineHeatGradientTsumEnergy_le, unitIntervalCosineHeatValue_deriv_of_l2, unitIntervalNeumann
CosineCoeff_l2_bound); the ONE genuinely-missing analytic input = spatial sine-Parseval ∫₀¹(Σbₙsin nπx)²=
½Σbₙ² (no output-direction Parseval for this operator in repo; Mathlib has no packaged fourierCoeffOn/tsum
interchange — build from tsum_sq_fourierCoeffOn on the odd reflection). That is the real next brick.
LESSON: a comment labeling a carried field "SATISFIABLE" is an ASSERTION, not a proof — test it. The audit
caught it exactly because the producer ATTEMPTED the proof instead of trusting the label.

## ★★★ STRUCTURAL INFLECTION — §3.3 FINGERPRINT (2026-06-22, 4th false field; STOP field-grind, AUDIT)
H1-hom semigroup_form_identity (IntervalBFormCron2SemigroupWeakDuhamel.lean:191) is the FOURTH false-as-
stated field this campaign (opus aebef98c, counterexample formalized axiom-clean, ChatGPT cross-checked):
false for arbitrary u because test φ=-u_-(t) can be a spatial KINK (classical deriv=0 a.e. → spatial
Dirichlet term collapses, fails to cancel nonzero time term). Counterexample: u₀=cos(πp), u(·,p)=-1 for
p≤1/2 else 0, t=1/2 → contribution = π·e^{-π²/2} ≠ 0. Needs φ=-u_-(t) ∈ H¹.
PATTERN (4 false fields, all same shape): source-bridge(closed-hderiv), bank-hchemCont(constExtend),
H1-grad(∀f no L²), H1-hom(∀u no H¹). The structure NegativePartStandardHeatSemigroupDuhamelFacts (:168) +
the deepest bundle PositiveDatumBFormSqDeepestHypotheses (IntervalBFormPositiveDatumLocalExistenceSqDeepest
.lean:35) carry the weak-identity facts as ASSUMED hypotheses with ZERO regularity assumption on
u=conjugatePicardLimit (a MILD solution). That under-hypothesis is exactly why the fields are false-as-stated.
THE STRUCTURAL QUESTION (§3.3 vacuity/satisfiability — must answer before fixing field-by-field):
 Is u=conjugatePicardLimit's spatial H¹ regularity (for t>0, via parabolic smoothing / the built H^σ
 bootstrap engine) GENUINELY AVAILABLE to discharge all 4 fields' regularity hypotheses — making the bundle
 sound with a single u-regularity input — OR is that regularity CIRCULAR with what local existence (hF1/H3)
 is supposed to produce, making the carried hypotheses unsatisfiable (vacuous bundle)?
 · If available (parabolic smoothing is a genuine separate input): fix = add ONE u-regularity field to the
   bundle (u t ∈ H¹ for t∈(0,T]), discharged by the bootstrap; all 4 weak-identity fields then become true.
   This RE-ELEVATES the H^σ bootstrap from "off critical path" to the discharging foundation. NON-circular.
 · If circular: the carried-hypothesis design is broken; needs redesign, not hypothesis-patching.
NOTE: H1-grad's MemLp fix (268754f) is clean/non-circular REGARDLESS (flux slices trivially L²); that fix
stands. The circularity risk is specifically the u-regularity (H¹) the SOLUTION-tested fields need.
ACTION: structural audit dispatched (does parabolic smoothing of the mild solution give u t∈H¹ for t>0
independently, or is it circular with hF1?). DO NOT patch H1-hom/src/chem field-by-field until answered.

## ★★★ STRUCTURAL VERDICT — GREEN: bundle SOUND, frontier CONSOLIDATES (2026-06-22, struct audit git-drop 7b1e544, all 7 anchors tree-verified)
VERDICT (option i): bundle is UNDER-HYPOTHESIZED, NOT vacuous. Do NOT redesign. Fix = add ONE bundle-level
positive-time H¹ field for u=conjugatePicardLimit, discharged by mild-solution parabolic smoothing (H^σ
bootstrap), NOT from localClassicalSolution. NON-CIRCULAR: dependency order is mild fixed point → bounded+
nonneg+continuous slices → H⁰=L² seed → positive-time H¹ smoothing → φ=-u_-(t) admissible H¹ test → weak
identity fields → localClassicalSolution (strictly upstream, no cycle). Only MemHSigma 1 needed (not ContDiffOn 2).
This RE-ELEVATES the H^σ bootstrap from "off critical path" to the discharging foundation (corrects the
earlier triple-confirmed "bootstrap off critical path" verdict — that was about ContDiffOn 2; MemHSigma 1 for
the weak-test admissibility IS on the path).

CONSOLIDATION (the big simplification): the 4 false weak-identity fields all reduce to ONE missing regularity
field + a NegativePartTestAdmissibleH1 predicate consumed by each. Two pieces now:
 A. STRUCTURAL (medium wiring): add field `u_posTime_memHSigma_one : ∀ t, 0<t→t≤DB.T → MemHSigma 1
    (cosineCoeffs (intervalDomainLift ((conjugatePicardLimit p u₀ DB.T) t)))` to the bundle; derive
    NegativePartTestAdmissibleH1 (Lipschitz Sobolev chain rule for negativePart); wire the 4 weak-identity
    fields to consume it.
 B. ANALYTIC KEYSTONE: instantiate UniformBootstrapStep (IntervalEnvelopeProp.lean:179 / IntervalUniform
    Bootstrap.lean:179, carried uninstantiated by gradientSolution_contDiffOn_two_FINAL:193) — the per-level
    MemHSigma σ → σ+α gain. Producer chain (all anchors VERIFIED): memHSigma_zero_of_continuousOn (H⁰ seed,
    IntervalChiNegCloseBaseSeed) ∘ conjugatePicardLimit_hasContinuousSlices ∘ chemFluxLifted_sup_bound_of_ball
    (bounded flux) ∘ fluxSineEnvelope_uniform (τ-uniform envelope hg/hg_dom, IntervalMixedProduct) ∘
    duhamelEnergy_endpoint_uniform (parabolic gain). Uses ONLY DB mild data — independent of hF1. → DISPATCH.
H1-grad (t^{-1/2}) still needed separately for the chemotaxis/source DCT dominators; opus a761b2f9 grinding it.
NET FRONTIER NOW: {B: UniformBootstrapStep instantiation [new keystone]} + {A: H¹-field structural wiring} +
{H1-grad t^{-1/2} [in flight]} + {H3 hF1 / H4 strip — still genuine but now the H¹ they implicitly needed is
the bootstrap field}. The 4 false fields are no longer 4 separate hard producers — they share ONE discharge.

## ★★ KEYSTONE B PRECISELY LOCATED (2026-06-22, boot opus a45e9570 — H1-grad ✅ landed b57f439, boot scaffold 8d4693e)
H1-grad ✅ DISCHARGED+VERIFIED (b57f439): NeumannHeatGradientTMinusHalfBound (L²-restricted, C=1), real
sine-Parseval (AddCircle.tsum_sq_fourierCoeffOn), cold-build 8414 green, axioms clean. First genuine hard
analytic atom closed this run.
Boot scaffold (8d4693e, CONDITIONAL): conjugatePicardLimit_slice_memHSigma_zero (H⁰ seed, UNCONDITIONAL,
non-circular) + memHSigma_antitone + the MemHSigma-1 ladder (carries UniformBootstrapStep, not discharged).
KEYSTONE B = instantiate UniformBootstrapStep α (slice) — the ONE shared blocker that discharges the H¹
field → admissibility → all of H1-hom/src/chem. Boot opus located it to two non-circular sub-bricks:
 B1: mild-only slice cosine decomposition hdecomp/conjugatePicardLimit_cosineSeries. The per-mode kernel
     identity EXISTS unconditionally (intervalConjugateKernelOperator_cosineSeries, IntervalConjugate
     CosineSeries.lean:246: cosineCoeffs(B_N(t)g)_n = e^{-tλ_n}√λ_n sineCoeffs(g)_n). Assembling the full
     slice series (conjugatePicardLimit_cosineSeries :507) needs DuhamelSourceTimeC1 + Duhamel-leg
     integrabilities + hsource_bridge VIA THE MILD ROUTE (currently only produced via downstream ContDiffOn
     2 Neumann: hchemFourier_slice_of_limit_C2Neumann / _PID_unconditional — must build the upstream variant).
 B2: σ-level flux envelope Mc∈H^σ needs v_x∈H^σ at running σ (fluxFunction_memHSigma). Elliptic gain: v
     solves -v''+v=u so v_x is one degree smoother than u → v_x∈H^σ from u∈H^{σ-1}. The bootstrap induction
     is well-founded from H⁰ (each step +α). No MemHSigma σ…of_bounded for σ>0 (L∞⇏H^{σ>0}) — must go
     through the per-level elliptic regularity, NOT a sup bound.
Both NON-circular (no localClassicalSolution). VERIFY-DON'T-ASSERT FLAG: the non-circularity is asserted by
the audit + boot opus; the producer must be built using ONLY mild data + the H^σ induction — if it secretly
needs C²/classical regularity, that IS the circularity, surface it. → DISPATCH one opus on B1+B2 (single
coherent core). codex returns Jun 26 for a 2nd thread.

## ★★ KEYSTONE B step BUILT mild-only — residual SHARPENED to ONE atom (2026-06-22, opus a6168b9a, verified 3608 green + axioms clean)
NON-CIRCULARITY CONFIRMED BY TEST: uniformBootstrapStep_of_sliceMildData : SliceMildStepData → Uniform
BootstrapStep α ut compiles importing ONLY IntervalBootstrapInputs + the scaffold (no localClassicalSolution
/C²-producer), axiom-clean. The structural audit "option i sound" is VINDICATED at the proof level.
B1+B2 SUPERSEDED: both already discharged mild-only in repo (B1 = gradientSolution_cosineCoeff_decomp_chi
IntervalBootstrapDecomp.lean:99; B2 = fluxSineEnvelope_uniform / IntervalEnvelopeProp).
THE ONE GENUINE RESIDUAL (sharpened): τ-uniform trajectory-H^σ flux envelope = SliceMildStepData.genv/glenv:
a per-σ sequence with hg: MemHSigma σ (genv σ) AND hg_dom: ∀τ∈[0,t]∀k |sineCoeffs(Q τ) k| ≤ genv σ k —
i.e. a single H^σ sequence dominating the flux sine-coeffs UNIFORMLY over the whole trajectory window [0,t],
not just the endpoint slice. Engine header: "no such uniform producer exists in Paper2." NON-circular (it's
the monotone H^σ induction propagated across [0,t] — a continuation/fixed-point closure, upstream of classical
existence). This is now THE single deepest analytic atom for χ₀<0 regularity.
OPEN QUESTION for the route: does the uniform-in-τ H^σ flux bound follow from the engine's ENDPOINT-uniform
per-mode bound (R(s)=s^{(1-α)/2}≤1, no Gronwall) + the uniform L∞ ball, OR need a full continuation/openness-
closedness argument? → dispatch opus (Lean) + ChatGPT git-drop (route) in parallel.
