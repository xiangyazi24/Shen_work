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
| T7e | **existence (`hlocal`) via weak-mild fixed point → post-hoc regularity** (breaks the circularity, avoids parabolic Schauder) | **Atom C DONE; architecture mapped; atoms B/D + divergence-form operator remain** | T6, T7[A][B] | **2026-05-30 route (ChatGPT+Xiang).** 3-layer: `IntervalMildSolution` (weak Duhamel eq, no 9-conjunct) → `IntervalMildRegularity` (T6/T7 source C¹/cosine/positivity) → `toClassical`. **Existing scaffold found** (`IntervalDomainExistence.lean`, ~6.6k lines): `intervalCoupledDuhamelOperator`, closed-ball Banach extraction `intervalCoupledDuhamel_fixed_point_exists_on_closed_ball`, and the reduction `localExistence_of_coupledDuhamel_resolver_estimates_and_regularization` — reduces `hlocal` to `IntervalCoupledResolverBallEstimates` (hmap/hchem/hint/hlift_int) + `hL_lip` (logistic Lipschitz) + `hregularize` (RegularityBootstrap=T6/T7). **`IntervalCoupledBallEstimates.lean`** further reduces all 4 conjuncts to a named C¹-flux Lipschitz hypothesis. **CRITICAL: existing scaffold uses the DIVERGENCE form `intervalDomainChemotaxisDiv` in the source** ⇒ hmap/hchem need `chemDiv` sup/Lipschitz-bounded (the over-strong 坑#2). The route's fix = **divergence-form mild map** (put ∂ₓ on `S(t−s)`, integrate the C⁰ flux against `∂ₓS`, use T1 `intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t` to absorb `(t−s)^{−1/2}`) ⇒ needs a NEW gradient-Duhamel operator (atom D, multi-session). **Atom C DONE** (`IntervalLogisticLipschitz.lean`): `intervalLogisticReaction_lipschitz_on_bounded` — `hL_lip` slot, `L=p.a+p.b(1+α)M^α+1`, MVT, requires explicit `1≤p.α`. **Atom B DONE** (`ShenWork/Paper2/IntervalResolverWeakBounds.lean`, axiom-clean): the resolver C⁰→C¹ bundle for an ARBITRARY bounded continuous ball element (no `hsol`). The existing quantitative bounds (`resolverValue_sup_le_of_ub` etc.) all take `hsol` (post-hoc) — unusable in the weak fixed point. Rebuilt from weak hypotheses: **B1** `resolverSourceCoeff_re_sq_summable_of_continuousOn` (source ℓ² from CONTINUITY alone, cosine-Bessel); **B2** `resolver_{cosine,sine}Series_summable_of_sourceL2` (resolver series abs-summable from â∈ℓ² ALONE via AM-GM against the ℓ² resolvent weight — the circularity-breaker: post-hoc needed `SourceCoeffQuadraticDecay`=solution C², but ℓ² Bessel suffices); **B3** `resolver{Value,Grad}_sup_le_of_bounded` (‖Eu‖∞,‖∂ₓEu‖∞ ≤ C·M^γ via `_sup_lipschitz` vs zero source + weak mass bound `source_coeffL2Norm_le_of_bounded`); **B4** `resolver{Value,Grad}_diff_sup_le_of_bounded` (‖Eu₁−Eu₂‖∞,‖∂ₓ(Eu₁)−∂ₓ(Eu₂)‖∞ ≤ C·2νγM^{γ-1}·D via the continuity-based Bessel-on-difference core `sourceCoeff_diff_energy_le_integral_of_continuousOn` + `rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma`, γ≥1); **B5 Neumann** = existing unconditional `resolverGradReal_zero`/`resolverGradReal_one` (every sine term vanishes at 0,1). **Atom C-flux** (Q(u)=u·∂ₓ(Eu)/(1+Eu)^β Lipschitz+bounded, depends on B), **Atom D** (weak/grad Duhamel √T estimate), **Atom A** (weighted path space completeness) remain. Build green 8381, axiom-clean. **STATE NOTE 2026-05-31:** the purported overnight skeletons (atoms A/D/E/F, `IntervalMildSolution`, commit `c947ba3`) do NOT exist in this repo — `HEAD = origin/main = ec8740a`, only B/C are done; `c947ba3` is not a valid object. **Newly mapped sub-obstructions (route to ChatGPT — these are architecture, not tactic):** **(O1) resolver positivity** `R(u) ≥ 0` for `u ≥ 0` is needed both for Atom C-flux's denominator `(1+Eu)^β ≥ 1` AND for the `hv_nonneg` conjunct. It is NOT reachable via the elliptic max principle for weak ball elements: `intervalNeumannResolverRLap_elliptic_identity` + the resolver's `C²`/`R''` structure all require `SourceCoeffQuadraticDecay` (O(1/k²) = source `C²`), which a weak ℓ²-only element lacks (the `R''` series `∑ âₖ(kπ)²/(μ+λₖ)cos` has terms `~|âₖ|`, only `o(1)`, non-summable). The positivity-preserving route is the semigroup-integral rep `R(u)=∫₀^∞ e^{−μt}S(t)(νu^γ)dt ≥ 0` (heat positivity `heatKernel ≥ 0` EXISTS; the rep `R=∫e^{−μt}S(t)` does NOT — needs the spectral Laplace identity `1/(μ+λₖ)=∫₀^∞e^{−(μ+λₖ)t}dt` + ∑∫ interchange). **(O2)** weak elements are `C¹` not `C²` (same ℓ²-vs-O(1/k²) gap) — the `C²` only re-appears post-fixed-point in the bootstrap (Atom G/H), consistent with the route's design. **Next buildable, positivity-free:** Atom D (linear grad-Duhamel √T, reuses T1 `..._deriv_Linfty_pointwise_sqrt_t`; T2 has `intervalFullCoupledDuhamel_grad_integral_bound_of_leibniz` conditional on a Leibniz interchange). **Atom D — sup bounds DONE 2026-05-31** (`ShenWork/PDE/IntervalGradDuhamelBound.lean`, axiom-clean): **`integral_sub_rpow_neg_half`** `∫₀ᵗ(t−s)^{−1/2}ds = 2√t` (substitute + `integral_rpow`); **`gradDuhamel_sup_bound`** `|∫₀ᵗ ∂ₓS(t−s)q ds| ≤ Cgrad·2√T·Cq` — **divergence form, ∂ₓ INSIDE S so NO Leibniz needed** (key vs T2's gated gradient-of-value form); singular per-slice gradient (T1) absorbed by the √-integral, via `abs_integral_le_integral_abs` + a.e. domination on `[0,t]` ({t} null) + `integral_mono_ae_restrict`; **`valueDuhamel_sup_bound`** `|∫₀ᵗ S(t−s)r ds| ≤ T·Cr` (semigroup L∞-contraction × length). The gradient-field/value-field interval-integrability is a named regularity prerequisite (continuity-derivable; à la T2's `hGrad_int`), NOT the conclusion. **Atom D difference Lipschitz DONE** (same file): `intervalFullSemigroupOperator_sub` (S(τ)(f−g)=S(τ)f−S(τ)g via `integral_sub`) + `valueDuhamel_diff_sup_bound` (`|∫(S(t−s)r₁−S(t−s)r₂)|≤T·D`); `intervalFullSemigroupOperator_deriv_sub` (∂ₓ linearity via `deriv_sub`) + `gradDuhamel_diff_sup_bound` (`|∫(∂ₓS(t−s)q₁−∂ₓS(t−s)q₂)|≤Cgrad·2√T·D`) — linearity rewrites difference-of-two-Duhamels to Duhamel-of-difference (`integral_congr`/`integral_congr_ae`, {t} null) then the sup bound on `r₁−r₂`/`q₁−q₂`. **Atom D COMPLETE** (sup + diff, value + gradient; positivity-free, linear, axiom-clean). Per-slice kernel-integrability / spatial-differentiability are honest named prerequisites (continuity-derivable). **Remaining for the route:** continuity ⟹ integrability (discharge the prerequisites from joint mild-path continuity); then **Atom E** (contraction K<1 from B/C/D constants, small T s.t. `T·LR+√T·|χ₀|·C·LQ<1`) — but E depends on **Atom C-flux** (Q=u·∂ₓR/(1+R)^β Lipschitz), whose denominator `(1+R)^β≥1` needs **O1** (R≥0); so **E is blocked on O1** (awaiting ChatGPT). Then **F/G/H**. **O1 STARTED 2026-05-31** (`ShenWork/PDE/IntervalResolverPositivity.lean`): **O1a `intervalFullSemigroupOperator_nonneg`** (S(t)f≥0 for f≥0, from full kernel nonneg + integral_nonneg). **ROUTE CORRECTION (route to ChatGPT):** ChatGPT's O1 sketch used the zeroth-reflection `intervalSemigroupOperator`, but that two-term kernel is only a small-`t` TRUNCATION (see `IntervalSemigroupSpectralForm` header) — it does NOT have the cosine spectral form `∑e^{−tλₖ}âₖcos`, so its per-mode Laplace coeffs would NOT match the resolver `âₖ/(μ+λₖ)`. **Correct operator = the FULL Neumann propagator `intervalFullSemigroupOperator`** (has BOTH nonneg AND `intervalFullSemigroupOperator_eq_cosineHeatValue`). **O1 remaining sub-steps:** **O1b** heat-value nonneg `0≤unitIntervalCosineHeatValue t (cosineCoeffs f) x` for `f≥0` cont, `x∈(0,1)` — via O1a + `eq_cosineHeatValue_unconditional`, but that needs `hkernel` (the pointwise kernel↔theta identity `K t x y=∑ₘθ`), which the repo carries as a HYPOTHESIS everywhere (NOT yet discharged from `t>0`); discharging it = Gaussian-lattice + cosine summability from `t>0` + `intervalNeumannFullKernel_eq_cosineKernel` (Poisson already proven). **O1c** Laplace truncation spectral form `R_T x=∫₀ᵀ e^{−μt}(heat value)dt = ∑ₖ((1−e^{−(μ+λₖ)T})/(μ+λₖ))âₖcos` (Fubini swap ∫₀ᵀ↔∑). **O1d** T→∞ limit (per-mode `→1/(μ+λₖ)`, dominated conv via ℓ²→L∞ bridge) + closed cone `Ici 0` ⟹ `R(u)≥0`. Internal helper `intervalNeumannResolverR_eq_laplaceSemigroup_limit`; do NOT expose generic `(μ−A)⁻¹`. Build green 8383, axiom-clean. |
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
