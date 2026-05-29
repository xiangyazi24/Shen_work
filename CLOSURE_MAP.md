# ShenWork Closure Map — precise remaining frontier (2026-05-26)

## ROUND-17 — full-kernel gradient L∞→L∞ estimate: diagnosis (2026-05-29)

Attacked the full-kernel gradient `L∞→L∞` estimate (the prerequisite for wiring
the full operator into the `_clean` chain).  Determination after mapping the
infrastructure and ruling out shortcuts — **this is a genuine multi-day
real-space theorem, no shortcut exists**:

WHAT IS NEEDED: `|deriv (intervalFullSemigroupOperator t f) x| ≤ C · t^(−1/2) · ‖f‖∞`
with the `t^(−1/2)` power (so the Duhamel envelope `∫₀ᵗ |∂ₓ S(t−s)F| ds` is
finite — `∫ (t−s)^(−1/2) ds = 2√t` converges; `∫ 1/(t−s) ds` DIVERGES).

SHORTCUTS RULED OUT (with reasons):
* **Spectral form is INSUFFICIENT.** Via the cosine identity the gradient is
  `∑ₙ exp(−t(nπ)²)·(−nπ sin(nπx))·aₙ`; each spatial derivative pulls a factor
  `nπ`, and `∑ₙ n e^(−tn²) ~ 1/t`, so the spectral sup bound is `C/t·‖f‖∞`
  (the proved `unitIntervalCosineHeatGradientValue_L2_Linfty_smoothing` is
  `Const/t`).  `1/(t−s)` is NON-integrable at `s=t` → useless for the envelope.
* **C²-compactness is INSUFFICIENT.** `intervalFullSemigroupOperator t f` is `C²`
  on `[0,1]` (`..._contDiff_two_unconditional`) so its derivative is bounded on
  the compact, but the bound is not uniform in `t` (blows up as `t→0⁺`) — again
  not the integrable `t^(−1/2)`.

THE ONLY ROUTE (real-space method-of-images tiling):
  `|deriv (S_full t f) x| ≤ ‖f‖∞ · ∫₀¹ |∂ₓ K_full(t,x,y)| dy`, and
  `∫₀¹ |∂ₓ K_full| dy = ∫₀¹ |∑ₖ (heat'(x−y+2k)+heat'(x+y+2k))| dy
     ≤ ∑ₖ ∫₀¹ (|heat'(x−y+2k)|+|heat'(x+y+2k)|) dy = ∫_ℝ |heat'(t,·)| = (1/√π)t^(−1/2)`,
  the last step being the TILING: the images `{x−y+2k}∪{x+y+2k}` (y∈[0,1], k∈ℤ)
  partition ℝ into unit cells.

FOUNDATIONAL PIECES IN PLACE:
* `heatKernel_deriv_abs_integral : ∫ |∂ₓ heat(t,·)| = 2/√(4πt) = (1/√π)t^(−1/2)`
  (HeatSemigroup.lean) — the L¹ gradient norm constant.
* `intervalSemigroupOperator_deriv_Linfty_pointwise_sqrt_t` — the zeroth-reflection
  analogue (`(1/√π)t^(−1/2)‖f‖∞`), the template.
* `tsum_int_eq_zero_add_two_mul_tsum_pnat` (IntervalFullKernelInterchange.lean) —
  the even-fold of the ℤ-lattice, reusable.

GENUINE REMAINING WORK (multi-step, best tackled with fresh context):
  (i) move `deriv` inside the lattice `tsum` (`hasDerivAt_tsum` + uniform
      Gaussian-gradient summability); (ii) the tiling identity
      `∑ₖ ∫₀¹ φ(·±y+2k) dy = ∫_ℝ φ` (via `integral_iUnion` over the cell
      partition + change of variables); (iii) assemble with the heat L¹ norm.

PROGRESS (file `ShenWork/PDE/IntervalFullKernelGradientTiling.lean`, small
independently-verified steps, all `#print axioms` = core three):
  * Step 1 `heatKernel_deriv_abs_integral_sqrt_form` — `∫_ℝ |∂ₓ heat(t,·)|`
    `= heatGradientLinftyLinftyConstant · t^(−1/2)` (the envelope-integrable
    power; restates the existing `= 2/√(4πt)`).
  * Step 2 `iUnion_Ioc_two_mul_eq_univ` + `pairwise_disjoint_Ioc_two_mul` — the
    period-`2` half-open cells `Ioc(2k)(2k+2)` partition `ℝ`.
  * Step 3 `integral_eq_tsum_integral_Ioc_two_mul` — `∫_ℝ G = ∑ₖ ∫_{cell} G`
    for integrable `G` (the tiling integral split, via `integral_iUnion`).
  REMAINING: Step 4 — move `deriv` inside the kernel's lattice `tsum`, the
  per-cell change of variables `∫_{cell} = ∫₀¹ (·±y+2k)`, assembly to
  `∫₀¹ |∂ₓ K_full(t,x,·)| ≤ ∫_ℝ |heat'|`, and the final L∞→L∞ bound.

NET: hGradEq is closed on the full kernel (ROUND-16); the full operator's
Duhamel-ball wiring is gated by this gradient estimate (the tiling theorem) and,
independently, by `hSol`'s interior Schauder `C²` content.

---

## ROUND-16 — Resolution (b): hGradEq is TRUE on the full Neumann kernel (2026-05-29, build 8352 axiom-clean)

Executed ROUND-15 resolution (b): rebuilt the gradient bridge on the full
Neumann kernel.  The `hGradEq` frontier is now CLOSED (proved, not assumed) for
the full-kernel Duhamel operator.

New files (all decls `#print axioms` = core three; whole project green 8352):

* `ShenWork/PDE/IntervalFullSemigroupNeumann.lean`:
  - `deriv_eq_zero_of_even_about` (general: even about `c` ⇒ `deriv = 0` at `c`).
  - `intervalNeumannFullKernel_even_zero` / `_period_two` / `_even_one` — the
    full kernel `∑' k:ℤ, heat(x−y+2k)+heat(x+y+2k)` is even about `0`, period
    `2`, hence even about `1` (lattice reindex: `Equiv.neg`, `Equiv.addRight`).
  - `intervalFullSemigroupOperator_even_{zero,one}` — inherited under the integral.
  - `intervalFullSemigroupOperator_deriv_at_{zero,one}_eq_zero` — genuine
    two-endpoint Neumann (the property the zeroth-reflection kernel lacked at `1`).
  - `intervalFullSemigroup_integral_even_{zero,one}`,
    `intervalFullDuhamelExplicit_deriv_at_{zero,one}_eq_zero` — the source-integral
    term and the full Duhamel explicit field are even about both endpoints
    (integral of even is even), so the explicit field's endpoint derivative is `0`.
    No differentiate-under-integral needed.

* `ShenWork/PDE/IntervalFullKernelDuhamelGradEq.lean`:
  - `intervalFullKernelCoupledDuhamelOperator` — the coupled Duhamel map rebuilt
    on `intervalFullSemigroupOperator`.
  - `intervalFullKernel_hGradEq` — **`hGradEq` holds at EVERY `x ∈ Icc 0 1`**,
    including `x = 1`: interior by lift=explicit on the open interior (set integral
    `Icc 0 τ` = interval integral `0..τ`); endpoints by both sides `= 0` (LHS
    zero-extension, RHS full-kernel two-endpoint Neumann).  This is exactly the
    identity that was FALSE at `x = 1` for the zeroth-reflection kernel (ROUND-15).

REMAINING for full (b) instantiation of Path-A:
  1. **Wire the full-kernel operator into the `_clean`/`_cleaner`/`_resolver`
     hmap chain.** Needs full-kernel gradient `L∞→L∞` estimates (analogues of the
     existing `intervalCoupledDuhamel_grad_*`, which are for the zeroth-reflection
     `intervalSemigroupOperator`) — substantial new analysis, likely via the
     cosine spectral form of the full kernel.
  2. **`hSol`** — the Duhamel image is a genuine classical solution. (b) fixes the
     BOUNDARY (Neumann at both endpoints, now genuine); the INTERIOR content (the
     image solves the PDE + closed-`Icc` `C²` regularity) is the Schauder
     analysis — kernel-independent, the genuine multi-week frontier.

---

## ROUND-14 — hChemDiv_joint_meas DISCHARGED via the AE route (2026-05-29, build 8350 axiom-clean)

The previously-open atomic frontier `hChemDiv_joint_meas` (joint measurability
of the lifted chemotaxis divergence `(s,y) ↦ lift(chemDiv p (u s)(R(u s))) y`)
is now **fully proved as a sequence of axiom-clean lemmas**, in the faithful
a.e. form the downstream consumer actually needs.

KEY FINDING (confirmed by reading the consumer): the leaf consumers
`intervalSemigroupOperator_s_dependent_{aestronglyMeasurable_x, deriv_…_x₀}`
use the joint-measurability input ONLY to produce `AEStronglyMeasurable` of the
`s`-integrand on the Fubini product measure
`(volume.restrict (uIoc 0 t)).prod (intervalMeasure 1)`. So the spatial-endpoint
lines `{y∈{0,1}}` (Lebesgue-null) are discardable — the genuine obstruction
(joint measurability of the *spatial-derivative field* on the full plane, which
Mathlib's `measurable_deriv_with_param` cannot give: it needs GLOBAL joint
continuity, broken by the zero-extension's endpoint jump) is sidestepped.

New files (both in `lake build ShenWork`, every decl `#print axioms` = core three):

* `ShenWork/PDE/IntervalParamDerivMeasurable.lean` — `diffQuotLimsup` surrogate:
  a globally-measurable function built from joint MEASURABILITY alone
  (`limsup_n (n+1)·(g(s,y+1/(n+1))−g(s,y))`), equal to the parametrized spatial
  derivative wherever it exists (`HasDerivAt.tendsto_slope` + `Tendsto.limsup_eq`).
* `ShenWork/PDE/IntervalChemDivAEMeasurable.lean`:
  - `solution_chemotaxisFlux_hasDerivAt` (flux differentiable at interior, deriv = chemDiv);
  - `intervalDomainChemDiv_v_lift_aestronglyMeasurable` (chemDiv-v field AE meas via nested diffQuotLimsup surrogate + interior-slab identification);
  - `aestronglyMeasurable_of_eqOn_interiorSlab` (reusable: agree on Ioo 0 T ×ˢ Ioo 0 1 ⇒ AE-equal, complement null for 0<t≤T);
  - `solution_chemDiv_resolver_eq_v_interior` (R=intervalNeumannResolverR ≡ v on interior);
  - `intervalDomainChemDiv_resolver_lift_aestronglyMeasurable`;
  - `intervalCoupledSource_lift_aestronglyMeasurable_of_components` (AE algebraic closure);
  - `intervalCoupledSource_resolver_lift_aestronglyMeasurable` — CAPSTONE: AEStronglyMeasurable of the lifted coupled-source field for R = paper-2 resolver, directly from a classical solution. This is exactly the `F`-field measurability the Duhamel ball-estimate chain currently takes as the full-`Measurable` `hF_joint_meas`/`hChemDiv_joint_meas` hypothesis.

DISCHARGE COMPLETE (commit c91d063, build 8350 axiom-clean). The consumer
chain `leaves → grad-bound lemmas → _clean → _cleaner` in
`IntervalCoupledClassicalBallEstimates.lean` was AE-refactored IN PLACE (the
chain has no external consumers, so blast radius is contained): the two leaves
and three grad-bound lemmas now take
`AEStronglyMeasurable (uncurry F) ((volume.restrict (uIoc 0 t)).prod
(intervalMeasure 1))` instead of full `Measurable (uncurry F)`; `_clean`/`_cleaner`
take the per-τ AE form. `_cleanest` keeps its `Measurable` hypotheses and
converts via `Measurable.aestronglyMeasurable`, so it and all existing callers
build unchanged.

NEW terminal theorem
`intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_resolver`
(IntervalChemDivAEMeasurable.lean): the C¹_x Duhamel-image ball map for
`R = intervalNeumannResolverR p` with the source-field joint-measurability
obligation (the former `hF_joint_meas`/`hChemDiv_joint_meas`) **eliminated** —
filled internally by `intervalCoupledSource_resolver_lift_aestronglyMeasurable`.
Only the genuine residuals `hSol` (Schauder) and `hGradEq` (Dirichlet endpoint
deriv) remain.  `#print axioms` = core three on the discharge and every
refactored chain lemma; no `sorryAx`/`_native`.

NET: the `hChemDiv_joint_meas` frontier is CLOSED. Two genuine PDE residuals
remain on the Path-A `_resolver` hmap: hSol (Schauder C^{2,1} interior
regularity of the Duhamel image — multi-week classical PDE) and hGradEq
(endpoint derivative-matching bridge — see ROUND-15 finding below).

## ROUND-15 — hGradEq DIAGNOSIS: FALSE at x=1 for the zeroth-reflection kernel (2026-05-29, build axiom-clean)

Rigorous endpoint analysis of `hGradEq` (commit a28055b, three new axiom-clean
lemmas in `IntervalChemDivAEMeasurable.lean`).

`hGradEq` asserts, for `x ∈ Icc 0 1`:
`deriv (intervalDomainLift (Duhamel image τ)) x = deriv (explicit semigroup+integral) x`.

* **Interior `x ∈ Ioo 0 1`:** trivially true — the lift coincides with the
  explicit on the open interior, so the derivatives agree.
* **Endpoints:** `deriv (intervalDomainLift g) 0 = 0` and `… 1 = 0` for EVERY
  `g` (`intervalDomainLift_deriv_at_{zero,one}_eq_zero`: the zero-extension's
  exterior-constant side pins the two-sided derivative to `0`, or it is `0` by
  the non-differentiable convention). So **LHS = 0 at both endpoints**.
  The RHS vanishes at `x = 0` (`intervalSemigroupOperator_deriv_at_zero_eq_zero`:
  the kernel `(1/2)(heatKernel(x−y)+heatKernel(x+y))` is even about `0`).

**FINDING.** `normalizedZerothReflectionKernel` reflects only about `0`, so it is
NOT Neumann at the right endpoint `x = 1`: `deriv (explicit) 1 ≠ 0` for generic
data, while LHS `= 0`.  Hence **`hGradEq` (as stated, ∀ x ∈ Icc) is FALSE at
x = 1**, i.e. the Path-A `_clean`/`_cleaner`/`_resolver` hmap currently carries a
hypothesis that is false for its own Duhamel kernel — the theorems are valid
implications but UNINSTANTIABLE as long as the Duhamel operator is built on the
zeroth-reflection `intervalSemigroupOperator`.

Root cause: `intervalCoupledDuhamelOperator` → `intervalFullDuhamelOperator`
uses `intervalSemigroupOperator` (zeroth reflection, Neumann at `0` only) rather
than the FULL Neumann semigroup.  The same root likely affects `hSol` (which
asserts the image is a genuine two-endpoint-Neumann classical solution).

Two sound resolutions, both architectural (flagged for Xiang/Liang — which
kernel the paper-2 mild solution should use):
  (a) **Weaken `hGradEq` to the interior `Ioo 0 1`** (where it is true) and prove
      the endpoint `G_u` bound directly via LHS `= 0` (`|0| ≤ G_u`).  This
      removes the false hypothesis and would discharge `hGradEq` outright, but
      leaves `hSol`'s two-endpoint-Neumann content unaddressed.
  (b) **Rebuild the Duhamel operator on the full Neumann kernel**
      (`intervalNeumannFullKernel`, proved `= cosineKernel`, Neumann at both
      endpoints).  Then both `hGradEq` and the boundary part of `hSol` become
      genuinely true.  This is the real Path-A frontier; the ROUND-14
      measurability discharge transfers verbatim (it is kernel-agnostic — about
      the source field, not the semigroup).

---


State after the Claude-subagent round (codex usage exhausted). Whole project
builds integrated: `lake build ShenWork` green, 8343 jobs, 0 sorry / 0 axiom
(every key theorem `#print axioms` = [propext, Classical.choice, Quot.sound]).
PDE direction confirmed by Liang: classical solution = joint C^{2,1}.

## ROUND-10 FINAL (2026-05-26, HEAD 66e6e90, self-verified) — GLUING CLOSED IN TWO FORMS

Two coexisting fully-verified gluing theorems (both axiom-clean):

### (A) γ≥1: FULLY UNCONDITIONAL (modulo regime + positive datum)
`GlobalSolutionGluingFromReachability_of_regime_gammaGeOne (p) (hχ : χ₀≤0) (ha : 0<a) (hb : 0<b) (hγ_ge_one : 1 ≤ γ) (hpos : ∀ pair, PositiveInitialDatum)`
covers paper2 formula (1.3)'s standard KS regime (γ=m=α=1). `L_γ = γ·M^(γ-1)` via
MVT on `[0,M]` (no `δ` needed since `x^{γ-1}` bounded when `γ≥1`).
File `Paper2/IntervalDomainL2UEnergyUniformGammaGeOne.lean`.

### (B) general γ>0: unconditional modulo δ>0 lower bound
`GlobalSolutionGluingFromReachability_of_regimeAndLowerBound (p) (hχ) (ha) (hb) (hpos) (hlower : ∃ δ>0, …)`
covers all `γ>0`; needs the `δ>0` lower bound only because `x↦x^γ` Lipschitz
constant on `[δ,M]` is `γ(δ^{γ-1}+M^{γ-1})` and `δ^{γ-1}` blows up at 0 for `γ<1`.
The `δ>0` is the strong-maximum-principle-style content (uniform positivity of
the solution on `(0,T)×[0,1]`); proving it is a separate genuine PDE theorem
(not in repo, not a Lean gap).

### Faithful def state
`intervalDomain.initialAdmissible := BddAbove (Set.range fun x => |u₀ x|)`
(strengthened from `True`; faithful PDE-classical-solution datum requirement).
`IsPaper2ClassicalSolution` carries closed-domain `0 < u`, `0 ≤ v`, closed-`Icc`
C² + endpoint Neumann (values), joint continuity, closed-slab ∂ₜ continuity,
endpoint time-differentiability — a genuine positive classical-solution predicate.

### Entire u-only uniqueness analytic machinery PROVED unconditional + axiom-clean
PDE substitution → dissipation `−∫(∂ₓw)²` (`intervalEnergyByParts`) → chemotaxis
IBP (`intervalFluxByParts`) → Young absorption → reaction Lipschitz → energy
inequality `∫integrandDeriv ≤ K·E_u` (`intervalDomainL2U_energy_diffIneq_bound`).
Full frontier (Leibniz HasDerivAt, cont, initial_vanishes, zero_pointwise where
v=V via resolver characterization). Static v-control (value+grad) by E_u.
Elliptic characterization `solution_v_resolverCoeff_eq` (coefficient-level
unconditional). Cosine coefficient decay `|f̂ₙ|≤M/(nπ)²` for C²-Neumann.
Resolver gradient bridge `resolverR_hasDerivAt_grad` (Weierstrass M-test).
Quantitative resolver sup bounds `F(M)=(ℓ²-weight)·2νM^γ`. Flux closed-Icc C¹.
Upper bound M derived from proven Lemma 3.1 (`uniform_lift_upper_bound_of_regime`).

### Commits this stretch
~18 verified commits 8561490 → 66e6e90, every one self-verified
(`lake build ShenWork` green + `#print axioms` = the three core only).

## ROUND-11 UPDATE (2026-05-27, HEAD 7806e57, build 8344) — GENERAL γ>0 DELTA-FREE

Eliminated the explicit `δ>0` hypothesis from the general γ>0 case using a
per-sub-horizon parallel gluing chain (file
`Paper2/IntervalDomainL2USubHorizonGluing.lean`, additive — doesn't touch the
γ≥1 / explicit-δ chains).

The trick: for each target `t < min T₁ T₂`, pick a strict sub-horizon
`T' := (t + min T₁ T₂)/2 ∈ (t, min T₁ T₂)`. On `(0, T']` the half-horizon
lemma gives uniform `δ_{T'} > 0` (from `lift_u_uniformPositive_on_halfHorizon`
fed by `IntervalDomainPosDatumLowerBound`), and `uniform_lift_upper_bound_of_regime`
gives `M`. Each pair (t, T') applies the existing energy method on the truncated
horizon `T'` (via `IsPaper2ClassicalSolution.restrict_horizon` + the proved
chain), concluding equality at the target `t`. This avoids the
"approaching min T₁ T₂" frontier where a uniform δ would need strong-max-principle
theory.

NEW final theorem:
`GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound (p)
  (hχ : χ₀≤0) (ha : 0<a) (hb : 0<b)
  (hpos : ∀ per-pair, PositiveInitialDatum)
  (hposLower : ∀ per-pair, IntervalDomainPosDatumLowerBound u₀)`
→ `GlobalSolutionGluingFromReachability p` (axiom-clean).

## CURRENT FINAL STATE — THREE COEXISTING UNCONDITIONAL GLUING THEOREMS

All `[propext, Classical.choice, Quot.sound]`:

1. `GlobalSolutionGluingFromReachability_of_regime_gammaGeOne` — paper2 standard
   regime + γ≥1 (covers formula (1.3): γ=m=α=1). Fully unconditional modulo
   regime + positive datum.
2. `GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound` (NEW) —
   general γ>0 + regime + positive datum with uniform lower bound `δ₀>0`.
   Fully unconditional. The lower-bound condition is the standard PDE-textbook
   "positive classical solution with bounded-below initial datum" assumption.
3. `GlobalSolutionGluingFromReachability_of_regimeAndLowerBound` (legacy) —
   general γ>0 + regime + positive datum + explicit `∃ δ>0, …(0,minT)…`. Kept
   for cases that supply the uniform δ externally.

The entire u-only uniqueness analytic machinery (energy inequality core,
frontier assembly, elliptic characterization, coefficient decay, gradient
bridge, faithful def repairs, static v-control, flux IBP/L²/C¹, quantitative
resolver F(M), upper bound from Lemma 3.1, sub-horizon truncation) — fully
unconditional, axiom-clean.

## ROUND-8 CONSOLIDATED (2026-05-26, HEAD 5a34322, self-verified) — GLUING ≈ CLOSED

The ENTIRE u-only uniqueness/gluing analytic body is now PROVED unconditional +
axiom-clean. Gluing `GlobalSolutionGluingFromReachability p` reduces to ONE
boundedness obligation `IntervalDomainL2UBoundedDatumUniform p`
(file Paper2/IntervalDomainL2UFrontierAssembly.lean), via
`GlobalSolutionGluingFromReachability_of_boundedDatumUniform`.

PROVED unconditional this stretch (commits 9c9778d…5a34322, all axiom-clean):
- Energy inequality CORE `intervalDomainL2U_energy_diffIneq_bound`
  (`∫ integrandDeriv ≤ K·E_u`, K=χ₀²Cflux+2L): PDE substitution + dissipation
  `−∫(∂ₓw)²` + chemotaxis IBP + Young `2χ₀∫∂ₓw·g ≤ ∫(∂ₓw)²+χ₀²∫g²` + reaction
  Lipschitz. File Paper2/IntervalDomainL2UEnergyCombine.lean.
- Full frontier assembled unconditional (Paper2/IntervalDomainL2UFrontierAssembly.lean):
  Leibniz `intervalDomainL2UEnergy_hasDerivAt_of_solution`, `cont`,
  `initial_vanishes`, `zero_pointwise` (E_u=0⟹u=U; v=V via static_v_value).
- Faithful def repairs (interior→closed / missing conjuncts): endpoint
  time-differentiability (conjunct 4 → closed), v≥0 (concentration), u>0,
  closed-Icc C² + Neumann, joint continuity. IsPaper2ClassicalSolution now a
  genuine positive classical-solution predicate.
- Static v-control (value+grad) by E_u, flux IBP, flux closed-Icc C¹, flux L²
  bound, elliptic characterization, coeff decay, gradient bridge — all earlier,
  all unconditional.

REMAINING = `IntervalDomainL2UBoundedDatumUniform p`: (bdd₀) shared initial
datum bounded + (Kunif) a τ-uniform Grönwall constant. KEY: this is a
BOUNDEDNESS obligation, NOT a new analytic gap — `Theorem_1_1_intervalDomain_conditional`
(Paper2/IntervalDomainChain.lean) ALREADY proves the uniform sup-norm bound
`supNorm(u t) ≤ max(supNorm u₀, (a/b)^{1/α})` (via Lemma_3_1 + initialSupNormApproach)
and constructs `IsPaper2BoundedBefore`. The per-time K(τ)=χ₀²Cflux+2L is bounded
once `supNorm(uᵢ τ) ≤ M` uniformly ⇒ Kunif; u₀ bounded ⇒ bdd₀. CAVEAT: Lemma_3_1's
bound holds under Theorem 1.1's parameter regime (hχ neg-sensitivity, a,b>0, m≥1),
so the honest resting point may be "gluing unconditional modulo boundedness, which
holds in the Theorem 1.1 regime" — matching paper2's own "bounded ⇒ global"
structure.

## ROUND-9 FINAL STATE (2026-05-26, HEAD ccb926a, self-verified, build 8342)

Discharge outcome: full-unconditional is FALSE (uniform M needs Thm 1.1 regime
χ₀≤0,a,b>0 via Lemma 3.1). Delivered the FAITHFUL reduction — gluing is now
`GlobalSolutionGluingFromReachability_of_uniformSupBound` (axiom-clean), taking the
NATURAL hypothesis `IntervalDomainUniformLiftBound p` (every solution-pair sharing
a trace is uniformly `lift(uᵢ τ) ∈ [δ,M]` on (0,minT)×[0,1]) + datum boundedness.
The ad-hoc Grönwall K is now DERIVED, not assumed: quantitative resolver sup bounds
`resolverValue/Grad_sup_le_of_ub` (`F(M)=(ℓ²-weight)·2νM^γ`) ⇒ `CfluxQuant(δ,M)` ⇒
uniform K. Files Paper2/IntervalDomainResolverSupQuantitative.lean,
Paper2/IntervalDomainL2UEnergyUniform.lean.

NET: the ENTIRE u-only uniqueness/gluing ANALYTIC machinery is proved unconditional
& axiom-clean. Gluing holds modulo exactly: (i) uniform sup bound `M` on solutions
(= `IsPaper2BoundedBefore`, which Theorem_1_1_intervalDomain_conditional ALREADY
proves under the regime); (ii) uniform positive lower bound `δ>0` (needed only for
`γ<1`; a strong-max-principle quantitative positivity — NOT yet in repo); (iii)
datum boundedness `bdd₀` (intervalDomain `initialAdmissible=True` is too weak — a
faithful-def question). All three are boundedness/positivity inputs matching paper2's
own structure, NOT analytic gaps. REMAINING WORK = formulation/architecture (connect
(i) to Lemma 3.1 under the regime; decide datum-admissibility def; prove uniform δ>0)
— best done with Xiang/Liang, not autonomously.

## ROUNDS 5–7 CONSOLIDATED (2026-05-26, HEAD 31c4df3, self-verified)

The ENTIRE analytic infrastructure for u-only uniqueness is now UNCONDITIONAL
(no hypotheses). Gluing closes via the chain
`IntervalDomainL2UDiffIneqResidual p` → `intervalDomainL2UJointTimeRegularity_of_residual`
→ `intervalDomainClassicalUniquenessL2EnergyMethod_of_uJointTimeRegularity`
→ `..._of_uFrontier` → `GlobalSolutionGluingFromReachability_of_l2EnergyMethod`,
and the ONLY remaining open obligation is the single residual structure
`IntervalDomainL2UDiffIneqResidual p` = the nonlinear parabolic energy
inequality `E_u'(τ) ≤ K·E_u(τ)` itself.

PROVED unconditional + axiom-clean this stretch (commits fc0f5c3, a67c952,
d1f581f, 4c3ee88, 31c4df3):
- Elliptic characterization `solution_v_resolverCoeff_eq` (v cosine-coeffs =
  resolver coeffs; coefficient-level, no hyps) + supporting eigenfunction-IBP
  `intervalCosineLaplacianCoeff_eq_of_contDiffOn`. File PDE/IntervalEllipticCharacterization.lean.
- Coefficient decay `cosineCoeff_decay` (|f̂ₙ|≤M/(nπ)² for C²-Neumann) +
  ℓ¹ value reconstruction `fourierCoeff_reflCircle_summable`. File PDE/IntervalCosineCoeffDecay.lean.
- Termwise-diff bridge `resolverR_hasDerivAt_grad` (deriv of value series =
  resolver gradient series, Weierstrass M-test). File PDE/IntervalResolverGradientBridge.lean.
- FAITHFUL POSITIVITY: `IsPaper2ClassicalSolution` positivity strengthened
  interior-conditional → closed-domain `0 < u t x` (positive classical solution,
  Chen–Ruau–Shen + strong max principle); ~30 sites re-discharged across 11
  files; Paper3 counterexample `proposition12Counter` given a positive profile
  (content preserved: u=t unbounded for t≥1, Thm1.1⇏Prop1.2 holds; the old
  version had exploited the vacuous empty-interior positivity).
- `sourceCoeffQuadraticDecay_of_solution` PROVED unconditional (positive lower
  bound + rpow C² on positives + Neumann endpoints + cosineCoeff_decay).
- `solution_resolver_grad_hasDerivAt` (static ∂ₓ(v−V) control) unconditional.
- Resolver-Lipschitz pointwise-reconstruction side-hyps discharged for solutions:
  `solution_resolver_(cosine|sine)Series_summable`. File Paper2/IntervalDomainL2UStaticVControl.lean.
- u-only track (E_u=∫(u−U)²) + Leibniz half + bridges (rounds 4): files
  Paper2/IntervalDomainL2UEnergy.lean, Paper2/IntervalDomainL2UEnergyInequality.lean.

REMAINING = `IntervalDomainL2UDiffIneqResidual p`, a 5-step nonlinear combine,
all inputs now unconditional:
1. Pointwise elliptic rep `lift(v t) = resolverR(u t)` unconditional for
   solutions (discharge `solution_v_eq_resolver_pointwise` F/hFcont/hFcoeff/
   hFsum/hFeq by constructing the continuous even-reflection representative;
   hFsum from `fourierCoeff_reflCircle_summable`, hRsum from the new summability).
2. Static L² control `∫ (lift(v₁−v₂))² + (∂ₓlift(v₁−v₂))² ≤ C·E_u`
   (per-point sup bounds + L∞ via conjunct-7 compactness).
3. Chemotaxis IBP lemma `∫ w·∂ₓ(F) = −∫ ∂ₓw·F` (Neumann kills boundary), analogue
   of proven `intervalEnergyByParts`.
4. Flux-difference pointwise bound `|flux₁−flux₂| ≤ C(|w|+|v-diff|+|∂ₓ v-diff|)`
   (product/quotient rule on `u·∂ₓv/(1+v)^β`, using `1+v≥1` from v>0).
5. Combine: `pde_u` substitution into `½E_u'=∫w·∂ₜw` + dissipation `−∫(∂ₓw)²`
   (`intervalEnergyByParts`) + reaction `intervalLogisticSource_lipschitz` +
   Young (sign-free `|χ₀|`, ε∫(∂ₓw)² absorbed) ⇒ `E_u'≤K·E_u`.
No Mathlib gap; pure repo-side nonlinear parabolic-elliptic energy estimate.

## ROUND-3 UPDATE (2026-05-26, commit 8561490, self-verified build+axioms)

R1 and R2 — the two pieces scoped as closeable — are DONE and clean:
- R1: conjunct (9) of `intervalDomainClassicalRegularity` = joint continuity of
  the solution field `(t,x)↦intervalDomainLift(u t)x` on `Ioo 0 T ×ˢ Icc 0 1`
  (+ for v). All 6 build-path constructors/transfer lemmas re-discharged.
- R2: `ShenWork.IntervalSolutionCoeffDeriv.intervalEnergyByParts`:
  `∫₀¹ w·w'' = −∫₀¹ (w')²` via closed-`Icc` `HasDerivAt` + endpoint Neumann
  values (conjunct 7), one `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`.

KEY SHIFT: because conjunct (7) now ASSERTS closed-Icc C² + endpoint Neumann in
the def, the remaining residual is NO LONGER "prove Schauder boundary
regularity" — that regularity is now hypothesised by the faithful def. The
single residual `IntervalDomainL2JointTimeRegularity p` is the nonlinear ENERGY
ESTIMATE assembly: substitute the pointwise PDE identity into E′, IBP via R2,
absorb chemotaxis/reaction differences by `intervalLogisticSource_lipschitz` +
resolver Lipschitz + the L∞ bound (now available: conjunct-7 `ContDiffOn (Icc 0
1)` ⇒ bounded on compact). Multi-lemma but reachable, repo-side, no Mathlib gap.

## ROUND-4 UPDATE (2026-05-26, commit 2b8a8b8, self-verified build 8328 + axioms)

FINDING: the bundled energy `∫₀¹ (u−U)²+(v−V)²` is the WRONG functional for a
parabolic-elliptic system. Differentiating `(v−V)²` forces `∫ z·∂ₜz` (z=v−V),
but z solves an ELLIPTIC relation (`0=∂ₓₓz−μz+ν(u₁^γ−u₂^γ)`) — no time-equation
among hypotheses ⇒ dead-end. Artifact of the energy choice, not a Mathlib gap.

FIX (standard parabolic-elliptic uniqueness; new file
`ShenWork/Paper2/IntervalDomainL2UEnergy.lean`, in build graph): u-only energy
`E_u=∫₀¹ (u−U)²`; z controlled STATICALLY (`‖z‖,‖∂ₓz‖≤C‖w‖` via proven
`intervalNeumannResolverR_(sup|grad_sup)_lipschitz`); `E_u=0⇒u=U⇒v=V` by
elliptic uniqueness. PROVED + axiom-clean: `…L2DifferenceEnergyU(+_nonneg)`,
`IntervalDomainClassicalOverlapL2UEnergyCertificate`,
`…overlap_unique_of_l2UEnergyCertificate` (genuine Grönwall on E_u),
`IntervalDomainL2UDifferenceEnergyFrontier(+_of_diffIneqFrontier)`,
`intervalDomainClassicalUniquenessL2EnergyMethod_of_uFrontier` (THE bridge ⇒
full joint method ⇒ `GlobalSolutionGluingFromReachability`),
`IntervalDomainL2UJointTimeRegularity`(+builder+`_of_uJointTimeRegularity`).

REMAINING (single obligation, strictly WEAKER — v-difference time-derivative
GONE): construct `IntervalDomainL2UJointTimeRegularity p` = standard parabolic
`E_u′≤K·E_u`. Leibniz half from conjuncts (8)(9)+slab machinery; dissipation
`−2∫(∂ₓw)²≤0` from proven `intervalEnergyByParts`. Open part = chemotaxis/
reaction Lipschitz absorption assembly + reconciling abstract `chemotaxisDiv`/
`laplacian` derivs with resolver-Lipschitz summability (may need a lemma that
the abstract solution's v IS the resolver of u).

## PROVEN this round (deep machinery, all axiom-clean, committed)

- Kernel↔spectral: `intervalNeumannFullKernel_eq_cosineKernel`, `intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional`, `..._contDiff_two_unconditional` (full Neumann kernel semigroup = cosine spectral heat value, spatially C²). Files: PDE/IntervalNeumannFullKernel.lean, PDE/IntervalFullKernelInterchange.lean.
- Poisson/theta: `gaussianLatticeSum_poisson(_complex)` (Mathlib Complex.tsum_exp_neg_quadratic).
- Heat smoothing C²: `unitIntervalCosineHeatValue_contDiff_two`. Parabolic gain: `parabolicGain_le_one` (kills s→t singularity). File: PDE/IntervalDuhamelRegularity.lean.
- IBP engine: `intervalCosineLaplacianCoeff_eq` (⟨Δg,eₙ⟩=−λₙ⟨g,eₙ⟩ for genuine-Neumann C² g). File: PDE/IntervalSolutionCoeffDeriv.lean.
- Spectral generator: `intervalFullSemigroupOperator_hasTimeDerivAt_spectral`. Duhamel rep assembly: `intervalDuhamelRepresentation_of`. File: PDE/IntervalDuhamelRepresentation.lean.
- Approximate identity: `intervalFullSemigroup_tendsto_id_at_zero` (Tannery). File: PDE/IntervalSemigroupApproxIdentity.lean.
- Regularity def completed to joint C^{2,1} (commit 754ee06 spatial C², 69176a5 time-diff).
- Neumann BC / sup IBP enablers; resolver R + L²/sup/grad Lipschitz; L2 uniqueness Gronwall core + certificate (cond. on frontiers); ball-estimates (hchem/hint/hlift_int over R); logistic Lipschitz.

## DEFINITION FAITHFULNESS GAPS (classical-solution def incomplete)

1. DONE: spatial interior C² added; timeDeriv made genuine (joint C^{2,1}).
2. OPEN — Neumann BC VACUOUS: `intervalDomainNormalDeriv f x := if x.1=0∨x.1=1 then 0 else deriv...` is hardcoded 0 at boundary → the `normalDeriv (u t)=0` conjunct of `IsPaper2ClassicalSolution` (Paper2/Statements.lean:70) asserts nothing about u. Need genuine one-sided derivative = 0; then re-prove the ~24 users. (Caught by the IBP work; the IBP needs genuine g'(0)=g'(1)=0.)
3. NOTE: S(0)=id is FALSE here (`heatKernel 0 = 0`); use the proven approximate-identity limit instead (da16507 documents).

## REMAINING ANALYTIC OBLIGATIONS (named, reachable, real theorems)

A. Pointwise cosine inversion `∑ₙ f̂ₙ cos(nπx) = f x` at interior x (repo has only L² totality `unitIntervalCosine_nat_total_ae_zero`) + ℓ¹ coeffs `Summable |f̂ₙ|`. → closes approximate-identity hypotheses (`hrecon`, `hl1`).
B. `CoeffTimeDerivUnderIntegral`: d/ds⟨u s,eₙ⟩=⟨∂ₛu s,eₙ⟩ (differentiate inner product under integral; needs uniform integrable envelope — joint-time-regularity class). `SpectralSeriesTermwiseDeriv`: termwise s-deriv of the cosine tsum.
C. Re-assemble `intervalDuhamelRepresentation_of` using the approximate-identity limit (proven) instead of the false `IntervalSemigroupIdentityAtZero`.
D. Genuine-Neumann regularity input for `IntervalSolutionFourierCoeffDeriv` (depends on gap #2).
E. Energy differential inequality `E′ τ ≤ K·E τ` for w=u₁−u₂ → `IntervalDomainL2DifferenceEnergyFrontier` → gluing (needs the under-integral Leibniz D1 ball-diff + D2 envelope, same joint-time class as B).
F. ASSEMBLE: representation + DuhamelTermInteriorC2 (needs DuhamelHeatValueRepresentation Fubini, blocked on the representation) + boundedness (proven) → `IntervalDomainGlobalSolutionExists` → `Theorem_1_1_intervalDomain` unconditional; gluing → uniqueness; Paper3 Theorem 2.x + Paper1 Theorem 1.2/1.3 follow (already reduced to existence).

## Honest summary
All deep mechanisms proven + integrated-verified. Theorem 1.1 NOT closed.
Remaining = complete the faithful def (genuine Neumann, #2) + standard analysis
(pointwise cosine inversion A; under-integral coeff/energy regularity B,E;
representation reassembly C) + final assembly F. Each reachable, real,
multi-step. No Mathlib gap identified — all repo-side / standard parabolic theory.

---

## ROUND-2 UPDATE (2026-05-25, after Claude-subagent push — 22 commits)

### Faithful definition COMPLETE
`intervalDomainClassicalRegularity` now has 6 conjuncts = genuine joint C^{2,1} + genuine Neumann:
`.1/.2` sup-mono; `.2.2.1` interior spatial ContDiffOn ℝ 2; `.2.2.2.1` per-x time DifferentiableAt + ∂ₜ ContinuousOn; `.2.2.2.2.1` JOINT (t,x) continuity of ∂ₜ on Ioo×Ioo; `.2.2.2.2.2` genuine one-sided Neumann. All constructors (constant/equilibrium/bad-tail) discharge. Full build green 8326.

### Additionally PROVEN this round (axiom-clean, committed)
- Obligation A CLOSED: `intervalCosine_hasSum_pointwise` + `intervalCosineCoeff_summable_abs` (pointwise cosine inversion + ℓ¹) — e40efab.
- Localized under-integral Leibniz `intervalIntegral_hasDerivAt_time_of_local` + `exists_bound_of_continuousOn_slab` (D1 fixed; D2 from closed-slab continuity) — 90db85f.
- Energy Leibniz machinery `intervalDomainClassicalL2DifferenceEnergy_hasDerivAt_of_slabContinuous` (energy time-derivative reduced to one closed-slab-continuity hypothesis) — 0614724.
- Genuine-Neumann (d20173a), continuous-∂ₜ (3fb3c1d), joint-continuity (c972404).

### THE RECURSIVE-DEEPENING FINDING (honest)
Each regularity level revealed the next: spatial-C² → genuine-Neumann → time-DifferentiableAt → time-ContinuousOn → JOINT continuity → now BOUNDARY regularity. The current blocker for E (gluing): `exists_bound_of_continuousOn_slab` needs continuity on the CLOSED slab `Icc(τ−δ,τ+δ) ×ˢ Icc 0 1`, but the def gives only OPEN `Ioo×Ioo` — i.e. a τ-uniform INTEGRABLE bound on ∂ₜw up to spatial endpoints x→0⁺,1⁻ (where the zero-extension lift branches). This is genuine PARABOLIC BOUNDARY REGULARITY — a real classical PDE theorem, not bookkeeping, not a Mathlib gap.

### REMAINING (genuine deep tail, each a real theorem)
1. Parabolic boundary regularity: ∂ₜu (and ∂ₓ,∂ₓₓ) continuous/integrable UP TO the spatial endpoints → closes the closed-slab envelope → E (gluing).
2. `Eprime ≤ K·E` IBP step (PDE substitution + Neumann IBP with genuine boundary w'(0)=w'(1)=0 + Lipschitz absorption).
3. localExistence genuine constructor: full-kernel mild solution satisfies the complete 6-conjunct regularity (needs joint Weierstrass `continuous_tsum` for −∑λₙe^{−tλₙ}f̂ₙcos) + the Duhamel term (DuhamelTermInteriorC2 / DuhamelHeatValueRepresentation).
4. Representation reassembly with the approximate-identity limit (C); final assembly (F) → Theorem 1.1.

### Honest status
Faithful def + all reachable deep machinery proven & verified & integrated (8326 green). Theorem 1.1 NOT closed; the remaining is genuine boundary parabolic-regularity theory — a sustained expert-level effort, not in-session subagent-grindable. No Mathlib gap identified.

## ROUND-12 — END-TO-END THEOREM 1.1 UMBRELLA (2026-05-27, HEAD be51e99, build 8345 axiom-clean)

After ROUND-11 closed the gluing chain for both γ≥1 (regime+datum) and general γ>0 (regime+datum+PosDatumLowerBound), wired the chain all the way to **Paper2 Theorem 1.1**.

### `Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded` (Paper2/IntervalDomainTheorem11Umbrella.lean)

Produces `Theorem_1_1 intervalDomain p` from minimal honest hypothesis set:
- **Math inputs (faithful):** regime (χ₀≤0, a,b>0); `PosDatumLowerBound u₀` (bounded-below positive datum) per pair; `PositiveInitialDatum u₀` per pair.
- **Textbook PDE inputs (genuine repo gaps, none fabricated):**
  - `hlocal`: standard short-time local classical existence.
  - `hrealize`: realization-at-`sSup` of reachable horizons (compactness/Ascoli–Arzelà).
  - `hextend_of_not_finiteAlternative`: restart past finite-sup when the finite alternative fails.
  - `hextend_of_not_mgeAlternative`: same for the m≥1 alternative.

### What was eliminated internally vs. the original umbrella:
- ❌ `hreach` (the `ReachableArbitrarilyLong` black-box) — DERIVED from regime + Lemma 3.1 sup-norm bound + supnorm-controls-pointwise + `not_finiteContinuationAlternativeBranch_of_boundedBefore_and_supNormControl` + `standardContinuationAlternative_of_finiteSup_realization_and_extension`.
- ❌ `hrangeBounded` — DERIVED from conjunct-7 (lift `ContDiffOn ℝ 2 (Icc 0 1)` ⇒ continuous on compact ⇒ bounded), via the proven `classicalSolution_u_range_bddAbove` lemma.
- ❌ `hboundedInitial` — DERIVED from `PositiveInitialDatum.admissible` (the strengthened datum-def, now `BddAbove (range |u₀|)`).
- ❌ Explicit `δ>0` uniform on (0,minT) — DERIVED from `PosDatumLowerBound` via sub-horizon construction + halfHorizon + lift_u_uniformPositive_on_compact.

### Net: the umbrella's textbook surface is now MINIMAL
The 4 PDE textbook inputs (hlocal + hrealize + hextend_*) are precisely the standard maximal-continuation theorem ingredients — exactly the content Paper2 cites from PDE literature, not anything specific to chemotaxis. The 3 datum pass-throughs (hposWit / hposLowerWit / per-pair positivity) are forced by gluing's universal quantification over solution pairs — semantically required, not removable without restructuring the gluing API.

### Building-block lemmas added (all axiom-clean, useful for future work):
- `lift_u_uniformPositive_on_compact` (closed [s,t]⊂(0,T) uniform δ from u_pos' + conjunct-9 + compactness).
- `lift_u_uniformPositive_on_halfHorizon` (uniform δ on (0,t] via trace squeeze + compactness, given PosDatumLowerBound).
- `lift_v_bounded_on_compact` (v-side parallel to u).
- `classicalSolution_u_range_bddAbove` (per-time bounded range from conjunct-7).

## ROUND-13 — MAXIMAL CONTINUATION COLLAPSE (2026-05-27, HEAD 715b1f7, build 8345 axiom-clean)

After Liang (Paper2 author) confirmed Paper2 only addresses γ≥1 (2026-05-27 cron group response), attacked maximal continuation theorem aggressively for the paper's actual regime. Three textbook PDE inputs eliminated via internal derivation, in 3 subagent rounds:

### Eliminations
1. **`hextend_finite`** discharged via `not_mgeOneFiniteHorizonAlternative_of_realize_in_negative_regime` (Paper2/IntervalDomainGlobalWellposed.lean): the MGeOne alternative implies the Finite alternative in the χ₀≤0/a,b>0 regime via Lemma 3.1 + initial-approach + classicalSolution_u_range_bddAbove + supNormControlsPointwiseBefore_of_timeSlice_rangeBounded.
2. **`hrealize`** discharged via `realize_at_finiteMaximalReachableHorizon_of_overlapUnique` (PDE/IntervalDomainExistence.lean): STRUCTURAL MERGING — at the open sup `T*`, solutions at horizons `T_n < T*` merge via proved overlap-uniqueness; predicate at horizon `T*` only requires properties on `(0, T*)` covered by `⋃ (0, T_n)`. NO Ascoli-Arzelà at endpoint needed. Verified via `continuousOn_of_locally_continuousOn` per regularity conjunct.
3. **`hextend_mge`** discharged via `extend_of_not_mgeAlternative_of_uniformLocalExistence` (Paper2/IntervalDomainTheorem11Umbrella.lean): packaged the textbook "parabolic continuation with uniform δ(M)" as ONE Prop `IntervalDomainUniformLocalExistence p`; combined with Lemma 3.1 + overlap uniqueness yields hextend_mge (and hextend_finite too).

### Final γ≥1 paper-aligned umbrella
`Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge_bundled` takes:
- regime (χ₀≤0, a,b>0)
- γ≥1
- `IntervalDomainPaper2ContinuationDataGammaGeOne_no_hextend_mge` bundle (3 fields):
  - `localExistence` — standard short-time classical local existence
  - `uniformLocal` — `IntervalDomainUniformLocalExistence p` (textbook parabolic continuation)
  - `posWit` — book-keeping pass-through (per-pair PositiveInitialDatum)

**ONLY 2 textbook PDE inputs remain**, both standard items Paper2 itself cites from PDE literature (Henry §3.3 / Amann Vol. I). From the 4-textbook-input baseline to 2 in three subagent rounds, every step axiom-clean and verified.
