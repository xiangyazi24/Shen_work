# Q3266 (cron1) — final six Moser/PDE frontiers triage

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Executive answer

The six listed frontiers are **not six independent hard PDE gaps**. The repo has already built a large part of the endpoint/FTC and scalar-Moser scaffolding. The remaining work should be reorganized as follows:

```text
Main hard PDE producer:
  #3 integratedMoserDissipation, using #4 relativeMassGradient and #6 initial-window FTC data.

Endpoint/FTC producer:
  #6 IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData.
  This largely subsumes #1 zeroRightDerivative.

Moser terminal producer:
  #5 quantitativeEndpoint.

Derived/packaging:
  #2 gradientTimeIntegrable should be derived after #3, not attacked first.
```

Recommended attack order:

```text
1. #6 initial-window FTC / PDE integrability package.
2. #4 relativeMassGradient / GN-Young package wiring.
3. #3 integratedMoserDissipationDropBefore from the integrated PDE energy inequality.
4. Derive #2 gradientTimeIntegrable from #3 + regularity/energy continuity.
5. #5 quantitativeEndpoint from the already-landed dyadic root-tower scalar lemmas.
6. Collapse #1 into #6 / closed-energy trace infrastructure, or prove it only as a corollary of the same FTC package.
```

The key audit result: `P3MoserEnergyContinuity.lean`, `P3MoserFTCInfrastructure.lean`, `P3MoserDissipationShape.lean`, `P3MoserIntegratedClosure.lean`, `P3MoserLemmaDischarge.lean`, `P3MoserActualWiring.lean`, `IntervalDomainMoserActualAtoms.lean`, and `IntervalDomainMoserClosure.lean` already contain most of the scaffolding. The remaining atoms are concentrated PDE estimates, not broad missing infrastructure.

## Frontier-by-frontier triage

### 1. `zeroRightDerivative`

**Likely status:** present under a related name, not the exact name.

The direct grep for `zeroRightDerivative` was not productive, but `P3MoserClosedEnergyProducer.lean` and `P3MoserFTCInfrastructure.lean` expose the exact shape:

```text
IntervalDomainL2SeedZeroRightDerivative u
ClosedEnergyIdentityTraceRemainingData.zeroRightDerivative
```

`P3MoserClosedEnergyProducer.lean` already proves the positive-time `HasDerivWithinAt` field:

```text
intervalDomainLpAbsEnergy_two_hasDerivWithinAt_of_classical_interior
intervalDomainLpAbsEnergy_two_hasDerivWithinAt_of_classical_and_zero
```

and packages the partial trace data for the re-anchored trajectory:

```text
closedEnergyIdentityTracePartialData_withInitialSlice_of_classical
closedEnergyIdentityTraceData_withInitialSlice_of_classical
```

`P3MoserFTCInfrastructure.lean` then specializes `IntegratedMoserEnergyWindowFTC` at exponent `2` to produce most of the closed-energy trace, with only the zero-time right derivative as a named remaining endpoint input:

```text
closedEnergyIdentityTraceRemainingData_of_integratedMoserEnergyWindowFTC
closedEnergyIdentityTraceRemainingData_of_globalPDEInitialData
closedEnergyIdentityTraceData_withInitialSlice_of_globalPDEInitialData
```

**Hardness:** medium, but probably redundant. It is an endpoint compatibility lemma, not a core PDE inequality.

**Most efficient tactic:** do not prove this directly from classical regularity at `t = 0`. Classical regularity is interior-time only. Instead, prove the stronger initial-window FTC package (#6). Then specialize it at exponent `2` via `P3MoserFTCInfrastructure.lean`; the right derivative becomes either a field in the same package or a corollary of the primitive identity.

**Key insight:** the re-anchored trajectory sets `u(0)=u₀`, but positive-time dynamics are unchanged. Endpoint differentiability at `0` should be derived from the right-primitive/FTC identity, not from a nonexistent classical time derivative at the boundary.

### 2. `gradientTimeIntegrable`

**Likely status:** the exact field is present and still carried.

Files:

```text
P3MoserRegularityProducer.lean
P3MoserEnergyContinuity.lean
P3MoserIntegratedClosure.lean
```

`P3MoserRegularityProducer.lean` defines:

```text
IntervalDomainRawMoserGradientTimeIntegrability
IntervalDomainIntegratedMoserRegularityFrontierData.gradientTimeIntegrable
IntervalDomainIntegratedMoserRegularityFrontierDataLite.gradientTimeIntegrable
IntervalDomainIntegratedMoserGlobalClassicalRegularityData.gradientTimeIntegrable
```

`P3MoserEnergyContinuity.lean` already has the null-singleton transfer across the re-anchored slice:

```text
intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw
```

So the endpoint rewrite has been handled. The raw integrability itself is the remaining analytic input.

**Hardness:** not independently hard if #3 is proved. It is currently a carried field, but should be derived from the integrated dissipation inequality.

**Existing bridge:** `P3MoserIntegratedClosure.lean` proves

```text
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
```

which takes `IntegratedMoserDissipationDropBefore` plus endpoint/time-integral bounds and yields a bound on the time integral of the Moser gradient. This is exactly the kind of result needed for `gradientTimeIntegrable`.

**Most efficient tactic:** after #3, derive `gradientTimeIntegrable` by applying the integrated drop with `t1=0`, `t2=T` or finite subwindows, using:

```text
energyContinuous / initialPowerBound / powerTimeIntegrable
```

from `IntegratedMoserFirstCrossingRegularity`.

**Key insight:** do not prove gradient integrability by endpoint smoothness of the gradient integrand. Use the integrated Moser energy inequality itself: it already contains the time integral of the gradient with a positive coefficient.

### 3. `integratedMoserDissipation`

**Likely status:** shape and scalar algebra proved; PDE producer not proved.

Files:

```text
P3MoserDissipationShape.lean
P3MoserIntegratedClosure.lean
P3MoserThresholdPlanProducer.lean
```

`P3MoserDissipationShape.lean` defines the faithful target:

```text
IntegratedMoserDissipationDropBefore
IntegratedMoserDissipationDropBeforeCoeff
```

and provides wrappers:

```text
integratedMoserDissipationDropBefore_of_coeff_two
integratedMoserDissipationDropBefore_of_coeff_ge_two
integratedMoserDissipationDropBefore_of_integrated_energy
```

It also documents why the old pointwise raw drop was not a faithful theorem target.

`P3MoserIntegratedClosure.lean` has scalar absorption lemmas, including:

```text
scalar_absorb_higherPower_window_const
scalar_absorb_higherPower_window
exists_pos_eps_mul_le_sub_of_coeff_gap
```

**Hardness:** genuinely hard, but now sharply localized. This is the main PDE estimate.

**Dependencies:** depends on #6 for the integrated window FTC and on #4 for the relative interpolation/absorption of the higher-power term.

**Most efficient tactic:** prove a theorem of this shape:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserDissipationShape
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.PDE.P3MoserLemmaDischarge

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserPDEDrop

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-
Target theorem shape:

theorem intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hT : 0 < T)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    -- plus cross-diffusion bounds already supplied by henergy/hcross
    : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
-/

end ShenWork.IntervalDomainExistence.P3MoserPDEDrop
```

The proof path is:

1. Use the FTC package to integrate the derivative term over `[t1,t2]`.
2. Use the already-landed `LpBootstrapEnergyInequality` / interval-domain Lp energy inequality to get the integrated inequality with a higher-power term.
3. Apply `RelativeMoserInterpolationBefore` with an `eps` chosen by `exists_pos_eps_mul_le_sub_of_coeff_gap`.
4. Package with `integratedMoserDissipationDropBefore_of_coeff_ge_two` or `..._of_integrated_energy`.

**Key insight:** prove the **integrated** inequality directly. Do not try to resurrect the old pointwise `rawMoserDrop` predicate. The repo already contains a counterexample showing why that shape is wrong.

### 4. `relativeMassGradient`

**Likely status:** partially proved under different names; assembly still needed.

Files:

```text
P3MoserLemmaDischarge.lean
P3MoserLemmas.lean
GagliardoNirenberg.lean
IntervalDomainMCL.lean
```

`P3MoserLemmaDischarge.lean` has:

```text
unitInterval_regular_power_GNYoung : UnitIntervalPowerGNYoungForMoser
relativeMoserInterpolationBefore_of_massGradient
```

`P3MoserLemmas.lean` has wrappers:

```text
intervalDomain_relativeMoserInterpolationBefore_of_massGradient
intervalDomain_relativeMoserInterpolationBefore_rho_one_of_massGradient
```

`GagliardoNirenberg.lean` contains a concrete 1D GN lemma:

```text
gagliardoNirenberg_interval
```

**Hardness:** medium. The analytic inequality is essentially present; the remaining work is matching interfaces and exponents.

**Most efficient tactic:** avoid a new general Sobolev/GN library. Use the already-proved `UnitIntervalPowerGNYoungForMoser` and package it into the exact `RelativeMoserInterpolationBefore` consumer. If the existing wrapper’s `hgrad` side condition is awkward, prove a more direct wrapper from `UnitIntervalPowerGNYoungForMoser` to `RelativeMoserInterpolationBefore` instead of forcing the older mass-gradient interface.

**Key mathematical insight:** set

```text
w = u^(p/2)
```

then

```text
u^(p+ρ) = w^(2 + 2ρ/p).
```

In 1D, GN/Young gives

```text
∫ w^(2 + 2ρ/p) ≤ η ∫ |w_x|² + Cη * lower_order(w).
```

The lower-order term is controlled by the current `Lp` energy (`∫ u^p`) and/or the mass-power-to-current-Lp lemma. This is exactly the relative interpolation shape used in the integrated Moser step.

**Possible collapse:** #4 is not a separate frontier once the wrapper from `UnitIntervalPowerGNYoungForMoser` to `RelativeMoserInterpolationBefore` exists.

### 5. `quantitativeEndpoint`

**Likely status:** scalar root-tower and final conversion are already proved; PDE recurrence/pointwise power control remains.

Files:

```text
IntervalDomainMoserActualAtoms.lean
IntervalDomainMoserClosure.lean
P3MoserActualWiring.lean
IntervalDomainMoserLadderAtoms.lean
```

`IntervalDomainMoserActualAtoms.lean` already proves finite dyadic root-tower estimates:

```text
dyadic_inv_sum_Icc_le_one
dyadic_k_inv_sum_Icc_eq
dyadic_k_inv_sum_Icc_le_two
dyadicMoserFactor
dyadic_moser_factor_prod_split
dyadic_root_tower_product_bound
dyadic_root_tower_iterate_bound
dyadic_root_tower_bound
```

`IntervalDomainMoserClosure.lean` defines the honest endpoint:

```text
IntervalDomainMoserPointwisePowerControlBefore
IntervalDomainMoserLpAbsRootBoundBefore
IntervalDomainMoserQuantitativeEndpoint
```

and proves conversion:

```text
intervalDomain_supNorm_le_of_pointwise_power_control
intervalDomain_boundedBefore_of_pointwise_power_control
intervalDomain_boundedBefore_of_moser_quantitative_endpoint
intervalDomain_boundedBefore_of_moser_iteration_chain_and_quantitative_endpoint
```

`P3MoserActualWiring.lean` shows Proposition 2.5 consumes `hEndpoint` as the remaining endpoint atom.

**Hardness:** hard, but it is a discrete/scalar recurrence plus one Sobolev/Agmon endpoint step, not broad PDE regularity.

**Most efficient tactic:** do not use the false abstract envelope frontier. Build the structured dyadic endpoint for the actual interval-domain solution:

```text
p_k = 2^k * p_start,
M_k = sup_t ||u(t)||_{p_k},
M_{k+1} ≤ (C * 2^k)^(1/2^k) * M_k.
```

Then feed `dyadic_root_tower_bound` to obtain a uniform finite root bound and finally produce

```text
IntervalDomainMoserPointwisePowerControlBefore
```

for some finite stage / limiting endpoint expected by the current hook.

**Key insight:** the scalar tower is already landed. The remaining task is generating the recurrence constants from the integrated Moser step/GN estimates in the exact `IntervalDomainMoserQuantitativeEndpoint` format.

### 6. `IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData`

**Likely status:** exact target exists; reduced to two subfields.

The exact structure is in `P3MoserEnergyContinuity.lean`:

```text
IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
```

with fields:

```text
atZero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
pdeCombinedInitial :
  IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0
```

and it already has a direct producer:

```text
intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData
```

There are also intermediate producers:

```text
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_powerInit
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_weightedTimeTerm
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeCombined
intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeTerms
```

**Hardness:** medium-hard but highly localized. This is the first thing to attack because it unlocks FTC and collapses `zeroRightDerivative`/endpoint issues.

**Most efficient tactic:** produce its two fields separately.

The `atZero` field is largely already handled by re-anchoring and trace:

```text
intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
```

The remaining real work is `pdeCombinedInitial`, i.e. integrability near `t=0` of

```text
q * DiffusionIntegral - q * χ₀ * ChemotaxisIntegral + q * LogisticIntegral.
```

Use the combined residual rather than componentwise unless componentwise estimates are already simpler. Endpoint `s=0` is irrelevant for interval integrability over `0..b`, because the relevant set is `Ioc 0 b`.

**Key insight:** global classical regularity handles every positive-start window. The only missing time interval is `[0,b]`. Use positivity/initial trace and already available lower-order a priori bounds to dominate the weighted time term near zero. If necessary, state a local-in-time integrable bound on the combined PDE scalar profile; the existing file will convert it to all the derivative-window packages.

## Redundancies and collapses

### `zeroRightDerivative` is mostly subsumed by #6

`P3MoserFTCInfrastructure.lean` shows that closed-energy trace data comes from `IntegratedMoserEnergyWindowFTC` at exponent `2`, plus `IntervalDomainL2SeedZeroRightDerivative`. The right derivative can either remain a tiny endpoint atom or be folded into the same initial-window FTC data. Do not treat it as a separate major PDE frontier.

### `gradientTimeIntegrable` should be derived from `integratedMoserDissipation`

Once #3 is available, `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds` is the intended route. Treat #2 as a derived regularity field, not as a primitive PDE theorem.

### `relativeMassGradient` is a wrapper around landed GN/Young data

The analytic core exists as `unitInterval_regular_power_GNYoung`. The work is interface alignment.

### `quantitativeEndpoint` already has its scalar skeleton

Do not rebuild dyadic products or root-tower estimates. Use `dyadic_root_tower_bound` and focus on deriving the recurrence from the integrated Moser step.

## Efficient attack order

### Step 1 — Close #6 first

Target file:

```text
ShenWork/PDE/P3MoserInitialWindowPDE.lean
```

Suggested theorem shape:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserInitialWindowPDE

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-
Target:

theorem intervalDomain_integratedMoserEnergyWindowFTCGlobalPDEInitialData_of_trace_bounds
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    -- minimal lower-order/a-priori data needed to dominate the combined PDE scalar near zero
    : IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
        params (intervalDomainWithInitialSlice u₀ u) v T p0
-/

end ShenWork.IntervalDomainExistence.P3MoserInitialWindowPDE
```

First prove `atZero` by existing theorem. Then prove `pdeCombinedInitial` via a local domination lemma for the combined PDE profile on `(0,b]`.

### Step 2 — Close #4 relative interpolation

Target file:

```text
ShenWork/PDE/P3MoserRelativeInterpolationDischarge.lean
```

Use:

```text
unitInterval_regular_power_GNYoung
relativeMoserInterpolationBefore_of_massGradient
```

or build a direct wrapper if the old mass-gradient interface is awkward.

### Step 3 — Close #3 integrated dissipation

Target file:

```text
ShenWork/PDE/P3MoserIntegratedDissipationPDE.lean
```

Use:

```text
IntegratedMoserEnergyWindowFTC
LpBootstrapEnergyInequality / interval-domain Lp PDE energy inequality
RelativeMoserInterpolationBefore
scalar_absorb_higherPower_window
IntegratedMoserDissipationDropBefore_of_integrated_energy
```

### Step 4 — Derive #2

Target theorem:

```text
gradientTimeIntegrable_of_integratedMoserDissipationDropBefore
```

Use `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds` to supply integrability of the gradient energy.

### Step 5 — Close #5 quantitative endpoint

Target file:

```text
ShenWork/PDE/P3MoserQuantitativeEndpointDischarge.lean
```

Use:

```text
dyadic_root_tower_bound
intervalDomain_boundedBefore_of_moser_quantitative_endpoint
intervalDomain_boundedBefore_of_moser_iteration_chain_and_quantitative_endpoint
```

The remaining work is deriving the recurrence constants from the already-proved integrated step and GN estimates.

### Step 6 — Assemble

Replace the six separate frontiers with three or four named inputs:

```text
InitialWindowPDEData        -- #6 plus #1
RelativeInterpolationData   -- #4
IntegratedDissipationData   -- #3, then #2 derived
QuantitativeEndpointData    -- #5
```

After #3 derives #2, even `IntegratedDissipationData` can be treated as the main Moser energy atom.

## Final classification table

| Frontier | Already proved under another name? | Hardness | Best action |
|---|---:|---:|---|
| `zeroRightDerivative` | partially: `IntervalDomainL2SeedZeroRightDerivative`, closed-energy partial data | medium / redundant | fold into #6; do not attack first |
| `gradientTimeIntegrable` | transfer and regularity packages exist; raw field carried | derived after #3 | derive from integrated dissipation |
| `integratedMoserDissipation` | predicate and scalar absorption proved | hard | main PDE energy estimate after #4/#6 |
| `relativeMassGradient` | GN/Young core and wrappers exist | medium | package `UnitIntervalPowerGNYoungForMoser` into `RelativeMoserInterpolationBefore` |
| `quantitativeEndpoint` | root-tower and final conversion proved | hard | prove recurrence/root-bound producer |
| `IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData` | exact structure and conversion theorems exist | medium-hard | attack first; reduces to `atZero` + `pdeCombinedInitial` |

## Bottom line

The efficient plan is to stop treating the six names as independent. The repo has already reduced the endpoint/FTC side to `IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData`, and the scalar Moser side to a small set of integrated/relative/endpoint atoms. Close the initial-window FTC package first, wire the existing GN/Young package second, prove the integrated Moser dissipation third, derive gradient-time integrability fourth, and leave the quantitative endpoint as the final Moser-iteration recurrence problem.
