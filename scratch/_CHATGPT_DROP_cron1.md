# Q3292 (cron1) — five residuals and the Moser boundedness loop

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Executive answer

The current 7-input assembly filler is a valid **wiring theorem**, but it is not a non-circular proof of `hBoundedBefore`.

The cycle is real:

```text
hBoundedBefore
  -> relativeMassGradient
  -> RelativeMoserInterpolationBefore
  -> integratedMoserDissipation
  -> IntegratedMoserFirstCrossingStep
  -> all Lp / quantitative endpoint
  -> hBoundedBefore
```

In `P3MoserAssemblyFiller.lean`, this appears concretely as:

```text
relativeMassGradientCore := intervalDomain_relativeMassGradient_of_classical_boundedBefore ... (hBoundedBefore ...)
```

and then `relativeMassGradientCore` is used to build `hrel`, which is used to build `integratedMoserDissipationCore`, which is part of the residual package later used to obtain boundedness. So 3-4-5 cannot close a **general** Moser boundedness theorem in their current form.

There are two clean paths:

1. **For the constant-solution existence theorem:** do not run this Moser loop. If bounded-before is already trivial from the constructed constant/global solution, pass that direct boundedness into the theorem route and leave the Moser residuals as a separate a priori theorem frontier.
2. **For a genuine Moser a priori theorem:** refactor the loop. The boundedness-dependent `relativeMassGradient` must be replaced by a non-circular relative interpolation/gradient estimate, and the impossible fixed-gap `2 < p*A` must be replaced by a coefficient-flexible integrated drop. Otherwise the theorem is structurally blocked.

The five residuals should be triaged as follows:

```text
#1 hGap: false for the fixed coefficient target; do not try to prove it.
#2 initial-time PDE integrability: real but producible with local/initial regularity, not from bare global-classical interior regularity alone.
#3 crossing step: producer exists, but circular unless fed non-circular dissipation/interpolation.
#4 quantitative endpoint: scalar conversion exists; PDE recurrence data missing.
#5 dyadic recurrence: scalar tower exists; recurrence + pointwise/limit endpoint missing.
```

## (a) Can the circularity in 3-4-5 be broken?

### Current chain: no, not without changing an input

The current filler proves `relativeMassGradientCore` from `hBoundedBefore`:

```lean
have relativeMassGradientCore : ... := by
  intro T rho p0 u v hsol hcross hboot
  exact
    intervalDomain_relativeMassGradient_of_classical_boundedBefore
      hsol hcross hboot
      (hBoundedBefore hsol hcross hboot)
```

That is mathematically exactly the loop. The proof of `hBoundedBefore` cannot depend on a field whose only producer assumes `hBoundedBefore`.

The concrete dependency is in `P3MoserRelativeMassGradientProducer.lean`:

```text
intervalDomain_weightedGradient_rho_le_of_boundedBefore
```

which uses a uniform pointwise/sup bound on `u` to prove

```text
u^rho * u^(p-2)|∇u|² ≤ M^rho * u^(p-2)|∇u|².
```

This is valid, but it is not usable for proving the first `L∞` bound.

### Break route 1: use independent boundedness, if the target is existence

If the existence theorem’s constructed solution is constant and bounded by construction, then use that direct bounded-before proof. Do not route through Moser. This is the fastest way to finish the existence headline, and it is honest.

The Moser assembly then becomes a separate statement:

```text
If bounded-before is supplied, then the integrated-drop residual surface can be filled.
```

That is useful, but it is not an a priori boundedness proof.

### Break route 2: replace boundedness-dependent relativeMassGradient

For a genuine Moser proof, replace the `u^rho ≤ M^rho` step by a GN/Young estimate at the level of the higher power itself:

```text
∫ u^(p+rho)
  ≤ eps * ∫ |∇(u^(p/2))|² + Ceps * lower_order(∫u^p, mass).
```

That estimate is the real relative interpolation. It should be used directly; do not first prove a weighted-gradient comparison requiring `u ≤ M`.

The repo already has related scaffolding:

```text
unitInterval_regular_power_GNYoung
relativeMoserInterpolationBefore_of_massGradient
intervalDomain_massGradientInterpolation_of_classical
MoserMassPowerToCurrentLpLowerOrder
```

But the current `intervalDomain_relativeMassGradient_of_classical_boundedBefore` still includes a boundedness-dependent weighted-gradient component. The non-circular route is to produce `RelativeMoserInterpolationBefore` directly from GN/Young + current `Lp` bootstrap, not from `weightedGradient_rho_le_of_boundedBefore`.

Suggested target:

```lean
import ShenWork.PDE.P3MoserRelativeMassGradientProducer
import ShenWork.PDE.P3MoserLemmaDischarge
import ShenWork.Paper2.IntervalDomainMCL

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRelativeNoBound

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge

/-
Target: no `IsPaper2BoundedBefore` input.

Use the already-proved 1D GN/Young package to produce the relative interpolation
shape directly from the current Lp bootstrap/mass lower-order data.

theorem intervalDomain_relativeMoserInterpolationBefore_of_classical_noBoundedBefore
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    RelativeMoserInterpolationBefore intervalDomain u T rho p0
-/

end ShenWork.IntervalDomainExistence.P3MoserRelativeNoBound
```

If this target is too hard at once, keep the existing `LpMassGradientInterpolationEstimate` but remove the extra `hgrad` field that compares weighted gradients using `u^rho ≤ M^rho`.

### Break route 3: refactor the fixed coefficient gap

The current `hGap` asks for

```text
2 < pExp * Acoef.
```

If the computed coefficient tends to `2` from below, that target is false for large `p`. So the fixed-coefficient dissipation predicate cannot be the universal endpoint.

The code already contains coefficient-parametric infrastructure:

```text
IntegratedMoserDissipationDropBeforeCoeff theta
scalar_absorb_higherPower_window_const
scalar_absorb_higherPower_window
```

but the public route specializes back to coefficient `2`, and `P3MoserIntegratedDissipationPDEv2.lean` encodes the gap at coefficient `2` via `LpBootstrapEnergyInequalityWithGap`.

A non-circular proof should keep a positive coefficient `theta_p` depending on `p`, for example

```text
theta_p = (p * Acoef) / 2
```

when `0 < p*Acoef`. The crossing proof constants then depend on `theta_p`; this is fine if the dyadic endpoint recurrence accounts for it. The important thing is to stop demanding a uniform fixed `2` coefficient if the PDE only gives a coefficient below `2`.

Suggested target:

```lean
import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2
import ShenWork.PDE.P3MoserDissipationShape

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserCoeffFlexible

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape

/-
Replace `LpBootstrapEnergyInequalityWithGap` by a satisfiable positive-coefficient
frontier.

def LpBootstrapEnergyInequalityWithPositiveCoeff
    (D : BoundedDomainData) (u : ℝ → D.Point) (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ theta > 0,
      IntegratedHigherPowerEnergyWindowCoeffFrontier D u T rho p0 theta

Then downstream crossing should consume the coefficient explicitly instead of
requiring `theta = 2`.
-/

end ShenWork.IntervalDomainExistence.P3MoserCoeffFlexible
```

Note: the snippet above is a route sketch. In the actual file, the type should remain `u : ℝ → D.Point → ℝ`; I wrote it compactly to emphasize the API change.

## (b) Item 2: is initial-time regularity genuine or producible?

It is **genuine from the current interface**, but should be **producible from a stronger local/initial regularity package**.

The repo has already reduced the FTC side very sharply. `P3MoserEnergyContinuity.lean` defines:

```text
IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData
```

with exactly two fields:

```text
atZero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
pdeCombinedInitial : IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0
```

and then proves:

```text
intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData
```

So the initial-window problem is not broad anymore.

### `atZero` is already essentially producible

For a re-anchored trajectory, the repository already has:

```text
intervalDomainWithInitialSlice
intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
```

This uses initial trace + paper-positive datum + re-anchoring. So the energy-continuity part is not the hard part.

### `pdeCombinedInitial` is the actual residual

The remaining field is integrability near `t=0` of the combined PDE scalar profile:

```text
q * diffusionIntegral
  - q * (χ₀ * chemotaxisIntegral)
  + q * logisticIntegral
```

The repo has bridges:

```text
intervalDomain_weightedTimeTermInitialWindowIntegrability_of_pdeCombined_initial
intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial
intervalDomain_moserDerivativeInitialWindowIntegrability_of_powerDerivIntegral
```

and positive-start windows are already handled by global classical regularity:

```text
intervalDomain_derivativePositiveStartWindowIntegrability_of_global_classical
```

So only the left endpoint remains.

### Can it be produced from `IsPaper2GlobalClassicalSolution` alone?

No. `IsPaper2GlobalClassicalSolution` gives classical regularity on every positive interval `(0,T)`. It does not give a uniform bound as `t ↓ 0` for the scalar PDE integrands. A function may be smooth on every `(ε,T)` and still have a nonintegrable singularity at `0` unless the local-existence/initial-trace theory supplies a domination.

### What should produce it?

One of:

1. The local existence construction, if it already gives enough near-zero regularity.
2. A mild/semigroup smoothing estimate near zero.
3. A stated local-in-time initial regularity package for the initial datum.

For the current global-classical-only API, keep item 2 as a carried residual. It is not fake; it is exactly the boundary between interior classical regularity and initial-time integrability.

Suggested target:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserInitialTime

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-
Target producer from a genuine local-in-time regularity package, not from bare
`IsPaper2GlobalClassicalSolution` alone.

theorem intervalDomain_pdeCombinedInitial_of_localMildRegularity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hlocal : LocalInitialMoserPDEIntegrability params u v T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0
-/

end ShenWork.IntervalDomainExistence.P3MoserInitialTime
```

## (c) Item 5: gap between scalar tower and full `DyadicMoserEndpointRecurrence`

The scalar tower is already done. `IntervalDomainMoserActualAtoms.lean` proves:

```text
dyadic_root_tower_bound
```

and `P3MoserQuantitativeEndpointDischarge.lean` wires:

```text
DyadicMoserEndpointRecurrence
  -> IntervalDomainMoserQuantitativeEndpoint
```

The gap is exactly the content of `DyadicMoserEndpointRecurrence`:

```text
∃ C terminalIndex,
  1 ≤ C
  ∧ 0 ≤ rootBound 1
  ∧ (∀ k ≥ 1, rootBound(k+1) ≤ dyadicMoserFactor C k * rootBound k)
  ∧ 0 < pSeq(terminalIndex+1)
  ∧ 0 ≤ rootBound(terminalIndex+1)
  ∧ IntervalDomainMoserPointwisePowerControlBefore u T pSeq(terminalIndex+1) rootBound(terminalIndex+1)
```

So the missing pieces are:

### 1. Define the dyadic exponents and root bounds

Typically:

```text
pSeq k = 2^k * pStart
rootBound k = a bound for sup_t (∫ |u(t)|^{pSeq k})^(1/pSeq k)
```

Lean needs these as actual functions with nonnegativity and recurrence proofs.

### 2. Prove the recurrence from the integrated Moser step

The recurrence must have the exact form

```text
rootBound(k+1) ≤ (C * 2^k)^((1/2)^k) * rootBound k.
```

This requires extracting per-step constants from the integrated Moser inequality and showing they grow at most geometrically in `k`. This is PDE/scalar bookkeeping, not covered by `dyadic_root_tower_bound`.

### 3. Produce terminal pointwise power control

This is the most important missing bridge. Finite `Lp` control at one exponent does **not** imply pointwise power control. The terminal field currently asks for:

```text
∀ t x, |u t x|^p ≤ R^p.
```

A full Moser endpoint usually obtains this by passing `p_k → ∞` and using continuity / compactness, or by a high-exponent limit lemma. The current `DyadicMoserEndpointRecurrence` bakes in a finite terminal pointwise-power field, which is stronger than what the scalar root tower directly gives.

Two possible fixes:

1. Prove a limit endpoint theorem:

```text
uniform root bounds for all k + continuity on compact domain
  -> sup bound
  -> pointwise power control for some chosen finite exponent or directly bounded-before
```

2. Refactor `DyadicMoserEndpointRecurrence` so the terminal field is `IsPaper2BoundedBefore` or an all-k root-bound endpoint, not finite-exponent pointwise power control.

Current best target:

```lean
import ShenWork.PDE.P3MoserQuantitativeEndpointDischarge
import ShenWork.PDE.IntervalDomainMoserActualAtoms

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserDyadicEndpoint

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserQuantitativeEndpointDischarge

/-
Target 1: recurrence producer from the integrated Moser step.

theorem dyadicMoserEndpointRecurrence_of_integrated_step_and_root_bounds
    {u : ℝ → intervalDomain.Point → ℝ} {T pStart : ℝ}
    (hstep : DyadicMoserStepInequalities u T pStart)
    (hlimit : DyadicRootBoundsGivePointwiseControl u T pStart) :
    ∃ pSeq rootBound,
      DyadicMoserEndpointRecurrence u T pSeq rootBound

Target 2: if finite terminal pointwise is too strong, replace it by a direct
bounded-before endpoint and then convert to `IntervalDomainMoserQuantitativeEndpoint`.
-/

end ShenWork.IntervalDomainExistence.P3MoserDyadicEndpoint
```

## (d) Dispatch priority

### If the goal is the current existence theorem with constant solutions

Do **not** dispatch 3-4-5 first. They are irrelevant if bounded-before is trivial from the constructed solution. Prioritize:

```text
1. Connect the constant-solution/existence branch directly to bounded-before.
2. Keep hGap and dyadic Moser endpoint as separate a priori frontiers.
3. Do item 2 only if the current theorem path still needs closed-energy/FTC data.
```

This is the fastest path to a clean theorem statement.

### If the goal is a genuine Moser a priori theorem

Dispatch in this order:

#### 0. Fix the false coefficient target

Do this before asking anyone to prove `hGap`. The current fixed gap

```text
2 < pExp * Acoef
```

is false for large `pExp`. Either keep it as an explicit assumption forever, or refactor the integrated drop/crossing step to use a coefficient `theta_p > 0` instead of fixed `2`.

#### 1. Item 2: initial-time PDE integrability

This is non-circular and already sharply isolated. It unlocks FTC/closed trace. It should be produced from local-initial regularity or kept as the only initial-time residual.

#### 2. Non-circular relative interpolation

Replace `intervalDomain_relativeMassGradient_of_classical_boundedBefore` with a producer that does not use `IsPaper2BoundedBefore`. This is the main loop breaker.

#### 3. Integrated dissipation / crossing step

Once coefficient and interpolation are fixed, `P3MoserIntegratedDissipationPDEv2` and `P3MoserThresholdPlanProducer` are mostly wiring.

#### 4. Dyadic recurrence and endpoint

Use the scalar tower already in `IntervalDomainMoserActualAtoms.lean`. Focus on recurrence constants and the final `p→∞`/continuity endpoint.

#### 5. Assembly

Only after the above should the assembly filler be used as a mainline theorem. As currently written, it is a wiring theorem conditional on `hBoundedBefore`, not a proof of `hBoundedBefore`.

## Direct answers

### (a) Can circularity in 3-4-5 be broken?

Not with the current boundedness-dependent `relativeMassGradient` producer. It can be broken either by supplying bounded-before independently, which is fine for the constant-solution existence branch, or by replacing the relative interpolation and fixed-gap APIs with non-circular versions.

### (b) Is item 2 genuine or producible from global classical?

It is genuine for the current `global classical` interface. Positive-time classical regularity does not control the singular behavior at `t=0`. It is producible from local-in-time initial regularity / mild solution estimates / an explicit initial-window integrability package. The repo has already reduced it to `atZero + pdeCombinedInitial`, and `atZero` is essentially done by re-anchoring and trace.

### (c) What is missing for full `DyadicMoserEndpointRecurrence`?

The scalar product/root tower is done. Missing are the PDE recurrence constants, a concrete definition of `pSeq/rootBound`, and the terminal pointwise/limit endpoint converting uniform root bounds into `IntervalDomainMoserPointwisePowerControlBefore` or directly into bounded-before.

### (d) Dispatch priority?

For existence: bypass the Moser loop and use the trivial bounded-before for constant solutions. For the real Moser theorem: first fix the false `hGap` target, then prove item 2, then non-circular relative interpolation, then integrated dissipation/crossing, then dyadic endpoint.

## Bottom line

The current residual set is not “five lemmas away” from a non-circular Moser proof. It contains one false fixed-gap hypothesis and one explicit boundedness loop. Treat the assembly filler as a conditional surface. For the existence theorem, avoid the loop. For the Moser a priori theorem, refactor the coefficient and relative-interpolation interfaces before dispatching proof workers to the dyadic endpoint.
