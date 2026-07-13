ANSWER Q4596 3987b91b

# Executive verdict

The advertised finite chain is **not unconditionally closed** on the current `chatgpt-scratch` branch.

The cleanest repository-accurate dependency graph is:

```text
signal-weighted elliptic estimate with gain rho = gamma
+ finite L^p0 seed
        |
        v
AbstractLpBootstrapHypothesis
        |
        +--> intervalDomain_LpBootstrapEnergyInequality_of_regularity   [CLOSED]
        |
        v
IntegratedMoserFirstCrossingStep / corrected Moser iteration           [OPEN]
        |
        v
Corollary_2_1 intervalDomain p                                         [CONDITIONAL]
        |
        v
one high finite-P bound
        |
        v
Proposition_2_5 intervalDomain p                                       [OPEN]
        |
        v
IsPaper2BoundedBefore
        |
        v
global extension                                                        [EXPLICIT CAUCHY INPUT]
        |
        v
critical all-time uniform bound (`hcriticalGlobalBound`)               [OPEN]
        |
        v
Theorem_1_2 intervalDomain p
```

There are therefore **three independent analytic blockers in the finite-horizon chain**—the critical seed/gain wiring, the all-finite-`Lp` Moser step, and the `Proposition_2_5` endpoint—and then a **fourth, separate all-time blocker** after global extension.

The pointwise-gradient issue is real for the direct one-dimensional Agmon route. The semigroup route would avoid that issue mathematically, but the repository currently contains only the linear heat `Lp -> Linfty` helper, not the nonlinear restarted Duhamel theorem needed to prove `Proposition_2_5`.

Audit target: `xiangyazi24/Shen_work`, branch `chatgpt-scratch`.

# 1. `Lemma_2_6`: exact type and what the weighted seed does not provide

## 1.1 Exact statement-layer type

In `ShenWork/Paper2/Statements.lean`, the relevant types are:

```lean
def AbstractLpBootstrapHypothesis
    (D : BoundedDomainData) (u : R -> D.Point -> R)
    (N T rho p0 : R) : Prop :=
  0 < rho ∧
  0 < T ∧
  max 1 (rho * N / 2) < p0 ∧
  LpPowerBoundedBefore D p0 T u


def Lemma_2_6 (D : BoundedDomainData) : Prop :=
  forall N > 0,
  forall u : R -> D.Point -> R,
  forall T rho p0,
    AbstractLpBootstrapHypothesis D u N T rho p0 ->
    LpBootstrapEnergyInequality D u T rho p0 ->
    forall pExp > 1,
      LpPowerBoundedBefore D pExp T u
```

So `Lemma_2_6` itself does **not** mention a pointwise spatial-gradient bound, a sup bound, or initial endpoint data. Its two payloads are:

1. the seed package `AbstractLpBootstrapHypothesis`; and
2. the complete per-exponent `LpBootstrapEnergyInequality`.

## 1.2 The generic `Lp` energy producer is closed

A positive result of this audit is that the second payload is now genuinely produced. In
`ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean`:

```lean
theorem intervalDomain_LpBootstrapEnergyInequality_of_regularity
    {params : CM2Params} {T rho p0 : R}
    {u v : R -> intervalDomain.Point -> R}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate
      intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis
      intervalDomain u (params.N : R) T rho p0) :
    LpBootstrapEnergyInequality intervalDomain u T rho p0
```

This theorem supplies, from classical regularity plus `hcross` and `hboot`:

- time differentiation of the `Lp` energy;
- insertion of the PDE under the spatial integral;
- Neumann integration by parts;
- diffusion coercivity;
- the real-power Moser-gradient chain rule;
- power integrability and positivity;
- the elementary lower-order comparison.

Thus **`hEnergyFromCrossDiffusion` is no longer the deepest unresolved leaf**. It can be instantiated by the theorem above.

## 1.3 The remaining `Lemma_2_6` burden

The interval-specific constructor in
`ShenWork/Paper2/IntervalDomainTheorem11.lean` is still conditional:

```lean
theorem Lemma_2_6_intervalDomain_of_mass_gradient_frontier
    (cGrad : ...)
    (hdiss : ...)
    (hcGrad : ...)
    (hMG : ...)
    (hgrad : ...)
    (hmass : ...)
    (hu_nonneg : ...)
    (hpow_int : ...) :
    Lemma_2_6 intervalDomain
```

Its substantive inputs are:

```lean
hdiss : MoserDissipationDropBefore-like closure
hMG   : LpMassGradientInterpolationEstimate at every p >= p0
hgrad : weighted-gradient to grad(u^(p/2)) comparison
hmass : uniform control of the mass-power lower-order term
```

The chain-rule, positivity, and power-integrability pieces are now available from `hsol`; mass comes from the mass estimate. The unresolved core is the actual **one-step Moser propagation**, not the bare PDE energy identity.

The newer and cleaner repository interface is the integrated one in
`ShenWork/PDE/P3MoserIntegratedClosure.lean`:

```lean
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : R -> D.Point -> R)
    (T rho p0 : R) : Prop :=
  forall p, p0 <= p ->
    LpPowerBoundedBefore D p T u ->
      LpPowerBoundedBefore D (p + rho) T u
```

The exact producer still missing from the all-`Lp` route has the following natural signature, which is already the explicit `hstep` argument of
`intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms`:

```lean
-- Missing analytic producer.
theorem intervalDomain_integratedMoserFirstCrossingStep_of_classical
    {params : CM2Params} {T rho p0 : R}
    {u v : R -> intervalDomain.Point -> R}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate
      intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis
      intervalDomain u (params.N : R) T rho p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

Internally, the current integrated framework shows the load-bearing subleaves:

```lean
IntegratedMoserEnergyWindowFTC
IntegratedMoserEnergyDerivativeWindowIntegrability
IntegratedHigherPowerEnergyWindowCoeffFrontier
RelativeMoserInterpolationBefore
```

`P3MoserIntegratedClosure.lean` explicitly says that continuity and time-integrability of the energy do not by themselves give the window FTC or integrability of its derivative.

Moreover, `ShenWork/PDE/P3MoserLemmaDischarge.lean` proves an adversarial counterexample:

```lean
LpBootstrapEnergyInequality_does_not_imply_MoserDissipationDropBefore
```

So the missing dissipation/first-crossing step cannot be dismissed as algebra already contained in the energy inequality.

### Status for question (1)

**REAL GAP.**

The signal-weighted estimate plus finite seed can provide `hcross` and `hboot`; and `intervalDomain_LpBootstrapEnergyInequality_of_regularity` then provides the PDE energy family. They do **not** by themselves inhabit `Lemma_2_6 intervalDomain`. A corrected integrated first-crossing producer, or the equivalent corrected dissipation plus relative-interpolation package, is still required.

## 1.4 Critical fidelity issue: `rho = gamma`, not the default `2*gamma`

For the paper-critical seed

```text
max {1, gamma/2} < p0 < (2*beta - 1)/chi0
```

the cross-diffusion gain must be

```lean
rho := params.gamma
```

on the interval `N = 1`, because the abstract seed condition is

```lean
p0 > max 1 (rho * N / 2).
```

The repository's generic classical producer used in several Moser wrappers instead chooses

```lean
rho := 2 * params.gamma
```

—for example `abstract_prop25_bootstrap_two_gamma` and the corresponding endpoint route in `P3MoserActualWiring.lean`. That choice asks for `p0 > gamma*N`, not `p0 > gamma*N/2`, and therefore does **not** recover the paper's critical interval.

Consequently the weighted resolver estimate must be wired all the way to a distinct theorem of the form

```lean
CrossDiffusionBootstrapEstimate intervalDomain params T params.gamma u v
```

before the advertised critical seed can inhabit `hcriticalBootstrap`. The default `rho = 2*gamma` producer is not a faithful substitute.

# 2. Pointwise versus time-integrated gradient control

## 2.1 The direct one-dimensional Agmon route really has a pointwise gap

`ShenWork/PDE/IntervalDomain1DLinfRoute.lean` is explicit about this. It defines:

```lean
def IntervalDomainPointwiseMoserGradientBoundBefore
    (u : R -> intervalDomain.Point -> R) (T pExp : R) : Prop :=
  exists M_diss : R,
    0 <= M_diss ∧
    forall t, 0 < t -> t < T ->
      intervalDomain.integral (fun x =>
        (intervalDomain.gradNorm
          (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) <= M_diss
```

and the concrete producer is:

```lean
theorem intervalDomain_Proposition_2_5_1d
    (params : CM2Params)
    (hlogistic_dominates : 2 * params.gamma < params.alpha)
    (hPointwiseGradient :
      forall {T u v},
        IsPaper2ClassicalSolution intervalDomain params T u v ->
        forall pExp,
          max params.N (max (params.m * params.N)
            (params.gamma * params.N)) < pExp ->
          LpPowerBoundedBefore intervalDomain pExp T u ->
          2 * params.gamma < params.alpha ->
          IntervalDomainPointwiseMoserGradientBoundBefore u T pExp) :
    Proposition_2_5 intervalDomain params
```

A time-integrated estimate

```text
integral_0^T G_p(t) dt <= C
```

does not imply

```text
sup_{0<t<T} G_p(t) <= C'.
```

Narrow temporal spikes are the elementary obstruction. No amount of algebraic rewriting turns the existing integrated dissipation into the pointwise hypothesis consumed by `intervalDomain_Linf_of_Lp_and_gradient`.

The direct Agmon route is also restricted by the extra assumption

```lean
2 * gamma < alpha,
```

which is not the general critical `m = 1`, `chi0 < chiBeta` regime.

### Status

**REAL GAP.** The exact missing input is

```lean
IntervalDomainPointwiseMoserGradientBoundBefore u T pExp
```

for each high exponent used in the endpoint theorem.

## 2.2 Does the semigroup `Proposition_2_5` route avoid it?

Mathematically, yes: the standard restarted mild/Duhamel proof can use one high finite `P` and heat-semigroup smoothing, with no pointwise `G_P` estimate.

Repository-wise, however, that nonlinear theorem is not present.

`ShenWork/Paper2/IntervalDomainLPI.lean` proves only the homogeneous linear helper:

```lean
intervalDomainHeat_Lp_Linfty_pointwise_from_memLp
intervalDomainHeat_Lp_Linfty_bound_from_memLp
intervalDomainSemigroupEstimateData_Lp_Linfty_bound_from_memLp
```

The file explicitly says that it **does not manufacture `prop25`**. Its only `Proposition_2_5` constructor is:

```lean
theorem Proposition_2_5_intervalDomain_of_structured_moser_data
    (hdata : ... -> IntervalDomainStructuredMoserBootstrapData u Tmax) :
    Proposition_2_5 intervalDomain p
```

which simply moves the missing endpoint into `hdata`.

A genuine semigroup proof would need a new theorem discharging all of the following at once:

- a restart mild identity at some positive `s < t`;
- the homogeneous `Lp -> Linfty` estimate;
- the divergence/gradient semigroup estimate for the chemotaxis Duhamel leg;
- `u^gamma` and resolver-gradient bounds at the chosen finite exponent;
- logistic-source integrability;
- integrability of the singular time kernels;
- constants uniform for all `0 < t < T`, with the short initial interval controlled from `InitialTrace`.

A paste-ready target is:

```lean
theorem intervalDomain_Proposition_2_5_of_restarted_mild_Lp_smoothing
    (params : CM2Params)
    (hrestart : IntervalDomainRestartedMildIdentity params)
    (hheat : IntervalDomainHeatLpToLinfty)
    (hdivHeat : IntervalDomainDivergenceHeatLpToLinfty)
    (hresolver : IntervalDomainResolverGradientFromFiniteLp params)
    (hsource : IntervalDomainFiniteLpSourceControl params) :
    Proposition_2_5 intervalDomain params
```

The names of the auxiliary structures can vary; the important point is that the current linear `LPI` lemma is only one field of this package.

## 2.3 Which endpoint route is currently gap-free?

**Neither.**

- The direct Agmon route requires the unproved pointwise gradient bound and `2*gamma < alpha`.
- The Moser endpoint route requires a quantitative root-tower endpoint; the older `MCL` route additionally assumes `OldUnitIntervalPowerGNYoungForMoser`, which its own file states is false for constant functions.
- The semigroup file proves only the linear heat estimate and does not treat the nonlinear Duhamel terms.

For the paper-critical branch, the **semigroup/restart route is the cleaner target** because it avoids upgrading integrated dissipation to a pointwise spatial-gradient bound. But it still needs to be built.

# 3. Initial trace and the `0 < t < T` endpoint

## 3.1 No hidden endpoint requirement in `boundedBefore_of_corollary21_and_proposition25`

The core predicates in `Statements.lean` are open-time predicates:

```lean
def LpPowerBoundedBefore D pExp Tmax u : Prop :=
  exists C, forall t, 0 < t -> t < Tmax ->
    D.integral (fun x => (u t x) ^ pExp) <= C


def IsPaper2BoundedBefore D Tmax u : Prop :=
  exists M, forall t, 0 < t -> t < Tmax ->
    D.supNorm (u t) <= M
```

The exact `InitialTrace` is also one-sided and does not assert definitional equality at `t = 0`:

```lean
def InitialTrace D u0 u : Prop :=
  forall eps > 0, exists delta > 0,
    forall t, 0 < t -> t < delta ->
      D.supNorm (fun x => u t x - u0 x) < eps
```

`boundedBefore_of_corollary21_and_proposition25` needs `InitialTrace` only because `Proposition_2_5` is stated with it. The conclusion samples only `0 < t < T`. It does not ask for `u 0`, a derivative at zero, or a closed-time classical solution.

Thus the specific concern

```text
Does boundedBefore -> boundedBefore secretly need H1InitialEndpointData?
```

has the answer:

**No. This is a non-issue at the statement-assembly level.**

`H1InitialEndpointData` belongs to the separate chi-nonpositive H1 bridge machinery and is not a hidden payload of the Theorem 1.2 finite-`Lp` handoff.

## 3.2 Where endpoint data really reappears

The unfinished integrated-Moser implementation introduces closed-time structures such as:

```lean
structure IntegratedMoserFirstCrossingRegularity ... where
  energyContinuous : forall p >= p0,
    ContinuousOn Y_p (Set.Icc 0 T)
  initialPowerBound : forall p >= p0,
    exists C0, ... Y_p 0 <= C0
  ...

structure IntegratedMoserEnergyWindowFTC ... where
  deriv_intervalIntegrable : ...
  window_ftc : ...
```

These are producer-level requirements, not requirements of `LpPowerBoundedBefore` itself.

The repository even records the issue in `IntervalDomainMoserLadderAtoms.lean`: the current classical-solution interface does not determine the arbitrary value `u 0`, so `l2SeedRegularity` remains explicit.

This endpoint problem can be handled without an H1 package:

1. define a representative `w` with `w 0 = u0` and `w t = u t` for positive times;
2. use `InitialTrace` plus boundedness/integrability of `u0` to prove `Y_p(t) -> Y_p(0)`;
3. use positive-time locality (`LpPowerBoundedBefore_congr_pos` and the corresponding integrated-step congruence lemmas) to transfer the result back to `u`.

The missing reusable bridge would have a shape such as:

```lean
theorem integratedMoserEnergyWindowFTC_of_classical_initialTrace
    {params : CM2Params} {T p0 : R}
    {u0 : intervalDomain.Point -> R}
    {u v : R -> intervalDomain.Point -> R}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u0 u)
    (hu0 : IntervalIntegrablePowerFamily u0 p0) :
    exists w,
      EqOnPositiveTimesBefore T u w ∧
      IntegratedMoserEnergyWindowFTC intervalDomain w T p0
```

### Status for question (3)

- **Final `boundedBefore` assembly:** NON-ISSUE.
- **Current integrated-Moser producer:** REAL but lower-level endpoint/FTC gap, already part of the unresolved Lemma 2.6 step.
- **Need for `H1InitialEndpointData`:** NO.

# 4. Conditional and `of_assumed_*` escape paths

## 4.1 `IntervalDomainTierChain.lean` is explicitly conditional

The file's own header says that it keeps every unproved analytic input explicit. Its principal theorem takes, among other arguments:

```lean
hGN
hdiss
hcGrad
hMG
hgrad
hmass
hu_nonneg
hpow_int
hEnergyFromCrossDiffusion
hProp25
hexist
hbootstrap
```

and only then returns:

```lean
Lemma_2_6 intervalDomain ∧
Lemma_4_1 intervalDomain p ∧
Corollary_2_1 intervalDomain p ∧
Theorem_1_1 intervalDomain p
```

This is useful dependency wiring, but it is not an unconditional discharge.

The energy argument has improved since that wrapper was written: `hEnergyFromCrossDiffusion` can now be filled by
`intervalDomain_LpBootstrapEnergyInequality_of_regularity`. The remaining frontiers do not disappear.

## 4.2 `hProp25` is still a direct hypothesis

Every Theorem 1.2 constructor in `IntervalDomainTheorem12.lean` takes:

```lean
hProp25 : Proposition_2_5 intervalDomain p
```

No theorem in the audited route supplies it without further analytic inputs.

The existing candidate producers remain conditional:

```lean
intervalDomain_Proposition_2_5_1d
  -- requires pointwise Moser-gradient control and 2*gamma < alpha

Proposition_2_5_intervalDomain_of_MCL_frontiers
  -- requires dissipation, a quantitative endpoint,
  -- and OldUnitIntervalPowerGNYoungForMoser (declared false)

intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
  -- requires IntegratedMoserFirstCrossingStep and a quantitative endpoint

Proposition_2_5_intervalDomain_of_structured_moser_data
  -- requires the entire structured data producer
```

So `hProp25` is a genuine unresolved payload, not a theorem already available from the heat estimate.

## 4.3 `hcriticalBootstrap` is still explicit

The critical branch of `IntervalDomainTheorem12.lean` requires:

```lean
hcriticalBootstrap :
  0 <= p.a -> 0 <= p.b -> 1 <= p.beta ->
  p.m = 1 -> p.chi0 < chiBeta p ->
  forall u0, PositiveInitialDatum intervalDomain u0 ->
  forall T > 0, forall u v,
    IsPaper2ClassicalSolution intervalDomain p T u v ->
    InitialTrace intervalDomain u0 u ->
      exists rho > 0,
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
        exists p0 > max 1 (rho * (p.N : R) / 2),
          LpPowerBoundedBefore intervalDomain p0 T u
```

The weighted elliptic mathematics from Q4589 is the correct route to this field, but the branch currently still receives the field as an argument. In particular, it must produce the **`rho = gamma`** cross-diffusion estimate; merely invoking the repository's generic `rho = 2*gamma` estimate does not recover the paper threshold.

### Status

**REAL GAP unless a new weighted-seed producer is added and explicitly wired here.**

## 4.4 The final hidden blocker: `hcriticalGlobalBound`

Even granting all finite-horizon steps, the critical theorem still has another independent argument:

```lean
hcriticalGlobalBound :
  0 <= p.a -> 0 <= p.b -> 1 <= p.beta ->
  p.m = 1 -> p.chi0 < chiBeta p ->
  forall u0, PositiveInitialDatum intervalDomain u0 ->
  forall u v,
    IsPaper2GlobalClassicalSolution intervalDomain p u v ->
    InitialTrace intervalDomain u0 u ->
    (forall T > 0,
      exists rho > 0,
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
        exists p0 > max 1 (rho * (p.N : R) / 2),
          LpPowerBoundedBefore intervalDomain p0 T u) ->
      IsPaper2Bounded intervalDomain u
```

This matters because

```lean
forall T > 0, IsPaper2BoundedBefore intervalDomain T u
```

allows the bound to depend on `T`; it does **not** yield one eventual-in-time constant. Global extension gives existence of the orbit, not uniform boundedness of that orbit.

The final proof uses `Theorem_1_2.of_assumed_solutions_branch`. This is a valid structural constructor, not an axiom, but it makes the conditionality transparent: the theorem is only as unconditional as `hcriticalBootstrap`, `hProp25`, `hglobalExtension`, and `hcriticalGlobalBound` supplied to it.

### Status

**REAL GAP, and a logically separate one from all finite-horizon Moser work.**

# 5. Severity ranking

## Severity 1 — fatal final-theorem blocker

### `hcriticalGlobalBound`

Even a perfect finite-horizon chain and global continuation do not prove `IsPaper2Bounded`. A uniform-in-time absorbing estimate is still required.

## Severity 2 — fatal finite-horizon endpoint blocker

### `Proposition_2_5 intervalDomain p`

No current producer is unconditional:

- direct Agmon needs `IntervalDomainPointwiseMoserGradientBoundBefore` and `2*gamma < alpha`;
- structured Moser needs the quantitative endpoint/root tower;
- the old MCL interpolation assumption is false;
- LPI supplies only the homogeneous heat estimate, not nonlinear Duhamel smoothing.

This prevents the high finite-`P` bound from becoming `IsPaper2BoundedBefore`.

## Severity 3 — fatal all-finite-`Lp` blocker

### Integrated Moser first-crossing / corrected Lemma 2.6 producer

The PDE `LpBootstrapEnergyInequality` is closed, but the one-step propagation

```lean
Lp(p) -> Lp(p + rho)
```

is still an explicit analytic atom. The window FTC, derivative integrability, relative interpolation, and first-crossing closure are not all produced.

## Severity 4 — entry blocker and fidelity issue

### Critical weighted seed with `rho = gamma`

`hcriticalBootstrap` remains an explicit theorem argument. The paper-critical interval requires `rho = gamma`; the generic `rho = 2*gamma` route has the wrong seed threshold.

## Severity 5 — Cauchy-theory wiring

### `hlocal` / `hglobalExtension`

These are still explicit in `IntervalDomainTheorem12.lean`. They may be supplied by other Cauchy-theory work, but this file does not prove them.

## Severity 6 — not a final-assembly gap

### Initial endpoint / H1 data

The open-time `LpPowerBoundedBefore` and `IsPaper2BoundedBefore` predicates do not require it. A closed-time energy/FTC bridge is needed only inside the unfinished integrated-Moser producer and can be built from `InitialTrace` using a positive-time-equivalent representative.

# 6. Per-question status table

| Audit item | Verdict | Exact reason |
|---|---|---|
| Signal-weighted estimate + finite seed fully discharge `Lemma_2_6` | **REAL GAP** | They give `hcross`/`hboot` and hence the PDE energy family, but not `IntegratedMoserFirstCrossingStep` or the equivalent corrected dissipation/interpolation package. |
| Extra pointwise bound hidden in the statement of `Lemma_2_6` | **NON-ISSUE** | The abstract statement has only `hboot` and `LpBootstrapEnergyInequality`; the pointwise-gradient requirement belongs to one particular `Proposition_2_5` route. |
| Direct one-dimensional Agmon endpoint | **REAL GAP** | Requires `IntervalDomainPointwiseMoserGradientBoundBefore`; integrated dissipation does not imply it. |
| Existing semigroup `Proposition_2_5` endpoint | **REAL GAP** | Only the linear heat `Lp -> Linfty` helper is proved; restarted nonlinear Duhamel estimates are not assembled. |
| InitialTrace / `(0,T)` versus `[0,T]` in `boundedBefore` assembly | **NON-ISSUE** | All relevant final predicates quantify over `0 < t < T`. |
| Closed-time endpoint inside integrated Moser | **REAL SUBGAP** | `IntegratedMoserEnergyWindowFTC` and initial-power continuity remain producer inputs; no H1 package is required, but a trace-to-energy bridge is. |
| `hEnergyFromCrossDiffusion` | **CLOSED** | Filled by `intervalDomain_LpBootstrapEnergyInequality_of_regularity`. |
| TierChain / final `of_assumed_*` path | **CONDITIONAL, not a closure** | Explicit frontiers are passed through; `hProp25`, `hcriticalBootstrap`, Cauchy theory, and `hcriticalGlobalBound` remain hypotheses. |

# Final adversarial conclusion

The intended paper chain is mathematically coherent, but the current Lean repository has **not yet reached the unconditional Theorem 1.2 endpoint**.

The shortest faithful execution order is:

```text
A. Build the weighted critical seed with rho = gamma.
B. Build the integrated first-crossing Moser producer
   (including per-exponent window FTC and relative interpolation).
C. Build Proposition_2_5 by restarted semigroup/Duhamel smoothing
   — preferable to the pointwise-gradient Agmon route.
D. Use boundedBefore_of_corollary21_and_proposition25.
E. Supply the Cauchy continuation/gluing theorem.
F. Prove one all-time absorbing bound, i.e. hcriticalGlobalBound.
G. Apply the existing Theorem_1_2 assembly.
```

Steps A–C close the finite-horizon chain. Step F is still indispensable: it cannot be replaced by reapplying finite-horizon estimates with constants depending on the horizon.