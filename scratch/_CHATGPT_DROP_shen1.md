# Q2836 (shen1) — can integrated Moser dissipation be proved from current energy APIs?

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Scope: proof audit only; no repository source modifications.

I inspected the current default-branch source around:

- `ShenWork/PDE/P3MoserDissipationShape.lean`
- `ShenWork/PDE/P3MoserIntegratedClosure.lean`
- `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`
- `ShenWork/PDE/P3MoserRegularityProducer.lean`
- `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean`

## Verdict

`IntegratedMoserDissipationDropBefore intervalDomain u T rho p0` is **not currently derivable** from the existing proved API

```lean
intervalDomain_LpBootstrapEnergyInequality_of_regularity
```

plus the current cross-diffusion/bootstrap hypotheses alone. It remains a genuine PDE/integrated-energy frontier.

The current clean threshold-plan route is real and proved:

```lean
P3MoserThresholdPlanProducer.integratedMoserFirstCrossingStep_of_abstract_data
P3MoserThresholdPlanProducer.intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
```

but those theorems consume

```lean
hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

as an input. They do not derive it from the Lp bootstrap energy inequality.

## Exact current API facts

### 1. The integrated dissipation target

In `P3MoserDissipationShape.lean`:

```lean
def IntegratedMoserDissipationDropBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        2 * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))
```

The only packaging theorem there is:

```lean
theorem integratedMoserDissipationDropBefore_of_integrated_energy
    (henergy :
      ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
        ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          ...same integrated inequality...) :
    IntegratedMoserDissipationDropBefore D u T rho p0
```

So the file packages an already-integrated inequality. It does not prove that inequality from the pointwise Lp bootstrap estimate.

### 2. The threshold plan consumes, but does not produce, `hdiss`

In `P3MoserThresholdPlanProducer.lean`:

```lean
theorem integratedMoserFirstCrossingStep_of_abstract_data
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hgrad_nonneg : ... ) :
    IntegratedMoserFirstCrossingStep D u T rho p0
```

and the interval specialization:

```lean
theorem intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

This confirms the clean route is:

```text
regularity + energy nonnegativity + integrated dissipation + relative interpolation
  ==> IntegratedMoserFirstCrossingStep
```

but integrated dissipation remains a separate input.

### 3. What `intervalDomain_LpBootstrapEnergyInequality_of_regularity` gives

In `IntervalDomainLpBootstrapEnergyInequality.lean`, the current theorem is:

```lean
theorem intervalDomain_LpBootstrapEnergyInequality_of_regularity
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    LpBootstrapEnergyInequality intervalDomain u T rho p0
```

Unfolded at use sites, `LpBootstrapEnergyInequality` supplies, for each exponent `p`, constants

```lean
∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L_const, ∀ t, 0 < t → t < T →
  (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x)^p)) t
    + A * G_p(t) + B * Y_p(t)
  ≤ K * Z_p(t) + L_const
```

where

```lean
Y_p(t) = ∫ u(t)^p
G_p(t) = ∫ |∇(u(t)^(p/2))|^2
Z_p(t) = ∫ u(t)^(p+rho)
```

This is a **pointwise differential inequality with a higher-power term on the right**. It is not the same shape as `IntegratedMoserDissipationDropBefore`, which is an **already-integrated** inequality with no `Z_p` term and a fixed `2 * ∫G_p` on the left.

## Why the derivation is not currently available

There are two independent gaps.

### Gap A: differential-to-integrated energy transport

To pass from the pointwise derivative inequality to

```lean
Y_p(t2) - Y_p(t1) + ... ≤ ...
```

Lean needs a fundamental-theorem/absolute-continuity bridge for

```lean
fun t => intervalDomain.integral (fun x => (u t x)^p)
```

on arbitrary `[t1,t2]` inside `[0,T]`. The current regularity package gives closed-time continuity and integrability fields, but it does not include a theorem saying the derivative integrates to the endpoint difference for every exponent.

So even before absorbing `Z_p`, `LpBootstrapEnergyInequality` cannot simply be integrated in Lean from the current APIs.

### Gap B: absorbing the `Z_p` term and normalizing the gradient coefficient

Even if the differential inequality were integrated, it contains

```lean
K * ∫ u^(p+rho)
```

on the right. Removing this term requires an interpolation/absorption input such as `RelativeMoserInterpolationBefore`, with a small epsilon chosen from the energy coefficient.

But `IntegratedMoserDissipationDropBefore` is currently separated from `hrel` in the clean threshold route. If one uses `hrel` to derive `hdiss`, then the route is no longer “energy alone gives dissipation”; it becomes a combined energy+interpolation absorption theorem.

There is also a coefficient issue: the integrated target has exactly

```lean
2 * ∫ G_p
```

on the left. The current `LpBootstrapEnergyInequality` only guarantees some positive coefficient `A`; after multiplying by `p` and absorbing part of the right-hand side, the available gradient coefficient is generally `p*A'`, not definitionally `2`. In the current interval-domain proof, the produced `Acoef` is positive but not advertised as large enough to imply the fixed coefficient `2` target.

This is why the existing route correctly treats `IntegratedMoserDissipationDropBefore` as its own frontier rather than deriving it from the pointwise Lp bootstrap inequality.

## Existing APIs that are close but not enough

### Old nonnegative-B route

`P3MoserDissipationShape.lean` has:

```lean
def MoserDissipationDropBeforeNonnegB ...
theorem moserDissipationDropBeforeNonnegB_of_raw_drop ...
```

and old wrappers:

```lean
moser_step_of_energy_nonnegB_relative_interpolation
moser_iteration_chain_of_energy_nonnegB_relative_interpolation
intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB
intervalDomain_endpointBoundFromLp_of_quantitative_root_tower_nonnegB
```

But this is not the clean threshold-plan route. It is the older pointwise route, and the same file even contains the counterexample:

```lean
theorem unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

which documents that the pointwise drop shape is not a formal consequence of a generic full energy inequality.

### Regularity producer

`P3MoserRegularityProducer.lean` is explicit that regularity fields are still frontier data. It produces regularity/nonnegativity packages from declared regularity data and a classical solution, but its data-assembly theorems still take:

```lean
hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

as a parameter, for example:

```lean
intervalDomain_lowerAverageUpperDataGapData_of_classical
intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
intervalDomain_firstCrossingStep_of_classical_and_upperDataGapFrontiers
intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
```

So regularity/nonnegativity are partially handled; dissipation is not.

## Minimal honest frontier

The minimal honest frontier should remain exactly the integrated dissipation package:

```lean
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

For an interval-domain classical solution route, the reusable residual field should be:

```lean
∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
  IsPaper2ClassicalSolution intervalDomain params T u v →
  CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
  AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0 →
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

This is the smallest non-stale field used by the current threshold-plan route. It should not be replaced by `LpBootstrapEnergyInequality` unless one proves the missing integrated absorption theorem below.

## If you want to prove it: missing theorem shape

The real missing theorem is an **integrated absorbed Lp-energy estimate**, not another wrapper. A good target statement is:

```lean
theorem intervalDomain_integratedMoserDissipationDropBefore_of_regularity
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    -- either include hrel here, or prove a separate higher-power absorption estimate
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    -- plus the missing FTC/absolute-continuity bridge for Y_p
    (hY_ac : ∀ p, p0 ≤ p →
      ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
        ∫ s in t1..t2,
          deriv (fun τ => intervalDomain.integral (fun x => (u τ x)^p)) s =
        intervalDomain.integral (fun x => (u t2 x)^p) -
          intervalDomain.integral (fun x => (u t1 x)^p)) :
    IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 := by
  -- use intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
  -- choose epsilon from the energy coefficient and hrel
  -- integrate the pointwise inequality using hY_ac
  -- absorb Z and dominate constants/Y terms by C*p*∫ max 1 Y
  -- coefficient-normalization issue must be solved or included in the lemma hypotheses
```

However, because of the fixed `2 * ∫G` coefficient in `IntegratedMoserDissipationDropBefore`, the above theorem may still need a stronger integrated energy input than the current `LpBootstrapEnergyInequality` exposes. A more faithful frontier is therefore:

```lean
def IntervalDomainIntegratedMoserEnergyEstimate
    (params : CM2Params) (u : ℝ → intervalDomain.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      intervalDomain.integral (fun x => (u t2 x)^p) -
          intervalDomain.integral (fun x => (u t1 x)^p) +
        2 * ∫ s in t1..t2,
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u s y)^(p / 2)) x)^2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (intervalDomain.integral (fun x => (u s x)^p))
```

Then the existing theorem

```lean
integratedMoserDissipationDropBefore_of_integrated_energy
```

immediately packages it.

## Recommended next Lean attack order

1. **Prove a scalar/integral absorption lemma independent of PDE.**
   Given an already-integrated inequality with `∫Z` on the right and a relative interpolation estimate, prove the `C*p*∫max(1,Y)` form. This isolates coefficient bookkeeping.

2. **Prove the FTC/absolute-continuity bridge for `Y_p`.**
   Target the exact endpoint-difference formula for
   `t ↦ intervalDomain.integral (fun x => (u t x)^p)` on `[t1,t2]`.

3. **Only then try to connect `intervalDomain_LpBootstrapEnergyInequality_of_regularity` to integrated dissipation.**
   At that point, check whether the current positive coefficient `Acoef` is strong enough to produce the fixed `2 * ∫G` target. If not, either strengthen the PDE energy theorem to produce the exact integrated coefficient or weaken/parameterize the integrated dissipation predicate.

## Bottom line

Current status: **not provable from existing APIs as-is**.

`intervalDomain_LpBootstrapEnergyInequality_of_regularity` is a proved pointwise differential inequality and is useful, but the threshold-plan `hdiss` input is an already-integrated, absorbed dissipation estimate. The missing piece is a genuine integrated PDE energy/absorption theorem. Until that theorem exists, keep `IntegratedMoserDissipationDropBefore intervalDomain u T rho p0` as an honest frontier field.
