# Q726 (cron2): `coupledChemDivSourceLift` continuity search

Static repo inspection only; I did not run a Lean build.

## Executive verdict

I did **not** find a landed theorem that directly proves the heat-level-0 target

```lean
ContinuousOn
  (Function.uncurry
    (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0)))
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

or the corresponding per-slice statement for the concrete heat trajectory.

What I found is:

1. The exact joint target is already isolated in `IntervalConjugateLevel0BFormSourceOn.lean` as `SUB-SORRY 2A`:

```lean
have hjoint_source_cont :
    ContinuousOn
      (Function.uncurry
        (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0)))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  sorry -- [SUB-SORRY 2A: joint continuity of chemDiv source]
```

2. That file already shows how to get per-slice continuity from the joint statement:

```lean
have hcont_slices : ∀ s ∈ Icc c T,
    ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
      (Icc (0 : ℝ) 1) := by
  intro s hs
  exact ContinuousOn.uncurry_left s hs hjoint_source_cont
```

3. The exact per-slab source-continuity field required by the FAC / local-chain-rule path exists in several `IntervalCoupledRegularityBootstrap` structures, but it is carried as an **input field**, not produced for heat level 0.

4. I found generic helper theorems that **consume** per-slice continuity of `coupledChemDivSourceLift` to get coefficient bounds, and helper theorems that give **coefficient time-continuity**, but not source-lift spatial/joint continuity itself.

So for `[c,T] × [0,1]`, this is still a real lemma to prove. It is not already packaged elsewhere.

## Definition check

`coupledChemDivSourceLift` is defined in:

```text
ShenWork/PDE/IntervalCoupledSourceTimeC1.lean
```

as:

```lean
/-- Lifted chemotaxis-divergence source with the elliptic resolver substituted. -/
def coupledChemDivSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (fun x => intervalDomainChemotaxisDiv p (u s)
      (coupledChemicalConcentration p u s) x)
```

and

```lean
def coupledChemDivSourceCoeffs (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n => cosineCoeffs (coupledChemDivSourceLift p u s) n
```

So your target is exactly continuity of the lifted spatial source slice, not merely continuity of the coefficient family.

Side note: level 0 of the B-form/conjugate Picard iterate is not defined as a clamp to `u₀`; it is definitionally

```lean
| 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
```

in `ShenWork/Paper2/IntervalConjugatePicard.lean`.

## Search results by requested pattern

### 1. `ContinuousOn.*coupledChemDivSourceLift`

Hits are mostly structure fields / hypotheses.

Important `IntervalCoupledRegularityBootstrap` occurrences:

#### `CoupledChemDivPointwiseChainAtoms`

File:

```text
ShenWork/PDE/IntervalChemDivLocalChainRule.lean
```

Field:

```lean
structure CoupledChemDivPointwiseChainAtoms
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    ...
```

The producer `coupledChemDivLocalChainRule_of_pointwiseChainAtoms` just forwards this field; it does not prove it.

#### `CoupledChemDivLocalChainRule`

File:

```text
ShenWork/PDE/IntervalChemDivTimeDerivative.lean
```

Field:

```lean
structure CoupledChemDivLocalChainRule
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    ...
```

Again, this is an input package.

#### `CoupledChemDivOuterCommuteAtoms`

File:

```text
ShenWork/PDE/IntervalChemDivOuterCommute.lean
```

Field:

```lean
structure CoupledChemDivOuterCommuteAtoms
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    ...
```

This file also has the useful interior identity:

```lean
theorem coupledChemDivSourceLift_eq_deriv_fluxLift_interior
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    coupledChemDivSourceLift p u s x =
      deriv (coupledChemDivFluxLift p u s) x
```

That identifies the source with the spatial derivative of the flux on the open interval, but it does not by itself give closed-interval continuity.

#### `CoupledChemDivFluxJointC2Hyp`

File:

```text
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
```

Field:

```lean
structure CoupledChemDivFluxJointC2Hyp
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    ...
```

The producer `coupledChemDivOuterCommuteAtoms_of_fluxJointC2` passes it through.

#### `CoupledChemDivFluxFactorJointC2Inputs`

File:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

Field:

```lean
structure CoupledChemDivFluxFactorJointC2Inputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    ...
```

The theorem `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs` passes this field through as `hsource_cont_slab`.

#### `FACLocalSlabInputs`

File:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
```

Contains the same source-continuity input:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
```

The FAC producer again passes this through; it does not prove source continuity.

#### `ChemDivSolutionRegularityResidual`

File:

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

Its `other` field contains the same per-slab source-continuity input.  This is explicitly part of the residual package.

### 2. `continuousOn.*chemDivSource`

Relevant helpers found:

#### `chemDivSource_weakH2_of_spatialC2`

File:

```text
ShenWork/PDE/IntervalChemDivFluxFACSourceDecay.lean
```

```lean
def chemDivSource_weakH2_of_spatialC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hC2 : ContDiffOn ℝ 2 (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    ... :
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
```

This consumes `ContDiffOn ℝ 2` of the source slice.  Since `ContDiffOn` implies continuity, it is a possible route, but the theorem does not produce `hC2`.

#### `coupledChemDivSource_zeroCoeff_of_uniformSup`

Same file:

```lean
theorem coupledChemDivSource_zeroCoeff_of_uniformSup
    ...
    (hcont : ∀ s, 0 ≤ s →
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    (hsup : ∀ s, 0 ≤ s → ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ Msup) :
    ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ 2 * max B Msup
```

This is a consumer of continuity + sup bound, not a continuity producer.

#### `chemDiv_earlyPoly_of_liftRegularity`

File:

```text
ShenWork/Wiener/EWA/ChemDivUncond.lean
```

```lean
theorem chemDiv_earlyPoly_of_liftRegularity
    ...
    (hLiftCont : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1))
    (hLiftBd : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ M) :
    ∀ s ∈ Set.Icc (0 : ℝ) τ₀, ∀ n,
      |coupledChemDivSourceCoeffs p u s n| ≤ (2 * M) * (1 + (n : ℝ))
```

Again, it consumes per-slice source continuity.

### 3. `chemDivSourceLift.*continuous`

The closest landed result is **coefficient** continuity, not source-lift continuity.

File:

```text
ShenWork/Wiener/EWA/ChemDivGcont.lean
```

```lean
theorem chemDiv_coeff_continuous_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (n : ℕ) :
    Continuous (fun s => coupledChemDivSourceCoeffs p u s n)
```

and

```lean
theorem chemDiv_coeff_timeContinuous
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ n, Continuous (fun s => coupledChemDivSourceCoeffs p u s n)
```

This helps with per-mode coefficient time-continuity, but it does not prove

```lean
ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)
```

or

```lean
ContinuousOn (Function.uncurry (coupledChemDivSourceLift p u)) (... ×ˢ ...)
```

### 4. Theorems in `IntervalCoupledRegularityBootstrap` about source continuity

Found `IntervalCoupledRegularityBootstrap` items are mostly wrappers that carry source continuity as a hypothesis:

```lean
CoupledChemDivPointwiseChainAtoms
CoupledChemDivLocalChainRule
CoupledChemDivOuterCommuteAtoms
CoupledChemDivFluxJointC2Hyp
CoupledChemDivFluxFactorJointC2Inputs
FACLocalSlabInputs
```

The useful non-continuity identity is:

```lean
coupledChemDivSourceLift_eq_deriv_fluxLift_interior
```

which may be useful in proving the source is continuous on `(0,1)` from differentiability/smoothness of the flux, but it does not handle endpoint continuity or joint continuity by itself.

## What this means for heat level 0

For your immediate target on a positive window `[c,T]`, the repo already has the exact local target as the Level0 sub-sorry:

```lean
hjoint_source_cont :
  ContinuousOn
    (Function.uncurry
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0)))
    (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

Once this is proved, per-slice continuity follows immediately by:

```lean
ContinuousOn.uncurry_left s hs hjoint_source_cont
```

But I did not find a reusable theorem already proving this from heat semigroup smoothing + resolver regularity + chemDiv composition.

Suggested proof route from existing pieces:

1. Prove a classical/joint regularity statement for the heat-level fields on `[c,T] × [0,1]`:
   * `u(s,x) = intervalDomainLift (conjugatePicardIter p u₀ 0 s) x`,
   * `v(s,x) = intervalDomainLift (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s) x`,
   * `∂ₓv(s,x)` and enough spatial derivatives.
2. Express the chemDiv source as the spatial derivative of the flux on the interior using:
   ```lean
   coupledChemDivSourceLift_eq_deriv_fluxLift_interior
   ```
3. Handle endpoint continuity separately, probably via the same even/reflect/Neumann boundary machinery already used in the Level0 file for weak-H²/source-decay.
4. Package the result as the joint statement `hjoint_source_cont`; per-slice and sup-bound consumers are already wired.

## Bottom line

No direct landed theorem found for heat-level-0 joint or per-slice continuity of `coupledChemDivSourceLift`.

The exact statement is already isolated as `SUB-SORRY 2A` in `IntervalConjugateLevel0BFormSourceOn.lean`; all other discovered occurrences either:

* carry source continuity as a field/hypothesis, or
* consume it to get coefficient bounds, or
* prove only coefficient time-continuity.
