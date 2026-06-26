# Q760 / cron1: dependency graph check for Level0 sub-sorries

Repo inspected: `xiangyazi24/Shen_work`.
Scratch write target: branch `chatgpt-scratch`, file `scratch/_CHATGPT_DROP_cron1.md`.

## Verdict

The proposed graph is **directionally right**, but it is **too linear**. The committed code supports a DAG with shared upstreams, not a single chain where every later node follows from the immediately previous one.

The most important corrections are:

1. `3D` is not implemented as “differentiate `3C`.” It is a sibling theorem from the same `PhysicalResolverJointC2Data` package, using the gradient majorant.
2. `PhysicalResolverJointC2Data` is not obtained from `3B` alone. It comes from `PhysicalSourceTimeC2` through `physicalResolverJointC2Data_of_floor`; producing `PhysicalSourceTimeC2` for the heat trajectory is its own source-coefficient/time-regularity task.
3. `2A-core` is not merely “joint continuity of flux.” In the Level0 file it is joint continuity of the **smooth representative of the chemDiv source**, namely the spatial derivative of the flux representative:

   ```lean
   fun q => deriv
     (ChemDivSpatialC2.chemFluxFun p.β U_cos(q.1) V_cos(q.1)) q.2
   ```

4. `1A` is not a formal consequence of `2A-core`. It needs a **higher-order/second-derivative representative** and compactness. It shares the same smooth-representative route, but at one higher spatial-derivative level.
5. `3G` does not depend on `3F`. Both are downstream of shared physical/iterate/representative data. `3G` is closed by `chemDivMixedTimeDeriv_jointContinuousOn_closed` once a `ChemDivMixedTimeDerivClosedRepr` is available; producing that representative is a separate witness-data route.
6. The heat semigroup `ContDiffAt` theorem is positive-time/local: `heatSemigroup_jointContDiffAt_two` needs `c < s₀`. If the target is literally the global `CoupledChemDivFluxJointC2Hyp.exists_local_slab : ∀ τ`, there is a positive-window mismatch to resolve. For the Level0 use on `[c,T]` with `c>0`, this is fine after window-localizing the chain-rule package.

## Confirmed heat-semigroup lane

Current file:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

The file now uses the cutoff plan and explicitly says §2 has exactly one sorry: the cutoff heat term derivative bound.

The remaining sorry is:

```lean
theorem cutoffHeatTerm_iteratedFDeriv_bound
    ... :
    ‖iteratedFDeriv ℝ k (cutoffHeatTerm u₀ c n) q‖ ≤
      (2 * k + 1) ^ k *
        (unitIntervalCosineEigenvalue n ^ k * M₀ *
          Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)) := by
  ...
  sorry
```

Then the dependency is committed as:

```lean
cutoffHeatTerm_iteratedFDeriv_bound
  → cutoffHeatSeries_contDiff_two
  → heatSeries_eventuallyEq_cutoff
  → heatSemigroup_jointContDiffAt_two
```

The final theorem is:

```lean
theorem heatSemigroup_jointContDiffAt_two
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) (s₀, x₀)
```

So the first part of your graph is correct **for positive-time points**:

```text
Leibniz/cutoff bound
  → heatSemigroup_jointContDiffAt_two
  → sub-sorry 3B, after matching the Level0 heat representation
```

Caveat: `3B` inside `CoupledChemDivFluxFactorJointC2Inputs` is a slab field `∀ τ, ∃ δ, ...`; the heat theorem only gives positive-time local `ContDiffAt`. In the Level0 window `[c,T]` this should be handled by choosing/localizing around points with `s>0`, not by claiming a global all-time heat theorem.

## Physical resolver lane

Current file:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

The relevant source-side package is:

```lean
structure PhysicalSourceTimeC2
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Es : ℕ → ℕ → ℝ) : Prop where
  src_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
  src_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (srcTimeCoeff p u k) t‖ ≤ Es i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant
      (fun i k => intervalNeumannResolverWeight p k * Es i k) m)
```

Producer:

```lean
theorem physicalResolverJointC2Data_of_floor
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

Thus the accurate edge is:

```text
PhysicalSourceTimeC2 for the heat trajectory
  → physicalResolverJointC2Data_of_floor
  → PhysicalResolverJointC2Data
```

not:

```text
3B alone → PhysicalResolverJointC2Data
```

For the heat trajectory, `PhysicalSourceTimeC2` itself should be derived from heat/floor/source coefficient estimates, but it is not just the same theorem as `heatSemigroup_jointContDiffAt_two`.

## Resolver C² fields: 3C and 3D

Current file:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

The physical data package is:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

From it:

```lean
theorem coupledChemical_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) (hx : x ∈ Ioo 0 1) :
    ContDiffAt ℝ 2
      (fun q => intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x)
```

and:

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    (H : PhysicalResolverJointC2Data p u Bt) (hx : x ∈ Ioo 0 1) :
    ContDiffAt ℝ 2
      (fun q => deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

So the corrected dependency is:

```text
PhysicalResolverJointC2Data
  ├─→ 3C via coupledChemical_jointContDiffAt_two
  └─→ 3D via coupledChemical_grad_jointContDiffAt_two
```

`3D` is morally the gradient version of `3C`, but in Lean it is produced directly from `grad_summable`, not by differentiating the statement of `3C`.

## Flux factor lane and 2A-core

Current file:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

`CoupledChemDivFluxFactorJointC2Inputs` has exactly the seven slab fields:

1. per-slab source continuity,
2. joint C² of `u`,
3. joint C² of `v`,
4. joint C² of `∂ₓv`,
5. positivity `0 < 1+v`,
6. time fderiv bridge,
7. mixed time-derivative continuity.

The flux C² step is:

```lean
coupledChemDivFlux_contDiffAt_of_factorJointC2
  (hu_c2 x hx s hs) (hv_c2 x hx s hs) (hgradv_c2 x hx s hs)
  (hbase x hx s hs)
```

So the intended flux-factor part is correct in this form:

```text
3B + 3C + 3D + 3E
  → joint C² of Function.uncurry (coupledChemDivFluxLift p u)
```

But in the Level0 `2A-core` comment, the target is not merely the flux value; it is:

```lean
ContinuousOn
  (fun q => deriv
    (ChemDivSpatialC2.chemFluxFun p.β U_cos(q.1) V_cos(q.1)) q.2)
  (Icc c T ×ˢ Icc 0 1)
```

That is the smooth representative for the chemDiv **source** `∂ₓ flux`. Therefore:

```text
3B + 3C + 3D + 3E
  → flux C² / composition machinery
  → 2A-core, after using the smooth representative and derivative/continuity transfer
```

rather than simply:

```text
3B+3C+3D → joint continuity of flux
```

## 1A is stronger than 2A-core

The Level0 file states `SUB-SORRY 1A` as a uniform pointwise bound on the second derivative, obtained from joint continuity of the second derivative on the compact slab. Its comment requires:

```text
(a1) heat semigroup jointly C⁴
(a2) resolver jointly C⁴
(a3) chemDiv flux composition C² jointly
(a4) secondDeriv agrees with deriv(deriv(flux))
```

So this edge in the proposed graph is too optimistic:

```text
2A-core → 1A
```

A better graph is:

```text
higher-order heat/resolver/flux representative data
  → joint continuity of secondDeriv_s(x)
  → compactness
  → 1A
```

`1A` and `2A-core` share the smooth-representative strategy, but `1A` is not just “the second derivative of 2A-core” unless the higher-order version of the representative has already been proved.

## 3F

Current file:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

The bridge theorem is exactly:

```lean
theorem coupledChemDivFlux_timeBridge_of_physicalJointC2
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_c2 : ∀ x ∈ Ioo 0 1, ∀ s : ℝ,
      ContDiffAt ℝ 2
        (fun q => intervalDomainLift (u q.1) q.2) (s, x))
    (hbase : ∀ s x : ℝ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x)
    (hx : x ∈ Ioo 0 1) :
    (fun y => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
        (s, y) (1, 0))
```

It uses:

```text
PhysicalResolverJointC2Data
  → coupledChemical_jointContDiffAt_two
  → coupledChemical_grad_jointContDiffAt_two
  → coupledChemical_innerCommute_of_physicalJointC2
```

plus `hu_c2` and the floor. So the graph entry for `3F` is correct if expanded as:

```text
PhysicalResolverJointC2Data + 3B/hu_c2 + 3E/floor
  → coupledChemDivFlux_timeBridge_of_physicalJointC2
  → 3F
```

## 3G

Current file:

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

The continuity theorem is:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc 0 1)
```

and:

```lean
def ChemDivMixedTimeDerivClosedRepr ... : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc 0 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

So this part is correct:

```text
ChemDivMixedTimeDerivClosedRepr
  → chemDivMixedTimeDeriv_jointContinuousOn_closed
  → 3G
```

But `3G` should **not** be downstream of `3F`. The representative route is separate. The highest-level producer found earlier is:

```lean
ShenWork.IntervalIterateGradMajorant.chemDivMixedClosedRepr_of_iterateGradSummable
```

which requires:

```text
PhysicalResolverJointC2Data
+ IteratePicardJointC2Data
+ iterate gradient summability
+ floor for the resolver value series
+ boundary agreement at x=0,1
```

So the more accurate edge is:

```text
PhysicalResolverJointC2Data + iterate joint data + HuGrad + floor + boundary
  → ChemDivMixedTimeDerivClosedRepr
  → 3G
```

`3F` and `3G` are siblings: they share upstream physical/heat/floor data but neither one is a prerequisite for the other.

## Independent / side branches

Your “independent” list is mostly right, with wording caveats:

### `2A-agree`

Correct. It is the agreement between `coupledChemDivSourceLift` and the smooth flux-derivative representative on `[0,1]`. The Level0 file describes it as unfolding plus the heat/resolver representation agreements. It is independent of the analytic `2A-core` continuity proof, though it still uses the representation equalities.

### `3A`

Mostly independent from the factor C²/Clairaut pipeline. It is the per-slab source continuity field. But analytically it still relies on the same heat/resolver smoothness and chemDiv composition facts; it is not independent of the heat trajectory itself.

### `3E`

Correct as a side branch. Current committed route is positivity/floor from nonnegative continuous `u` and resolver positivity:

```lean
coupledChemical_floor_pos_of_nonneg_continuous
```

It is not downstream of `3C`/`3D`.

## Corrected DAG

A better dependency graph is:

```text
A. Heat local joint C²
   cutoff/Leibniz bound (only remaining sorry in HeatRegularity)
     → cutoffHeatSeries_contDiff_two
     → heatSemigroup_jointContDiffAt_two
     → 3B / hu_c2  [positive-time local]

B. Resolver physical joint C²
   PhysicalSourceTimeC2 for the heat trajectory
     → physicalResolverJointC2Data_of_floor
     → PhysicalResolverJointC2Data
        ├─→ 3C via coupledChemical_jointContDiffAt_two
        ├─→ 3D via coupledChemical_grad_jointContDiffAt_two
        └─→ inner commute for 3F via coupledChemical_innerCommute_of_physicalJointC2

C. Flux/source joint continuity
   3B + 3C + 3D + 3E
     → flux joint C² / smooth composition
     → 2A-core (joint continuity of ∂ₓ flux representative)
   2A-agree is a separate representation-unfolding agreement.

D. Uniform second-derivative bound
   higher-order heat/resolver/flux representative data (C⁴-level, not merely 2A-core)
     → joint continuity of second derivative on compact slab
     → 1A
   1B then follows from 1A by integral bound.

E. Flux time bridge
   PhysicalResolverJointC2Data + 3B/hu_c2 + 3E/floor
     → coupledChemDivFlux_timeBridge_of_physicalJointC2
     → 3F

F. Mixed time-derivative continuity
   PhysicalResolverJointC2Data + IteratePicardJointC2Data + HuGrad + floor + boundary
     → ChemDivMixedTimeDerivClosedRepr
     → chemDivMixedTimeDeriv_jointContinuousOn_closed
     → 3G
```

## Final answer

The proposed graph is **not wrong as a high-level intuition**, but it should be adjusted before using it as a Lean closure plan. The main fixes are: make `3C` and `3D` parallel children of `PhysicalResolverJointC2Data`; do not treat `PhysicalResolverJointC2Data` as a consequence of `3B` alone; do not treat `1A` as a consequence of `2A-core` alone; and do not put `3G` after `3F`. `3F` and `3G` are separate branches sharing upstream physical/heat/floor data.
