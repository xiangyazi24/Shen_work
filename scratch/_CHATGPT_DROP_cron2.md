# Q759 (cron2): Level0 sub-sorry producer status

Static repo inspection only; I did not run a Lean build.

## Verdict table

Your list is mostly right. Main corrections:

* `3D` has a named existing producer: `coupledChemical_grad_jointContDiffAt_two`.
* `3A` appears to remain an explicit slab input; I did not find a standalone generic producer that closes it.
* `2A-agree` has the named interior theorem, but that theorem alone is not the full `Icc 0 1` agreement target.
* `3E` has both the low-level resolver nonnegativity theorem and a coupled-floor wrapper that is closer to the FAC field.

## Per sub-sorry

### 1A — joint pointwise bound of `secondDeriv`

Status: **no existing complete producer found**.

There are per-slice spatial tools:

```lean
chemFluxDeriv_contDiff_two
chemDivLift_contDiffOn_two_of_global
chemDivSource_weakH2_of_cosineRep
```

Files:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
ShenWork/PDE/IntervalChemDivFluxFACSourceDecay.lean
```

But I did not find a named theorem that produces the needed **joint-in-`(s,x)` pointwise bound** for the chosen `secondDeriv` on `[c,T] × [0,1]`. The expected route is still: produce a jointly continuous representative of the relevant second derivative, then use compactness to get the bound.

### 2A-core — joint continuity of the smooth flux derivative

Status: **no existing complete producer found**.

Relevant partial tools exist:

```lean
chemFlux_contDiff_three
chemFluxDeriv_contDiff_two
coupledChemDivFlux_contDiffAt_of_factorJointC2
```

Files:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

But these are not a ready-made producer for the exact Level0 target:

```lean
ContinuousOn
  (fun q : ℝ × ℝ => deriv (chemFluxFun ... time-dependent factors ...) q.2)
  (Icc c T ×ˢ Icc 0 1)
```

So your “needs joint C²/C³ of flux factors → no existing producer” assessment is correct.

### 2A-agree — agreement of `coupledChemDivSourceLift` with smooth flux derivative

Status: **partial existing theorem only**.

Existing theorem:

```lean
coupledChemDivSourceLift_eq_deriv_fluxLift_interior
```

File:

```text
ShenWork/PDE/IntervalChemDivOuterCommute.lean
```

It proves the interior statement:

```lean
x ∈ Ioo (0 : ℝ) 1 →
  coupledChemDivSourceLift p u s x = deriv (coupledChemDivFluxLift p u s) x
```

Correction: this is **interior only**. The Level0 `2A-agree` target in `IntervalConjugateLevel0BFormSourceOn.lean` is stated on `Icc 0 1`, so endpoints still need either a separate endpoint argument, a continuity/closure transfer, or a stronger agreement lemma.

Nearby useful pattern:

```lean
chemDivLift_contDiffOn_two_of_global
```

in

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

It contains an `Icc` agreement by unfolding `chemDivLift` against `deriv (chemFluxFun ...)`, but it is for the per-slice `chemDivLift p u v`/`intervalDomainLift` setup, not directly the Level0 smooth-representative agreement.

### 3A — per-slab source continuity

Status: **no standalone generic producer found**.

This field is still carried explicitly in several slab packages, e.g.

```lean
FACLocalSlabInputs
CoupledChemDivFluxFactorJointC2Inputs_of_physical
coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

Files:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

For Level0, this should be derivable from either `2A-core`/joint source continuity or per-slice `ContDiffOn` of the source, but I did not find a named theorem closing exactly:

```lean
∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)
```

### 3B — heat joint C²

Status: **existing but still depends on the cutoff Leibniz sorry**.

Existing theorem:

```lean
heatSemigroup_jointContDiffAt_two
```

File:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

It gives joint `ContDiffAt ℝ 2` for the heat semigroup series at positive time, via the cutoff series. The remaining blocker is the cutoff-term bound:

```lean
cutoffHeatTerm_iteratedFDeriv_bound
```

The current proof has already applied the Leibniz split, but the final bound after `norm_iteratedFDeriv_mul_le` is still `sorry`.

### 3C — resolver value joint C²

Status: **existing, with hypothesis**.

Existing theorem:

```lean
coupledChemical_jointContDiffAt_two
```

File:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

Hypothesis:

```lean
PhysicalResolverJointC2Data p u Bt
```

There is also the older/spectral FAC path through:

```lean
coupledChemicalConcentration_resolver_jointC2At_c2Data
```

File:

```text
ShenWork/PDE/IntervalCoupledResolverJointC2.lean
```

But the physical producer is the cleaner current one.

### 3D — resolver gradient joint C²

Status: **existing named producer**.

Correction to your note: this is not merely “follows from 3C + derivative” in the current repo; there is a dedicated theorem using the bounded-weight gradient series:

```lean
coupledChemical_grad_jointContDiffAt_two
```

File:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

Hypothesis:

```lean
PhysicalResolverJointC2Data p u Bt
```

It uses `boundedWeightJointGradSeries_contDiff_two` and the gradient summability field `H.grad_summable`.

### 3E — resolver positivity floor

Status: **existing**.

Low-level theorem you named exists:

```lean
intervalNeumannResolverR_nonneg_of_nonneg_source
```

File:

```text
ShenWork/PDE/IntervalResolverPositivity.lean
```

Closer coupled/FAC wrapper:

```lean
coupledChemical_floor_pos_of_nonneg_continuous
```

File:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
```

It proves:

```lean
0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x
```

from:

```lean
∀ s, Continuous (u s)
∀ s, ∀ x, 0 ≤ u s x
```

So yes, this field has an existing producer; the coupled wrapper is probably the one to use in the FAC chain.

### 3F — flux time bridge

Status: **existing, with side hypotheses**.

Existing theorem:

```lean
coupledChemDivFlux_timeBridge_of_physicalJointC2
```

File:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

Hypotheses include:

```lean
PhysicalResolverJointC2Data p u Bt
hu_c2 : ∀ x ∈ Ioo 0 1, ∀ s, ContDiffAt ℝ 2 (u_lift_uncurried) (s,x)
hbase : ∀ s x, 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x
```

There is also an assembler that discharges the bridge field inside the factor-input package:

```lean
coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
```

It still leaves source continuity, `hu_c2`, and `htime_cont` as upstream data.

### 3G — time-derivative continuity

Status: **existing, with representative hypothesis**.

Existing theorem:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

File:

```text
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

Hypothesis:

```lean
ChemDivMixedTimeDerivClosedRepr p u τ δ
```

There is also a factor-input assembler using it:

```lean
coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

This removes `htime_cont` as an explicit slab hypothesis, but still requires the closed-slab representative.

## Bottom line

Corrected status:

```text
1A       no complete producer found
2A-core  no complete producer found
2A-agree partial: coupledChemDivSourceLift_eq_deriv_fluxLift_interior, interior only
3A       no standalone producer found; still carried as slab input
3B       heatSemigroup_jointContDiffAt_two exists, but rests on cutoffHeatTerm_iteratedFDeriv_bound sorry
3C       coupledChemical_jointContDiffAt_two exists, needs PhysicalResolverJointC2Data
3D       coupledChemical_grad_jointContDiffAt_two exists, needs PhysicalResolverJointC2Data
3E       exists: intervalNeumannResolverR_nonneg_of_nonneg_source; closer wrapper coupledChemical_floor_pos_of_nonneg_continuous
3F       coupledChemDivFlux_timeBridge_of_physicalJointC2 exists, needs PhysicalResolverJointC2Data + hu_c2 + hbase
3G       chemDivMixedTimeDeriv_jointContinuousOn_closed exists, needs ChemDivMixedTimeDerivClosedRepr
```
