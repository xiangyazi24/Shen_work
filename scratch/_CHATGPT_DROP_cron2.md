# Q860 (cron2) — resolver C² shortcut via heat-semigroup composition?

Static repo inspection only; I did not run Lean.

## Short answer

I would **not** try the shortcut as stated.

The repo does not appear to have the resolver packaged as a `ContinuousLinearMap`
/ bounded linear operator on an `H^σ → H^{σ+2}` Banach scale, nor a ready
composition theorem of the form:

```lean
ContDiffAt ℝ 2 U (s,x) → ContDiffAt ℝ 2 (R(U)) (s,x)
```

The committed resolver regularity route is coefficient/spectral, not Banach-space
operator composition.  It already captures the elliptic-weight shortcut, but in
the form Mathlib/this repo can currently consume:

```lean
srcTimeCoeff p u k t
resolverTimeCoeff p u k t = intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
PhysicalSourceTimeC2 → PhysicalResolverJointC2Data
PhysicalResolverJointC2Data → coupledChemical_jointContDiffAt_two
```

So for cron2, the best route remains: extract/build `PhysicalResolverJointC2Data`
for the heat level, then use `coupledChemical_jointContDiffAt_two` and
`coupledChemical_grad_jointContDiffAt_two`.

## Why `heatSemigroup_jointContDiffAt_two` alone is not enough

`heatSemigroup_jointContDiffAt_two` gives pointwise joint `C²` for the heat
population representative `U(s,x)`.  But the resolver is not simply a pointwise
smooth function of `U(s,x)`.  It is:

```lean
V(s,x) = R(ν · U(s,·)^γ)(x)
```

That is nonlocal in `x`: the value at `x` depends on all cosine coefficients of
`ν · U(s,·)^γ`.  A Banach-composition proof would require several objects that I
do not see as existing repo APIs:

1. a concrete function space/norm for the source slices, e.g. `H^σ`, `C²`, or
   an ℓ¹ weighted coefficient space;
2. `R` packaged as a bounded linear map between those spaces;
3. a theorem saying `s ↦ ν · U(s,·)^γ` is `ContDiff` into that source space;
4. a `ContinuousLinearMap.comp_contDiffAt`-style application back to pointwise
   `(s,x)` evaluation.

The current repo avoids all of that by working directly with mode coefficients
and summable majorants.

## Closest existing “operator” fact

There is a spatial-only physical resolver file that proves exactly the elliptic
multiplier idea, but not as a `ContinuousLinearMap`:

```lean
resolverR_eigenWeighted_le_source
resolverR_eigenWeighted_summable_of_sourceL1
resolverR_contDiff_two_of_source_l1
resolverR_contDiffOn_Icc_of_source_l1
```

This says: if the source coefficients are ℓ¹, then the resolver coefficients are
spatially eigenvalue-weighted ℓ¹, because

```lean
λ_k * |v̂_k| ≤ |â_k|.
```

That is the right mathematical shortcut for **spatial** C².  But it is not a
joint time-space composition theorem; it does not discharge the time derivatives
or the joint `(s,x)` `contDiff_tsum` obligations by itself.

## Existing joint route that already implements the shortcut

For joint `(s,x)` C², the relevant API is in the bounded-weight physical route:

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

Then:

```lean
coupledChemical_jointContDiffAt_two
coupledChemical_grad_jointContDiffAt_two
```

produce the resolver value and resolver-gradient joint C² facts.

And the source-to-resolver bridge is already committed:

```lean
resolverTimeCoeff_eq_weight_smul
resolverTimeCoeff_iteratedFDeriv_eq
resolverTimeCoeff_bound
physicalResolverJointC2Data_of_floor
```

This is the coefficient-level version of “bounded linear elliptic resolver
preserves `C²`”.  It is just not exposed as a functional-analysis operator.

## Practical recommendation for 2A-sup / heat level

Do **not** build a new Banach operator layer for this sub-sorry.  That would be a
large detour and would still need the same coefficient/source regularity facts to
instantiate the function-space differentiability hypotheses.

Instead, make the heat-specific theorem produce the existing structure:

```lean
noncomputable theorem level0_physicalResolverJointC2Data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
  -- Build the heat-level source-side data:
  --   Hfloor : FlooredSourceTimeData p (conjugatePicardIter p u₀ 0) s₁ s₂
  -- Then:
  --   Hsrc  := physicalSourceTimeC2_of_floored Hfloor hval hgrad
  --   Hphys := physicalResolverJointC2Data_of_floor Hsrc
  -- Return ⟨_, Hphys⟩.
```

After that, the facts needed by the smooth representative are one-liners:

```lean
have hv_c2 : ContDiffAt ℝ 2
    (fun q : ℝ × ℝ =>
      intervalDomainLift
        (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
    (s, x) := by
  obtain ⟨Bt, Hphys⟩ := level0_physicalResolverJointC2Data
    p hc hcT hu₀_cont hu₀_bound hpos hub
  exact coupledChemical_jointContDiffAt_two Hphys hx

have hgradv_c2 : ContDiffAt ℝ 2
    (fun q : ℝ × ℝ =>
      deriv (intervalDomainLift
        (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1)) q.2)
    (s, x) := by
  obtain ⟨Bt, Hphys⟩ := level0_physicalResolverJointC2Data
    p hc hcT hu₀_cont hu₀_bound hpos hub
  exact coupledChemical_grad_jointContDiffAt_two Hphys hx
```

If the current construction is only valid on the positive window `[c,T]`, use the
window-local wrappers from Q851 instead of a global `PhysicalResolverJointC2Data`.
That is still sufficient for `2A-sup`.

## Bottom line

The repo has the elliptic multiplier shortcut, but **at coefficient level**, not
as a bounded linear operator composition.  Use the existing physical resolver C²
pipeline.  `heatSemigroup_jointContDiffAt_two` is useful for building the source
side (`ν·U^γ` and its time derivatives), but it does not by itself turn into
`ContDiffAt` of the nonlocal resolver without the coefficient summability /
bounded-weight machinery.
