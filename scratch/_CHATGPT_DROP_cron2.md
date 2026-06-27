# Q1006 (cron2) — F1 `ContinuousOn` → `IntervalIntegrable` upstream weakening

Static repo inspection only; I did **not** run Lean.

## Verdict

Yes: for `cosineCoeffs_hasDerivAt_of_smooth_param`, the `ContinuousOn (f s) (Icc 0 1)` hypothesis on the **source slice** `f s` is stronger than needed.  The proof uses it only to get:

1. `AEStronglyMeasurable (g s) intervalDomainInteriorMeasure` for
   `g s x = cos(nπx) * f s x`, eventually in `s` near `τ`;
2. `IntervalIntegrable (g τ) volume 0 1` at the base time.

Both can be recovered from eventual

```lean
IntervalIntegrable (f s) MeasureTheory.volume (0 : ℝ) 1
```

because the cosine weight is continuous and bounded on `[0,1]`.  The proof does **not** otherwise need endpoint continuity of `f s`.  The derivative-side continuity

```lean
ContinuousOn (Function.uncurry f')
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

is still needed exactly as before: it supplies measurability of `g' τ` and the compact-slab dominated bound via `exists_bound_of_continuousOn_slab`.

So the F1 weakening is legitimate, with this precise interpretation:

```text
source slice f:     ContinuousOn on Icc 0 1  -->  IntervalIntegrable on [0,1]
derivative slice f': keep ContinuousOn on the compact slab
pointwise HasDerivAt: keep unchanged
```

This directly addresses the `intervalDomainLift` zero-extension problem: the endpoint mismatch blocks `ContinuousOn` on the closed interval, but it does not block integrability on `[0,1]` / the interior measure.

## 1. Is `IntervalIntegrable` sufficient for `cosineCoeffs_hasDerivAt_of_smooth_param`?

Yes.

The current proof of `cosineCoeffs_hasDerivAt_of_smooth_param` does the following with `hf_cont`:

```lean
(hf_cont : ∀ᶠ s in 𝓝 τ, ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
```

### Use A: measurability of the integrand `g s`

Current code shape:

```lean
· -- (hF_meas) AEStronglyMeasurable for g s
  filter_upwards [hf_cont] with s hs
  have : ContinuousOn (g s) (Set.Ioo (0 : ℝ) 1) :=
    ContinuousOn.mul hcos_cont.continuousOn (hs.mono Set.Ioo_subset_Icc_self)
  exact this.aestronglyMeasurable measurableSet_Ioo
```

Replacement route from `IntervalIntegrable`:

```lean
· -- (hF_meas) AEStronglyMeasurable for g s
  filter_upwards [hf_int] with s hs
  -- hs : IntervalIntegrable (f s) volume 0 1
  -- cosine is continuous/bounded, so g s is also interval-integrable;
  -- interval-integrable implies integrable on Ioc, hence AEStronglyMeasurable
  -- on the interior measure after `restrict_Ioo_eq_restrict_Ioc`.
  exact intervalIntegrable_cos_mul_aestronglyMeasurable_Ioo
    (n := n) hs
```

This needs a small helper lemma if no existing Mathlib lemma is convenient:

```lean
private lemma intervalIntegrable_cos_mul_aestronglyMeasurable_Ioo
    {f : ℝ → ℝ} (n : ℕ)
    (hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1) :
    AEStronglyMeasurable
      (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x) * f x)
      intervalDomainInteriorMeasure := by
  -- Convert `hf` to integrability on `Ioc 0 1` using the same conversion used in
  -- `intervalIntegral_hasDerivAt_time_of_local`.
  -- Then multiply by the bounded continuous cosine factor, and use
  -- `restrict_Ioo_eq_restrict_Ioc` to move to `intervalDomainInteriorMeasure`.
  sorry
```

The proof pattern should mirror `IntervalUnderIntegralLeibniz.intervalIntegral_hasDerivAt_time_of_local`, where `IntervalIntegrable (g τ) volume 0 1` is converted to integrability under `intervalDomainInteriorMeasure` via:

```lean
((intervalIntegrable_iff_integrableOn_Ioc_of_le
  (show (0 : ℝ) ≤ 1 by norm_num)).mp hF_int).integrable
```

and then:

```lean
simpa [intervalDomainInteriorMeasure,
  MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using hIoc
```

### Use B: interval integrability of the base integrand `g τ`

Current code shape:

```lean
· -- (hF_int) IntervalIntegrable for g τ at the base point
  have hτ_cont := hf_cont.self_of_nhds
  have : ContinuousOn (g τ) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ContinuousOn.mul hcos_cont.continuousOn hτ_cont
  exact this.intervalIntegrable
```

Replacement route from `IntervalIntegrable`:

```lean
· -- (hF_int) IntervalIntegrable for g τ at the base point
  have hτ_int : IntervalIntegrable (f τ) MeasureTheory.volume (0 : ℝ) 1 :=
    hf_int.self_of_nhds
  exact intervalIntegrable_cos_mul (n := n) hτ_int
```

Again, add a small helper if needed:

```lean
private lemma intervalIntegrable_cos_mul
    {f : ℝ → ℝ} (n : ℕ)
    (hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1) :
    IntervalIntegrable
      (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x) * f x)
      MeasureTheory.volume (0 : ℝ) 1 := by
  -- Use that `x ↦ cos(nπx)` is continuous and bounded on `[0,1]`.
  -- If there is no direct `IntervalIntegrable.mul_*` lemma, unfold/convert to
  -- integrability on `Ioc 0 1` and use bounded multiplication there.
  sorry
```

### What does **not** change

These parts of `cosineCoeffs_hasDerivAt_of_smooth_param` remain exactly the same:

```lean
(h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
  ∀ s ∈ Metric.ball τ δ,
    HasDerivAt (fun r => f r x) (f' s x) s)

(h_cont_deriv : ContinuousOn (Function.uncurry f')
  (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1))
```

The `hF'_meas`, dominated-bound, and pointwise derivative subgoals do not use `hf_cont`; they use `h_cont_deriv`, `hbound`, and `h_diff`.

## 2. Exact changes

Use fully qualified `MeasureTheory.volume` in the structures to avoid having to add `open MeasureTheory` everywhere.

### A. `IntervalMildPicardRegularity.lean`: theorem signature

Old:

```lean
theorem cosineCoeffs_hasDerivAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {τ δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hf_cont : ∀ᶠ s in 𝓝 τ, ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => f r x) (f' s x) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) τ := by
```

New:

```lean
theorem cosineCoeffs_hasDerivAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {τ δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hf_int : ∀ᶠ s in 𝓝 τ,
      IntervalIntegrable (f s) MeasureTheory.volume (0 : ℝ) 1)
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => f r x) (f' s x) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) τ := by
```

Only the two `hf_cont`-based subproofs are rewritten, as described above.

### B. `IntervalChemDivOuterCommuteProducer.lean`: `CoupledChemDivFluxJointC2Hyp`

Old field:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
```

New field:

```lean
(∀ᶠ s in 𝓝 τ,
  IntervalIntegrable (coupledChemDivSourceLift p u s)
    MeasureTheory.volume (0 : ℝ) 1) ∧
```

The producer `coupledChemDivOuterCommuteAtoms_of_fluxJointC2` just transports this field, so rename local variables from e.g. `hsource_cont` / `hsource_cont_slab` to `hsource_int` / `hsource_int_slab` and pass through unchanged.

### C. `IntervalChemDivOuterCommute.lean`: `CoupledChemDivOuterCommuteAtoms`

Old field:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
```

New field:

```lean
(∀ᶠ s in 𝓝 τ,
  IntervalIntegrable (coupledChemDivSourceLift p u s)
    MeasureTheory.volume (0 : ℝ) 1) ∧
```

The theorem `coupledChemDivLocalChainRule_of_outerCommuteAtoms` only passes this field to the next package.  No analysis changes there.

### D. `IntervalChemDivLocalChainRule.lean`: `CoupledChemDivPointwiseChainAtoms`

Old field:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
```

New field:

```lean
(∀ᶠ s in 𝓝 τ,
  IntervalIntegrable (coupledChemDivSourceLift p u s)
    MeasureTheory.volume (0 : ℝ) 1) ∧
```

The theorem `coupledChemDivLocalChainRule_of_pointwiseChainAtoms` is a field copy:

```lean
exists_local_slab := A.exists_local_slab
```

so it should continue to work after the target structure is changed the same way.

### E. `IntervalChemDivTimeDerivative.lean`: `CoupledChemDivLocalChainRule`

Old field:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
```

New field:

```lean
(∀ᶠ s in 𝓝 τ,
  IntervalIntegrable (coupledChemDivSourceLift p u s)
    MeasureTheory.volume (0 : ℝ) 1) ∧
```

Then update the only local consumer in that file:

Old:

```lean
rcases F.hchain.exists_local_slab s with
  ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
exact
  ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
    (f := coupledChemDivSourceLift p u)
    (f' := coupledChemDivTimeDerivativeLift p u)
    (τ := s) (δ := δ) (n := n) hδ hf_cont hdiff hcont_deriv
```

New:

```lean
rcases F.hchain.exists_local_slab s with
  ⟨δ, hδ, hf_int, hdiff, hcont_deriv⟩
exact
  ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
    (f := coupledChemDivSourceLift p u)
    (f' := coupledChemDivTimeDerivativeLift p u)
    (τ := s) (δ := δ) (n := n) hδ hf_int hdiff hcont_deriv
```

## Required extra updates not in the four-file list

The four requested structures are not the only declarations whose types must be updated for the chain to compile.  I found these additional source-field carriers or direct callers.

### 1. `IntervalChemDivFluxJointC2Producer.lean`: `CoupledChemDivFluxFactorJointC2Inputs`

This structure also carries the same source slice field before producing `CoupledChemDivFluxJointC2Hyp`.

Old:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
```

New:

```lean
(∀ᶠ s in 𝓝 τ,
  IntervalIntegrable (coupledChemDivSourceLift p u s)
    MeasureTheory.volume (0 : ℝ) 1) ∧
```

Then rename/pass through the field in `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs`.

### 2. `IntervalChemDivFluxFactorFAC.lean`: `FACLocalSlabInputs`

Old:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
```

New:

```lean
(∀ᶠ s in 𝓝 τ,
  IntervalIntegrable (coupledChemDivSourceLift p u s)
    MeasureTheory.volume (0 : ℝ) 1) ∧
```

This field is later unpacked by `coupledChemDivFluxFactorJointC2Inputs_of_FACInputs` and passed into `CoupledChemDivFluxFactorJointC2Inputs`.

### 3. `IntervalResolverJointC2PhysicalConcrete.lean` and `IntervalPhysicalResolverDataConcrete.lean`: `other` argument shapes

Both physical/floor producers have an `other` argument whose first field is the old eventual `ContinuousOn`.  Change the first conjunct of those `other` arguments to the same eventual `IntervalIntegrable` type.

Old first conjunct:

```lean
(∀ᶠ s in 𝓝 τ,
  ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
```

New first conjunct:

```lean
(∀ᶠ s in 𝓝 τ,
  IntervalIntegrable (coupledChemDivSourceLift p u s)
    MeasureTheory.volume (0 : ℝ) 1) ∧
```

### 4. `IntervalFlooredSourceTimeDataIterate.lean`: `other` argument shape

The theorem `coupledChemDivFluxFactorJointC2Inputs_of_iterate` has the same `other` first conjunct.  Change it identically.

### 5. `IntervalChemDivWinDischarge.lean`: residual field `other`

The residual bundle `ChemDivSolutionRegularityResidual.other` has the same `other` first conjunct.  Change it identically.

### 6. `Wiener/EWA/ChemDivAdot.lean`: direct caller

This file has another direct theorem:

```lean
coupledChemDivCoeff_hasDerivAt_of_chainRule
```

It unpacks:

```lean
rcases hchain.exists_local_slab s with
  ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
```

and passes `hf_cont` to `cosineCoeffs_hasDerivAt_of_smooth_param`.  After the theorem weakening, update this exactly as in `IntervalChemDivTimeDerivative.lean`:

```lean
rcases hchain.exists_local_slab s with
  ⟨δ, hδ, hf_int, hdiff, hcont_deriv⟩
...
  (τ := s) (δ := δ) (n := n) hδ hf_int hdiff hcont_deriv
```

## 3. Are there other consumers of the `ContinuousOn` field?

For the four requested structures, I found no downstream use of the source `ContinuousOn` as continuity data except through `cosineCoeffs_hasDerivAt_of_smooth_param`.

More precisely:

* `CoupledChemDivFluxJointC2Hyp` → `CoupledChemDivOuterCommuteAtoms`: the source field is just copied.
* `CoupledChemDivOuterCommuteAtoms` → `CoupledChemDivLocalChainRule`: copied.
* `CoupledChemDivPointwiseChainAtoms` → `CoupledChemDivLocalChainRule`: copied.
* `CoupledChemDivLocalChainRule` → coefficient derivative: consumed in `coupledChemDivCoeff_hasDerivAt_of_fields`, which calls `cosineCoeffs_hasDerivAt_of_smooth_param`.
* `Wiener/EWA/ChemDivAdot.lean` has a second direct consumer, `coupledChemDivCoeff_hasDerivAt_of_chainRule`, also only calling `cosineCoeffs_hasDerivAt_of_smooth_param`.

There are several **producers/pass-through wrappers** carrying the same field (`FACLocalSlabInputs`, `CoupledChemDivFluxFactorJointC2Inputs`, physical `other` arguments, iterate `other`, and `ChemDivSolutionRegularityResidual.other`).  These must be updated for type compatibility, but they do not use closed-interval continuity analytically.

I did not find another load-bearing consumer that needs `ContinuousOn` specifically for endpoint topology.  The load-bearing consumer is the cosine-coefficient time-Leibniz theorem, and it can be weakened to `IntervalIntegrable` for the source slice.

## Suggested implementation order

1. Add two local helper lemmas near `cosineCoeffs_hasDerivAt_of_smooth_param`:

```lean
import ShenWork.PDE.IntervalUnderIntegralLeibniz
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity

open MeasureTheory Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.IntervalDomainLpMonotonicity (intervalDomainInteriorMeasure)

namespace ShenWork.IntervalMildPicardRegularity

private lemma intervalIntegrable_cos_mul
    {f : ℝ → ℝ} (n : ℕ)
    (hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1) :
    IntervalIntegrable
      (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x) * f x)
      MeasureTheory.volume (0 : ℝ) 1 := by
  -- prove by bounded continuous multiplier on the compact interval, or by
  -- converting to integrability on `Ioc 0 1` and using bounded multiplication.
  sorry

private lemma intervalIntegrable_cos_mul_aestronglyMeasurable_Ioo
    {f : ℝ → ℝ} (n : ℕ)
    (hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1) :
    AEStronglyMeasurable
      (fun x : ℝ => Real.cos ((n : ℝ) * Real.pi * x) * f x)
      intervalDomainInteriorMeasure := by
  -- prove from `intervalIntegrable_cos_mul n hf`, following the conversion in
  -- `IntervalUnderIntegralLeibniz.intervalIntegral_hasDerivAt_time_of_local`.
  sorry

end ShenWork.IntervalMildPicardRegularity
```

2. Change `cosineCoeffs_hasDerivAt_of_smooth_param` signature from `hf_cont` to `hf_int` and replace only the two subproofs described above.

3. Change the four requested structures' source field from eventual `ContinuousOn` to eventual `IntervalIntegrable`.

4. Change the additional pass-through carriers listed above.

5. Update the two direct call sites:

```lean
coupledChemDivCoeff_hasDerivAt_of_fields
coupledChemDivCoeff_hasDerivAt_of_chainRule
```

6. Rename local variables (`hsource_cont`, `hf_cont`) to `hsource_int`, `hf_int` where helpful; most producer proofs should otherwise remain structurally identical.
