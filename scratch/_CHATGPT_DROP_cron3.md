# Q1579 (cron3): next `sorry` on the FAC critical path

## Short answer

With `ShenWork/Paper2/IntervalHeatResolverJointC2.lean` now clean, the next blocker is **not** in the downstream FAC reducers.

The remaining FAC-critical `sorry`s are concentrated in:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

specifically inside:

```lean
theorem heatSemigroup_level0_resolverJointC2Data
```

The two files

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
ShenWork/PDE/IntervalCoupledResolverJointC2.lean
```

are currently clean with respect to executable `sorry` tokens in the searched tree.

So the next actual critical-path `sorry` is:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:837:
  (hsliceC2 := by intro i hi t ht; sorry)
```

But the **true analytic blocker** is the `FlooredSourceTimeData` package as a whole, especially:

```text
hlaplBound := by intro i hi; sorry
```

because `hlaplBound` is the `(kπ)⁻²` source-slice coefficient envelope needed to build `builtEs`, and the previous analysis shows the global-in-`t > 0` version is problematic for `i = 1` unless the statement is localized away from `0` or strengthened with more initial regularity.

## Equivalent grep results

I inspected the current default indexed tree, whose relevant search hits point at commit:

```text
2360e7433b1f3bb673ee6dcf6ff34364f5e2a068
```

### 1. `grep -rn sorry ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean`

Important executable hits:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:837:
  (hsliceC2 := by intro i hi t ht; sorry)

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:838:
  (hsliceNeumann := by intro i hi t ht; sorry)

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:839:
  (hzerothBound := by intro i hi; sorry)

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:840:
  (hlaplBound := by intro i hi; sorry)

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:851:
  intro m hm; sorry

ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean:854:
  intro m hm; sorry
```

Context:

```lean
have hFSTD := ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
  hu₀_bound hu₀_cont (p := p)
  (hfloor := by
    intro t ht x hx
    exact ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_pos_of_pos
      hu₀_cont hu₀_pos ht hx)
  (hsliceC2 := by intro i hi t ht; sorry)
  (hsliceNeumann := by intro i hi t ht; sorry)
  (hzerothBound := by intro i hi; sorry)
  (hlaplBound := by intro i hi; sorry)
```

and then:

```lean
have hSTC2 : ShenWork.IntervalPhysicalResolverDataConcrete.PhysicalSourceTimeC2 p u Es :=
  ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored hFSTD
    (by
        intro m hm; sorry)
    (by
        intro m hm; sorry)
```

Comment-only hits also exist in the same file, for example the header says the heat-semigroup part is `0 sorry` and the resolver section comments describe the remaining `sorry'd` fields.  Those are not executable blockers.

### 2. `grep -rn sorry ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean`

No executable `sorry` hits found.

The file is a clean reducer.  Its key theorem is:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_FACInputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputs p u) :
    CoupledChemDivFluxFactorJointC2Inputs p u := by
```

The theorem consumes a `CoupledChemDivFluxFactorFACInputs` package, obtains resolver C² from the resolver spectral C² package, proves the resolver floor using positivity/nonnegativity, and returns `CoupledChemDivFluxFactorJointC2Inputs` without local `sorry`s.

The key input structure is:

```lean
structure CoupledChemDivFluxFactorFACInputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_package :
    ∃ U : ℝ,
      ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u) ∧
      ∀ τ : ℝ, ∃ δ : ℝ, FACLocalSlabInputs p u U τ δ
```

Thus this file does not block by itself; it tells us what upstream package must be produced.

### 3. `grep -rn sorry ShenWork/PDE/IntervalCoupledResolverJointC2.lean`

No executable `sorry` hits found.

This file is also a clean transfer layer.  Its key endpoint is:

```lean
theorem coupledChemicalConcentration_resolver_jointC2At_c2Data
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U s x : ℝ}
    (H : ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u))
    ... :
    ContDiffAt ℝ 2 ... ∧
    ContDiffAt ℝ 2 ... :=
  resolver_jointC2At_of_spectralAgreement_c2Data
    H hs0 hsU hx hC2
```

So this file is not the remaining obstruction either.  It just transports the C2-coefficient spectral-agreement package into resolver value/gradient joint `C²`.

## What blocks the headline theorem?

The headline FAC chain now blocks at construction of the heat-level-0 resolver joint C² data:

```lean
heatSemigroup_level0_resolverJointC2Data
```

This theorem is supposed to produce:

```lean
∃ Bt : ℕ → ℕ → ℝ,
  PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

and then `heatResolverJointContDiffAt_two` extracts that package and applies:

```lean
coupledChemical_jointContDiffAt_two hBt hx₀
```

Therefore the concrete blocker list is:

1. `hsliceC2` — each source time-slice family `i = 0,1,2` is spatial `C²` on `[0,1]` for `t > 0`.
2. `hsliceNeumann` — corresponding Neumann endpoint derivative conditions for those slices.
3. `hzerothBound` — uniform zeroth cosine coefficient bound for those slices.
4. `hlaplBound` — uniform positive-mode `(kπ)⁻²` coefficient bound for those slices.
5. `value_summable` — summability for `boundedWeightJointMajorant` after converting `FlooredSourceTimeData` to `PhysicalSourceTimeC2`.
6. `grad_summable` — summability for `boundedWeightJointGradMajorant` after the same conversion.

The downstream FAC files are already wired: once this package exists, `PhysicalSourceTimeC2 → PhysicalResolverJointC2Data → resolver joint C² → FAC joint factor inputs` is no longer the main problem.

## Recommended next move

Do **not** start in `IntervalChemDivFluxFactorFAC.lean` or `IntervalCoupledResolverJointC2.lean`; those files are reducer/wiring layers and appear clean.

Start in `IntervalHeatSemigroupHighRegularity.lean`, at the `hFSTD` construction in `heatSemigroup_level0_resolverJointC2Data`.

The first syntactic `sorry` is `hsliceC2`, but the critical analytic decision is `hlaplBound`:

```lean
(hlaplBound := by intro i hi; sorry)
```

If the current global `∀ t > 0` `hlaplBound` is retained, this is likely the hard blocker.  If the package is changed to a local-positive-time/slab formulation, then `hsliceC2`, `hsliceNeumann`, `hzerothBound`, and the two summability fields become much more mechanical after positive-time heat smoothing and IBP estimates.
