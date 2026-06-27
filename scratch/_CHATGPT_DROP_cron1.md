# Q1058 / cron2 — cascade from positive-time `FlooredSourceTimeData` to Level0 3C/3D

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

The **mathematical / structural chain exists**, and there is **no additional mathematical gap between `PhysicalSourceTimeC2` and `PhysicalResolverJointC2Data`**. That part is already a completed mechanical bridge:

```text
PhysicalSourceTimeC2
  -- physicalResolverJointC2Data_of_floor -->
PhysicalResolverJointC2Data
  -- coupledChemical_jointContDiffAt_two --> 3C / hv_c2
  -- coupledChemical_grad_jointContDiffAt_two --> 3D / hgradv_c2
```

However, in the current committed files there are two important caveats:

1. `heatSemigroup_level0_resolverJointC2Data` still has **two summability sorries** when calling `physicalSourceTimeC2_of_floored`: `hval` and `hgrad`. These are not between `PhysicalSourceTimeC2` and `PhysicalResolverJointC2Data`; they are inputs needed to obtain `PhysicalSourceTimeC2` from `FlooredSourceTimeData`.
2. If `FlooredSourceTimeData` is weakened from global `∀ t` / `∀ τ` to positive-time-only `∀ t, 0 < t → ...`, then the downstream types in `IntervalPhysicalSourceTimeC2Concrete.lean` are currently still **global**. So either those downstream structures must also be localized to positive time, or one must keep/provide a global extension package. Merely weakening `FlooredSourceTimeData` alone will break the current global proofs of `srcTimeCoeff_contDiff` and `physicalSourceTimeC2_of_floored`.

So the best precise answer is:

```text
FSTD positive-time fills the 6 analytic fields, but the existing chain works as-is only
if either:
  A. FSTD still provides global coefficient regularity via a harmless extension, or
  B. PhysicalSourceTimeC2 / PhysicalResolverJointC2Data / bounded-weight assemblers are
     localized to positive-time neighborhoods.

Once a compatible PhysicalSourceTimeC2 is obtained, the rest of the cascade to 3C/3D
is already complete. No hidden gap exists after PhysicalSourceTimeC2.
```

## 1. Current `FlooredSourceTimeData` shape and positive-time issue

File:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

Current structure fields are global:

```lean
structure FlooredSourceTimeData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) : Prop where
  d0 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ...
  d1 : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧ ...
  sliceC2 : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ,
    ContDiffOn ℝ 2 ((sliceFam (srcSlice p u) s₁ s₂ i) t) (Icc (0:ℝ) 1)
  sliceNeumann : ∀ i : ℕ, i ≤ 2 → ∀ t : ℝ, ...
  zerothBound : ∀ i : ℕ, i ≤ 2 → ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ...
  laplBound : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, 0 ≤ M ∧ ∀ t k, ...
```

The dependent lemmas also use global time:

```lean
private theorem srcTimeCoeff_deriv
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    Differentiable ℝ (srcTimeCoeff p u k) ∧
    deriv (srcTimeCoeff p u k) = fun t => cosineCoeffs (s₁ t) k
```

```lean
private theorem cosS1_deriv
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    Differentiable ℝ (fun t => cosineCoeffs (s₁ t) k) ∧
    deriv (fun t => cosineCoeffs (s₁ t) k) = fun t => cosineCoeffs (s₂ t) k
```

```lean
theorem srcTimeCoeff_contDiff
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (srcTimeCoeff p u k)
```

Thus, if `FlooredSourceTimeData` is literally changed to positive-time only, these lemmas need to become positive-time/local versions, for example:

```text
srcTimeCoeff_contDiffAt_of_pos
srcTimeCoeff_bound_of_pos
physicalSourceTimeC2On_of_flooredOn
PhysicalResolverJointC2DataOn
coupledChemical_jointContDiffAt_two_of_physicalOn
```

or else the Level0 coefficient families must be extended smoothly to nonpositive time so the old global `ContDiff ℝ 2` conclusions remain true.

## 2. `FlooredSourceTimeData → PhysicalSourceTimeC2`

File:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

The producer exists:

```lean
theorem physicalSourceTimeC2_of_floored
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂)
    (hval : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m))
    (hgrad : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant
        (fun i k => intervalNeumannResolverWeight p k * builtEs H i k) m)) :
    PhysicalSourceTimeC2 p u (builtEs H)
```

So `FlooredSourceTimeData` alone is not enough. It also needs the value/gradient majorant summability hypotheses `hval` and `hgrad`.

This producer fills:

```lean
src_contDiff k := srcTimeCoeff_contDiff H k
src_bound i k t hi := srcTimeCoeff_bound H i k t hi
value_summable := hval
grad_summable := hgrad
```

Therefore, after positive-time weakening, the two impacted facts are exactly the global `src_contDiff` and global `src_bound` conclusions. If the target is only positive-time 3C/3D, these can be localized.

## 3. `PhysicalSourceTimeC2 → PhysicalResolverJointC2Data`

File:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

The bridge is complete:

```lean
theorem physicalResolverJointC2Data_of_floor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Es : ℕ → ℕ → ℝ}
    (H : PhysicalSourceTimeC2 p u Es) :
    PhysicalResolverJointC2Data p u
      (fun i k => intervalNeumannResolverWeight p k * Es i k)
```

This uses:

```lean
resolverTimeCoeff_eq_weight_smul
resolverTimeCoeff_iteratedFDeriv_eq
resolverTimeCoeff_bound
```

and then simply passes through:

```lean
value_summable := H.value_summable
grad_summable := H.grad_summable
```

There is no additional gap here. The constant elliptic resolver weight is already handled.

## 4. `PhysicalResolverJointC2Data → 3C / 3D`

File:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

The structure is:

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

The value-side theorem for 3C is complete:

```lean
theorem coupledChemical_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

The gradient-side theorem for 3D is also complete:

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

These use the generic assemblers in:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

```lean
boundedWeightJointSeries_contDiff_two
boundedWeightJointGradSeries_contDiff_two
```

Those assemblers are already proved. So, once `PhysicalResolverJointC2Data` is in hand, 3C and 3D are done.

There is also an FAC-level wrapper:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical
    (H : PhysicalResolverJointC2Data p u Bt)
    (other : ... non-resolver FAC fields ...) :
    CoupledChemDivFluxFactorJointC2Inputs p u
```

It fills the resolver fields by:

```lean
(fun x hx s _ => coupledChemical_jointContDiffAt_two H hx)
(fun x hx s _ => coupledChemical_grad_jointContDiffAt_two H hx)
```

and leaves the non-resolver FAC fields in `other`. So 3C/3D specifically are covered.

## 5. Heat Level0 top-level theorem

File:

```text
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

The intended Level0 theorem is:

```lean
theorem heatSemigroup_level0_resolverJointC2Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

It already has exactly the cascade:

```lean
have hFSTD := HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData ...
set Es := IntervalPhysicalSourceTimeC2Concrete.builtEs hFSTD
have hSTC2 : PhysicalSourceTimeC2 p u Es :=
  physicalSourceTimeC2_of_floored hFSTD
    (by intro m hm; sorry)  -- value_summable
    (by intro m hm; sorry)  -- grad_summable
exact ⟨_, physicalResolverJointC2Data_of_floor hSTC2⟩
```

Then:

```lean
theorem heatResolverJointContDiffAt_two ... :
    ContDiffAt ℝ 2 (fun q => intervalDomainLift
      (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀) := by
  obtain ⟨Bt, hBt⟩ := heatSemigroup_level0_resolverJointC2Data ...
  exact coupledChemical_jointContDiffAt_two hBt hx₀
```

This closes 3C. For 3D, one uses the same extracted `hBt` with:

```lean
coupledChemical_grad_jointContDiffAt_two hBt hx₀
```

or the FAC wrapper `coupledChemDivFluxFactorJointC2Inputs_of_physical`.

## Remaining gaps / no-gaps classification

### No further gap after `PhysicalSourceTimeC2`

Complete mechanical bridge:

```text
PhysicalSourceTimeC2
  -> PhysicalResolverJointC2Data
  -> coupledChemical_jointContDiffAt_two
  -> coupledChemical_grad_jointContDiffAt_two
```

### Remaining gap before `PhysicalSourceTimeC2`

The two summability inputs to `physicalSourceTimeC2_of_floored` remain as sorries in `heatSemigroup_level0_resolverJointC2Data`:

```lean
hval  : ∀ m ≤ 2, Summable (boundedWeightJointMajorant (w * builtEs H) m)
hgrad : ∀ m ≤ 2, Summable (boundedWeightJointGradMajorant (w * builtEs H) m)
```

The comments say they should follow from `(kπ)⁻²` decay in `builtEs` and the elliptic weight `wₖ = 1/(μ+λₖ)`.

### API gap if `FlooredSourceTimeData` is positive-time-only

The current chain uses global `ContDiff ℝ 2` and bounds in the intermediate structures. If `FlooredSourceTimeData` is changed to only positive-time fields, then the following must be adjusted or replaced:

```text
srcTimeCoeff_deriv
cosS1_deriv
cosS2_continuous
srcTimeCoeff_contDiff
srcTimeCoeff_bound
physicalSourceTimeC2_of_floored
PhysicalSourceTimeC2
PhysicalResolverJointC2Data
boundedWeightJointSeries_contDiff_two / boundedWeightJointGradSeries_contDiff_two callers
```

The minimal engineering options are:

1. **Local positive-time route:** create `PhysicalSourceTimeC2On` / `PhysicalResolverJointC2DataOn` with `ContDiffAt` or local neighborhood hypotheses around `s₀ > 0`. This matches 3C/3D exactly.
2. **Global extension route:** define the Level0 source coefficient package with a smooth cutoff/extension to nonpositive time so the old global `ContDiff ℝ 2` APIs remain valid. Then the existing chain works unchanged.

## Bottom line

If the six Level0 `FlooredSourceTimeData` obligations are made fillable by weakening them to positive time, the downstream **mathematical cascade to 3C/3D is valid**, but the current global APIs will need a matching localization or smooth extension.

There are **no additional gaps between `PhysicalSourceTimeC2` and `PhysicalResolverJointC2Data`**. The only remaining proof obligations in the committed top-level Level0 chain are:

```text
1. value_summable for builtEs with resolver weight,
2. grad_summable for builtEs with resolver weight,
3. API localization/global-extension if FlooredSourceTimeData becomes positive-time-only.
```

Once these are handled, `heatSemigroup_level0_resolverJointC2Data` yields `PhysicalResolverJointC2Data`, and 3C/3D follow by the already committed `coupledChemical_jointContDiffAt_two` and `coupledChemical_grad_jointContDiffAt_two`.
