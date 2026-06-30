# Q2510 shen1 — audit of local precrossing/window plumbing layer

Repo: `xiangyazi24/Shen_work`

Baseline referenced by prompt: commit `9d9250e6fbc8e0efb30a61130cd0b6e471ed4321`.

Target file:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Visible-source caveat: the GitHub-visible `main` copy I can inspect still shows the pre-local-patch `P3MoserIntegratedClosure.lean`.  This audit is therefore based on the prompt’s description of the local patch, plus the exact fixed-window helper APIs visible at commit `9d9250e6`.  The user reports:

```text
uisai2 lake env lean ShenWork/PDE/P3MoserIntegratedClosure.lean
```

passes for the modified file.

## Bottom line

The described patch is architecturally honest and useful, provided it remains exactly a fixed-window/precrossing packaging layer and does not claim `IntegratedMoserFirstCrossingStep` or `LpPowerBoundedBefore D (p + rho) T u` from a time-integral estimate.

The layer has the right role:

1. normalize notation for `Y_p` and `G_p`,
2. restrict regularity/integrability hypotheses to windows,
3. package the current-exponent Icc bound and endpoint/nonnegativity data,
4. apply the existing fixed-window integrated Moser estimates,
5. return only an existential time-integral upper bound for `Y_{p+rho}`.

That is exactly the honest staging point before the high-excursion/pointwise extraction frontier.

## Source/API alignment

The current helper APIs at `9d9250e6` require the following, and the described patch appears aligned with them.

### `integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound`

Current visible shape:

```lean
integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
  (hab : a ≤ b)
  (hYmax_int :
    IntervalIntegrable
      (fun s => max (1 : ℝ)
        (D.integral (fun x => (u s x) ^ p)))
      volume a b)
  (hY_le : ∀ s ∈ Set.Icc a b,
    D.integral (fun x => (u s x) ^ p) ≤ M)
```

So adding a `maxOneEnergy_intervalIntegrable` field to the precrossing record is necessary and honest.  It is not derivable from a pointwise bound alone in arbitrary `BoundedDomainData`; it must come from power-profile integrability plus max/abs closure.

### `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`

Current visible shape requires:

```lean
hrel hp heps hab ha hb hZ_int hG_int hY_le hG_le
```

The described record fields `higherPower_intervalIntegrable`, `gradient_intervalIntegrable`, `currentEnergy_le_Icc`, plus the gradient-bound wrapper are exactly the right supply chain.

### `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds`

Current visible shape requires:

```lean
hinteg hp hp_nonneg haT hbT hYa hYb_nonneg hmaxInt
```

Keeping `hp_nonneg` and `right_currentEnergy_nonneg` explicit in the precrossing layer is correct.  Neither is automatic from `p0 ≤ p` in the abstract statement unless there is an extra `0 ≤ p0`; and energy nonnegativity is not automatic from `BoundedDomainData`.

## Honesty audit by component

### `integratedMoserEnergy` and `integratedMoserGradientEnergy`

Status: honest, useful notation.

These are definitional aliases for existing expressions.  They add no analytic content and help later theorem statements stay readable.

Suggested names are fine.  If you want slightly more explicit names, these are possible but not necessary:

```lean
integratedMoserPowerEnergy
integratedMoserMoserGradientEnergy
```

I would keep the current names unless there is already a collision.  Short names are valuable in first-crossing statements.

### interval-integrable restriction from `IntegrableOn (Set.uIcc 0 T)`

Status: pure Lean plumbing.

A helper of the form

```lean
intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
```

is honest.  The key is that the theorem must require an orientation hypothesis such as `a ≤ b`, because the standard rewrite to `IntegrableOn f (Set.Ioc a b)` uses the non-reversed interval.  It should also require a subset hypothesis strong enough to place the window inside `Set.uIcc 0 T`.

Recommended statement shape:

```lean
theorem intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    {f : ℝ → ℝ} {T a b : ℝ}
    (hab : a ≤ b)
    (hint : IntegrableOn f (Set.uIcc (0 : ℝ) T) volume)
    (hsub : Set.Icc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact hint.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
```

This is no-sorry plumbing if the local Mathlib spelling is `IntegrableOn.mono_set`, which the repo already uses elsewhere.

### `max-one intervalIntegrable` via abs formula

Status: honest; slightly more robust than relying on a possibly renamed `IntegrableOn.max` method.

Using the identity

```lean
max 1 y = (1 + y + |1 - y|) / 2
```

is mathematically sound and not an analytic assumption.  It requires only interval integrability closure under constants, addition/subtraction, scalar multiplication, and absolute value.  If it passes on uisai2, it is preferable to a fragile direct `hconst.max hY` proof.

Recommended theorem name:

```lean
intervalIntegrable_max_one_of_intervalIntegrable
```

If the local proof uses the abs formula, the docstring should say so explicitly, e.g.

```lean
/-- If `Y` is interval-integrable, so is `max 1 Y`; proved via
`max 1 y = (1 + y + |1 - y|) / 2` to avoid depending on the exact Mathlib name
for integrability under `max`. -/
```

No hidden false claim here.

### `IntegratedMoserFirstCrossingRegularity` interval-integrability producers

Status: honest and useful.

The fields

```lean
powerTimeIntegrable
gradientTimeIntegrable
```

are global-on-`uIcc 0 T` hypotheses.  Producing interval-integrability on `a..b` is pure restriction plumbing.

Suggested names are good:

```lean
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
```

One caveat: `higherPower_intervalIntegrable` for exponent `p + rho` must require or derive

```lean
p0 ≤ p + rho
```

so the constructor needs `0 ≤ rho` or `0 < rho`.  This is not a false claim; it is just an important hypothesis.  In the actual iteration route, `rho_pos` is available from `AbstractLpBootstrapHypothesis`, so `0 ≤ rho` is a reasonable field/hypothesis here.

### `IntegratedMoserEnergyNonnegativity`

Status: honest as an explicit abstract frontier/plumbing assumption; do not derive it abstractly.

This is the right architecture.  The abstract `BoundedDomainData` has an arbitrary `integral` field, so one cannot prove

```lean
0 ≤ D.integral (fun x => (u t x) ^ p)
```

from `0 ≤ u` or `0 ≤ p` unless the domain/integral API carries positivity.  Making this a named hypothesis is honest.

Suggested name is fine:

```lean
IntegratedMoserEnergyNonnegativity
```

If you want the name to advertise the time interval, use:

```lean
IntegratedMoserEnergyNonnegativeOnIcc
```

I slightly prefer `IntegratedMoserEnergyNonnegativity` because it matches the current abstract-frontier naming style.

Potential future producer should be interval-domain-specific, e.g.

```lean
intervalDomain_integratedMoserEnergyNonnegativity_of_classicalSolution
```

but that should not be part of this abstract plumbing patch.

### `LpPowerBoundedBefore` Icc `Cp` extraction

Status: honest and useful.

A helper like

```lean
currentEnergy_Icc_bound_of_LpPowerBoundedBefore
```

or

```lean
exists_currentEnergy_Icc_bound_of_LpPowerBoundedBefore
```

is pure unpacking of `LpPowerBoundedBefore` plus `0 < a` and `b < T`.

Recommended theorem name if it returns an existential constant:

```lean
exists_currentEnergy_Icc_bound_of_LpPowerBoundedBefore
```

Recommended theorem name if it takes a chosen `Cp` and a proof `hCp`:

```lean
currentEnergy_le_Icc_of_forall_before_bound
```

If the patch uses only one theorem returning `∃ Cp`, that is enough.

### `IntegratedMoserPrecrossingIntervalData`

Status: honest and useful.

The record should be a `Prop` structure, not computational data, because it packages proof obligations and constants already chosen externally.  The fields listed in the prompt are the right minimal set:

```lean
hp
hp_nonneg
hab
ha_pos
hb_lt
haT
hbT
currentEnergy_le_Icc
right_currentEnergy_nonneg
maxOneEnergy_intervalIntegrable
higherPower_intervalIntegrable
gradient_intervalIntegrable
```

No hidden false claim, as long as the record does not assert any pointwise information about `Y_{p+rho}`.

Potential rename: `IntegratedMoserPrecrossingWindowData` is slightly better than `...IntervalData`, because “window” is the mathematical role.  However, if the committed patch already uses `IntegratedMoserPrecrossingIntervalData` and compiles, I would not churn the name unless downstream code has not started using it.

The constructor from regularity should be named to make clear it builds only window data, e.g.

```lean
integratedMoserPrecrossingIntervalData_of_regular_window
```

or, with the better noun:

```lean
integratedMoserPrecrossingWindowData_of_regular_window
```

### `IntegratedMoserWindowUpperBoundData` as a `Prop` existential

Status: honest and useful.

If it is implemented as a `Prop` existential such as

```lean
def IntegratedMoserWindowUpperBoundData ... : Prop :=
  ∃ Gbound Ceps, 0 ≤ Ceps ∧ ...
```

that is a good minimal interface.  It records exactly the output of the fixed-window machinery and does not expose computational data unnecessarily.  It is also appropriate because the later high-excursion frontier only needs existence of an upper bound to contradict.

Potential rename: if it is a `Prop`, drop `Data`:

```lean
IntegratedMoserWindowUpperBound
```

Use `Data` only if it is a `structure ... : Prop where` with named fields/accessors.  Both styles are acceptable.  If the current patch uses existential `Prop`, the cleanest name would be:

```lean
IntegratedMoserWindowUpperBound
```

But I would not rename unless this is still unmerged; the current name is not misleading enough to justify churn.

Important: do not add a field

```lean
0 ≤ Gbound
```

unless it is actually needed and proved.  The upper estimate only needs an upper witness.  Positivity of the gradient integral is also abstractly not automatic from `BoundedDomainData`.

## Architecture check

The patch belongs in `P3MoserIntegratedClosure.lean`, inside:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

and before:

```lean
moser_iteration_chain_of_integrated_first_crossing_step
```

This placement is right because:

* it depends on fixed-window helper lemmas above it,
* it supplies ingredients for the future first-crossing frontier,
* it should not be imported into lower PDE/Paper2 files,
* and it should not live in Paper3-specific statement assembly.

No new imports should be needed if the local patch already passes.

## Hidden-false-claim audit

I do not see a hidden false analytic claim in the described layer.  The crucial honesty points are all respected:

* It does not conclude `IntegratedMoserFirstCrossingStep`.
* It does not conclude `LpPowerBoundedBefore D (p + rho) T u`.
* It keeps energy nonnegativity explicit at the abstract `BoundedDomainData` level.
* It keeps max-one integrability explicit/produced from integrability, not from mere boundedness.
* It requires interior window hypotheses `0 < a`, `b < T` for relative-Moser pointwise inputs.
* It uses endpoint membership `a ∈ Icc 0 T`, `b ∈ Icc a T` for the integrated dissipation extraction.
* It requires `0 ≤ rho` or equivalent to ask regularity for `p + rho`.

The only thing to watch is wording: comments should say “precrossing/window” rather than “first-crossing step” or “bootstrap step.”  The latter can be misread as already proving the pointwise extraction.

## Suggested final local names

If this patch is not yet stabilized downstream, I recommend this exact naming set:

```lean
integratedMoserEnergy
integratedMoserGradientEnergy
intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
Icc_subset_uIcc_zero_T_of_endpoint_memberships
intervalIntegrable_max_one_of_intervalIntegrable
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
IntegratedMoserEnergyNonnegativity
exists_currentEnergy_Icc_bound_of_LpPowerBoundedBefore
IntegratedMoserPrecrossingIntervalData
integratedMoserPrecrossingIntervalData_of_regular_window
IntegratedMoserWindowUpperBound
integratedMoser_windowUpperBound_of_precrossing
```

If the existing local patch already uses `IntegratedMoserWindowUpperBoundData`, keep it unless you want to align `Data` with structure/accessor style.

## Recommended `#print axioms` targets

After this plumbing layer, the important targets are:

```lean
#print axioms intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
#print axioms Icc_subset_uIcc_zero_T_of_endpoint_memberships
#print axioms intervalIntegrable_max_one_of_intervalIntegrable
#print axioms IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
#print axioms IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
#print axioms IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
#print axioms currentEnergy_Icc_bound_of_LpPowerBoundedBefore
#print axioms integratedMoserPrecrossingIntervalData_of_regular_window
#print axioms integratedMoser_windowUpperBoundData_of_precrossing
```

Adjust the last two names if you rename `WindowUpperBoundData` to `WindowUpperBound`.

## Next honest frontier after this layer

The next theorem should still be frontier-parameterized, for example:

```lean
structure IntegratedMoserHighExcursionContradictionFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  choose_level_and_contradict :
    -- high-excursion/window-thickness/AC-modulus content here
    ...
```

Then the eventual wrapper can be:

```lean
theorem integratedMoserFirstCrossingStep_of_windowUpper_and_highExcursion
    ...
    (hupper : IntegratedMoserWindowUpperEstimateProvider D u T rho p0)
    (hexcur : IntegratedMoserHighExcursionContradictionFrontier D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0 := by
  ...
```

Do not skip this frontier by converting a window integral directly to a pointwise bound.
