# Q1251 (cron3): heat floor for `conjugatePicardIter p u₀ 0`

## Verdict

The current `heatSemigroup_level0_resolverJointC2Data` signature has only

```lean
(hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
(hu₀_cont  : Continuous u₀)
```

Those hypotheses are **not enough** to prove

```lean
∀ t, 0 < t → ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

Counterexample: `u₀ = 0` satisfies continuity and bounded coefficient hypotheses, but
`S(t)u₀ = 0`, so strict positivity is false.

You need at least one of the following additional assumptions on `u₀`:

1. **Project-faithful / strongest / easiest:**

   ```lean
   huPaper : PaperPositiveInitialDatum intervalDomain u₀
   ```

   This carries a closed-domain positive floor
   `∃ η > 0, ∀ x : intervalDomainPoint, η ≤ u₀ x`.

2. **Weaker analytic minimum for strict heat positivity:**

   ```lean
   hu₀_cont : Continuous u₀
   hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x
   hu₀_pos_somewhere : ∃ x : intervalDomainPoint, 0 < u₀ x
   ```

   This is enough by strict positivity of the Neumann heat kernel.

For this project, I would add/pass `huPaper : PaperPositiveInitialDatum intervalDomain u₀` to `heatSemigroup_level0_resolverJointC2Data` (or an enclosing input structure), because it is already the paper-faithful datum and directly provides a clean floor theorem.

## Existing repo theorems found

### 1. Strict heat-kernel positivity from nontrivial nonnegative data

File:

```lean
ShenWork/PDE/IntervalSemigroupConeAtoms.lean
```

Theorem:

```lean
ShenWork.IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_pos
```

Shape:

```lean
theorem intervalFullSemigroupOperator_pos
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Icc (0 : ℝ) 1) (hf_pos : 0 < f y₀)
    (x : ℝ) :
    0 < intervalFullSemigroupOperator t f x
```

This is the theorem to use if your available assumptions are nonnegativity plus positive somewhere.

### 2. Non-strict heat positivity is available but insufficient

File:

```lean
ShenWork/PDE/IntervalResolverPositivity.lean
```

Theorem:

```lean
ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg
```

Shape:

```lean
theorem intervalFullSemigroupOperator_nonneg {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x
```

This only proves `0 ≤ S(t)u₀`, not `0 < S(t)u₀`. It cannot discharge the `hfloor` needed for rpow differentiation.

### 3. Paper-positive floor route

File:

```lean
ShenWork/Paper2/IntervalConjugatePicardInfThreshold.lean
```

Definitions/theorems:

```lean
ShenWork.IntervalConjugatePicard.paperPositiveFloor
ShenWork.IntervalConjugatePicard.paperPositiveFloor_pos
ShenWork.IntervalConjugatePicard.paperPositiveFloor_le
ShenWork.IntervalConjugatePicard.intervalFullSemigroupOperator_ge_paperPositiveFloor
```

The important theorem is:

```lean
theorem intervalFullSemigroupOperator_ge_paperPositiveFloor
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    paperPositiveFloor hu₀ ≤
      intervalFullSemigroupOperator t (intervalDomainLift u₀) x
```

Since `paperPositiveFloor_pos hu₀ : 0 < paperPositiveFloor hu₀`, this immediately gives
`0 < intervalFullSemigroupOperator t (intervalDomainLift u₀) x` for all real `x` and all `t > 0`.

### 4. What `PaperPositiveInitialDatum` means

File:

```lean
ShenWork/Paper2/Statements.lean
```

Definition:

```lean
def PaperPositiveInitialDatum (D : BoundedDomainData) (u₀ : D.Point → ℝ) : Prop :=
  D.initialAdmissible u₀ ∧ ∃ η : ℝ, 0 < η ∧ ∀ x : D.Point, η ≤ u₀ x
```

So `PaperPositiveInitialDatum intervalDomain u₀` is exactly a closed-domain positive floor.

### 5. Continuous strict positivity can be upgraded to `PaperPositiveInitialDatum`

File:

```lean
ShenWork/Paper2/IntervalPositiveDatumThreshold.lean
```

Theorem:

```lean
ShenWork.Paper2.IntervalMildExistenceAssembly.intervalDomain_paperPositiveInitialDatum_of_continuous_pos
```

Shape:

```lean
theorem intervalDomain_paperPositiveInitialDatum_of_continuous_pos
    {u₀ : intervalDomainPoint → ℝ}
    (hadm : intervalDomain.initialAdmissible u₀)
    (hu₀_cont : Continuous u₀) (hu₀_pos : ∀ x, 0 < u₀ x) :
    PaperPositiveInitialDatum intervalDomain u₀
```

So if you already have admissibility, continuity, and strict positivity everywhere on the subtype, you can manufacture the paper-positive datum.

### 6. `[0,1]` floor theorem for real-space sources

File:

```lean
ShenWork/Wiener/EWA/HeatFloorIcc.lean
```

Theorem:

```lean
ShenWork.EWA.intervalFullSemigroupOperator_ge_floor_Icc
```

Shape:

```lean
theorem intervalFullSemigroupOperator_ge_floor_Icc {t : ℝ} (ht : 0 < t)
    {u₀ : ℝ → ℝ} (hu₀ : Continuous u₀) {δ : ℝ}
    (hfloor : ∀ y ∈ Set.Icc (0 : ℝ) 1, δ ≤ u₀ y) (x : ℝ) :
    δ ≤ intervalFullSemigroupOperator t u₀ x
```

This is useful for continuous real-space representatives. It is usually **not** the best theorem for `intervalDomainLift u₀`, because the zero-extension lift is generally discontinuous at `0,1` when `u₀` has a positive boundary value. The `PaperPositiveInitialDatum` theorem above is tailored to `intervalDomainLift u₀` and avoids that issue.

## Recommended wiring: use `PaperPositiveInitialDatum`

Add this import where you fill `hfloor`:

```lean
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold
```

Then add a helper:

```lean
import ShenWork.Paper2.IntervalConjugatePicardInfThreshold

open Set
open ShenWork.IntervalDomain (intervalDomain intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

/-- Positive heat floor for the level-0 conjugate Picard iterate from a
paper-positive initial datum. -/
theorem level0_heat_hfloor_of_paperPositive
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huPaper : PaperPositiveInitialDatum intervalDomain u₀) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
  intro t ht x hx
  have hfloor_le :
      ShenWork.IntervalConjugatePicard.paperPositiveFloor huPaper ≤
        intervalFullSemigroupOperator t (intervalDomainLift u₀) x :=
    ShenWork.IntervalConjugatePicard.intervalFullSemigroupOperator_ge_paperPositiveFloor
      huPaper ht x
  have hfloor_pos :
      0 < ShenWork.IntervalConjugatePicard.paperPositiveFloor huPaper :=
    ShenWork.IntervalConjugatePicard.paperPositiveFloor_pos huPaper
  have hS_pos : 0 < intervalFullSemigroupOperator t (intervalDomainLift u₀) x :=
    lt_of_lt_of_le hfloor_pos hfloor_le
  simpa [conjugatePicardIter, intervalDomainLift, hx] using hS_pos

end ShenWork.Paper2.HeatResolverJointRegularity
```

Then change the resolver-data theorem signature from:

```lean
theorem heatSemigroup_level0_resolverJointC2Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
```

to:

```lean
theorem heatSemigroup_level0_resolverJointC2Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (huPaper : PaperPositiveInitialDatum intervalDomain u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
```

and fill the existing `hfloor := ...` argument as:

```lean
  have hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x :=
    level0_heat_hfloor_of_paperPositive (p := p) huPaper

  have hFSTD :=
    ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData.heatSemigroup_flooredSourceTimeData
      hu₀_bound hu₀_cont (p := p) (hfloor := hfloor)
```

This is the shortest project-native route.

## Weaker route: nonnegative and positive somewhere

If you do not want to thread `PaperPositiveInitialDatum`, the strict heat-kernel theorem gives a weaker alternative. Add:

```lean
import ShenWork.PDE.IntervalSemigroupConeAtoms
```

Then use:

```lean
import ShenWork.PDE.IntervalSemigroupConeAtoms
import ShenWork.Paper2.IntervalConjugatePicard

open Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointRegularity

/-- Positive heat floor for the level-0 conjugate Picard iterate from a continuous,
nonnegative, nontrivial initial datum. -/
theorem level0_heat_hfloor_of_nonneg_pos_somewhere
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x)
    (hu₀_pos_somewhere : ∃ x : intervalDomainPoint, 0 < u₀ x) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x := by
  intro t ht x hx

  have hlift_cont : ContinuousOn (intervalDomainLift u₀) (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have hrestr : Set.restrict (Icc (0 : ℝ) 1) (intervalDomainLift u₀) = u₀ := by
      funext y
      rcases y with ⟨y, hy⟩
      simp [Set.restrict_apply, intervalDomainLift, hy]
    simpa [hrestr] using hu₀_cont

  have hlift_nonneg : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ y := by
    intro y hy
    simpa [intervalDomainLift, hy] using hu₀_nonneg ⟨y, hy⟩

  obtain ⟨y₀p, hy₀p_pos⟩ := hu₀_pos_somewhere
  let y₀ : ℝ := y₀p.1
  have hy₀ : y₀ ∈ Icc (0 : ℝ) 1 := y₀p.2
  have hy₀_pos : 0 < intervalDomainLift u₀ y₀ := by
    simpa [y₀, intervalDomainLift, hy₀] using hy₀p_pos

  have hS_pos : 0 < intervalFullSemigroupOperator t (intervalDomainLift u₀) x :=
    ShenWork.IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_pos
      ht hlift_cont hlift_nonneg hy₀ hy₀_pos x

  simpa [conjugatePicardIter, intervalDomainLift, hx] using hS_pos

end ShenWork.Paper2.HeatResolverJointRegularity
```

This route proves the same `hfloor`, but it requires carrying both nonnegativity and nontriviality. If you only have

```lean
hu₀_nonneg : ∀ x, 0 ≤ u₀ x
```

then you are still missing `∃ x, 0 < u₀ x`; otherwise the zero datum is a counterexample.

## Recommendation

For `heatSemigroup_level0_resolverJointC2Data`, use:

```lean
huPaper : PaperPositiveInitialDatum intervalDomain u₀
```

as the extra hypothesis. It is the faithful paper datum, it implies strict positivity via the already-proved floor theorem, and it avoids proving continuity of `intervalDomainLift u₀` as a real-space function.
