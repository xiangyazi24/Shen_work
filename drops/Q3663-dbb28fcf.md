ANSWER Q3663 dbb28fcf

# Task202 audit: concrete C1/eta `w_split` / cutoff representation

## Verdict

There is **no existing end-to-end theorem** on `origin/main`/`b7e37b3e` that proves the current phase-1 C1/eta consumer's concrete `w_split` directly from `GradientMildSolutionData`.

The repo has all the pieces for a small representation/cutoff atom, but there is an important scope issue:

* For the **true lifted slice** `w := intervalDomainLift (Dsol.u t)`, the current global field
  ```lean
  w_split : ∀ x : ℝ,
    w x = initialValueLeg t (intervalDomainLift u₀) x
      - χ₀ * chemLitLeg t (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x
      + reactionValueLeg t L x
  ```
  is not provable as stated.  Outside `[0,1]`, `intervalDomainLift (Dsol.u t) x = 0`, while the heat/Duhamel RHS is generally not zero.
* On `x ∈ Icc 0 1`, the representation is small: use `Dsol.hmild`, unfold `intervalGradientDuhamelMap`, and replace the raw flux/reaction sources by time cutoffs using `intervalIntegral.integral_congr_ae` on `uIoc 0 t`.
* Therefore Task202 should either
  1. introduce a **global smooth representative** `wRep` defined by the RHS and prove `wRep = intervalDomainLift (Dsol.u t)` on `[0,1]`; or
  2. refactor the C1/eta bridge to carry only `w_split_Icc`, which is larger because the current bridge also uses the global RHS equality to prove `Continuous w`.

I recommend option (1) as the small Task202: define/instantiate the C1/eta slice for the global RHS representative, and bank an `[0,1]` agreement theorem with the real mild slice.  Later transfer cosine coefficients to the real lifted slice by an `Icc` congruence theorem such as the existing `cosineCoeffs_congr_on_Icc` pattern.

## Existing APIs/fields that give the mild equation and legs

### The real mild equation

File: `ShenWork/Paper2/IntervalGradientDuhamelMap.lean`

* `chemFluxLifted` is the true weak chemotaxis flux:
  ```lean
  def chemFluxLifted (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ := ...
  ```
* `logisticLifted` is the true lifted logistic source:
  ```lean
  def logisticLifted (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ := ...
  ```
* `intervalGradientDuhamelMap` is the weak divergence-form map:
  ```lean
  def intervalGradientDuhamelMap (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
      (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (x : intervalDomainPoint) : ℝ :=
    intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
      + (-p.χ₀) * (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s) (chemFluxLifted p (u s)) z) x.1)
      + ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1
  ```
* `IntervalMildSolution` is the exact fixed-point equation:
  ```lean
  def IntervalMildSolution ... : Prop :=
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      u t x = intervalGradientDuhamelMap p u₀ u t x
  ```

File: `ShenWork/Paper2/IntervalMildPicard.lean`

* `GradientMildSolutionData` exposes this via
  ```lean
  hmild : IntervalMildSolution p T u₀ u
  ```
  together with the fields needed for source cutoffs:
  ```lean
  hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M
  hnonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x
  hcont : HasContinuousSlices T u
  hmeas : HasJointMeasurability u
  ```

So for a concrete slice and `x : intervalDomainPoint`, the starting point is exactly:

```lean
have hm := Dsol.hmild t ht htT x
```

### The C1/eta leg definitions

File: `ShenWork/Paper2/ChemMildC1etaAssembly.lean`

* `initialValueLeg` is the homogeneous value leg:
  ```lean
  noncomputable def initialValueLeg (t : ℝ) (u₀ : ℝ → ℝ) : ℝ → ℝ :=
    fun x => intervalFullSemigroupOperator t u₀ x
  ```
* `reactionValueLeg` is the value reaction Duhamel leg:
  ```lean
  noncomputable def reactionValueLeg (t : ℝ) (L : ℝ → ℝ → ℝ) : ℝ → ℝ :=
    fun x => ∫ s in (0 : ℝ)..t, intervalFullSemigroupOperator (t - s) (L s) x
  ```
* `reactionValueLeg_hasDerivAt` and `reactionValueLeg_deriv_eq` are the phase-1 derivative APIs.

File: `ShenWork/Paper2/ChemMildInterchange.lean`

* `chemLitLeg` is the literal first-derivative chemotaxis Duhamel leg:
  ```lean
  noncomputable def chemLitLeg (t₀ : ℝ) (Q : ℝ → ℝ → ℝ) : ℝ → ℝ :=
    fun x => ∫ s in (0:ℝ)..t₀,
      deriv (fun z : ℝ => intervalFullSemigroupOperator (t₀ - s) (Q s) z) x
  ```
* `chemLitLeg₂` is the differentiated chem leg.
* `chemLeg_interior_hasDerivAt` / `chemLeg_interior_deriv_eq` prove the interior chemotaxis interchange.

File: `ShenWork/Paper2/ChemMildDifferentiableOn.lean`

* This file upgrades the chem leg to the closed-interval `DifferentiableOn` route, but it is not a value-level mild representation theorem.  It supplies `chemLeg_differentiableOn_Icc`, `chemLeg_derivWithin_eq_Icc`, `chemLitLeg_continuousAt`, etc.

### The cutoff chem-flux source

File: `ShenWork/Paper2/IntervalChemFluxHolderFrontier.lean`

The cutoff source already exists:

```lean
def chemFluxCthetaCutoffSource
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) :
    ℝ → ℝ → ℝ :=
  fun s y => if 0 < s ∧ s ≤ T then chemFluxLifted p (u s) y else 0
```

and it has source-regularity helpers:

* `chemFluxCthetaCutoffSource_aestronglyMeasurable`
* `chemFluxCthetaCutoffSource_bound`
* `chemFluxCthetaCutoffSource_holder`

File: `ShenWork/Paper2/IntervalChemFluxHolderSourceDecay.lean`

This file gives source packages such as:

* `ChemFluxCthetaSourceOn_of_gradientMild_uniform_components`
* `ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_components`
* `ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_smallTheta_components`
* `ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_uniformSourceCoeff_components`

These produce `ChemFluxCthetaSourceOn`, hence the cutoff source regularity.  They do **not** prove the mild representation/cutoff `w_split`.

## Exact mismatches

### 1. Subtype domain vs global-ℝ representative

`Dsol.hmild` is an equation for `x : intervalDomainPoint`.  The consumer's `w_split` is an equation for **all** `x : ℝ`.

For `x ∈ Icc 0 1`, one can set `xp : intervalDomainPoint := ⟨x, hx⟩` and use `Dsol.hmild t ht htT xp`.  Outside `[0,1]`, the true lifted solution `intervalDomainLift (Dsol.u t)` is zero, but the RHS made from heat/Duhamel legs is generally nonzero.  Therefore the current global `∀ x` shape should not be targeted with `w := intervalDomainLift (Dsol.u t)`.

This is not just a proof gap; it is mathematically the wrong global representative.

### 2. True flux vs cutoff flux

`intervalGradientDuhamelMap` uses the raw source

```lean
fun s => chemFluxLifted p (Dsol.u s)
```

whereas the C1/eta source package uses

```lean
chemFluxCthetaCutoffSource p Dsol.u Dsol.T
```

These agree only under `0 < s ∧ s ≤ Dsol.T`.  For an integral on `0..t`, the replacement is valid from `ht : 0 < t` and `htT : t ≤ Dsol.T`, because after `Set.uIoc_of_le ht.le`, every relevant `s` satisfies `0 < s ∧ s ≤ t ≤ Dsol.T`.

This is the same local proof pattern already used internally in `IntervalMildPicard.lean` with local `r_grad` and `hgrad_eq`, and in `ChemMildHolderBootstrap.lean` for the reaction leg with a local cutoff `f` and `hcongr`.  But the repo does not expose the needed congruence theorem as a public reusable atom.

### 3. True logistic source vs `L`

The phase-1 consumer is parameterized by an arbitrary `L : ℝ → ℝ → ℝ`, with global assumptions:

```lean
hL_meas : Measurable (Function.uncurry L)
hL_bdd  : ∀ s y, |L s y| ≤ CL
```

Taking

```lean
L := fun s => logisticLifted p (Dsol.u s)
```

matches the raw mild equation, but does **not** directly satisfy the global bound from `Dsol.hbound`, because `Dsol.hbound` is only on `0 < s ≤ Dsol.T`.  Therefore the right concrete `L` for the Task201 consumer should be a public logistic time cutoff, analogous to `chemFluxCthetaCutoffSource`:

```lean
def logisticCutoffSource
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) :
    ℝ → ℝ → ℝ :=
  fun s y => if 0 < s ∧ s ≤ T then logisticLifted p (u s) y else 0
```

There is no existing public `logisticCutoffSource`; only local versions appear in proofs.

### 4. Sign/parameter mismatch

The mild map uses

```lean
+ (-p.χ₀) * G
```

whereas the C1/eta consumer uses

```lean
- χ₀ * chemLitLeg ...
```

The concrete wrapper should instantiate `χ₀ := p.χ₀`, or include a hypothesis `hχ₀ : χ₀ = p.χ₀`.  Do not leave `χ₀` arbitrary.

## Is this a small Task202?

There are two different tasks:

### Small and recommended

A small Task202 is to bank a **global C1/eta representative** plus an `[0,1]` agreement theorem:

```lean
wRep x = initialValueLeg t (intervalDomainLift u₀) x
  - p.χ₀ * chemLitLeg t (chemFluxCthetaCutoffSource p Dsol.u Dsol.T) x
  + reactionValueLeg t (logisticCutoffSource p Dsol.u Dsol.T) x
```

Then the current consumer's global `w_split` is trivial (`rfl`), because `w := wRep`.  The nontrivial theorem is only that `wRep` agrees with the true mild solution on `[0,1]`.

This is small and can live in `ChemMildC1etaUncond.lean`, after adding the reusable logistic cutoff source either there or, better, in a source/cutoff file.

### Larger / not recommended as Task202

Trying to prove the existing global `w_split` for

```lean
w := intervalDomainLift (Dsol.u t)
```

is not faithful.  It fails outside `[0,1]` and also conflicts with the current bridge's use of the global RHS equality to obtain a globally continuous representative.  Refactoring the bridge to use only `w_split_Icc` would be a larger task because the current `differentiatedMildSliceDiffOn_continuous` proof is global.

## Smallest reusable atom to bank first

I would bank these atoms in this order.

### Atom A: public logistic cutoff source

Suggested file: either a new `ShenWork/Paper2/IntervalMildCutoffSources.lean`, or near `chemFluxCthetaCutoffSource` in `IntervalChemFluxHolderFrontier.lean` if you want all time-cutoff source definitions together.  If avoiding import churn, it can be added to `ChemMildC1etaUncond.lean`, but it is reusable enough to deserve a lower-level home.

Unverified skeleton:

```lean
import ShenWork.Paper2.ChemMildC1etaUncond

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (HasJointMeasurability)

namespace ShenWork.Paper2

noncomputable section

/-- Time-cutoff logistic source, matching `logisticLifted p (u s)` on `0 < s ≤ T`. -/
def logisticCutoffSource
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) :
    ℝ → ℝ → ℝ :=
  fun s y => if 0 < s ∧ s ≤ T then logisticLifted p (u s) y else 0

/-- Joint measurability of the logistic cutoff source. -/
theorem logisticCutoffSource_measurable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hmeas : HasJointMeasurability u) :
    Measurable (Function.uncurry (logisticCutoffSource p u T)) := by
  -- same proof pattern as the local cutoff in `holderLeg_reaction`:
  -- use `logisticLifted_uncurry_measurable hmeas`, then `Measurable.ite` on
  -- `{q | 0 < q.1 ∧ q.1 ≤ T}`.
  sorry

/-- Uniform global bound for the cutoff logistic source from the positive-window order box. -/
theorem logisticCutoffSource_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T M : ℝ}
    (hM : 0 < M)
    (hbound : ∀ s, 0 < s → s ≤ T → ∀ x, |u s x| ≤ M) :
    ∀ s y : ℝ,
      |logisticCutoffSource p u T s y| ≤ M * (p.a + p.b * M ^ p.α) := by
  -- same proof pattern as `holderLeg_reaction` local `hf_bdd`.
  intro s y
  by_cases hs : 0 < s ∧ s ≤ T
  · simp [logisticCutoffSource, hs]
    exact logisticLifted_orderBox_bound hM hbound s hs.1 hs.2 y
  · have hCL : 0 ≤ M * (p.a + p.b * M ^ p.α) := by positivity
    simp [logisticCutoffSource, hs, hCL]

end

end ShenWork.Paper2
```

The `sorry`s above are not proposed code; they mark the expected proof bodies.  The measurability proof is already present as a local pattern in `holderLeg_reaction` and as private cutoff machinery in `IntervalMildPicard.lean`.

### Atom B: global RHS representative and Icc agreement

Suggested file: `ChemMildC1etaUncond.lean`, because this is exactly the representation needed by the C1/eta phase-1 value-leg consumer.

Unverified skeleton:

```lean
import ShenWork.Paper2.ChemMildC1etaUncond

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted chemFluxLifted)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

namespace ShenWork.Paper2

noncomputable section

/-- The global smooth representative of the positive-time mild slice used by the C1/eta route. -/
def gradientMildC1etaRepresentative
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (T t : ℝ) : ℝ → ℝ :=
  fun x =>
    initialValueLeg t (intervalDomainLift u₀) x
      - p.χ₀ * chemLitLeg t (chemFluxCthetaCutoffSource p u T) x
      + reactionValueLeg t (logisticCutoffSource p u T) x

/-- The C1/eta bridge `w_split` is definitional for the global representative. -/
theorem gradientMildC1etaRepresentative_w_split
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (T t : ℝ) :
    ∀ x : ℝ,
      gradientMildC1etaRepresentative p u₀ u T t x =
        initialValueLeg t (intervalDomainLift u₀) x
          - p.χ₀ * chemLitLeg t (chemFluxCthetaCutoffSource p u T) x
          + reactionValueLeg t (logisticCutoffSource p u T) x := by
  intro x
  rfl

/-- On `[0,1]`, the global C1/eta representative agrees with the actual mild slice. -/
theorem gradientMildC1etaRepresentative_eq_lift_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      gradientMildC1etaRepresentative p u₀ D.u D.T t x =
        intervalDomainLift (D.u t) x := by
  intro x hx
  let xp : intervalDomainPoint := ⟨x, hx⟩
  have hm := D.hmild t ht htT xp

  have hchem :
      (∫ s in (0:ℝ)..t,
        deriv (fun z =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
            (t - s) (chemFluxLifted p (D.u s)) z) x)
      = chemLitLeg t (chemFluxCthetaCutoffSource p D.u D.T) x := by
    unfold chemLitLeg chemFluxCthetaCutoffSource
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hsT : s ≤ D.T := le_trans hs.2 htT
    simp [hs.1, hsT]

  have hreact :
      (∫ s in (0:ℝ)..t,
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
          (t - s) (logisticLifted p (D.u s)) x)
      = reactionValueLeg t (logisticCutoffSource p D.u D.T) x := by
    unfold reactionValueLeg logisticCutoffSource
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hsT : s ≤ D.T := le_trans hs.2 htT
    simp [hs.1, hsT]

  have hlift : intervalDomainLift (D.u t) x = D.u t xp := by
    simp [intervalDomainLift, hx, xp]

  -- Finish by unfolding the mild map and the representative, then using the two cutoff congruences.
  -- The sign conversion is just `+ (-p.χ₀) * G = - p.χ₀ * G`.
  rw [hlift, hm]
  simp [gradientMildC1etaRepresentative, intervalGradientDuhamelMap,
        initialValueLeg, hchem, hreact, xp]
  ring

end

end ShenWork.Paper2
```

This theorem is intentionally only an `[0,1]` agreement theorem.  It should not be strengthened to `∀ x : ℝ` with `intervalDomainLift`, because that is false in general.

## How this feeds the current Task201 consumer

Use the Task201 consumer with:

```lean
w  := gradientMildC1etaRepresentative p u₀ Dsol.u Dsol.T t
L  := logisticCutoffSource p Dsol.u Dsol.T
χ₀ := p.χ₀
```

Then the required `w_split` is exactly:

```lean
gradientMildC1etaRepresentative_w_split p u₀ Dsol.u Dsol.T t
```

The remaining source-side inputs for `L` are supplied by the new logistic cutoff atoms:

* `logisticCutoffSource_measurable Dsol.hmeas`
* `logisticCutoffSource_bound Dsol.hM Dsol.hbound`
* `CL := Dsol.M * (p.a + p.b * Dsol.M ^ p.α)`

The chem source regularity is still produced by the existing `ChemFluxCthetaSourceOn_of_gradientMild_*` chain and then consumed by `ChemLegData_of_gradientMild_initialHolder_smallTheta_cutoff_components` inside `ChemMildC1etaUncond.lean`.

## What not to do

Do not attempt a global theorem with:

```lean
w := intervalDomainLift (Dsol.u t)
```

and the current `∀ x : ℝ` `w_split`.  It fails outside `[0,1]` and would also give the wrong global continuity story for the diff-on Wiener feed.  The honest route is: global smooth representative for C1/eta, plus an `Icc` agreement/congruence bridge to the actual lifted mild slice.
