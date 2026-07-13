ANSWER Q3961 aed3a9ff

# Q3961: truncated chemotaxis flux regularity at positive time

I found the three target stubs in `ShenWork/Paper2/IntervalTruncatedPositiveTimeBootstrap.lean` in namespace `ShenWork.Paper2.TruncatedPositiveTimeBootstrap`. The flux is exactly

```lean
def truncatedChemFluxLifted (p : CM2Params) (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun y => positivePart (intervalDomainLift w y) * resolverGradReal p w y
    / (1 + intervalDomainLift (intervalNeumannResolverR p w) y) ^ p.β
```

The following is the Lean-facing proof plan I would use. It deliberately separates the low-level analytic facts into named helper lemmas. The target theorem bodies then become short, stable, and use the existing positive-time bootstrap theorems such as `truncatedPicardLimit_gradient_bound_positive_time`.

Two cautions are important.

First, the exceptional set for `positivePart ∘ u` should **not** be stated as the full zero set `{x | u x = 0}`. A `C¹` function can have an uncountable zero set. The countable set is the **transversal zero set** `{x | u x = 0 ∧ deriv u x ≠ 0}`. At zeros with `deriv u x = 0`, `positivePart ∘ u` is differentiable with derivative `0`.

Second, continuity and differentiability of the quotient require a denominator floor, for example `0 < η ≤ 1 + R(x)` on `[0,1]`. In this project that should come from resolver positivity / strict positivity for the elliptic Neumann resolver. If that floor is not available from the current hypotheses, the continuity and derivative-bound statements are analytically under-specified.

## Drop-in Lean skeleton

Put the helper interface before the `Level 4c: Chem flux regularity` section, prove the helper lemmas in the indicated upstream files, and then replace the three theorem bodies by the bodies below.

```lean
import ShenWork.Paper2.IntervalBFormCron2TruncatedCoefficientWeakTest
import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard
import ShenWork.Paper2.IntervalCoeffLadderFull
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.PDE.CosineSpectrum
import ShenWork.PDE.IntervalResolverSpatialC2
import ShenWork.PDE.IntervalResolverPositivity
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Set Filter Topology
open scoped BigOperators Topology Real

noncomputable section

namespace ShenWork.Paper2.TruncatedPositiveTimeBootstrap

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.Paper2.BFormPositiveDatumNegPart
  (truncatedChemFluxLifted truncatedChemDivSourceCoeff
   truncatedLogisticSourceCoeff truncatedBFormSourceCoeff
   truncatedLogisticLocal truncatedLogisticLifted
   truncatedPicardCoeff truncatedPicardCoeffTimeDeriv
   truncatedPicardInitialCoeff
   truncatedConjugatePicardIter
   truncatedConjugatePicardIter_ball
   truncatedConjugatePicardIter_geometric
   truncatedConjugatePicardLimit
   truncatedConjugateMildExistenceData
   truncatedConjugateMildSolutionData
   truncatedConjugateMildSolutionData_of_data
   negativePartTest cosineTestCoeff)

/-! ### Small data-derived facts already provable from the file -/

private theorem truncatedLimit_hasContinuousSlices_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) :
    HasContinuousSlices DT.T (truncatedConjugatePicardLimit p u₀ DT.T) := by
  have hball_cont := fun n =>
    truncatedConjugatePicardIter_ball p u₀ DT.hbase_ball DT.hbase_cont
      DT.hmapsTo DT.hcont_preserved DT.hbase_meas DT.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hcont_iterates := fun n => (hball_cont n).2
  have hmeas_iterates : ∀ n,
      HasJointMeasurability (truncatedConjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact DT.hbase_meas
    | succ n ih => exact DT.hmeas_preserved _ ih
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ DT.hK_nn hball
    hcont_iterates hmeas_iterates DT.hcontr DT.hC₀ DT.hbase_diff
  exact truncatedConjugatePicardLimit_hasContinuousSlices p u₀ DT.hT
    DT.hK DT.hK_nn DT.hC₀ (fun n => hgeom n) hcont_iterates

private theorem truncatedLimit_bounded_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) :
    ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ DT.T t x| ≤ DT.M := by
  have hball_cont := fun n =>
    truncatedConjugatePicardIter_ball p u₀ DT.hbase_ball DT.hbase_cont
      DT.hmapsTo DT.hcont_preserved DT.hbase_meas DT.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hcont_iterates := fun n => (hball_cont n).2
  have hmeas_iterates : ∀ n,
      HasJointMeasurability (truncatedConjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact DT.hbase_meas
    | succ n ih => exact DT.hmeas_preserved _ ih
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ DT.hK_nn hball
    hcont_iterates hmeas_iterates DT.hcontr DT.hC₀ DT.hbase_diff
  exact truncatedConjugatePicardLimit_bounded p u₀ DT.hK DT.hK_nn DT.hC₀
    (fun n => hgeom n) hball

/-! ### Helper interface to prove upstream

These are the real analytic obligations. They are intentionally stated in the
form consumed by the target theorem bodies. In production, do not leave them as
`axiom`; prove them in the resolver / one-dimensional calculus files.
-/

/-- A continuous function on the subtype interval has a continuous lifted real
representative on `[0,1]`. Proof: on points of `Icc 0 1`, rewrite
`intervalDomainLift w x` to `w ⟨x,hx⟩` and compose `hw` with the continuous
subtype embedding. -/
axiom intervalDomainLift_continuousOn_Icc_of_continuous
    {w : intervalDomainPoint → ℝ} :
    Continuous w → ContinuousOn (intervalDomainLift w) (Icc (0 : ℝ) 1)

/-- Positive-time spectral regularity gives pointwise differentiability of the
lifted limit slice on the open interval. This is the differentiability companion
to `truncatedPicardLimit_gradient_bound_positive_time`, coming from the same
`Σ |a_k| kπ < ∞` termwise differentiated cosine series argument. -/
axiom truncatedPicardLimit_hasDerivAt_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt
        (intervalDomainLift ((truncatedConjugatePicardLimit p u₀ DT.T) t))
        (deriv (intervalDomainLift
          ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x) x

/-- Countability of transversal zeros. This is the correct countability lemma:
the full zero set of a `C¹` function need not be countable. Proof: if
`f x = 0` and `f' x ≠ 0`, the derivative definition makes `x` an isolated zero;
any set of isolated points in `ℝ` is countable. -/
axiom transversal_zeroSet_countable_of_hasDerivAt
    {f : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt f (deriv f x) x) :
    ({x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ f x = 0 ∧ deriv f x ≠ 0}).Countable

/-- Flux continuity from continuity of the slice and elliptic resolver regularity.
Proof outline: `positivePart` is continuous because it is `max id 0`; the
resolver value and `resolverGradReal` are continuous on `[0,1]`; the denominator
has a positive floor; then use product and quotient continuity. -/
axiom truncatedChemFluxLifted_continuousOn_of_lift_continuousOn
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hw : ContinuousOn (intervalDomainLift w) (Icc (0 : ℝ) 1)) :
    ContinuousOn (truncatedChemFluxLifted p w) (Icc (0 : ℝ) 1)

/-- Flux differentiability away from transversal zeros of `u`. The resolver
factors are `C¹`; `positivePart ∘ u` is differentiable at all non-transversal
points: away from zero it is locally either `u` or `0`, and at a zero with
`u' = 0` its derivative is `0`. -/
axiom truncatedChemFluxLifted_hasDerivAt_off_transversalZeros
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hwC1 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift w)
        (deriv (intervalDomainLift w) x) x)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnotTrans :
      ¬ (intervalDomainLift w x = 0 ∧ deriv (intervalDomainLift w) x ≠ 0)) :
    HasDerivAt (truncatedChemFluxLifted p w)
      (deriv (truncatedChemFluxLifted p w) x) x

/-- Uniform derivative bound for the flux. The proof expands the derivative of
`u₊ · R_x · (1+R)^(-β)` and bounds the factors on the compact interval. The
inputs used here are exactly the positive-time value bound, the positive-time
gradient bound, continuity/compactness, resolver `C²` bounds, and denominator
floor. -/
axiom truncatedChemFluxLifted_deriv_bound_of_gradient_bound
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M G : ℝ}
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, |intervalDomainLift w x| ≤ M)
    (hGnn : 0 ≤ G)
    (hG : ∀ x ∈ Icc (0 : ℝ) 1, |deriv (intervalDomainLift w) x| ≤ G)
    (hwcont : ContinuousOn (intervalDomainLift w) (Icc (0 : ℝ) 1)) :
    ∃ C_chem : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (truncatedChemFluxLifted p w) x| ≤ C_chem

/-! ### Target theorem bodies -/

theorem truncatedChemFlux_continuousOn_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ContinuousOn
      (truncatedChemFluxLifted p
        ((truncatedConjugatePicardLimit p u₀ DT.T) t))
      (Icc (0 : ℝ) 1) := by
  let w : intervalDomainPoint → ℝ :=
    (truncatedConjugatePicardLimit p u₀ DT.T) t
  have hslice_cont : Continuous w := by
    simpa [w] using (truncatedLimit_hasContinuousSlices_of_data DT t ht htT)
  have hw_lift_cont : ContinuousOn (intervalDomainLift w) (Icc (0 : ℝ) 1) :=
    intervalDomainLift_continuousOn_Icc_of_continuous hslice_cont
  simpa [w] using
    truncatedChemFluxLifted_continuousOn_of_lift_continuousOn
      (p := p) (w := w) hw_lift_cont

theorem truncatedChemFlux_diff_off_countable_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ s_chem : Set ℝ, s_chem.Countable ∧
      ∀ x ∈ Ioo (0 : ℝ) 1 \ s_chem,
        HasDerivAt
          (truncatedChemFluxLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) t))
          (deriv (truncatedChemFluxLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x) x := by
  classical
  let w : intervalDomainPoint → ℝ :=
    (truncatedConjugatePicardLimit p u₀ DT.T) t
  let uLift : ℝ → ℝ := intervalDomainLift w
  let Z : Set ℝ :=
    {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ uLift x = 0 ∧ deriv uLift x ≠ 0}
  have huC1 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt uLift (deriv uLift x) x := by
    simpa [uLift, w] using
      truncatedPicardLimit_hasDerivAt_positive_time DT ht htT
  refine ⟨Z, ?_, ?_⟩
  · simpa [Z, uLift] using
      transversal_zeroSet_countable_of_hasDerivAt (f := uLift) huC1
  · intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hx.1
    have hxnotZ : x ∉ Z := hx.2
    have hnotTrans : ¬ (uLift x = 0 ∧ deriv uLift x ≠ 0) := by
      intro htrans
      exact hxnotZ ⟨hxIoo, htrans.1, htrans.2⟩
    simpa [uLift, w] using
      truncatedChemFluxLifted_hasDerivAt_off_transversalZeros
        (p := p) (w := w) huC1 hxIoo hnotTrans

theorem truncatedChemFlux_deriv_bound_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ DT.T) :
    ∃ C_chem : ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (truncatedChemFluxLifted p
        ((truncatedConjugatePicardLimit p u₀ DT.T) t)) x| ≤ C_chem := by
  let w : intervalDomainPoint → ℝ :=
    (truncatedConjugatePicardLimit p u₀ DT.T) t
  have hbound_point : ∀ z : intervalDomainPoint, |w z| ≤ DT.M := by
    simpa [w] using truncatedLimit_bounded_of_data DT t ht htT
  have hM_lift : ∀ x ∈ Icc (0 : ℝ) 1, |intervalDomainLift w x| ≤ DT.M := by
    intro x hx
    have h := hbound_point ⟨x, hx⟩
    simpa [w, intervalDomainLift, hx] using h
  obtain ⟨G, hGnn, hG⟩ :=
    truncatedPicardLimit_gradient_bound_positive_time DT ht htT
  have hslice_cont : Continuous w := by
    simpa [w] using (truncatedLimit_hasContinuousSlices_of_data DT t ht htT)
  have hw_lift_cont : ContinuousOn (intervalDomainLift w) (Icc (0 : ℝ) 1) :=
    intervalDomainLift_continuousOn_Icc_of_continuous hslice_cont
  simpa [w] using
    truncatedChemFluxLifted_deriv_bound_of_gradient_bound
      (p := p) (w := w) (M := DT.M) (G := G)
      hM_lift hGnn hG hw_lift_cont

end ShenWork.Paper2.TruncatedPositiveTimeBootstrap
```

## What the helper lemmas must prove

### 1. `truncatedChemFluxLifted_continuousOn_of_lift_continuousOn`

For `u = intervalDomainLift w`, `R = intervalDomainLift (intervalNeumannResolverR p w)`, and `g = resolverGradReal p w`, rewrite

```lean
truncatedChemFluxLifted p w x
  = positivePart (u x) * g x / (1 + R x) ^ p.β
```

Then prove:

* `ContinuousOn u (Icc 0 1)` from the slice continuity.
* `ContinuousOn (fun x => positivePart (u x)) (Icc 0 1)` using `positivePart = max id 0`.
* `ContinuousOn R (Icc 0 1)` and `ContinuousOn g (Icc 0 1)` from elliptic resolver regularity.
* `∀ x ∈ Icc 0 1, (1 + R x) ^ p.β ≠ 0` from the resolver floor.
* close by `mul` and `div` for `ContinuousOn`.

The natural resolver regularity theorem is either the existing spectral `SourceCoeffQuadraticDecay → ContDiffOn ℝ 2` route in `IntervalResolverSpatialC2`, or a more PDE-style theorem saying continuous input gives a `C²` Neumann solution of `-R'' + μR = ν u^γ`.

### 2. `transversal_zeroSet_countable_of_hasDerivAt`

Do not try to prove the full zero set countable. Use transversal zeros.

For a zero `x` with `deriv f x = a ≠ 0`, the derivative definition gives a punctured neighborhood where `(f y - f x)/(y-x)` is close to `a`, hence nonzero. Since `f x = 0`, no other zero lies in that punctured neighborhood. Thus every transversal zero is isolated. A subset of `ℝ` whose points are isolated is countable by choosing, for each isolated point, a rational in a small isolating interval.

At non-transversal zeros (`f x = 0`, `deriv f x = 0`), the derivative of `positivePart ∘ f` is `0` because

```lean
0 ≤ positivePart (f y) ≤ |f y|
```

and `|f y| / |y-x| → 0` follows from `HasDerivAt f 0 x`.

### 3. `truncatedChemFluxLifted_hasDerivAt_off_transversalZeros`

Let

```lean
u  := intervalDomainLift w
up := fun x => positivePart (u x)
R  := fun x => intervalDomainLift (intervalNeumannResolverR p w) x
g  := fun x => resolverGradReal p w x
q  := fun x => ((1 + R x) ^ p.β)⁻¹
F  := fun x => up x * g x * q x
```

The resolver supplies `HasDerivAt R (g x) x`, `HasDerivAt g (R₂ x) x`, and the denominator floor supplies differentiability of `q`. The only branch is `up`:

* if `u x > 0`, `up = u` locally;
* if `u x < 0`, `up = 0` locally;
* if `u x = 0` and `deriv u x = 0`, `HasDerivAt up 0 x`;
* if `u x = 0` and `deriv u x ≠ 0`, this is exactly the excluded set.

Then use `HasDerivAt.mul`, `HasDerivAt.div`, or equivalently the product rule on `up * g * q`. The derivative value can be converted to `deriv F x` using `HasDerivAt.deriv`.

### 4. `truncatedChemFluxLifted_deriv_bound_of_gradient_bound`

With `A = 1 + R`, `g = R'`, and `up = u₊`, the derivative is

```text
F' = up' * g * A^(-β)
   + up  * g' * A^(-β)
   - β * up * g * g * A^(-β-1).
```

On the compact interval obtain constants:

```text
|up|  ≤ M
|up'| ≤ G
|g|   ≤ B₁
|g'|  ≤ B₂
A     ≥ η > 0
|A^(-β)|   ≤ Q₀
|A^(-β-1)| ≤ Q₁
```

Then one valid bound is

```text
C_chem = G * B₁ * Q₀ + M * B₂ * Q₀ + p.β * M * B₁ * B₁ * Q₁
```

or, if resolver positivity gives `A ≥ 1` and `0 ≤ β`, the simpler bound

```text
C_chem = G * B₁ + M * B₂ + p.β * M * B₁ * B₁
```

is enough. In Lean, use `abs_add`, `abs_mul`, the nonnegativity of the constants, and the positive-time theorem

```lean
truncatedPicardLimit_gradient_bound_positive_time DT ht htT
```

for the `G` input.
