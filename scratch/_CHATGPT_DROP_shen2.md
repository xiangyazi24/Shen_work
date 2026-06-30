# Q2446 shen2: next honest integrated-Moser lemma after max-one bound

Repo target: `xiangyazi24/Shen_work`.

## Verdict

The next smallest mathematically honest lemma is a **time-integrated relative-Moser interpolation bound** on a fixed subinterval.  It should take as inputs:

* the existing pointwise `RelativeMoserInterpolationBefore`,
* a current-exponent bound `Y_p(s) ≤ M` on `Set.Icc a b`,
* interval-integrability of the higher-power and gradient terms on `a..b`,
* optionally a bound on the integrated gradient term.

It should output a bound for

```lean
∫ s in a..b, D.integral (fun x => (u s x) ^ (p + rho))
```

in terms of

```lean
eps * ∫ s in a..b, D.integral (fun x => (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)
```

plus a lower-order time-length term.  This is exactly the missing algebraic bridge after the gradient-integral extraction lemma: once `∫G_p` is bounded, relative interpolation gives a time-integral bound for `Y_{p+rho}`.

This does **not** smuggle the hard theorem.  It does not prove pointwise control of `Y_{p+rho}`, does not construct a first-crossing time, and does not produce `IntegratedMoserFirstCrossingStep`.  It only integrates an already-assumed pointwise interpolation inequality over a fixed interval.

## Why this is the right next lemma

Current Stage 1 already has the closure consumers from a supplied `IntegratedMoserFirstCrossingStep`.  The integrated dissipation side can now extract a gradient-integral bound from endpoint/time-integral bounds.  The previous max-one lemma supplies the time-integral bound for the `max 1 Y_p` term under a uniform pre-crossing bound.

The next bottleneck is therefore the other half of the Moser step:

```lean
Y_{p+rho}(s) ≤ eps * G_p(s) + Ceps * Y_p(s)
```

from `RelativeMoserInterpolationBefore`, integrated over `s ∈ [a,b]`.  The lemma below packages only that fixed-interval integration.

## Imports / namespace

Put this in:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

inside:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

The file's existing import/open block should be enough:

```lean
import ShenWork.PDE.P3MoserDissipationShape

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval
```

The proof uses the same interval-integral API already used in the repo, especially:

```lean
intervalIntegral.integral_mono_on
intervalIntegral.integral_add
intervalIntegral.integral_const_mul
intervalIntegral.integral_const
intervalIntegrable_const
```

## Proposed code: generic affine interval-integral helper

This generic helper is useful beyond Moser and keeps the specialized lemma short.

```lean
/-- Integrate a pointwise affine upper bound over an oriented interval.

This is pure interval-integral bookkeeping: if `F ≤ A * G + B` on `[a,b]`,
then the interval integral of `F` is bounded by the affine expression in the
interval integral of `G`. -/
theorem intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
    {a b A B : ℝ} {F G : ℝ → ℝ}
    (hab : a ≤ b)
    (hF_int : IntervalIntegrable F MeasureTheory.volume a b)
    (hG_int : IntervalIntegrable G MeasureTheory.volume a b)
    (hpoint : ∀ s ∈ Set.Icc a b, F s ≤ A * G s + B) :
    ∫ s in a..b, F s ≤
      A * ∫ s in a..b, G s + (b - a) * B := by
  have hR_int :
      IntervalIntegrable (fun s => A * G s + B) MeasureTheory.volume a b :=
    (hG_int.const_mul A).add intervalIntegrable_const
  have hmono :=
    intervalIntegral.integral_mono_on hab hF_int hR_int hpoint
  have hR :
      (∫ s in a..b, A * G s + B) =
        A * ∫ s in a..b, G s + (b - a) * B := by
    rw [intervalIntegral.integral_add
      (hG_int.const_mul A) intervalIntegrable_const]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [hR] at hmono
  exact hmono
```

If the method name `hG_int.const_mul A` is brittle in the local Mathlib version, use the same idea with whichever spelling Lean suggests for scalar multiplication of an `IntervalIntegrable` function.  The repo already uses `.add intervalIntegrable_const`, so the only uncertain syntactic point is the scalar-multiplication method name.

## Proposed code: integrated relative-Moser bound

This is the actual next Moser-specific lemma.

```lean
/-- Integrate the relative Moser interpolation inequality over a time interval,
using a uniform current-exponent bound on that interval.

This is a fixed-interval estimate.  It does not assert any first-crossing or
pointwise-in-time bound for the higher exponent. -/
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
        MeasureTheory.volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
        MeasureTheory.volume a b)
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        D.integral (fun x => (u s x) ^ p) ≤ M) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * ∫ s in a..b,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) +
        (b - a) * (Ceps * M) := by
  rcases hrel p hp eps heps with ⟨Ceps, hCeps_nonneg, hrel_eps⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  exact
    intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
      (F := fun s => D.integral (fun x => (u s x) ^ (p + rho)))
      (G := fun s =>
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
      (A := eps) (B := Ceps * M)
      hab hZ_int hG_int
      (by
        intro s hs
        have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
        have hsT : s < T := lt_of_le_of_lt hs.2 hb
        have hrel_s := hrel_eps s hs0 hsT
        have hY_s := hY_le s hs
        have hCY_s :
            Ceps * D.integral (fun x => (u s x) ^ p) ≤ Ceps * M :=
          mul_le_mul_of_nonneg_left hY_s hCeps_nonneg
        linarith)
```

## Optional follow-up in the same patch: consume a supplied gradient-integral bound

If the preceding gradient-extraction lemma returns a separate bound

```lean
∫ G ≤ Gbound
```

then this wrapper is a useful one-line combination.  It is still not the first-crossing theorem: it only turns a supplied gradient-integral bound into a supplied higher-power time-integral bound.

```lean
/-- Integrated relative-Moser bound after substituting a supplied bound on the
integrated gradient term. -/
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps Gbound : ℝ}
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab : a ≤ b)
    (ha : 0 < a)
    (hb : b < T)
    (hZ_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
        MeasureTheory.volume a b)
    (hG_int :
      IntervalIntegrable
        (fun s =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
        MeasureTheory.volume a b)
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        D.integral (fun x => (u s x) ^ p) ≤ M)
    (hG_le :
      ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤ Gbound) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * Gbound + (b - a) * (Ceps * M) := by
  rcases
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M) (eps := eps)
      hrel hp heps hab ha hb hZ_int hG_int hY_le with
    ⟨Ceps, hCeps_nonneg, htime⟩
  refine ⟨Ceps, hCeps_nonneg, ?_⟩
  have hscaled :
      eps * ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      eps * Gbound :=
    mul_le_mul_of_nonneg_left hG_le heps.le
  linarith
```

This optional wrapper is often the most convenient consumer after
`integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds`, because that extraction lemma likely outputs exactly `hG_le` or a bound on `2 * ∫G` that can be rescaled.

## Why this is not smuggling the hard theorem

These lemmas assume all fixed-interval input data explicitly:

* interval-integrability of the higher-power term `Y_{p+rho}`;
* interval-integrability of the gradient term `G_p`;
* a uniform current-exponent bound `Y_p ≤ M` on the chosen interval;
* optionally a supplied integrated-gradient bound.

They do **not** prove:

```lean
LpPowerBoundedBefore D (p + rho) T u
```

and they do **not** infer pointwise control from a time-integral estimate.  The later hard first-crossing step still has to use continuity of `Y_{p+rho}` to turn a time-integral contradiction into pointwise boundedness.  That is the genuine analytic part and remains outside these lemmas.

## Suggested `#print axioms`

```lean
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

Expected profile: no `sorryAx`, no custom axioms.  These are order/interval-integral wrappers over existing assumptions.
