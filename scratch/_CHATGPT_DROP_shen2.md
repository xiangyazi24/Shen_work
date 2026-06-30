# Q2438 shen2: next smallest integrated-Moser lemma after gradient extraction

Repo target: `xiangyazi24/Shen_work`, `main` at commit `830352766089c95945fc741ccc208762862c54c6`.

## Verdict

After adding

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
```

the next smallest buildable lemma is exactly the generic interval-integral cap for the `max 1 Y` term:

```lean
∫ s in a..b, max 1 (Y s) ≤ (b - a) * max 1 M
```

from:

* `a ≤ b`,
* `∀ s ∈ Set.Icc a b, Y s ≤ M`,
* interval-integrability of `fun s => max 1 (Y s)` on `a..b`.

This lemma is purely order/interval-integral bookkeeping.  It does not prove any first-crossing step and does not mention `IntegratedMoserDissipationDropBefore`.

The most compile-stable form should take the max-integrability hypothesis explicitly.  Deriving that hypothesis from continuity or from `IntegratedMoserFirstCrossingRegularity.powerTimeIntegrable` is a separate later convenience lemma; do not mix it into this smallest bound lemma.

## Placement

Add the lemma in

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

inside namespace

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

The current file already imports:

```lean
import ShenWork.PDE.P3MoserDissipationShape
```

and already opens:

```lean
open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval
```

No additional import should be necessary for this lemma, because nearby source already uses `intervalIntegral.integral_mono_on`, `intervalIntegrable_const`, and `intervalIntegral.integral_const` under the same dependency chain.

## Exact generic lemma likely to compile

```lean
/-- Bound the integrated `max 1 Y` term by a uniform pointwise bound on `Y`.

This is the small order/interval-integral lemma needed after extracting the
integrated Moser gradient term.  It deliberately assumes interval-integrability
of `max 1 ∘ Y`; producing that integrability from solution regularity can be a
separate later lemma. -/
theorem intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
    {a b M : ℝ} {Y : ℝ → ℝ}
    (hab : a ≤ b)
    (hYmax_int :
      IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) MeasureTheory.volume a b)
    (hY_le : ∀ s ∈ Set.Icc a b, Y s ≤ M) :
    ∫ s in a..b, max (1 : ℝ) (Y s) ≤
      (b - a) * max (1 : ℝ) M := by
  have hpoint :
      ∀ s ∈ Set.Icc a b,
        max (1 : ℝ) (Y s) ≤ max (1 : ℝ) M := by
    intro s hs
    exact max_le
      (le_max_left (1 : ℝ) M)
      (le_trans (hY_le s hs) (le_max_right (1 : ℝ) M))
  have hmono :=
    intervalIntegral.integral_mono_on hab
      hYmax_int intervalIntegrable_const hpoint
  have hconst :
      (∫ _s in a..b, max (1 : ℝ) M) =
        (b - a) * max (1 : ℝ) M := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
  simpa [hconst] using hmono
```

### Why this should compile

The proof uses the same interval-integral API already used in the repo.  For example, `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean` uses:

```lean
intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
  hp_int (hq_int.add intervalIntegrable_const) hpoint
```

and then rewrites constants using:

```lean
rw [intervalIntegral.integral_const]
norm_num [smul_eq_mul]
```

The proposed proof uses the same two Mathlib lemmas:

* `intervalIntegral.integral_mono_on`
* `intervalIntegral.integral_const`

plus `intervalIntegrable_const`, `max_le`, `le_max_left`, and `le_max_right`.

## Optional Moser-specialized wrapper

The generic lemma is probably enough, but a one-line Moser-specialized wrapper can make later code cleaner.  It should also compile if the generic lemma compiles.

```lean
/-- Moser-energy specialization of
`intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound`. -/
theorem integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {a b M p : ℝ}
    (hab : a ≤ b)
    (hYmax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ)
          (D.integral (fun x => (u s x) ^ p)))
        MeasureTheory.volume a b)
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        D.integral (fun x => (u s x) ^ p) ≤ M) :
    ∫ s in a..b,
      max (1 : ℝ) (D.integral (fun x => (u s x) ^ p)) ≤
        (b - a) * max (1 : ℝ) M :=
  intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
    (Y := fun s => D.integral (fun x => (u s x) ^ p))
    hab hYmax_int hY_le
```

This wrapper is optional; the generic lemma is the minimal useful patch.

## How it feeds the gradient extraction lemma

Suppose the already-added extraction lemma has hypotheses roughly:

```lean
hY1 : Y t1 ≤ M
hY2 : Y t2 ≤ M
hMaxInt : ∫ s in t1..t2, max 1 (Y s) ≤ R
```

or an explicit bound on that max integral.  The new lemma supplies the natural `R`:

```lean
R := (t2 - t1) * max 1 M
```

provided the first-crossing setup supplies

```lean
t1 ≤ t2
∀ s ∈ Set.Icc t1 t2, Y s ≤ M
IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) MeasureTheory.volume t1 t2
```

This is exactly the bounded-pre-crossing input one expects before proving the full first-crossing theorem.

## Do not overreach in this patch

Do not add any of the following yet:

```lean
IntegratedMoserDissipationDropBefore ... → IntegratedMoserFirstCrossingStep ...
```

or

```lean
IntegratedMoserFirstCrossingRegularity ... →
  IntervalIntegrable (fun s => max 1 (Y s)) MeasureTheory.volume a b
```

unless you separately verify the required max-preserves-interval-integrability API.  The lemma above avoids that uncertainty and should be the next smallest buildable step.

## Suggested `#print axioms`

After adding the generic lemma:

```lean
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
```

If you also add the Moser wrapper:

```lean
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
```

Expected profile: no `sorryAx`, no custom axioms.  The generic theorem should only depend on standard mathlib/Lean axioms already used by interval-integral order lemmas.
