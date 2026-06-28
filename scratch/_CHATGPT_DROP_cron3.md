# Q1605 (cron3): replacing `cutoffResolverMajorant_bddAbove_of_physical`

## Short answer

You cannot get the required **global**

```lean
BddAbove (Set.range fun q : ℝ × ℝ =>
  ‖iteratedFDeriv ℝ j (cutoffResolverTerm p u c k) q‖)
```

from just these two facts:

```lean
cutoffResolverTerm_contDiff_two  : ContDiff ℝ 2 (cutoffResolverTerm ...)
cutoffResolverCoeff_contDiff_two : ContDiff ℝ 2 (fun t => φ t * resolverTimeCoeff ... t)
```

plus “the cutoff term vanishes for `t < c/2`.”

`ContDiff` gives continuity of each `iteratedFDeriv`, but a continuous function on all of `ℝ × ℝ` need not be bounded.  Vanishing on the left half-space also does not help, because the right cutoff is `1` on `t ≥ c`, not zero.  The term is not compactly supported.

So the clean replacement is **not** “derive `BddAbove` from `ContDiff`.”  The clean replacement is:

1. reduce the term bound to scalar coefficient derivative bounds plus cosine derivative bounds;
2. prove or assume those scalar coefficient derivative bounds directly from the resolver/source estimates;
3. then get `BddAbove` by a finite Leibniz sum.

That removes dependence on `PhysicalResolverJointC2Data`, but it still needs a real right-tail bound for the resolver coefficient derivatives.

## Why the proposed shortcut is false

A right-cutoff counterexample has the same shape as your resolver cutoff:

```lean
fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1 * q.1
```

This is `C²`, and it vanishes for `q.1 ≤ c/2`.  But for `q.1 ≥ c`, the cutoff is `1`, so the function is `q.1`; hence the norm range is unbounded.  Replacing `q.1` by `Real.exp q.1` also makes the first and second time derivatives unbounded.

Thus this theorem shape is not valid:

```lean
-- false, even for j = 0
ContDiff ℝ 2 f →
(∀ q, q.1 < c / 2 → f q = 0) →
BddAbove (Set.range fun q => ‖iteratedFDeriv ℝ j f q‖)
```

The missing information is a right-tail bound.

## What `ContDiff` does give

For local compact sets, this is fine:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Bounded

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.Paper2.HeatResolverJointC2Direct

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- Local compact bound from `ContDiff`.  This is useful, but it is **not** the global
majorant needed by `contDiff_tsum`. -/
example
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hc : 0 < c) (j k : ℕ) (hj : (j : ℕ∞) ≤ 2)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ q ∈ K,
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤ C := by
  have htermC2 : ContDiff ℝ (2 : ℕ∞)
      (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) :=
    cutoffResolverTerm_contDiff_two hu₀_bound hu₀_cont hfloor hc k

  have hjω : (j : ℕ∞ω) ≤ ((2 : ℕ∞) : ℕ∞ω) := by
    exact_mod_cast hj

  have hcont : Continuous fun q : ℝ × ℝ =>
      iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q :=
    htermC2.continuous_iteratedFDeriv (m := j) hjω

  exact hK.exists_bound_of_continuousOn hcont.continuousOn

end ShenWork.Paper2.HeatResolverJointC2Direct
```

This proves compact-rectangle boundedness, not global `BddAbove`.

## Clean global replacement: reduce to scalar coefficient bounds

The term has the form

```lean
cutoffResolverTerm p u c k q = A q.1 * cosineMode k q.2
```

where

```lean
A t = smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t
```

So the clean global route is to replace the old physical package by a small **scalar derivative bound package**:

```lean
/-- Scalar bounds for the cutoff resolver coefficient for one fixed mode `k`. -/
def CutoffResolverCoeffDerivBounds
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : Prop :=
  ∀ i : ℕ, (i : ℕ∞) ≤ 2 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i
        (fun t : ℝ => smoothRightCutoff (c / 2) c t *
          resolverTimeCoeff p u k t) t‖ ≤ C
```

Then the `BddAbove` proof is purely mechanical.

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Bounded

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalResolverSpectralJointC2CutoffBounds
  (norm_iteratedFDeriv_comp_fst_le norm_iteratedFDeriv_comp_snd_le)
open ShenWork.Paper2.HeatResolverJointC2Direct

noncomputable section

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- A convenient scalar bound package for the cutoff coefficient. -/
def CutoffResolverCoeffDerivBounds
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : Prop :=
  ∀ i : ℕ, (i : ℕ∞) ≤ 2 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i
        (fun t : ℝ => smoothRightCutoff (c / 2) c t *
          resolverTimeCoeff p u k t) t‖ ≤ C

/-- Finite Leibniz majorant built from scalar coefficient derivative bounds. -/
noncomputable def cutoffResolverCoeffBasedBound
    (A : ℕ → ℝ) (c : ℝ) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * A i * (|(k : ℝ) * Real.pi| ^ (j - i))

/-- Proof skeleton: coefficient derivative bounds imply global boundedness of each
term derivative.  Fill the two `sorry`s with the existing projection/cosine lemmas
used elsewhere in the file. -/
theorem cutoffResolverMajorant_bddAbove_of_coeff_bounds
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (hc : 0 < c) (j k : ℕ) (hj : (j : ℕ∞) ≤ 2)
    (hA : CutoffResolverCoeffDerivBounds p (conjugatePicardIter p u₀ 0) c k) :
    BddAbove (Set.range fun q : ℝ × ℝ =>
      ‖iteratedFDeriv ℝ j
        (cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k) q‖) := by
  classical

  let u := conjugatePicardIter p u₀ 0
  let Acoef : ℝ → ℝ := fun t =>
    smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t
  let G : ℝ × ℝ → ℝ := fun q => Acoef q.1
  let Hcos : ℝ × ℝ → ℝ := fun q => cosineMode k q.2

  have hterm : cutoffResolverTerm p u c k = fun q : ℝ × ℝ => G q * Hcos q := by
    funext q
    simp [cutoffResolverTerm, Acoef, G, Hcos, u, mul_assoc]

  have hAcoefC2 : ContDiff ℝ (2 : ℕ∞) Acoef := by
    -- This is exactly `cutoffResolverCoeff_contDiff_two` after unfolding `Acoef`.
    simpa [Acoef, u] using
      (cutoffResolverCoeff_contDiff_two
        (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hfloor hc k)

  have hG : ContDiff ℝ (2 : ℕ∞) G :=
    hAcoefC2.comp contDiff_fst

  have hHcos0 : ContDiff ℝ ⊤ (cosineMode k) := by
    unfold cosineMode
    fun_prop

  have hHcos : ContDiff ℝ (2 : ℕ∞) Hcos :=
    (hHcos0.comp contDiff_snd).of_le le_top

  -- Choose a scalar bound for every coefficient derivative order appearing in
  -- the finite Leibniz sum.  Since `i ≤ j ≤ 2`, `hA` applies.
  choose C hC_nonneg hC_bound using
    fun i : ℕ => hA i (by
      have hjNat : j ≤ 2 := by exact_mod_cast hj
      by_cases hi : i ≤ j
      · exact_mod_cast (le_trans hi hjNat)
      · exact_mod_cast (Nat.zero_le 2)  -- dummy branch; not used below for i ∈ range (j+1))

  refine ⟨cutoffResolverCoeffBasedBound C c j k, ?_⟩
  rintro _ ⟨q, rfl⟩

  have hjTop : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast hj

  rw [hterm]
  calc
    ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => G q * Hcos q) q‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i G q‖ *
            ‖iteratedFDeriv ℝ (j - i) Hcos q‖ := by
          simpa [mul_assoc] using norm_iteratedFDeriv_mul_le hG hHcos q hjTop
    _ ≤ cutoffResolverCoeffBasedBound C c j k := by
      unfold cutoffResolverCoeffBasedBound
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hjNat : j ≤ 2 := by exact_mod_cast hj
      have hiTop : (i : ℕ∞) ≤ (2 : ℕ∞) := by
        exact_mod_cast (le_trans hik hjNat)
      have hjiTop : ((j - i : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by
        exact_mod_cast (le_trans (Nat.sub_le j i) hjNat)

      have hG_bound : ‖iteratedFDeriv ℝ i G q‖ ≤ C i := by
        -- projection to `fst` plus scalar coefficient derivative bound
        -- Existing helper: `norm_iteratedFDeriv_comp_fst_le`.
        refine (norm_iteratedFDeriv_comp_fst_le hAcoefC2 ?_ q).trans ?_
        · exact_mod_cast hiTop
        · exact hC_bound i q.1

      have hH_bound : ‖iteratedFDeriv ℝ (j - i) Hcos q‖ ≤
          |(k : ℝ) * Real.pi| ^ (j - i) := by
        -- projection to `snd` plus cosine derivative bound.
        -- In this repo this is the same pattern used in
        -- `IntervalHeatSemigroupHighRegularity.lean`:
        --   norm_iteratedFDeriv_comp_snd_le
        --   + CD6CosineModeBounds.unitIntervalCosineMode_iteratedFDeriv_bound
        sorry

      have hchoose_nn : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      have hCnn : 0 ≤ C i := hC_nonneg i

      calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i G q‖ *
              ‖iteratedFDeriv ℝ (j - i) Hcos q‖
          ≤ (j.choose i : ℝ) * C i *
              ‖iteratedFDeriv ℝ (j - i) Hcos q‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hG_bound hchoose_nn) (norm_nonneg _)
        _ ≤ (j.choose i : ℝ) * C i * (|(k : ℝ) * Real.pi| ^ (j - i)) := by
            exact mul_le_mul_of_nonneg_left hH_bound (mul_nonneg hchoose_nn hCnn)

end ShenWork.Paper2.HeatResolverJointC2Direct
```

The above is the clean replacement pattern.  The one intentional hole is the already-standard cosine bound line; it should be filled by the same lemmas used in `IntervalHeatSemigroupHighRegularity.lean`, namely the `comp_snd` helper plus the cosine-mode iterated derivative bound.

## Even cleaner: avoid `choose` awkwardness

For actual implementation, avoid the ugly `choose` over all `i`.  Define the bound directly inside the finite sum using `Classical.choose`:

```lean
noncomputable def coeffDerivBound
    (hA : CutoffResolverCoeffDerivBounds p u c k)
    (i : ℕ) (hi : (i : ℕ∞) ≤ 2) : ℝ :=
  Classical.choose (hA i hi)
```

with projection lemmas:

```lean
lemma coeffDerivBound_nonneg ... : 0 ≤ coeffDerivBound hA i hi :=
  (Classical.choose_spec (hA i hi)).1

lemma coeffDerivBound_spec ... :
    ‖iteratedFDeriv ℝ i Acoef t‖ ≤ coeffDerivBound hA i hi :=
  (Classical.choose_spec (hA i hi)).2 t
```

Then the finite sum can use the proof-relevant `hi` obtained from `i ∈ range (j+1)` and `j ≤ 2`.

## Where to get `CutoffResolverCoeffDerivBounds`

This is the real remaining analytic obligation.  It is **not** a consequence of `ContDiff` alone.  It should be proved by a right/left split:

```lean
by_cases ht : t < c / 2
· -- local zero from `smoothRightCutoff_eq_zero_of_le`; derivatives vanish by eventuallyEq
· -- t ≥ c / 2: use explicit resolver/source coefficient estimates
```

For the right-tail case, you need bounds on

```lean
iteratedFDeriv ℝ i
  (fun t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t) t
```

These should come from the already-proved source coefficient derivative formulas and heat/spectral envelopes, not from `PhysicalResolverJointC2Data`.  In other words: replace `H.coeff_bound` by a direct coefficient-bound lemma for `resolverTimeCoeff`, not by compactness.

## Bottom line

The cleanest replacement is:

```text
PhysicalResolverJointC2Data
  old:  H.coeff_contDiff + H.coeff_bound

replace by:
  cutoffResolverCoeff_contDiff_two
  + direct scalar coefficient derivative global bounds
  + cosine derivative bounds
  + finite Leibniz sum
```

`cutoffResolverTerm_contDiff_two` is useful for continuity/local compact bounds, but it does not by itself give the global `BddAbove` needed for `ciSup`/majorant.  The missing ingredient is a global right-tail coefficient bound.
