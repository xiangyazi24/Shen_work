import ShenWork.Wiener.EWA.CoeffBridge

/-!
# EWA brick — the ℓ¹ value envelope of an EWA source element

The committed `DuhamelSourceTimeC1On` package requires an `envelope : ℕ → ℝ` that
is summable and dominates the (absolute values of the) cosine-coefficient family
of the source, uniformly in time.  This file supplies that envelope DATA for an
EWA source element `F : EWA T 0`, **unconditionally** — intrinsic to the EWA
element, requiring no realization hypothesis.

The envelope is the `±`-pair of `CT T` sup-norms
`sourceEnvelope F k = ‖F.toFun k‖ + ‖F.toFun (-k)‖`, and the three obligations are:

* `sourceEnvelope_summable` — the envelope is summable.  The `CT T`-coefficient
  family `n ↦ ‖F.toFun n‖` is `ℤ`-summable (`F.mem`, i.e. `GMemW 0`), and the
  `ℕ`-indexed `±`-pair of a `ℤ`-summable family is summable
  (`Summable.nat_add_neg`).
* `ewaCosCoeffAt_abs_le_envelope` — the `±`-mode cosine extractor at any time
  `τ` is dominated by the envelope, via `Complex.abs_re_le_norm` and the `CT T`
  sup-norm bound `ContinuousMap.norm_coe_le_norm`.
* `sourceEnvelope_tsum_le_norm` — the envelope's `ℓ¹` mass is `≤ 2‖F‖`.  The
  `ℕ`-indexed `±`-cover of `ℤ` double-counts only `n = 0`
  (`tsum_nat_add_neg`: `∑'_ℕ (f n + f (-n)) = (∑'_ℤ f) + f 0`), so the total is
  `‖F‖ + ‖F.toFun 0‖ ≤ 2‖F‖`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- The ℓ¹ value envelope of an EWA source element: the `±`-pair of `CT T`
sup-norms of its time-coefficient family. -/
noncomputable def sourceEnvelope (F : EWA T 0) (k : ℕ) : ℝ :=
  ‖F.toFun (k : ℤ)‖ + ‖F.toFun (-(k : ℤ))‖

/-- `‖F‖ = ∑'_{n:ℤ} ‖F.toFun n‖` since `gWeight 0 n = 1`. -/
theorem norm_eq_tsum_coeff (F : EWA T 0) : ‖F‖ = ∑' n : ℤ, ‖F.toFun n‖ := by
  rw [GWA.norm_def, GWA.gNorm]
  refine tsum_congr (fun n => ?_)
  rw [GWA.gWeight, pow_zero, one_mul]

/-- The `CT T`-coefficient family of an EWA element is `ℤ`-summable. -/
theorem summable_coeff_norm (F : EWA T 0) : Summable (fun n : ℤ => ‖F.toFun n‖) := by
  have hmem := F.mem
  rw [GMemW] at hmem
  refine hmem.congr (fun n => ?_)
  rw [GWA.gWeight, pow_zero, one_mul]

/-- **The envelope is summable.**  The `ℕ`-indexed `±`-pair of the `ℤ`-summable
coefficient-norm family is summable (`Summable.nat_add_neg`). -/
theorem sourceEnvelope_summable (F : EWA T 0) : Summable (sourceEnvelope F) := by
  have h := (summable_coeff_norm F).nat_add_neg
  simpa only [sourceEnvelope] using h

/-- **The pointwise envelope bound.**  At any time `τ`, the `±`-mode cosine
extractor is dominated by the envelope. -/
theorem ewaCosCoeffAt_abs_le_envelope (F : EWA T 0) (τ : TimeDom T) (k : ℕ) :
    |ewaCosCoeffAt F τ k| ≤ sourceEnvelope F k := by
  unfold ewaCosCoeffAt sourceEnvelope
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, coeff_sliceWA]
    have h1 : |((F.toFun 0) τ).re| ≤ ‖(F.toFun (0 : ℤ)) τ‖ := by
      simpa using Complex.abs_re_le_norm ((F.toFun (0 : ℤ)) τ)
    have h2 : ‖(F.toFun (0 : ℤ)) τ‖ ≤ ‖F.toFun (0 : ℤ)‖ :=
      ContinuousMap.norm_coe_le_norm (F.toFun (0 : ℤ)) τ
    have h3 : (0 : ℝ) ≤ ‖F.toFun (-(0 : ℤ))‖ := norm_nonneg _
    have hcast : ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_cast
    rw [hcast]
    calc |((F.toFun 0) τ).re| ≤ ‖F.toFun (0 : ℤ)‖ := h1.trans h2
      _ ≤ ‖F.toFun (0 : ℤ)‖ + ‖F.toFun (-(0 : ℤ))‖ := by linarith
  · rw [if_neg hk, coeff_sliceWA, coeff_sliceWA]
    have hadd : ((F.toFun (k : ℤ)) τ + (F.toFun (-(k : ℤ))) τ).re
        = ((F.toFun (k : ℤ)) τ).re + ((F.toFun (-(k : ℤ))) τ).re := by
      rw [Complex.add_re]
    rw [hadd]
    have hbound : |((F.toFun (k : ℤ)) τ).re| + |((F.toFun (-(k : ℤ))) τ).re|
        ≤ ‖F.toFun (k : ℤ)‖ + ‖F.toFun (-(k : ℤ))‖ := by
      have hp : |((F.toFun (k : ℤ)) τ).re| ≤ ‖F.toFun (k : ℤ)‖ :=
        (Complex.abs_re_le_norm _).trans (ContinuousMap.norm_coe_le_norm (F.toFun (k : ℤ)) τ)
      have hn : |((F.toFun (-(k : ℤ))) τ).re| ≤ ‖F.toFun (-(k : ℤ))‖ :=
        (Complex.abs_re_le_norm _).trans
          (ContinuousMap.norm_coe_le_norm (F.toFun (-(k : ℤ))) τ)
      linarith
    exact (abs_add_le _ _).trans hbound

/-- **The envelope's ℓ¹ mass is `≤ 2‖F‖`.**  The `ℕ`-indexed `±`-cover of `ℤ`
double-counts only `n = 0` (`tsum_nat_add_neg` gives `‖F‖ + ‖F.toFun 0‖`), and
`‖F.toFun 0‖ ≤ ‖F‖`. -/
theorem sourceEnvelope_tsum_le_norm (F : EWA T 0) :
    ∑' k, sourceEnvelope F k ≤ 2 * ‖F‖ := by
  have hsum := summable_coeff_norm F
  have heq : ∑' k : ℕ, sourceEnvelope F k
      = (∑' n : ℤ, ‖F.toFun n‖) + ‖F.toFun (0 : ℤ)‖ := by
    have h := tsum_nat_add_neg (f := fun n : ℤ => ‖F.toFun n‖) hsum
    simpa only [sourceEnvelope] using h
  rw [heq, norm_eq_tsum_coeff]
  have h0 : ‖F.toFun (0 : ℤ)‖ ≤ ∑' n : ℤ, ‖F.toFun n‖ :=
    hsum.le_tsum 0 (fun n _ => norm_nonneg _)
  linarith

end ShenWork.EWA

#print axioms ShenWork.EWA.sourceEnvelope_summable
#print axioms ShenWork.EWA.ewaCosCoeffAt_abs_le_envelope
#print axioms ShenWork.EWA.sourceEnvelope_tsum_le_norm
