import Mathlib
import ShenWork.Wiener.EWA.CoeffBridge

/-!
# EWA parity foundations — committed atoms for the Phase C parity/coefficient route

This file collects small, certainly-correct foundational lemmas describing how the
cosine-coefficient extractor `ewaCosCoeffAt` interacts with the even ℤ-bilateral
embedding `ofCosineCoeffs`.  Everything here is pure algebra over the committed
definitions; no PDE, no realization hypotheses beyond a coefficient identity on the
slice.  These are the "parity atoms" the endgame coefficient-identity route reuses.

## Contents
1. **Coefficient recovery** (`ewaCosCoeffAt_of_slice_eq`, and the pure-embedding
   core `re_ofCosineCoeffs_*`): if the EWA slice coefficients are exactly
   `ofCosineCoeffs c` (real `c`), then `ewaCosCoeffAt F τ k = c k`.
2. **Summability transfer** (`summable_abs_of_slice_eq`): the EWA element's intrinsic
   ℓ¹ summability (`F.mem`, i.e. `GMemW 0`) plus the slice identity gives
   `Summable (fun k : ℕ => |c k|)` — a non-circular source for `summable_cos`.
3. **Reality / conjugate helpers** (`re_ofCosineCoeffs`, `conj_ofCosineCoeffs`,
   `re_ofCosineCoeffs_add_neg`): small parity facts on `ofCosineCoeffs`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### 1. Pure-embedding parity / reality cores. -/

/-- `(ofCosineCoeffs c n)` is real: its real part is its own value as a real number.
At `0` it is `c 0`, off `0` it is `c_{|n|}/2`. -/
theorem re_ofCosineCoeffs (c : ℕ → ℝ) (n : ℤ) :
    (ofCosineCoeffs c n).re = if n = 0 then c 0 else c n.natAbs / 2 := by
  unfold ofCosineCoeffs
  by_cases h : n = 0
  · simp [h]
  · simp [h, Complex.ofReal_re]

/-- The `k = 0` coefficient recovery (pure embedding): `(ofCosineCoeffs c 0).re = c 0`. -/
theorem re_ofCosineCoeffs_zero (c : ℕ → ℝ) :
    (ofCosineCoeffs c 0).re = c 0 := by
  rw [re_ofCosineCoeffs]; simp

/-- The `k ≥ 1` coefficient recovery (pure embedding): the two even halves at `±k`
add to the full real coefficient `c k`. -/
theorem re_ofCosineCoeffs_add_neg (c : ℕ → ℝ) (k : ℕ) (hk : k ≠ 0) :
    (ofCosineCoeffs c (k : ℤ) + ofCosineCoeffs c (-(k : ℤ))).re = c k := by
  rw [ofCosineCoeffs_neg, Complex.add_re]
  rw [re_ofCosineCoeffs, if_neg (by exact_mod_cast hk)]
  rw [Int.natAbs_natCast]
  ring

/-- Conjugate symmetry of the embedding restated for `re`: `conj` fixes the (real)
coefficients, so `re (conj a_n) = re a_n`. -/
theorem conj_ofCosineCoeffs (c : ℕ → ℝ) (n : ℤ) :
    starRingEnd ℂ (ofCosineCoeffs c n) = ofCosineCoeffs c n := by
  apply Complex.ext <;>
    simp [Complex.conj_re, Complex.conj_im, ofCosineCoeffs_im]

/-! ### 2. Coefficient recovery for `ewaCosCoeffAt` under a slice identity. -/

/-- **Coefficient recovery from the even embedding (the key atom).**
If the EWA slice coefficients at time `τ` are exactly the even embedding
`ofCosineCoeffs c` of a real family `c`, then the `±`-mode extractor returns `c k`. -/
theorem ewaCosCoeffAt_of_slice_eq {F : EWA T 0} {c : ℕ → ℝ} {τ : TimeDom T}
    (hslice : (sliceWA τ F).toFun = ofCosineCoeffs c) (k : ℕ) :
    ewaCosCoeffAt F τ k = c k := by
  unfold ewaCosCoeffAt
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, hslice, re_ofCosineCoeffs_zero]
  · rw [if_neg hk, hslice, re_ofCosineCoeffs_add_neg c k hk]

/-! ### 3. Summability transfer (non-circular `summable_cos` source). -/

/-- `gWeight 0 n = 1`, so the `r = 0` membership of an EWA element is exactly the
plain summability of the coefficient norms. -/
theorem summable_norm_toFun_of_mem (F : EWA T 0) :
    Summable (fun n : ℤ => ‖F.toFun n‖) := by
  have h := F.mem
  rw [GMemW] at h
  refine h.congr (fun n => ?_)
  simp [gWeight]

/-- **Summability transfer.**  From the EWA element's intrinsic ℓ¹ summability
(`F.mem`, i.e. `GMemW 0 F.toFun`) and the slice identity
`(sliceWA τ F).toFun = ofCosineCoeffs c`, the cosine family `c` is absolutely
summable: `Summable (fun k : ℕ => |c k|)`.  This decouples the circular
`summable_cos` field of `EWARealizesOn` from the realization.

The bound is `|c k| ≤ 2 · ‖F.toFun k‖` at every `τ`: indeed
`‖ofCosineCoeffs c k‖ = ‖(F.toFun k) τ‖ ≤ ‖F.toFun k‖`, and `‖ofCosineCoeffs c k‖`
is `|c 0|` (at `0`) or `|c k|/2` (off `0`), in both cases `≥ |c k|/2`. -/
theorem summable_abs_of_slice_eq {F : EWA T 0} {c : ℕ → ℝ} {τ : TimeDom T}
    (hslice : (sliceWA τ F).toFun = ofCosineCoeffs c) :
    Summable (fun k : ℕ => |c k|) := by
  -- The intrinsic ℤ-summability, restricted to nonnegative indices `(k : ℤ)`.
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ)) := by
    intro p q h; simpa using h
  have hℕ : Summable (fun k : ℕ => ‖F.toFun (k : ℤ)‖) :=
    (summable_norm_toFun_of_mem F).comp_injective hinj
  have hℕ2 : Summable (fun k : ℕ => 2 * ‖F.toFun (k : ℤ)‖) := hℕ.mul_left 2
  -- Termwise: `|c k| ≤ 2 · ‖F.toFun (k : ℤ)‖`.
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hℕ2
  -- `‖ofCosineCoeffs c k‖ = ‖(sliceWA τ F).toFun k‖ = ‖(F.toFun k) τ‖ ≤ ‖F.toFun k‖`.
  have hcoeff : ofCosineCoeffs c (k : ℤ) = (F.toFun (k : ℤ)) τ := by
    have := congrFun hslice (k : ℤ)
    rw [coeff_sliceWA] at this
    exact this.symm
  have hnorm_le : ‖ofCosineCoeffs c (k : ℤ)‖ ≤ ‖F.toFun (k : ℤ)‖ := by
    rw [hcoeff]; exact ContinuousMap.norm_coe_le_norm (F.toFun (k : ℤ)) τ
  -- `|c k| / 2 ≤ ‖ofCosineCoeffs c k‖` (equality off `0`, and `≤ |c 0|` at `0`).
  have hhalf : |c k| / 2 ≤ ‖ofCosineCoeffs c (k : ℤ)‖ := by
    rw [norm_ofCosineCoeffs]
    by_cases hk : (k : ℤ) = 0
    · have hk0 : k = 0 := by exact_mod_cast hk
      subst hk0
      simp only [if_pos hk]
      -- `|c 0| / 2 ≤ |c 0|`
      have : (0 : ℝ) ≤ |c 0| := abs_nonneg _
      linarith
    · rw [if_neg hk, Int.natAbs_natCast]
  -- Chain: `|c k| ≤ 2‖ofCosineCoeffs c k‖ ≤ 2‖F.toFun k‖`.
  have h1 : |c k| ≤ 2 * ‖ofCosineCoeffs c (k : ℤ)‖ := by linarith
  calc |c k| ≤ 2 * ‖ofCosineCoeffs c (k : ℤ)‖ := h1
    _ ≤ 2 * ‖F.toFun (k : ℤ)‖ := by
        exact mul_le_mul_of_nonneg_left hnorm_le (by norm_num)

end ShenWork.EWA
