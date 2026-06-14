import Mathlib
import ShenWork.Wiener.WeightedL1Convolution

/-!
# The cosine ↔ ℤ-bilateral adapter (algebraic core) — brick 6a

The committed PDE layer indexes real cosine coefficients by `ℕ`: a real `f` on `[0,1]`
expands as `f(x) = ∑_{k≥0} (c k) · cos(k π x)`. In the exponential basis `e^{i n π x}`
(`n ∈ ℤ`), `cos(k π x) = ½(e^{i k π x} + e^{-i k π x})`, so the ℤ-bilateral coefficient is
the EVEN, conjugate-symmetric (real) embedding
`a₀ = c₀`, `aₙ = a₋ₙ = ½ c_{|n|}` (`n ≠ 0`).

This file is pure algebra: the embedding `ofCosineCoeffs`, its reality/evenness, membership
in the weighted-ℓ¹ space, and the weighted-norm identity (the ½-factor doubled by the two
`±n` halves). No PDE, no basis-matching to the committed `cosineMode` (that is brick 6b).
-/

open scoped BigOperators

namespace ShenWork.Wiener

/-- The even ℤ-bilateral embedding of real cosine coefficients:
`a₀ = c₀` and `aₙ = a₋ₙ = ½ c_{|n|}` for `n ≠ 0`. -/
noncomputable def ofCosineCoeffs (c : ℕ → ℝ) : ℤ → ℂ :=
  fun n => if n = 0 then (c 0 : ℂ) else ((c n.natAbs : ℝ) / 2 : ℂ)

/-- The cosine-side weighted ℓ¹ norm `∑_{k≥0} (1+k)^r |c k|`. -/
noncomputable def cosineWNorm (r : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, (1 + (k : ℝ)) ^ r * |c k|

/-- Evenness: `ofCosineCoeffs c (-n) = ofCosineCoeffs c n`. -/
theorem ofCosineCoeffs_neg (c : ℕ → ℝ) (n : ℤ) :
    ofCosineCoeffs c (-n) = ofCosineCoeffs c n := by
  unfold ofCosineCoeffs
  by_cases h : n = 0
  · simp [h]
  · simp only [neg_eq_zero, h, if_false, Int.natAbs_neg]

/-- Reality: every coefficient has zero imaginary part. -/
theorem ofCosineCoeffs_im (c : ℕ → ℝ) (n : ℤ) :
    (ofCosineCoeffs c n).im = 0 := by
  unfold ofCosineCoeffs
  by_cases h : n = 0 <;> simp [h]

/-- Conjugate symmetry: `ofCosineCoeffs c (-n) = conj (ofCosineCoeffs c n)`
(both sides real, so this is evenness composed with `conj`-of-real). -/
theorem ofCosineCoeffs_conj_neg (c : ℕ → ℝ) (n : ℤ) :
    ofCosineCoeffs c (-n) = starRingEnd ℂ (ofCosineCoeffs c n) := by
  rw [ofCosineCoeffs_neg]
  apply Complex.ext <;> simp [ofCosineCoeffs_im, Complex.conj_re, Complex.conj_im]

/-- The norm of a coefficient: `if n = 0 then |c 0| else |c_{|n|}|/2`. -/
theorem norm_ofCosineCoeffs (c : ℕ → ℝ) (n : ℤ) :
    ‖ofCosineCoeffs c n‖ = if n = 0 then |c 0| else |c n.natAbs| / 2 := by
  unfold ofCosineCoeffs
  by_cases h : n = 0
  · simp [h, Complex.norm_real]
  · rw [if_neg h, if_neg h, norm_div, Complex.norm_real, Real.norm_eq_abs]
    norm_num

/-- The weighted ℓ¹ summand for `ofCosineCoeffs`. -/
private noncomputable def wterm (r : ℕ) (c : ℕ → ℝ) (n : ℤ) : ℝ :=
  wWeight r n * ‖ofCosineCoeffs c n‖

/-- The target (cosine-side) summand. -/
private def cterm (r : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ := (1 + (k : ℝ)) ^ r * |c k|

/-- At `0` the weighted summand is `|c 0|`. -/
private theorem wterm_zero (r : ℕ) (c : ℕ → ℝ) : wterm r c 0 = |c 0| := by
  unfold wterm wWeight
  rw [norm_ofCosineCoeffs]; simp

/-- On the positive half, the weighted summand is half the cosine summand at `k+1`. -/
private theorem wterm_succ (r : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    wterm r c ((m : ℤ) + 1) = cterm r c (m + 1) / 2 := by
  unfold wterm cterm wWeight
  rw [norm_ofCosineCoeffs (n := ((m : ℤ) + 1))]
  have hne : ((m : ℤ) + 1) ≠ 0 := by omega
  rw [if_neg hne]
  have hcast : |(((m : ℤ) + 1 : ℤ) : ℝ)| = 1 + (m : ℝ) := by
    push_cast; rw [abs_of_nonneg (by positivity)]; ring
  have hnat : ((m : ℤ) + 1).natAbs = m + 1 := by omega
  rw [hcast, hnat]; push_cast; ring

/-- On the negative half, the weighted summand is also half the cosine summand at `k+1`. -/
private theorem wterm_neg_succ (r : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    wterm r c (-((m : ℤ) + 1)) = cterm r c (m + 1) / 2 := by
  unfold wterm cterm wWeight
  rw [ofCosineCoeffs_neg, norm_ofCosineCoeffs (n := ((m : ℤ) + 1))]
  have hne : ((m : ℤ) + 1) ≠ 0 := by omega
  rw [if_neg hne]
  have hcast : |((-((m : ℤ) + 1) : ℤ) : ℝ)| = 1 + (m : ℝ) := by
    push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring
  have hnat : ((m : ℤ) + 1).natAbs = m + 1 := by omega
  rw [hcast, hnat]; push_cast; ring

/-- Summability of the cosine summand at shifted index `k+1`. -/
private theorem summable_cterm_succ {r : ℕ} {c : ℕ → ℝ}
    (hc : Summable (cterm r c)) : Summable (fun m : ℕ => cterm r c (m + 1)) :=
  (summable_nat_add_iff 1).2 hc

/-- Membership of the embedded coefficients in the weighted ℓ¹ space. -/
theorem memW_ofCosineCoeffs {r : ℕ} {c : ℕ → ℝ}
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)) :
    MemW r (ofCosineCoeffs c) := by
  have hc' : Summable (cterm r c) := hc
  have hpos : Summable (fun m : ℕ => wterm r c ((m : ℤ) + 1)) :=
    ((summable_cterm_succ hc').div_const 2).congr (fun m => (wterm_succ r c m).symm)
  have hneg : Summable (fun m : ℕ => wterm r c (-((m : ℤ) + 1))) :=
    ((summable_cterm_succ hc').div_const 2).congr (fun m => (wterm_neg_succ r c m).symm)
  exact (hpos.of_add_one_of_neg_add_one hneg)

/-- **The adapter norm identity**: the weighted ℓ¹ norm of the embedded coefficients equals
the cosine-side weighted ℓ¹ norm `∑_{k≥0} (1+k)^r |c k|`. The ½ in each coefficient is
doubled by the two `±n` halves of the ℤ-split, recovering the full cosine summand. -/
theorem wNorm_ofCosineCoeffs {r : ℕ} {c : ℕ → ℝ}
    (hc : Summable (fun k : ℕ => (1 + (k : ℝ)) ^ r * |c k|)) :
    wNorm r (ofCosineCoeffs c) = ∑' k : ℕ, (1 + (k : ℝ)) ^ r * |c k| := by
  have hc' : Summable (cterm r c) := hc
  have hcs := summable_cterm_succ hc'
  have hpos : Summable (fun m : ℕ => wterm r c ((m : ℤ) + 1)) :=
    (hcs.div_const 2).congr (fun m => (wterm_succ r c m).symm)
  have hneg : Summable (fun m : ℕ => wterm r c (-((m : ℤ) + 1))) :=
    (hcs.div_const 2).congr (fun m => (wterm_neg_succ r c m).symm)
  have hsplit : (∑' n : ℤ, wterm r c n)
      = (∑' m : ℕ, wterm r c ((m : ℤ) + 1)) + wterm r c 0
        + ∑' m : ℕ, wterm r c (-((m : ℤ) + 1)) :=
    tsum_of_add_one_of_neg_add_one hpos hneg
  have hposval : (∑' m : ℕ, wterm r c ((m : ℤ) + 1))
      = ∑' m : ℕ, cterm r c (m + 1) / 2 :=
    tsum_congr (fun m => wterm_succ r c m)
  have hnegval : (∑' m : ℕ, wterm r c (-((m : ℤ) + 1)))
      = ∑' m : ℕ, cterm r c (m + 1) / 2 :=
    tsum_congr (fun m => wterm_neg_succ r c m)
  have htarget : (∑' k : ℕ, cterm r c k)
      = cterm r c 0 + ∑' m : ℕ, cterm r c (m + 1) := hc'.tsum_eq_zero_add
  have hwNorm : wNorm r (ofCosineCoeffs c) = ∑' n : ℤ, wterm r c n := rfl
  rw [hwNorm, hsplit, hposval, hnegval, wterm_zero]
  rw [show (∑' m : ℕ, cterm r c (m + 1) / 2) = (∑' m : ℕ, cterm r c (m + 1)) / 2 from
    tsum_div_const]
  have hc0 : cterm r c 0 = |c 0| := by unfold cterm; simp
  rw [show (∑' k : ℕ, (1 + (k : ℝ)) ^ r * |c k|) = ∑' k : ℕ, cterm r c k from rfl, htarget, hc0]
  ring

end ShenWork.Wiener
