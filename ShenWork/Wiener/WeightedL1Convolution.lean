import Mathlib

/-!
# The weighted ℓ¹ Wiener algebra on bilateral coefficients ℤ → ℂ

Pure sequence algebra (no PDE, unconditional). The exponential basis
`e_n(x) = e^{i n π x}` makes products ordinary convolution, so the multiplication
core is the ℤ-indexed weighted-ℓ¹ convolution algebra with submultiplicative
weight `(1 + |n|)^r`.

This is brick 1: the weight, membership predicate, convolution, the
submultiplicative-weight inequality `wWeight_submul`, and the Banach-algebra
product-norm bound `wNorm_conv_le`.
-/

open scoped BigOperators

namespace ShenWork.Wiener

/-- The submultiplicative weight `(1 + |n|)^r` on ℤ. -/
def wWeight (r : ℕ) (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ r

/-- Membership in the weighted ℓ¹ space: `(1+|n|)^r ‖a n‖` is summable. -/
def MemW (r : ℕ) (a : ℤ → ℂ) : Prop := Summable (fun n => wWeight r n * ‖a n‖)

/-- The weighted ℓ¹ norm. -/
noncomputable def wNorm (r : ℕ) (a : ℤ → ℂ) : ℝ := ∑' n, wWeight r n * ‖a n‖

/-- Bilateral convolution `(a ⋆ b)_n = ∑_m a_m b_{n-m}`. -/
noncomputable def wConv (a b : ℤ → ℂ) : ℤ → ℂ := fun n => ∑' m, a m * b (n - m)

/-- The weight is nonnegative. -/
theorem wWeight_nonneg (r : ℕ) (n : ℤ) : 0 ≤ wWeight r n := by
  unfold wWeight; positivity

/-- The weighted summand `(1+|n|)^r ‖a n‖` is nonnegative. -/
theorem weightedNorm_nonneg (r : ℕ) (a : ℤ → ℂ) (n : ℤ) :
    0 ≤ wWeight r n * ‖a n‖ := by
  have := wWeight_nonneg r n; positivity

/-- **The submultiplicative weight (the algebraic crux).**
`(1 + |m+n|)^r ≤ (1 + |m|)^r (1 + |n|)^r`. -/
theorem wWeight_submul (r : ℕ) (m n : ℤ) :
    wWeight r (m + n) ≤ wWeight r m * wWeight r n := by
  unfold wWeight
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ r
  push_cast
  have htri : |(m : ℝ) + n| ≤ |(m : ℝ)| + |(n : ℝ)| := abs_add_le _ _
  have h1 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
  nlinarith [htri, h1, h2]

section Conv

variable {r : ℕ} {a b : ℤ → ℂ}

/-- Abbreviation for the nonnegative weighted-norm summand of `a`. -/
private noncomputable def wabs (r : ℕ) (a : ℤ → ℂ) (m : ℤ) : ℝ := wWeight r m * ‖a m‖

private theorem wabs_nonneg (r : ℕ) (a : ℤ → ℂ) (m : ℤ) : 0 ≤ wabs r a m :=
  weightedNorm_nonneg r a m

private theorem memW_iff_wabs (r : ℕ) (a : ℤ → ℂ) : MemW r a ↔ Summable (wabs r a) :=
  Iff.rfl

/-- The shear `(m, n) ↦ (m, n - m)` on `ℤ × ℤ`. -/
private noncomputable def shear : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.refl ℤ).prodShear (fun m => Equiv.subRight m)

private theorem shear_apply (m n : ℤ) : shear (m, n) = (m, n - m) := by
  simp [shear, Equiv.prodShear, Equiv.subRight]

/-- The product majorant `(m, k) ↦ wabs a m * wabs b k` is summable on `ℤ × ℤ`. -/
private theorem summable_prod_majorant (ha : MemW r a) (hb : MemW r b) :
    Summable (fun p : ℤ × ℤ => wabs r a p.1 * wabs r b p.2) :=
  Summable.mul_of_nonneg ha hb (fun m => wabs_nonneg r a m) (fun k => wabs_nonneg r b k)

/-- After the shear, the majorant becomes `(m, n) ↦ wabs a m * (wWeight r (n-m) * ‖b (n-m)‖)`,
which is summable. -/
private theorem summable_sheared (ha : MemW r a) (hb : MemW r b) :
    Summable (fun p : ℤ × ℤ => wabs r a p.1 * (wWeight r (p.2 - p.1) * ‖b (p.2 - p.1)‖)) := by
  have hsum := summable_prod_majorant ha hb
  have := (shear.summable_iff
      (f := fun p : ℤ × ℤ => wabs r a p.1 * wabs r b p.2)).2 hsum
  refine this.congr ?_
  rintro ⟨m, k⟩
  rw [Function.comp_apply, shear_apply]
  rfl

/-- The sheared majorant, coordinates swapped: `(n,m) ↦ wabs a m * (wWeight (n-m) * ‖b (n-m)‖)`. -/
private theorem summable_sheared_swap (ha : MemW r a) (hb : MemW r b) :
    Summable (fun p : ℤ × ℤ => wabs r a p.2 * (wWeight r (p.1 - p.2) * ‖b (p.1 - p.2)‖)) :=
  (Equiv.prodComm ℤ ℤ).summable_iff.2 (summable_sheared ha hb)

/-- The inner majorant `m ↦ wabs a m * (wWeight (n-m) * ‖b (n-m)‖)` is summable for each `n`. -/
private theorem summable_inner (ha : MemW r a) (hb : MemW r b) (n : ℤ) :
    Summable (fun m => wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖)) := by
  have h := (summable_sheared_swap ha hb).prod_factor n
  simpa using h

/-- **Per-`n` convolution norm summability**: `∑' m, ‖a m * b (n - m)‖` is summable. -/
theorem summable_conv_norm (ha : MemW r a) (hb : MemW r b) (n : ℤ) :
    Summable (fun m => ‖a m * b (n - m)‖) := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_ (summable_inner ha hb n)
  intro m
  rw [norm_mul]
  have hwm : (1 : ℝ) ≤ wWeight r m := by
    unfold wWeight; exact one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hwk : (1 : ℝ) ≤ wWeight r (n - m) := by
    unfold wWeight; exact one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hAm : ‖a m‖ ≤ wabs r a m := by
    have : ‖a m‖ = 1 * ‖a m‖ := (one_mul _).symm
    rw [this]; simp only [wabs]; gcongr
  have hBm : ‖b (n - m)‖ ≤ wWeight r (n - m) * ‖b (n - m)‖ := by
    nlinarith [norm_nonneg (b (n - m)), wWeight_nonneg r (n - m)]
  have h2 : (0 : ℝ) ≤ ‖b (n - m)‖ := norm_nonneg _
  exact mul_le_mul hAm hBm h2 (wabs_nonneg r a m)

/-- **Per-`n` convolution summability** (ℂ-valued): `∑' m, a m * b (n - m)` is summable. -/
theorem summable_conv_term (ha : MemW r a) (hb : MemW r b) (n : ℤ) :
    Summable (fun m => a m * b (n - m)) :=
  Summable.of_norm (summable_conv_norm ha hb n)

/-- The outer sum `n ↦ ∑'_m wabs a m * (wWeight (n-m) * ‖b (n-m)‖)` is summable. -/
private theorem summable_outer (ha : MemW r a) (hb : MemW r b) :
    Summable (fun n : ℤ => ∑' m : ℤ, wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖)) := by
  have hsheared := summable_sheared ha hb
  have hswap : Summable
      (fun p : ℤ × ℤ => wabs r a p.2 * (wWeight r (p.1 - p.2) * ‖b (p.1 - p.2)‖)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.2 hsheared
  have hnn : 0 ≤ fun p : ℤ × ℤ => wabs r a p.2 * (wWeight r (p.1 - p.2) * ‖b (p.1 - p.2)‖) := by
    intro p
    have h1 := wabs_nonneg r a p.2; have h2 := wWeight_nonneg r (p.1 - p.2)
    have h3 := norm_nonneg (b (p.1 - p.2)); positivity
  exact ((summable_prod_of_nonneg hnn).1 hswap).2

/-- **The per-`n` termwise bound**: `wWeight n · ‖(a ⋆ b) n‖ ≤ ∑'_m wabs a m · wabs b (n-m)`. -/
private theorem conv_term_le (ha : MemW r a) (hb : MemW r b) (n : ℤ) :
    wWeight r n * ‖wConv a b n‖
      ≤ ∑' m : ℤ, wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖) := by
  have htriangle : ‖wConv a b n‖ ≤ ∑' m, ‖a m * b (n - m)‖ :=
    norm_tsum_le_tsum_norm (summable_conv_norm ha hb n)
  have hsumL : Summable (fun m => wWeight r n * ‖a m * b (n - m)‖) :=
    (summable_conv_norm ha hb n).mul_left _
  have hle : ∀ m : ℤ, wWeight r n * ‖a m * b (n - m)‖
      ≤ wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖) := by
    intro m
    unfold wabs
    rw [norm_mul]
    have hwsub : wWeight r n ≤ wWeight r m * wWeight r (n - m) := by
      have := wWeight_submul r m (n - m); simpa using this
    have h3 : (0 : ℝ) ≤ ‖a m‖ * ‖b (n - m)‖ := by positivity
    calc wWeight r n * (‖a m‖ * ‖b (n - m)‖)
        ≤ (wWeight r m * wWeight r (n - m)) * (‖a m‖ * ‖b (n - m)‖) :=
          mul_le_mul_of_nonneg_right hwsub h3
      _ = wWeight r m * ‖a m‖ * (wWeight r (n - m) * ‖b (n - m)‖) := by ring
  calc wWeight r n * ‖wConv a b n‖
      ≤ wWeight r n * ∑' m, ‖a m * b (n - m)‖ :=
        mul_le_mul_of_nonneg_left htriangle (wWeight_nonneg r n)
    _ = ∑' m, wWeight r n * ‖a m * b (n - m)‖ := by rw [tsum_mul_left]
    _ ≤ ∑' m, wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖) :=
        Summable.tsum_mono hsumL (summable_inner ha hb n) hle

/-- Group the sheared majorant by `n`, then by `m`: a single number both as a `ℤ×ℤ` tsum
and as the iterated `∑'_n ∑'_m`. -/
private theorem tsum_sheared_eq (ha : MemW r a) (hb : MemW r b) :
    (∑' p : ℤ × ℤ, wabs r a p.1 * (wWeight r (p.2 - p.1) * ‖b (p.2 - p.1)‖))
      = ∑' n : ℤ, ∑' m : ℤ, wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖) := by
  have hsum := summable_sheared ha hb
  rw [hsum.tsum_prod]
  -- goal: ∑'_m ∑'_n F(m,n) = ∑'_n ∑'_m F(m,n)
  have hcomm := Summable.tsum_comm
      (f := fun m n => wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖))
      (hsum.congr (fun p => by cases p; rfl))
  exact hcomm.symm

/-- The shear identifies the ℤ×ℤ product tsum with the sheared (convolution) tsum. -/
private theorem tsum_prod_eq_sheared (a b : ℤ → ℂ) :
    (∑' p : ℤ × ℤ, wabs r a p.1 * wabs r b p.2)
      = ∑' p : ℤ × ℤ, wabs r a p.1 * (wWeight r (p.2 - p.1) * ‖b (p.2 - p.1)‖) := by
  rw [← Equiv.tsum_eq shear (fun p : ℤ × ℤ => wabs r a p.1 * wabs r b p.2)]
  refine tsum_congr ?_
  rintro ⟨m, k⟩
  rw [shear_apply]
  rfl

/-- The RHS factorization: the product of the two norms equals the ℤ×ℤ majorant tsum. -/
private theorem wNorm_mul_eq_prod (ha : MemW r a) (hb : MemW r b) :
    wNorm r a * wNorm r b = ∑' p : ℤ × ℤ, wabs r a p.1 * wabs r b p.2 := by
  have hna : Summable (fun m => ‖wabs r a m‖) := by
    refine ha.congr ?_; intro m; rw [Real.norm_of_nonneg (wabs_nonneg r a m)]; rfl
  have hnb : Summable (fun k => ‖wabs r b k‖) := by
    refine hb.congr ?_; intro k; rw [Real.norm_of_nonneg (wabs_nonneg r b k)]; rfl
  have key := tsum_mul_tsum_of_summable_norm hna hnb
  have hwa : wNorm r a = ∑' m, wabs r a m := by rfl
  have hwb : wNorm r b = ∑' k, wabs r b k := by rfl
  rw [hwa, hwb, key]

/-- **Closure**: `MemW r a` and `MemW r b` imply `MemW r (a ⋆ b)`. -/
theorem memW_conv (ha : MemW r a) (hb : MemW r b) : MemW r (wConv a b) := by
  rw [MemW]
  refine Summable.of_nonneg_of_le (fun n => weightedNorm_nonneg r (wConv a b) n) ?_
    (summable_outer ha hb)
  exact fun n => conv_term_le ha hb n

/-- **The product norm bound (the Banach-algebra core).**
`wNorm r (a ⋆ b) ≤ wNorm r a · wNorm r b`. -/
theorem wNorm_conv_le (r : ℕ) {a b : ℤ → ℂ} (ha : MemW r a) (hb : MemW r b) :
    wNorm r (wConv a b) ≤ wNorm r a * wNorm r b := by
  have hLHS : Summable (fun n => wWeight r n * ‖wConv a b n‖) := memW_conv ha hb
  have hbound : wNorm r (wConv a b)
      ≤ ∑' n : ℤ, ∑' m : ℤ, wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖) := by
    rw [wNorm]
    exact Summable.tsum_mono hLHS (summable_outer ha hb) (fun n => conv_term_le ha hb n)
  calc wNorm r (wConv a b)
      ≤ ∑' n : ℤ, ∑' m : ℤ, wabs r a m * (wWeight r (n - m) * ‖b (n - m)‖) := hbound
    _ = ∑' p : ℤ × ℤ, wabs r a p.1 * (wWeight r (p.2 - p.1) * ‖b (p.2 - p.1)‖) :=
        (tsum_sheared_eq ha hb).symm
    _ = ∑' p : ℤ × ℤ, wabs r a p.1 * wabs r b p.2 := (tsum_prod_eq_sheared a b).symm
    _ = wNorm r a * wNorm r b := (wNorm_mul_eq_prod ha hb).symm

end Conv

end ShenWork.Wiener
