import ShenWork.Wiener.GWA.Basic

/-!
# Brick E2 — the generic convolution Banach algebra `GWA K r`

This file equips the generic weighted ℓ¹ space `GWA K r` (brick E1,
`ShenWork/Wiener/GWA/Basic.lean`) with its convolution Banach-algebra structure,
mirroring the committed concrete-`ℂ` Wiener-algebra bricks
(`WeightedL1Convolution.lean`, `WeightedL1RingLaws.lean`,
`WeightedL1Algebra.lean`, `WeightedL1Eval.lean`) verbatim, with the coefficient
field `ℂ` replaced by an arbitrary complete `ℂ`-Banach-algebra `K`.

The **only** `K`-specific change relative to the `ℂ` template is the product
bound `‖x * y‖ ≤ ‖x‖ * ‖y‖`, which here comes from `norm_mul_le` (`NormedRing K`)
— an inequality — rather than the `ℂ`-equality `norm_mul`.  The ℤ×ℤ shear
product bound, the convolution ring laws (commutativity from `K` commutative,
associativity from `K` associative, the unit laws), distributivity, and the
`NormedCommRing` / `NormedAlgebra ℂ` instances are otherwise identical.

Delivered:
* `gConv`, `gOne`, `gMemW_gConv` (closure), `summable_gConv_term`;
* `gNorm_gConv_le` — the product-norm bound (the ℤ×ℤ Tonelli + `Equiv` shear);
* ring laws `gConv_comm`, `gConv_assoc`, `gConv_gOne_left/right`, `gConv_add`;
* instances `Mul`, `One`, `CommRing`, `NormedRing`, `NormedCommRing`,
  `Algebra ℂ`, `NormedAlgebra ℂ` on `GWA K r`.
-/

open scoped BigOperators

namespace ShenWork.GWA

variable {K : Type*} [NormedCommRing K] [NormedAlgebra ℂ K] [CompleteSpace K]

/-- Bilateral convolution `(a ⋆ b)_n = ∑_m a_m · b_{n-m}` (`K`'s ring `*`). -/
noncomputable def gConv (a b : ℤ → K) : ℤ → K := fun n => ∑' m, a m * b (n - m)

/-- The multiplicative unit (Kronecker delta at `0`). -/
def gOne : ℤ → K := fun n => if n = 0 then (1 : K) else 0

/-- **The submultiplicative weight** `(1 + |m+n|)^r ≤ (1 + |m|)^r (1 + |n|)^r`.
`ℝ`-only — identical to the concrete `wWeight_submul`. -/
theorem gWeight_submul (r : ℕ) (m n : ℤ) :
    gWeight r (m + n) ≤ gWeight r m * gWeight r n := by
  unfold gWeight
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ r
  push_cast
  have htri : |(m : ℝ) + n| ≤ |(m : ℝ)| + |(n : ℝ)| := abs_add_le _ _
  have h1 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
  nlinarith [htri, h1, h2]

section Conv

variable {r : ℕ} {a b : ℤ → K}

/-- Abbreviation for the nonnegative weighted-norm summand of `a`. -/
private noncomputable def gabs (r : ℕ) (a : ℤ → K) (m : ℤ) : ℝ := gWeight r m * ‖a m‖

private theorem gabs_nonneg (r : ℕ) (a : ℤ → K) (m : ℤ) : 0 ≤ gabs r a m :=
  gWeightedNorm_nonneg r a m

/-- The shear `(m, n) ↦ (m, n - m)` on `ℤ × ℤ`. -/
private noncomputable def shear : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.refl ℤ).prodShear (fun m => Equiv.subRight m)

private theorem shear_apply (m n : ℤ) : shear (m, n) = (m, n - m) := by
  simp [shear, Equiv.prodShear, Equiv.subRight]

/-- The product majorant `(m, k) ↦ gabs a m * gabs b k` is summable on `ℤ × ℤ`. -/
private theorem summable_prod_majorant (ha : GMemW r a) (hb : GMemW r b) :
    Summable (fun p : ℤ × ℤ => gabs r a p.1 * gabs r b p.2) :=
  Summable.mul_of_nonneg ha hb (fun m => gabs_nonneg r a m) (fun k => gabs_nonneg r b k)

/-- After the shear: `(m, n) ↦ gabs a m * (gWeight (n-m) * ‖b (n-m)‖)` is summable. -/
private theorem summable_sheared (ha : GMemW r a) (hb : GMemW r b) :
    Summable (fun p : ℤ × ℤ => gabs r a p.1 * (gWeight r (p.2 - p.1) * ‖b (p.2 - p.1)‖)) := by
  have hsum := summable_prod_majorant ha hb
  have := (shear.summable_iff
      (f := fun p : ℤ × ℤ => gabs r a p.1 * gabs r b p.2)).2 hsum
  refine this.congr ?_
  rintro ⟨m, k⟩
  rw [Function.comp_apply, shear_apply]
  rfl

/-- The sheared majorant, coordinates swapped. -/
private theorem summable_sheared_swap (ha : GMemW r a) (hb : GMemW r b) :
    Summable (fun p : ℤ × ℤ => gabs r a p.2 * (gWeight r (p.1 - p.2) * ‖b (p.1 - p.2)‖)) :=
  (Equiv.prodComm ℤ ℤ).summable_iff.2 (summable_sheared ha hb)

/-- The inner majorant `m ↦ gabs a m * (gWeight (n-m) * ‖b (n-m)‖)` is summable for each `n`. -/
private theorem summable_inner (ha : GMemW r a) (hb : GMemW r b) (n : ℤ) :
    Summable (fun m => gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖)) := by
  have h := (summable_sheared_swap ha hb).prod_factor n
  simpa using h

/-- **Per-`n` convolution norm summability**: `∑' m, ‖a m * b (n - m)‖` is summable. -/
theorem summable_gConv_norm (ha : GMemW r a) (hb : GMemW r b) (n : ℤ) :
    Summable (fun m => ‖a m * b (n - m)‖) := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_ (summable_inner ha hb n)
  intro m
  have hwm : (1 : ℝ) ≤ gWeight r m := by
    unfold gWeight; exact one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hwk : (1 : ℝ) ≤ gWeight r (n - m) := by
    unfold gWeight; exact one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hAm : ‖a m‖ ≤ gabs r a m := by
    have : ‖a m‖ = 1 * ‖a m‖ := (one_mul _).symm
    rw [this]; simp only [gabs]; gcongr
  have hBm : ‖b (n - m)‖ ≤ gWeight r (n - m) * ‖b (n - m)‖ := by
    nlinarith [norm_nonneg (b (n - m)), gWeight_nonneg r (n - m)]
  have h2 : (0 : ℝ) ≤ ‖b (n - m)‖ := norm_nonneg _
  calc ‖a m * b (n - m)‖
      ≤ ‖a m‖ * ‖b (n - m)‖ := norm_mul_le _ _
    _ ≤ gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖) :=
        mul_le_mul hAm hBm h2 (gabs_nonneg r a m)

/-- **Per-`n` convolution summability** (`K`-valued). -/
theorem summable_gConv_term (ha : GMemW r a) (hb : GMemW r b) (n : ℤ) :
    Summable (fun m => a m * b (n - m)) :=
  Summable.of_norm (summable_gConv_norm ha hb n)

/-- The outer sum is summable. -/
private theorem summable_outer (ha : GMemW r a) (hb : GMemW r b) :
    Summable (fun n : ℤ => ∑' m : ℤ, gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖)) := by
  have hsheared := summable_sheared ha hb
  have hswap : Summable
      (fun p : ℤ × ℤ => gabs r a p.2 * (gWeight r (p.1 - p.2) * ‖b (p.1 - p.2)‖)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.2 hsheared
  have hnn : 0 ≤ fun p : ℤ × ℤ => gabs r a p.2 * (gWeight r (p.1 - p.2) * ‖b (p.1 - p.2)‖) := by
    intro p
    have h1 := gabs_nonneg r a p.2; have h2 := gWeight_nonneg r (p.1 - p.2)
    have h3 := norm_nonneg (b (p.1 - p.2)); positivity
  exact ((summable_prod_of_nonneg hnn).1 hswap).2

/-- **The per-`n` termwise bound**. -/
private theorem gConv_term_le (ha : GMemW r a) (hb : GMemW r b) (n : ℤ) :
    gWeight r n * ‖gConv a b n‖
      ≤ ∑' m : ℤ, gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖) := by
  have htriangle : ‖gConv a b n‖ ≤ ∑' m, ‖a m * b (n - m)‖ :=
    norm_tsum_le_tsum_norm (summable_gConv_norm ha hb n)
  have hsumL : Summable (fun m => gWeight r n * ‖a m * b (n - m)‖) :=
    (summable_gConv_norm ha hb n).mul_left _
  have hle : ∀ m : ℤ, gWeight r n * ‖a m * b (n - m)‖
      ≤ gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖) := by
    intro m
    unfold gabs
    have hwsub : gWeight r n ≤ gWeight r m * gWeight r (n - m) := by
      have := gWeight_submul r m (n - m); simpa using this
    have hmul : ‖a m * b (n - m)‖ ≤ ‖a m‖ * ‖b (n - m)‖ := norm_mul_le _ _
    have h3 : (0 : ℝ) ≤ ‖a m‖ * ‖b (n - m)‖ := by positivity
    calc gWeight r n * ‖a m * b (n - m)‖
        ≤ gWeight r n * (‖a m‖ * ‖b (n - m)‖) :=
          mul_le_mul_of_nonneg_left hmul (gWeight_nonneg r n)
      _ ≤ (gWeight r m * gWeight r (n - m)) * (‖a m‖ * ‖b (n - m)‖) :=
          mul_le_mul_of_nonneg_right hwsub h3
      _ = gWeight r m * ‖a m‖ * (gWeight r (n - m) * ‖b (n - m)‖) := by ring
  calc gWeight r n * ‖gConv a b n‖
      ≤ gWeight r n * ∑' m, ‖a m * b (n - m)‖ :=
        mul_le_mul_of_nonneg_left htriangle (gWeight_nonneg r n)
    _ = ∑' m, gWeight r n * ‖a m * b (n - m)‖ := by rw [tsum_mul_left]
    _ ≤ ∑' m, gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖) :=
        Summable.tsum_mono hsumL (summable_inner ha hb n) hle

/-- Group the sheared majorant by `n`, then by `m`. -/
private theorem tsum_sheared_eq (ha : GMemW r a) (hb : GMemW r b) :
    (∑' p : ℤ × ℤ, gabs r a p.1 * (gWeight r (p.2 - p.1) * ‖b (p.2 - p.1)‖))
      = ∑' n : ℤ, ∑' m : ℤ, gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖) := by
  have hsum := summable_sheared ha hb
  rw [hsum.tsum_prod]
  have hcomm := Summable.tsum_comm
      (f := fun m n => gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖))
      (hsum.congr (fun p => by cases p; rfl))
  exact hcomm.symm

/-- The shear identifies the ℤ×ℤ product tsum with the sheared tsum. -/
private theorem tsum_prod_eq_sheared (a b : ℤ → K) :
    (∑' p : ℤ × ℤ, gabs r a p.1 * gabs r b p.2)
      = ∑' p : ℤ × ℤ, gabs r a p.1 * (gWeight r (p.2 - p.1) * ‖b (p.2 - p.1)‖) := by
  rw [← Equiv.tsum_eq shear (fun p : ℤ × ℤ => gabs r a p.1 * gabs r b p.2)]
  refine tsum_congr ?_
  rintro ⟨m, k⟩
  rw [shear_apply]
  rfl

/-- The RHS factorization: the product of norms = the ℤ×ℤ majorant tsum. -/
private theorem gNorm_mul_eq_prod (ha : GMemW r a) (hb : GMemW r b) :
    gNorm r a * gNorm r b = ∑' p : ℤ × ℤ, gabs r a p.1 * gabs r b p.2 := by
  have hna : Summable (fun m => ‖gabs r a m‖) := by
    refine ha.congr ?_; intro m; rw [Real.norm_of_nonneg (gabs_nonneg r a m)]; rfl
  have hnb : Summable (fun k => ‖gabs r b k‖) := by
    refine hb.congr ?_; intro k; rw [Real.norm_of_nonneg (gabs_nonneg r b k)]; rfl
  have key := tsum_mul_tsum_of_summable_norm hna hnb
  have hwa : gNorm r a = ∑' m, gabs r a m := by rfl
  have hwb : gNorm r b = ∑' k, gabs r b k := by rfl
  rw [hwa, hwb, key]

/-- **Closure**: `GMemW r a` and `GMemW r b` imply `GMemW r (a ⋆ b)`. -/
theorem gMemW_gConv (ha : GMemW r a) (hb : GMemW r b) : GMemW r (gConv a b) := by
  rw [GMemW]
  refine Summable.of_nonneg_of_le (fun n => gWeightedNorm_nonneg r (gConv a b) n) ?_
    (summable_outer ha hb)
  exact fun n => gConv_term_le ha hb n

/-- **The product norm bound (the Banach-algebra core).** -/
theorem gNorm_gConv_le (r : ℕ) {a b : ℤ → K} (ha : GMemW r a) (hb : GMemW r b) :
    gNorm r (gConv a b) ≤ gNorm r a * gNorm r b := by
  have hLHS : Summable (fun n => gWeight r n * ‖gConv a b n‖) := gMemW_gConv ha hb
  have hbound : gNorm r (gConv a b)
      ≤ ∑' n : ℤ, ∑' m : ℤ, gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖) := by
    rw [gNorm]
    exact Summable.tsum_mono hLHS (summable_outer ha hb) (fun n => gConv_term_le ha hb n)
  calc gNorm r (gConv a b)
      ≤ ∑' n : ℤ, ∑' m : ℤ, gabs r a m * (gWeight r (n - m) * ‖b (n - m)‖) := hbound
    _ = ∑' p : ℤ × ℤ, gabs r a p.1 * (gWeight r (p.2 - p.1) * ‖b (p.2 - p.1)‖) :=
        (tsum_sheared_eq ha hb).symm
    _ = ∑' p : ℤ × ℤ, gabs r a p.1 * gabs r b p.2 := (tsum_prod_eq_sheared a b).symm
    _ = gNorm r a * gNorm r b := (gNorm_mul_eq_prod ha hb).symm

end Conv

/-! ### The convolution ring laws (mirroring `WeightedL1RingLaws.lean`). -/

section RingLaws

/-- **Commutativity of convolution.** Uses `K` commutative. -/
theorem gConv_comm {a b : ℤ → K} (ha : GMemW 0 a) (hb : GMemW 0 b) :
    gConv a b = gConv b a := by
  funext n
  unfold gConv
  rw [← Equiv.tsum_eq (Equiv.subLeft n) (fun m => b m * a (n - m))]
  refine tsum_congr ?_
  intro m
  simp only [Equiv.subLeft_apply]
  rw [sub_sub_cancel, mul_comm]

/-- **Left unit.** `gOne ⋆ a = a`. -/
theorem gConv_gOne_left {a : ℤ → K} : gConv gOne a = a := by
  funext n
  unfold gConv
  rw [tsum_eq_single 0]
  · simp [gOne]
  · intro m hm
    simp [gOne, hm]

/-- **Right unit.** `a ⋆ gOne = a`. -/
theorem gConv_gOne_right {a : ℤ → K} : gConv a gOne = a := by
  funext n
  unfold gConv
  rw [tsum_eq_single n]
  · simp [gOne]
  · intro m hm
    have : n - m ≠ 0 := by
      intro h; apply hm; omega
    simp [gOne, this]

section Assoc

variable {a b c : ℤ → K} {n : ℤ}

/-- The reindexing equiv `(k, m) ↦ (m, k - m)` on `ℤ × ℤ`. -/
private noncomputable def shearA : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.prodComm ℤ ℤ).trans ((Equiv.refl ℤ).prodShear (fun m => Equiv.subRight m))

private theorem shearA_apply (k m : ℤ) : shearA (k, m) = (m, k - m) := by
  simp [shearA, Equiv.prodShear, Equiv.subRight, Equiv.prodComm]

/-- The `K`-valued triple family `(m, p) ↦ a m · b p · c (n - m - p)`. -/
private noncomputable def triF (a b c : ℤ → K) (n : ℤ) (p : ℤ × ℤ) : K :=
  a p.1 * b p.2 * c (n - p.1 - p.2)

/-- The triple family is (absolutely) summable on `ℤ × ℤ`. -/
private theorem summable_triF (ha : GMemW 0 a) (hb : GMemW 0 b) (hc : GMemW 0 c) :
    Summable (triF a b c n) := by
  have hna : Summable (fun m => ‖a m‖) := by
    refine ha.congr ?_; intro m; simp [gWeight]
  have hnb : Summable (fun p => ‖b p‖) := by
    refine hb.congr ?_; intro p; simp [gWeight]
  have hnc : Summable (fun y => ‖c y‖) := by
    refine hc.congr ?_; intro y; simp [gWeight]
  set C : ℝ := ∑' y, ‖c y‖ with hC
  have hCbound : ∀ x : ℤ, ‖c x‖ ≤ C := by
    intro x; exact hnc.le_tsum x (fun j _ => norm_nonneg _)
  have hmaj : Summable (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖) :=
    Summable.mul_of_nonneg hna hnb (fun m => norm_nonneg _) (fun p => norm_nonneg _)
  have hN : Summable (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ * C) := hmaj.mul_right C
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) ?_ hN
  intro p
  have hcle : ‖c (n - p.1 - p.2)‖ ≤ C := hCbound _
  have h0 : (0 : ℝ) ≤ ‖a p.1‖ * ‖b p.2‖ := by positivity
  calc ‖triF a b c n p‖
      = ‖a p.1 * b p.2 * c (n - p.1 - p.2)‖ := by rw [triF]
    _ ≤ ‖a p.1 * b p.2‖ * ‖c (n - p.1 - p.2)‖ := norm_mul_le _ _
    _ ≤ ‖a p.1‖ * ‖b p.2‖ * ‖c (n - p.1 - p.2)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖a p.1‖ * ‖b p.2‖ * C := mul_le_mul_of_nonneg_left hcle h0

/-- **Associativity of convolution.** `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)` for `GMemW 0`. -/
theorem gConv_assoc {a b c : ℤ → K} (ha : GMemW 0 a) (hb : GMemW 0 b)
    (hc : GMemW 0 c) : gConv (gConv a b) c = gConv a (gConv b c) := by
  funext n
  have hF : Summable (triF a b c n) := summable_triF ha hb hc
  have hG : Summable (fun p : ℤ × ℤ =>
      (a p.2 * b (p.1 - p.2)) * c (n - p.1)) := by
    have hpb := (shearA.summable_iff (f := triF a b c n)).2 hF
    refine hpb.congr ?_
    rintro ⟨k, m⟩
    rw [Function.comp_apply, shearA_apply, triF]
    have : n - m - (k - m) = n - k := by ring
    rw [this, mul_assoc]
  have hRHS : gConv a (gConv b c) n = ∑' p : ℤ × ℤ, triF a b c n p := by
    rw [hF.tsum_prod]
    unfold gConv
    refine tsum_congr ?_
    intro m
    rw [← (summable_gConv_term hb hc (n - m)).tsum_mul_left (a m)]
    refine tsum_congr ?_
    intro j
    rw [triF, mul_assoc]
  have hLHS : gConv (gConv a b) c n = ∑' p : ℤ × ℤ, triF a b c n p := by
    have hstep1 : gConv (gConv a b) c n
        = ∑' k : ℤ, ∑' m : ℤ, (a m * b (k - m)) * c (n - k) := by
      unfold gConv
      refine tsum_congr ?_
      intro k
      rw [← (summable_gConv_term ha hb k).tsum_mul_right (c (n - k))]
    rw [hstep1, ← hG.tsum_prod, ← Equiv.tsum_eq shearA (triF a b c n)]
    refine tsum_congr ?_
    rintro ⟨k, m⟩
    rw [shearA_apply, triF]
    have he : n - m - (k - m) = n - k := by ring
    rw [he, mul_assoc]
  rw [hLHS, hRHS]

end Assoc

end RingLaws

/-! ### The bundled algebra instances on `GWA K r`. -/

namespace GWA

variable {r : ℕ}

/-- Cast a `GMemW r` witness down to `GMemW 0`, to apply the `GMemW 0` ring laws. -/
theorem gMem0 (a : GWA K r) : GMemW 0 a.toFun := by
  rw [GMemW]
  refine Summable.of_nonneg_of_le (fun n => gWeightedNorm_nonneg 0 a.toFun n) ?_ a.mem
  intro n
  have hle : gWeight 0 n ≤ gWeight r n := by
    unfold gWeight
    exact pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (Nat.zero_le r)
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- `gOne` lies in every weighted ℓ¹ space (it is finitely supported). -/
theorem gMemW_gOne (r : ℕ) : GMemW r (gOne : ℤ → K) := by
  rw [GMemW]
  refine summable_of_hasFiniteSupport ?_
  apply Set.Finite.subset (Set.finite_singleton (0 : ℤ))
  intro n hn
  simp only [Function.mem_support, Set.mem_singleton_iff] at *
  by_contra hne
  apply hn
  simp [gOne, hne]

/-- `gConv` pulls a left scalar out: `gConv (c • a) b = c • gConv a b`. -/
theorem gConv_smul_left (c : ℂ) (a b : ℤ → K) :
    gConv (c • a) b = c • gConv a b := by
  funext n
  show (∑' m, (c • a) m * b (n - m)) = c • (∑' m, a m * b (n - m))
  rw [← tsum_const_smul'']
  refine tsum_congr ?_
  intro m; rw [Pi.smul_apply, smul_mul_assoc]

/-- `gConv` distributes over `+` on the right.  New helper. -/
theorem gConv_add {a b c : ℤ → K} (ha : GMemW r a) (hb : GMemW r b) (hc : GMemW r c) :
    gConv a (b + c) = gConv a b + gConv a c := by
  funext n
  show (∑' m, a m * (b + c) (n - m))
    = (∑' m, a m * b (n - m)) + ∑' m, a m * c (n - m)
  have hsb : Summable (fun m => a m * b (n - m)) := summable_gConv_term ha hb n
  have hsc : Summable (fun m => a m * c (n - m)) := summable_gConv_term ha hc n
  rw [← Summable.tsum_add hsb hsc]
  refine tsum_congr ?_
  intro m
  rw [Pi.add_apply]; ring

/-- Convolution multiplication on `GWA K r`. -/
noncomputable instance : Mul (GWA K r) :=
  ⟨fun a b => ⟨gConv a.toFun b.toFun, gMemW_gConv a.mem b.mem⟩⟩
/-- The convolution unit `gOne`. -/
instance : One (GWA K r) := ⟨⟨gOne, gMemW_gOne r⟩⟩

@[simp] theorem mul_toFun (a b : GWA K r) : (a * b).toFun = gConv a.toFun b.toFun := rfl
@[simp] theorem one_toFun : (1 : GWA K r).toFun = gOne := rfl

noncomputable instance : CommRing (GWA K r) where
  mul_comm a b := GWA.ext (by simp only [mul_toFun]; exact gConv_comm (gMem0 a) (gMem0 b))
  mul_assoc a b c :=
    GWA.ext (by simp only [mul_toFun]; exact gConv_assoc (gMem0 a) (gMem0 b) (gMem0 c))
  one_mul a := GWA.ext (by simp only [mul_toFun, one_toFun]; exact gConv_gOne_left)
  mul_one a := GWA.ext (by simp only [mul_toFun, one_toFun]; exact gConv_gOne_right)
  left_distrib a b c :=
    GWA.ext (by simp only [mul_toFun, add_toFun]; exact gConv_add a.mem b.mem c.mem)
  right_distrib a b c := GWA.ext (by
    simp only [mul_toFun, add_toFun]
    rw [gConv_comm (gMemW_add (gMem0 a) (gMem0 b)) (gMem0 c),
      gConv_add (gMem0 c) (gMem0 a) (gMem0 b),
      gConv_comm (gMem0 c) (gMem0 a), gConv_comm (gMem0 c) (gMem0 b)])
  zero_mul a := GWA.ext (by
    simp only [mul_toFun, zero_toFun]
    funext n; simp [gConv])
  mul_zero a := GWA.ext (by
    simp only [mul_toFun, zero_toFun]
    funext n; simp [gConv])

/-- The submultiplicative norm bound on `GWA K r`: `‖a * b‖ ≤ ‖a‖ * ‖b‖`. -/
theorem norm_mul_le_gwa (a b : GWA K r) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by
  show gNorm r (gConv a.toFun b.toFun) ≤ gNorm r a.toFun * gNorm r b.toFun
  exact gNorm_gConv_le r a.mem b.mem

/-- `GWA K r` is a normed ring (convolution, submultiplicative `gNorm`). -/
noncomputable instance : NormedRing (GWA K r) where
  dist_eq a b := by rw [dist_eq_norm]; rw [show -a + b = b - a by ring, norm_sub_rev]
  norm_mul_le := norm_mul_le_gwa

/-- `GWA K r` is a normed commutative ring — the gateway to `NormedSpace.exp`. -/
noncomputable instance : NormedCommRing (GWA K r) where
  mul_comm := mul_comm

/-! ### The `Algebra ℂ` / `NormedAlgebra ℂ` instances. -/

/-- `GWA K r` is a `ℂ`-algebra (algebraMap `c ↦ c • 1`). -/
noncomputable instance algebraInst {r : ℕ} : Algebra ℂ (GWA K r) :=
  Algebra.ofModule
    (fun c a b => by
      apply GWA.ext
      simp only [smul_toFun, mul_toFun, smul_toFun]
      exact gConv_smul_left c a.toFun b.toFun)
    (fun c a b => by
      apply GWA.ext
      simp only [smul_toFun, mul_toFun, smul_toFun]
      rw [gConv_comm (gMem0 a) (gMemW_smul c (gMem0 b)), gConv_smul_left,
        gConv_comm (gMem0 b) (gMem0 a)])

@[simp] theorem algebraMap_toFun {r : ℕ} (c : ℂ) :
    (algebraMap ℂ (GWA K r) c).toFun = c • gOne := rfl

/-- `GWA K r` is a `ℂ`-normed algebra. -/
noncomputable instance normedAlgebraInst {r : ℕ} : NormedAlgebra ℂ (GWA K r) where
  norm_smul_le c a := by
    rw [norm_def, norm_def, smul_toFun, gNorm_smul]

/-- Sanity test lemma exercising the `NormedCommRing` `norm_mul_le` field. -/
theorem test_norm_mul_le (a b : GWA K r) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le a b

/-- Sanity test: `ℂ` is a valid coefficient ring `K`, so `NormedCommRing` fires on `GWA ℂ 1`. -/
noncomputable example : NormedCommRing (GWA ℂ 1) := inferInstance

/-- Sanity test: `NormedAlgebra ℂ` fires on `GWA ℂ 1`. -/
noncomputable example : NormedAlgebra ℂ (GWA ℂ 1) := inferInstance

end GWA

end ShenWork.GWA
