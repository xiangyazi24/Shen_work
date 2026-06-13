import ShenWork.Wiener.WeightedL1Power

/-!
# Brick 4a — the convolution ring laws on weighted ℓ¹ functions

Building on brick 1 (`wConv`, `memW_conv`, `summable_conv_term`) and the unit
`wOne` (brick 3a), this brick supplies the **commutative ring axioms** for the
convolution multiplication `wConv` with unit `wOne`, on the functions that are
`MemW 0` (absolutely summable, so all tsums converge and reindexing is valid):

* **Part A — commutativity** `wConv_comm`.
* **Part B — left/right unit** `wConv_wOne_left`, `wConv_wOne_right`.
* **Part C — associativity** `wConv_assoc` (the triple-sum Fubini, mirroring the
  brick-1 `wNorm_conv_le` factorization machinery).

These are the `CommRing` axioms feeding brick 4b (the `NormedCommRing` instance
on `A^r`).
-/

open scoped BigOperators

namespace ShenWork.Wiener

section RingLaws

/-! ## Part A — commutativity -/

/-- **Commutativity of convolution.** `(a ⋆ b) = (b ⋆ a)` for `MemW 0` functions. -/
theorem wConv_comm {a b : ℤ → ℂ} (ha : MemW 0 a) (hb : MemW 0 b) :
    wConv a b = wConv b a := by
  funext n
  unfold wConv
  -- Reindex m ↦ n - m via `Equiv.subLeft n`, then `mul_comm`.
  rw [← Equiv.tsum_eq (Equiv.subLeft n) (fun m => b m * a (n - m))]
  refine tsum_congr ?_
  intro m
  simp only [Equiv.subLeft_apply]
  rw [sub_sub_cancel, mul_comm]

/-! ## Part B — left/right unit -/

/-- **Left unit.** `wOne ⋆ a = a`. -/
theorem wConv_wOne_left {a : ℤ → ℂ} : wConv wOne a = a := by
  funext n
  unfold wConv
  rw [tsum_eq_single 0]
  · simp [wOne]
  · intro m hm
    simp [wOne, hm]

/-- **Right unit.** `a ⋆ wOne = a`. -/
theorem wConv_wOne_right {a : ℤ → ℂ} : wConv a wOne = a := by
  funext n
  unfold wConv
  rw [tsum_eq_single n]
  · simp [wOne]
  · intro m hm
    have : n - m ≠ 0 := by
      intro h; apply hm; omega
    simp [wOne, this]

/-! ## Part C — associativity (triple-sum Fubini) -/

section Assoc

variable {a b c : ℤ → ℂ} {n : ℤ}

/-- The reindexing equiv `(k, m) ↦ (m, k - m)` on `ℤ × ℤ`. -/
private noncomputable def shearA : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.prodComm ℤ ℤ).trans ((Equiv.refl ℤ).prodShear (fun m => Equiv.subRight m))

private theorem shearA_apply (k m : ℤ) : shearA (k, m) = (m, k - m) := by
  simp [shearA, Equiv.prodShear, Equiv.subRight, Equiv.prodComm]

/-- The ℂ-valued triple family `(m, p) ↦ a m · b p · c (n - m - p)`. -/
private noncomputable def triF (a b c : ℤ → ℂ) (n : ℤ) (p : ℤ × ℤ) : ℂ :=
  a p.1 * b p.2 * c (n - p.1 - p.2)

/-- The triple family is (absolutely) summable on `ℤ × ℤ`. -/
private theorem summable_triF (ha : MemW 0 a) (hb : MemW 0 b) (hc : MemW 0 c) :
    Summable (triF a b c n) := by
  have hna : Summable (fun m => ‖a m‖) := by
    refine ha.congr ?_; intro m; simp [wWeight]
  have hnb : Summable (fun p => ‖b p‖) := by
    refine hb.congr ?_; intro p; simp [wWeight]
  have hnc : Summable (fun y => ‖c y‖) := by
    refine hc.congr ?_; intro y; simp [wWeight]
  set C : ℝ := ∑' y, ‖c y‖ with hC
  have hCbound : ∀ x : ℤ, ‖c x‖ ≤ C := by
    intro x; exact hnc.le_tsum x (fun j _ => norm_nonneg _)
  -- majorant `N(m,p) = ‖a m‖ * ‖b p‖ * C` is summable
  have hmaj : Summable (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖) :=
    Summable.mul_of_nonneg hna hnb (fun m => norm_nonneg _) (fun p => norm_nonneg _)
  have hN : Summable (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ * C) := hmaj.mul_right C
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) ?_ hN
  intro p
  rw [triF, norm_mul, norm_mul]
  have hcle : ‖c (n - p.1 - p.2)‖ ≤ C := hCbound _
  have h0 : (0 : ℝ) ≤ ‖a p.1‖ * ‖b p.2‖ := by positivity
  calc ‖a p.1‖ * ‖b p.2‖ * ‖c (n - p.1 - p.2)‖
      ≤ ‖a p.1‖ * ‖b p.2‖ * C := mul_le_mul_of_nonneg_left hcle h0

/-- **Associativity of convolution.** `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)` for `MemW 0`. -/
theorem wConv_assoc {a b c : ℤ → ℂ} (ha : MemW 0 a) (hb : MemW 0 b)
    (hc : MemW 0 c) : wConv (wConv a b) c = wConv a (wConv b c) := by
  funext n
  have hF : Summable (triF a b c n) := summable_triF ha hb hc
  -- The LHS family `G(k,m) = (a m · b (k - m)) · c (n - k)`, summable via the reindex.
  have hG : Summable (fun p : ℤ × ℤ =>
      (a p.2 * b (p.1 - p.2)) * c (n - p.1)) := by
    have hpb := (shearA.summable_iff (f := triF a b c n)).2 hF
    refine hpb.congr ?_
    rintro ⟨k, m⟩
    rw [Function.comp_apply, shearA_apply, triF]
    have : n - m - (k - m) = n - k := by ring
    rw [this, mul_assoc]
  -- RHS = ∑'_{(m,j)} triF
  have hRHS : wConv a (wConv b c) n = ∑' p : ℤ × ℤ, triF a b c n p := by
    rw [hF.tsum_prod]
    unfold wConv
    refine tsum_congr ?_
    intro m
    rw [← (summable_conv_term hb hc (n - m)).tsum_mul_left (a m)]
    refine tsum_congr ?_
    intro j
    rw [triF, mul_assoc]
  -- LHS = ∑'_k ∑'_m G = ∑'_{(k,m)} G = ∑'_{(m,j)} triF (via the shear reindex)
  have hLHS : wConv (wConv a b) c n = ∑' p : ℤ × ℤ, triF a b c n p := by
    have hstep1 : wConv (wConv a b) c n
        = ∑' k : ℤ, ∑' m : ℤ, (a m * b (k - m)) * c (n - k) := by
      unfold wConv
      refine tsum_congr ?_
      intro k
      rw [← (summable_conv_term ha hb k).tsum_mul_right (c (n - k))]
    rw [hstep1, ← hG.tsum_prod, ← Equiv.tsum_eq shearA (triF a b c n)]
    refine tsum_congr ?_
    rintro ⟨k, m⟩
    rw [shearA_apply, triF]
    have he : n - m - (k - m) = n - k := by ring
    rw [he, mul_assoc]
  rw [hLHS, hRHS]

end Assoc

end RingLaws

end ShenWork.Wiener
