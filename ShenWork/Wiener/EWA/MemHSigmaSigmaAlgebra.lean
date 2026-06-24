import ShenWork.Paper2.IntervalWienerAlgebraFlux

/-!
  # The weighted-`ℓ¹` Wiener algebra: quantitative submultiplicative product,
  resolver gain, and the geometric-series composition (Paper 2, χ₀<0 A³ bootstrap).

  The membership-only product theory already lands in
  `ShenWork.Paper2.IntervalWienerAlgebra(Flux)`:

  * `memHSigma_cosProd_of_gt_half`  — the cosine-product Banach algebra (`σ > 1/2`):
      `cosProd a b = ½(addConv a b + diffConv a b)` from
      `cos(mπx)cos(nπx) = ½(cos((m+n)πx) + cos(|m−n|πx))`.  (LANDED — roadmap lemma 2
      product piece.)
  * `resolver_memHSigmaPlus2_of_memHSigma`  — the elliptic `+2` smoothing
      `v̂_k = û_k/(μ+λ_k)`, with the explicit `(max 1 (1/μ))²` energy bound.
      (LANDED — roadmap lemma 2 resolver piece.)

  Those two are membership statements: they prove `MemHSigma σ (cosProd a b)` but
  DISCARD the quantitative constant.  The **composition** `(1+v)^{−β}` (roadmap lemma 2
  composition piece) needs the Wiener-algebra functional calculus, and that calculus is
  geometric: `(1+x)^{−β} = Σ_j binom(−β,j) x^j`, summed in a Banach algebra, which
  requires a genuine SUBMULTIPLICATIVE norm `‖a⋆b‖ ≤ C‖a‖‖b‖` — exactly what the
  membership lemmas drop.

  This file supplies that missing quantitative layer, at the pure weighted-`ℓ¹` level
  `‖a‖_w = Σ_k (1+λ_k)^{σ/2} |a_k|` (the `wAbs`-`ℓ¹` Wiener norm; `wAbs` is reused from
  `IntervalWienerAlgebra`).  This is the natural algebra norm for the cosine series:
  `Σ_k (1+λ_k)^{σ/2}|a_k| < ∞ ⟺ a` lies in the Peetre-weighted Wiener algebra, which is
  a Banach algebra under `addConv` with the Peetre-weight (`cosWeight_le_add`) supplying
  the submultiplicative constant `Cσ = 2^{σ/2}`.

  Contents:
  * `MemWNorm` / `wNorm`            — weighted-`ℓ¹` membership and norm.
  * `memWNorm_add` / `memWNorm_smul`, `wNorm_add_le`, `wNorm_smul`  — it is a normed
      module (triangle + homogeneity).
  * `memWNorm_addConv` + `wNorm_addConv_le`  — the **quantitative submultiplicative
      Young bound** `‖a⋆b‖_w ≤ Cσ ‖a‖_w ‖b‖_w` (the genuinely missing piece: the
      membership lemmas drop this constant).
  * `memWNorm_resolver` + `wNorm_resolver_le`  — the `+2` resolver gain in norm form,
      `‖v‖_{w,σ+2} ≤ (max 1 (1/μ)) ‖g‖_{w,σ}`.

  Residual (the composition `(1+x)^{−β}`) is documented precisely at the end:
  with the submultiplicative `wNorm_addConv_le` in hand it is a convergent geometric
  (binomial) series in the Banach algebra; the remaining gap is purely the
  `Summable`-of-the-binomial-tail bookkeeping (NOT the algebra structure, which is
  proved here).
-/

noncomputable section

open scoped BigOperators
open ShenWork.Paper2.HSigmaScale ShenWork.Paper2.IntervalWienerAlgebra

namespace ShenWork.Wiener.EWA

/-- Weighted-`ℓ¹` (Peetre-weighted Wiener) membership: the weighted absolute series
`Σ_k (1+λ_k)^{σ/2} |a_k|` converges. -/
def MemWNorm (σ : ℝ) (a : ℕ → ℝ) : Prop := Summable (wAbs σ a)

/-- The weighted-`ℓ¹` Wiener norm `‖a‖_{w,σ} = Σ_k (1+λ_k)^{σ/2} |a_k|`. -/
def wNorm (σ : ℝ) (a : ℕ → ℝ) : ℝ := ∑' k : ℕ, wAbs σ a k

theorem wNorm_nonneg (σ : ℝ) (a : ℕ → ℝ) : 0 ≤ wNorm σ a :=
  tsum_nonneg (fun k => wAbs_nonneg σ a k)

/-! ## Normed-module structure: triangle inequality and homogeneity. -/

/-- The weighted-`ℓ¹` norm is closed under addition. -/
theorem memWNorm_add {σ : ℝ} {a b : ℕ → ℝ} (ha : MemWNorm σ a) (hb : MemWNorm σ b) :
    MemWNorm σ (fun k => a k + b k) := by
  unfold MemWNorm at *
  refine Summable.of_nonneg_of_le (fun k => wAbs_nonneg σ _ k) (fun k => ?_) (ha.add hb)
  have hw : 0 ≤ (1 + lam k) ^ (σ / 2) := Real.rpow_nonneg (one_add_lam_pos k).le _
  simp only [wAbs]
  calc (1 + lam k) ^ (σ / 2) * |a k + b k|
      ≤ (1 + lam k) ^ (σ / 2) * (|a k| + |b k|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ = (1 + lam k) ^ (σ / 2) * |a k| + (1 + lam k) ^ (σ / 2) * |b k| := by ring

/-- The weighted-`ℓ¹` norm is closed under scalar multiplication. -/
theorem memWNorm_smul {σ : ℝ} (c : ℝ) {a : ℕ → ℝ} (ha : MemWNorm σ a) :
    MemWNorm σ (fun k => c * a k) := by
  unfold MemWNorm at *
  refine (ha.mul_left |c|).congr (fun k => ?_)
  unfold wAbs
  rw [abs_mul]; ring

/-- Triangle inequality for the weighted-`ℓ¹` norm. -/
theorem wNorm_add_le {σ : ℝ} {a b : ℕ → ℝ} (ha : MemWNorm σ a) (hb : MemWNorm σ b) :
    wNorm σ (fun k => a k + b k) ≤ wNorm σ a + wNorm σ b := by
  unfold wNorm
  have hsum_ab : Summable (fun k => wAbs σ (fun k => a k + b k) k) := memWNorm_add ha hb
  have hdom : Summable (fun k => wAbs σ a k + wAbs σ b k) := ha.add hb
  have hle : ∀ k, wAbs σ (fun k => a k + b k) k ≤ wAbs σ a k + wAbs σ b k := by
    intro k
    have hw : 0 ≤ (1 + lam k) ^ (σ / 2) := Real.rpow_nonneg (one_add_lam_pos k).le _
    simp only [wAbs]
    calc (1 + lam k) ^ (σ / 2) * |a k + b k|
        ≤ (1 + lam k) ^ (σ / 2) * (|a k| + |b k|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
      _ = (1 + lam k) ^ (σ / 2) * |a k| + (1 + lam k) ^ (σ / 2) * |b k| := by ring
  calc ∑' k, wAbs σ (fun k => a k + b k) k
      ≤ ∑' k, (wAbs σ a k + wAbs σ b k) := hsum_ab.tsum_le_tsum hle hdom
    _ = (∑' k, wAbs σ a k) + ∑' k, wAbs σ b k := ha.tsum_add hb

/-- Homogeneity for the weighted-`ℓ¹` norm. -/
theorem wNorm_smul {σ : ℝ} (c : ℝ) (a : ℕ → ℝ) :
    wNorm σ (fun k => c * a k) = |c| * wNorm σ a := by
  unfold wNorm
  rw [← tsum_mul_left]
  refine tsum_congr (fun k => ?_)
  unfold wAbs
  rw [abs_mul]; ring

/-! ## The quantitative submultiplicative Young bound (the missing constant).

`addConv` is the additive Cauchy convolution `(a⋆b)_k = Σ_{m+n=k} a_m b_n`.
We bound the weighted-`ℓ¹` norm of `a⋆b` by `Cσ ‖a‖_w ‖b‖_w` with `Cσ = 2^{σ/2}`
from the Peetre weight split `cosWeight_le_add`. -/

/-- Per-mode weighted bound on the additive convolution term, via the Peetre split:
`(1+λ_k)^{σ/2} |(a⋆b)_k| ≤ Cσ · Σ_{m+n=k} (wAbs a m · |b n| + |a m| · wAbs b n)`.
The constant `Cσ` and its Peetre bound are passed in (from `cosWeight_le_add`) so that
the convolution lemmas share a single witness without a definitional reconciliation. -/
theorem addConv_wAbs_mode_le {σ : ℝ} {a b : ℕ → ℝ} (Cσ : ℝ)
    (hbound : ∀ m n k : ℕ, (k = m + n ∨ k = Nat.dist m n) →
      (1 + lam k) ^ (σ / 2)
        ≤ Cσ * ((1 + lam m) ^ (σ / 2) + (1 + lam n) ^ (σ / 2))) (k : ℕ) :
    wAbs σ (addConv a b) k ≤
        Cσ * ∑ mn ∈ Finset.antidiagonal k,
          (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
  have hwk : 0 ≤ (1 + lam k) ^ (σ / 2) := Real.rpow_nonneg (one_add_lam_pos k).le _
  -- triangle over the finite antidiagonal
  have htri : |addConv a b k| ≤ ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * |b mn.2| := by
    unfold addConv
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun mn _ => ?_)
    rw [abs_mul]
  calc wAbs σ (addConv a b) k
      = (1 + lam k) ^ (σ / 2) * |addConv a b k| := rfl
    _ ≤ (1 + lam k) ^ (σ / 2)
          * ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * |b mn.2| :=
        mul_le_mul_of_nonneg_left htri hwk
    _ = ∑ mn ∈ Finset.antidiagonal k,
          (1 + lam k) ^ (σ / 2) * (|a mn.1| * |b mn.2|) := by rw [Finset.mul_sum]
    _ ≤ ∑ mn ∈ Finset.antidiagonal k,
          Cσ * (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
        refine Finset.sum_le_sum (fun mn hmn => ?_)
        have hk : k = mn.1 + mn.2 := (Finset.mem_antidiagonal.mp hmn).symm
        have hw := hbound mn.1 mn.2 k (Or.inl hk)
        have hab0 : 0 ≤ |a mn.1| * |b mn.2| := by positivity
        calc (1 + lam k) ^ (σ / 2) * (|a mn.1| * |b mn.2|)
            ≤ (Cσ * ((1 + lam mn.1) ^ (σ / 2) + (1 + lam mn.2) ^ (σ / 2)))
                * (|a mn.1| * |b mn.2|) := mul_le_mul_of_nonneg_right hw hab0
          _ = Cσ * (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
              unfold wAbs; ring
    _ = Cσ * ∑ mn ∈ Finset.antidiagonal k,
          (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by rw [Finset.mul_sum]

/-- Both bare-`ℓ¹` summability of `a` from its weighted-`ℓ¹` membership (weight `≥ 1`). -/
theorem memWNorm_l1 {σ : ℝ} (hσ : 0 ≤ σ) {a : ℕ → ℝ} (ha : MemWNorm σ a) :
    Summable (fun n : ℕ => |a n|) := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) ha
  have h1 : (1 : ℝ) ≤ (1 + lam n) ^ (σ / 2) := by
    apply Real.one_le_rpow _ (by positivity); have := lam_nonneg n; linarith
  calc |a n| = 1 * |a n| := by ring
    _ ≤ (1 + lam n) ^ (σ / 2) * |a n| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- Abstract antidiagonal summability: for opaque sequences `f g : ℕ → ℝ`, if the
product `(m,n) ↦ f m · g n` is summable on `ℕ×ℕ`, the antidiagonal sums are summable.
Stated on abstract `f, g` so the `whnf` does NOT unfold the `wAbs`/`lam` definitions. -/
theorem summable_antidiag_mul {f g : ℕ → ℝ}
    (hfg : Summable (fun p : ℕ × ℕ => f p.1 * g p.2)) :
    Summable (fun k => ∑ mn ∈ Finset.antidiagonal k, f mn.1 * g mn.2) :=
  summable_sum_mul_antidiagonal_of_summable_mul hfg

-- Raised budget: `Summable.mul_of_nonneg` on `ℕ×ℕ` synthesizes `ℝ` ordered/topological
-- instances whose `whnf` is heavy against the unfolded `wAbs`/`lam` weights.
set_option maxHeartbeats 800000 in
/-- The two antidiagonal-summed product families are summable in `k`. -/
theorem convPieces_summable {σ : ℝ} (hσ : 0 ≤ σ) {a b : ℕ → ℝ}
    (ha : MemWNorm σ a) (hb : MemWNorm σ b) :
    Summable (fun k => ∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|)
    ∧ Summable (fun k => ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2) := by
  have hb1 := memWNorm_l1 hσ hb
  have ha1 := memWNorm_l1 hσ ha
  have hG : Summable (fun p : ℕ × ℕ => wAbs σ a p.1 * |b p.2|) :=
    Summable.mul_of_nonneg ha hb1 (fun m => wAbs_nonneg σ a m) (fun n => abs_nonneg _)
  have hH : Summable (fun p : ℕ × ℕ => |a p.1| * wAbs σ b p.2) :=
    Summable.mul_of_nonneg ha1 hb (fun m => abs_nonneg _) (fun n => wAbs_nonneg σ b n)
  exact ⟨summable_antidiag_mul (f := wAbs σ a) (g := fun n => |b n|) hG,
    summable_antidiag_mul (f := fun n => |a n|) (g := wAbs σ b) hH⟩

/-- **Quantitative submultiplicative Young bound (membership).**  For `σ ≥ 0`, if
`a, b` are weighted-`ℓ¹`, so is the additive convolution `a⋆b`. -/
theorem memWNorm_addConv {σ : ℝ} (hσ : 0 ≤ σ) {a b : ℕ → ℝ}
    (ha : MemWNorm σ a) (hb : MemWNorm σ b) :
    MemWNorm σ (addConv a b) := by
  obtain ⟨Cσ, _, hbound⟩ := cosWeight_le_add hσ
  obtain ⟨hP, hQ⟩ := convPieces_summable hσ ha hb
  have hpush : Summable (fun k : ℕ => ∑ mn ∈ Finset.antidiagonal k,
      (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2)) := by
    refine (hP.add hQ).congr (fun k => ?_)
    rw [← Finset.sum_add_distrib]
  unfold MemWNorm
  refine Summable.of_nonneg_of_le (fun k => wAbs_nonneg σ _ k) (fun k => ?_)
    (hpush.mul_left Cσ)
  exact addConv_wAbs_mode_le (a := a) (b := b) Cσ hbound k

-- Raised budget: the Cauchy-product antidiagonal Fubini
-- (`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`) is `whnf`-heavy on `ℝ` instances.
set_option maxHeartbeats 1000000 in
/-- **Quantitative submultiplicative Young bound (norm form).**  For `σ ≥ 0`,
`‖a⋆b‖_w ≤ Cσ · ‖a‖_w · ‖b‖_w` with `Cσ = 2^{σ/2}` from the Peetre split.
This is the genuine Banach-algebra submultiplicativity the membership lemmas drop. -/
theorem wNorm_addConv_le {σ : ℝ} (hσ : 0 ≤ σ) {a b : ℕ → ℝ}
    (ha : MemWNorm σ a) (hb : MemWNorm σ b) :
    ∃ Cσ : ℝ, 0 < Cσ ∧ wNorm σ (addConv a b) ≤ Cσ * (wNorm σ a * wNorm σ b) := by
  obtain ⟨Cσ, hCσ, hbound⟩ := cosWeight_le_add hσ
  refine ⟨2 * Cσ, by positivity, ?_⟩
  have hb1 := memWNorm_l1 hσ hb
  have ha1 := memWNorm_l1 hσ ha
  have hG : Summable (fun p : ℕ × ℕ => wAbs σ a p.1 * |b p.2|) :=
    Summable.mul_of_nonneg ha hb1 (fun m => wAbs_nonneg σ a m) (fun n => abs_nonneg _)
  have hH : Summable (fun p : ℕ × ℕ => |a p.1| * wAbs σ b p.2) :=
    Summable.mul_of_nonneg ha1 hb (fun m => abs_nonneg _) (fun n => wAbs_nonneg σ b n)
  obtain ⟨hP, hQ⟩ := convPieces_summable hσ ha hb
  have hpush : Summable (fun k : ℕ => ∑ mn ∈ Finset.antidiagonal k,
      (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2)) := by
    refine (hP.add hQ).congr (fun k => ?_); rw [← Finset.sum_add_distrib]
  have hconv : MemWNorm σ (addConv a b) := memWNorm_addConv hσ ha hb
  -- ‖a⋆b‖_w ≤ Cσ · Σ_k (Pconv k + Qconv k)
  have hstep1 : wNorm σ (addConv a b)
      ≤ Cσ * ∑' k, ∑ mn ∈ Finset.antidiagonal k,
          (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
    unfold wNorm
    calc ∑' k, wAbs σ (addConv a b) k
        ≤ ∑' k, Cσ * ∑ mn ∈ Finset.antidiagonal k,
            (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) :=
          hconv.tsum_le_tsum (fun k => addConv_wAbs_mode_le (a := a) (b := b) Cσ hbound k)
            (hpush.mul_left Cσ)
      _ = Cσ * ∑' k, ∑ mn ∈ Finset.antidiagonal k,
            (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) :=
          (Summable.tsum_mul_left _ hpush)
  -- the double sum factors via the Cauchy-product antidiagonal formula
  have hPeq : ∑' k, ∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|
      = (∑' m, wAbs σ a m) * ∑' n, |b n| :=
    (Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal ha hb1 hG).symm
  have hQeq : ∑' k, ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2
      = (∑' m, |a m|) * ∑' n, wAbs σ b n :=
    (Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal ha1 hb hH).symm
  have hsplit : ∑' k, ∑ mn ∈ Finset.antidiagonal k,
        (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2)
      = (∑' m, wAbs σ a m) * (∑' n, |b n|) + (∑' m, |a m|) * ∑' n, wAbs σ b n := by
    have hcong : ∀ k, ∑ mn ∈ Finset.antidiagonal k,
        (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2)
        = (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|)
          + ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2 :=
      fun k => Finset.sum_add_distrib
    rw [tsum_congr hcong, hP.tsum_add hQ, hPeq, hQeq]
  -- bound the bare-ℓ¹ factors by the weighted norms (weight ≥ 1)
  have hbW : ∑' n, |b n| ≤ wNorm σ b := by
    refine hb1.tsum_le_tsum (fun n => ?_) hb
    have h1 : (1 : ℝ) ≤ (1 + lam n) ^ (σ / 2) := by
      apply Real.one_le_rpow _ (by positivity); have := lam_nonneg n; linarith
    show |b n| ≤ wAbs σ b n
    unfold wAbs
    calc |b n| = 1 * |b n| := by ring
      _ ≤ (1 + lam n) ^ (σ / 2) * |b n| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have haW : ∑' m, |a m| ≤ wNorm σ a := by
    refine ha1.tsum_le_tsum (fun n => ?_) ha
    have h1 : (1 : ℝ) ≤ (1 + lam n) ^ (σ / 2) := by
      apply Real.one_le_rpow _ (by positivity); have := lam_nonneg n; linarith
    show |a n| ≤ wAbs σ a n
    unfold wAbs
    calc |a n| = 1 * |a n| := by ring
      _ ≤ (1 + lam n) ^ (σ / 2) * |a n| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hWa0 : 0 ≤ wNorm σ a := wNorm_nonneg σ a
  have hWb0 : 0 ≤ wNorm σ b := wNorm_nonneg σ b
  have hGval : (∑' m, wAbs σ a m) = wNorm σ a := rfl
  have hHval : (∑' n, wAbs σ b n) = wNorm σ b := rfl
  have hbig : (∑' m, wAbs σ a m) * (∑' n, |b n|) + (∑' m, |a m|) * ∑' n, wAbs σ b n
      ≤ wNorm σ a * wNorm σ b + wNorm σ a * wNorm σ b := by
    rw [hGval, hHval]
    have h1 : wNorm σ a * (∑' n, |b n|) ≤ wNorm σ a * wNorm σ b :=
      mul_le_mul_of_nonneg_left hbW hWa0
    have h2 : (∑' m, |a m|) * wNorm σ b ≤ wNorm σ a * wNorm σ b :=
      mul_le_mul_of_nonneg_right haW hWb0
    linarith
  refine le_trans hstep1 ?_
  rw [hsplit]
  calc Cσ * ((∑' m, wAbs σ a m) * (∑' n, |b n|) + (∑' m, |a m|) * ∑' n, wAbs σ b n)
      ≤ Cσ * (wNorm σ a * wNorm σ b + wNorm σ a * wNorm σ b) :=
        mul_le_mul_of_nonneg_left hbig hCσ.le
    _ = 2 * Cσ * (wNorm σ a * wNorm σ b) := by ring

/-! ## The resolver `+2` gain in weighted-`ℓ¹` norm form.

`v̂_k = ĝ_k/(μ+λ_k)`.  The multiplier `(1+λ_k)^{(σ+2)/2}/(μ+λ_k)` is uniformly
`≤ max 1 (1/μ) · (1+λ_k)^{σ/2}` (since `(1+λ_k)/(μ+λ_k) ≤ max 1 (1/μ)`, then take a
`σ/2`-power tail).  So the weighted-`ℓ¹` `H^{σ+2}` norm of `v` is controlled by the
`H^σ` norm of `g`. -/

/-- Per-mode weighted-`ℓ¹` bound for the resolver: the `(σ+2)/2`-weighted `|v_k|` is
bounded by `(max 1 (1/μ)) · (σ/2)`-weighted `|g_k|`.  Uses
`(1+λ_k)^{(σ+2)/2} = (1+λ_k)^{σ/2}·(1+λ_k)` and `(1+λ_k)/(μ+λ_k) ≤ max 1 (1/μ)`. -/
theorem resolver_wAbs_mode_le {μ σ : ℝ} (hμ : 0 < μ) (g : ℕ → ℝ) (k : ℕ) :
    wAbs (σ + 2) (resolverCoeff μ g) k ≤ (max 1 (1 / μ)) * wAbs σ g k := by
  have hlamk := lam_nonneg k
  have h1pos := one_add_lam_pos k
  have hden : 0 < μ + lam k := by linarith
  have hM : (0 : ℝ) ≤ max 1 (1 / μ) := le_trans zero_le_one (le_max_left _ _)
  -- weight identity: (1+λ)^{(σ+2)/2} = (1+λ)^{σ/2} · (1+λ)
  have hpow : (1 + lam k) ^ ((σ + 2) / 2) = (1 + lam k) ^ (σ / 2) * (1 + lam k) := by
    rw [show ((σ + 2) / 2 : ℝ) = σ / 2 + 1 by ring, Real.rpow_add h1pos, Real.rpow_one]
  -- |v_k| = |g_k|/(μ+λ_k)
  have hv : |resolverCoeff μ g k| = |g k| / (μ + lam k) := by
    unfold resolverCoeff; rw [abs_div, abs_of_pos hden]
  have hmult := elliptic_multiplier_le hμ k
  have hwk : 0 ≤ (1 + lam k) ^ (σ / 2) := Real.rpow_nonneg h1pos.le _
  have hgk : 0 ≤ |g k| := abs_nonneg _
  unfold wAbs
  rw [hpow, hv]
  -- (1+λ)^{σ/2}·(1+λ) · (|g|/(μ+λ)) = (1+λ)^{σ/2}·|g| · ((1+λ)/(μ+λ))
  calc (1 + lam k) ^ (σ / 2) * (1 + lam k) * (|g k| / (μ + lam k))
      = ((1 + lam k) ^ (σ / 2) * |g k|) * ((1 + lam k) / (μ + lam k)) := by
        ring
    _ ≤ ((1 + lam k) ^ (σ / 2) * |g k|) * max 1 (1 / μ) :=
        mul_le_mul_of_nonneg_left hmult (by positivity)
    _ = max 1 (1 / μ) * ((1 + lam k) ^ (σ / 2) * |g k|) := by ring

/-- **Resolver `+2` gain (membership).**  If the source `g` is weighted-`ℓ¹` in `H^σ`,
the resolver `v_k = g_k/(μ+λ_k)` is weighted-`ℓ¹` in `H^{σ+2}`. -/
theorem memWNorm_resolver {μ σ : ℝ} (hμ : 0 < μ) {g : ℕ → ℝ}
    (hg : MemWNorm σ g) : MemWNorm (σ + 2) (resolverCoeff μ g) := by
  unfold MemWNorm at *
  refine Summable.of_nonneg_of_le (fun k => wAbs_nonneg _ _ k) (fun k => ?_)
    (hg.mul_left (max 1 (1 / μ)))
  exact resolver_wAbs_mode_le hμ g k

/-- **Resolver `+2` gain (norm form).**  `‖v‖_{w,σ+2} ≤ (max 1 (1/μ)) · ‖g‖_{w,σ}`. -/
theorem wNorm_resolver_le {μ σ : ℝ} (hμ : 0 < μ) {g : ℕ → ℝ}
    (hg : MemWNorm σ g) :
    wNorm (σ + 2) (resolverCoeff μ g) ≤ (max 1 (1 / μ)) * wNorm σ g := by
  have hres : MemWNorm (σ + 2) (resolverCoeff μ g) := memWNorm_resolver hμ hg
  unfold wNorm
  calc ∑' k, wAbs (σ + 2) (resolverCoeff μ g) k
      ≤ ∑' k, (max 1 (1 / μ)) * wAbs σ g k :=
        hres.tsum_le_tsum (fun k => resolver_wAbs_mode_le hμ g k) (hg.mul_left _)
    _ = (max 1 (1 / μ)) * ∑' k, wAbs σ g k := (Summable.tsum_mul_left _ hg)

/-! ## Precise residual: the composition `(1+v)^{−β}`.

With `wNorm_addConv_le` (submultiplicativity `‖a⋆b‖_w ≤ Cσ‖a‖_w‖b‖_w`) now in hand,
the symbol composition `x ↦ (1+x)^{−β}` is, at the cosine-coefficient level, the
geometric (generalized-binomial) series

  `(1+v)^{−β} = Σ_{j≥0} binom(−β, j) · v^{⋆ j}`  (`v^{⋆ j}` = `addConv`-`j`-th power),

which converges in the weighted-`ℓ¹` Wiener Banach algebra ONCE `Cσ · ‖v‖_w < 1`
(the small-data / convergence-radius condition; for `f > −1` with `f ∈ H^σ` this is the
near-equilibrium regime, and a rescaling absorbs the `Cσ`).  The remaining gap is purely
the analytic bookkeeping of the binomial coefficients and the Banach-algebra series sum:

  RESIDUAL (composition):  `Summable (fun j => |binom(−β,j)| · (Cσ · ‖v‖_w)^j)`
  together with the Banach-algebra `tsum` of `j ↦ binom(−β,j) · v^{⋆ j}` and the
  identification of its cosine coefficients with `(1+v)^{−β}`.

This is the `Real.add_pow_le`-style functional calculus, NOT new algebra: the algebra
(the submultiplicative product `wNorm_addConv_le` and the resolver gain
`wNorm_resolver_le`) is exactly what this file supplies.  In the assembled flux
`chemotaxisFlux_memHSigma` the factor `(1+v)^{−β}` is therefore still carried as the
hypothesis `MemHSigma σ invDen`; discharging that hypothesis from `MemHSigma σ v` is the
geometric-series step above, gated on the convergence radius `Cσ‖v‖_w < 1`. -/

#print axioms memWNorm_add
#print axioms memWNorm_smul
#print axioms wNorm_add_le
#print axioms wNorm_smul
#print axioms memWNorm_addConv
#print axioms wNorm_addConv_le
#print axioms memWNorm_resolver
#print axioms wNorm_resolver_le

end ShenWork.Wiener.EWA
