import ShenWork.Paper2.IntervalWienerAlgebra

/-!
  # WALL-A completion: the difference-convolution `H^σ` algebra and the chemotaxis
  flux regularity (σ > 1/2), Paper 2.

  Builds on `ShenWork.Paper2.IntervalWienerAlgebra` (the additive-convolution prize):
  `cosWeight_le_add`, `hSigma_subset_l1_of_gt_half`, `memHSigma_addConv_of_gt_half`,
  `wAbs`, `summable_wAbs_sq`, `addConv`.

  Contents:
  * `corr1` / `memHSigma_corr1`     — the difference-convolution `(m−n=k)` correlation
      piece via the AT-MOST-2-COVER reindex (the genuine combinatorial gap of WALL-A:
      `Nat.dist m n = k` is not injective on `(m,n) ↦ k`, so the fiber splits into the
      two injective pieces `{m−n=k}` and `{n−m=k}`; each is handled by the shift
      reindex `corrShift_sum_le_tsum`).
  * `diffConv` / `memHSigma_diffConv_of_gt_half` — the difference convolution
      `(a ⊗ b)_k = Σ_{|m−n|=k} aₘbₙ = corr1 a b k + corr1 b a k`, in `H^σ`.
  * `cosProd` / `memHSigma_cosProd_of_gt_half`   — the cosine product coefficient
      `½(a ⋆ b + a ⊗ b)` and its `H^σ` membership (the H^σ Banach algebra).
  * `memHSigma_mul3_of_gt_half`     — the triple product (associated to `u^m·w·v_x`).
  * `chemotaxisFlux_memHSigma`      — THE TARGET: given the three cosine-coefficient
      factors of `u^m`, `(1+v)^{−β}`, `v_x` in `H^σ`, the chemotaxis flux coefficient
      sequence `Q = u^m (1+v)^{−β} v_x` lies in `H^σ`.
  * `chemotaxisFlux_L2_of_bounded`  — the elementary step-1 seed (`H^0 = ℓ²`).

  Everything is at the cosine-coefficient sequence level (`MemHSigma`), exactly the
  level at which the resolver gain `resolver_memHSigmaPlus2_of_memHSigma` and the
  Duhamel energy bound `hSigmaEnergy_duhamel_bound` already live.
-/

noncomputable section

open scoped BigOperators
open ShenWork.Paper2.HSigmaScale

namespace ShenWork.Paper2.IntervalWienerAlgebra

/-! ## `MemHSigma` is a module: closed under addition and scalar multiplication. -/

/-- `H^σ` is closed under addition. -/
theorem memHSigma_add {σ : ℝ} {a b : ℕ → ℝ} (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (fun k => a k + b k) := by
  unfold MemHSigma at *
  have hbound : ∀ k, (1 + lam k) ^ σ * (a k + b k) ^ 2 ≤
      2 * ((1 + lam k) ^ σ * (a k) ^ 2) + 2 * ((1 + lam k) ^ σ * (b k) ^ 2) := by
    intro k
    have hw : 0 ≤ (1 + lam k) ^ σ := Real.rpow_nonneg (one_add_lam_pos k).le σ
    nlinarith [sq_nonneg (a k - b k), hw]
  refine Summable.of_nonneg_of_le (fun k => ?_) hbound ((ha.mul_left 2).add (hb.mul_left 2))
  have hw : 0 ≤ (1 + lam k) ^ σ := Real.rpow_nonneg (one_add_lam_pos k).le σ
  positivity

/-- `H^σ` is closed under scalar multiplication. -/
theorem memHSigma_smul {σ : ℝ} (c : ℝ) {a : ℕ → ℝ} (ha : MemHSigma σ a) :
    MemHSigma σ (fun k => c * a k) := by
  unfold MemHSigma at *
  exact (ha.mul_left (c ^ 2)).congr (fun k => by ring)

/-! ## The shift reindex (the 2-cover engine). -/

/-- The shift map `(k,n) ↦ (n+k, n)` (one injective leaf of the `Nat.dist`-fiber). -/
theorem corrShift_inj : Function.Injective (fun p : ℕ × ℕ => (p.2 + p.1, p.2)) := by
  rintro ⟨k1, n1⟩ ⟨k2, n2⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h; subst h2
  have : k1 = k2 := by omega
  subst this; rfl

/-- **Shift reindex bound.**  For nonneg summable `g : ℕ×ℕ → ℝ`, the partial sum over
`k ∈ u` of the shifted fiber `∑'_n g(n+k, n)` is `≤ ∑' g`.  The reindex `(k,n) ↦
(n+k, n)` is injective; this is the difference-convolution analogue of
`sum_antidiagonal_le_tsum`. -/
theorem corrShift_sum_le_tsum {g : ℕ × ℕ → ℝ} (hg0 : ∀ p, 0 ≤ g p)
    (hg : Summable g) (u : Finset ℕ) :
    ∑ k ∈ u, ∑' n : ℕ, g (n + k, n) ≤ ∑' p, g p := by
  set i : ℕ × ℕ → ℕ × ℕ := fun p => (p.2 + p.1, p.2) with hi
  have hinj : Function.Injective i := corrShift_inj
  have hG : Summable (fun p : ℕ × ℕ => g (i p)) := hg.comp_injective hinj
  have hfib := hG.hasSum.prod_fiberwise (g := fun k => ∑' n : ℕ, g (i (k, n)))
    (fun k => (hG.prod_factor k).hasSum)
  have houter : Summable (fun k : ℕ => ∑' n : ℕ, g (i (k, n))) := hfib.summable
  have hstep1 : ∑ k ∈ u, ∑' n : ℕ, g (n + k, n) ≤ ∑' q : ℕ × ℕ, g (i q) := by
    have heq : ∀ k n : ℕ, g (i (k, n)) = g (n + k, n) := fun k n => rfl
    calc ∑ k ∈ u, ∑' n : ℕ, g (n + k, n)
        = ∑ k ∈ u, ∑' n : ℕ, g (i (k, n)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_); simp only [heq]
      _ ≤ ∑' k : ℕ, ∑' n : ℕ, g (i (k, n)) :=
          Summable.sum_le_tsum u (fun k _ => tsum_nonneg (fun n => hg0 _)) houter
      _ = ∑' q : ℕ × ℕ, g (i q) := (hG.tsum_prod).symm
  exact le_trans hstep1
    (hG.tsum_le_tsum_of_inj i hinj (fun _ _ => hg0 _) (fun _ => le_refl _) hg)

/-- **tsum-level weighted Cauchy–Schwarz.**  For nonneg weight `p` and summability of
the three relevant series, `(∑' p·|b|)² ≤ (∑'|b|)·(∑' p²·|b|)`. -/
theorem tsum_cs_weighted (p b : ℕ → ℝ) (hb : Summable (fun n => |b n|))
    (hpb : Summable (fun n => (p n) ^ 2 * |b n|)) (hpb1 : Summable (fun n => p n * |b n|)) :
    (∑' n, p n * |b n|) ^ 2 ≤ (∑' n, |b n|) * (∑' n, (p n) ^ 2 * |b n|) := by
  have hfin : ∀ s : Finset ℕ,
      (∑ n ∈ s, p n * |b n|) ^ 2 ≤ (∑' n, |b n|) * (∑' n, (p n) ^ 2 * |b n|) := by
    intro s
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun n => Real.sqrt |b n|) (fun n => p n * Real.sqrt |b n|)
    have hL : ∀ n, Real.sqrt |b n| * (p n * Real.sqrt |b n|) = p n * |b n| := by
      intro n
      have : Real.sqrt |b n| * Real.sqrt |b n| = |b n| := Real.mul_self_sqrt (abs_nonneg _)
      calc Real.sqrt |b n| * (p n * Real.sqrt |b n|)
          = p n * (Real.sqrt |b n| * Real.sqrt |b n|) := by ring
        _ = p n * |b n| := by rw [this]
    have hR1 : ∀ n, (Real.sqrt |b n|) ^ 2 = |b n| := fun n => Real.sq_sqrt (abs_nonneg _)
    have hR2 : ∀ n, (p n * Real.sqrt |b n|) ^ 2 = (p n) ^ 2 * |b n| := by
      intro n; rw [mul_pow, hR1]
    rw [Finset.sum_congr rfl (fun n _ => hL n)] at hcs
    rw [Finset.sum_congr rfl (fun n _ => hR1 n),
        Finset.sum_congr rfl (fun n _ => hR2 n)] at hcs
    have h1 : ∑ n ∈ s, |b n| ≤ ∑' n, |b n| :=
      Summable.sum_le_tsum s (fun n _ => abs_nonneg _) hb
    have h2 : ∑ n ∈ s, (p n) ^ 2 * |b n| ≤ ∑' n, (p n) ^ 2 * |b n| :=
      Summable.sum_le_tsum s (fun n _ => by positivity) hpb
    calc (∑ n ∈ s, p n * |b n|) ^ 2
        ≤ (∑ n ∈ s, |b n|) * (∑ n ∈ s, (p n) ^ 2 * |b n|) := hcs
      _ ≤ (∑' n, |b n|) * (∑' n, (p n) ^ 2 * |b n|) :=
          mul_le_mul h1 h2 (Finset.sum_nonneg (fun n _ => by positivity))
            (tsum_nonneg (fun n => abs_nonneg _))
  have hsum : Filter.Tendsto (fun s : Finset ℕ => ∑ n ∈ s, p n * |b n|)
      Filter.atTop (nhds (∑' n, p n * |b n|)) := hpb1.hasSum
  exact le_of_tendsto (hsum.pow 2) (Filter.Eventually.of_forall hfin)

/-! ## The correlation piece `corr1` and its `H^σ` membership. -/

/-- The `(m−n=k)` correlation piece: `corr1 a b k = Σ'_n a(n+k) b(n)`. -/
def corr1 (a b : ℕ → ℝ) (k : ℕ) : ℝ := ∑' n : ℕ, a (n + k) * b n

/-- `wAbs σ a` is bounded (square-summable ⇒ tends to 0 ⇒ bounded above). -/
theorem wAbs_bddAbove {σ : ℝ} {a : ℕ → ℝ} (hWa : Summable (fun m => (wAbs σ a m) ^ 2)) :
    ∃ W, ∀ m, wAbs σ a m ≤ W := by
  obtain ⟨C, hC⟩ := hWa.tendsto_cofinite_zero.bddAbove_range_of_cofinite
  refine ⟨Real.sqrt C, fun m => ?_⟩
  have hsq : (wAbs σ a m) ^ 2 ≤ C := hC ⟨m, rfl⟩
  have h0 : 0 ≤ wAbs σ a m := wAbs_nonneg σ a m
  calc wAbs σ a m = Real.sqrt ((wAbs σ a m) ^ 2) := by rw [Real.sqrt_sq h0]
    _ ≤ Real.sqrt C := Real.sqrt_le_sqrt hsq

theorem corr1_summable_abs {a b : ℕ → ℝ} (ha : Summable (fun n => |a n|))
    (hb : Summable (fun n => |b n|)) (k : ℕ) :
    Summable (fun n => |a (n + k)| * |b n|) := by
  obtain ⟨C, hC⟩ := hb.tendsto_cofinite_zero.bddAbove_range_of_cofinite
  have hak : Summable (fun n => |a (n + k)|) := (summable_nat_add_iff k).mpr ha
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hak.mul_right C)
  exact mul_le_mul_of_nonneg_left (hC ⟨n, rfl⟩) (abs_nonneg _)

theorem corr1_P_summable {σ : ℝ} {a b : ℕ → ℝ}
    (hWa : Summable (fun m => (wAbs σ a m) ^ 2)) (hb : Summable (fun n => |b n|)) (k : ℕ) :
    Summable (fun n => wAbs σ a (n + k) * |b n|) := by
  obtain ⟨W, hW⟩ := wAbs_bddAbove hWa
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (wAbs_nonneg σ a _) (abs_nonneg _)) (fun n => ?_) (hb.mul_left W)
  exact mul_le_mul_of_nonneg_right (hW (n + k)) (abs_nonneg _)

theorem corr1_Q_summable {σ : ℝ} {a b : ℕ → ℝ} (ha : Summable (fun n => |a n|))
    (hWb : Summable (fun m => (wAbs σ b m) ^ 2)) (k : ℕ) :
    Summable (fun n => |a (n + k)| * wAbs σ b n) := by
  obtain ⟨W, hW⟩ := wAbs_bddAbove hWb
  have hak : Summable (fun n => |a (n + k)|) := (summable_nat_add_iff k).mpr ha
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (wAbs_nonneg σ b _)) (fun n => ?_) (hak.mul_right W)
  exact mul_le_mul_of_nonneg_left (hW n) (abs_nonneg _)

theorem shifted_wAbs_sq_b_summable {σ : ℝ} {a b : ℕ → ℝ}
    (hWa : Summable (fun m => (wAbs σ a m) ^ 2)) (hb : Summable (fun n => |b n|))
    (k : ℕ) : Summable (fun n => (wAbs σ a (n + k)) ^ 2 * |b n|) := by
  obtain ⟨C, hC⟩ := hb.tendsto_cofinite_zero.bddAbove_range_of_cofinite
  have hWak : Summable (fun n => (wAbs σ a (n + k)) ^ 2) := (summable_nat_add_iff k).mpr hWa
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hWak.mul_right C)
  exact mul_le_mul_of_nonneg_left (hC ⟨n, rfl⟩) (by positivity)

theorem wsq_times_shifted_summable {σ : ℝ} {a b : ℕ → ℝ}
    (hWb : Summable (fun m => (wAbs σ b m) ^ 2)) (ha : Summable (fun n => |a n|))
    (k : ℕ) : Summable (fun n => (wAbs σ b n) ^ 2 * |a (n + k)|) := by
  obtain ⟨W, hW⟩ := wAbs_bddAbove hWb
  have hW2 : ∀ n, (wAbs σ b n) ^ 2 ≤ W ^ 2 :=
    fun n => pow_le_pow_left₀ (wAbs_nonneg σ b n) (hW n) 2
  have hak : Summable (fun n => |a (n + k)|) := (summable_nat_add_iff k).mpr ha
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hak.mul_left (W ^ 2))
  exact mul_le_mul_of_nonneg_right (hW2 n) (abs_nonneg _)

/-- Per-mode weight-split bound for `corr1` (using `k = Nat.dist (n+k) n`). -/
theorem corr1_halfWeight_le {σ : ℝ} (hσ : 0 ≤ σ) {a b : ℕ → ℝ}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|))
    (hWa : Summable (fun m => (wAbs σ a m) ^ 2)) (hWb : Summable (fun m => (wAbs σ b m) ^ 2)) :
    ∃ Cσ : ℝ, 0 < Cσ ∧ ∀ k : ℕ,
      (1 + lam k) ^ (σ / 2) * |corr1 a b k| ≤
        Cσ * ((∑' n, wAbs σ a (n + k) * |b n|) + (∑' n, |a (n + k)| * wAbs σ b n)) := by
  obtain ⟨Cσ, hCσ, hbound⟩ := cosWeight_le_add hσ
  refine ⟨Cσ, hCσ, fun k => ?_⟩
  have hWk : 0 ≤ (1 + lam k) ^ (σ / 2) := Real.rpow_nonneg (one_add_lam_pos k).le _
  have htri : |corr1 a b k| ≤ ∑' n, |a (n + k)| * |b n| := by
    unfold corr1
    have hsummable : Summable (fun n => ‖a (n + k) * b n‖) := by
      simpa [Real.norm_eq_abs, abs_mul] using corr1_summable_abs ha hb k
    calc |∑' n, a (n + k) * b n| = ‖∑' n, a (n + k) * b n‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' n, ‖a (n + k) * b n‖ := norm_tsum_le_tsum_norm hsummable
      _ = ∑' n, |a (n + k)| * |b n| := by
          refine tsum_congr (fun n => ?_); rw [Real.norm_eq_abs, abs_mul]
  have hPsum : Summable (fun n => wAbs σ a (n + k) * |b n|) := corr1_P_summable hWa hb k
  have hQsum : Summable (fun n => |a (n + k)| * wAbs σ b n) := corr1_Q_summable ha hWb k
  have habsum : Summable (fun n => |a (n + k)| * |b n|) := corr1_summable_abs ha hb k
  calc (1 + lam k) ^ (σ / 2) * |corr1 a b k|
      ≤ (1 + lam k) ^ (σ / 2) * ∑' n, |a (n + k)| * |b n| :=
        mul_le_mul_of_nonneg_left htri hWk
    _ = ∑' n, (1 + lam k) ^ (σ / 2) * (|a (n + k)| * |b n|) := by rw [tsum_mul_left]
    _ ≤ ∑' n, Cσ * (wAbs σ a (n + k) * |b n| + |a (n + k)| * wAbs σ b n) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (habsum.mul_left _)
          ((hPsum.add hQsum).mul_left _)
        have hk : (k : ℕ) = Nat.dist (n + k) n := by unfold Nat.dist; omega
        have hw := hbound (n + k) n k (Or.inr hk)
        have hab0 : 0 ≤ |a (n + k)| * |b n| := by positivity
        calc (1 + lam k) ^ (σ / 2) * (|a (n + k)| * |b n|)
            ≤ (Cσ * ((1 + lam (n + k)) ^ (σ / 2) + (1 + lam n) ^ (σ / 2)))
                * (|a (n + k)| * |b n|) := mul_le_mul_of_nonneg_right hw hab0
          _ = Cσ * (wAbs σ a (n + k) * |b n| + |a (n + k)| * wAbs σ b n) := by
              unfold wAbs; ring
    _ = Cσ * ((∑' n, wAbs σ a (n + k) * |b n|) + (∑' n, |a (n + k)| * wAbs σ b n)) := by
        rw [tsum_mul_left, hPsum.tsum_add hQsum]

set_option maxHeartbeats 1600000 in
/-- **`H^σ` membership of the `corr1` correlation piece** (`σ > 1/2`). -/
theorem memHSigma_corr1 {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (corr1 a b) := by
  have hσ0 : 0 ≤ σ := by linarith
  have ha1 : Summable (fun n => |a n|) := hSigma_subset_l1_of_gt_half hσ ha
  have hb1 : Summable (fun n => |b n|) := hSigma_subset_l1_of_gt_half hσ hb
  have hWa : Summable (fun m => (wAbs σ a m) ^ 2) := summable_wAbs_sq ha
  have hWb : Summable (fun n => (wAbs σ b n) ^ 2) := summable_wAbs_sq hb
  have hGa : Summable (fun p : ℕ × ℕ => (wAbs σ a p.1) ^ 2 * |b p.2|) :=
    Summable.mul_of_nonneg hWa hb1 (fun m => sq_nonneg _) (fun n => abs_nonneg _)
  have hHb : Summable (fun p : ℕ × ℕ => |a p.1| * (wAbs σ b p.2) ^ 2) :=
    Summable.mul_of_nonneg ha1 hWb (fun m => abs_nonneg _) (fun n => sq_nonneg _)
  obtain ⟨Cσ, hCσ, hbound⟩ := corr1_halfWeight_le hσ0 ha1 hb1 hWa hWb
  set NB : ℝ := ∑' n, |b n| with hNB
  set NA : ℝ := ∑' n, |a n| with hNA
  set GA : ℝ := ∑' p : ℕ × ℕ, (wAbs σ a p.1) ^ 2 * |b p.2| with hGAdef
  set HB : ℝ := ∑' p : ℕ × ℕ, |a p.1| * (wAbs σ b p.2) ^ 2 with hHBdef
  have henergy0 : ∀ k, 0 ≤ (1 + lam k) ^ σ * (corr1 a b k) ^ 2 := by
    intro k; have := Real.rpow_nonneg (one_add_lam_pos k).le σ; positivity
  refine summable_of_sum_le
    (c := Cσ ^ 2 * (2 * (NB * GA) + 2 * (NA * HB))) henergy0 (fun u => ?_)
  have hpermode : ∀ k ∈ u,
      (1 + lam k) ^ σ * (corr1 a b k) ^ 2 ≤
        Cσ ^ 2 * (2 * (∑' n, wAbs σ a (n + k) * |b n|) ^ 2
                  + 2 * (∑' n, |a (n + k)| * wAbs σ b n) ^ 2) := by
    intro k _
    have heq : (1 + lam k) ^ σ * (corr1 a b k) ^ 2
        = ((1 + lam k) ^ (σ / 2) * |corr1 a b k|) ^ 2 := by
      rw [mul_pow, sq_abs, ← Real.rpow_natCast ((1 + lam k) ^ (σ / 2)) 2,
          ← Real.rpow_mul (one_add_lam_pos k).le]
      congr 2; push_cast; ring
    set P := ∑' n, wAbs σ a (n + k) * |b n| with hP
    set Q := ∑' n, |a (n + k)| * wAbs σ b n with hQ
    have hPQ0 : (1 + lam k) ^ (σ / 2) * |corr1 a b k| ≤ Cσ * (P + Q) := hbound k
    have hlhs0 : 0 ≤ (1 + lam k) ^ (σ / 2) * |corr1 a b k| := by
      have := Real.rpow_nonneg (one_add_lam_pos k).le (σ / 2); positivity
    rw [heq]
    calc ((1 + lam k) ^ (σ / 2) * |corr1 a b k|) ^ 2
        ≤ (Cσ * (P + Q)) ^ 2 := pow_le_pow_left₀ hlhs0 hPQ0 2
      _ = Cσ ^ 2 * (P + Q) ^ 2 := by ring
      _ ≤ Cσ ^ 2 * (2 * P ^ 2 + 2 * Q ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [sq_nonneg (P - Q)]
  calc ∑ k ∈ u, (1 + lam k) ^ σ * (corr1 a b k) ^ 2
      ≤ ∑ k ∈ u, Cσ ^ 2 * (2 * (∑' n, wAbs σ a (n + k) * |b n|) ^ 2
            + 2 * (∑' n, |a (n + k)| * wAbs σ b n) ^ 2) := Finset.sum_le_sum hpermode
    _ = Cσ ^ 2 * (2 * ∑ k ∈ u, (∑' n, wAbs σ a (n + k) * |b n|) ^ 2
          + 2 * ∑ k ∈ u, (∑' n, |a (n + k)| * wAbs σ b n) ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Cσ ^ 2 * (2 * (NB * GA) + 2 * (NA * HB)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hPpiece : ∑ k ∈ u, (∑' n, wAbs σ a (n + k) * |b n|) ^ 2 ≤ NB * GA := by
          calc ∑ k ∈ u, (∑' n, wAbs σ a (n + k) * |b n|) ^ 2
              ≤ ∑ k ∈ u, NB * (∑' n, (wAbs σ a (n + k)) ^ 2 * |b n|) := by
                refine Finset.sum_le_sum (fun k _ => ?_)
                exact tsum_cs_weighted (fun n => wAbs σ a (n + k)) b hb1
                  (shifted_wAbs_sq_b_summable hWa hb1 k) (corr1_P_summable hWa hb1 k)
            _ = NB * ∑ k ∈ u, ∑' n, (wAbs σ a (n + k)) ^ 2 * |b n| := by rw [Finset.mul_sum]
            _ ≤ NB * GA := by
                apply mul_le_mul_of_nonneg_left _ (tsum_nonneg (fun n => abs_nonneg _))
                exact corrShift_sum_le_tsum (g := fun p => (wAbs σ a p.1) ^ 2 * |b p.2|)
                  (fun p => by positivity) hGa u
        have hQpiece : ∑ k ∈ u, (∑' n, |a (n + k)| * wAbs σ b n) ^ 2 ≤ NA * HB := by
          calc ∑ k ∈ u, (∑' n, |a (n + k)| * wAbs σ b n) ^ 2
              ≤ ∑ k ∈ u, NA * (∑' n, (wAbs σ b n) ^ 2 * |a (n + k)|) := by
                refine Finset.sum_le_sum (fun k _ => ?_)
                have hcomm : (∑' n, |a (n + k)| * wAbs σ b n)
                    = ∑' n, wAbs σ b n * |a (n + k)| := tsum_congr (fun n => by ring)
                rw [hcomm]
                have hQs : Summable (fun n => wAbs σ b n * |a (n + k)|) :=
                  (corr1_Q_summable (a := a) (b := b) ha1 hWb k).congr (fun n => by ring)
                have hcs := tsum_cs_weighted (fun n => wAbs σ b n) (fun n => a (n + k))
                  ((summable_nat_add_iff k).mpr ha1)
                  (wsq_times_shifted_summable hWb ha1 k) hQs
                have hshift_le : (∑' n, |a (n + k)|) ≤ NA := by
                  rw [hNA]
                  exact ((summable_nat_add_iff k).mpr ha1).tsum_le_tsum_of_inj (· + k)
                    (add_left_injective k) (fun _ _ => abs_nonneg _) (fun n => le_refl _) ha1
                have hWbsq0 : 0 ≤ ∑' n, (wAbs σ b n) ^ 2 * |a (n + k)| :=
                  tsum_nonneg (fun n => by positivity)
                calc (∑' n, wAbs σ b n * |a (n + k)|) ^ 2
                    ≤ (∑' n, |a (n + k)|) * (∑' n, (wAbs σ b n) ^ 2 * |a (n + k)|) := hcs
                  _ ≤ NA * (∑' n, (wAbs σ b n) ^ 2 * |a (n + k)|) :=
                      mul_le_mul_of_nonneg_right hshift_le hWbsq0
            _ = NA * ∑ k ∈ u, ∑' n, (wAbs σ b n) ^ 2 * |a (n + k)| := by rw [Finset.mul_sum]
            _ ≤ NA * HB := by
                apply mul_le_mul_of_nonneg_left _ (tsum_nonneg (fun n => abs_nonneg _))
                have hHb' : Summable (fun p : ℕ × ℕ => (wAbs σ b p.2) ^ 2 * |a p.1|) :=
                  hHb.congr (fun p => by ring)
                exact (corrShift_sum_le_tsum (g := fun p => (wAbs σ b p.2) ^ 2 * |a p.1|)
                  (fun p => by positivity) hHb' u).trans
                  (le_of_eq (by rw [hHBdef]; exact tsum_congr (fun p => by ring)))
        linarith [hPpiece, hQpiece]

/-! ## The difference convolution and its `H^σ` membership. -/

/-- **Difference convolution** `(a ⊗ b)_k = Σ_{|m−n|=k} aₘbₙ`, realized as the sum of
the two injective correlation leaves `corr1 a b + corr1 b a`.  (For `k = 0` the
diagonal is counted in both leaves; this over-count is harmless for the
`H^σ`-membership bound.) -/
def diffConv (a b : ℕ → ℝ) (k : ℕ) : ℝ := corr1 a b k + corr1 b a k

/-- **WALL-A difference-convolution `H^σ` membership** (`σ > 1/2`).  The genuine
2-cover completion: each leaf `corr1` is in `H^σ` by `memHSigma_corr1`, and `H^σ` is
closed under addition. -/
theorem memHSigma_diffConv_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (diffConv a b) :=
  memHSigma_add (memHSigma_corr1 hσ ha hb) (memHSigma_corr1 hσ hb ha)

/-! ## The cosine product coefficient `cosProd` and the `H^σ` Banach algebra. -/

/-- The **cosine product coefficient** of two sequences,
`(a ⊛ b)_k = ½((a ⋆ b)_k + (a ⊗ b)_k)`, from
`cos(mπx)cos(nπx) = ½(cos((m+n)πx) + cos(|m−n|πx))`. -/
def cosProd (a b : ℕ → ℝ) (k : ℕ) : ℝ := (1 / 2 : ℝ) * (addConv a b k + diffConv a b k)

/-- **`H^σ` is a Banach algebra under `cosProd`** (`σ > 1/2`): the cosine product of
two `H^σ` cosine-coefficient sequences is again `H^σ`. -/
theorem memHSigma_cosProd_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (cosProd a b) :=
  memHSigma_smul (1 / 2)
    (memHSigma_add (memHSigma_addConv_of_gt_half hσ ha hb)
      (memHSigma_diffConv_of_gt_half hσ ha hb))

/-- **Triple cosine product** stays in `H^σ` (`σ > 1/2`). -/
theorem memHSigma_cosProd3_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b c : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) (hc : MemHSigma σ c) :
    MemHSigma σ (cosProd a (cosProd b c)) :=
  memHSigma_cosProd_of_gt_half hσ ha (memHSigma_cosProd_of_gt_half hσ hb hc)

/-! ## Integer-power composition (`u^{m+1}` via product iteration). -/

/-- The iterated cosine product `cosPow a m` represents `u^{m+1}` (so `cosPow a 0 = u`,
`cosPow a 1 = u^2`, …): a clean instance of composition with the analytic symbol
`t ↦ t^{m+1}` realized purely by the `H^σ` Banach algebra. -/
def cosPow (a : ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => a
  | (m + 1) => cosProd a (cosPow a m)

/-- **Integer-power composition `H^σ` membership** (`σ > 1/2`): every positive integer
power `u^{m+1}` (`= cosPow u m`) of an `H^σ` cosine-coefficient sequence is `H^σ`.
This discharges the `u^m` factor of the chemotaxis flux for integer `m ≥ 1`. -/
theorem memHSigma_cosPow_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a : ℕ → ℝ}
    (ha : MemHSigma σ a) : ∀ m : ℕ, MemHSigma σ (cosPow a m)
  | 0 => ha
  | (m + 1) => memHSigma_cosProd_of_gt_half hσ ha (memHSigma_cosPow_of_gt_half hσ ha m)

/-! ## The chemotaxis flux target. -/

/-- **THE TARGET — chemotaxis flux `H^σ` regularity (algebra form).**  Let `σ > 1/2`.
Given the cosine-coefficient sequences of the three flux factors —
`uPow` (`= u^m` for `u ∈ H^σ ∩ [c,M]`), `invDen` (`= (1+v)^{−β}`, `v ∈ H^{σ+2}`),
and `vx` (`= v_x ∈ H^{σ+1} ⊂ H^σ`) — each in `H^σ`, the chemotaxis flux coefficient
sequence `Q = u^m (1+v)^{−β} v_x` (assembled by the cosine product) lies in `H^σ`.

This is `chemotaxisFlux_memHSigma`: the `H^σ` Banach-algebra closure
(`memHSigma_cosProd3_of_gt_half`) applied to the three flux factors.  The factors'
own `H^σ`-membership is supplied by the resolver gain
`resolver_memHSigmaPlus2_of_memHSigma` (for `v`), the `H^{σ+1} ⊂ H^σ` scale embedding
(for `v_x`), and the composition lemmas (for `u^m` and `(1+v)^{−β}`). -/
theorem chemotaxisFlux_memHSigma {σ : ℝ} (hσ : 1 / 2 < σ) {uPow invDen vx : ℕ → ℝ}
    (hu : MemHSigma σ uPow) (hv : MemHSigma σ invDen) (hvx : MemHSigma σ vx) :
    MemHSigma σ (cosProd uPow (cosProd invDen vx)) :=
  memHSigma_cosProd3_of_gt_half hσ hu hv hvx

/-- **Chemotaxis flux `H^σ` (integer power form).**  For integer `m ≥ 1`, taking
`uPow = u^m = cosPow u (m-1)`, the flux `u^m (1+v)^{−β} v_x` lies in `H^σ` directly
from `u, (1+v)^{−β}, v_x ∈ H^σ`.  Stated with `cosPow u m` (`= u^{m+1}`) to avoid the
`m-1` shift. -/
theorem chemotaxisFlux_memHSigma_intPow {σ : ℝ} (hσ : 1 / 2 < σ) {u invDen vx : ℕ → ℝ}
    (hu : MemHSigma σ u) (hv : MemHSigma σ invDen) (hvx : MemHSigma σ vx) (m : ℕ) :
    MemHSigma σ (cosProd (cosPow u m) (cosProd invDen vx)) :=
  memHSigma_cosProd3_of_gt_half hσ (memHSigma_cosPow_of_gt_half hσ hu m) hv hvx

/-! ## Step-1 seed: the flux is `L² = H^0` from bounded data (no algebra). -/

/-- **Step-1 flux `L²` seed.**  If the cosine-product flux coefficient sequence is
square-summable (the `H^0 = ℓ²` datum from `u, v ∈ L^∞`, `v_x ∈ L²`), then it lies in
`H^0`.  Elementary: `H^0` membership is exactly `ℓ²` square-summability. -/
theorem chemotaxisFlux_L2_of_bounded {Q : ℕ → ℝ} (hQ : Summable (fun k => (Q k) ^ 2)) :
    MemHSigma 0 Q := (memHSigma_zero Q).mpr hQ

#print axioms memHSigma_corr1
#print axioms memHSigma_diffConv_of_gt_half
#print axioms memHSigma_cosProd_of_gt_half
#print axioms memHSigma_cosProd3_of_gt_half
#print axioms memHSigma_cosPow_of_gt_half
#print axioms chemotaxisFlux_memHSigma
#print axioms chemotaxisFlux_memHSigma_intPow
#print axioms chemotaxisFlux_L2_of_bounded

end ShenWork.Paper2.IntervalWienerAlgebra
