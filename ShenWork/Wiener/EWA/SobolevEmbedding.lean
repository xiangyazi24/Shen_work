import ShenWork.Wiener.EWA.MemHSigmaSigmaAlgebra

/-!
  # The Sobolev embedding `H^s ↪ A^σ` (weighted-`ℓ²` into weighted-`ℓ¹`).

  This file supplies the shared bridge for the `A³` bootstrap seed and the
  general-data composition: a function whose `H^s` cosine energy
  `Σ_k (1+λ_k)^s (a_k)²` converges lies in the weighted-`ℓ¹` Wiener algebra
  `A^σ = MemWNorm σ` (the `Σ_k (1+λ_k)^{σ/2}|a_k|` algebra) whenever
  `σ + 1/2 < s`.

  The proof is pure AM–GM: split each weighted-`ℓ¹` term as a product
  `wAbs σ a k = u k · v k` with `u k = (1+λ_k)^{s/2}|a_k|` (whose square is the
  `H^s` energy term) and `v k = (1+λ_k)^{(σ−s)/2}` (whose square is the
  convergent `p`-series tail `(1+λ_k)^{−(s−σ)}` with exponent `s−σ > 1/2`).
  AM–GM `uv ≤ (u²+v²)/2` then dominates the `ℓ¹` term by a summable series.

  Contents:
  * `MemHSob`                          — the `ℓ²`-weighted Sobolev membership.
  * `summable_one_add_lam_rpow_neg`    — the convergent weight `p`-series
      `Σ_k (1+λ_k)^{−p}` for `p > 1/2`.
  * `memWNorm_of_memHSob`              — the embedding `H^s ↪ A^σ`.
-/

noncomputable section

open scoped BigOperators
open ShenWork.Paper2.HSigmaScale ShenWork.Paper2.IntervalWienerAlgebra

namespace ShenWork.Wiener.EWA

/-- The `ℓ²`-weighted (fractional cosine `H^s`) Sobolev membership: the squared
energy series `Σ_k (1+λ_k)^s (a_k)²` converges. -/
def MemHSob (s : ℝ) (a : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => (1 + lam k) ^ s * (a k) ^ 2)

/-- The weight `p`-series `Σ_k (1+λ_k)^{−p}` converges for `p > 1/2`, because
`1 + λ_k ≥ λ_k = (kπ)²`, so the term is `≤ π^{−2p} k^{−2p}` and `2p > 1`. -/
theorem summable_one_add_lam_rpow_neg {p : ℝ} (hp : (1 / 2 : ℝ) < p) :
    Summable (fun k : ℕ => (1 + lam k) ^ (-p)) := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- It suffices to prove summability after dropping the `k = 0` term.
  rw [← summable_nat_add_iff 1]
  -- The comparison series `C · ((n+1)^{2p})⁻¹`, summable since `2p > 1`.
  have hcmp :
      Summable (fun n : ℕ => Real.pi ^ (-(2 * p)) * (((n : ℝ) + 1) ^ (2 * p))⁻¹) := by
    refine Summable.mul_left _ ?_
    have hshift : Summable (fun k : ℕ => ((k : ℝ) ^ (2 * p))⁻¹) := by
      rw [Real.summable_nat_rpow_inv]; linarith
    have := (summable_nat_add_iff 1).2 hshift
    refine this.congr (fun n => ?_)
    rw [Nat.cast_add, Nat.cast_one]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hcmp
  · exact Real.rpow_nonneg (one_add_lam_pos _).le _
  · -- Term bound: `(1+λ_{n+1})^{−p} ≤ π^{−2p} · ((n+1)^{2p})⁻¹`.
    set k := n + 1 with hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.succ_pos n
    -- `λ_k = (kπ)² = k² π²`, and `1 + λ_k ≥ λ_k > 0`.
    have hlam : lam k = ((k : ℝ) * Real.pi) ^ 2 := rfl
    have hlampos : (0 : ℝ) < lam k := by
      rw [hlam]; positivity
    -- `(1+λ_k)^{−p} ≤ (λ_k)^{−p}` since base `1+λ_k ≥ λ_k > 0` and exponent `−p < 0`.
    have hbase : lam k ≤ 1 + lam k := by linarith
    have hstep1 : (1 + lam k) ^ (-p) ≤ (lam k) ^ (-p) := by
      apply Real.rpow_le_rpow_of_nonpos hlampos hbase
      linarith
    -- `(λ_k)^{−p} = ((kπ)²)^{−p} = π^{−2p}·(k^{2p})⁻¹`.
    have heq : (lam k) ^ (-p) = Real.pi ^ (-(2 * p)) * (((k : ℝ)) ^ (2 * p))⁻¹ := by
      rw [hlam, ← Real.rpow_natCast ((k : ℝ) * Real.pi) 2,
        ← Real.rpow_mul (by positivity), Real.mul_rpow hkpos.le hπ.le]
      rw [show ((2 : ℕ) : ℝ) * (-p) = -(2 * p) by push_cast; ring]
      rw [Real.rpow_neg hkpos.le]
      ring
    calc (1 + lam k) ^ (-p) ≤ (lam k) ^ (-p) := hstep1
      _ = Real.pi ^ (-(2 * p)) * (((k : ℝ)) ^ (2 * p))⁻¹ := heq
      _ = Real.pi ^ (-(2 * p)) * (((n : ℝ) + 1) ^ (2 * p))⁻¹ := by
          rw [hk]; push_cast; ring_nf

/-- The Sobolev embedding `H^s ↪ A^σ`: if the `ℓ²`-weighted `H^s` energy of `a`
converges and `σ + 1/2 < s`, then `a` lies in the weighted-`ℓ¹`
Wiener algebra `A^σ = MemWNorm σ`.  Proof by AM–GM on the split
`(1+λ_k)^{σ/2}|a_k| = u_k v_k`, `u_k = (1+λ_k)^{s/2}|a_k|`,
`v_k = (1+λ_k)^{(σ−s)/2}`, with `u²` the `H^s` energy and `v²` a convergent
weight `p`-series of exponent `s−σ > 1/2`. -/
theorem memWNorm_of_memHSob {σ s : ℝ} (hs : σ + (1 / 2 : ℝ) < s)
    {a : ℕ → ℝ} (ha : MemHSob s a) : MemWNorm σ a := by
  classical
  set u : ℕ → ℝ := fun k => (1 + lam k) ^ (s / 2) * |a k| with hu
  set v : ℕ → ℝ := fun k => (1 + lam k) ^ ((σ - s) / 2) with hv
  -- `u² = (1+λ)^s (a)²` is the `H^s` energy term, hence summable from `ha`.
  have husq : Summable (fun k => (u k) ^ 2) := by
    refine ha.congr (fun k => ?_)
    have hb : (0 : ℝ) < 1 + lam k := one_add_lam_pos k
    rw [hu]
    rw [mul_pow, ← Real.rpow_natCast ((1 + lam k) ^ (s / 2)) 2,
      ← Real.rpow_mul hb.le, sq_abs]
    rw [show (s / 2) * ((2 : ℕ) : ℝ) = s by push_cast; ring]
  -- `v² = (1+λ)^{σ−s} = (1+λ)^{−(s−σ)}` is a convergent weight `p`-series.
  have hvsq : Summable (fun k => (v k) ^ 2) := by
    have hps : (1 / 2 : ℝ) < s - σ := by linarith
    have hsum := summable_one_add_lam_rpow_neg hps
    refine hsum.congr (fun k => ?_)
    have hb : (0 : ℝ) < 1 + lam k := one_add_lam_pos k
    rw [hv, ← Real.rpow_natCast ((1 + lam k) ^ ((σ - s) / 2)) 2, ← Real.rpow_mul hb.le]
    rw [show ((σ - s) / 2) * ((2 : ℕ) : ℝ) = -(s - σ) by push_cast; ring]
  -- AM–GM dominating series `(u² + v²)/2` is summable.
  have hdom : Summable (fun k => ((u k) ^ 2 + (v k) ^ 2) / 2) :=
    (husq.add hvsq).div_const 2
  refine Summable.of_nonneg_of_le (fun k => wAbs_nonneg σ a k) (fun k => ?_) hdom
  -- `wAbs σ a k = u k * v k`.
  have hb : (0 : ℝ) < 1 + lam k := one_add_lam_pos k
  have hsplit : wAbs σ a k = u k * v k := by
    rw [hu, hv]
    unfold wAbs
    rw [mul_right_comm, ← Real.rpow_add hb]
    rw [show s / 2 + (σ - s) / 2 = σ / 2 by ring]
  rw [hsplit]
  -- AM–GM: `u v ≤ (u² + v²)/2`.
  have hamgm := two_mul_le_add_sq (u k) (v k)
  linarith

end ShenWork.Wiener.EWA
