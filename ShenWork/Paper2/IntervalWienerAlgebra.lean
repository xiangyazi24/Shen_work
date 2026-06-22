import ShenWork.Paper2.IntervalHSigmaScale
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
  # Wiener-algebra route to the `H^σ` product theory (σ > 1/2), Paper 2 (WALL-A).

  For `σ > 1/2` the cosine-Sobolev space embeds into `ℓ¹` (Wiener algebra), so
  products close by the elementary coefficient-convolution + Peetre-weight + Young
  route, with NO paraproduct.  This file builds that abstract sequence theory on top
  of `ShenWork.Paper2.HSigmaScale.MemHSigma`.

  Pipeline:
  * `cosWeight_le_add`           — Peetre / triangle weight split.
  * `hSigma_subset_l1_of_gt_half`— `σ>1/2 ⟹ H^σ ⊂ ℓ¹` (Cauchy–Schwarz).
-/

noncomputable section

open ShenWork.Paper2.HSigmaScale

namespace ShenWork.Paper2.IntervalWienerAlgebra

/-- `√(1+λ_k)`, the half-weight at mode `k`. -/
def wHalf (k : ℕ) : ℝ := Real.sqrt (1 + lam k)

theorem wHalf_nonneg (k : ℕ) : 0 ≤ wHalf k := Real.sqrt_nonneg _

theorem wHalf_pos (k : ℕ) : 0 < wHalf k :=
  Real.sqrt_pos.mpr (one_add_lam_pos k)

/-- `lam k = ((k:ℝ)*π)^2`. -/
theorem lam_eq (k : ℕ) : lam k = ((k : ℝ) * Real.pi) ^ 2 := rfl

/-- `lam` is monotone in the mode index. -/
theorem lam_mono {j k : ℕ} (h : j ≤ k) : lam j ≤ lam k := by
  rw [lam_eq, lam_eq]
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hjk : (j : ℝ) * Real.pi ≤ (k : ℝ) * Real.pi := by
    have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    nlinarith [hpi, this]
  have hjpos : (0 : ℝ) ≤ (j : ℝ) * Real.pi := by positivity
  nlinarith [hjk, hjpos]

/-- `wHalf` is monotone in the mode index. -/
theorem wHalf_mono {j k : ℕ} (h : j ≤ k) : wHalf j ≤ wHalf k := by
  unfold wHalf
  exact Real.sqrt_le_sqrt (by linarith [lam_mono h])

/-- **√-subadditivity of the Peetre weight.**
`√(1 + λ_{m+n}) ≤ √(1 + λ_m) + √(1 + λ_n)`. -/
theorem wHalf_add_le (m n : ℕ) : wHalf (m + n) ≤ wHalf m + wHalf n := by
  set a : ℝ := (m : ℝ) * Real.pi with ha
  set b : ℝ := (n : ℝ) * Real.pi with hb
  have ha0 : 0 ≤ a := by have := Real.pi_pos; positivity
  have hb0 : 0 ≤ b := by have := Real.pi_pos; positivity
  have hlam_mn : lam (m + n) = (a + b) ^ 2 := by
    rw [lam_eq]; push_cast; ring
  have hlam_m : lam m = a ^ 2 := by rw [lam_eq]
  have hlam_n : lam n = b ^ 2 := by rw [lam_eq]
  -- nonneg sqrt factors
  have hA0 : 0 ≤ Real.sqrt (1 + a ^ 2) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ Real.sqrt (1 + b ^ 2) := Real.sqrt_nonneg _
  have hsqA : Real.sqrt (1 + a ^ 2) ^ 2 = 1 + a ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hsqB : Real.sqrt (1 + b ^ 2) ^ 2 = 1 + b ^ 2 :=
    Real.sq_sqrt (by positivity)
  -- reduce target to squared inequality
  rw [wHalf, wHalf, wHalf, hlam_mn, hlam_m, hlam_n]
  have hRHS0 : 0 ≤ Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) := by positivity
  -- cross term: AB = √((1+a²)(1+b²)) ≥ ab
  have hcross : a * b ≤ Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    have hab2 : (a * b) ^ 2 ≤ (1 + a ^ 2) * (1 + b ^ 2) := by nlinarith [ha0, hb0]
    calc a * b = Real.sqrt ((a * b) ^ 2) := by rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2)) := Real.sqrt_le_sqrt hab2
  -- (A+B)² ≥ 1+(a+b)²
  have hsqRHS : (Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2)) ^ 2
      = (1 + a ^ 2) + (1 + b ^ 2)
        + 2 * (Real.sqrt (1 + a ^ 2) * Real.sqrt (1 + b ^ 2)) := by
    rw [add_sq, hsqA, hsqB]; ring
  have hle : 1 + (a + b) ^ 2
      ≤ (Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2)) ^ 2 := by
    rw [hsqRHS]; nlinarith [hcross]
  calc Real.sqrt (1 + (a + b) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) := Real.sqrt_sq hRHS0

/-- `(1+λ_k)^(σ/2) = (wHalf k)^σ`. -/
theorem rpow_halfWeight (σ : ℝ) (k : ℕ) :
    (1 + lam k) ^ (σ / 2) = (wHalf k) ^ σ := by
  unfold wHalf
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (one_add_lam_pos k).le]
  congr 1
  ring

/-- For `σ ≥ 0`, `(max X Y) ^ σ ≤ X ^ σ + Y ^ σ` (nonneg bases). -/
theorem max_rpow_le_add {X Y σ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hσ : 0 ≤ σ) :
    (max X Y) ^ σ ≤ X ^ σ + Y ^ σ := by
  rcases le_total X Y with h | h
  · rw [max_eq_right h]
    have : Y ^ σ ≤ X ^ σ + Y ^ σ := by
      have := Real.rpow_nonneg hX σ; linarith
    exact this
  · rw [max_eq_left h]
    have : X ^ σ ≤ X ^ σ + Y ^ σ := by
      have := Real.rpow_nonneg hY σ; linarith
    exact this

/-- **Lemma 1 (Peetre / triangle weight split).**
For `σ ≥ 0` there is a constant `Cσ = 2^σ > 0` such that whenever the output mode
`k` equals either the additive index `m+n` or the difference index `Nat.dist m n`,
the half-weight at `k` is bounded by `Cσ` times the sum of half-weights at `m,n`. -/
theorem cosWeight_le_add {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ Cσ : ℝ, 0 < Cσ ∧ ∀ m n k : ℕ,
      (k = m + n ∨ k = Nat.dist m n) →
      (1 + lam k) ^ (σ / 2)
        ≤ Cσ * ((1 + lam m) ^ (σ / 2) + (1 + lam n) ^ (σ / 2)) := by
  refine ⟨(2 : ℝ) ^ σ, Real.rpow_pos_of_pos (by norm_num) σ, ?_⟩
  intro m n k hk
  -- k ≤ m + n in both cases
  have hkmn : k ≤ m + n := by
    rcases hk with h | h
    · exact h.le
    · rw [h]; unfold Nat.dist; omega
  -- move to wHalf
  rw [rpow_halfWeight, rpow_halfWeight, rpow_halfWeight]
  have hXY : wHalf k ≤ wHalf m + wHalf n :=
    le_trans (wHalf_mono hkmn) (wHalf_add_le m n)
  have hX0 : 0 ≤ wHalf m := wHalf_nonneg m
  have hY0 : 0 ≤ wHalf n := wHalf_nonneg n
  have hk0 : 0 ≤ wHalf k := wHalf_nonneg k
  -- (wHalf k)^σ ≤ (wHalf m + wHalf n)^σ
  have hmono : (wHalf k) ^ σ ≤ (wHalf m + wHalf n) ^ σ :=
    Real.rpow_le_rpow hk0 hXY hσ
  -- (X+Y)^σ ≤ (2 * max X Y)^σ = 2^σ * (max X Y)^σ ≤ 2^σ * (X^σ + Y^σ)
  have hsum_le : wHalf m + wHalf n ≤ 2 * max (wHalf m) (wHalf n) := by
    rcases le_total (wHalf m) (wHalf n) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hmax0 : 0 ≤ max (wHalf m) (wHalf n) := le_max_of_le_left hX0
  have hstep1 : (wHalf m + wHalf n) ^ σ ≤ (2 * max (wHalf m) (wHalf n)) ^ σ :=
    Real.rpow_le_rpow (by positivity) hsum_le hσ
  have hstep2 : (2 * max (wHalf m) (wHalf n)) ^ σ
      = (2 : ℝ) ^ σ * (max (wHalf m) (wHalf n)) ^ σ := by
    rw [Real.mul_rpow (by norm_num) hmax0]
  have hstep3 : (max (wHalf m) (wHalf n)) ^ σ ≤ (wHalf m) ^ σ + (wHalf n) ^ σ :=
    max_rpow_le_add hX0 hY0 hσ
  calc (wHalf k) ^ σ ≤ (wHalf m + wHalf n) ^ σ := hmono
    _ ≤ (2 * max (wHalf m) (wHalf n)) ^ σ := hstep1
    _ = (2 : ℝ) ^ σ * (max (wHalf m) (wHalf n)) ^ σ := hstep2
    _ ≤ (2 : ℝ) ^ σ * ((wHalf m) ^ σ + (wHalf n) ^ σ) := by
        apply mul_le_mul_of_nonneg_left hstep3
        exact Real.rpow_nonneg (by norm_num) σ

/-! ## Lemma 2 : `σ > 1/2 ⟹ H^σ ⊂ ℓ¹` (Wiener-algebra embedding). -/

/-- The negative-power weight `(1+λ_n)^{-σ}` is summable iff captured by the
`p`-series with `p = 2σ`.  For `σ > 1/2` (so `2σ > 1`) it converges. -/
theorem summable_negPow_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => (1 + lam n) ^ (-σ)) := by
  have h2σ : (1 : ℝ) < 2 * σ := by linarith
  -- comparison series: π^{-2σ} · (n^{2σ})⁻¹, summable for the shifted index.
  have hps : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * σ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr h2σ
  -- shift by 1 so the comparison is valid (n ≥ 1).
  rw [← summable_nat_add_iff 1]
  set C : ℝ := (Real.pi ^ (2 * σ))⁻¹ with hC
  have hCpos : 0 < C := by
    rw [hC]; positivity
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (((summable_nat_add_iff 1).mpr hps).mul_left C)
  · exact Real.rpow_nonneg (one_add_lam_pos (n + 1)).le _
  · -- (1+λ_{n+1})^{-σ} ≤ C · ((n+1)^{2σ})⁻¹
    have hπ : 0 < Real.pi := Real.pi_pos
    have hnp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * Real.pi := by positivity
    have h1l : 0 < 1 + lam (n + 1) := one_add_lam_pos (n + 1)
    -- (n+1)^{2σ} · π^{2σ} = ((n+1)π)^{2σ} ≤ (1+λ)^{σ}, then invert.
    have hkey : (((n + 1 : ℕ) : ℝ) * Real.pi) ^ (2 * σ) ≤ (1 + lam (n + 1)) ^ σ := by
      have hlb : (((n + 1 : ℕ) : ℝ) * Real.pi) ^ 2 ≤ 1 + lam (n + 1) := by
        rw [lam_eq]; push_cast; nlinarith [hnp]
      have h2σpos : (0 : ℝ) < 2 * σ := by linarith
      calc (((n + 1 : ℕ) : ℝ) * Real.pi) ^ (2 * σ)
          = ((((n + 1 : ℕ) : ℝ) * Real.pi) ^ 2) ^ σ := by
            rw [← Real.rpow_natCast (((n + 1 : ℕ) : ℝ) * Real.pi) 2,
                ← Real.rpow_mul hnp.le]
            norm_num
        _ ≤ (1 + lam (n + 1)) ^ σ :=
            Real.rpow_le_rpow (by positivity) hlb (by linarith)
    have hsplit : (((n + 1 : ℕ) : ℝ) * Real.pi) ^ (2 * σ)
        = ((n + 1 : ℕ) : ℝ) ^ (2 * σ) * Real.pi ^ (2 * σ) := by
      rw [Real.mul_rpow (by positivity) hπ.le]
    -- so (1+λ)^{-σ} ≤ C * ((n+1)^{2σ})⁻¹
    have hposL : 0 < (1 + lam (n + 1)) ^ σ := Real.rpow_pos_of_pos h1l σ
    have hposN : 0 < ((n + 1 : ℕ) : ℝ) ^ (2 * σ) := by positivity
    rw [Real.rpow_neg h1l.le]
    rw [hC]
    -- goal: (1+λ)^σ)⁻¹ ≤ (π^{2σ})⁻¹ * ((n+1)^{2σ})⁻¹
    rw [← mul_inv]
    apply inv_anti₀ (by positivity)
    rw [mul_comm (Real.pi ^ (2 * σ)) _, ← hsplit]
    exact hkey

/-- **Lemma 2 (Wiener-algebra embedding).**  For `σ > 1/2`, a coefficient sequence
in `H^σ` is absolutely summable: `Σ |a_n| < ∞`.  Proof by the AM–GM (Cauchy–Schwarz
per-term) split `|a_n| ≤ ½((1+λ_n)^{-σ} + (1+λ_n)^σ a_n²)`. -/
theorem hSigma_subset_l1_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a : ℕ → ℝ}
    (ha : MemHSigma σ a) : Summable (fun n : ℕ => |a n|) := by
  have hneg : Summable (fun n : ℕ => (1 + lam n) ^ (-σ)) :=
    summable_negPow_of_gt_half hσ
  -- both summable ⇒ ½(sum) summable
  have hdom : Summable
      (fun n : ℕ => (1 / 2 : ℝ) * ((1 + lam n) ^ (-σ) + (1 + lam n) ^ σ * (a n) ^ 2)) :=
    (hneg.add ha).mul_left (1 / 2)
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hdom
  -- per-term AM-GM bound
  have h1 : 0 < 1 + lam n := one_add_lam_pos n
  set w : ℝ := (1 + lam n) ^ (σ / 2) with hw
  set wi : ℝ := (1 + lam n) ^ (-(σ / 2)) with hwi
  have hw0 : 0 < w := Real.rpow_pos_of_pos h1 _
  have hwi0 : 0 < wi := Real.rpow_pos_of_pos h1 _
  have hprod : wi * w = 1 := by
    rw [hwi, hw, ← Real.rpow_add h1]; simp
  have hwi_sq : wi ^ 2 = (1 + lam n) ^ (-σ) := by
    rw [hwi, ← Real.rpow_natCast ((1 + lam n) ^ (-(σ / 2))) 2,
        ← Real.rpow_mul h1.le]
    congr 1; push_cast; ring
  have hw_sq : w ^ 2 = (1 + lam n) ^ σ := by
    rw [hw, ← Real.rpow_natCast ((1 + lam n) ^ (σ / 2)) 2, ← Real.rpow_mul h1.le]
    congr 1; push_cast; ring
  -- |a n| = wi * (w * |a n|), then AM-GM
  have hkey : |a n| = wi * (w * |a n|) := by
    rw [← mul_assoc, hprod, one_mul]
  rw [hkey]
  have hsq : (w * |a n|) ^ 2 = (1 + lam n) ^ σ * (a n) ^ 2 := by
    rw [mul_pow, hw_sq, sq_abs]
  -- 2 (wi)(w|a|) ≤ wi² + (w|a|)²
  have hamgm : 2 * (wi * (w * |a n|)) ≤ wi ^ 2 + (w * |a n|) ^ 2 := by
    nlinarith [sq_nonneg (wi - w * |a n|)]
  rw [hwi_sq, hsq] at hamgm
  linarith [hamgm]

/-! ## Lemma 3 scaffolding : the cosine product coefficient and the weight split.

The cosine product coefficient of two sequences is
`(a ⊛ b)_k = ½ Σ_{(m,n)} [m+n=k ∨ dist m n = k] a_m b_n`,
matching `cos(mπx)·cos(nπx) = ½(cos((m+n)πx) + cos(|m−n|πx))`.

We package the relevant index relation and prove the per-pair Peetre weight split
(the genuine reusable content for the product estimate). -/

/-- The two index relations contributing to the cosine product at output mode `k`:
the additive index `m+n` and the difference index `Nat.dist m n`. -/
def cosIndexRel (m n k : ℕ) : Prop := k = m + n ∨ k = Nat.dist m n

/-- Peetre weight split for a contributing pair, in the absolute-value form used by
the product estimate: if `(m,n)` contributes to mode `k`, then the `σ/2`-weighted
product `|a_m b_n|` at `k` is controlled by the `σ/2`-weighted factors. -/
theorem weight_split_term {σ : ℝ} (hσ : 0 ≤ σ) {m n k : ℕ} (hk : cosIndexRel m n k)
    (am bn : ℝ) :
    ∃ Cσ : ℝ, 0 < Cσ ∧
      (1 + lam k) ^ (σ / 2) * (|am| * |bn|) ≤
        Cσ * ((1 + lam m) ^ (σ / 2) * |am| * |bn|
               + |am| * ((1 + lam n) ^ (σ / 2) * |bn|)) := by
  obtain ⟨Cσ, hCσ, hbound⟩ := cosWeight_le_add hσ
  refine ⟨Cσ, hCσ, ?_⟩
  have hw := hbound m n k hk
  have hab0 : 0 ≤ |am| * |bn| := by positivity
  calc (1 + lam k) ^ (σ / 2) * (|am| * |bn|)
      ≤ (Cσ * ((1 + lam m) ^ (σ / 2) + (1 + lam n) ^ (σ / 2))) * (|am| * |bn|) :=
        mul_le_mul_of_nonneg_right hw hab0
    _ = Cσ * ((1 + lam m) ^ (σ / 2) * |am| * |bn|
               + |am| * ((1 + lam n) ^ (σ / 2) * |bn|)) := by ring

/-- The **additive Cauchy convolution** of two sequences:
`(a ⋆ b)_k = Σ_{m+n=k} a_m b_n`, summed over `Finset.antidiagonal k` (a finite sum,
so well-defined without any summability hypothesis). -/
def addConv (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ mn ∈ Finset.antidiagonal k, a mn.1 * b mn.2

/-- **Wiener-algebra closure at the `ℓ¹` level (additive convolution).**
For `σ > 1/2`, since `H^σ ⊂ ℓ¹`, the additive Cauchy convolution of two `H^σ`
sequences is absolutely summable: `Σ_k |(a ⋆ b)_k| < ∞`.  This is the genuine
Banach-algebra fact underlying the product theory (it is the `ℓ¹` Wiener algebra
being closed under convolution). -/
theorem addConv_summable_abs_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    Summable (fun k : ℕ => |addConv a b k|) := by
  have ha1 : Summable (fun n : ℕ => ‖a n‖) := by
    simpa [Real.norm_eq_abs] using hSigma_subset_l1_of_gt_half hσ ha
  have hb1 : Summable (fun n : ℕ => ‖b n‖) := by
    simpa [Real.norm_eq_abs] using hSigma_subset_l1_of_gt_half hσ hb
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm (f := a) (g := b) ha1 hb1
  simpa [addConv, Real.norm_eq_abs] using h

/-! ### `H^σ` membership of the additive convolution (discrete Young, partial-sum route).

We prove `MemHSigma σ (addConv a b)` for `σ>1/2` by the elementary discrete-Young
argument: bound every finite partial sum of the `H^σ` energy of the convolution by a
fixed constant, then invoke `summable_of_sum_le`.  The half-weighted sequence
`W_k|a_k|` lies in `ℓ²` (its square is the `H^σ` energy) and `|b|` lies in `ℓ¹`. -/

/-- The half-weight times the absolute coefficient, `(1+λ_k)^{σ/2} |a_k|`. -/
def wAbs (σ : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ := (1 + lam k) ^ (σ / 2) * |a k|

theorem wAbs_nonneg (σ : ℝ) (a : ℕ → ℝ) (k : ℕ) : 0 ≤ wAbs σ a k := by
  unfold wAbs
  have := Real.rpow_nonneg (one_add_lam_pos k).le (σ / 2); positivity

theorem wAbs_sq (σ : ℝ) (a : ℕ → ℝ) (k : ℕ) :
    (wAbs σ a k) ^ 2 = (1 + lam k) ^ σ * (a k) ^ 2 := by
  unfold wAbs
  rw [mul_pow, sq_abs, ← Real.rpow_natCast ((1 + lam k) ^ (σ / 2)) 2,
      ← Real.rpow_mul (one_add_lam_pos k).le]
  congr 2; push_cast; ring

/-- The squared half-weighted sequence is summable iff `a ∈ H^σ`. -/
theorem summable_wAbs_sq {σ : ℝ} {a : ℕ → ℝ} (ha : MemHSigma σ a) :
    Summable (fun k : ℕ => (wAbs σ a k) ^ 2) := by
  refine ha.congr (fun k => ?_); rw [wAbs_sq]

/-- Per-mode weight-split bound for the additive convolution:
`(1+λ_k)^{σ/2} |(a⋆b)_k| ≤ C Σ_{m+n=k} (wAbs a m · |b n| + |a m| · wAbs b n)`. -/
theorem halfWeight_addConv_le {σ : ℝ} (hσ : 0 ≤ σ) {a b : ℕ → ℝ} :
    ∃ Cσ : ℝ, 0 < Cσ ∧ ∀ k : ℕ,
      (1 + lam k) ^ (σ / 2) * |addConv a b k| ≤
        Cσ * ∑ mn ∈ Finset.antidiagonal k,
          (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
  obtain ⟨Cσ, hCσ, hbound⟩ := cosWeight_le_add hσ
  refine ⟨Cσ, hCσ, fun k => ?_⟩
  -- triangle inequality across the antidiagonal
  have htri : |addConv a b k| ≤ ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * |b mn.2| := by
    unfold addConv
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun mn _ => ?_); rw [abs_mul]
  have hwpos : 0 ≤ (1 + lam k) ^ (σ / 2) :=
    Real.rpow_nonneg (one_add_lam_pos k).le _
  calc (1 + lam k) ^ (σ / 2) * |addConv a b k|
      ≤ (1 + lam k) ^ (σ / 2) * ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * |b mn.2| :=
        mul_le_mul_of_nonneg_left htri hwpos
    _ = ∑ mn ∈ Finset.antidiagonal k,
          (1 + lam k) ^ (σ / 2) * (|a mn.1| * |b mn.2|) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ mn ∈ Finset.antidiagonal k,
          Cσ * (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
        refine Finset.sum_le_sum (fun mn hmn => ?_)
        have hmem : mn.1 + mn.2 = k := Finset.mem_antidiagonal.mp hmn
        have hk : cosIndexRel mn.1 mn.2 k := Or.inl hmem.symm
        obtain ⟨C', hC', hsplit⟩ := weight_split_term hσ hk (a mn.1) (b mn.2)
        -- align the two split constants: use cosWeight directly
        have hw := hbound mn.1 mn.2 k hk
        have hab0 : 0 ≤ |a mn.1| * |b mn.2| := by positivity
        calc (1 + lam k) ^ (σ / 2) * (|a mn.1| * |b mn.2|)
            ≤ (Cσ * ((1 + lam mn.1) ^ (σ / 2) + (1 + lam mn.2) ^ (σ / 2)))
                * (|a mn.1| * |b mn.2|) :=
              mul_le_mul_of_nonneg_right hw hab0
          _ = Cσ * (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
              unfold wAbs; ring
    _ = Cσ * ∑ mn ∈ Finset.antidiagonal k,
          (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) := by
        rw [Finset.mul_sum]

/-- Antidiagonal reindex bound: for a nonneg summable `g : ℕ×ℕ → ℝ`, the partial
double sum over antidiagonals indexed by a finset `u` is `≤ ∑' g`. -/
theorem sum_antidiagonal_le_tsum {g : ℕ × ℕ → ℝ} (hg0 : ∀ p, 0 ≤ g p)
    (hg : Summable g) (u : Finset ℕ) :
    ∑ k ∈ u, ∑ mn ∈ Finset.antidiagonal k, g mn ≤ ∑' p, g p := by
  classical
  -- collapse the double sum to a sum over the (disjoint) union sigma → image
  rw [Finset.sum_sigma' u (fun k => Finset.antidiagonal k) (fun _ mn => g mn)]
  -- the map ⟨k,mn⟩ ↦ mn is injective on u.sigma antidiagonal (k = mn.1+mn.2)
  set S : Finset (Σ _ : ℕ, ℕ × ℕ) := u.sigma (fun k => Finset.antidiagonal k) with hS
  have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ × ℕ => x.2) S := by
    rintro ⟨xk, xmn⟩ hx ⟨yk, ymn⟩ hy hxy
    simp only [hS, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe,
      Finset.mem_antidiagonal] at hx hy
    obtain ⟨_, hx2⟩ := hx
    obtain ⟨_, hy2⟩ := hy
    simp only at hxy
    subst hxy
    have hk : xk = yk := by rw [← hx2, ← hy2]
    subst hk; rfl
  rw [← Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  exact Summable.sum_le_tsum (S.image (fun x => x.2)) (fun p _ => hg0 p) hg

/-- Per-mode Cauchy–Schwarz piece: `P_k² ≤ (∑_{antidiag k} |b n|)·(∑_{antidiag k}
(wAbs a m)² |b n|)`, where `P_k = ∑_{antidiag k} wAbs a m · |b n|`. -/
theorem cs_piece (σ : ℝ) (a b : ℕ → ℝ) (k : ℕ) :
    (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|) ^ 2 ≤
      (∑ mn ∈ Finset.antidiagonal k, |b mn.2|) *
        (∑ mn ∈ Finset.antidiagonal k, (wAbs σ a mn.1) ^ 2 * |b mn.2|) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.antidiagonal k)
    (fun mn => Real.sqrt |b mn.2|) (fun mn => wAbs σ a mn.1 * Real.sqrt |b mn.2|)
  -- rewrite both sides into the desired shape
  have hL : ∀ mn : ℕ × ℕ,
      Real.sqrt |b mn.2| * (wAbs σ a mn.1 * Real.sqrt |b mn.2|)
        = wAbs σ a mn.1 * |b mn.2| := by
    intro mn
    have : Real.sqrt |b mn.2| * Real.sqrt |b mn.2| = |b mn.2| :=
      Real.mul_self_sqrt (abs_nonneg _)
    calc Real.sqrt |b mn.2| * (wAbs σ a mn.1 * Real.sqrt |b mn.2|)
        = wAbs σ a mn.1 * (Real.sqrt |b mn.2| * Real.sqrt |b mn.2|) := by ring
      _ = wAbs σ a mn.1 * |b mn.2| := by rw [this]
  have hLsum : ∑ mn ∈ Finset.antidiagonal k,
      Real.sqrt |b mn.2| * (wAbs σ a mn.1 * Real.sqrt |b mn.2|)
        = ∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2| :=
    Finset.sum_congr rfl (fun mn _ => hL mn)
  have hR1 : ∀ mn : ℕ × ℕ, (Real.sqrt |b mn.2|) ^ 2 = |b mn.2| := by
    intro mn; rw [Real.sq_sqrt (abs_nonneg _)]
  have hR2 : ∀ mn : ℕ × ℕ,
      (wAbs σ a mn.1 * Real.sqrt |b mn.2|) ^ 2 = (wAbs σ a mn.1) ^ 2 * |b mn.2| := by
    intro mn; rw [mul_pow, hR1]
  rw [hLsum] at h
  rw [Finset.sum_congr rfl (fun mn _ => hR1 mn),
      Finset.sum_congr rfl (fun mn _ => hR2 mn)] at h
  exact h

/-- `∑_{antidiag k} |b mn.2| = ∑_{n ∈ range (k+1)} |b n| ≤ ∑' n, |b n|`. -/
theorem sum_antidiag_proj_le {b : ℕ → ℝ} (hb : Summable (fun n => |b n|)) (k : ℕ) :
    ∑ mn ∈ Finset.antidiagonal k, |b mn.2| ≤ ∑' n, |b n| := by
  have heq : ∑ mn ∈ Finset.antidiagonal k, |b mn.2|
      = ∑ j ∈ Finset.range (k + 1), |b (k - j)| := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => |b ij.2|) k]
  rw [heq]
  have hrefl : ∑ j ∈ Finset.range (k + 1), |b (k - j)|
      = ∑ j ∈ Finset.range (k + 1), |b j| := by
    have := Finset.sum_range_reflect (fun j => |b j|) (k + 1)
    simpa using this
  rw [hrefl]
  exact Summable.sum_le_tsum (Finset.range (k + 1)) (fun n _ => abs_nonneg _) hb

/-- One Young piece bound: `∑_{k∈u} (∑_{antidiag k} wAbs a m · |b n|)²
≤ (∑'|b|) · (∑'(wAbs a)²) · (∑'|b|)`.  Uses per-mode Cauchy–Schwarz, the projection
bound, and the antidiagonal reindex. -/
theorem young_piece {σ : ℝ} {a b : ℕ → ℝ}
    (hb1 : Summable (fun n => |b n|))
    (hGa : Summable (fun p : ℕ × ℕ => (wAbs σ a p.1) ^ 2 * |b p.2|))
    (u : Finset ℕ) :
    ∑ k ∈ u, (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|) ^ 2 ≤
      (∑' n, |b n|) * (∑' p : ℕ × ℕ, (wAbs σ a p.1) ^ 2 * |b p.2|) := by
  set nb : ℝ := ∑' n, |b n| with hnb
  have hnb0 : 0 ≤ nb := tsum_nonneg (fun n => abs_nonneg _)
  -- per-mode CS + projection bound
  have hstep : ∀ k ∈ u,
      (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|) ^ 2 ≤
        nb * (∑ mn ∈ Finset.antidiagonal k, (wAbs σ a mn.1) ^ 2 * |b mn.2|) := by
    intro k _
    have hcs := cs_piece σ a b k
    have hproj : ∑ mn ∈ Finset.antidiagonal k, |b mn.2| ≤ nb :=
      sum_antidiag_proj_le hb1 k
    have hTk0 : 0 ≤ ∑ mn ∈ Finset.antidiagonal k, (wAbs σ a mn.1) ^ 2 * |b mn.2| :=
      Finset.sum_nonneg (fun mn _ => by positivity)
    calc (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|) ^ 2
        ≤ (∑ mn ∈ Finset.antidiagonal k, |b mn.2|) *
            (∑ mn ∈ Finset.antidiagonal k, (wAbs σ a mn.1) ^ 2 * |b mn.2|) := hcs
      _ ≤ nb * (∑ mn ∈ Finset.antidiagonal k, (wAbs σ a mn.1) ^ 2 * |b mn.2|) :=
          mul_le_mul_of_nonneg_right hproj hTk0
  calc ∑ k ∈ u, (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|) ^ 2
      ≤ ∑ k ∈ u, nb * (∑ mn ∈ Finset.antidiagonal k, (wAbs σ a mn.1) ^ 2 * |b mn.2|) :=
        Finset.sum_le_sum hstep
    _ = nb * ∑ k ∈ u, ∑ mn ∈ Finset.antidiagonal k, (wAbs σ a mn.1) ^ 2 * |b mn.2| := by
        rw [Finset.mul_sum]
    _ ≤ nb * (∑' p : ℕ × ℕ, (wAbs σ a p.1) ^ 2 * |b p.2|) := by
        apply mul_le_mul_of_nonneg_left _ hnb0
        exact sum_antidiagonal_le_tsum (fun p => by positivity) hGa u

set_option maxHeartbeats 800000 in
/-- **WALL-A, additive convolution H^σ membership (discrete Young).**
For `σ > 1/2`, if `a, b ∈ H^σ` then the additive Cauchy convolution `a ⋆ b ∈ H^σ`. -/
theorem memHSigma_addConv_of_gt_half {σ : ℝ} (hσ : 1 / 2 < σ) {a b : ℕ → ℝ}
    (ha : MemHSigma σ a) (hb : MemHSigma σ b) :
    MemHSigma σ (addConv a b) := by
  have hσ0 : 0 ≤ σ := by linarith
  have ha1 : Summable (fun n => |a n|) := hSigma_subset_l1_of_gt_half hσ ha
  have hb1 : Summable (fun n => |b n|) := hSigma_subset_l1_of_gt_half hσ hb
  have hWa : Summable (fun m => (wAbs σ a m) ^ 2) := summable_wAbs_sq ha
  have hWb : Summable (fun n => (wAbs σ b n) ^ 2) := summable_wAbs_sq hb
  -- product sequences over ℕ×ℕ are summable
  have hGa : Summable (fun p : ℕ × ℕ => (wAbs σ a p.1) ^ 2 * |b p.2|) :=
    Summable.mul_of_nonneg hWa hb1 (fun m => sq_nonneg _) (fun n => abs_nonneg _)
  have hGb : Summable (fun p : ℕ × ℕ => (wAbs σ b p.1) ^ 2 * |a p.2|) :=
    Summable.mul_of_nonneg hWb ha1 (fun m => sq_nonneg _) (fun n => abs_nonneg _)
  obtain ⟨Cσ, hCσ, hbound⟩ := halfWeight_addConv_le hσ0 (a := a) (b := b)
  have henergy0 : ∀ k, 0 ≤ (1 + lam k) ^ σ * (addConv a b k) ^ 2 := by
    intro k; have := Real.rpow_nonneg (one_add_lam_pos k).le σ; positivity
  refine summable_of_sum_le
    (c := Cσ ^ 2 * (2 * ((∑' n, |b n|) * (∑' p : ℕ × ℕ, (wAbs σ a p.1) ^ 2 * |b p.2|))
        + 2 * ((∑' n, |a n|) * (∑' p : ℕ × ℕ, (wAbs σ b p.1) ^ 2 * |a p.2|))))
    henergy0 (fun u => ?_)
  -- per-mode: energy_k ≤ Cσ² (2 P_k² + 2 Q_k²)
  have hpermode : ∀ k ∈ u,
      (1 + lam k) ^ σ * (addConv a b k) ^ 2 ≤
        Cσ ^ 2 * (2 * (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|) ^ 2
                  + 2 * (∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2) ^ 2) := by
    intro k _
    have hbk := hbound k
    -- left side = ((1+λ)^{σ/2} |addConv|)²
    have heq : (1 + lam k) ^ σ * (addConv a b k) ^ 2
        = ((1 + lam k) ^ (σ / 2) * |addConv a b k|) ^ 2 := by
      rw [mul_pow, sq_abs, ← Real.rpow_natCast ((1 + lam k) ^ (σ / 2)) 2,
          ← Real.rpow_mul (one_add_lam_pos k).le]
      congr 2; push_cast; ring
    set P := ∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2| with hP
    set Q := ∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2 with hQ
    have hPQ0 : (1 + lam k) ^ (σ / 2) * |addConv a b k| ≤ Cσ * (P + Q) := by
      have : ∑ mn ∈ Finset.antidiagonal k,
          (wAbs σ a mn.1 * |b mn.2| + |a mn.1| * wAbs σ b mn.2) = P + Q := by
        rw [hP, hQ, ← Finset.sum_add_distrib]
      rw [this] at hbk; exact hbk
    have hlhs0 : 0 ≤ (1 + lam k) ^ (σ / 2) * |addConv a b k| := by
      have := Real.rpow_nonneg (one_add_lam_pos k).le (σ / 2); positivity
    rw [heq]
    calc ((1 + lam k) ^ (σ / 2) * |addConv a b k|) ^ 2
        ≤ (Cσ * (P + Q)) ^ 2 := by
          apply pow_le_pow_left₀ hlhs0 hPQ0
      _ = Cσ ^ 2 * (P + Q) ^ 2 := by ring
      _ ≤ Cσ ^ 2 * (2 * P ^ 2 + 2 * Q ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [sq_nonneg (P - Q)]
  -- sum over u and apply the two Young pieces
  calc ∑ k ∈ u, (1 + lam k) ^ σ * (addConv a b k) ^ 2
      ≤ ∑ k ∈ u, Cσ ^ 2 * (2 * (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|) ^ 2
            + 2 * (∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2) ^ 2) :=
        Finset.sum_le_sum hpermode
    _ = Cσ ^ 2 * (2 * ∑ k ∈ u, (∑ mn ∈ Finset.antidiagonal k, wAbs σ a mn.1 * |b mn.2|) ^ 2
          + 2 * ∑ k ∈ u, (∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2) ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Cσ ^ 2 * (2 * ((∑' n, |b n|) * (∑' p : ℕ × ℕ, (wAbs σ a p.1) ^ 2 * |b p.2|))
          + 2 * ((∑' n, |a n|) * (∑' p : ℕ × ℕ, (wAbs σ b p.1) ^ 2 * |a p.2|))) := by
        have hYa := young_piece (σ := σ) (a := a) (b := b) hb1 hGa u
        have hYb' := young_piece (σ := σ) (a := b) (b := a) ha1 hGb u
        -- align hYb' shape (factors |a m| * wAbs b n) with Q via commutativity
        have hQeq : ∀ k, (∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2) ^ 2
            = (∑ mn ∈ Finset.antidiagonal k, wAbs σ b mn.1 * |a mn.2|) ^ 2 := by
          intro k
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
                (fun ij => |a ij.1| * wAbs σ b ij.2) k,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
                (fun ij => wAbs σ b ij.1 * |a ij.2|) k]
          have := Finset.sum_range_reflect
            (fun j => wAbs σ b j * |a (k - j)|) (k + 1)
          simp only at this ⊢
          rw [← this]
          refine congrArg (· ^ 2) (Finset.sum_congr rfl (fun j hj => ?_))
          have hjk : j ≤ k := by
            simp only [Finset.mem_range] at hj; omega
          have e1 : k + 1 - 1 - j = k - j := by omega
          rw [e1]
          have e2 : k - (k - j) = j := by omega
          rw [e2]; ring
        have hQsum : ∑ k ∈ u, (∑ mn ∈ Finset.antidiagonal k, |a mn.1| * wAbs σ b mn.2) ^ 2
            = ∑ k ∈ u, (∑ mn ∈ Finset.antidiagonal k, wAbs σ b mn.1 * |a mn.2|) ^ 2 :=
          Finset.sum_congr rfl (fun k _ => hQeq k)
        rw [hQsum]
        have hCσ2 : 0 ≤ Cσ ^ 2 := sq_nonneg _
        apply mul_le_mul_of_nonneg_left _ hCσ2
        linarith [hYa, hYb']

#print axioms cosWeight_le_add
#print axioms summable_negPow_of_gt_half
#print axioms hSigma_subset_l1_of_gt_half
#print axioms weight_split_term
#print axioms addConv_summable_abs_of_gt_half
#print axioms wAbs_sq
#print axioms halfWeight_addConv_le
#print axioms sum_antidiagonal_le_tsum
#print axioms cs_piece
#print axioms sum_antidiag_proj_le
#print axioms young_piece
#print axioms memHSigma_addConv_of_gt_half

end ShenWork.Paper2.IntervalWienerAlgebra
