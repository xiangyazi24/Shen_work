/-
  Phase-0 / M-gate-3: explicit power-law upper bounds for the homogeneous
  smoothing weights `eigExpWeight` and `sqrtEigExpWeight`
  (defined in `IntervalHomogeneousQuantBound`).

  We prove, for every `τ > 0`, EXPLICIT constants (closed form, no
  existentials):

    (1)  eigExpWeight τ      ≤ C₂ / τ²            with C₂ = 4 / (e · π²)
    (2)  sqrtEigExpWeight τ  ≤ C₁ / (τ · √τ)      with C₁ = 2 / (√e · π²)

  Both bounds are monotone-decreasing in `τ`, hence usable for the ratio
  comparisons `Ē(τ/2)/Ē(τ)` of the restart recursion.  The exponent landed
  is `p = 2` for `E₂` and `p = 3/2` for `E₁` (acceptable per the M-gate-3
  spec: explicit monotone power bounds, exact exponent secondary).

  Core mechanism (per mode, `z := τλ`):
    * `z · e^{−z} ≤ 1/e`           (from `z ≤ e^{z−1}`)
    * `(√z · e^{−z/2})² = z·e^{−z} ≤ 1/e`  ⟹  `√z·e^{−z/2} ≤ 1/√e`
    * tail `∑_{n≥1} e^{−(τπ²/2) n²} ≤ ∑_{n≥1} e^{−(τπ²/2) n} = r/(1−r)
       ≤ 1/(e^{x}−1) ≤ 1/x = 2/(τπ²)`  with `x = τπ²/2`.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.  New file only.
-/
import ShenWork.PDE.IntervalHomogeneousQuantBound

noncomputable section

namespace ShenWork.IntervalWeightPowerBound

open ShenWork.IntervalHomogeneousQuantBound
open ShenWork.IntervalMildRegularityBootstrap

/-- `eigExpWeight` is antitone in `τ` on `0 < τ` (term-by-term). -/
theorem eigExpWeight_antitone {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ ≤ τ₂) :
    eigExpWeight τ₂ ≤ eigExpWeight τ₁ := by
  have hτ₂ : 0 < τ₂ := lt_of_lt_of_le hτ₁ hτ₁₂
  simp only [eigExpWeight]
  refine Summable.tsum_le_tsum (fun n => ?_)
    (unitIntervalCosineEigenvalue_mul_exp_summable hτ₂)
    (unitIntervalCosineEigenvalue_mul_exp_summable hτ₁)
  have hlam : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hlam
  have : τ₁ * unitIntervalCosineEigenvalue n ≤ τ₂ * unitIntervalCosineEigenvalue n :=
    mul_le_mul_of_nonneg_right hτ₁₂ hlam
  linarith

/-- `sqrtEigExpWeight` is antitone in `τ` on `0 < τ` (term-by-term). -/
theorem sqrtEigExpWeight_antitone {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ ≤ τ₂) :
    sqrtEigExpWeight τ₂ ≤ sqrtEigExpWeight τ₁ := by
  have hτ₂ : 0 < τ₂ := lt_of_lt_of_le hτ₁ hτ₁₂
  simp only [sqrtEigExpWeight]
  refine Summable.tsum_le_tsum (fun n => ?_)
    (sqrtEig_mul_exp_summable hτ₂) (sqrtEig_mul_exp_summable hτ₁)
  have hlam : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)
  have : τ₁ * unitIntervalCosineEigenvalue n ≤ τ₂ * unitIntervalCosineEigenvalue n :=
    mul_le_mul_of_nonneg_right hτ₁₂ hlam
  linarith

/-- Scalar bound `z · e^{−z} ≤ 1/e` for all real `z`.  (Sup of `z e^{−z}`.) -/
theorem mul_exp_neg_le_inv_e (z : ℝ) :
    z * Real.exp (-z) ≤ Real.exp (-1) := by
  -- `z ≤ e^{z−1}` from `1 + (z−1) ≤ e^{z−1}`.
  have hle : z ≤ Real.exp (z - 1) := by
    have := Real.add_one_le_exp (z - 1)
    linarith
  have hexp : (0:ℝ) < Real.exp (-z) := Real.exp_pos _
  calc z * Real.exp (-z)
      ≤ Real.exp (z - 1) * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right hle hexp.le
    _ = Real.exp ((z - 1) + (-z)) := (Real.exp_add _ _).symm
    _ = Real.exp (-1) := by ring_nf

/-- `√z · e^{−z/2} ≤ 1/√e` for `z ≥ 0` (square it: `z e^{−z} ≤ 1/e`). -/
theorem sqrt_mul_exp_neg_half_le (z : ℝ) (hz : 0 ≤ z) :
    Real.sqrt z * Real.exp (-z / 2) ≤ Real.sqrt (Real.exp (-1)) := by
  have hlhs : (0:ℝ) ≤ Real.sqrt z * Real.exp (-z / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  have hrhs : (0:ℝ) ≤ Real.sqrt (Real.exp (-1)) := Real.sqrt_nonneg _
  -- square of LHS is `z * e^{−z}`.
  have hsq : (Real.sqrt z * Real.exp (-z / 2)) ^ 2 = z * Real.exp (-z) := by
    have h1 : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz
    have h2 : (Real.exp (-z / 2)) ^ 2 = Real.exp (-z) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc (Real.sqrt z * Real.exp (-z / 2)) ^ 2
        = (Real.sqrt z) ^ 2 * (Real.exp (-z / 2)) ^ 2 := by ring
      _ = z * Real.exp (-z) := by rw [h1, h2]
  -- LHS = √(LHS²) = √(z·e^{−z}) ≤ √(e^{−1}).
  have hsq_le : (Real.sqrt z * Real.exp (-z / 2)) ^ 2 ≤ Real.exp (-1) := by
    rw [hsq]; exact mul_exp_neg_le_inv_e z
  calc Real.sqrt z * Real.exp (-z / 2)
      = Real.sqrt ((Real.sqrt z * Real.exp (-z / 2)) ^ 2) := by
        rw [Real.sqrt_sq hlhs]
    _ ≤ Real.sqrt (Real.exp (-1)) := Real.sqrt_le_sqrt hsq_le

/-- `e^c − 1 ≥ c` ⟹ shifted geometric tail `∑' (e^{−c})^{n+1} = 1/(e^c−1) ≤ 1/c`. -/
theorem geometric_tail_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, (Real.exp (-c)) ^ (n + 1)) ≤ 1 / c := by
  set r : ℝ := Real.exp (-c) with hr_def
  have hr0 : 0 ≤ r := (Real.exp_nonneg _)
  have hr1 : r < 1 := by
    rw [hr_def]; exact Real.exp_lt_one_iff.mpr (by linarith)
  -- ∑' r^(n+1) = r · ∑' r^n = r/(1−r)
  have hsum : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have htail : (∑' n : ℕ, r ^ (n + 1)) = r * (1 - r)⁻¹ := by
    have : (∑' n : ℕ, r ^ (n + 1)) = r * ∑' n : ℕ, r ^ n := by
      rw [← tsum_mul_left]
      congr 1; funext n; ring
    rw [this, tsum_geometric_of_lt_one hr0 hr1]
  rw [htail]
  -- r/(1−r) = 1/(e^c − 1) ≤ 1/c.
  have hexpc : Real.exp c > 0 := Real.exp_pos _
  have h1mr_pos : 0 < 1 - r := by linarith
  have hrinv : r * (1 - r)⁻¹ = 1 / (Real.exp c - 1) := by
    have hreq : r = (Real.exp c)⁻¹ := by
      rw [hr_def, Real.exp_neg]
    rw [hreq]
    have hne : Real.exp c ≠ 0 := ne_of_gt hexpc
    field_simp
  rw [hrinv]
  have hecm1 : c ≤ Real.exp c - 1 := by
    have := Real.add_one_le_exp c; linarith
  have : 1 / (Real.exp c - 1) ≤ 1 / c := one_div_le_one_div_of_le hc hecm1
  linarith

/-- Per-mode `λₙ e^{−τλₙ} ≤ (2/(e·τ)) · e^{−τλₙ/2}` for `τ > 0`. -/
theorem eig_mode_le {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    unitIntervalCosineEigenvalue n *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)
      ≤ (2 / (Real.exp 1 * τ)) *
          Real.exp (-(τ / 2) * unitIntervalCosineEigenvalue n) := by
  set lam : ℝ := unitIntervalCosineEigenvalue n with hlam_def
  have hlam : 0 ≤ lam := by
    rw [hlam_def]; unfold unitIntervalCosineEigenvalue; positivity
  -- z := τ·lam/2 ≥ 0, use z·e^{−z} ≤ e^{−1}.
  have hz := mul_exp_neg_le_inv_e (τ * lam / 2)
  have hsplit : Real.exp (-τ * lam) =
      Real.exp (-(τ * lam / 2)) * Real.exp (-(τ / 2) * lam) := by
    rw [← Real.exp_add]; congr 1; ring
  have he1 : Real.exp 1 > 0 := Real.exp_pos _
  -- lam·e^{−τ·lam} = (2/τ)·(τ·lam/2·e^{−τ·lam/2})·e^{−τ·lam/2}
  have hkey : lam * Real.exp (-τ * lam)
      = (2 / τ) * ((τ * lam / 2) * Real.exp (-(τ * lam / 2)))
          * Real.exp (-(τ / 2) * lam) := by
    rw [hsplit]; field_simp
  rw [hkey]
  have hexp_pos : 0 ≤ Real.exp (-(τ / 2) * lam) := Real.exp_nonneg _
  have h2τ : 0 ≤ 2 / τ := by positivity
  calc (2 / τ) * ((τ * lam / 2) * Real.exp (-(τ * lam / 2)))
          * Real.exp (-(τ / 2) * lam)
      ≤ (2 / τ) * Real.exp (-1) * Real.exp (-(τ / 2) * lam) := by
        have hstep : (2 / τ) * ((τ * lam / 2) * Real.exp (-(τ * lam / 2)))
            ≤ (2 / τ) * Real.exp (-1) :=
          mul_le_mul_of_nonneg_left hz h2τ
        exact mul_le_mul_of_nonneg_right hstep hexp_pos
    _ = (2 / (Real.exp 1 * τ)) * Real.exp (-(τ / 2) * lam) := by
        rw [Real.exp_neg]; field_simp

/-- **Power-law bound for `E₂`**:  `eigExpWeight τ ≤ (4/(e·π²)) / τ²`. -/
theorem eigExpWeight_le {τ : ℝ} (hτ : 0 < τ) :
    eigExpWeight τ ≤ (4 / (Real.exp 1 * Real.pi ^ 2)) / τ ^ 2 := by
  set c : ℝ := τ * Real.pi ^ 2 / 2 with hc_def
  have hc : 0 < c := by rw [hc_def]; positivity
  have he1 : 0 < Real.exp 1 := Real.exp_pos _
  -- summability of the λ-weight
  have hwt := unitIntervalCosineEigenvalue_mul_exp_summable hτ
  -- majorant per mode bound, then split off n=0 (zero) + reindex to geometric tail.
  -- For n≥1: e^{−(τ/2)λ_{n}} ≤ (e^{−c})^{n}  via λ_n = π²n² and n²≥n.
  have hmode : ∀ n : ℕ,
      Real.exp (-(τ / 2) * unitIntervalCosineEigenvalue (n + 1))
        ≤ (Real.exp (-c)) ^ (n + 1) := by
    intro n
    have hlam : unitIntervalCosineEigenvalue (n + 1)
        = ((n + 1 : ℝ) ^ 2) * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue; push_cast; ring
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hlam, hc_def]
    have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [hn1]
    have hpi : (0 : ℝ) ≤ τ * Real.pi ^ 2 / 2 := by positivity
    have hmul : ((n : ℝ) + 1) * (τ * Real.pi ^ 2 / 2)
        ≤ ((n : ℝ) + 1) ^ 2 * (τ * Real.pi ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hsq hpi
    push_cast
    nlinarith [hmul]
  -- Per-mode majorant: λ_{n+1} e^{−τλ_{n+1}} ≤ (2/(eτ))·(e^{−c})^{n+1}.
  have hmaj : ∀ n : ℕ,
      unitIntervalCosineEigenvalue (n + 1) *
          Real.exp (-τ * unitIntervalCosineEigenvalue (n + 1))
        ≤ (2 / (Real.exp 1 * τ)) * (Real.exp (-c)) ^ (n + 1) := by
    intro n
    refine (eig_mode_le hτ (n + 1)).trans ?_
    have hco : (0:ℝ) ≤ 2 / (Real.exp 1 * τ) := by positivity
    exact mul_le_mul_of_nonneg_left (hmode n) hco
  -- The shifted weight series is summable.
  have htail_summable : Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue (n + 1) *
        Real.exp (-τ * unitIntervalCosineEigenvalue (n + 1))) :=
    (summable_nat_add_iff 1).mpr hwt
  -- Geometric majorant series is summable.
  have hgeo_summable : Summable (fun n : ℕ =>
      (2 / (Real.exp 1 * τ)) * (Real.exp (-c)) ^ (n + 1)) := by
    have hr0 : (0:ℝ) ≤ Real.exp (-c) := Real.exp_nonneg _
    have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hbase : Summable (fun n : ℕ => (Real.exp (-c)) ^ (n + 1)) :=
      ((summable_geometric_of_lt_one hr0 hr1).comp_injective
        (add_left_injective 1)).congr (fun n => by simp)
    exact hbase.mul_left _
  -- Assemble: split n=0, bound tail.
  have hzero : unitIntervalCosineEigenvalue 0 *
      Real.exp (-τ * unitIntervalCosineEigenvalue 0) = 0 := by
    unfold unitIntervalCosineEigenvalue; simp
  have hsplit : eigExpWeight τ =
      ∑' n : ℕ, unitIntervalCosineEigenvalue (n + 1) *
        Real.exp (-τ * unitIntervalCosineEigenvalue (n + 1)) := by
    simp only [eigExpWeight]
    rw [hwt.tsum_eq_zero_add, hzero, zero_add]
  rw [hsplit]
  calc (∑' n : ℕ, unitIntervalCosineEigenvalue (n + 1) *
        Real.exp (-τ * unitIntervalCosineEigenvalue (n + 1)))
      ≤ ∑' n : ℕ, (2 / (Real.exp 1 * τ)) * (Real.exp (-c)) ^ (n + 1) :=
        Summable.tsum_le_tsum hmaj htail_summable hgeo_summable
    _ = (2 / (Real.exp 1 * τ)) * ∑' n : ℕ, (Real.exp (-c)) ^ (n + 1) :=
        tsum_mul_left
    _ ≤ (2 / (Real.exp 1 * τ)) * (1 / c) := by
        have hco : (0:ℝ) ≤ 2 / (Real.exp 1 * τ) := by positivity
        exact mul_le_mul_of_nonneg_left (geometric_tail_le hc) hco
    _ = (4 / (Real.exp 1 * Real.pi ^ 2)) / τ ^ 2 := by
        rw [hc_def]; field_simp; ring

/-- Per-mode `√λₙ e^{−τλₙ} ≤ (√(e^{−1})/√τ) · e^{−(τ/2)λₙ}` for `τ > 0`. -/
theorem sqrtEig_mode_le {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    Real.sqrt (unitIntervalCosineEigenvalue n) *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)
      ≤ (Real.sqrt (Real.exp (-1)) / Real.sqrt τ) *
          Real.exp (-(τ / 2) * unitIntervalCosineEigenvalue n) := by
  set lam : ℝ := unitIntervalCosineEigenvalue n with hlam_def
  have hlam : 0 ≤ lam := by
    rw [hlam_def]; unfold unitIntervalCosineEigenvalue; positivity
  have hτ0 : 0 ≤ τ := hτ.le
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  -- √(τ·lam) · e^{−τ·lam/2} ≤ √(e^{−1}).
  have hz := sqrt_mul_exp_neg_half_le (τ * lam) (by positivity)
  -- √lam = √(τ·lam)/√τ
  have hsqrt_lam : Real.sqrt lam = Real.sqrt (τ * lam) / Real.sqrt τ := by
    rw [Real.sqrt_mul hτ0]
    field_simp
  -- e^{−τ·lam} = e^{−(τ·lam)/2} · e^{−(τ/2)·lam}
  have hsplit : Real.exp (-τ * lam) =
      Real.exp (-(τ * lam) / 2) * Real.exp (-(τ / 2) * lam) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp_pos : 0 ≤ Real.exp (-(τ / 2) * lam) := Real.exp_nonneg _
  -- rewrite LHS and bound.
  have hkey : Real.sqrt lam * Real.exp (-τ * lam)
      = (1 / Real.sqrt τ) *
          (Real.sqrt (τ * lam) * Real.exp (-(τ * lam) / 2))
          * Real.exp (-(τ / 2) * lam) := by
    rw [hsqrt_lam, hsplit]; field_simp
  rw [hkey]
  have hinvs : (0:ℝ) ≤ 1 / Real.sqrt τ := by positivity
  calc (1 / Real.sqrt τ) *
          (Real.sqrt (τ * lam) * Real.exp (-(τ * lam) / 2))
          * Real.exp (-(τ / 2) * lam)
      ≤ (1 / Real.sqrt τ) * Real.sqrt (Real.exp (-1))
          * Real.exp (-(τ / 2) * lam) := by
        have hstep : (1 / Real.sqrt τ) *
            (Real.sqrt (τ * lam) * Real.exp (-(τ * lam) / 2))
            ≤ (1 / Real.sqrt τ) * Real.sqrt (Real.exp (-1)) :=
          mul_le_mul_of_nonneg_left hz hinvs
        exact mul_le_mul_of_nonneg_right hstep hexp_pos
    _ = (Real.sqrt (Real.exp (-1)) / Real.sqrt τ)
          * Real.exp (-(τ / 2) * lam) := by ring

/-- **Power-law bound for `E₁`**:  `sqrtEigExpWeight τ ≤ (2/(√e·π²)) / (τ·√τ)`. -/
theorem sqrtEigExpWeight_le {τ : ℝ} (hτ : 0 < τ) :
    sqrtEigExpWeight τ ≤
      (2 / (Real.sqrt (Real.exp 1) * Real.pi ^ 2)) / (τ * Real.sqrt τ) := by
  set c : ℝ := τ * Real.pi ^ 2 / 2 with hc_def
  have hc : 0 < c := by rw [hc_def]; positivity
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hwt := sqrtEig_mul_exp_summable hτ
  -- tail geometric majorant bound on e^{−(τ/2)λ_{n+1}} (reused from eig case).
  have hmode : ∀ n : ℕ,
      Real.exp (-(τ / 2) * unitIntervalCosineEigenvalue (n + 1))
        ≤ (Real.exp (-c)) ^ (n + 1) := by
    intro n
    have hlam : unitIntervalCosineEigenvalue (n + 1)
        = ((n + 1 : ℝ) ^ 2) * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue; push_cast; ring
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hlam, hc_def]
    have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [hn1]
    have hpi : (0 : ℝ) ≤ τ * Real.pi ^ 2 / 2 := by positivity
    have hmul : ((n : ℝ) + 1) * (τ * Real.pi ^ 2 / 2)
        ≤ ((n : ℝ) + 1) ^ 2 * (τ * Real.pi ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hsq hpi
    push_cast
    nlinarith [hmul]
  -- Per-mode √λ majorant.
  have hcoef : (0:ℝ) ≤ Real.sqrt (Real.exp (-1)) / Real.sqrt τ := by positivity
  have hmaj : ∀ n : ℕ,
      Real.sqrt (unitIntervalCosineEigenvalue (n + 1)) *
          Real.exp (-τ * unitIntervalCosineEigenvalue (n + 1))
        ≤ (Real.sqrt (Real.exp (-1)) / Real.sqrt τ) *
            (Real.exp (-c)) ^ (n + 1) := by
    intro n
    refine (sqrtEig_mode_le hτ (n + 1)).trans ?_
    exact mul_le_mul_of_nonneg_left (hmode n) hcoef
  have htail_summable : Summable (fun n : ℕ =>
      Real.sqrt (unitIntervalCosineEigenvalue (n + 1)) *
        Real.exp (-τ * unitIntervalCosineEigenvalue (n + 1))) :=
    (summable_nat_add_iff 1).mpr hwt
  have hgeo_summable : Summable (fun n : ℕ =>
      (Real.sqrt (Real.exp (-1)) / Real.sqrt τ) * (Real.exp (-c)) ^ (n + 1)) := by
    have hr0 : (0:ℝ) ≤ Real.exp (-c) := Real.exp_nonneg _
    have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hbase : Summable (fun n : ℕ => (Real.exp (-c)) ^ (n + 1)) :=
      ((summable_geometric_of_lt_one hr0 hr1).comp_injective
        (add_left_injective 1)).congr (fun n => by simp)
    exact hbase.mul_left _
  have hzero : Real.sqrt (unitIntervalCosineEigenvalue 0) *
      Real.exp (-τ * unitIntervalCosineEigenvalue 0) = 0 := by
    unfold unitIntervalCosineEigenvalue; simp
  have hsplit : sqrtEigExpWeight τ =
      ∑' n : ℕ, Real.sqrt (unitIntervalCosineEigenvalue (n + 1)) *
        Real.exp (-τ * unitIntervalCosineEigenvalue (n + 1)) := by
    simp only [sqrtEigExpWeight]
    rw [hwt.tsum_eq_zero_add, hzero, zero_add]
  rw [hsplit]
  calc (∑' n : ℕ, Real.sqrt (unitIntervalCosineEigenvalue (n + 1)) *
        Real.exp (-τ * unitIntervalCosineEigenvalue (n + 1)))
      ≤ ∑' n : ℕ, (Real.sqrt (Real.exp (-1)) / Real.sqrt τ) *
          (Real.exp (-c)) ^ (n + 1) :=
        Summable.tsum_le_tsum hmaj htail_summable hgeo_summable
    _ = (Real.sqrt (Real.exp (-1)) / Real.sqrt τ) *
          ∑' n : ℕ, (Real.exp (-c)) ^ (n + 1) := tsum_mul_left
    _ ≤ (Real.sqrt (Real.exp (-1)) / Real.sqrt τ) * (1 / c) :=
        mul_le_mul_of_nonneg_left (geometric_tail_le hc) hcoef
    _ = (2 / (Real.sqrt (Real.exp 1) * Real.pi ^ 2)) / (τ * Real.sqrt τ) := by
        have hsqrt_inv : Real.sqrt (Real.exp (-1)) = 1 / Real.sqrt (Real.exp 1) := by
          rw [Real.exp_neg, Real.sqrt_inv]; ring
        rw [hsqrt_inv, hc_def]
        have he1 : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos _)
        have hpi : (0:ℝ) < Real.pi := Real.pi_pos
        field_simp

end ShenWork.IntervalWeightPowerBound
