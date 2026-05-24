/-
  ShenWork/Paper1/Lemma25Helpers.lean

  Helpers for the Lemma 2.5 main-chain assembly (TASK_QUEUE Slot A).
  Kept in a separate file so concurrent edits to Paper1/Statements.lean
  don't race over them.
-/
import ShenWork.Paper1.Statements

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-! ### Laplace-kernel integral with the integration variable in front -/

lemma kernel_exp_combine_integrable
    {c k : ℝ} (hk_lt : k < c) (y : ℝ) :
    Integrable (fun x : ℝ => Real.exp ((k - c) * |x - y|)) := by
  have hkc_pos : 0 < c - k := by linarith
  have hbase := _root_.kernel_exp_neg_mul_abs_integrable hkc_pos y
  have habs_eq :
      (fun x : ℝ => Real.exp ((k - c) * |x - y|)) =
        (fun x : ℝ => Real.exp (-(c - k) * |y - x|)) := by
    funext x
    rw [abs_sub_comm y x]
    congr 1
    ring
  rw [habs_eq]
  exact hbase

lemma integral_exp_combine_eq
    {c k : ℝ} (hk_lt : k < c) (y : ℝ) :
    (∫ x : ℝ, Real.exp ((k - c) * |x - y|)) = 2 / (c - k) := by
  have hkc_pos : 0 < c - k := by linarith
  have hbase := integral_exp_neg_mul_abs_sub hkc_pos y
  have habs_eq :
      (fun x : ℝ => Real.exp ((k - c) * |x - y|)) =
        (fun x : ℝ => Real.exp (-(c - k) * |y - x|)) := by
    funext x
    rw [abs_sub_comm y x]
    congr 1
    ring
  rw [habs_eq]
  exact hbase

/-! ### Weight transfer for Lemma 2.5

For a `c`-positive resolvent kernel and an exponential weight ψ whose
log-derivative is bounded by `k < c`,
`∫ exp(-c|x-y|) · ψ(x) dx ≤ ψ(y) · 2/(c-k)`. -/

theorem kernel_weight_integral_le_psi
    (psi : ExponentialWeight) {c k : ℝ} (hc : 0 < c) (hk_nn : 0 ≤ k)
    (hk_lt : k < c)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z) (y : ℝ) :
    ∫ x : ℝ, Real.exp (-c * |x - y|) * psi.weight x ≤
      psi.weight y * (2 / (c - k)) := by
  have hpw : ∀ x : ℝ,
      Real.exp (-c * |x - y|) * psi.weight x ≤
        psi.weight y * Real.exp ((k - c) * |x - y|) := by
    intro x
    have hψ_le := psi.weight_ratio_le hk_nn hk_bound x y
    have hexp_nonneg : 0 ≤ Real.exp (-c * |x - y|) := (Real.exp_pos _).le
    have h1 : Real.exp (-c * |x - y|) * psi.weight x ≤
        Real.exp (-c * |x - y|) * (psi.weight y * Real.exp (k * |x - y|)) :=
      mul_le_mul_of_nonneg_left hψ_le hexp_nonneg
    have h_rearrange :
        Real.exp (-c * |x - y|) * (psi.weight y * Real.exp (k * |x - y|)) =
          psi.weight y * Real.exp ((k - c) * |x - y|) := by
      rw [← mul_assoc, mul_comm (Real.exp (-c * |x - y|)) (psi.weight y),
        mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [h_rearrange] at h1
    exact h1
  have h_RHS_int : Integrable
      (fun x : ℝ => psi.weight y * Real.exp ((k - c) * |x - y|)) :=
    (kernel_exp_combine_integrable hk_lt y).const_mul (psi.weight y)
  have h_LHS_int : Integrable
      (fun x : ℝ => Real.exp (-c * |x - y|) * psi.weight x) := by
    refine h_RHS_int.mono' ?_ ?_
    · have h_meas_left : Measurable (fun x : ℝ => Real.exp (-c * |x - y|)) := by
        fun_prop
      have h_meas_psi : Measurable psi.weight :=
        (psi.smooth.differentiable two_ne_zero).continuous.measurable
      exact (h_meas_left.mul h_meas_psi).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hpos : 0 ≤ Real.exp (-c * |x - y|) * psi.weight x :=
        mul_nonneg (Real.exp_pos _).le (psi.pos x).le
      rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      exact hpw x
  have hint :
      ∫ x, Real.exp (-c * |x - y|) * psi.weight x ≤
        ∫ x, psi.weight y * Real.exp ((k - c) * |x - y|) :=
    MeasureTheory.integral_mono h_LHS_int h_RHS_int hpw
  rw [MeasureTheory.integral_const_mul, integral_exp_combine_eq hk_lt y] at hint
  exact hint

/-! ### Combined Jensen + weight-transfer step

Convolves Jensen on `Ψ^p` with `kernel_weight_integral_le_psi` to bound
the ψ-weighted L^p norm of `Ψ(u^γ)` by a multiple of the ψ-weighted L^p
norm of `u^γ`.  Constant depends on `(l, μ, p, k)` where `k < √l`
controls the ψ log-derivative. -/

theorem psi_pExp_weighted_le_kernel_weighted
    (psi : ExponentialWeight) {pExp gamma l mu k : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp) (hk_nn : 0 ≤ k)
    (hk_lt : k < Real.sqrt l)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y) :
    ∀ x : ℝ,
      (Psi u l mu x) ^ pExp * psi.weight x ≤
        (mu / (2 * Real.sqrt l)) ^ pExp *
          (2 / Real.sqrt l) ^ (pExp - 1) *
          (∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * (u y) ^ pExp) *
            psi.weight x := by
  intro x
  have hJensen := lemma_2_5_jensenStep u l mu pExp hl hmu hpExp hu hu_nn x
  have hψ_nn : 0 ≤ psi.weight x := (psi.pos x).le
  exact mul_le_mul_of_nonneg_right hJensen hψ_nn

/-! ### Pointwise gradient bound times weight -/

theorem psi_deriv_pExp_weighted_le
    (psi : ExponentialWeight) {pExp l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 0 < pExp)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y) :
    ∀ x : ℝ,
      |deriv (fun z => Psi u l mu z) x| ^ pExp * psi.weight x ≤
        (Real.sqrt l) ^ pExp * (Psi u l mu x) ^ pExp * psi.weight x := by
  intro x
  have hdrv_le := Psi_deriv_abs_rpow_le_Psi_rpow hl hmu hpExp hu hu_nn x
  have hψ_nn : 0 ≤ psi.weight x := (psi.pos x).le
  exact mul_le_mul_of_nonneg_right hdrv_le hψ_nn

end ShenWork.Paper1

end
