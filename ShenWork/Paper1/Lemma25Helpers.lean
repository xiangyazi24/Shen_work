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

/-! ### Pointwise combined estimate (Jensen ∘ deriv-bound) -/

/-- Pointwise combined estimate: at each x,
`|Ψ'(u)(x)|^p · ψ(x) ≤ √l^p · const_J · ψ(x) · ∫_y K_{x-y} u(y)^p dy`. -/
theorem psi_deriv_pExp_weighted_le_kernel_weighted
    (psi : ExponentialWeight) {pExp l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y) :
    ∀ x : ℝ,
      |deriv (fun z => Psi u l mu z) x| ^ pExp * psi.weight x ≤
        (Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
              (2 / Real.sqrt l) ^ (pExp - 1) *
              (∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * (u y) ^ pExp)) *
          psi.weight x := by
  intro x
  have hpExp_pos : 0 < pExp := lt_of_lt_of_le zero_lt_one hpExp
  have hψ_nn : 0 ≤ psi.weight x := (psi.pos x).le
  have hsqrt_nn : 0 ≤ (Real.sqrt l) ^ pExp :=
    Real.rpow_nonneg (Real.sqrt_nonneg l) pExp
  have hPsi_nn : 0 ≤ (Psi u l mu x) ^ pExp :=
    Real.rpow_nonneg (Psi_nonneg hl hmu hu_nn x) pExp
  have h1 := psi_deriv_pExp_weighted_le psi hl hmu hpExp_pos hu hu_nn x
  have h2 : (Psi u l mu x) ^ pExp ≤
      (mu / (2 * Real.sqrt l)) ^ pExp *
          (2 / Real.sqrt l) ^ (pExp - 1) *
          ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * (u y) ^ pExp :=
    lemma_2_5_jensenStep u l mu pExp hl hmu hpExp hu hu_nn x
  calc |deriv (fun z => Psi u l mu z) x| ^ pExp * psi.weight x
      ≤ (Real.sqrt l) ^ pExp * (Psi u l mu x) ^ pExp * psi.weight x := h1
    _ ≤ (Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
              (2 / Real.sqrt l) ^ (pExp - 1) *
              ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * (u y) ^ pExp) *
          psi.weight x := by
        have hmul := mul_le_mul_of_nonneg_left h2 hsqrt_nn
        exact mul_le_mul_of_nonneg_right hmul hψ_nn

/-! ### Integrated form of step 2c (with explicit integrability hypotheses) -/

/-- Integrated combined estimate, given integrability on both sides.  Once
the integrability hypotheses are discharged from Fubini + the
hypothesis `Integrable (u^p · ψ)`, this completes the chain. -/
theorem psi_deriv_pExp_integral_le_kernel_weighted_integral
    (psi : ExponentialWeight) {pExp l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y)
    (hLHS_int :
      Integrable
        (fun x : ℝ =>
          |deriv (fun z => Psi u l mu z) x| ^ pExp * psi.weight x))
    (hRHS_int :
      Integrable
        (fun x : ℝ =>
          (Real.sqrt l) ^ pExp *
            ((mu / (2 * Real.sqrt l)) ^ pExp *
                (2 / Real.sqrt l) ^ (pExp - 1) *
                (∫ y : ℝ,
                  Real.exp (-Real.sqrt l * |x - y|) * (u y) ^ pExp)) *
            psi.weight x)) :
    ∫ x : ℝ, |deriv (fun z => Psi u l mu z) x| ^ pExp * psi.weight x ≤
      ∫ x : ℝ,
        (Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
              (2 / Real.sqrt l) ^ (pExp - 1) *
              (∫ y : ℝ,
                Real.exp (-Real.sqrt l * |x - y|) * (u y) ^ pExp)) *
          psi.weight x := by
  refine MeasureTheory.integral_mono hLHS_int hRHS_int ?_
  intro x
  exact psi_deriv_pExp_weighted_le_kernel_weighted psi hl hmu hpExp hu hu_nn x

/-! ### Fubini-conditional final assembly -/

/-- Conditional Lemma 2.5 with explicit k < √l:  given that the
double-integral form on the right is already known to equal the expected
ψ-weighted form (via Fubini + `kernel_weight_integral_le_psi`), the
combined integral inequality lifts step 2c to its weighted target.
The conditional hypothesis `hFubini_le` packages the Fubini and
weight-transfer reductions in a single inequality so this lemma can be
used while the Fubini bookkeeping is built up. -/
theorem Lemma_2_5_with_explicit_k_via_Fubini_hypothesis
    (psi : ExponentialWeight) {pExp gamma l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    {u : ℝ → ℝ} (hu : IsCUnifBdd (fun y => (u y) ^ gamma))
    (hu_nn : ∀ y, 0 ≤ (u y) ^ gamma)
    (hLHS_int :
      Integrable
        (fun x : ℝ =>
          |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
            psi.weight x))
    (hRHS_int :
      Integrable
        (fun x : ℝ =>
          (Real.sqrt l) ^ pExp *
            ((mu / (2 * Real.sqrt l)) ^ pExp *
                (2 / Real.sqrt l) ^ (pExp - 1) *
                (∫ y : ℝ,
                  Real.exp (-Real.sqrt l * |x - y|) * ((u y) ^ gamma) ^ pExp)) *
            psi.weight x))
    {C : ℝ}
    (hFubini_le :
      (∫ x : ℝ,
        (Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
              (2 / Real.sqrt l) ^ (pExp - 1) *
              (∫ y : ℝ,
                Real.exp (-Real.sqrt l * |x - y|) * ((u y) ^ gamma) ^ pExp)) *
          psi.weight x) ≤
        C * ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x) :
    ∫ x : ℝ,
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x ≤
      C * ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x := by
  have hstep3 :=
    psi_deriv_pExp_integral_le_kernel_weighted_integral
      (psi := psi) (pExp := pExp) (l := l) (mu := mu)
      hl hmu hpExp hu hu_nn hLHS_int hRHS_int
  exact le_trans hstep3 hFubini_le

/-! ### Domination integrand for joint Fubini -/

/-- The pointwise bound for the joint integrand `ψ(x) · K_{x-y} · v(y)`
where `v = (u^γ)^p`.  When ψ has log-derivative bounded by `k < c`,
the joint integrand is dominated by `ψ(y) · exp((k-c)|x-y|) · v(y)`,
whose double integral collapses via Fubini to a finite multiple of
`∫_y ψ(y) v(y) dy`. -/
lemma joint_integrand_le
    (psi : ExponentialWeight) {c k : ℝ} (hc : 0 < c) (hk_nn : 0 ≤ k)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {v : ℝ → ℝ} (hv_nn : ∀ y, 0 ≤ v y) (x y : ℝ) :
    psi.weight x * Real.exp (-c * |x - y|) * v y ≤
      psi.weight y * Real.exp ((k - c) * |x - y|) * v y := by
  have hψ_le := psi.weight_ratio_le hk_nn hk_bound x y
  have hexp_nonneg : 0 ≤ Real.exp (-c * |x - y|) := (Real.exp_pos _).le
  have hv_nonneg : 0 ≤ v y := hv_nn y
  have h1 : psi.weight x * Real.exp (-c * |x - y|) ≤
      psi.weight y * Real.exp (k * |x - y|) * Real.exp (-c * |x - y|) := by
    have := mul_le_mul_of_nonneg_right hψ_le hexp_nonneg
    linarith
  have h2 :
      psi.weight y * Real.exp (k * |x - y|) * Real.exp (-c * |x - y|) =
        psi.weight y * Real.exp ((k - c) * |x - y|) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h2] at h1
  exact mul_le_mul_of_nonneg_right h1 hv_nonneg

/-! ### Integrability of ExponentialWeight on the line -/

/-- An `ExponentialWeight` ψ is integrable on `ℝ` (Lebesgue measure): the
`decay` field gives `ψ(x) ≤ exp(-k|x|)` for some `k > 0`, and the
exponential bound is integrable. -/
theorem ExponentialWeight.integrable (psi : ExponentialWeight) :
    Integrable psi.weight := by
  obtain ⟨k, hk_pos, hψ_le⟩ := psi.decay
  have h_meas : Measurable psi.weight :=
    (psi.smooth.differentiable two_ne_zero).continuous.measurable
  have h_exp_int : Integrable (fun x : ℝ => Real.exp (-k * |x|)) := by
    have : (fun x : ℝ => Real.exp (-k * |x|)) =
        (fun x : ℝ => Real.exp (-k * |0 - x|)) := by
      funext x; rw [zero_sub, abs_neg]
    rw [this]
    exact _root_.kernel_exp_neg_mul_abs_integrable hk_pos 0
  refine h_exp_int.mono' h_meas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (psi.pos x).le]
  exact hψ_le x

/-! ### Integrability of `ψ(x) · K_{x-y}` for each `y` -/

/-- For each `y ∈ ℝ`, the function `x ↦ ψ(x) · exp(-c|x-y|)` is
integrable on `ℝ` (dominated by `ψ` × bounded factor `exp ≤ 1`). -/
theorem ExponentialWeight.kernel_integrable
    (psi : ExponentialWeight) {c : ℝ} (_hc : 0 < c) (y : ℝ) :
    Integrable (fun x : ℝ => psi.weight x * Real.exp (-c * |x - y|)) := by
  have hψ_int : Integrable psi.weight := psi.integrable
  have h_meas_psi : Measurable psi.weight :=
    (psi.smooth.differentiable two_ne_zero).continuous.measurable
  have h_meas_exp : Measurable (fun x : ℝ => Real.exp (-c * |x - y|)) := by
    fun_prop
  refine hψ_int.mono' (h_meas_psi.mul h_meas_exp).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hψ_nn : 0 ≤ psi.weight x := (psi.pos x).le
  have hexp_nn : 0 ≤ Real.exp (-c * |x - y|) := (Real.exp_pos _).le
  have hexp_le_one : Real.exp (-c * |x - y|) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have habs_nn : 0 ≤ |x - y| := abs_nonneg _
    have hc_nn : 0 ≤ c := _hc.le
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hψ_nn hexp_nn)]
  calc psi.weight x * Real.exp (-c * |x - y|)
      ≤ psi.weight x * 1 := mul_le_mul_of_nonneg_left hexp_le_one hψ_nn
    _ = psi.weight x := by ring
    _ ≤ |psi.weight x| := le_abs_self _

/-! ### Joint integrability of `ψ(x) · K_{x-y} · v(y)` -/

/-- The joint function `(x, y) ↦ ψ(x) · exp(-c|x-y|) · v(y)` is integrable
on `volume.prod volume`, provided `ψ` has log-derivative bounded by `k < c`
and `ψ · v` is integrable.  Proven via `integrable_prod_iff'` with
domination by `kernel_weight_integral_le_psi`. -/
theorem joint_kernel_weight_v_integrable
    (psi : ExponentialWeight) {c k : ℝ} (hc : 0 < c) (hk_nn : 0 ≤ k)
    (hk_lt : k < c)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {v : ℝ → ℝ} (hv_nn : ∀ y, 0 ≤ v y) (hv_meas : Measurable v)
    (hv_int : Integrable (fun y : ℝ => psi.weight y * v y)) :
    Integrable
      (Function.uncurry
        (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y))
      (MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.volume) := by
  have h_meas_psi : Measurable psi.weight :=
    (psi.smooth.differentiable two_ne_zero).continuous.measurable
  have h_meas_uncurry :
      Measurable
        (Function.uncurry
          (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y)) := by
    unfold Function.uncurry
    have hf : Measurable (fun p : ℝ × ℝ => psi.weight p.1) :=
      h_meas_psi.comp measurable_fst
    have hg : Measurable (fun p : ℝ × ℝ => Real.exp (-c * |p.1 - p.2|)) := by
      fun_prop
    have hh : Measurable (fun p : ℝ × ℝ => v p.2) :=
      hv_meas.comp measurable_snd
    exact (hf.mul hg).mul hh
  refine (MeasureTheory.integrable_prod_iff' h_meas_uncurry.aestronglyMeasurable).mpr
    ⟨?_, ?_⟩
  · -- ∀ᵐ y, Integrable (fun x => f(x, y))
    refine Filter.Eventually.of_forall fun y => ?_
    -- f(x, y) = ψ(x) · exp(-c|x-y|) · v(y) = (ψ(x) · exp(-c|x-y|)) · v(y)
    have h_eq :
        (fun x : ℝ =>
          Function.uncurry
            (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y)
            (x, y)) =
          (fun x : ℝ => v y * (psi.weight x * Real.exp (-c * |x - y|))) := by
      funext x
      unfold Function.uncurry
      ring
    rw [h_eq]
    exact (psi.kernel_integrable hc y).const_mul (v y)
  · -- Integrable (fun y => ∫ x, ‖f(x, y)‖)
    -- Bound by v(y) · ψ(y) · 2/(c-k)
    have h_bound : ∀ y, ∫ x, ‖Function.uncurry
        (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y) (x, y)‖ ≤
          v y * (psi.weight y * (2 / (c - k))) := by
      intro y
      have h_nonneg : ∀ x : ℝ,
          0 ≤ Function.uncurry
            (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y)
            (x, y) := by
        intro x
        unfold Function.uncurry
        exact mul_nonneg (mul_nonneg (psi.pos x).le (Real.exp_pos _).le) (hv_nn y)
      have h_norm_eq :
          (fun x : ℝ => ‖Function.uncurry
            (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y)
            (x, y)‖) =
            (fun x : ℝ => v y * (psi.weight x * Real.exp (-c * |x - y|))) := by
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (h_nonneg x)]
        unfold Function.uncurry
        ring
      rw [h_norm_eq]
      rw [MeasureTheory.integral_const_mul]
      have h_kw := kernel_weight_integral_le_psi psi hc hk_nn hk_lt hk_bound y
      exact mul_le_mul_of_nonneg_left h_kw (hv_nn y)
    -- Now show Integrable (fun y => ∫ x, ‖...‖)
    refine MeasureTheory.Integrable.mono'
      ((hv_int.const_mul (2 / (c - k))).congr ?_) ?_ ?_
    · -- (2/(c-k)) * (ψ y * v y) =ᵃᵉ v y * (ψ y * 2/(c-k))
      refine Filter.Eventually.of_forall fun y => ?_
      ring
    · -- AEStronglyMeasurable of (fun y => ∫ x, ‖...‖ ∂volume)
      have h_meas : Measurable
          (fun y : ℝ => ∫ x : ℝ, ‖Function.uncurry
            (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y)
            (x, y)‖) := by
        have h_unc_norm : Measurable
            (Function.uncurry
              (fun x y : ℝ => ‖psi.weight x * Real.exp (-c * |x - y|) * v y‖)) := by
          have := h_meas_uncurry
          exact this.norm
        exact h_unc_norm.integral_prod_right'
      exact h_meas.aestronglyMeasurable
    · -- ∀ᵐ y, |∫ x, ‖...‖| ≤ v y * (ψ y * 2/(c-k))
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs]
      have h_int_nn : 0 ≤ ∫ x, ‖Function.uncurry
          (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y)
          (x, y)‖ :=
        MeasureTheory.integral_nonneg (fun x => norm_nonneg _)
      rw [abs_of_nonneg h_int_nn]
      exact h_bound y

end ShenWork.Paper1

end
