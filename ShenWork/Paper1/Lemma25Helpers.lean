/-
  ShenWork/Paper1/Lemma25Helpers.lean

  Helpers for the Lemma 2.5 main-chain assembly (TASK_QUEUE Slot A).
  Kept in a separate file so concurrent edits to Paper1/Statements.lean
  don't race over them.
-/
import ShenWork.Paper1.Statements
import ShenWork.PDE.ResolventEstimate

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-! ### Laplace-kernel integral with the integration variable in front -/

lemma kernel_exp_combine_integrable
    {c k : ℝ} (hk_lt : k < c) (y : ℝ) :
    Integrable (fun x : ℝ => Real.exp ((k - c) * |x - y|)) := by
  exact
    ShenWork.PDE.ResolventEstimate.weightedResolventKernelEnvelope_integrable
      hk_lt y

lemma integral_exp_combine_eq
    {c k : ℝ} (hk_lt : k < c) (y : ℝ) :
    (∫ x : ℝ, Real.exp ((k - c) * |x - y|)) = 2 / (c - k) := by
  simpa [ShenWork.PDE.ResolventEstimate.wholeLineResolventWeightConstant] using
    ShenWork.PDE.ResolventEstimate.weightedResolventKernelEnvelope_integral_eq
      hk_lt y

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
  have hLHS_nn : 0 ≤ psi.weight x * Real.exp (-c * |x - y|) :=
    mul_nonneg hψ_nn hexp_nn
  rw [Real.norm_eq_abs, abs_of_nonneg hLHS_nn]
  have h1 := mul_le_mul_of_nonneg_left hexp_le_one hψ_nn
  linarith

/-! ### Named derivative envelope for `ExponentialWeight` -/

/-- The derivative-bound witness carried by an `ExponentialWeight`.

The paper notation behind the weighted resolvent step uses a bound commonly
written as `k_dab`; the structure stores it existentially in `deriv_abs_le`.
This selector exposes that witness without strengthening the weight class. -/
noncomputable def ExponentialWeight.k_dab (psi : ExponentialWeight) : ℝ :=
  Classical.choose psi.deriv_abs_le

theorem ExponentialWeight.k_dab_pos (psi : ExponentialWeight) :
    0 < psi.k_dab :=
  (Classical.choose_spec psi.deriv_abs_le).1

theorem ExponentialWeight.k_dab_nonneg (psi : ExponentialWeight) :
    0 ≤ psi.k_dab :=
  (psi.k_dab_pos).le

theorem ExponentialWeight.deriv_abs_le_k_dab (psi : ExponentialWeight) :
    ∀ x, |deriv psi.weight x| ≤ psi.k_dab * psi.weight x :=
  (Classical.choose_spec psi.deriv_abs_le).2

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
      have h_kw_raw :=
        kernel_weight_integral_le_psi psi hc hk_nn hk_lt hk_bound y
      -- h_kw_raw integrand is `exp(-c|x-y|) * ψ(x)`; flip to `ψ(x) * exp(-c|x-y|)`
      have h_kw :
          ∫ x : ℝ, psi.weight x * Real.exp (-c * |x - y|) ≤
            psi.weight y * (2 / (c - k)) := by
        have h_eq :
            (fun x : ℝ => psi.weight x * Real.exp (-c * |x - y|)) =
              (fun x : ℝ => Real.exp (-c * |x - y|) * psi.weight x) := by
          funext x; ring
        rw [h_eq]
        exact h_kw_raw
      exact mul_le_mul_of_nonneg_left h_kw (hv_nn y)
    -- Now show Integrable (fun y => ∫ x, ‖...‖)
    set g : ℝ → ℝ := fun y => 2 / (c - k) * (psi.weight y * v y) with hg_def
    have hg_int : Integrable g := hv_int.const_mul (2 / (c - k))
    refine MeasureTheory.Integrable.mono' hg_int ?_ ?_
    · -- AEStronglyMeasurable of (fun y => ∫ x, ‖...‖ ∂volume)
      have h_unc_norm_strong : StronglyMeasurable
          (Function.uncurry
            (fun x y : ℝ => ‖psi.weight x * Real.exp (-c * |x - y|) * v y‖)) :=
        h_meas_uncurry.norm.stronglyMeasurable
      exact (MeasureTheory.StronglyMeasurable.integral_prod_left
        h_unc_norm_strong).aestronglyMeasurable
    · -- ∀ᵐ y, ‖∫ x, ‖f‖‖ ≤ g y
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs]
      have h_int_nn : 0 ≤ ∫ x, ‖Function.uncurry
          (fun x y : ℝ => psi.weight x * Real.exp (-c * |x - y|) * v y)
          (x, y)‖ :=
        MeasureTheory.integral_nonneg (fun x => norm_nonneg _)
      rw [abs_of_nonneg h_int_nn]
      have h_g_eq : g y = v y * (psi.weight y * (2 / (c - k))) := by
        show 2 / (c - k) * (psi.weight y * v y) =
          v y * (psi.weight y * (2 / (c - k)))
        ring
      rw [h_g_eq]
      exact h_bound y

/-! ### Fubini swap + weight transfer (the Step 6 reduction) -/

/-- The Fubini + weight-transfer step:
`∫_x ψ(x) · (∫_y K_{x-y} · v(y) dy) dx ≤ ψ(y)-weighted ∫ v · 2/(c-k)`.
Joint integrability comes from `joint_kernel_weight_v_integrable`;
the inner ∫ y bound comes from `kernel_weight_integral_le_psi`. -/
theorem kernel_v_psi_double_integral_le
    (psi : ExponentialWeight) {c k : ℝ} (hc : 0 < c) (hk_nn : 0 ≤ k)
    (hk_lt : k < c)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {v : ℝ → ℝ} (hv_nn : ∀ y, 0 ≤ v y) (hv_meas : Measurable v)
    (hv_int : Integrable (fun y : ℝ => psi.weight y * v y)) :
    (∫ x : ℝ, psi.weight x *
        (∫ y : ℝ, Real.exp (-c * |x - y|) * v y)) ≤
      2 / (c - k) * ∫ y : ℝ, psi.weight y * v y := by
  set f : ℝ → ℝ → ℝ :=
    fun x y => psi.weight x * Real.exp (-c * |x - y|) * v y
  have hjoint :=
    joint_kernel_weight_v_integrable psi hc hk_nn hk_lt hk_bound hv_nn hv_meas hv_int
  -- LHS: ψ(x) · ∫_y K(x,y) · v(y) dy = ∫_y f(x,y) dy
  have hLHS_eq :
      (fun x : ℝ => psi.weight x *
        (∫ y : ℝ, Real.exp (-c * |x - y|) * v y)) =
        (fun x : ℝ => ∫ y : ℝ, f x y) := by
    funext x
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    show psi.weight x * (Real.exp (-c * |x - y|) * v y) =
      psi.weight x * Real.exp (-c * |x - y|) * v y
    ring
  rw [hLHS_eq]
  -- Apply Fubini swap
  rw [MeasureTheory.integral_integral_swap hjoint]
  -- Now: ∫_y ∫_x f(x,y) dx dy ≤ ∫_y ψ(y) · v(y) · 2/(c-k) dy
  -- Inner: ∫_x f(x,y) = ∫_x ψ(x) K(x,y) v(y) dx = v(y) · ∫_x ψ(x) K(x,y) dx ≤ v(y) · ψ(y) · 2/(c-k)
  have h_inner_bound : ∀ y : ℝ,
      ∫ x : ℝ, f x y ≤ v y * (psi.weight y * (2 / (c - k))) := by
    intro y
    have h_eq :
        (fun x : ℝ => f x y) =
          (fun x : ℝ => v y * (psi.weight x * Real.exp (-c * |x - y|))) := by
      funext x
      show psi.weight x * Real.exp (-c * |x - y|) * v y =
        v y * (psi.weight x * Real.exp (-c * |x - y|))
      ring
    rw [h_eq, MeasureTheory.integral_const_mul]
    have h_kw_raw :=
      kernel_weight_integral_le_psi psi hc hk_nn hk_lt hk_bound y
    have h_kw :
        ∫ x : ℝ, psi.weight x * Real.exp (-c * |x - y|) ≤
          psi.weight y * (2 / (c - k)) := by
      have h_flip :
          (fun x : ℝ => psi.weight x * Real.exp (-c * |x - y|)) =
            (fun x : ℝ => Real.exp (-c * |x - y|) * psi.weight x) := by
        funext x; ring
      rw [h_flip]
      exact h_kw_raw
    exact mul_le_mul_of_nonneg_left h_kw (hv_nn y)
  have hint_LHS : Integrable (fun y : ℝ => ∫ x : ℝ, f x y) :=
    hjoint.integral_prod_right
  have hint_RHS : Integrable
      (fun y : ℝ => v y * (psi.weight y * (2 / (c - k)))) := by
    have : (fun y : ℝ => v y * (psi.weight y * (2 / (c - k)))) =
        (fun y : ℝ => (2 / (c - k)) * (psi.weight y * v y)) := by
      funext y; ring
    rw [this]
    exact hv_int.const_mul _
  have hbound :
      ∫ y : ℝ, ∫ x : ℝ, f x y ≤
        ∫ y : ℝ, v y * (psi.weight y * (2 / (c - k))) :=
    MeasureTheory.integral_mono hint_LHS hint_RHS h_inner_bound
  -- Simplify RHS to 2/(c-k) · ∫ψv
  have hRHS_eq :
      ∫ y : ℝ, v y * (psi.weight y * (2 / (c - k))) =
        2 / (c - k) * ∫ y : ℝ, psi.weight y * v y := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y; ring
  rw [hRHS_eq] at hbound
  exact hbound

/-! ### RHS integrability discharge for Step 4 -/

/-- The RHS function `(√l)^p · C_J · (∫_y K v) · ψ(x)` is integrable in x.
Reduces via `Integrable.integral_prod_left` on the joint integrability
from `joint_kernel_weight_v_integrable`. -/
theorem psi_kernel_v_integral_integrable
    (psi : ExponentialWeight) {c k : ℝ} (hc : 0 < c) (hk_nn : 0 ≤ k)
    (hk_lt : k < c)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {v : ℝ → ℝ} (hv_nn : ∀ y, 0 ≤ v y) (hv_meas : Measurable v)
    (hv_int : Integrable (fun y : ℝ => psi.weight y * v y)) :
    Integrable
      (fun x : ℝ => psi.weight x *
        (∫ y : ℝ, Real.exp (-c * |x - y|) * v y)) := by
  set f : ℝ → ℝ → ℝ :=
    fun x y => psi.weight x * Real.exp (-c * |x - y|) * v y
  have hjoint :=
    joint_kernel_weight_v_integrable psi hc hk_nn hk_lt hk_bound hv_nn hv_meas hv_int
  -- Show the function in x equals (fun x => ∫ y, f x y)
  have h_eq :
      (fun x : ℝ => psi.weight x *
        (∫ y : ℝ, Real.exp (-c * |x - y|) * v y)) =
        (fun x : ℝ => ∫ y : ℝ, f x y) := by
    funext x
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    show psi.weight x * (Real.exp (-c * |x - y|) * v y) =
      psi.weight x * Real.exp (-c * |x - y|) * v y
    ring
  rw [h_eq]
  exact hjoint.integral_prod_left

/-! ### Final Lemma 2.5 with explicit k -/

/-- **Lemma 2.5 with explicit `k < √l`**: full weighted resolvent-gradient
estimate, assembled from the step 2c pointwise bound, step 7a RHS
integrability, step 6 Fubini swap + weight transfer, and step 4 le_trans
wrapper.  Constant `C := √l^p · (μ/(2√l))^p · (2/√l)^(p-1) · 2/(√l - k)`. -/
theorem Lemma_2_5_with_explicit_k
    (psi : ExponentialWeight) {pExp gamma l mu k : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    (hgamma : 0 < gamma) (hk_nn : 0 ≤ k)
    (hk_lt : k < Real.sqrt l)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y)
    (hint_hyp :
      Integrable
        (fun x : ℝ => ((u x) ^ gamma) ^ pExp * psi.weight x)) :
    Integrable
      (fun x : ℝ =>
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x) ∧
    ∫ x : ℝ,
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x ≤
      ((Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
            (2 / Real.sqrt l) ^ (pExp - 1) *
            (2 / (Real.sqrt l - k)))) *
        ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x := by
  set c : ℝ := Real.sqrt l with hc_def
  have hc_pos : 0 < c := Real.sqrt_pos.mpr hl
  have hpExp_pos : 0 < pExp := lt_of_lt_of_le zero_lt_one hpExp
  have hu_gamma_nn : ∀ y, 0 ≤ (u y) ^ gamma := fun y =>
    Real.rpow_nonneg (hu_nn y) gamma
  have hu_gamma_bdd : IsCUnifBdd (fun y => (u y) ^ gamma) := by
    rcases hu.2 with ⟨M, hM⟩
    exact ⟨hu.1.rpow_const (fun y => Or.inr hgamma.le),
      ⟨M ^ gamma, fun y => by
        rw [abs_of_nonneg (hu_gamma_nn y)]
        have hM_nn : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
        exact Real.rpow_le_rpow (hu_nn y)
          (by simpa [abs_of_nonneg (hu_nn y)] using hM y) hgamma.le⟩⟩
  set v : ℝ → ℝ := fun y => ((u y) ^ gamma) ^ pExp with hv_def
  have hv_nn : ∀ y, 0 ≤ v y := fun y => Real.rpow_nonneg (hu_gamma_nn y) pExp
  have h_u_gamma_cont : Continuous (fun y => (u y) ^ gamma) :=
    hu.1.rpow_const (fun y => Or.inr hgamma.le)
  have h_v_cont : Continuous v := by
    rw [hv_def]
    exact h_u_gamma_cont.rpow_const (fun y => Or.inr hpExp_pos.le)
  have hv_meas : Measurable v := h_v_cont.measurable
  have hv_int :
      Integrable (fun y : ℝ => psi.weight y * v y) := by
    have h_eq : (fun x : ℝ => ((u x) ^ gamma) ^ pExp * psi.weight x) =
        (fun y : ℝ => psi.weight y * v y) := by
      funext y
      show ((u y) ^ gamma) ^ pExp * psi.weight y = psi.weight y * v y
      rw [hv_def]; ring
    rw [h_eq] at hint_hyp
    exact hint_hyp
  have hRHS_int_bare :
      Integrable
        (fun x : ℝ => psi.weight x *
          (∫ y : ℝ, Real.exp (-c * |x - y|) * v y)) :=
    psi_kernel_v_integral_integrable psi hc_pos hk_nn hk_lt hk_bound hv_nn hv_meas hv_int
  set Cinner : ℝ :=
    (mu / (2 * Real.sqrt l)) ^ pExp *
      (2 / Real.sqrt l) ^ (pExp - 1) with hCinner_def
  set Couter : ℝ := (Real.sqrt l) ^ pExp with hCouter_def
  have hRHS_int_full :
      Integrable
        (fun x : ℝ =>
          Couter *
            (Cinner *
              (∫ y : ℝ,
                Real.exp (-Real.sqrt l * |x - y|) * ((u y) ^ gamma) ^ pExp)) *
            psi.weight x) := by
    have h_eq :
        (fun x : ℝ =>
            Couter *
              (Cinner *
                (∫ y : ℝ,
                  Real.exp (-Real.sqrt l * |x - y|) * ((u y) ^ gamma) ^ pExp)) *
              psi.weight x) =
          (fun x : ℝ =>
            (Couter * Cinner) *
              (psi.weight x *
                (∫ y : ℝ,
                  Real.exp (-c * |x - y|) * v y))) := by
      funext x
      show Couter *
            (Cinner *
              (∫ y : ℝ,
                Real.exp (-Real.sqrt l * |x - y|) * ((u y) ^ gamma) ^ pExp)) *
            psi.weight x =
          (Couter * Cinner) *
            (psi.weight x *
              (∫ y : ℝ,
                Real.exp (-c * |x - y|) * v y))
      rw [hc_def, hv_def]
      ring
    rw [h_eq]
    exact hRHS_int_bare.const_mul (Couter * Cinner)
  have h_deriv_meas :
      Measurable (deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z)) :=
    measurable_deriv _
  have h_psi_meas : Measurable psi.weight :=
    (psi.smooth.differentiable two_ne_zero).continuous.measurable
  have h_abs_meas : Measurable
      (fun x : ℝ => |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x|) := by
    have := h_deriv_meas.norm
    simpa [Real.norm_eq_abs] using this
  have h_abs_pow_meas : Measurable
      (fun x : ℝ =>
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp) :=
    h_abs_meas.pow_const pExp
  have hLHS_meas :
      Measurable
        (fun x : ℝ =>
          |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
            psi.weight x) :=
    h_abs_pow_meas.mul h_psi_meas
  have hLHS_int :
      Integrable
        (fun x : ℝ =>
          |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
            psi.weight x) := by
    refine hRHS_int_full.mono' hLHS_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    have hbd := psi_deriv_pExp_weighted_le_kernel_weighted psi (u := fun y => (u y)^gamma)
      hl hmu hpExp hu_gamma_bdd hu_gamma_nn x
    have hψ_nn : 0 ≤ psi.weight x := (psi.pos x).le
    have h_LHS_nn :
        0 ≤ |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
            psi.weight x :=
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) pExp) hψ_nn
    rw [Real.norm_eq_abs, abs_of_nonneg h_LHS_nn]
    show |deriv _ x| ^ pExp * psi.weight x ≤
        Couter *
          (Cinner *
            (∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * ((u y) ^ gamma) ^ pExp)) *
          psi.weight x
    rw [hCouter_def, hCinner_def]
    exact hbd
  have hFub := kernel_v_psi_double_integral_le psi hc_pos hk_nn hk_lt hk_bound
    hv_nn hv_meas hv_int
  set C : ℝ := Couter * Cinner * (2 / (c - k)) with hC_def
  have hCinner_nn : 0 ≤ Cinner := by
    rw [hCinner_def]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  have hCouter_nn : 0 ≤ Couter := by
    rw [hCouter_def]
    exact Real.rpow_nonneg (Real.sqrt_nonneg l) _
  have hC_outer_inner_nn : 0 ≤ Couter * Cinner := mul_nonneg hCouter_nn hCinner_nn
  have hFub_scaled :
      (Couter * Cinner) *
        (∫ x : ℝ, psi.weight x *
          (∫ y : ℝ, Real.exp (-c * |x - y|) * v y)) ≤
      C * ∫ y : ℝ, psi.weight y * v y := by
    rw [hC_def]
    have := mul_le_mul_of_nonneg_left hFub hC_outer_inner_nn
    linarith
  have hRHS_int_eq :
      ∫ x : ℝ,
          Couter *
            (Cinner *
              (∫ y : ℝ,
                Real.exp (-Real.sqrt l * |x - y|) * ((u y) ^ gamma) ^ pExp)) *
            psi.weight x =
        (Couter * Cinner) *
          ∫ x : ℝ, psi.weight x *
            (∫ y : ℝ, Real.exp (-c * |x - y|) * v y) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    rw [hc_def, hv_def]
    ring
  have hFub_le :
      (∫ x : ℝ,
        Couter *
          (Cinner *
            (∫ y : ℝ,
              Real.exp (-Real.sqrt l * |x - y|) * ((u y) ^ gamma) ^ pExp)) *
          psi.weight x) ≤
      C * ∫ y : ℝ, psi.weight y * v y := by
    rw [hRHS_int_eq]
    exact hFub_scaled
  have h_target_RHS_eq :
      C * ∫ y : ℝ, psi.weight y * v y =
        C * ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x := by
    congr 1
    rw [hv_def]
    have h_eq :
        (fun y : ℝ => psi.weight y * ((u y) ^ gamma) ^ pExp) =
          (fun x : ℝ => ((u x) ^ gamma) ^ pExp * psi.weight x) := by
      funext y; ring
    rw [h_eq]
  rw [h_target_RHS_eq] at hFub_le
  have hassemble :=
    Lemma_2_5_with_explicit_k_via_Fubini_hypothesis (psi := psi)
      (pExp := pExp) (gamma := gamma) (l := l) (mu := mu) (C := C)
      hl hmu hpExp hu_gamma_bdd hu_gamma_nn hLHS_int hRHS_int_full hFub_le
  have hC_full_eq :
      C =
        (Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
            (2 / Real.sqrt l) ^ (pExp - 1) *
            (2 / (Real.sqrt l - k))) := by
    rw [hC_def, hCouter_def, hCinner_def, hc_def]
    ring
  rw [hC_full_eq] at hassemble
  exact ⟨hLHS_int, hassemble⟩

/-! ### Paper-form RHS for the explicit-k estimate -/

/-- Explicit-k Lemma 2.5 with the right-hand side written in the original
Paper1 power form `u^(γp)`.  The proof is just the nonnegative-base identity
`(u^γ)^p = u^(γp)` on top of `Lemma_2_5_with_explicit_k`. -/
theorem Lemma_2_5_with_explicit_k_original_power
    (psi : ExponentialWeight) {pExp gamma l mu k : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    (hgamma : 0 < gamma) (hk_nn : 0 ≤ k)
    (hk_lt : k < Real.sqrt l)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y)
    (hint_hyp :
      Integrable
        (fun x : ℝ => (u x) ^ (gamma * pExp) * psi.weight x)) :
    Integrable
      (fun x : ℝ =>
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x) ∧
    ∫ x : ℝ,
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x ≤
      ((Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
            (2 / Real.sqrt l) ^ (pExp - 1) *
            (2 / (Real.sqrt l - k)))) *
        ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x := by
  have hpow_eq :
      (fun x : ℝ => ((u x) ^ gamma) ^ pExp * psi.weight x) =
        (fun x : ℝ => (u x) ^ (gamma * pExp) * psi.weight x) := by
    funext x
    rw [← Real.rpow_mul (hu_nn x) gamma pExp]
  have hint_explicit :
      Integrable
        (fun x : ℝ => ((u x) ^ gamma) ^ pExp * psi.weight x) := by
    rw [hpow_eq]
    exact hint_hyp
  obtain ⟨hLHS_int, hmain⟩ :=
    Lemma_2_5_with_explicit_k psi hl hmu hpExp hgamma hk_nn hk_lt
      hk_bound hu hu_nn hint_explicit
  refine ⟨hLHS_int, ?_⟩
  have hintegral_eq :
      (∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x) =
        ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x := by
    rw [hpow_eq]
  rw [hintegral_eq] at hmain
  exact hmain

/-! ### `k_dab` specialization of Lemma 2.5 -/

/-- Lemma 2.5 driven by the named `k_dab` derivative envelope of a concrete
`ExponentialWeight`.  The remaining analytic smallness condition is explicit:
`k_dab < √l`. -/
theorem Lemma_2_5_with_k_dab
    (psi : ExponentialWeight) {pExp gamma l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    (hgamma : 0 < gamma) (hk_lt : psi.k_dab < Real.sqrt l)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y)
    (hint_hyp :
      Integrable
        (fun x : ℝ => (u x) ^ (gamma * pExp) * psi.weight x)) :
    Integrable
      (fun x : ℝ =>
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x) ∧
    ∫ x : ℝ,
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x ≤
      ((Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
            (2 / Real.sqrt l) ^ (pExp - 1) *
            (2 / (Real.sqrt l - psi.k_dab)))) *
        ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x :=
  Lemma_2_5_with_explicit_k_original_power psi hl hmu hpExp hgamma
    (ExponentialWeight.k_dab_nonneg psi) hk_lt
    (ExponentialWeight.deriv_abs_le_k_dab psi) hu hu_nn hint_hyp

theorem Lemma_2_5_with_k_dab_CMParams_unit
    (p : CMParams) (psi : ExponentialWeight) {pExp : ℝ}
    (hpExp : 1 ≤ pExp) (hk_lt : psi.k_dab < 1)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y)
    (hint_hyp :
      Integrable
        (fun x : ℝ => (u x) ^ (p.γ * pExp) * psi.weight x)) :
    Integrable
      (fun x : ℝ =>
        |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
          psi.weight x) ∧
    ∫ x : ℝ,
        |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
          psi.weight x ≤
      ((Real.sqrt 1) ^ pExp *
          ((1 / (2 * Real.sqrt 1)) ^ pExp *
            (2 / Real.sqrt 1) ^ (pExp - 1) *
            (2 / (Real.sqrt 1 - psi.k_dab)))) *
        ∫ x : ℝ, (u x) ^ (p.γ * pExp) * psi.weight x := by
  have hk_lt_sqrt : psi.k_dab < Real.sqrt 1 := by
    rw [Real.sqrt_one]
    exact hk_lt
  exact Lemma_2_5_with_k_dab psi (l := 1) (mu := 1)
    one_pos one_pos hpExp (lt_of_lt_of_le one_pos p.hγ)
    hk_lt_sqrt hu hu_nn hint_hyp

theorem Lemma_2_5_with_k_dab_exists_constant
    (psi : ExponentialWeight) {pExp gamma l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    (hgamma : 0 < gamma) (hk_lt : psi.k_dab < Real.sqrt l) :
    ∃ C > 0, ∀ {u : ℝ → ℝ}, IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x : ℝ => (u x) ^ (gamma * pExp) * psi.weight x) →
        Integrable
          (fun x : ℝ =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^
                pExp * psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^
                pExp * psi.weight x ≤
          C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x := by
  refine ⟨(Real.sqrt l) ^ pExp *
        ((mu / (2 * Real.sqrt l)) ^ pExp *
          (2 / Real.sqrt l) ^ (pExp - 1) *
          (2 / (Real.sqrt l - psi.k_dab))), ?_, ?_⟩
  · have hsqrt_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
    have hden_pos : 0 < Real.sqrt l - psi.k_dab := by linarith
    have hCouter_pos : 0 < (Real.sqrt l) ^ pExp :=
      Real.rpow_pos_of_pos hsqrt_pos _
    have hC1_pos : 0 < (mu / (2 * Real.sqrt l)) ^ pExp :=
      Real.rpow_pos_of_pos (by positivity) _
    have hC2_pos : 0 < (2 / Real.sqrt l) ^ (pExp - 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hC3_pos : 0 < 2 / (Real.sqrt l - psi.k_dab) := by positivity
    positivity
  · intro u hu hu_nn hint
    exact Lemma_2_5_with_k_dab psi hl hmu hpExp hgamma hk_lt
      hu hu_nn hint

theorem Lemma_2_5_with_k_dab_CMParams_unit_exists_constant
    (p : CMParams) (psi : ExponentialWeight) {pExp : ℝ}
    (hpExp : 1 ≤ pExp) (hk_lt : psi.k_dab < 1) :
    ∃ C > 0, ∀ {u : ℝ → ℝ}, IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x : ℝ => (u x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable
          (fun x : ℝ =>
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^
                pExp * psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^
                pExp * psi.weight x ≤
          C * ∫ x : ℝ, (u x) ^ (p.γ * pExp) * psi.weight x := by
  have hk_lt_sqrt : psi.k_dab < Real.sqrt 1 := by
    rw [Real.sqrt_one]
    exact hk_lt
  exact Lemma_2_5_with_k_dab_exists_constant psi (l := 1) (mu := 1)
    one_pos one_pos hpExp (lt_of_lt_of_le one_pos p.hγ) hk_lt_sqrt

/-! ### Resolvent-admissible weights

The unrestricted `ExponentialWeight` structure records only that some finite
log-derivative envelope exists.  The weighted whole-line resolvent estimate
needs that envelope below the resolvent decay rate.  This subtype keeps that
smallness as part of the weight data instead of exposing it as a per-use proof
argument. -/

/-- Exponential weights whose named derivative envelope is below the
whole-line resolvent decay rate `√l`. -/
abbrev ResolventAdmissibleExponentialWeight (l : ℝ) :=
  {psi : ExponentialWeight // psi.k_dab < Real.sqrt l}

theorem Lemma_2_5_resolventAdmissibleWeight
    {pExp gamma l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    (hgamma : 0 < gamma) (psi : ResolventAdmissibleExponentialWeight l) :
    ∃ C > 0, ∀ {u : ℝ → ℝ}, IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x : ℝ => (u x) ^ (gamma * pExp) * psi.1.weight x) →
        Integrable
          (fun x : ℝ =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^
                pExp * psi.1.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^
                pExp * psi.1.weight x ≤
          C * ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.1.weight x :=
  Lemma_2_5_with_k_dab_exists_constant psi.1 hl hmu hpExp hgamma psi.2

theorem Lemma_2_5_resolventAdmissibleWeight_CMParams_unit
    (p : CMParams) (psi : ResolventAdmissibleExponentialWeight 1)
    {pExp : ℝ} (hpExp : 1 ≤ pExp) :
    ∃ C > 0, ∀ {u : ℝ → ℝ}, IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x : ℝ => (u x) ^ (p.γ * pExp) * psi.1.weight x) →
        Integrable
          (fun x : ℝ =>
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^
                pExp * psi.1.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^
                pExp * psi.1.weight x ≤
          C * ∫ x : ℝ, (u x) ^ (p.γ * pExp) * psi.1.weight x :=
  Lemma_2_5_with_k_dab_CMParams_unit_exists_constant p psi.1 hpExp
    (by simpa [Real.sqrt_one] using psi.2)

/-! ### Paper Lemma 2.5 closure -/

/-- Paper1 Lemma 2.5 in the corrected statement shape from `Statements.lean`.
The paper's `κ₁ << 1` is witnessed here by `κ₁ < √l / 2`, which makes the
constant uniform over all admissible weights with that derivative envelope. -/
theorem lemma_2_5 : Lemma_2_5 := by
  intro pExp gamma l mu hpExp hgamma hl hmu
  set s : ℝ := Real.sqrt l with hs_def
  have hs_pos : 0 < s := by
    rw [hs_def]
    exact Real.sqrt_pos.mpr hl
  refine ⟨s / 2, by positivity, ?_⟩
  set C : ℝ :=
    s ^ pExp *
      ((mu / (2 * s)) ^ pExp *
        (2 / s) ^ (pExp - 1) *
        (4 / s)) with hC_def
  refine ⟨C, ?_, ?_⟩
  · have hCouter_pos : 0 < s ^ pExp :=
      Real.rpow_pos_of_pos hs_pos _
    have hC1_pos : 0 < (mu / (2 * s)) ^ pExp :=
      Real.rpow_pos_of_pos (by positivity) _
    have hC2_pos : 0 < (2 / s) ^ (pExp - 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hC3_pos : 0 < 4 / s := by positivity
    positivity
  · intro k hk_nn hk_small u psi hu hu_nn hk_bound _hk_second hint
    have hk_lt_sqrt : k < Real.sqrt l := by
      rw [← hs_def]
      nlinarith
    obtain ⟨hLHS_int, hmain⟩ :=
      Lemma_2_5_with_explicit_k_original_power psi hl hmu (le_of_lt hpExp)
        hgamma hk_nn hk_lt_sqrt hk_bound hu hu_nn hint
    refine ⟨hLHS_int, le_trans hmain ?_⟩
    have hden_pos : 0 < s - k := by nlinarith
    have hkernel_le : 2 / (s - k) ≤ 4 / s := by
      rw [div_le_div_iff₀ hden_pos hs_pos]
      nlinarith
    set A : ℝ :=
      s ^ pExp * ((mu / (2 * s)) ^ pExp * (2 / s) ^ (pExp - 1)) with hA_def
    have hA_nn : 0 ≤ A := by
      positivity
    have hconst_le :
        (Real.sqrt l) ^ pExp *
            ((mu / (2 * Real.sqrt l)) ^ pExp *
              (2 / Real.sqrt l) ^ (pExp - 1) *
              (2 / (Real.sqrt l - k))) ≤
          C := by
      rw [← hs_def]
      calc
        s ^ pExp *
            ((mu / (2 * s)) ^ pExp *
              (2 / s) ^ (pExp - 1) * (2 / (s - k)))
            = A * (2 / (s - k)) := by
              rw [hA_def]
              ring
        _ ≤ A * (4 / s) := mul_le_mul_of_nonneg_left hkernel_le hA_nn
        _ = C := by
              rw [hA_def, hC_def]
              ring
    have hRHS_nonneg :
        0 ≤ ∫ x : ℝ, (u x) ^ (gamma * pExp) * psi.weight x := by
      refine integral_nonneg (fun x => ?_)
      exact mul_nonneg
        (Real.rpow_nonneg (hu_nn x) (gamma * pExp))
        (psi.weight_nonneg x)
    exact mul_le_mul_of_nonneg_right hconst_le hRHS_nonneg

/-! ### Section 5 arbitrary-wave signal-derivative estimates -/

/-- Section 5 two-wave bridge: once both wave signals are identified with the
elliptic resolvent, Lemma 2.5 supplies one small-weight window and one weighted
signal-derivative constant that work for both arbitrary profiles. -/
theorem Lemma_5_3_pair_weighted_signal_derivative_from_Lemma_2_5
    (p : CMParams) {pExp : ℝ} (hpExp : 1 < pExp)
    {U₁ U₂ V₁ V₂ : ℝ → ℝ}
    (hV₁ : V₁ = frozenElliptic p U₁)
    (hV₂ : V₂ = frozenElliptic p U₂)
    (hU₁ : IsCUnifBdd U₁) (hU₂ : IsCUnifBdd U₂)
    (hU₁_nonneg : ∀ x, 0 ≤ U₁ x)
    (hU₂_nonneg : ∀ x, 0 ≤ U₂ x) :
    ∃ kMax > 0, ∃ C > 0,
      ∀ k : ℝ, 0 ≤ k → k < kMax →
      ∀ psi : ExponentialWeight,
        (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
        (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
        Integrable (fun x : ℝ => (U₁ x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable (fun x : ℝ => (U₂ x) ^ (p.γ * pExp) * psi.weight x) →
          (Integrable
              (fun x : ℝ => |deriv V₁ x| ^ pExp * psi.weight x) ∧
            ∫ x : ℝ, |deriv V₁ x| ^ pExp * psi.weight x ≤
              C * ∫ x : ℝ, (U₁ x) ^ (p.γ * pExp) * psi.weight x) ∧
          (Integrable
              (fun x : ℝ => |deriv V₂ x| ^ pExp * psi.weight x) ∧
            ∫ x : ℝ, |deriv V₂ x| ^ pExp * psi.weight x ≤
              C * ∫ x : ℝ, (U₂ x) ^ (p.γ * pExp) * psi.weight x) := by
  have hgamma_pos : 0 < p.γ := lt_of_lt_of_le zero_lt_one p.hγ
  obtain ⟨kMax, hkMax_pos, C, hC_pos, hC⟩ :=
    lemma_2_5 pExp p.γ 1 1 hpExp hgamma_pos one_pos one_pos
  refine ⟨kMax, hkMax_pos, C, hC_pos, ?_⟩
  intro k hk_nonneg hk_small psi hk_deriv hk_second hint₁ hint₂
  subst V₁
  subst V₂
  constructor
  · simpa [frozenElliptic] using
      hC k hk_nonneg hk_small U₁ psi hU₁ hU₁_nonneg hk_deriv hk_second hint₁
  · simpa [frozenElliptic] using
      hC k hk_nonneg hk_small U₂ psi hU₂ hU₂_nonneg hk_deriv hk_second hint₂

/-- Tail-bound specialization of the two-wave Section 5 bridge.  The
`IsCUnifBdd` and nonnegativity inputs required by Lemma 2.5 are discharged from
the upper-tail bounds and continuity. -/
theorem Lemma_5_3_pair_weighted_signal_derivative_of_tail_bounds
    (p : CMParams) {c pExp : ℝ} (hpExp : 1 < pExp)
    {U₁ U₂ V₁ V₂ : ℝ → ℝ}
    (_hTW₁ : IsTravelingWave p c U₁ V₁)
    (_hTW₂ : IsTravelingWave p c U₂ V₂)
    (hV₁ : V₁ = frozenElliptic p U₁)
    (hV₂ : V₂ = frozenElliptic p U₂)
    (hU₁_cont : Continuous U₁) (hU₂_cont : Continuous U₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂) :
    ∃ kMax > 0, ∃ C > 0,
      ∀ k : ℝ, 0 ≤ k → k < kMax →
      ∀ psi : ExponentialWeight,
        (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
        (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
        Integrable (fun x : ℝ => (U₁ x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable (fun x : ℝ => (U₂ x) ^ (p.γ * pExp) * psi.weight x) →
          (Integrable
              (fun x : ℝ => |deriv V₁ x| ^ pExp * psi.weight x) ∧
            ∫ x : ℝ, |deriv V₁ x| ^ pExp * psi.weight x ≤
              C * ∫ x : ℝ, (U₁ x) ^ (p.γ * pExp) * psi.weight x) ∧
          (Integrable
              (fun x : ℝ => |deriv V₂ x| ^ pExp * psi.weight x) ∧
            ∫ x : ℝ, |deriv V₂ x| ^ pExp * psi.weight x ≤
              C * ∫ x : ℝ, (U₂ x) ^ (p.γ * pExp) * psi.weight x) :=
  Lemma_5_3_pair_weighted_signal_derivative_from_Lemma_2_5 p hpExp
    hV₁ hV₂
    (hbound₁.isCUnifBdd_of_continuous hU₁_cont)
    (hbound₂.isCUnifBdd_of_continuous hU₂_cont)
    (fun x => (hbound₁.pos x).le)
    (fun x => (hbound₂.pos x).le)

/-- Regular arbitrary-wave specialization: the elliptic-resolvent
identification of both signals is discharged from the regularity bundles. -/
theorem Lemma_5_3_pair_weighted_signal_derivative_of_regular_waves
    (p : CMParams) {c pExp : ℝ} (hpExp : 1 < pExp)
    {U₁ U₂ V₁ V₂ : ℝ → ℝ}
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hreg₁ : TravelingWaveRegularity p c U₁ V₁)
    (hreg₂ : TravelingWaveRegularity p c U₂ V₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂) :
    ∃ kMax > 0, ∃ C > 0,
      ∀ k : ℝ, 0 ≤ k → k < kMax →
      ∀ psi : ExponentialWeight,
        (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
        (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
        Integrable (fun x : ℝ => (U₁ x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable (fun x : ℝ => (U₂ x) ^ (p.γ * pExp) * psi.weight x) →
          (Integrable
              (fun x : ℝ => |deriv V₁ x| ^ pExp * psi.weight x) ∧
            ∫ x : ℝ, |deriv V₁ x| ^ pExp * psi.weight x ≤
              C * ∫ x : ℝ, (U₁ x) ^ (p.γ * pExp) * psi.weight x) ∧
          (Integrable
              (fun x : ℝ => |deriv V₂ x| ^ pExp * psi.weight x) ∧
            ∫ x : ℝ, |deriv V₂ x| ^ pExp * psi.weight x ≤
              C * ∫ x : ℝ, (U₂ x) ^ (p.γ * pExp) * psi.weight x) :=
  Lemma_5_3_pair_weighted_signal_derivative_of_tail_bounds p hpExp
    hTW₁ hTW₂
    (IsTravelingWave.V_eq_frozenElliptic_full hTW₁ hbound₁ hreg₁)
    (IsTravelingWave.V_eq_frozenElliptic_full hTW₂ hbound₂ hreg₂)
    hreg₁.U_cont hreg₂.U_cont hbound₁ hbound₂

/-- Near-neighbor Section 5 signal control: for a regular target traveling
wave and an arbitrary admissible nearby initial datum, Lemma 2.5 gives one
small-weight window and one constant controlling both the target wave signal
and the frozen elliptic signal generated by the initial datum. -/
theorem Lemma_5_3_profile_initial_signal_derivative_from_Lemma_2_5
    (p : CMParams) {c pExp : ℝ} (hpExp : 1 < pExp)
    {U V u₀ : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hu₀ : NonnegativeInitialDatum u₀) :
    ∃ kMax > 0, ∃ C > 0,
      ∀ k : ℝ, 0 ≤ k → k < kMax →
      ∀ psi : ExponentialWeight,
        (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
        (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
        Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
        Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
          (Integrable
              (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
            ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
              C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
          (Integrable
              (fun x : ℝ =>
                |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
            ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                psi.weight x ≤
              C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x) :=
  Lemma_5_3_pair_weighted_signal_derivative_from_Lemma_2_5 p hpExp
    (IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg)
    rfl
    (hbound.isCUnifBdd_of_continuous hreg.U_cont)
    hu₀.1
    (fun x => (hbound.pos x).le)
    hu₀.2

/-- FRONTIER / Point 17: fixed near-neighbor branch of Theorem 1.2.

What is discharged here: Lemma 2.5 plus the Section 5 arbitrary-wave signal
estimate, including the identification of the traveling-wave signal with
`frozenElliptic p U` and the frozen elliptic signal generated by the nearby
datum `u₀`.

What remains outside this file: the nonlinear Cauchy stability principle
`hmovingFrame`, converting those signal estimates and the initial weighted
closeness into existence of a global Cauchy solution and moving-frame
convergence.  No theorem currently in the repository proves that nonlinear
moving-frame convergence from the Section 5 signal estimates alone. -/
theorem Theorem_1_2_nearby_initial_data_branch_of_signal_to_movingFrame
    (p : CMParams) {c η pExp : ℝ} (hpExp : 1 < pExp)
    {U V u₀ : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hu₀ : NonnegativeInitialDatum u₀)
    (hleft : StrictlyPositiveAtLeft u₀)
    (hclose : WeightedL2InitialCloseness η u₀ U)
    (hmovingFrame :
      NonnegativeInitialDatum u₀ →
      StrictlyPositiveAtLeft u₀ →
      WeightedL2InitialCloseness η u₀ U →
      (∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x)) →
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        WeightedL2MovingFrameConvergence η c u U ∧
        UniformMovingFrameConvergence c u U) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      WeightedL2MovingFrameConvergence η c u U ∧
      UniformMovingFrameConvergence c u U := by
  have hsignal :
      ∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x) :=
    Lemma_5_3_profile_initial_signal_derivative_from_Lemma_2_5 p hpExp
      hTW hreg hstrict.hasWaveUpperTailBound hu₀
  exact hmovingFrame hu₀ hleft hclose hsignal

/-- A pure moving-frame `L²` closure lemma: a nonnegative weighted energy
bounded eventually by any scalar function tending to zero converges to zero.
This is the analytic endpoint needed after deriving a perturbation energy
estimate. -/
theorem WeightedL2MovingFrameConvergence.of_eventual_bound_tendsto_zero
    {η c : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {B : ℝ → ℝ}
    (hB : Tendsto B atTop (𝓝 0))
    (hbound :
      ∀ᶠ t in atTop,
        ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤ B t) :
    WeightedL2MovingFrameConvergence η c u U := by
  unfold WeightedL2MovingFrameConvergence
  have hnonneg :
      ∀ᶠ t in atTop,
        0 ≤ ∫ x : ℝ, Real.exp (2 * η * x) *
          |u t x - U (x - c * t)| ^ 2 := by
    exact Eventually.of_forall fun t => by
      exact integral_nonneg fun x => by
        exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  exact squeeze_zero' hnonneg hbound hB

/-- Exponential weighted-energy decay is enough for moving-frame weighted
`L²` convergence.  The coefficient `A` is intentionally unrestricted: the
eventual upper bound itself carries any required sign information. -/
theorem WeightedL2MovingFrameConvergence.of_eventual_exponential_decay
    {η c lam A : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hlam : 0 < lam)
    (hdecay :
      ∀ᶠ t in atTop,
        ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
          A * Real.exp (-lam * t)) :
    WeightedL2MovingFrameConvergence η c u U := by
  have hmul0 : Tendsto (fun t : ℝ => t * lam) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hlam
  have hmul : Tendsto (fun t : ℝ => lam * t) atTop atTop := by
    simpa [mul_comm] using hmul0
  have hneg : Tendsto (fun t : ℝ => -(lam * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(lam * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hupper :
      Tendsto (fun t : ℝ => A * Real.exp (-lam * t)) atTop (𝓝 0) := by
    have hmul_exp :
        Tendsto (fun t : ℝ => A * Real.exp (-(lam * t))) atTop (𝓝 (A * 0)) :=
      tendsto_const_nhds.mul hexp
    simpa using hmul_exp
  exact
    WeightedL2MovingFrameConvergence.of_eventual_bound_tendsto_zero
      hupper hdecay

/-- Scalar Grönwall closure for a dissipative energy.  If `E' ≤ -lam E`
on every finite interval starting at `0`, then eventually
`E t ≤ E 0 * exp (-lam t)`.  Positivity of `lam` is not needed for this
finite-time estimate; it is used by downstream convergence lemmas. -/
theorem scalarEnergy_eventual_exponential_bound_of_deriv_le
    {E : ℝ → ℝ} {lam : ℝ}
    (hcont : ∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T))
    (hderiv : ∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt E (deriv E t) (Set.Ici t) t)
    (hdiss : ∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t) :
    ∀ᶠ t in atTop, E t ≤ E 0 * Real.exp (-lam * t) := by
  refine eventually_atTop.2 ⟨0, ?_⟩
  intro T hT
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) T, deriv E x ≤ -lam * E x + 0 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    simpa using hdiss x hx0
  have hslope : ∀ x ∈ Set.Ico (0 : ℝ) T, ∀ r, deriv E x < r →
      ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (E z - E x) < r := by
    intro x hx r hr
    exact (hderiv T hT x hx).liminf_right_slope_le hr
  have hgr := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := fun x => deriv E x)
    (δ := E 0) (K := -lam) (ε := 0) (a := 0) (b := T)
    (hcont T hT) hslope (le_refl _) hbound T ⟨hT, le_rfl⟩
  have hgw : gronwallBound (E 0) (-lam) 0 (T - 0) =
      E 0 * Real.exp ((-lam) * (T - 0)) := by
    rw [gronwallBound_ε0]
  rw [hgw] at hgr
  convert hgr using 1
  ring_nf

/-- Moving-frame weighted `L²` convergence from a scalar dissipative energy
that dominates the weighted perturbation energy.  This is the scalar Grönwall
part of the stability proof, separated from the PDE derivation of the
differential inequality. -/
theorem WeightedL2MovingFrameConvergence.of_energy_dissipation
    {η c lam : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {E : ℝ → ℝ}
    (hlam : 0 < lam)
    (hcontrol : ∀ᶠ t in atTop,
      ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤ E t)
    (hcont : ∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T))
    (hderiv : ∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt E (deriv E t) (Set.Ici t) t)
    (hdiss : ∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t) :
    WeightedL2MovingFrameConvergence η c u U := by
  have hE_decay : ∀ᶠ t in atTop, E t ≤ E 0 * Real.exp (-lam * t) :=
    scalarEnergy_eventual_exponential_bound_of_deriv_le hcont hderiv hdiss
  have hdecay : ∀ᶠ t in atTop,
      ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
        E 0 * Real.exp (-lam * t) := by
    filter_upwards [hcontrol, hE_decay] with t hctrl hE
    exact le_trans hctrl hE
  exact WeightedL2MovingFrameConvergence.of_eventual_exponential_decay
    hlam hdecay

/-- The remaining moving-frame upgrade needed after the weighted-energy
argument has proved weighted `L²` convergence.  This is intentionally stated
as a separate frontier package: weighted `L²` on the whole line, with an
exponential right weight, does not by itself imply uniform convergence without
additional parabolic smoothing, localization, or spectral/coercive input. -/
def WeightedL2ToUniformMovingFrameUpgrade
    (p : CMParams) (η c : ℝ) (u₀ U : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ → ℝ → ℝ,
    IsGlobalCauchySolutionFrom p u₀ u v →
    WeightedL2MovingFrameConvergence η c u U →
    UniformMovingFrameConvergence c u U

/-- A right-tail asymptotic at rate `κ₁` gives an eventual pointwise
exponential error bound against the leading tail `exp (-κx)`. -/
theorem HasWaveRightTailAsymptotic.eventually_abs_sub_exp_le
    {c κ₁ : ℝ} {U : ℝ → ℝ}
    (h : HasWaveRightTailAsymptotic c κ₁ U) :
    ∀ᶠ x in atTop,
      |U x - Real.exp (-(kappa c) * x)| ≤ Real.exp (-κ₁ * x) := by
  have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds _ zero_lt_one
  filter_upwards [h.eventually hball] with x hx
  set e : ℝ := Real.exp (-(kappa c * x))
  set r : ℝ := U x / e - 1
  have he_pos : 0 < e := by
    dsimp [e]
    exact Real.exp_pos _
  have hxle :
      |Real.exp ((κ₁ - kappa c) * x) * r| ≤ (1 : ℝ) := by
    have hxlt :
        ‖Real.exp ((κ₁ - kappa c) * x) *
            (U x / Real.exp (-(kappa c * x)) - 1)‖ < (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    exact le_of_lt (by simpa [Real.norm_eq_abs, e, r] using hxlt)
  have hprod : Real.exp ((κ₁ - kappa c) * x) * |r| ≤ (1 : ℝ) := by
    simpa [abs_mul, abs_of_nonneg (Real.exp_nonneg _)] using hxle
  have hr : |r| ≤ Real.exp (-(κ₁ - kappa c) * x) := by
    calc
      |r| =
          (Real.exp ((κ₁ - kappa c) * x))⁻¹ *
            (Real.exp ((κ₁ - kappa c) * x) * |r|) := by
            field_simp [Real.exp_ne_zero]
      _ ≤ (Real.exp ((κ₁ - kappa c) * x))⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left hprod
          (inv_nonneg.mpr (Real.exp_nonneg _))
      _ = Real.exp (-(κ₁ - kappa c) * x) := by
        rw [← Real.exp_neg, mul_one]
        congr 1
        ring
  calc
    |U x - Real.exp (-(kappa c) * x)| = e * |r| := by
      have hsub : U x - e = e * r := by
        dsimp [r]
        field_simp [ne_of_gt he_pos]
      rw [show Real.exp (-(kappa c) * x) = e by
        dsimp [e]
        congr 1
        ring, hsub, abs_mul,
        abs_of_nonneg he_pos.le]
    _ ≤ e * Real.exp (-(κ₁ - kappa c) * x) :=
      mul_le_mul_of_nonneg_left hr he_pos.le
    _ = Real.exp (-κ₁ * x) := by
      dsimp [e]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Two profiles with the same right-tail asymptotic rate differ by twice
the eventual tail-error envelope. -/
theorem HasWaveRightTailAsymptotic.eventually_abs_sub_abs_le_two_exp
    {c κ₁ : ℝ} {U₁ U₂ : ℝ → ℝ}
    (h₁ : HasWaveRightTailAsymptotic c κ₁ U₁)
    (h₂ : HasWaveRightTailAsymptotic c κ₁ U₂) :
    ∀ᶠ x in atTop,
      |U₂ x - U₁ x| ≤ 2 * Real.exp (-κ₁ * x) := by
  filter_upwards [h₁.eventually_abs_sub_exp_le,
    h₂.eventually_abs_sub_exp_le] with x hx₁ hx₂
  let E : ℝ := Real.exp (-(kappa c) * x)
  have htri :
      |U₂ x - U₁ x| ≤ |U₂ x - E| + |U₁ x - E| := by
    have h :=
      abs_sub_le (U₂ x - E) 0 (U₁ x - E)
    have hsub : (U₂ x - E) - (U₁ x - E) = U₂ x - U₁ x := by ring
    simpa [hsub, abs_neg, abs_sub_comm] using h
  calc
    |U₂ x - U₁ x| ≤ |U₂ x - E| + |U₁ x - E| := htri
    _ ≤ Real.exp (-κ₁ * x) + Real.exp (-κ₁ * x) :=
      add_le_add (by simpa [E] using hx₂) (by simpa [E] using hx₁)
    _ = 2 * Real.exp (-κ₁ * x) := by ring

/-- Common right-tail asymptotics at rate `κ₁` imply the weighted initial
closeness needed to use wave `U₂` as nearby Cauchy data for stability around
`U₁`, as long as the stability weight lies below `κ₁`. -/
theorem WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
    {p : CMParams} {c η κ₁ : ℝ} {U₁ U₂ : ℝ → ℝ}
    (hη : 0 < η) (hηκ₁ : η < κ₁)
    (hU₁_cont : Continuous U₁) (hU₂_cont : Continuous U₂)
    (hbound₁ : HasWaveUpperTailBound p c U₁)
    (hbound₂ : HasWaveUpperTailBound p c U₂)
    (htail₁ : HasWaveRightTailAsymptotic c κ₁ U₁)
    (htail₂ : HasWaveRightTailAsymptotic c κ₁ U₂) :
    WeightedL2InitialCloseness η U₂ U₁ := by
  refine
    WeightedL2InitialCloseness.of_left_exp_bound_eventual_right_exp_bound
      (η := η) (δ := 2 * (κ₁ - η)) hη (by linarith) ?_ ?_ ?_
  · exact
      (Continuous.mul
        (Real.continuous_exp.comp
          ((continuous_const.mul continuous_const).mul continuous_id))
        ((hU₂_cont.sub hU₁_cont).abs.pow 2)).aestronglyMeasurable
  · have hM_pos : 0 < MChi p :=
      lt_of_lt_of_le (hbound₁.pos 0) (hbound₁.le_MChi 0)
    refine ⟨(2 * MChi p) ^ 2, sq_nonneg _, fun x => ?_⟩
    exact
      weightedL2_integrand_norm_le_of_abs_sub_le
        (η := η) (A := 2 * MChi p)
        (u₀ := U₂) (U := U₁) (by linarith)
        (hbound₁.abs_sub_le_two_MChi hbound₂ x)
  · have hevent :
        ∀ᶠ x in atTop, |U₂ x - U₁ x| ≤ 2 * Real.exp (-κ₁ * x) :=
      htail₁.eventually_abs_sub_abs_le_two_exp htail₂
    rcases eventually_atTop.1 hevent with ⟨R, hR⟩
    refine ⟨R, 4, by norm_num, fun x hx => ?_⟩
    have habs : |U₂ x - U₁ x| ≤ 2 * Real.exp (-κ₁ * x) :=
      hR x (le_of_lt hx)
    have hraw :=
      weightedL2_integrand_norm_le_of_abs_sub_le_exp
        (η := η) (β := κ₁) (B := 2)
        (u₀ := U₂) (U := U₁) (by norm_num : (0 : ℝ) ≤ 2) habs
    convert hraw using 2
    ring

/-- FRONTIER / Point 17: weighted-`L²` part of the near-neighbor stability
branch after Lemma 2.5 and the Section 5 signal estimates.

Discharged here: the resolvent/signal side and the final passage from an
eventual exponential weighted-energy estimate to moving-frame `L²`
convergence.

Remaining deep analysis fact: derive `henergy` from the parabolic perturbation
equations, i.e. construct the Cauchy solution and prove the eventual
exponential bound for
`∫ exp(2ηx)|u(t,x)-U(x-ct)|² dx` using the Section 5 signal estimates.  The
repository currently has no weighted perturbation energy identity or Grönwall
closure for arbitrary nearby whole-line Cauchy data. -/
theorem Theorem_1_2_weightedL2_branch_of_signal_energy_decay
    (p : CMParams) {c η pExp : ℝ} (hpExp : 1 < pExp)
    {U V u₀ : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hu₀ : NonnegativeInitialDatum u₀)
    (hleft : StrictlyPositiveAtLeft u₀)
    (hclose : WeightedL2InitialCloseness η u₀ U)
    (henergy :
      NonnegativeInitialDatum u₀ →
      StrictlyPositiveAtLeft u₀ →
      WeightedL2InitialCloseness η u₀ U →
      (∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x)) →
      ∃ u v : ℝ → ℝ → ℝ, ∃ lam > 0, ∃ A : ℝ,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        ∀ᶠ t in atTop,
          ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
            A * Real.exp (-lam * t)) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      WeightedL2MovingFrameConvergence η c u U := by
  have hsignal :
      ∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x) :=
    Lemma_5_3_profile_initial_signal_derivative_from_Lemma_2_5 p hpExp
      hTW hreg hstrict.hasWaveUpperTailBound hu₀
  rcases henergy hu₀ hleft hclose hsignal with
    ⟨u, v, lam, hlam, A, hsol, hdecay⟩
  exact
    ⟨u, v, hsol,
      WeightedL2MovingFrameConvergence.of_eventual_exponential_decay
        hlam hdecay⟩

/-- FRONTIER / Point 17: same weighted-`L²` branch, but the remaining PDE
input is only a scalar energy dissipation inequality.  Lemma 2.5 and the
Section 5 signal estimates are discharged before the energy package is used;
Mathlib Grönwall then turns the dissipative inequality into the exponential
weighted-energy decay needed for moving-frame `L²` convergence.

Remaining deep analysis fact: construct such an `E` from the whole-line
parabolic perturbation equations and prove that it dominates the weighted
moving-frame `L²` error while satisfying `E' ≤ -lam E`. -/
theorem Theorem_1_2_weightedL2_branch_of_signal_energy_dissipation
    (p : CMParams) {c η pExp : ℝ} (hpExp : 1 < pExp)
    {U V u₀ : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hu₀ : NonnegativeInitialDatum u₀)
    (hleft : StrictlyPositiveAtLeft u₀)
    (hclose : WeightedL2InitialCloseness η u₀ U)
    (henergy :
      NonnegativeInitialDatum u₀ →
      StrictlyPositiveAtLeft u₀ →
      WeightedL2InitialCloseness η u₀ U →
      (∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x)) →
      ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        (∀ᶠ t in atTop,
          ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
            E t) ∧
        (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
        (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
          HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
        (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t)) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      WeightedL2MovingFrameConvergence η c u U := by
  have hsignal :
      ∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x) :=
    Lemma_5_3_profile_initial_signal_derivative_from_Lemma_2_5 p hpExp
      hTW hreg hstrict.hasWaveUpperTailBound hu₀
  rcases henergy hu₀ hleft hclose hsignal with
    ⟨u, v, E, lam, hlam, hsol, hcontrol, hcont, hderiv, hdiss⟩
  exact
    ⟨u, v, hsol,
      WeightedL2MovingFrameConvergence.of_energy_dissipation
        hlam hcontrol hcont hderiv hdiss⟩

/-- Near-neighbor Theorem 1.2 branch where Lemma 2.5, the Section 5 signal
estimates, and the scalar energy dissipation package prove the weighted
moving-frame `L²` convergence; the final uniform moving-frame conclusion is
delegated to a separate `WeightedL2ToUniformMovingFrameUpgrade`.

Remaining deep analysis fact: prove that upgrade for arbitrary nearby
whole-line Cauchy data.  A real proof should supply uniform-in-space
parabolic smoothing/localization and a stability/coercivity mechanism around
the traveling wave; this is not a formal consequence of weighted `L²`
convergence alone. -/
theorem Theorem_1_2_nearby_initial_data_branch_of_signal_energy_dissipation_of_l2_to_uniform
    (p : CMParams) {c η pExp : ℝ} (hpExp : 1 < pExp)
    {U V u₀ : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hu₀ : NonnegativeInitialDatum u₀)
    (hleft : StrictlyPositiveAtLeft u₀)
    (hclose : WeightedL2InitialCloseness η u₀ U)
    (henergy :
      NonnegativeInitialDatum u₀ →
      StrictlyPositiveAtLeft u₀ →
      WeightedL2InitialCloseness η u₀ U →
      (∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x)) →
      ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        (∀ᶠ t in atTop,
          ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
            E t) ∧
        (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
        (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
          HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
        (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t))
    (hupgrade : WeightedL2ToUniformMovingFrameUpgrade p η c u₀ U) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      WeightedL2MovingFrameConvergence η c u U ∧
      UniformMovingFrameConvergence c u U := by
  rcases
    Theorem_1_2_weightedL2_branch_of_signal_energy_dissipation
      (p := p) (c := c) (η := η) (pExp := pExp) hpExp
      hTW hstrict hreg hu₀ hleft hclose henergy with
    ⟨u, v, hsol, hweighted⟩
  exact ⟨u, v, hsol, hweighted, hupgrade u v hsol hweighted⟩

/-- Near-neighbor Theorem 1.2 branch with the weighted-`L²` part discharged
from a scalar energy dissipation package.  Compared with
`Theorem_1_2_nearby_initial_data_branch_of_signal_to_movingFrame`, the
nonlinear input no longer has to prove weighted moving-frame convergence
directly: it provides the energy control/dissipation inequality and the
uniform moving-frame convergence for the same Cauchy solution.

Remaining deep analysis fact: derive this common solution, weighted energy
package, and uniform moving-frame convergence from the whole-line perturbation
PDE.  This theorem proves that, once those inputs are available, Lemma 2.5,
the Section 5 signal estimates, scalar Grönwall, and the weighted-`L²`
component of Theorem 1.2 close without further assumptions. -/
theorem Theorem_1_2_nearby_initial_data_branch_of_signal_energy_dissipation
    (p : CMParams) {c η pExp : ℝ} (hpExp : 1 < pExp)
    {U V u₀ : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hu₀ : NonnegativeInitialDatum u₀)
    (hleft : StrictlyPositiveAtLeft u₀)
    (hclose : WeightedL2InitialCloseness η u₀ U)
    (henergy :
      NonnegativeInitialDatum u₀ →
      StrictlyPositiveAtLeft u₀ →
      WeightedL2InitialCloseness η u₀ U →
      (∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x)) →
      ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
        IsGlobalCauchySolutionFrom p u₀ u v ∧
        (∀ᶠ t in atTop,
          ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
            E t) ∧
        (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
        (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
          HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
        (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t) ∧
        UniformMovingFrameConvergence c u U) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      WeightedL2MovingFrameConvergence η c u U ∧
      UniformMovingFrameConvergence c u U := by
  have hsignal :
      ∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p u₀) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) * psi.weight x) :=
    Lemma_5_3_profile_initial_signal_derivative_from_Lemma_2_5 p hpExp
      hTW hreg hstrict.hasWaveUpperTailBound hu₀
  rcases henergy hu₀ hleft hclose hsignal with
    ⟨u, v, E, lam, hlam, hsol, hcontrol, hcont, hderiv, hdiss, huniform⟩
  exact
    ⟨u, v, hsol,
      WeightedL2MovingFrameConvergence.of_energy_dissipation
        hlam hcontrol hcont hderiv hdiss,
      huniform⟩

/-- Theorem 1.2 closure through the Lemma 2.5 / Section 5 signal estimates.
This isolates the remaining nonlinear stability step: once a stability
criterion consumes the signal estimates produced below, the full paper-level
Theorem 1.2 follows. -/
theorem Theorem_1_2.of_signal_derivative_stability_branch
    {pExp : ℝ} (hpExp : 1 < pExp)
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hregularity : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          TravelingWaveRegularity p c U V)
    (hstability : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          (∃ kMax > 0, ∃ C > 0,
            ∀ k : ℝ, 0 ≤ k → k < kMax →
            ∀ psi : ExponentialWeight,
              (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
              (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
              Integrable
                (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
              Integrable
                (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
                (Integrable
                    (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
                  ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                    C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
                (Integrable
                    (fun x : ℝ =>
                      |deriv (frozenElliptic p u₀) x| ^ pExp *
                        psi.weight x) ∧
                  ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                      psi.weight x ≤
                    C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) *
                      psi.weight x)) →
          ∃ u v : ℝ → ℝ → ℝ,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
            WeightedL2MovingFrameConvergence η c u U ∧
            UniformMovingFrameConvergence c u U) :
    Theorem_1_2 := by
  refine Theorem_1_2.of_assumed_stability_branch cStarStarFn hcStarStar ?_
  intro p hregime c hc U V hTW hstrict htail η hketa heta u₀ hu₀ hleft hclose
  have hreg : TravelingWaveRegularity p c U V :=
    hregularity p hregime c hc U V hTW hstrict htail η hketa heta
  exact
    Theorem_1_2_nearby_initial_data_branch_of_signal_to_movingFrame
      (p := p) (c := c) (η := η) (pExp := pExp) hpExp
      hTW hstrict hreg hu₀ hleft hclose
      (fun hu₀' hleft' hclose' hsignal =>
        hstability p hregime c hc U V u₀ hTW hstrict htail η
          hketa heta hu₀' hleft' hclose' hsignal)

/-- Theorem 1.2 closure with the weighted-`L²` stability component reduced to
a scalar energy dissipation package.

This is the main-theorem version of
`Theorem_1_2_nearby_initial_data_branch_of_signal_energy_dissipation`: the
Section 5 signal estimates and Lemma 2.5 are supplied internally, scalar
Grönwall proves weighted moving-frame `L²` convergence, and the only remaining
nonlinear stability input is a common Cauchy solution carrying both the
weighted energy dissipation inequality and uniform moving-frame convergence.

Remaining frontier: prove the `hstability` package from the whole-line
perturbation PDE.  In particular, the repository still lacks the weighted
energy identity/dissipation estimate and the separate uniform convergence
argument for arbitrary nearby Cauchy data. -/
theorem Theorem_1_2.of_signal_energy_dissipation_uniform_branch
    {pExp : ℝ} (hpExp : 1 < pExp)
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hregularity : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          TravelingWaveRegularity p c U V)
    (hstability : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          (∃ kMax > 0, ∃ C > 0,
            ∀ k : ℝ, 0 ≤ k → k < kMax →
            ∀ psi : ExponentialWeight,
              (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
              (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
              Integrable
                (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
              Integrable
                (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
                (Integrable
                    (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
                  ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                    C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
                (Integrable
                    (fun x : ℝ =>
                      |deriv (frozenElliptic p u₀) x| ^ pExp *
                        psi.weight x) ∧
                  ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                      psi.weight x ≤
                    C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) *
                      psi.weight x)) →
          ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
            (∀ᶠ t in atTop,
              ∫ x : ℝ,
                Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
                  E t) ∧
            (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
            (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
              HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
            (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t) ∧
            UniformMovingFrameConvergence c u U) :
    Theorem_1_2 := by
  refine Theorem_1_2.of_assumed_stability_branch cStarStarFn hcStarStar ?_
  intro p hregime c hc U V hTW hstrict htail η hketa heta u₀ hu₀ hleft hclose
  have hreg : TravelingWaveRegularity p c U V :=
    hregularity p hregime c hc U V hTW hstrict htail η hketa heta
  exact
    Theorem_1_2_nearby_initial_data_branch_of_signal_energy_dissipation
      (p := p) (c := c) (η := η) (pExp := pExp) hpExp
      hTW hstrict hreg hu₀ hleft hclose
      (fun hu₀' hleft' hclose' hsignal =>
        hstability p hregime c hc U V u₀ hTW hstrict htail η
          hketa heta hu₀' hleft' hclose' hsignal)

/-- Theorem 1.2 closure after reducing the main stability proof to two
separate near-neighbor analytic packages:

* a weighted energy package whose dissipation inequality is converted by
  Grönwall into moving-frame weighted `L²` convergence, using Lemma 2.5 and
  the Section 5 signal estimates internally;
* an upgrade from that weighted `L²` convergence to uniform moving-frame
  convergence for the same global Cauchy solution.

This is the sharp interface currently reachable in the repository.  The
remaining hard facts are the whole-line perturbation energy identity with a
coercive dissipation estimate, and the weighted-`L²` to uniform upgrade
(typically requiring parabolic smoothing/localization plus a spectral-gap or
nonlinear stability estimate near the wave). -/
theorem Theorem_1_2.of_signal_energy_dissipation_l2_to_uniform_branch
    {pExp : ℝ} (hpExp : 1 < pExp)
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hregularity : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          TravelingWaveRegularity p c U V)
    (henergy : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          (∃ kMax > 0, ∃ C > 0,
            ∀ k : ℝ, 0 ≤ k → k < kMax →
            ∀ psi : ExponentialWeight,
              (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
              (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
              Integrable
                (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
              Integrable
                (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
                (Integrable
                    (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
                  ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                    C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
                (Integrable
                    (fun x : ℝ =>
                      |deriv (frozenElliptic p u₀) x| ^ pExp *
                        psi.weight x) ∧
                  ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                      psi.weight x ≤
                    C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) *
                      psi.weight x)) →
          ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
            (∀ᶠ t in atTop,
              ∫ x : ℝ,
                Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
                  E t) ∧
            (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
            (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
              HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
            (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t))
    (hupgrade : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        TravelingWaveRegularity p c U V →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          WeightedL2ToUniformMovingFrameUpgrade p η c u₀ U) :
    Theorem_1_2 := by
  refine Theorem_1_2.of_assumed_stability_branch cStarStarFn hcStarStar ?_
  intro p hregime c hc U V hTW hstrict htail η hketa heta u₀ hu₀ hleft hclose
  have hreg : TravelingWaveRegularity p c U V :=
    hregularity p hregime c hc U V hTW hstrict htail η hketa heta
  exact
    Theorem_1_2_nearby_initial_data_branch_of_signal_energy_dissipation_of_l2_to_uniform
      (p := p) (c := c) (η := η) (pExp := pExp) hpExp
      hTW hstrict hreg hu₀ hleft hclose
      (fun hu₀' hleft' hclose' hsignal =>
        henergy p hregime c hc U V u₀ hTW hstrict htail η
          hketa heta hu₀' hleft' hclose' hsignal)
      (hupgrade p hregime c hc U V u₀ hTW hstrict htail hreg η
        hketa heta hu₀ hleft hclose)

/-- Theorem 1.3 profile-uniqueness branch driven by the B5 stability chain.
The second wave is used as nearby initial data for stability around the first
wave.  Lemma 2.5 and the Section 5 estimates produce the signal package,
energy dissipation gives moving-frame weighted `L²` convergence, the explicit
`WeightedL2ToUniformMovingFrameUpgrade` gives uniform moving-frame
convergence, and Cauchy uniqueness identifies the produced solution with the
moving second wave.

Remaining deep inputs are exactly the PDE facts not proved here: the weighted
energy package, the `L²`-to-uniform moving-frame upgrade, and Cauchy
uniqueness for the whole-line Cauchy problem with traveling-wave data. -/
theorem Theorem_1_3_profile_eq_of_signal_energy_dissipation_l2_to_uniform
    (p : CMParams) {c η pExp : ℝ} (hpExp : 1 < pExp)
    {U₁ V₁ U₂ V₂ : ℝ → ℝ}
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hstrict₁ : HasStrictWaveUpperTailBound p c U₁)
    (hstrict₂ : HasStrictWaveUpperTailBound p c U₂)
    (hreg₁ : TravelingWaveRegularity p c U₁ V₁)
    (hreg₂ : TravelingWaveRegularity p c U₂ V₂)
    (hclose : WeightedL2InitialCloseness η U₂ U₁)
    (henergy :
      NonnegativeInitialDatum U₂ →
      StrictlyPositiveAtLeft U₂ →
      WeightedL2InitialCloseness η U₂ U₁ →
      (∃ kMax > 0, ∃ C > 0,
        ∀ k : ℝ, 0 ≤ k → k < kMax →
        ∀ psi : ExponentialWeight,
          (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
          (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
          Integrable (fun x : ℝ => (U₁ x) ^ (p.γ * pExp) * psi.weight x) →
          Integrable (fun x : ℝ => (U₂ x) ^ (p.γ * pExp) * psi.weight x) →
            (Integrable
                (fun x : ℝ => |deriv V₁ x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv V₁ x| ^ pExp * psi.weight x ≤
                C * ∫ x : ℝ, (U₁ x) ^ (p.γ * pExp) * psi.weight x) ∧
            (Integrable
                (fun x : ℝ =>
                  |deriv (frozenElliptic p U₂) x| ^ pExp * psi.weight x) ∧
              ∫ x : ℝ, |deriv (frozenElliptic p U₂) x| ^ pExp *
                  psi.weight x ≤
                C * ∫ x : ℝ, (U₂ x) ^ (p.γ * pExp) * psi.weight x)) →
      ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
        IsGlobalCauchySolutionFrom p U₂ u v ∧
        (∀ᶠ t in atTop,
          ∫ x : ℝ, Real.exp (2 * η * x) * |u t x - U₁ (x - c * t)| ^ 2 ≤
            E t) ∧
        (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
        (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
          HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
        (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t))
    (hupgrade : WeightedL2ToUniformMovingFrameUpgrade p η c U₂ U₁)
    (hcauchy_unique :
      ∀ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U₂ u v →
          ∀ t x, u t x = U₂ (x - c * t)) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) := by
  have hU₂_bdd : IsCUnifBdd U₂ :=
    hstrict₂.hasWaveUpperTailBound.isCUnifBdd_of_continuous hreg₂.U_cont
  have hu₂ : NonnegativeInitialDatum U₂ :=
    IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂_bdd
  have hleft₂ : StrictlyPositiveAtLeft U₂ :=
    IsTravelingWave.strictlyPositiveAtLeft hTW₂
  rcases
    Theorem_1_2_nearby_initial_data_branch_of_signal_energy_dissipation_of_l2_to_uniform
      (p := p) (c := c) (η := η) (pExp := pExp) hpExp
      hTW₁ hstrict₁ hreg₁ hu₂ hleft₂ hclose henergy hupgrade with
    ⟨u, v, hsol, _hweighted, huniform⟩
  have hconv :
      UniformMovingFrameConvergence c (fun t x => U₂ (x - c * t)) U₁ := by
    intro ε hε
    rcases huniform ε hε with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t x ht
    have hu_eq : u t x = U₂ (x - c * t) := hcauchy_unique u v hsol t x
    simpa [hu_eq] using hT t x ht
  exact
    Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent
      hconv
      (IsTravelingWave.V_eq_frozenElliptic_full hTW₁
        hstrict₁.hasWaveUpperTailBound hreg₁)
      (IsTravelingWave.V_eq_frozenElliptic_full hTW₂
        hstrict₂.hasWaveUpperTailBound hreg₂)

/-- Main Theorem 1.3 closure through the B5 Theorem 1.2 stability chain.
The common right-tail asymptotic supplies the weighted closeness of the two
profiles at a stability weight chosen between `kappa c` and both the
stability cap and the tail rate.  The rest is the stability-to-uniqueness
argument in `Theorem_1_3_profile_eq_of_signal_energy_dissipation_l2_to_uniform`.

This reaches the natural frontier for the current repository: the remaining
unproved hypotheses are the whole-line energy dissipation package, the
weighted-`L²` to uniform upgrade, and Cauchy uniqueness for the produced
global solution. -/
theorem Theorem_1_3.of_signal_energy_dissipation_l2_to_uniform_and_cauchy_unique
    {pExp : ℝ} (hpExp : 1 < pExp)
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hregularity : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          TravelingWaveRegularity p c U V)
    (henergy : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          (∃ kMax > 0, ∃ C > 0,
            ∀ k : ℝ, 0 ≤ k → k < kMax →
            ∀ psi : ExponentialWeight,
              (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
              (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
              Integrable
                (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
              Integrable
                (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
                (Integrable
                    (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
                  ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                    C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
                (Integrable
                    (fun x : ℝ =>
                      |deriv (frozenElliptic p u₀) x| ^ pExp *
                        psi.weight x) ∧
                  ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                      psi.weight x ≤
                    C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) *
                      psi.weight x)) →
          ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
            (∀ᶠ t in atTop,
              ∫ x : ℝ,
                Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
                  E t) ∧
            (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
            (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
              HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
            (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t))
    (hupgrade : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        TravelingWaveRegularity p c U V →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          WeightedL2ToUniformMovingFrameUpgrade p η c u₀ U)
    (hcauchy_unique : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        TravelingWaveRegularity p c U V →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t)) :
    Theorem_1_3 := by
  refine Theorem_1_3.of_assumed_uniqueness_branch cStarStarFn hcStarStar ?_
  intro p hregime c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hstrict₁ hstrict₂ htailPair
  rcases hcStarStar p hregime with ⟨_hasymp, hbaseline⟩
  rcases htailPair with ⟨κ₁, hκ_gt, hκ_lt_one, htail₁, htail₂⟩
  have hcap : kappa c < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) :=
    kappa_lt_stability_weight_cap_of_stabilitySpeedBaseline_lt
      hbaseline hc
  rcases exists_between (lt_min hκ_gt hcap) with ⟨η, hketa, heta_min⟩
  have heta_tail : η < κ₁ := lt_of_lt_of_le heta_min (min_le_left _ _)
  have heta_cap : η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) :=
    lt_of_lt_of_le heta_min (min_le_right _ _)
  have htail₁_exists :
      ∃ κ, kappa c < κ ∧ κ < 1 ∧ HasWaveRightTailAsymptotic c κ U₁ :=
    ⟨κ₁, hκ_gt, hκ_lt_one, htail₁⟩
  have htail₂_exists :
      ∃ κ, kappa c < κ ∧ κ < 1 ∧ HasWaveRightTailAsymptotic c κ U₂ :=
    ⟨κ₁, hκ_gt, hκ_lt_one, htail₂⟩
  have hreg₁ : TravelingWaveRegularity p c U₁ V₁ :=
    hregularity p hregime c hc U₁ V₁ hTW₁ hstrict₁ htail₁_exists
      η hketa heta_cap
  have hreg₂ : TravelingWaveRegularity p c U₂ V₂ :=
    hregularity p hregime c hc U₂ V₂ hTW₂ hstrict₂ htail₂_exists
      η hketa heta_cap
  have hclose : WeightedL2InitialCloseness η U₂ U₁ :=
    WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
      (eta_pos_of_stability_weight_hypotheses hbaseline hc hketa)
      heta_tail hreg₁.U_cont hreg₂.U_cont
      hstrict₁.hasWaveUpperTailBound hstrict₂.hasWaveUpperTailBound
      htail₁ htail₂
  have hU₂_bdd : IsCUnifBdd U₂ :=
    hstrict₂.hasWaveUpperTailBound.isCUnifBdd_of_continuous hreg₂.U_cont
  have hu₂ : NonnegativeInitialDatum U₂ :=
    IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂_bdd
  have hleft₂ : StrictlyPositiveAtLeft U₂ :=
    IsTravelingWave.strictlyPositiveAtLeft hTW₂
  exact
    Theorem_1_3_profile_eq_of_signal_energy_dissipation_l2_to_uniform
      (p := p) (c := c) (η := η) (pExp := pExp) hpExp
      hTW₁ hTW₂ hstrict₁ hstrict₂ hreg₁ hreg₂ hclose
      (fun hu₂' hleft₂' hclose' hsignal =>
        henergy p hregime c hc U₁ V₁ U₂ hTW₁ hstrict₁ htail₁_exists
          η hketa heta_cap hu₂' hleft₂' hclose' hsignal)
      (hupgrade p hregime c hc U₁ V₁ U₂ hTW₁ hstrict₁ htail₁_exists
        hreg₁ η hketa heta_cap hu₂ hleft₂ hclose)
      (hcauchy_unique p hregime c hc U₂ V₂ hTW₂ hstrict₂ htail₂_exists
        hreg₂)

/-- Theorem 1.3 from the already-formalized Theorem 1.2 stability statement.
This isolates the uniqueness part of the paper's main line: once the full
near-neighbor stability theorem is available, the second wave can be used as
nearby initial data for stability around the first wave.  The common right
tail supplies the weighted initial closeness, Cauchy uniqueness identifies
the produced solution with the translated second wave, and the frozen
resolvent identities identify the signal profiles.

Point 17 frontier: this theorem does not re-assume the B5 energy package or
the weighted-`L²` to uniform upgrade; those are now contained in
`Theorem_1_2`.  The remaining external PDE facts needed to get the paper's
unconditional uniqueness theorem are:

* `Theorem_1_2` itself for arbitrary nearby whole-line data;
* regularity/frozen-resolvent identification for all waves in the uniqueness
  regime;
* whole-line Cauchy uniqueness for traveling-wave initial data. -/
theorem Theorem_1_3.of_Theorem_1_2_and_regular_tail_cauchy_unique
    (h12 : Theorem_1_2)
    (hregularity : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          TravelingWaveRegularity p c U V)
    (hcauchy_unique : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        TravelingWaveRegularity p c U V →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t)) :
    Theorem_1_3 := by
  intro p hregime
  rcases h12 p hregime with ⟨cStarStar, hasymp, hbaseline, hstability⟩
  refine ⟨cStarStar, hasymp, hbaseline, ?_⟩
  intro c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hstrict₁ hstrict₂ htailPair
  rcases htailPair with ⟨κ₁, hκ_gt, hκ_lt_one, htail₁, htail₂⟩
  have hcap : kappa c < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) :=
    kappa_lt_stability_weight_cap_of_stabilitySpeedBaseline_lt
      hbaseline hc
  rcases exists_between (lt_min hκ_gt hcap) with ⟨η, hketa, heta_min⟩
  have heta_tail : η < κ₁ := lt_of_lt_of_le heta_min (min_le_left _ _)
  have heta_cap : η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) :=
    lt_of_lt_of_le heta_min (min_le_right _ _)
  have htail₁_exists :
      ∃ κ, kappa c < κ ∧ κ < 1 ∧ HasWaveRightTailAsymptotic c κ U₁ :=
    ⟨κ₁, hκ_gt, hκ_lt_one, htail₁⟩
  have htail₂_exists :
      ∃ κ, kappa c < κ ∧ κ < 1 ∧ HasWaveRightTailAsymptotic c κ U₂ :=
    ⟨κ₁, hκ_gt, hκ_lt_one, htail₂⟩
  have hreg₁ : TravelingWaveRegularity p c U₁ V₁ :=
    hregularity p hregime c U₁ V₁ hTW₁ hstrict₁ htail₁_exists
      η hketa heta_cap
  have hreg₂ : TravelingWaveRegularity p c U₂ V₂ :=
    hregularity p hregime c U₂ V₂ hTW₂ hstrict₂ htail₂_exists
      η hketa heta_cap
  have hclose : WeightedL2InitialCloseness η U₂ U₁ :=
    WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
      (eta_pos_of_stability_weight_hypotheses hbaseline hc hketa)
      heta_tail hreg₁.U_cont hreg₂.U_cont
      hstrict₁.hasWaveUpperTailBound hstrict₂.hasWaveUpperTailBound
      htail₁ htail₂
  have hU₂_bdd : IsCUnifBdd U₂ :=
    hstrict₂.hasWaveUpperTailBound.isCUnifBdd_of_continuous hreg₂.U_cont
  have hu₂ : NonnegativeInitialDatum U₂ :=
    IsTravelingWave.nonnegativeInitialDatum hTW₂ hU₂_bdd
  have hleft₂ : StrictlyPositiveAtLeft U₂ :=
    IsTravelingWave.strictlyPositiveAtLeft hTW₂
  rcases
      hstability c hc U₁ V₁ hTW₁ hstrict₁ htail₁_exists
        η hketa heta_cap U₂ hu₂ hleft₂ hclose with
    ⟨u, v, hsol, _hweighted, huniform⟩
  have hconv :
      UniformMovingFrameConvergence c (fun t x => U₂ (x - c * t)) U₁ := by
    intro ε hε
    rcases huniform ε hε with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t x ht
    have hu_eq : u t x = U₂ (x - c * t) :=
      hcauchy_unique p hregime c U₂ V₂ hTW₂ hstrict₂ htail₂_exists
        hreg₂ u v hsol t x
    simpa [hu_eq] using hT t x ht
  exact
    Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent
      hconv
      (IsTravelingWave.V_eq_frozenElliptic_full hTW₁
        hstrict₁.hasWaveUpperTailBound hreg₁)
      (IsTravelingWave.V_eq_frozenElliptic_full hTW₂
        hstrict₂.hasWaveUpperTailBound hreg₂)

/-- Joint main-conclusion package when stability has already been proved.
Compared with the B5 energy closure below, this theorem makes the logical
frontier smaller: Theorem 1.3 is downstream of Theorem 1.2 plus regularity
and Cauchy uniqueness. -/
theorem Theorem_1_2_and_1_3.of_Theorem_1_2_and_regular_tail_cauchy_unique
    (h12 : Theorem_1_2)
    (hregularity : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          TravelingWaveRegularity p c U V)
    (hcauchy_unique : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        TravelingWaveRegularity p c U V →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t)) :
    Theorem_1_2 ∧ Theorem_1_3 := by
  exact
    ⟨h12,
      Theorem_1_3.of_Theorem_1_2_and_regular_tail_cauchy_unique
        h12 hregularity hcauchy_unique⟩

/-- Joint B5 closure of Theorems 1.2 and 1.3 from the same analytic
frontier.  Lemma 2.5, the Section 5 signal estimates, and the scalar
energy-to-weighted-`L²` Grönwall step are discharged before this interface.

The remaining hypotheses are the genuine PDE frontiers: whole-line
perturbation energy dissipation, the weighted-`L²` to uniform moving-frame
upgrade, and whole-line Cauchy uniqueness for traveling-wave initial data. -/
theorem Theorem_1_2_and_1_3.of_signal_energy_dissipation_l2_to_uniform_and_cauchy_unique
    {pExp : ℝ} (hpExp : 1 < pExp)
    (cStarStarFn : CMParams → (ℝ → ℝ))
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hregularity : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          TravelingWaveRegularity p c U V)
    (henergy : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          (∃ kMax > 0, ∃ C > 0,
            ∀ k : ℝ, 0 ≤ k → k < kMax →
            ∀ psi : ExponentialWeight,
              (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
              (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
              Integrable
                (fun x : ℝ => (U x) ^ (p.γ * pExp) * psi.weight x) →
              Integrable
                (fun x : ℝ => (u₀ x) ^ (p.γ * pExp) * psi.weight x) →
                (Integrable
                    (fun x : ℝ => |deriv V x| ^ pExp * psi.weight x) ∧
                  ∫ x : ℝ, |deriv V x| ^ pExp * psi.weight x ≤
                    C * ∫ x : ℝ, (U x) ^ (p.γ * pExp) * psi.weight x) ∧
                (Integrable
                    (fun x : ℝ =>
                      |deriv (frozenElliptic p u₀) x| ^ pExp *
                        psi.weight x) ∧
                  ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ pExp *
                      psi.weight x ≤
                    C * ∫ x : ℝ, (u₀ x) ^ (p.γ * pExp) *
                      psi.weight x)) →
          ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
            (∀ᶠ t in atTop,
              ∫ x : ℝ,
                Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
                  E t) ∧
            (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
            (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
              HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
            (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t))
    (hupgrade : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        TravelingWaveRegularity p c U V →
        ∀ η : ℝ, kappa c < η →
          η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          WeightedL2ToUniformMovingFrameUpgrade p η c u₀ U)
    (hcauchy_unique : ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        TravelingWaveRegularity p c U V →
        ∀ u v : ℝ → ℝ → ℝ,
          IsGlobalCauchySolutionFrom p U u v →
            ∀ t x, u t x = U (x - c * t)) :
    Theorem_1_2 ∧ Theorem_1_3 := by
  refine ⟨?_, ?_⟩
  · exact
      Theorem_1_2.of_signal_energy_dissipation_l2_to_uniform_branch
        (pExp := pExp) hpExp cStarStarFn hcStarStar
        hregularity henergy hupgrade
  · exact
      Theorem_1_3.of_signal_energy_dissipation_l2_to_uniform_and_cauchy_unique
        (pExp := pExp) hpExp cStarStarFn hcStarStar
        hregularity henergy hupgrade hcauchy_unique

/-- Paper1 B5 mainline existence/frontier package.

This is the Paper2/Paper3-style reduces-to-existence interface for the
whole-line stability/uniqueness mainline.  It is deliberately not a theorem
wrapper: no field states `Theorem_1_2`, `Theorem_1_3`, or their combined
conclusion.  The fields are exactly the remaining analytic content after the
Lemma 2.5 weighted resolvent estimate, Section 5 signal estimates, and scalar
Grönwall step have been discharged in this file.

The package is canonical at the weighted `L²` exponent `2`, matching the
statement of `Theorem_1_2`.  The remaining Point 17 frontiers are:

* the paper's stability speed threshold family;
* regularity/frozen-resolvent identification for traveling waves in the
  stability regime;
* whole-line perturbation energy dissipation for nearby Cauchy data;
* weighted-`L²` to uniform moving-frame upgrade;
* whole-line Cauchy uniqueness for traveling-wave initial data. -/
structure Paper1MainlineExistence
    (cStarStarFn : CMParams → (ℝ → ℝ)) : Prop where
  cStarStar_spec : ∀ p : CMParams, StableWaveParameterRegime p →
    StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
      stabilitySpeedBaseline p ≤ cStarStarFn p p.χ
  regularity : ∀ p : CMParams, StableWaveParameterRegime p →
    ∀ c : ℝ, cStarStarFn p p.χ < c →
    ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V →
      HasStrictWaveUpperTailBound p c U →
      (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
      ∀ η : ℝ, kappa c < η →
        η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
        TravelingWaveRegularity p c U V
  energyDissipation : ∀ p : CMParams, StableWaveParameterRegime p →
    ∀ c : ℝ, cStarStarFn p p.χ < c →
    ∀ U V u₀ : ℝ → ℝ,
      IsTravelingWave p c U V →
      HasStrictWaveUpperTailBound p c U →
      (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
      ∀ η : ℝ, kappa c < η →
        η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
        NonnegativeInitialDatum u₀ →
        StrictlyPositiveAtLeft u₀ →
        WeightedL2InitialCloseness η u₀ U →
        (∃ kMax > 0, ∃ C > 0,
          ∀ k : ℝ, 0 ≤ k → k < kMax →
          ∀ psi : ExponentialWeight,
            (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
            (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
            Integrable
              (fun x : ℝ => (U x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
            Integrable
              (fun x : ℝ => (u₀ x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
              (Integrable
                  (fun x : ℝ => |deriv V x| ^ (2 : ℝ) * psi.weight x) ∧
                ∫ x : ℝ, |deriv V x| ^ (2 : ℝ) * psi.weight x ≤
                  C * ∫ x : ℝ, (U x) ^ (p.γ * (2 : ℝ)) * psi.weight x) ∧
              (Integrable
                  (fun x : ℝ =>
                    |deriv (frozenElliptic p u₀) x| ^ (2 : ℝ) *
                      psi.weight x) ∧
                ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ (2 : ℝ) *
                    psi.weight x ≤
                  C * ∫ x : ℝ, (u₀ x) ^ (p.γ * (2 : ℝ)) *
                    psi.weight x)) →
        ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ, ∃ lam > 0,
          IsGlobalCauchySolutionFrom p u₀ u v ∧
          (∀ᶠ t in atTop,
            ∫ x : ℝ,
              Real.exp (2 * η * x) * |u t x - U (x - c * t)| ^ 2 ≤
                E t) ∧
          (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
          (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
            HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
          (∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t)
  l2ToUniform : ∀ p : CMParams, StableWaveParameterRegime p →
    ∀ c : ℝ, cStarStarFn p p.χ < c →
    ∀ U V u₀ : ℝ → ℝ,
      IsTravelingWave p c U V →
      HasStrictWaveUpperTailBound p c U →
      (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
      TravelingWaveRegularity p c U V →
      ∀ η : ℝ, kappa c < η →
        η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) →
        NonnegativeInitialDatum u₀ →
        StrictlyPositiveAtLeft u₀ →
        WeightedL2InitialCloseness η u₀ U →
        WeightedL2ToUniformMovingFrameUpgrade p η c u₀ U
  cauchyUnique : ∀ p : CMParams, StableWaveParameterRegime p →
    ∀ c : ℝ, cStarStarFn p p.χ < c →
    ∀ U V : ℝ → ℝ,
      IsTravelingWave p c U V →
      HasStrictWaveUpperTailBound p c U →
      (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
      TravelingWaveRegularity p c U V →
      ∀ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U u v →
          ∀ t x, u t x = U (x - c * t)

/-- Theorem 1.2 from the canonical Paper1 mainline existence package. -/
theorem Theorem_1_2.of_mainlineExistence
    {cStarStarFn : CMParams → (ℝ → ℝ)}
    (hexist : Paper1MainlineExistence cStarStarFn) :
    Theorem_1_2 :=
  Theorem_1_2.of_signal_energy_dissipation_l2_to_uniform_branch
    (pExp := (2 : ℝ)) (by norm_num)
    cStarStarFn hexist.cStarStar_spec
    hexist.regularity hexist.energyDissipation hexist.l2ToUniform

/-- Instance-facing Theorem 1.2 endpoint from the canonical Paper1 mainline
existence package. -/
theorem Theorem_1_2.of_mainlineExistenceFact
    {cStarStarFn : CMParams → (ℝ → ℝ)}
    [hexist : Fact (Paper1MainlineExistence cStarStarFn)] :
    Theorem_1_2 :=
  Theorem_1_2.of_mainlineExistence hexist.out

/-- Theorem 1.3 from the canonical Paper1 mainline existence package. -/
theorem Theorem_1_3.of_mainlineExistence
    {cStarStarFn : CMParams → (ℝ → ℝ)}
    (hexist : Paper1MainlineExistence cStarStarFn) :
    Theorem_1_3 :=
  Theorem_1_3.of_signal_energy_dissipation_l2_to_uniform_and_cauchy_unique
    (pExp := (2 : ℝ)) (by norm_num)
    cStarStarFn hexist.cStarStar_spec
    hexist.regularity hexist.energyDissipation hexist.l2ToUniform
    hexist.cauchyUnique

/-- Instance-facing Theorem 1.3 endpoint from the canonical Paper1 mainline
existence package. -/
theorem Theorem_1_3.of_mainlineExistenceFact
    {cStarStarFn : CMParams → (ℝ → ℝ)}
    [hexist : Fact (Paper1MainlineExistence cStarStarFn)] :
    Theorem_1_3 :=
  Theorem_1_3.of_mainlineExistence hexist.out

/-- Literal Paper1 B5 endpoint reduced to the canonical mainline existence
package.  The conclusion is exactly `Theorem_1_2 ∧ Theorem_1_3`, with no
intermediate target alias. -/
theorem Theorem_1_2_and_1_3.of_mainlineExistence
    {cStarStarFn : CMParams → (ℝ → ℝ)}
    (hexist : Paper1MainlineExistence cStarStarFn) :
    Theorem_1_2 ∧ Theorem_1_3 := by
  exact
    ⟨Theorem_1_2.of_mainlineExistence hexist,
      Theorem_1_3.of_mainlineExistence hexist⟩

/-- Instance-facing endpoint: once the canonical Paper1 mainline existence
package is registered, the B5 endpoint has no explicit frontier argument. -/
theorem Theorem_1_2_and_1_3.of_mainlineExistenceFact
    {cStarStarFn : CMParams → (ℝ → ℝ)}
    [hexist : Fact (Paper1MainlineExistence cStarStarFn)] :
    Theorem_1_2 ∧ Theorem_1_3 :=
  Theorem_1_2_and_1_3.of_mainlineExistence hexist.out

/-- Audit record for the Paper1 B5 mainline reduction.

Coverage: `Theorem_1_2`, `Theorem_1_3`, and the literal combined endpoint
all follow from the same canonical existence/frontier package.  The package
fields above contain no theorem-shaped conclusion field. -/
structure Paper1MainlineReductionCoverage
    (cStarStarFn : CMParams → (ℝ → ℝ)) : Prop where
  theorem12 :
    ∀ _hexist : Paper1MainlineExistence cStarStarFn, Theorem_1_2
  theorem13 :
    ∀ _hexist : Paper1MainlineExistence cStarStarFn, Theorem_1_3
  combined :
    ∀ _hexist : Paper1MainlineExistence cStarStarFn,
      Theorem_1_2 ∧ Theorem_1_3

/-- Proof that the Paper1 B5 mainline is reduced to the canonical
existence/frontier package. -/
theorem Theorem_1_2_and_1_3_reduces_to_existence_coverage
    (cStarStarFn : CMParams → (ℝ → ℝ)) :
    Paper1MainlineReductionCoverage cStarStarFn := by
  refine ⟨?_, ?_, ?_⟩
  · intro hexist
    exact Theorem_1_2.of_mainlineExistence hexist
  · intro hexist
    exact Theorem_1_3.of_mainlineExistence hexist
  · intro hexist
    exact Theorem_1_2_and_1_3.of_mainlineExistence hexist

/-! ### Unit-resolvent specialization of Lemma_2_5_with_explicit_k -/

/-- Unit-resolvent (`l = μ = 1`) specialization of
`Lemma_2_5_with_explicit_k`.  Constant simplifies to
`C := 1 · (1/2)^p · 2^(p-1) · 2/(1 - k) = (1/2) · 2/(1 - k) = 1/(1 - k)`
on the convex hull of standard simplifications, though the literal value
emitted preserves the explicit factors. -/
theorem Lemma_2_5_with_explicit_k_unit
    (p : CMParams) (psi : ExponentialWeight) {pExp k : ℝ}
    (hpExp : 1 ≤ pExp) (hk_nn : 0 ≤ k) (hk_lt : k < 1)
    (hk_bound : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y)
    (hint_hyp :
      Integrable
        (fun x : ℝ => ((u x) ^ p.γ) ^ pExp * psi.weight x)) :
    Integrable
      (fun x : ℝ =>
        |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
          psi.weight x) ∧
    ∫ x : ℝ,
        |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
          psi.weight x ≤
      ((Real.sqrt 1) ^ pExp *
          ((1 / (2 * Real.sqrt 1)) ^ pExp *
            (2 / Real.sqrt 1) ^ (pExp - 1) *
            (2 / (Real.sqrt 1 - k)))) *
        ∫ x : ℝ, ((u x) ^ p.γ) ^ pExp * psi.weight x := by
  have hk_lt_sqrt : k < Real.sqrt 1 := by
    rw [Real.sqrt_one]; exact hk_lt
  exact Lemma_2_5_with_explicit_k psi (l := 1) (mu := 1) (k := k)
    one_pos one_pos hpExp (lt_of_lt_of_le one_pos p.hγ) hk_nn hk_lt_sqrt
    hk_bound hu hu_nn hint_hyp

/-! ### Existential Lemma 2.5 for ψ-class with k < √l -/

/-- Existential Lemma 2.5 for the restricted exponential-weight class
satisfying `|ψ'| ≤ k · ψ` for some `k < √l`: for every fixed
`(pExp, γ, l, μ)` there is a single positive constant `C(pExp, γ, l, μ, k)`
that bounds the weighted resolvent gradient.

This is the natural strong form of `Lemma_2_5`: the full statement
quantifies over arbitrary `ExponentialWeight`, but on the unrestricted
class `C` cannot be uniform in `ψ` (the bound `2/(√l - k)` blows up).
By packaging `k` explicitly, the constant becomes uniform in the
restricted class. -/
theorem Lemma_2_5_existential_for_small_k_psi
    {pExp gamma l mu k : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp) (hgamma : 0 < gamma)
    (hk_nn : 0 ≤ k) (hk_lt : k < Real.sqrt l) :
    ∃ C > 0, ∀ (psi : ExponentialWeight),
      (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
      ∀ {u : ℝ → ℝ}, IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x : ℝ => ((u x) ^ gamma) ^ pExp * psi.weight x) →
        Integrable
          (fun x : ℝ =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x ≤
          C * ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x := by
  refine ⟨(Real.sqrt l) ^ pExp *
        ((mu / (2 * Real.sqrt l)) ^ pExp *
          (2 / Real.sqrt l) ^ (pExp - 1) *
          (2 / (Real.sqrt l - k))), ?_, ?_⟩
  · -- Positivity of C
    have hsqrt_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
    have hsqrt_sub_pos : 0 < Real.sqrt l - k := by linarith
    have hCouter_pos : 0 < (Real.sqrt l) ^ pExp :=
      Real.rpow_pos_of_pos hsqrt_pos _
    have hC1_pos : 0 < (mu / (2 * Real.sqrt l)) ^ pExp :=
      Real.rpow_pos_of_pos (by positivity) _
    have hC2_pos : 0 < (2 / Real.sqrt l) ^ (pExp - 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hC3_pos : 0 < 2 / (Real.sqrt l - k) := by positivity
    positivity
  · intro psi hk_bound u hu hu_nn hint
    exact Lemma_2_5_with_explicit_k psi hl hmu hpExp hgamma hk_nn hk_lt
      hk_bound hu hu_nn hint

/-! ### Lemma 2.5 with explicit ε margin -/

/-- **Lemma 2.5 with explicit ε margin**: for every `(pExp, γ, l, μ, ε)`
with `ε ∈ (0, √l)`, there is a single positive constant
`C(pExp, γ, l, μ, ε)` that bounds the weighted resolvent gradient for
every weight ψ whose log-derivative is bounded by `√l − ε`.

The constant `C := √l^p · (μ/(2√l))^p · (2/√l)^(p-1) · 2/ε`. -/
theorem Lemma_2_5_explicit_epsilon
    {pExp gamma l mu epsilon : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp) (hgamma : 0 < gamma)
    (hε_pos : 0 < epsilon) (hε_lt : epsilon < Real.sqrt l) :
    ∃ C > 0, ∀ (psi : ExponentialWeight),
      (∀ z, |deriv psi.weight z| ≤ (Real.sqrt l - epsilon) * psi.weight z) →
      ∀ {u : ℝ → ℝ}, IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x : ℝ => ((u x) ^ gamma) ^ pExp * psi.weight x) →
        Integrable
          (fun x : ℝ =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x ≤
          C * ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x := by
  set k := Real.sqrt l - epsilon
  have hk_nn : 0 ≤ k := by
    have hsqrt_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
    have hk_pos_or : Real.sqrt l - epsilon ≥ 0 := by linarith
    exact hk_pos_or
  have hk_lt : k < Real.sqrt l := by
    show Real.sqrt l - epsilon < Real.sqrt l
    linarith
  have hε_eq : Real.sqrt l - k = epsilon := by simp [k]
  obtain ⟨C, hC_pos, hC⟩ :=
    Lemma_2_5_existential_for_small_k_psi
      (pExp := pExp) (gamma := gamma) (l := l) (mu := mu) (k := k)
      hl hmu hpExp hgamma hk_nn hk_lt
  refine ⟨C, hC_pos, ?_⟩
  intro psi hk_bound u hu hu_nn hint
  exact hC psi hk_bound hu hu_nn hint

/-! ### CMParams-flavored existential ε form -/

/-- CMParams-flavored version of `Lemma_2_5_explicit_epsilon` with `γ`
specialized to `p.γ`.  Generalizes `Lemma_2_5_with_explicit_k_unit` to
arbitrary `(l, μ)` parameters (not just `l = μ = 1`). -/
theorem Lemma_2_5_explicit_epsilon_CMParams
    (p : CMParams) {pExp l mu epsilon : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp)
    (hε_pos : 0 < epsilon) (hε_lt : epsilon < Real.sqrt l) :
    ∃ C > 0, ∀ (psi : ExponentialWeight),
      (∀ z, |deriv psi.weight z| ≤ (Real.sqrt l - epsilon) * psi.weight z) →
      ∀ {u : ℝ → ℝ}, IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x : ℝ => ((u x) ^ p.γ) ^ pExp * psi.weight x) →
        Integrable
          (fun x : ℝ =>
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) l mu z) x| ^ pExp *
              psi.weight x ≤
          C * ∫ x : ℝ, ((u x) ^ p.γ) ^ pExp * psi.weight x :=
  Lemma_2_5_explicit_epsilon (gamma := p.γ) hl hmu hpExp
    (lt_of_lt_of_le one_pos p.hγ) hε_pos hε_lt

/-! ### CMParams + (l, μ) = (1, 1) ε form -/

/-- CMParams + unit-resolvent ε form: takes (p, ε) with ε ∈ (0, 1),
specializes to (l, μ) = (1, 1).  Useful for downstream Paper 4
applications that consume the unit resolvent directly. -/
theorem Lemma_2_5_explicit_epsilon_CMParams_unit
    (p : CMParams) {pExp epsilon : ℝ}
    (hpExp : 1 ≤ pExp)
    (hε_pos : 0 < epsilon) (hε_lt : epsilon < 1) :
    ∃ C > 0, ∀ (psi : ExponentialWeight),
      (∀ z, |deriv psi.weight z| ≤ (1 - epsilon) * psi.weight z) →
      ∀ {u : ℝ → ℝ}, IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x : ℝ => ((u x) ^ p.γ) ^ pExp * psi.weight x) →
        Integrable
          (fun x : ℝ =>
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ p.γ) 1 1 z) x| ^ pExp *
              psi.weight x ≤
          C * ∫ x : ℝ, ((u x) ^ p.γ) ^ pExp * psi.weight x := by
  have hε_lt_sqrt : epsilon < Real.sqrt 1 := by
    rw [Real.sqrt_one]; exact hε_lt
  have h_bound_eq : (1 : ℝ) - epsilon = Real.sqrt 1 - epsilon := by
    rw [Real.sqrt_one]
  obtain ⟨C, hC_pos, hC⟩ :=
    Lemma_2_5_explicit_epsilon_CMParams p (l := 1) (mu := 1)
      one_pos one_pos hpExp hε_pos hε_lt_sqrt
  refine ⟨C, hC_pos, ?_⟩
  intro psi hk_bound u hu hu_nn hint
  refine hC psi ?_ hu hu_nn hint
  intro z
  rw [← h_bound_eq]
  exact hk_bound z

/-! ### Lemma_2_5 from a ψ-extracted-k witness -/

/-- Lemma 2.5 follows from a ψ-extracted k-witness that is `< √l`.  The
witness packs the choice of `k_ψ` into the `ψ`-input alongside the
existing `deriv_abs_le` field; downstream code that provides `ψ` with
such a witness can directly invoke this lemma.

This is the sharpest closure of `Lemma_2_5` that doesn't require
restricting the `ExponentialWeight` class:  for each ψ supplied with a
`k_ψ < √l` witness, the bound holds with the explicit constant. -/
theorem Lemma_2_5_from_extracted_psi_k_witness
    {pExp gamma l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp) (hgamma : 0 < gamma)
    (psi : ExponentialWeight) {k : ℝ}
    (hk_nn : 0 ≤ k) (hk_lt : k < Real.sqrt l)
    (hk_witness : ∀ z, |deriv psi.weight z| ≤ k * psi.weight z)
    {u : ℝ → ℝ} (hu : IsCUnifBdd u) (hu_nn : ∀ y, 0 ≤ u y)
    (hint_hyp :
      Integrable (fun x : ℝ => ((u x) ^ gamma) ^ pExp * psi.weight x)) :
    Integrable
      (fun x : ℝ =>
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x) ∧
    ∫ x : ℝ,
        |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
          psi.weight x ≤
      ((Real.sqrt l) ^ pExp *
          ((mu / (2 * Real.sqrt l)) ^ pExp *
            (2 / Real.sqrt l) ^ (pExp - 1) *
            (2 / (Real.sqrt l - k)))) *
      ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x :=
  Lemma_2_5_with_explicit_k psi hl hmu hpExp hgamma hk_nn hk_lt
    hk_witness hu hu_nn hint_hyp

/-- Standard-name bridge for grep-based statement-target audits. -/
theorem Lemma_2_5_proved : Lemma_2_5 :=
  lemma_2_5

/-! ### Legacy restricted small-k ψ-class wrapper -/

/-- Older restricted Prop used while the statement layer still had an
unrestricted weight quantifier.  It remains as a convenient explicit-k wrapper
around the same assembled estimate. -/
def Lemma_2_5_restricted_psi_class : Prop :=
  ∀ pExp gamma l mu : ℝ, 1 < pExp → 0 < gamma → 0 < l → 0 < mu →
    ∀ k : ℝ, 0 ≤ k → k < Real.sqrt l →
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
      Integrable (fun x => ((u x) ^ gamma) ^ pExp * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x

theorem Lemma_2_5_restricted_psi_class_holds : Lemma_2_5_restricted_psi_class := by
  intro pExp gamma l mu hpExp hgamma hl hmu k hk_nn hk_lt
  obtain ⟨C, hC_pos, hC⟩ :=
    Lemma_2_5_existential_for_small_k_psi (pExp := pExp) (gamma := gamma)
      (l := l) (mu := mu) (k := k) hl hmu (le_of_lt hpExp) hgamma hk_nn hk_lt
  refine ⟨C, hC_pos, ?_⟩
  intro u psi hu hu_nn hk_bound hint
  exact hC psi hk_bound hu hu_nn hint

/-! ### Uniform-k ψ-class assumption for full Lemma 2.5

The full `Lemma_2_5` Prop in `Statements.lean` requires `∃ C > 0` uniform
over all `psi : ExponentialWeight`, which the class-wide `deriv_abs_le`
existential does not guarantee.  We expose a `UniformKBound` predicate
that packages a single ψ-uniform k bound; on this restricted class, the
ε-explicit closure becomes the full `∃C > 0, ∀ψ` shape. -/

/-- A `ψ-uniform-k` bound on a family of `ExponentialWeight`s:
all weights in the family share a common `k < √l` bound on
`|deriv ψ| / ψ`. -/
def UniformKBound (l : ℝ) (k : ℝ) : Set ExponentialWeight :=
  {psi | ∀ z, |deriv psi.weight z| ≤ k * psi.weight z}

theorem Lemma_2_5_from_uniform_k_class
    {pExp gamma l mu k : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hpExp : 1 ≤ pExp) (hgamma : 0 < gamma)
    (hk_nn : 0 ≤ k) (hk_lt : k < Real.sqrt l) :
    ∃ C > 0, ∀ u : ℝ → ℝ, ∀ psi : ExponentialWeight,
      psi ∈ UniformKBound l k →
      IsCUnifBdd u → (∀ y, 0 ≤ u y) →
      Integrable (fun x => ((u x) ^ gamma) ^ pExp * psi.weight x) →
        Integrable
          (fun x =>
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x) ∧
        ∫ x : ℝ,
            |deriv (fun z => Psi (fun y => (u y) ^ gamma) l mu z) x| ^ pExp *
              psi.weight x
          ≤ C * ∫ x : ℝ, ((u x) ^ gamma) ^ pExp * psi.weight x := by
  obtain ⟨C, hC_pos, hC⟩ :=
    Lemma_2_5_existential_for_small_k_psi (pExp := pExp) (gamma := gamma)
      (l := l) (mu := mu) (k := k) hl hmu hpExp hgamma hk_nn hk_lt
  refine ⟨C, hC_pos, ?_⟩
  intro u psi hpsi_class hu hu_nn hint
  exact hC psi hpsi_class hu hu_nn hint

section AxiomAudit

#print axioms lemma_2_5
#print axioms Lemma_2_5_proved

end AxiomAudit

end ShenWork.Paper1

end
