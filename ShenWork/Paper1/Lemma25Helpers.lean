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

/-! ### Lemma 2.5 restricted to the small-k ψ-class -/

/-- Lemma 2.5 restricted Prop: identical statement as `Lemma_2_5` but the
inner quantifier over `psi : ExponentialWeight` is replaced by a
quantifier over `ψ` with an explicit `k < √l` deriv_abs_le witness.
This is provable from the explicit-k assembly above. -/
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

end ShenWork.Paper1

end
