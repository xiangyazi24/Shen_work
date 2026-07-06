/-
  ShenWork/PDE/IntervalFullKernelSecondDerivCtheta.lean

  **C^θ-cancellation second-derivative estimates for the interval-Neumann heat
  semigroup** — the kernel-side bricks of the divergence-form Schauder estimate that
  upgrades `u(t)∈C^θ` to `u_x(t)∈C^η` (hence `u(t)∈C^{1+η}`) at positive time.

  The naive sup bound `‖∂ₓₓ S(σ)h‖∞ ≤ Cσ⁻¹‖h‖∞` is NON-integrable against the
  chemotaxis Duhamel time integral `∫(t−s)⁻¹ds`.  The CORRECT bound tests `∂ₓₓ S(σ)`
  against the HÖLDER MODULUS of `h`, using the mean-zero cancellation
  `∫₀¹ ∂ₓₓ K_σ(x,y) dy = 0` (the Neumann semigroup preserves constants):

    `∂ₓₓ S(σ)h(x) = ∫₀¹ ∂ₓₓ K_σ(x,y) (h(y) − h(x)) dy`   ⟹
    `‖∂ₓₓ S(σ)h‖∞ ≤ Cθ · σ^{−1+θ/2} · [h]_{C^θ}`         (INTEGRABLE in σ for θ>0).

  ## Bricks
  * `intervalNeumannFullKernel_secondDeriv_integral_zero` (brick 1, mean-zero):
    `∫₀¹ ∂ₓₓ K_σ(x,y) dy = 0`, from `S(σ)(const) = const` (kernel mass 1) and the
    committed second-order DUI `intervalFullSemigroupOperator_hasDerivAt_deriv_fst`.

  No `sorry`/`admit`/custom `axiom`/`native_decide`.
-/
import ShenWork.PDE.IntervalFullKernelSecondDerivLinfty
import ShenWork.PDE.IntervalFullKernelSupBound

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-! ## Brick 1 — mean-zero cancellation `∫₀¹ ∂ₓₓ K_σ(x,·) = 0` -/

/-- **The propagator preserves constants.**  `S(σ)(const c) = c` everywhere, since
the full Neumann kernel has unit mass `∫₀¹ K_σ(x,y) dy = 1`. -/
theorem intervalFullSemigroupOperator_const {t : ℝ} (ht : 0 < t) (c : ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t (fun _ => c) x = c := by
  unfold intervalFullSemigroupOperator
  have hmass := intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht x
  calc (∫ y, intervalNeumannFullKernel t x y * c ∂(intervalMeasure 1))
      = (∫ y, intervalNeumannFullKernel t x y ∂(intervalMeasure 1)) * c := by
        rw [MeasureTheory.integral_mul_const]
    _ = 1 * c := by rw [hmass]
    _ = c := one_mul c

/-- **Brick 1 — mean-zero cancellation.**  For `t > 0`,

  `∫₀¹ ∂ₓₓ K_full(t,x,y) dy = 0`   (over `intervalMeasure 1`).

The Neumann semigroup preserves constants (`intervalFullSemigroupOperator_const`),
so `x ↦ S(t)(const 1)(x) = 1` is constant and its second `x`-derivative vanishes.
The committed second-order DUI `intervalFullSemigroupOperator_hasDerivAt_deriv_fst`
identifies that second derivative with `∫ ∂ₓₓ K_full(t,x,y)·1 dy`. -/
theorem intervalNeumannFullKernel_secondDeriv_integral_zero {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y, deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x
        ∂(intervalMeasure 1)) = 0 := by
  -- constant-1 data
  set f : ℝ → ℝ := fun _ => (1 : ℝ) with hf_def
  have hf_meas : AEStronglyMeasurable f (intervalMeasure 1) := aestronglyMeasurable_const
  have hf : ∀ y, |f y| ≤ (1 : ℝ) := fun y => by simp [hf_def]
  -- the operator on constant data is constant in `x`, so its 2nd `x`-deriv is 0.
  have hSconst : (fun z : ℝ => intervalFullSemigroupOperator t f z) = fun _ : ℝ => (1 : ℝ) := by
    funext z; rw [hf_def]; exact intervalFullSemigroupOperator_const ht 1 z
  have hderiv0 : deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator t f w) z) x
      = 0 := by
    have h1 : (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator t f w) z)
        = fun _ : ℝ => (0 : ℝ) := by
      funext z; rw [hSconst]; simp
    rw [h1]; simp
  -- the committed 2nd-order DUI: that 2nd `x`-deriv equals `∫ ∂ₓₓK·f`.
  have hDUI := (intervalFullSemigroupOperator_hasDerivAt_deriv_fst ht hf_meas hf x).deriv
  rw [hderiv0] at hDUI
  -- `∫ ∂ₓₓK·1 = ∫ ∂ₓₓK`.
  have hsimp : (∫ y, deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x
        * f y ∂(intervalMeasure 1))
      = ∫ y, deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x
        ∂(intervalMeasure 1) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    rw [hf_def]; ring
  rw [hsimp] at hDUI
  exact hDUI.symm

/-! ## Brick 2 — weighted second-derivative kernel mass `≤ Cθ σ^{−1+θ/2}` -/

/-- The `θ`-th absolute Gaussian moment `∫_ℝ |u|^θ exp(−u²) du` (a finite positive
constant for `θ > −1`; here `0 < θ < 1`).  The scale-free constant in brick 2. -/
noncomputable def gaussianAbsMoment (θ : ℝ) : ℝ :=
  ∫ u : ℝ, |u| ^ θ * Real.exp (-u ^ 2)

theorem gaussianAbsMoment_nonneg (θ : ℝ) : 0 ≤ gaussianAbsMoment θ := by
  unfold gaussianAbsMoment
  refine MeasureTheory.integral_nonneg (fun u => ?_)
  positivity

/-- `u ↦ |u|^θ exp(−b u²)` is integrable on `ℝ` for `b > 0`, `0 ≤ θ ≤ 1`.  Dominate
the even prefactor by `1 + u²` (`|u|^θ ≤ 1 + u²` for `0 ≤ θ ≤ 1`), reducing to
`exp(−b u²)` and `u²·exp(−b u²)`, both Mathlib-integrable. -/
theorem integrable_abs_rpow_mul_exp_neg_mul_sq {b θ : ℝ} (hb : 0 < b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    MeasureTheory.Integrable (fun u : ℝ => |u| ^ θ * Real.exp (-b * u ^ 2)) := by
  -- dominating integrable function `(1 + u²)·exp(−b u²)`.
  have hdom : MeasureTheory.Integrable
      (fun u : ℝ => (1 + u ^ 2) * Real.exp (-b * u ^ 2)) := by
    have h1 : MeasureTheory.Integrable (fun u : ℝ => Real.exp (-b * u ^ 2)) :=
      integrable_exp_neg_mul_sq hb
    have h2' : MeasureTheory.Integrable (fun u : ℝ => u ^ (2 : ℝ) * Real.exp (-b * u ^ 2)) :=
      integrable_rpow_mul_exp_neg_mul_sq hb (s := (2 : ℝ)) (by norm_num)
    have hcongr : (fun u : ℝ => u ^ (2 : ℝ) * Real.exp (-b * u ^ 2))
        = fun u : ℝ => u ^ 2 * Real.exp (-b * u ^ 2) := by
      funext u; rw [Real.rpow_two]
    have h2 : MeasureTheory.Integrable (fun u : ℝ => u ^ 2 * Real.exp (-b * u ^ 2)) := by
      rw [← hcongr]; exact h2'
    have hsum : (fun u : ℝ => Real.exp (-b * u ^ 2) + u ^ 2 * Real.exp (-b * u ^ 2))
        = fun u : ℝ => (1 + u ^ 2) * Real.exp (-b * u ^ 2) := by
      funext u; ring
    rw [← hsum]; exact h1.add h2
  have hmeas : AEStronglyMeasurable (fun u : ℝ => |u| ^ θ * Real.exp (-b * u ^ 2)) volume :=
    ((continuous_abs.rpow_const (fun _ => Or.inr hθ0)).mul (by fun_prop)).aestronglyMeasurable
  refine hdom.mono' hmeas (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hbound : |u| ^ θ ≤ 1 + u ^ 2 := by
    rcases le_or_gt |u| 1 with h | h
    · calc |u| ^ θ ≤ (1 : ℝ) ^ θ := Real.rpow_le_rpow (abs_nonneg _) h hθ0
        _ = 1 := Real.one_rpow _
        _ ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg u]
    · calc |u| ^ θ ≤ |u| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hθ1
        _ = |u| := Real.rpow_one _
        _ ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hexp_nn : (0 : ℝ) ≤ Real.exp (-b * u ^ 2) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right hbound hexp_nn

/-- **Gaussian moment scaling.**  For `c > 0`, `0 < θ < 1`,
`∫_ℝ |w|^θ exp(−w²/c) dw = c^{(θ+1)/2} · gaussianAbsMoment θ`.

Change of variables `w = u·√c` (`integral_comp_mul_right`); `|u·√c|^θ = c^{θ/2}|u|^θ`
and `exp(−(u√c)²/c) = exp(−u²)`. -/
theorem gaussian_abs_moment_scaling {c θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hcpos : 0 < c) :
    (∫ w : ℝ, |w| ^ θ * Real.exp (-w ^ 2 / c))
      = c ^ ((θ + 1) / 2 : ℝ) * gaussianAbsMoment θ := by
  have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hcpos
  set g : ℝ → ℝ := fun w => |w| ^ θ * Real.exp (-w ^ 2 / c) with hg
  -- `∫ g(w·√c) dw = |(√c)⁻¹| • ∫ g(y) dy`.
  have hcomp := MeasureTheory.Measure.integral_comp_mul_right g (Real.sqrt c)
  -- the integrand at `w·√c` is `c^{θ/2}·|w|^θ·exp(−w²)`.
  have hpt : ∀ w : ℝ, g (w * Real.sqrt c)
      = c ^ (θ / 2 : ℝ) * (|w| ^ θ * Real.exp (-w ^ 2)) := by
    intro w
    show |w * Real.sqrt c| ^ θ * Real.exp (-(w * Real.sqrt c) ^ 2 / c)
        = c ^ (θ / 2 : ℝ) * (|w| ^ θ * Real.exp (-w ^ 2))
    have habs : |w * Real.sqrt c| ^ θ = c ^ (θ / 2 : ℝ) * |w| ^ θ := by
      rw [abs_mul, abs_of_nonneg hsc.le, Real.mul_rpow (abs_nonneg _) hsc.le,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hcpos.le,
        show (1 / 2 : ℝ) * θ = θ / 2 by ring, mul_comm]
    have hexp : Real.exp (-(w * Real.sqrt c) ^ 2 / c) = Real.exp (-w ^ 2) := by
      congr 1
      rw [mul_pow, Real.sq_sqrt hcpos.le]
      field_simp
    rw [habs, hexp]; ring
  -- assemble
  have hLHS : (∫ w : ℝ, g (w * Real.sqrt c))
      = c ^ (θ / 2 : ℝ) * gaussianAbsMoment θ := by
    rw [show (fun w : ℝ => g (w * Real.sqrt c))
        = fun w : ℝ => c ^ (θ / 2 : ℝ) * (|w| ^ θ * Real.exp (-w ^ 2)) from funext hpt,
      MeasureTheory.integral_const_mul]
    rfl
  rw [hLHS] at hcomp
  -- `hcomp : c^{θ/2}·moment = |(√c)⁻¹| • ∫ g`; solve for `∫ g`.
  rw [smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr hsc.le)] at hcomp
  have hsc_ne : Real.sqrt c ≠ 0 := ne_of_gt hsc
  have hfinal : (∫ w : ℝ, g w) = Real.sqrt c * (c ^ (θ / 2 : ℝ) * gaussianAbsMoment θ) := by
    field_simp at hcomp ⊢
    linarith [hcomp]
  rw [hg] at hfinal
  rw [hfinal]
  -- `√c · c^{θ/2} = c^{(θ+1)/2}`.
  rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hcpos]
  congr 2
  ring

/-- The weighted-mass constant `Cθ = 5·(8)^{(θ+1)/2}/(2·√(4π)) · gaussianAbsMoment θ`,
the scale-free prefactor in the `σ^{−1+θ/2}` weighted second-derivative mass bound. -/
noncomputable def weightedHeatHessConst (θ : ℝ) : ℝ :=
  5 * (8 : ℝ) ^ ((θ + 1) / 2 : ℝ) / (2 * Real.sqrt (4 * Real.pi)) * gaussianAbsMoment θ

theorem weightedHeatHessConst_nonneg (θ : ℝ) : 0 ≤ weightedHeatHessConst θ := by
  unfold weightedHeatHessConst
  have := gaussianAbsMoment_nonneg θ
  positivity

/-- **Whole-line `|z|^θ`-weighted second-derivative heat mass.**  For `t > 0`,
`0 ≤ θ ≤ 1` (used with `0 < θ < 1`),

  `∫_ℝ |∂ₓₓ heat(t,w)| · |w|^θ dw ≤ weightedHeatHessConst θ · t^{−1+θ/2}`.

Pointwise `|∂ₓₓheat| ≤ heatHessPointwiseBound t · exp(−w²/(8t))`, then the Gaussian
moment scaling `∫|w|^θ exp(−w²/(8t)) = (8t)^{(θ+1)/2}·gaussianAbsMoment θ`; the
`t`-powers collapse to `t^{−1+θ/2}`. -/
theorem heatKernel_secondDeriv_weighted_abs_integral_le {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫ w : ℝ, |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| * |w| ^ θ)
      ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ) := by
  have h8t : (0 : ℝ) < 8 * t := by linarith
  -- the dominating weighted Gaussian.
  set maj : ℝ → ℝ := fun w =>
    heatHessPointwiseBound t * Real.exp (-w ^ 2 / (4 * (2 * t))) * |w| ^ θ with hmaj
  have hmaj_int : MeasureTheory.Integrable maj := by
    rw [hmaj]
    have hbase := integrable_abs_rpow_mul_exp_neg_mul_sq
      (b := 1 / (4 * (2 * t))) (θ := θ) (by positivity) hθ0.le hθ1.le
    have hcongr : (fun w : ℝ =>
        heatHessPointwiseBound t * Real.exp (-w ^ 2 / (4 * (2 * t))) * |w| ^ θ)
        = fun w : ℝ => heatHessPointwiseBound t
          * (|w| ^ θ * Real.exp (-(1 / (4 * (2 * t))) * w ^ 2)) := by
      funext w
      rw [show -w ^ 2 / (4 * (2 * t)) = -(1 / (4 * (2 * t))) * w ^ 2 by ring]; ring
    rw [hcongr]
    exact (hbase.const_mul (heatHessPointwiseBound t))
  -- the LHS integrand is integrable (dominated by maj).
  have hLHS_int : MeasureTheory.Integrable
      (fun w : ℝ => |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| * |w| ^ θ) := by
    refine hmaj_int.mono'
      (((continuous_secondDeriv_heatKernel ht).abs.mul
        (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hk := abs_secondDeriv_heatKernel_le ht w
    have hwθ : (0 : ℝ) ≤ |w| ^ θ := Real.rpow_nonneg (abs_nonneg _) _
    exact mul_le_mul_of_nonneg_right hk hwθ
  -- dominate the integral.
  have hmono : (∫ w : ℝ,
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| * |w| ^ θ)
      ≤ ∫ w : ℝ, maj w := by
    refine MeasureTheory.integral_mono hLHS_int hmaj_int (fun w => ?_)
    rw [hmaj]
    have hk := abs_secondDeriv_heatKernel_le ht w
    have hwθ : (0 : ℝ) ≤ |w| ^ θ := Real.rpow_nonneg (abs_nonneg _) _
    exact mul_le_mul_of_nonneg_right hk hwθ
  refine hmono.trans ?_
  -- evaluate `∫ maj = heatHessPointwiseBound t · (8t)^{(θ+1)/2} · gaussianAbsMoment θ`.
  have hmaj_eval : (∫ w : ℝ, maj w)
      = heatHessPointwiseBound t
        * ((4 * (2 * t)) ^ ((θ + 1) / 2 : ℝ) * gaussianAbsMoment θ) := by
    rw [hmaj]
    have hfun : (fun w : ℝ =>
        heatHessPointwiseBound t * Real.exp (-w ^ 2 / (4 * (2 * t))) * |w| ^ θ)
        = fun w : ℝ => heatHessPointwiseBound t
          * (|w| ^ θ * Real.exp (-w ^ 2 / (4 * (2 * t)))) := by
      funext w; ring
    rw [hfun, MeasureTheory.integral_const_mul,
      gaussian_abs_moment_scaling hθ0 hθ1 (by positivity : (0 : ℝ) < 4 * (2 * t))]
  rw [hmaj_eval]
  -- collapse the `t`-powers and numeric constants to `weightedHeatHessConst θ · t^{−1+θ/2}`.
  unfold heatHessPointwiseBound weightedHeatHessConst
  have htne : t ≠ 0 := ne_of_gt ht
  have h4t : Real.sqrt (4 * Real.pi * t) = Real.sqrt (4 * Real.pi) * Real.sqrt t := by
    rw [← Real.sqrt_mul (by positivity)]
  have h8tpow : (4 * (2 * t) : ℝ) ^ ((θ + 1) / 2 : ℝ)
      = (8 : ℝ) ^ ((θ + 1) / 2 : ℝ) * t ^ ((θ + 1) / 2 : ℝ) := by
    rw [show (4 * (2 * t) : ℝ) = 8 * t by ring,
      Real.mul_rpow (by norm_num) ht.le]
  have hsqrt_t : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
  -- LHS = 5·(1/(2t))·(1/(√(4π)·√t))·8^{(θ+1)/2}·t^{(θ+1)/2}·M
  --     = [5·8^{(θ+1)/2}/(2√(4π))·M] · t^{−1−1/2+(θ+1)/2}
  --     = weightedHeatHessConst · t^{−1+θ/2}.
  rw [h4t, h8tpow, hsqrt_t]
  rw [show (-1 + θ / 2 : ℝ) = -1 + (-(1 / 2) + (θ + 1) / 2) by ring,
    Real.rpow_add ht, Real.rpow_add ht, Real.rpow_neg_one, Real.rpow_neg ht.le]
  have hMnn : 0 ≤ gaussianAbsMoment θ := gaussianAbsMoment_nonneg θ
  have hsqpi : Real.sqrt (4 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hth : (0 : ℝ) < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht _
  apply le_of_eq
  field_simp

/-- Integrability of the `|z|^θ`-weighted `|∂ₓₓheat|`. -/
theorem heatKernel_secondDeriv_weighted_abs_integrable {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    MeasureTheory.Integrable
      (fun w : ℝ => |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| * |w| ^ θ) := by
  set maj : ℝ → ℝ := fun w =>
    heatHessPointwiseBound t * Real.exp (-w ^ 2 / (4 * (2 * t))) * |w| ^ θ with hmaj
  have hmaj_int : MeasureTheory.Integrable maj := by
    rw [hmaj]
    have hbase := integrable_abs_rpow_mul_exp_neg_mul_sq
      (b := 1 / (4 * (2 * t))) (θ := θ) (by positivity) hθ0.le hθ1.le
    have hcongr : (fun w : ℝ =>
        heatHessPointwiseBound t * Real.exp (-w ^ 2 / (4 * (2 * t))) * |w| ^ θ)
        = fun w : ℝ =>
          heatHessPointwiseBound t * (|w| ^ θ * Real.exp (-(1 / (4 * (2 * t))) * w ^ 2)) := by
      funext w
      rw [show -w ^ 2 / (4 * (2 * t)) = -(1 / (4 * (2 * t))) * w ^ 2 by ring]; ring
    rw [hcongr]
    exact hbase.const_mul (heatHessPointwiseBound t)
  refine hmaj_int.mono'
    (((continuous_secondDeriv_heatKernel ht).abs.mul
      (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact mul_le_mul_of_nonneg_right (abs_secondDeriv_heatKernel_le ht w)
    (Real.rpow_nonneg (abs_nonneg _) _)

/-! ## Brick 2 (kernel side) — `∫₀¹ |∂ₓₓK_σ(x,y)| |x−y|^θ dy ≤ Cθ σ^{−1+θ/2}` -/

/-- **Weight domination on a period-`2` cell.**  For `x, y ∈ [0,1]` and any `k`,
`|x − y| ≤ |x − y + 2k|` and `|x − y| ≤ |x + y + 2k|`.  (Both images dominate the
diagonal distance, the geometric fact behind the weighted tiling.) -/
theorem abs_sub_le_image_args {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (k : ℤ) :
    |x - y| ≤ |x - y + 2 * (k : ℝ)| ∧ |x - y| ≤ |x + y + 2 * (k : ℝ)| := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hxy1 : |x - y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  constructor
  · -- `|x−y| ≤ |x−y+2k|`: `k=0` equality; `|k|≥1 ⟹ |x−y+2k| ≥ 2−1 = 1 ≥ |x−y|`.
    rcases eq_or_ne k 0 with hk | hk
    · subst hk; simp
    · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
      have : (1 : ℝ) ≤ |x - y + 2 * (k : ℝ)| := by
        have hge : |x - y + 2 * (k : ℝ)| ≥ 2 * |(k : ℝ)| - |x - y| := by
          have := abs_sub_abs_le_abs_sub (2 * (k : ℝ)) (-(x - y))
          have h2k : |2 * (k : ℝ)| = 2 * |(k : ℝ)| := by rw [abs_mul]; norm_num
          calc |x - y + 2 * (k : ℝ)| = |2 * (k : ℝ) - (-(x - y))| := by ring_nf
            _ ≥ |2 * (k : ℝ)| - |-(x - y)| := abs_sub_abs_le_abs_sub _ _
            _ = 2 * |(k : ℝ)| - |x - y| := by rw [h2k, abs_neg]
        linarith [hge, hxy1, hk1]
      linarith [hxy1]
  · -- `|x−y| ≤ |x+y+2k|`: case on `k ≥ 0` (then `x+y+2k ≥ x+y ≥ |x−y|`) vs `k ≤ −1`.
    have hxy_le : |x - y| ≤ x + y := by rw [abs_le]; constructor <;> linarith
    rcases le_or_gt 0 k with hk | hk
    · have hknn : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hpos : (0 : ℝ) ≤ x + y + 2 * (k : ℝ) := by linarith
      rw [abs_of_nonneg hpos]; linarith
    · have hkle : (k : ℝ) ≤ -1 := by
        have : k ≤ -1 := by omega
        exact_mod_cast this
      have hneg : x + y + 2 * (k : ℝ) ≤ 0 := by linarith
      have hxy2 : |x - y| ≤ -x - y - 2 * (k : ℝ) := by
        rw [abs_le]; constructor <;> linarith
      rw [abs_of_nonpos hneg]; linarith

/-- Abbreviation for the `|w|^θ`-weighted `|∂ₓₓheat|` whole-line integrand. -/
private noncomputable def weightedHeatHess (t θ : ℝ) : ℝ → ℝ :=
  fun w => |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| * |w| ^ θ

/-- **Lattice summability of the weighted heat-Hessian.**  For `t > 0`, `0 ≤ θ ≤ 1`,
`k ↦ weightedHeatHess t θ (z + 2k)` is summable: `|∂ₓₓheat| ≤ Gaussian` and the
polynomial weight `|z+2k|^θ ≤ 2 + (z+2k)²` is absorbed by half the Gaussian
(`s·exp(−s) ≤ 1`), reducing to `latticeExpSummable`. -/
theorem summable_weightedHeatHess_shift {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (z : ℝ) :
    Summable (fun k : ℤ => weightedHeatHess t θ (z + 2 * (k:ℝ))) := by
  set C : ℝ := heatHessPointwiseBound t * (2 + 32 * t) with hC
  have hCnn : 0 ≤ C := by rw [hC]; have := heatHessPointwiseBound_nonneg ht; positivity
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((latticeExpSummable (by positivity : (0:ℝ) < 8 * t) z).mul_left C)
  · rw [weightedHeatHess]; positivity
  · -- `g(z+2k) ≤ C·exp(−(z+2k)²/(4·8t))`.
    rw [weightedHeatHess]
    set r : ℝ := z + 2 * (k:ℝ) with hr
    -- `|∂ₓₓheat r| ≤ heatHessPointwiseBound t · exp(−r²/(4·2t))`.
    have hk := abs_secondDeriv_heatKernel_le ht r
    have hpoly : |r| ^ θ ≤ 2 + r ^ 2 := by
      rcases le_or_gt |r| 1 with h | h
      · calc |r| ^ θ ≤ (1:ℝ) ^ θ := Real.rpow_le_rpow (abs_nonneg _) h hθ0
          _ = 1 := Real.one_rpow _
          _ ≤ 2 + r ^ 2 := by nlinarith [sq_nonneg r]
      · calc |r| ^ θ ≤ |r| ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hθ1
          _ = |r| := Real.rpow_one _
          _ ≤ 2 + r ^ 2 := by nlinarith [sq_nonneg (|r| - 1), sq_abs r]
    -- `(2+r²)·exp(−r²/(4·2t)) ≤ (2+32t)·exp(−r²/(4·8t))`.
    have hgauss : (2 + r ^ 2) * Real.exp (-r ^ 2 / (4 * (2 * t)))
        ≤ (2 + 32 * t) * Real.exp (-r ^ 2 / (4 * (8 * t))) := by
      have hsplit : Real.exp (-r ^ 2 / (4 * (2 * t)))
          = Real.exp (-r ^ 2 / (4 * (8 * t)))
            * (Real.exp (-r ^ 2 / (4 * (8 * t)))
              * (Real.exp (-r ^ 2 / (4 * (8 * t)))
                * Real.exp (-r ^ 2 / (4 * (8 * t))))) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
      have hs : 0 ≤ r ^ 2 / (4 * (8 * t)) := by positivity
      have hmel : (r ^ 2 / (4 * (8 * t))) * Real.exp (-(r ^ 2 / (4 * (8 * t)))) ≤ 1 :=
        real_mul_exp_neg_le_one hs
      have hr2exp : r ^ 2 * Real.exp (-r ^ 2 / (4 * (8 * t))) ≤ 32 * t := by
        have hrw : r ^ 2 * Real.exp (-r ^ 2 / (4 * (8 * t)))
            = (4 * (8 * t)) * ((r ^ 2 / (4 * (8 * t)))
              * Real.exp (-(r ^ 2 / (4 * (8 * t))))) := by
          rw [show -(r ^ 2 / (4 * (8 * t))) = -r ^ 2 / (4 * (8 * t)) by ring]; field_simp
        rw [hrw]; nlinarith [hmel, ht.le]
      have hE1 : Real.exp (-r ^ 2 / (4 * (8 * t))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg r]) (by positivity))
      have hE0 : 0 < Real.exp (-r ^ 2 / (4 * (8 * t))) := Real.exp_pos _
      rw [hsplit]
      set E : ℝ := Real.exp (-r ^ 2 / (4 * (8 * t))) with hE
      -- `(2+r²)·E⁴ = 2E⁴ + (r²E)·E³ ≤ 2E + 32t·E = (2+32t)E`.
      have hE2 : E ^ 2 ≤ E := by nlinarith [hE1, hE0]
      have hE3 : E ^ 3 ≤ E := by nlinarith [hE1, hE0, sq_nonneg E]
      have hE4 : E ^ 4 ≤ E := by nlinarith [hE1, hE0, sq_nonneg E, sq_nonneg (E ^ 2)]
      have hr2E : r ^ 2 * E ≤ 32 * t := hr2exp
      have hbig : (2 + r ^ 2) * (E * (E * (E * E))) ≤ (2 + 32 * t) * E := by
        have hrw : (2 + r ^ 2) * (E * (E * (E * E))) = 2 * E ^ 4 + (r ^ 2 * E) * E ^ 3 := by ring
        rw [hrw]
        have h1 : 2 * E ^ 4 ≤ 2 * E := by linarith [hE4]
        have h2 : (r ^ 2 * E) * E ^ 3 ≤ 32 * t * E := by
          calc (r ^ 2 * E) * E ^ 3 ≤ (32 * t) * E ^ 3 :=
                mul_le_mul_of_nonneg_right hr2E (by positivity)
            _ ≤ (32 * t) * E := mul_le_mul_of_nonneg_left hE3 (by positivity)
        nlinarith [h1, h2]
      exact hbig
    calc |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) r| * |r| ^ θ
        ≤ (heatHessPointwiseBound t * Real.exp (-r ^ 2 / (4 * (2 * t)))) * (2 + r ^ 2) :=
          mul_le_mul hk hpoly (Real.rpow_nonneg (abs_nonneg _) _)
            (by have := heatHessPointwiseBound_nonneg ht; positivity)
      _ = heatHessPointwiseBound t * ((2 + r ^ 2) * Real.exp (-r ^ 2 / (4 * (2 * t)))) := by ring
      _ ≤ heatHessPointwiseBound t * ((2 + 32 * t) * Real.exp (-r ^ 2 / (4 * (8 * t)))) :=
          mul_le_mul_of_nonneg_left hgauss (heatHessPointwiseBound_nonneg ht)
      _ = C * Real.exp (-(z + 2 * (k:ℝ)) ^ 2 / (4 * (8 * t))) := by rw [hC, hr]; ring

/-- **Brick 2 — `|x−y|^θ`-weighted second-derivative kernel mass.**  For `t > 0`,
`0 < θ < 1`, `x ∈ [0,1]`,

  `∫₀¹ |∂ₓₓ K_full(t,x,y)| · |x−y|^θ dy ≤ weightedHeatHessConst θ · t^{−1+θ/2}`.

Dominate `|∂ₓₓK_full|` by the lattice series
(`abs_secondDeriv_intervalNeumannFullKernel_fst_le`); on each cell the weight
`|x−y|^θ ≤ |imageArg|^θ` (`abs_sub_le_image_args`) upgrades the weight onto the
kernel argument, and the cell-tiling identity (`tsum_cell_integral_eq_integral`
with `g = weightedHeatHess`) folds the lattice sum to the whole-line weighted mass
`heatKernel_secondDeriv_weighted_abs_integral_le`. -/
theorem intervalNeumannFullKernel_secondDeriv_weighted_mass {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (∫ y in (0:ℝ)..1,
        |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x|
          * |x - y| ^ θ)
      ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set g : ℝ → ℝ := weightedHeatHess t θ with hg
  have hg_int : MeasureTheory.Integrable g :=
    heatKernel_secondDeriv_weighted_abs_integrable ht hθ0 hθ1
  have hg_nonneg : ∀ w, 0 ≤ g w := fun w => by
    rw [hg, weightedHeatHess]; positivity
  -- per-cell weighted integrand `hk k y`.
  set hk : ℤ → ℝ → ℝ := fun k y => g (x - y + 2 * (k : ℝ)) + g (x + y + 2 * (k : ℝ)) with hk_def
  have hk_nonneg : ∀ k y, 0 ≤ hk k y := fun k y => by
    rw [hk_def]; exact add_nonneg (hg_nonneg _) (hg_nonneg _)
  -- Step 0: pointwise on `[0,1]`, the weighted kernel ≤ `∑ₖ hk k y`.
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 1,
      |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x|
          * |x - y| ^ θ
        ≤ ∑' k : ℤ, hk k y := by
    intro y hy
    have hbase := abs_secondDeriv_intervalNeumannFullKernel_fst_le ht x y
    have hwθ : (0 : ℝ) ≤ |x - y| ^ θ := Real.rpow_nonneg (abs_nonneg _) _
    -- multiply the lattice bound by the weight and distribute (tsum_mul_right).
    have hsumA : Summable (fun k : ℤ =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k:ℝ))|) :=
      summable_abs_iff.mpr (latticeGaussianHessSummable ht (x - y))
    have hsumB : Summable (fun k : ℤ =>
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x + y + 2 * (k:ℝ))|) :=
      summable_abs_iff.mpr (latticeGaussianHessSummable ht (x + y))
    calc |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x|
            * |x - y| ^ θ
        ≤ (∑' k : ℤ,
            (|deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k:ℝ))|
              + |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                  (x + y + 2 * (k:ℝ))|)) * |x - y| ^ θ :=
          mul_le_mul_of_nonneg_right hbase hwθ
      _ = ∑' k : ℤ,
            ((|deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y + 2 * (k:ℝ))|
              + |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                  (x + y + 2 * (k:ℝ))|) * |x - y| ^ θ) := by
          rw [tsum_mul_right]
      _ ≤ ∑' k : ℤ, hk k y := by
          refine Summable.tsum_le_tsum (fun k => ?_) ?_ ?_
          · -- weight upgrade: `(A+B)·|x−y|^θ ≤ A·|arg₁|^θ + B·|arg₂|^θ = hk k y`.
            obtain ⟨hw1, hw2⟩ := abs_sub_le_image_args hx hy k
            have hA : (0:ℝ) ≤ |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                (x - y + 2 * (k:ℝ))| := abs_nonneg _
            have hB : (0:ℝ) ≤ |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
                (x + y + 2 * (k:ℝ))| := abs_nonneg _
            have hwa : |x - y| ^ θ ≤ |x - y + 2 * (k:ℝ)| ^ θ :=
              Real.rpow_le_rpow (abs_nonneg _) hw1 hθ0.le
            have hwb : |x - y| ^ θ ≤ |x + y + 2 * (k:ℝ)| ^ θ :=
              Real.rpow_le_rpow (abs_nonneg _) hw2 hθ0.le
            simp only [hk_def, hg, weightedHeatHess, add_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left hwa hA)
              (mul_le_mul_of_nonneg_left hwb hB)
          · -- summability of the weighted LHS series.
            exact ((hsumA.add hsumB).mul_right (|x - y| ^ θ))
          · -- summability of `hk · y` via the lattice weighted summability helper.
            have hSA := summable_weightedHeatHess_shift ht hθ0.le hθ1.le (x - y)
            have hSB := summable_weightedHeatHess_shift ht hθ0.le hθ1.le (x + y)
            refine (hSA.add hSB).congr (fun k => ?_)
            rw [hk_def, hg]
  -- Step 1: integrate the pointwise bound.
  have hker_ii : IntervalIntegrable
      (fun y : ℝ => |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x|
        * |x - y| ^ θ) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact ((continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x).abs.mul
      (((continuous_abs.comp (by fun_prop)).rpow_const
        (fun _ => Or.inr hθ0.le)).continuousOn))
  -- the tiling series is interval-integrable, and equals `∫_ℝ g` after Tonelli.
  have hcells_int : ∀ k : ℤ, IntervalIntegrable (hk k) MeasureTheory.volume 0 1 := by
    intro k
    have hcontg : Continuous g := by
      simp only [hg, weightedHeatHess]
      exact (continuous_secondDeriv_heatKernel ht).abs.mul
        (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))
    rw [hk_def]
    exact ((hcontg.comp (by fun_prop)).add (hcontg.comp (by fun_prop))).intervalIntegrable 0 1
  -- per-cell integral masses are summable (each pair = cell mass of integrable `g`).
  have hcellmass_summable : Summable (fun k : ℤ =>
      (∫ y in (0:ℝ)..1, g (x - y + 2 * (k:ℝ))) + ∫ y in (0:ℝ)..1, g (x + y + 2 * (k:ℝ))) := by
    have hint : MeasureTheory.IntegrableOn g
        (⋃ k : ℤ, Set.Ioc ((x - 1) + 2 * (k:ℝ)) ((x - 1) + 2 * (k:ℝ) + 2)) := by
      rw [ShenWork.iUnion_Ioc_offset_eq_univ]; exact hg_int.integrableOn
    have hsum := (hasSum_integral_iUnion (fun k : ℤ => measurableSet_Ioc)
      (ShenWork.pairwise_disjoint_Ioc_offset (x - 1)) hint).summable
    refine hsum.congr (fun k => ?_)
    have hset : Set.Ioc ((x - 1) + 2 * (k:ℝ)) ((x - 1) + 2 * (k:ℝ) + 2)
        = Set.Ioc (x + 2 * (k:ℝ) - 1) (x + 2 * (k:ℝ) + 1) := by congr 1 <;> ring
    rw [hset]; exact (ShenWork.cell_integral_eq hg_int x k).symm
  -- bound the per-cell masses by a summable majorant for `continuousOn_tsum`.
  have hcont_pair : ∀ k : ℤ, Continuous (hk k) := by
    intro k
    have hcontg : Continuous g := by
      simp only [hg, weightedHeatHess]
      exact (continuous_secondDeriv_heatKernel ht).abs.mul
        (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))
    rw [hk_def]; exact (hcontg.comp (by fun_prop)).add (hcontg.comp (by fun_prop))
  -- summable window majorant `Wk` for `hk k y`, `y ∈ [0,1]` (committed-style).
  set Wk : ℤ → ℝ := fun k =>
    heatHessWindowBound t x 1 k * (|x + 2 * (k:ℝ)| + 1) ^ θ with hWk
  -- absorption constant `(2 + 32t)`: `(2+r²)·exp(−r²/(16t)) ≤ (2+32t)·exp(−r²/(32t))`.
  have hWk_summable : Summable Wk := by
    set C : ℝ := heatHessPointwiseBound t * Real.exp (1 ^ 2 / (4 * (2 * t)))
      * (2 + 32 * t) with hC
    have hCnn : 0 ≤ C := by rw [hC]; have := heatHessPointwiseBound_nonneg ht; positivity
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      ((latticeExpSummable (by positivity : (0:ℝ) < 8 * t) x).mul_left C)
    · rw [hWk]; unfold heatHessWindowBound heatHessPointwiseBound; positivity
    · -- `Wk k ≤ C·exp(−(x+2k)²/(4·(8t)))`.
      rw [hWk]; unfold heatHessWindowBound
      set r : ℝ := x + 2 * (k:ℝ) with hr
      have hpoly : (|r| + 1) ^ θ ≤ 2 + r ^ 2 := by
        have hbase1 : (1 : ℝ) ≤ |r| + 1 := by linarith [abs_nonneg r]
        have hle1 : (|r| + 1) ^ θ ≤ |r| + 1 := by
          calc (|r| + 1) ^ θ ≤ (|r| + 1) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hbase1 hθ1.le
            _ = |r| + 1 := Real.rpow_one _
        have hquad : |r| + 1 ≤ 2 + r ^ 2 := by nlinarith [sq_nonneg (|r| - 1), sq_abs r]
        linarith
      -- `(2+r²)·exp(−r²/(16t)) ≤ (2+16t)·exp(−r²/(32t))` via `s·exp(−s) ≤ 1`.
      have hgauss : (2 + r ^ 2) * Real.exp (-r ^ 2 / (4 * (4 * t)))
          ≤ (2 + 32 * t) * Real.exp (-r ^ 2 / (4 * (8 * t))) := by
        have hsplit : Real.exp (-r ^ 2 / (4 * (4 * t)))
            = Real.exp (-r ^ 2 / (4 * (8 * t))) * Real.exp (-r ^ 2 / (4 * (8 * t))) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
        have hs : 0 ≤ r ^ 2 / (4 * (8 * t)) := by positivity
        have hmel : (r ^ 2 / (4 * (8 * t))) * Real.exp (-(r ^ 2 / (4 * (8 * t)))) ≤ 1 :=
          real_mul_exp_neg_le_one hs
        have hr2exp : r ^ 2 * Real.exp (-r ^ 2 / (4 * (8 * t))) ≤ 32 * t := by
          have hrw : r ^ 2 * Real.exp (-r ^ 2 / (4 * (8 * t)))
              = (4 * (8 * t)) * ((r ^ 2 / (4 * (8 * t)))
                * Real.exp (-(r ^ 2 / (4 * (8 * t))))) := by
            rw [show -(r ^ 2 / (4 * (8 * t))) = -r ^ 2 / (4 * (8 * t)) by ring]
            field_simp
          rw [hrw]; nlinarith [hmel, ht.le]
        have hE1 : Real.exp (-r ^ 2 / (4 * (8 * t))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg r]) (by positivity))
        have hE0 : 0 < Real.exp (-r ^ 2 / (4 * (8 * t))) := Real.exp_pos _
        rw [hsplit]
        set E : ℝ := Real.exp (-r ^ 2 / (4 * (8 * t))) with hE
        have hbig : (2 + r ^ 2) * (E * E) ≤ (2 + 32 * t) * E := by
          have hrw2 : (2 + r ^ 2) * (E * E) = 2 * E ^ 2 + (r ^ 2 * E) * E := by ring
          rw [hrw2]
          have h1 : 2 * E ^ 2 ≤ 2 * E := by nlinarith [hE1, hE0]
          have h2 : (r ^ 2 * E) * E ≤ 32 * t * E :=
            mul_le_mul_of_nonneg_right hr2exp hE0.le
          nlinarith [h1, h2]
        exact hbig
      -- combine: heatHessPointwiseBound · exp(1/(4·2t)) · [(|r|+1)^θ · exp(−r²/(16t))]
      calc heatHessPointwiseBound t * Real.exp (1 ^ 2 / (4 * (2 * t)))
            * Real.exp (-r ^ 2 / (4 * (4 * t))) * (|r| + 1) ^ θ
          = heatHessPointwiseBound t * Real.exp (1 ^ 2 / (4 * (2 * t)))
              * ((|r| + 1) ^ θ * Real.exp (-r ^ 2 / (4 * (4 * t)))) := by ring
        _ ≤ heatHessPointwiseBound t * Real.exp (1 ^ 2 / (4 * (2 * t)))
              * ((2 + r ^ 2) * Real.exp (-r ^ 2 / (4 * (4 * t)))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by
              have := heatHessPointwiseBound_nonneg ht; positivity)
            exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
        _ ≤ heatHessPointwiseBound t * Real.exp (1 ^ 2 / (4 * (2 * t)))
              * ((2 + 32 * t) * Real.exp (-r ^ 2 / (4 * (8 * t)))) := by
            refine mul_le_mul_of_nonneg_left hgauss (by
              have := heatHessPointwiseBound_nonneg ht; positivity)
        _ = C * Real.exp (-(x + 2 * (k:ℝ)) ^ 2 / (4 * (8 * t))) := by rw [hC, hr]; ring
  -- y-uniform window bound: for `y ∈ [0,1]`, `g(x±y+2k) ≤ Wk k`.
  have hg_window : ∀ (k : ℤ) (s : ℝ), |s| ≤ 1 → g (x + s + 2 * (k:ℝ)) ≤ Wk k := by
    intro k s hs
    rw [hg]; simp only [weightedHeatHess]
    have harg : |x + s + 2 * (k:ℝ) - (x + 2 * (k:ℝ))| ≤ 1 := by
      rw [show x + s + 2 * (k:ℝ) - (x + 2 * (k:ℝ)) = s by ring]; exact hs
    have hHess := abs_secondDeriv_heatKernel_le_windowShift ht x 1 k harg
    have hwt : |x + s + 2 * (k:ℝ)| ^ θ ≤ (|x + 2 * (k:ℝ)| + 1) ^ θ := by
      refine Real.rpow_le_rpow (abs_nonneg _) ?_ hθ0.le
      calc |x + s + 2 * (k:ℝ)| ≤ |x + 2 * (k:ℝ)| + |s| := by
            rw [show x + s + 2 * (k:ℝ) = (x + 2 * (k:ℝ)) + s by ring]; exact abs_add_le _ _
        _ ≤ |x + 2 * (k:ℝ)| + 1 := by linarith
    rw [hWk]
    exact mul_le_mul hHess hwt (Real.rpow_nonneg (abs_nonneg _) _)
      (by unfold heatHessWindowBound heatHessPointwiseBound; positivity)
  have hk_bound : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Icc (0:ℝ) 1 → ‖hk k y‖ ≤ 2 * Wk k := by
    intro k y hy
    have hkn : 0 ≤ hk k y := hk_nonneg k y
    rw [Real.norm_eq_abs, abs_of_nonneg hkn, hk_def]
    have h1 : g (x - y + 2 * (k:ℝ)) ≤ Wk k := by
      have := hg_window k (-y) (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hy.1],
        by linarith [hy.2]⟩)
      rwa [show x + -y + 2 * (k:ℝ) = x - y + 2 * (k:ℝ) by ring] at this
    have h2 : g (x + y + 2 * (k:ℝ)) ≤ Wk k :=
      hg_window k y (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    linarith
  -- `hDii`: the tiling tsum is interval-integrable (continuousOn_tsum + window majorant).
  have hDii : IntervalIntegrable (fun y : ℝ => ∑' k : ℤ, hk k y) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_tsum (fun k => (hcont_pair k).continuousOn)
      (hWk_summable.mul_left 2) hk_bound
  -- Step 2a: `∫₀¹ weightedKernel ≤ ∫₀¹ ∑ₖ hk`.
  have hmono : (∫ y in (0:ℝ)..1,
        |deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x|
          * |x - y| ^ θ)
      ≤ ∫ y in (0:ℝ)..1, ∑' k : ℤ, hk k y :=
    intervalIntegral.integral_mono_on h01 hker_ii hDii (fun y hy => hpt y hy)
  refine hmono.trans ?_
  -- Step 2b: Tonelli `∫₀¹ ∑ₖ hk = ∑ₖ ∫₀¹ hk = ∫_ℝ g`, then the whole-line weighted bound.
  have hμint : ∀ k : ℤ,
      MeasureTheory.Integrable (hk k) (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    fun k => (intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp (hcells_int k)
  have hg_compA : ∀ k : ℤ, IntervalIntegrable (fun y : ℝ => g (x - y + 2 * (k:ℝ)))
      MeasureTheory.volume 0 1 := fun k => by
    rw [hg]
    exact (((continuous_secondDeriv_heatKernel ht).abs.mul
      (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))).comp
        (by fun_prop : Continuous fun y : ℝ => x - y + 2 * (k:ℝ))).intervalIntegrable 0 1
  have hg_compB : ∀ k : ℤ, IntervalIntegrable (fun y : ℝ => g (x + y + 2 * (k:ℝ)))
      MeasureTheory.volume 0 1 := fun k => by
    rw [hg]
    exact (((continuous_secondDeriv_heatKernel ht).abs.mul
      (continuous_abs.rpow_const (fun _ => Or.inr hθ0.le))).comp
        (by fun_prop : Continuous fun y : ℝ => x + y + 2 * (k:ℝ))).intervalIntegrable 0 1
  have hk_split : ∀ k : ℤ, (∫ y in (0:ℝ)..1, hk k y)
      = (∫ y in (0:ℝ)..1, g (x - y + 2 * (k:ℝ)))
        + ∫ y in (0:ℝ)..1, g (x + y + 2 * (k:ℝ)) := by
    intro k
    have hfun : (fun y : ℝ => hk k y)
        = fun y : ℝ => g (x - y + 2 * (k:ℝ)) + g (x + y + 2 * (k:ℝ)) := by
      funext y; rw [hk_def]
    rw [hfun, intervalIntegral.integral_add (hg_compA k) (hg_compB k)]
  have hμnorm_summable : Summable
      (fun k : ℤ => ∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    refine hcellmass_summable.congr (fun k => ?_)
    have he : (∫ y, ‖hk k y‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)))
        = ∫ y in (0:ℝ)..1, hk k y := by
      rw [intervalIntegral.integral_of_le h01]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (hk_nonneg k y))
    rw [he, hk_split k]
  have hTonelli := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) (F := hk) hμint hμnorm_summable
  have hval : (∫ y in (0:ℝ)..1, ∑' k : ℤ, hk k y) = ∫ w : ℝ, g w := by
    calc (∫ y in (0:ℝ)..1, ∑' k : ℤ, hk k y)
        = ∫ y, (∑' k : ℤ, hk k y) ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
          intervalIntegral.integral_of_le h01
      _ = ∑' k : ℤ, ∫ y, hk k y ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) :=
          hTonelli.symm
      _ = ∑' k : ℤ, ((∫ y in (0:ℝ)..1, g (x - y + 2 * (k:ℝ)))
            + ∫ y in (0:ℝ)..1, g (x + y + 2 * (k:ℝ))) := by
          refine tsum_congr (fun k => ?_)
          rw [← intervalIntegral.integral_of_le h01]; exact hk_split k
      _ = ∫ w : ℝ, g w := ShenWork.tsum_cell_integral_eq_integral hg_int x
  rw [hval]
  -- whole-line weighted mass bound.
  have hwhole : (∫ w : ℝ, g w) ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ) := by
    rw [hg]; simp only [weightedHeatHess]
    exact heatKernel_secondDeriv_weighted_abs_integral_le ht hθ0 hθ1
  exact hwhole

/-! ## Brick 3 — `C^θ → L∞` second-derivative operator bound -/

/-- **Brick 3 — `‖∂ₓₓ S(σ)h‖∞ ≤ Cθ σ^{−1+θ/2} [h]_θ`.**  For `t > 0`, `0 < θ < 1`,
bounded measurable `h` (`|h| ≤ Ch`) with Hölder modulus `Hh` (`|h(a)−h(b)| ≤ Hh|a−b|^θ`),
and `x ∈ [0,1]`,

  `|∂ₓₓ S(t)h(x)| ≤ weightedHeatHessConst θ · t^{−1+θ/2} · Hh`.

The second `x`-derivative of the propagator is `∫ ∂ₓₓ K(x,y) h(y) dμ`
(`intervalFullSemigroupOperator_hasDerivAt_deriv_fst`); the mean-zero cancellation
`∫ ∂ₓₓ K(x,·) = 0` (brick 1) lets us subtract `h(x)`:
`∂ₓₓ S(t)h(x) = ∫ ∂ₓₓ K(x,y) (h(y) − h(x)) dμ`, bounded in absolute value by
`Hh · ∫₀¹ |∂ₓₓ K(x,y)| |x − y|^θ dy ≤ Hh · Cθ t^{−1+θ/2}` (brick 2). -/
theorem neumannHeatSecondDeriv_Ctheta_to_Linfty {t θ : ℝ} (ht : 0 < t)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {h : ℝ → ℝ}
    (hh_meas : AEStronglyMeasurable h (intervalMeasure 1))
    {Ch : ℝ} (hh : ∀ y, |h y| ≤ Ch) {Hh : ℝ} (hHh_nn : 0 ≤ Hh)
    (hHh : ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → |h a - h b| ≤ Hh * |a - b| ^ θ)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |deriv (fun z : ℝ => deriv (fun w : ℝ => intervalFullSemigroupOperator t h w) z) x|
      ≤ weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ) * Hh := by
  classical
  -- the second-derivative integral representation.
  have hrepr := (intervalFullSemigroupOperator_hasDerivAt_deriv_fst ht hh_meas hh x).deriv
  rw [hrepr]
  -- abbreviations.
  set K : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) z) x with hK
  -- `K` is integrable on `[0,1]` and `K·h` integrable.
  have hKcont : ContinuousOn K (Set.Icc 0 1) :=
    continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x
  have hKint : MeasureTheory.Integrable K (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]; exact hKcont.integrableOn_Icc
  have hbdd : ∀ᵐ y ∂(intervalMeasure 1), ‖h y‖ ≤ Ch :=
    Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hh y
  have hKhint : MeasureTheory.Integrable (fun y => K y * h y) (intervalMeasure 1) :=
    hKint.mul_bdd hh_meas hbdd
  -- mean-zero cancellation: `∫ K·h(x) = h(x)·∫ K = 0`.
  have hmean0 : (∫ y, K y ∂(intervalMeasure 1)) = 0 :=
    intervalNeumannFullKernel_secondDeriv_integral_zero ht x
  have hsub : (∫ y, K y * h y ∂(intervalMeasure 1))
      = ∫ y, K y * (h y - h x) ∂(intervalMeasure 1) := by
    have hxint : MeasureTheory.Integrable (fun y => K y * h x) (intervalMeasure 1) :=
      hKint.mul_const (h x)
    rw [show (fun y => K y * (h y - h x)) = (fun y => K y * h y - K y * h x) from by
        funext y; ring,
      MeasureTheory.integral_sub hKhint hxint,
      show (fun y => K y * h x) = (fun y => h x * K y) from by funext y; ring,
      MeasureTheory.integral_const_mul, hmean0, mul_zero, sub_zero]
  rw [hsub]
  -- bound by the weighted kernel mass times the Hölder modulus.
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 1, ‖K y * (h y - h x)‖ ≤ Hh * (|K y| * |x - y| ^ θ) := by
    intro y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hhy := hHh y x hy hx
    have hsymm : |y - x| ^ θ = |x - y| ^ θ := by rw [abs_sub_comm]
    rw [hsymm] at hhy
    calc |K y| * |h y - h x| ≤ |K y| * (Hh * |x - y| ^ θ) :=
          mul_le_mul_of_nonneg_left hhy (abs_nonneg _)
      _ = Hh * (|K y| * |x - y| ^ θ) := by ring
  -- integrate.
  have hweight_int : MeasureTheory.Integrable
      (fun y => |K y| * |x - y| ^ θ) (intervalMeasure 1) := by
    simp only [intervalMeasure, intervalSet]
    exact (hKcont.abs.mul (((continuous_abs.comp (by fun_prop)).rpow_const
      (fun _ => Or.inr hθ0.le)).continuousOn)).integrableOn_Icc
  calc |∫ y, K y * (h y - h x) ∂(intervalMeasure 1)|
      ≤ ∫ y, ‖K y * (h y - h x)‖ ∂(intervalMeasure 1) := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, Hh * (|K y| * |x - y| ^ θ) ∂(intervalMeasure 1) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hweight_int.const_mul Hh) ?_
        simp only [intervalMeasure, intervalSet]
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall fun y hy => hpt y hy)
    _ = Hh * ∫ y, |K y| * |x - y| ^ θ ∂(intervalMeasure 1) := MeasureTheory.integral_const_mul _ _
    _ ≤ Hh * (weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hHh_nn
        have hcv : (∫ y, |K y| * |x - y| ^ θ ∂(intervalMeasure 1))
            = ∫ y in (0:ℝ)..1, |K y| * |x - y| ^ θ := by
          simp only [intervalMeasure, intervalSet]
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
        rw [hcv, hK]
        exact intervalNeumannFullKernel_secondDeriv_weighted_mass ht hθ0 hθ1 hx
    _ = weightedHeatHessConst θ * t ^ (-1 + θ / 2 : ℝ) * Hh := by ring

/-! ## Duhamel-time wrappers for the cancellative second-derivative bound -/

/-- The cancellative Hessian time kernel is interval-integrable on `[0,t]`:
`s ↦ (t-s)^{-1+θ/2}` has exponent strictly larger than `-1` as soon as `θ > 0`. -/
theorem intervalIntegrable_sub_rpow_hessian {t θ : ℝ} (hθ0 : 0 < θ) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + θ / 2 : ℝ)) volume 0 t := by
  have hr : (-1 : ℝ) < -1 + θ / 2 := by linarith
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-1 + θ / 2 : ℝ)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) hr
  have h := (h0.comp_sub_left t).symm
  simpa using h

/-- Time-kernel evaluation for the cancellative Hessian exponent:
`∫₀ᵗ (t-s)^{-1+θ/2} ds = t^{θ/2}/(θ/2)`. -/
theorem integral_sub_rpow_hessian {t θ : ℝ} (_ht : 0 ≤ t) (hθ0 : 0 < θ) :
    (∫ s in (0 : ℝ)..t, (t - s) ^ (-1 + θ / 2 : ℝ))
      = t ^ (θ / 2 : ℝ) / (θ / 2) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-1 + θ / 2 : ℝ)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -1 + θ / 2))]
  have hexp : (-1 + θ / 2 : ℝ) + 1 = θ / 2 := by ring
  have hθhalf_ne : (θ / 2 : ℝ) ≠ 0 := by linarith
  rw [hexp, Real.zero_rpow hθhalf_ne, sub_zero]

/-- Uniform small-time bound for the second-derivative Duhamel term under a uniform
`C^θ` modulus of the source slices.  This is the Duhamel-time form of
`neumannHeatSecondDeriv_Ctheta_to_Linfty`, with the integrable
`(t-s)^{-1+θ/2}` singularity explicitly evaluated. -/
theorem secondDerivDuhamel_sup_bound_Ctheta
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {q : ℝ → ℝ → ℝ} {Cq Hq : ℝ}
    (hHq_nn : 0 ≤ Hq)
    (hq_meas : ∀ s, AEStronglyMeasurable (q s) (intervalMeasure 1))
    (hq_bound : ∀ s y, |q s y| ≤ Cq)
    (hq_holder : ∀ s a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |q s a - q s b| ≤ Hq * |a - b| ^ θ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (h2_int : IntervalIntegrable
      (fun s : ℝ => deriv (fun z : ℝ => deriv
        (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x)
      volume 0 t) :
    |∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x|
      ≤ weightedHeatHessConst θ * (t ^ (θ / 2 : ℝ) / (θ / 2)) * Hq := by
  set Cθ : ℝ := weightedHeatHessConst θ with hCθ
  have hdom_int : IntervalIntegrable
      (fun s : ℝ => Cθ * (t - s) ^ (-1 + θ / 2 : ℝ) * Hq) volume 0 t :=
    (((intervalIntegrable_sub_rpow_hessian (t := t) hθ0).const_mul Cθ).mul_const Hq)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s : ℝ => |deriv (fun z : ℝ => deriv
        (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x|)
      ≤ᵐ[volume.restrict (Set.Icc 0 t)]
      (fun s : ℝ => Cθ * (t - s) ^ (-1 + θ / 2 : ℝ) * Hq) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hs_ne hs_mem
    have hs_lt : s < t := lt_of_le_of_ne hs_mem.2 hs_ne
    have hts : 0 < t - s := sub_pos.mpr hs_lt
    simpa [hCθ] using
      (neumannHeatSecondDeriv_Ctheta_to_Linfty hts hθ0 hθ1 (hq_meas s)
        (hq_bound s) hHq_nn (hq_holder s) hx)
  calc |∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ => deriv
            (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x|
      ≤ ∫ s in (0 : ℝ)..t, |deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x| :=
        intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0 : ℝ)..t, Cθ * (t - s) ^ (-1 + θ / 2 : ℝ) * Hq :=
        intervalIntegral.integral_mono_ae_restrict ht.le h2_int.abs hdom_int hae
    _ = Cθ * (t ^ (θ / 2 : ℝ) / (θ / 2)) * Hq := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
          integral_sub_rpow_hessian ht.le hθ0]
    _ = weightedHeatHessConst θ * (t ^ (θ / 2 : ℝ) / (θ / 2)) * Hq := by rw [hCθ]

/-- Zero-time vanishing of the second-derivative Duhamel integral under a uniform
`C^θ` source modulus.  This is the cancellative chemotaxis-leg analogue of the
gradient-Duhamel `O(√t)` zero-time wrapper: the time singularity integrates to
`O(t^{θ/2})`. -/
theorem secondDerivDuhamel_tendsto_zero_of_uniform_holder
    {q : ℝ → ℝ → ℝ} {θ Cq Hq : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHq_nn : 0 ≤ Hq)
    (hq_meas : ∀ s, AEStronglyMeasurable (q s) (intervalMeasure 1))
    (hq_bound : ∀ s y, |q s y| ≤ Cq)
    (hq_holder : ∀ s a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |q s a - q s b| ≤ Hq * |a - b| ^ θ)
    (h2_int : ∀ {t x : ℝ}, 0 < t →
      IntervalIntegrable
        (fun s : ℝ => deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x)
        volume 0 t) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → ∀ x : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 →
      |∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ => deriv
            (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x| < ε := by
  intro ε hε
  let A : ℝ := weightedHeatHessConst θ * (1 / (θ / 2)) * Hq
  have hθhalf_pos : 0 < θ / 2 := by linarith
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (weightedHeatHessConst_nonneg θ) (by positivity))
      hHq_nn
  let δ : ℝ := (ε / (A + 1)) ^ (2 / θ : ℝ)
  have hbase_pos : 0 < ε / (A + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ x hx
  have hbound := secondDerivDuhamel_sup_bound_Ctheta (t := t) (θ := θ) ht hθ0 hθ1
    (q := q) (Cq := Cq) (Hq := Hq) hHq_nn hq_meas hq_bound hq_holder
    x hx (h2_int (t := t) (x := x) ht)
  have hδpow : δ ^ (θ / 2 : ℝ) = ε / (A + 1) := by
    dsimp [δ]
    rw [← Real.rpow_mul hbase_pos.le]
    have hmul : (2 / θ : ℝ) * (θ / 2) = 1 := by field_simp [ne_of_gt hθ0]
    rw [hmul, Real.rpow_one]
  have htpow_bound : t ^ (θ / 2 : ℝ) < ε / (A + 1) := by
    calc t ^ (θ / 2 : ℝ) < δ ^ (θ / 2 : ℝ) :=
          Real.rpow_lt_rpow ht.le htδ hθhalf_pos
      _ = ε / (A + 1) := hδpow
  have htail : weightedHeatHessConst θ * (t ^ (θ / 2 : ℝ) / (θ / 2)) * Hq < ε := by
    have hA_lt : A * t ^ (θ / 2 : ℝ) < ε := by
      have hden_pos : 0 < A + 1 := by linarith
      have hA_step : A * t ^ (θ / 2 : ℝ) ≤ A * (ε / (A + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt htpow_bound) hA_nonneg
      have hfrac_lt : A * (ε / (A + 1)) < ε := by
        calc
          A * (ε / (A + 1)) = (A * ε) / (A + 1) := by ring
          _ < ε := by
            rw [div_lt_iff₀ hden_pos]
            nlinarith [hε]
      exact lt_of_le_of_lt hA_step hfrac_lt
    simpa [A, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hA_lt
  exact lt_of_le_of_lt hbound htail

/-- Zero-time vanishing of the spatial derivative of a full-kernel gradient-Duhamel
leg, assuming the derivative-under-the-time-integral identity. -/
theorem gradDuhamel_deriv_tendsto_zero_of_uniform_holder
    {q : ℝ → ℝ → ℝ} {θ Cq Hq : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hHq_nn : 0 ≤ Hq)
    (hq_meas : ∀ s, AEStronglyMeasurable (q s) (intervalMeasure 1))
    (hq_bound : ∀ s y, |q s y| ≤ Cq)
    (hq_holder : ∀ s a b, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |q s a - q s b| ≤ Hq * |a - b| ^ θ)
    (h2_int : ∀ {t x : ℝ}, 0 < t →
      IntervalIntegrable
        (fun s : ℝ => deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x)
        volume 0 t)
    (hLeibniz : ∀ {t x : ℝ}, 0 < t →
      deriv (fun y : ℝ =>
        ∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) y) x =
      ∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ => deriv
          (fun w : ℝ => intervalFullSemigroupOperator (t - s) (q s) w) z) x) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → ∀ x : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 →
      |deriv (fun y : ℝ =>
        ∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) y) x| < ε := by
  intro ε hε
  rcases secondDerivDuhamel_tendsto_zero_of_uniform_holder
      hθ0 hθ1 hHq_nn hq_meas hq_bound hq_holder h2_int ε hε with
    ⟨δ, hδ, hδsmall⟩
  exact ⟨δ, hδ, fun t ht htδ x hx => by
    rw [hLeibniz (t := t) (x := x) ht]
    exact hδsmall t ht htδ x hx⟩

end ShenWork.IntervalNeumannFullKernel
