/-
  ShenWork/PDE/IntervalGradDuhamelBound.lean

  T7 existence — **Atom D**: linear C⁰ estimates for the weak / gradient-Duhamel
  maps.  These are the heat-semigroup half of the mild fixed-point contraction
  (Atom E); they are LINEAR and POSITIVITY-FREE (no `R ≥ 0` needed).

  Targets:
  * value Duhamel sup bound  `‖∫₀ᵗ S(t−s) r ds‖_{T,∞} ≤ T·‖r‖_{T,∞}`;
  * gradient Duhamel sup bound  `‖∫₀ᵗ ∂ₓS(t−s) q ds‖_{T,∞} ≤ C·√T·‖q‖_{T,∞}`
    (divergence form: `∂ₓ` is INSIDE on `S(t−s)`, so NO Leibniz interchange is
    needed — unlike the gradient-of-value form; the singular factor
    `(t−s)^{−1/2}` from T1's `intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t`
    is absorbed by `∫₀ᵗ (t−s)^{−1/2} ds = 2√t`);
  * difference Lipschitz (linear ⟹ same bounds on the difference);
  * continuous source ⟹ continuous mild path.

  This file starts with the calculus core `∫₀ᵗ (t−s)^{−1/2} ds = 2√t`.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ShenWork.PDE.IntervalFullKernelGradEstimate
import ShenWork.PDE.IntervalFullKernelSupBound

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant
  heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.IntervalGradDuhamelBound

/-- **The parabolic √-integral.**  `∫₀ᵗ (t−s)^{−1/2} ds = 2√t` (`t ≥ 0`):
substitute `u = t − s` then `integral_rpow` with `r = −1/2 > −1`.  This is the
finite value of the (improperly singular at `s = t`) gradient-Duhamel kernel
integral that absorbs the `(t−s)^{−1/2}` semigroup-gradient blow-up. -/
theorem integral_sub_rpow_neg_half {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, (t - s) ^ (-(1/2) : ℝ)) = 2 * Real.sqrt t := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1/2) : ℝ)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1/2)))]
  have hexp : (-(1/2) : ℝ) + 1 = 1/2 := by norm_num
  rw [hexp, Real.zero_rpow (by norm_num : (1/2 : ℝ) ≠ 0), sub_zero,
    Real.sqrt_eq_rpow]
  rw [div_eq_iff (by norm_num : (1/2 : ℝ) ≠ 0)]
  ring

/-- **`(t−s)^{−1/2}` is interval-integrable on `[0,t]`** (`−1 < −1/2`, via
`intervalIntegrable_rpow'` composed with `s ↦ t − s`). -/
theorem intervalIntegrable_sub_rpow_neg_half (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1/2) : ℝ)) volume 0 t := by
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ (-(1/2) : ℝ)) volume 0 t :=
    intervalIntegrable_rpow' (by norm_num)
  have h := (h0.comp_sub_left t).symm
  simpa using h

/-- **Atom D — gradient-Duhamel sup bound (divergence form).**  For a source path
`q` bounded by `Cq`, the divergence-form gradient-Duhamel integral
`∫₀ᵗ ∂ₓS(t−s) q(s) ds` (with `∂ₓ` INSIDE `S`, so no Leibniz interchange) is
bounded uniformly in `t ≤ T` by `Cgrad·2√T·Cq`.  The singular `(t−s)^{−1/2}`
per-slice gradient (T1) is integrated by `∫₀ᵗ (t−s)^{−1/2} ds = 2√t ≤ 2√T`.

The gradient-field interval-integrability `hg_int` is a named regularity
prerequisite (it follows from continuity of the mild path; discharged
separately, à la T2's `hGrad_int`) — NOT the conclusion: the analytic content
is the `√T` absorption proved here. -/
theorem gradDuhamel_sup_bound
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ)
    (hg_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x) volume 0 t) :
    |∫ s in (0:ℝ)..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq := by
  set Cg := heatGradientLinftyLinftyConstant with hCgdef
  have hCgnn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
  -- per-slice pointwise gradient bound on `s < t`.
  have hptw : ∀ s, 0 ≤ s → s < t →
      |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
        ≤ Cg * Cq * (t - s) ^ (-(1/2) : ℝ) := by
    intro s hs0 hst
    have h := intervalFullCoupledDuhamel_grad_integrand_pointwise_bound
      hs0 hst (hq_int s) hCq (hq_sup s) x
    calc |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
        ≤ Cg * (t - s) ^ (-(1/2) : ℝ) * Cq := h
      _ = Cg * Cq * (t - s) ^ (-(1/2) : ℝ) := by ring
  -- the dominating integrand.
  have hdom_int : IntervalIntegrable
      (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) volume 0 t :=
    ((intervalIntegrable_sub_rpow_neg_half t).const_mul (Cg * Cq))
  -- a.e. domination of `|g|` on `[0,t]` (the bound holds for `s < t`; `{t}` null).
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s : ℝ => |deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|)
      ≤ᵐ[volume.restrict (Set.Icc 0 t)]
      (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hs_ne hs_mem
    exact hptw s hs_mem.1 (lt_of_le_of_ne hs_mem.2 hs_ne)
  calc |∫ s in (0:ℝ)..t, deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
      ≤ ∫ s in (0:ℝ)..t, |deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x| :=
        intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0:ℝ)..t, Cg * Cq * (t - s) ^ (-(1/2) : ℝ) :=
        intervalIntegral.integral_mono_ae_restrict ht.le hg_int.abs hdom_int hae
    _ = Cg * Cq * (2 * Real.sqrt t) := by
        rw [intervalIntegral.integral_const_mul, integral_sub_rpow_neg_half ht.le]
    _ ≤ Cg * (2 * Real.sqrt T) * Cq := by
        have hsqrt : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
        have hsqT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
        nlinarith [hCgnn, hCq, Real.sqrt_nonneg t, hsqrt, mul_nonneg hCgnn hCq]

/-- **Atom D — value-Duhamel sup bound.**  For a source path `r` bounded by `Cr`,
the value-Duhamel integral `∫₀ᵗ S(t−s) r(s) ds` is bounded by `T·Cr`.  The
non-singular per-slice value (semigroup `L∞`-contraction
`intervalFullSemigroupOperator_Linfty_bound`, `|S(τ)f| ≤ Cr`) integrates against
the length `t ≤ T`.  `hr_int` is the (continuity-derivable) integrability
prerequisite. -/
theorem valueDuhamel_sup_bound
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {r : ℝ → ℝ → ℝ}
    {Cr : ℝ} (hCr : 0 ≤ Cr) (hr_sup : ∀ s y, |r s y| ≤ Cr) (x : ℝ)
    (hr_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (r s) x) volume 0 t) :
    |∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r s) x| ≤ T * Cr := by
  have hptw : ∀ s, 0 ≤ s → s < t →
      |intervalFullSemigroupOperator (t - s) (r s) x| ≤ Cr := fun s _ hst =>
    intervalFullSemigroupOperator_Linfty_bound (sub_pos.mpr hst) hCr (hr_sup s) x
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae : (fun s : ℝ => |intervalFullSemigroupOperator (t - s) (r s) x|)
      ≤ᵐ[volume.restrict (Set.Icc 0 t)] (fun _ : ℝ => Cr) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hs_ne hs_mem
    exact hptw s hs_mem.1 (lt_of_le_of_ne hs_mem.2 hs_ne)
  calc |∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r s) x|
      ≤ ∫ s in (0:ℝ)..t, |intervalFullSemigroupOperator (t - s) (r s) x| :=
        intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ _s in (0:ℝ)..t, Cr :=
        intervalIntegral.integral_mono_ae_restrict ht.le hr_int.abs
          (_root_.intervalIntegrable_const) hae
    _ = t * Cr := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    _ ≤ T * Cr := by gcongr

/-! ## Atom D — difference Lipschitz (semigroup linearity)

The maps are LINEAR in the source, so the difference of two Duhamel images is the
Duhamel image of the difference source; the sup bounds then apply to `r₁ − r₂`. -/

/-- **Semigroup linearity.**  `S(τ)(f − g) = S(τ)f − S(τ)g` (the operator is
`∫ K·(·)`, so this is `integral_sub` once the kernel-weighted integrands are
integrable). -/
theorem intervalFullSemigroupOperator_sub {τ x : ℝ} {f g : ℝ → ℝ}
    (hf : Integrable (fun y => intervalNeumannFullKernel τ x y * f y) (intervalMeasure 1))
    (hg : Integrable (fun y => intervalNeumannFullKernel τ x y * g y) (intervalMeasure 1)) :
    intervalFullSemigroupOperator τ (fun y => f y - g y) x
      = intervalFullSemigroupOperator τ f x - intervalFullSemigroupOperator τ g x := by
  unfold intervalFullSemigroupOperator
  have hpt : (fun y => intervalNeumannFullKernel τ x y * (f y - g y))
      = (fun y => intervalNeumannFullKernel τ x y * f y
          - intervalNeumannFullKernel τ x y * g y) := by
    funext y; ring
  rw [hpt, MeasureTheory.integral_sub hf hg]

/-- **Atom D — value-Duhamel difference Lipschitz.**  By linearity the difference
of two value-Duhamel images equals the value-Duhamel image of the source
difference, so `|∫₀ᵗ (S(t−s)r₁ − S(t−s)r₂) ds| ≤ T·D` whenever `|r₁ − r₂| ≤ D`.
`hKr₁/hKr₂` are the per-slice kernel-integrability prerequisites used by the
linearity split (honest regularity inputs, NOT the conclusion). -/
theorem valueDuhamel_diff_sup_bound
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {r₁ r₂ : ℝ → ℝ → ℝ}
    {D : ℝ} (hD : 0 ≤ D) (hr_diff : ∀ s y, |r₁ s y - r₂ s y| ≤ D) (x : ℝ)
    (hKr₁ : ∀ s, Integrable
      (fun y => intervalNeumannFullKernel (t - s) x y * r₁ s y) (intervalMeasure 1))
    (hKr₂ : ∀ s, Integrable
      (fun y => intervalNeumannFullKernel (t - s) x y * r₂ s y) (intervalMeasure 1))
    (hdiff_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (fun y => r₁ s y - r₂ s y) x)
      volume 0 t) :
    |∫ s in (0:ℝ)..t, (intervalFullSemigroupOperator (t - s) (r₁ s) x
        - intervalFullSemigroupOperator (t - s) (r₂ s) x)| ≤ T * D := by
  have hcongr : (fun s : ℝ => intervalFullSemigroupOperator (t - s) (r₁ s) x
        - intervalFullSemigroupOperator (t - s) (r₂ s) x)
      = fun s : ℝ => intervalFullSemigroupOperator (t - s) (fun y => r₁ s y - r₂ s y) x := by
    funext s
    rw [intervalFullSemigroupOperator_sub (hKr₁ s) (hKr₂ s)]
  rw [intervalIntegral.integral_congr (g := fun s : ℝ =>
        intervalFullSemigroupOperator (t - s) (fun y => r₁ s y - r₂ s y) x)
      (fun s _ => congrFun hcongr s)]
  exact valueDuhamel_sup_bound ht htT hD hr_diff x hdiff_int

/-- **Gradient semigroup linearity.**  `∂ₓ(S(τ)(f−g)) = ∂ₓ(S(τ)f) − ∂ₓ(S(τ)g)`:
the function-level `intervalFullSemigroupOperator_sub` (at every `z`) plus
`deriv_sub`. -/
theorem intervalFullSemigroupOperator_deriv_sub {τ x : ℝ} {f g : ℝ → ℝ}
    (hKf : ∀ z, Integrable
      (fun y => intervalNeumannFullKernel τ z y * f y) (intervalMeasure 1))
    (hKg : ∀ z, Integrable
      (fun y => intervalNeumannFullKernel τ z y * g y) (intervalMeasure 1))
    (hdf : DifferentiableAt ℝ (fun z => intervalFullSemigroupOperator τ f z) x)
    (hdg : DifferentiableAt ℝ (fun z => intervalFullSemigroupOperator τ g z) x) :
    deriv (fun z => intervalFullSemigroupOperator τ (fun y => f y - g y) z) x
      = deriv (fun z => intervalFullSemigroupOperator τ f z) x
        - deriv (fun z => intervalFullSemigroupOperator τ g z) x := by
  have hfun : (fun z => intervalFullSemigroupOperator τ (fun y => f y - g y) z)
      = (fun z => intervalFullSemigroupOperator τ f z
          - intervalFullSemigroupOperator τ g z) := by
    funext z; exact intervalFullSemigroupOperator_sub (hKf z) (hKg z)
  rw [hfun]; exact deriv_sub hdf hdg

/-- **Atom D — gradient-Duhamel difference Lipschitz.**  By gradient linearity the
difference of two gradient-Duhamel images equals the gradient-Duhamel image of
the source difference, so `|∫₀ᵗ (∂ₓS(t−s)q₁ − ∂ₓS(t−s)q₂) ds| ≤ Cgrad·2√T·D`
whenever `|q₁ − q₂| ≤ D`.  `hKq₁/hKq₂` (per-`(s,z)` kernel integrability) and
`hd₁/hd₂` (per-slice spatial differentiability, from T1) are the honest
regularity inputs of the linearity split. -/
theorem gradDuhamel_diff_sup_bound
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q₁ q₂ : ℝ → ℝ → ℝ}
    {D : ℝ} (hD : 0 ≤ D) (hq_diff : ∀ s y, |q₁ s y - q₂ s y| ≤ D)
    (hq_int_diff : ∀ s, Integrable (fun y => q₁ s y - q₂ s y) (intervalMeasure 1))
    (x : ℝ)
    (hKq₁ : ∀ s z, Integrable
      (fun y => intervalNeumannFullKernel (t - s) z y * q₁ s y) (intervalMeasure 1))
    (hKq₂ : ∀ s z, Integrable
      (fun y => intervalNeumannFullKernel (t - s) z y * q₂ s y) (intervalMeasure 1))
    (hd₁ : ∀ s, 0 ≤ s → s < t →
      DifferentiableAt ℝ (fun z => intervalFullSemigroupOperator (t - s) (q₁ s) z) x)
    (hd₂ : ∀ s, 0 ≤ s → s < t →
      DifferentiableAt ℝ (fun z => intervalFullSemigroupOperator (t - s) (q₂ s) z) x)
    (hg_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (fun y => q₁ s y - q₂ s y) z) x)
      volume 0 t) :
    |∫ s in (0:ℝ)..t,
        (deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q₁ s) z) x
          - deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q₂ s) z) x)|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * D := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hcongr : ∀ᵐ s : ℝ ∂volume, s ∈ Set.uIoc 0 t →
      deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q₁ s) z) x
          - deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q₂ s) z) x
        = deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (fun y => q₁ s y - q₂ s y) z) x := by
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Set.uIoc_of_le ht.le] at hs_mem
    have hst : s < t := lt_of_le_of_ne hs_mem.2 hs_ne
    exact (intervalFullSemigroupOperator_deriv_sub (hKq₁ s) (hKq₂ s)
      (hd₁ s hs_mem.1.le hst) (hd₂ s hs_mem.1.le hst)).symm
  rw [intervalIntegral.integral_congr_ae hcongr]
  exact gradDuhamel_sup_bound ht htT hq_int_diff hD hq_diff x hg_int

end ShenWork.IntervalGradDuhamelBound
