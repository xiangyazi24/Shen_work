/-
  ShenWork/PDE/IntervalChemDivFluxHDgWiring.lean

  BRIDGE — wire the residual gradient-Lipschitz `hDg_le : D_g ≤ L_u · D` for the
  divergence-form gradient-Duhamel trajectory, from the COMMITTED t^{-1/2}
  heat-gradient bound (via `gradDuhamel_diff_sup_bound`) + the source Lipschitz.

  `chemDivFlux_physical_KD_collapse` (IntervalChemDivFluxC1PhysicalBridge.lean)
  consumes a single residual analytic input
      `hDg_le : D_g ≤ L_u · D`,
  the parabolic Lipschitz of the trajectory's spatial gradient in `u`.  For the
  divergence-form gradient-Duhamel map
      G(q)(t,x) = ∫₀ᵗ ∂ₓ S(t−s) q(s) (x) ds,
  the committed Atom-D bound `gradDuhamel_diff_sup_bound` gives
      |G(q₁) − G(q₂)|(t,x) ≤ Cgrad · 2√T · D'      when |q₁ − q₂| ≤ D'.
  Feeding the SOURCE Lipschitz `|q₁ − q₂| ≤ source_Lip · D` (with `q = source`
  the lifted coupled source, whose difference is `source_Lip · D`-bounded by the
  committed `intervalCoupledSource_lift_diff_bound`) collapses this to
      D_g ≤ (Cgrad · 2√T · source_Lip) · D = L_u · D,
  i.e. `hDg_le` with the EXPLICIT `L_u := Cgrad · 2√T · source_Lip`.

  This file proves that wiring as a standalone lemma `gradDuhamel_hDg_le`,
  supplying `L_u` and discharging it from the committed t^{-1/2} gradient (no new
  Mathlib gap, no `sorry`).  The honest residual it leaves explicit is the
  value-vs-divergence reconciliation of the trajectory's own gradient (the lift
  derivative `deriv (intervalDomainLift (u_i τ))`) with the divergence-form
  gradient-Duhamel `D_g`; that identification is the parabolic regularity bridge
  recorded by `intervalCoupledDuhamel_grad_estimate_gap`, not part of this file.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.PDE.IntervalCoupledClassicalBallEstimates

open MeasureTheory intervalIntegral
open ShenWork.IntervalDomain (intervalMeasure intervalSemigroupOperator)
open ShenWork.IntervalCoupledClassicalBallEstimates
  (intervalCoupledDuhamel_grad_integral_bound_no_int
   intervalCoupledDuhamel_grad_integral_hasDerivAt
   intervalSemigroupOperator_s_dependent_aestronglyMeasurable_x
   intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
   intervalCoupledDuhamel_grad_envelope_intervalIntegrable)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.IntervalChemDivFluxHDgWiring

/-- The explicit residual Lipschitz constant
`L_u = Cgrad · 2√T · source_Lip` for the divergence-form gradient-Duhamel
trajectory, where `Cgrad = heatGradientLinftyLinftyConstant = 1/√π`. -/
def gradDuhamelLuConstant (T source_Lip : ℝ) : ℝ :=
  heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * source_Lip

theorem gradDuhamelLuConstant_nonneg {T source_Lip : ℝ}
    (hsLnn : 0 ≤ source_Lip) : 0 ≤ gradDuhamelLuConstant T source_Lip := by
  unfold gradDuhamelLuConstant
  have hsqT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hCg : 0 ≤ heatGradientLinftyLinftyConstant :=
    heatGradientLinftyLinftyConstant_nonneg
  positivity

/-- **BRIDGE — `hDg_le` for the divergence-form gradient-Duhamel trajectory.**

Let `q₁, q₂ : ℝ → ℝ → ℝ` be two lifted source fields with `|q₁ s y − q₂ s y| ≤
source_Lip · D` (the SOURCE Lipschitz in the trajectory separation `D`).  Then
the divergence-form gradient-Duhamel difference
`G(q₁) − G(q₂)` obeys, at every `x`,
    |G(q₁)(t,x) − G(q₂)(t,x)| ≤ L_u · D
with the EXPLICIT `L_u = Cgrad · 2√T · source_Lip`.

This is exactly the `D_g ≤ L_u · D` shape that
`chemDivFlux_physical_KD_collapse` consumes, with `D_g` the divergence-form
gradient-Duhamel difference and `L_u` produced from the committed
`gradDuhamel_diff_sup_bound` (whose only analytic content is the committed
`intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t` t^{-1/2}
gradient + `∫₀ᵗ (t−s)^{-1/2} ds = 2√t`).  The per-slice differentiability
(`hd₁/hd₂`), kernel integrability (`hKq₁/hKq₂`), and the integrand
interval-integrability (`hg_int`) are the honest regularity inputs of the
linearity split — discharged from joint continuity downstream. -/
theorem gradDuhamel_hDg_le
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {q₁ q₂ : ℝ → ℝ → ℝ}
    {D source_Lip : ℝ} (hD : 0 ≤ D) (hsLnn : 0 ≤ source_Lip)
    (hq_diff : ∀ s y, |q₁ s y - q₂ s y| ≤ source_Lip * D)
    (hq_int_diff : ∀ s,
      Integrable (fun y => q₁ s y - q₂ s y) (intervalMeasure 1))
    (x : ℝ)
    (hKq₁ : ∀ s z, Integrable
      (fun y => intervalNeumannFullKernel (t - s) z y * q₁ s y) (intervalMeasure 1))
    (hKq₂ : ∀ s z, Integrable
      (fun y => intervalNeumannFullKernel (t - s) z y * q₂ s y) (intervalMeasure 1))
    (hd₁ : ∀ s, 0 ≤ s → s < t →
      DifferentiableAt ℝ
        (fun z => intervalFullSemigroupOperator (t - s) (q₁ s) z) x)
    (hd₂ : ∀ s, 0 ≤ s → s < t →
      DifferentiableAt ℝ
        (fun z => intervalFullSemigroupOperator (t - s) (q₂ s) z) x)
    (hg_int : IntervalIntegrable
      (fun s : ℝ => deriv
        (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s) (fun y => q₁ s y - q₂ s y) z) x)
      volume 0 t) :
    |∫ s in (0:ℝ)..t,
        (deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q₁ s) z) x
          - deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q₂ s) z) x)|
      ≤ gradDuhamelLuConstant T source_Lip * D := by
  have hsLD : 0 ≤ source_Lip * D := mul_nonneg hsLnn hD
  -- The committed Atom-D difference bound, with separation `D' = source_Lip · D`.
  have hbase := ShenWork.IntervalGradDuhamelBound.gradDuhamel_diff_sup_bound
    (t := t) (T := T) ht htT (q₁ := q₁) (q₂ := q₂)
    (D := source_Lip * D) hsLD hq_diff hq_int_diff x hKq₁ hKq₂ hd₁ hd₂ hg_int
  -- Re-associate `Cgrad · 2√T · (source_Lip · D) = L_u · D`.
  have hassoc :
      heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * (source_Lip * D)
        = gradDuhamelLuConstant T source_Lip * D := by
    unfold gradDuhamelLuConstant; ring
  rw [hassoc] at hbase
  exact hbase

/-! ### Value-form helper-semigroup `hDg_le` (the residual's actual shape)

The residual `chemDivFlux_physical_KD_collapse` consumes `hDg_le` for
`D_g = sup|deriv (intervalDomainLift (u₁ τ)) − deriv (intervalDomainLift
(u₂ τ))|` where `u_i` are the *trajectories*.  On the interior,
`intervalCoupledDuhamel_lift_deriv_eq_explicit_interior` rewrites each
trajectory lift-derivative to the VALUE-form helper-semigroup gradient
`deriv (S(τ) u₀ + ∫₀^τ S(τ−s) source_i)`.  The initial-data term `S(τ) u₀`
is identical for both trajectories (same `u₀`), so it cancels in the
difference, leaving the source-integral gradient difference — bounded by the
committed value-form bound `intervalCoupledDuhamel_grad_integral_bound_no_int`
applied to the lifted SOURCE DIFFERENCE field.

The lemma below produces the value-form difference bound on the source-integral
gradient directly, in the helper semigroup that the trajectory lift uses. -/

/-- **BRIDGE (value form) — source-integral gradient difference bound in the
helper semigroup.**

For two lifted source fields `F₁, F₂` with separation `|F₁ s y − F₂ s y| ≤
source_Lip · D`, the difference of their value-form helper-semigroup
source-integral gradients at `x₀` is bounded by `L_u · D`, with the explicit
`L_u = Cgrad · 2√T · source_Lip`.  This is the value-form (`∂ₓ` OUTSIDE the
helper semigroup, via the committed Leibniz interchange) companion of
`gradDuhamel_hDg_le`, matching the helper operator `intervalSemigroupOperator`
used by `intervalCoupledDuhamelOperator`. -/
theorem grad_integral_hDg_le_value
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {F₁ F₂ : ℝ → ℝ → ℝ}
    {D source_Lip : ℝ} (hD : 0 ≤ D) (hsLnn : 0 ≤ source_Lip)
    (hF_ae : AEStronglyMeasurable
      (Function.uncurry (fun s y => F₁ s y - F₂ s y))
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (hF₁_int : ∀ s, Integrable (F₁ s) (intervalMeasure 1))
    (hF₂_int : ∀ s, Integrable (F₂ s) (intervalMeasure 1))
    (hF_diff_sup : ∀ s, ∀ y : ℝ, |F₁ s y - F₂ s y| ≤ source_Lip * D)
    (x₀ : ℝ)
    -- The two value-Duhamel integrals' `HasDerivAt`s (from the committed
    -- helper-form Leibniz lemma `intervalCoupledDuhamel_grad_integral_hasDerivAt`),
    -- packaged as the per-trajectory differentiability of the source integral.
    (hHasDeriv₁ : HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₁ s) x)
      (deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₁ s) x) x₀) x₀)
    (hHasDeriv₂ : HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₂ s) x)
      (deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₂ s) x) x₀) x₀)
    -- Per-`x` interval-integrability of each value integrand (the honest
    -- regularity input of the slicewise linearity split; discharged from the
    -- per-slice helper-semigroup sup bound downstream).
    (hII₁ : ∀ x : ℝ, IntervalIntegrable
      (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F₁ s) x) volume 0 t)
    (hII₂ : ∀ x : ℝ, IntervalIntegrable
      (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F₂ s) x) volume 0 t) :
    |deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₁ s) x) x₀
      - deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₂ s) x) x₀|
      ≤ gradDuhamelLuConstant T source_Lip * D := by
  set G : ℝ → ℝ → ℝ := fun s y => F₁ s y - F₂ s y with hG
  have hsLD : 0 ≤ source_Lip * D := mul_nonneg hsLnn hD
  have hG_int : ∀ s, Integrable (G s) (intervalMeasure 1) := fun s =>
    (hF₁_int s).sub (hF₂_int s)
  -- The two value-Duhamel integrals subtract, slicewise, via helper linearity.
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hcongr : (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (G s) x)
      = (fun x : ℝ =>
          (∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₁ s) x)
            - (∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₂ s) x)) := by
    funext x
    rw [← intervalIntegral.integral_sub (hII₁ x) (hII₂ x)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Set.uIoc_of_le ht.le] at hs_mem
    have hst : s < t := lt_of_le_of_ne hs_mem.2 hs_ne
    have htms_pos : 0 < t - s := sub_pos.mpr hst
    exact
      ShenWork.IntervalDomain.intervalSemigroupOperator_sub htms_pos
        (hF₁_int s) (hF₂_int s) x
  -- The combined `G`-integral has `HasDerivAt` = difference of the two derivs.
  have hHasDerivG :
      HasDerivAt (fun x : ℝ =>
          ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (G s) x)
        (deriv (fun x : ℝ =>
            ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₁ s) x) x₀
          - deriv (fun x : ℝ =>
            ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₂ s) x) x₀)
        x₀ := by
    rw [hcongr]; exact hHasDeriv₁.sub hHasDeriv₂
  have hderiv_eq :
      deriv (fun x : ℝ =>
          ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₁ s) x) x₀
        - deriv (fun x : ℝ =>
          ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₂ s) x) x₀
      = deriv (fun x : ℝ =>
          ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (G s) x) x₀ :=
    hHasDerivG.deriv.symm
  rw [hderiv_eq]
  have hbound := intervalCoupledDuhamel_grad_integral_bound_no_int
    (t := t) (T := T) ht htT (F := G) hF_ae hG_int
    (C_source := source_Lip * D) hsLD hF_diff_sup x₀
  have hassoc :
      heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * (source_Lip * D)
        = gradDuhamelLuConstant T source_Lip * D := by
    unfold gradDuhamelLuConstant; ring
  rw [hassoc] at hbound
  exact hbound

/-- **BRIDGE (value form, self-contained) — `hDg_le` from joint measurability.**

The `_clean` capstone of `grad_integral_hDg_le_value`: the per-trajectory
`HasDerivAt`s (`hHasDeriv₁/₂`) and the value-integrand interval-integrabilities
(`hII₁/₂`) are now produced internally from the natural source data —
per-trajectory joint a.e.-measurability, per-slice `intervalMeasure`
integrability, and a uniform pointwise sup bound on each trajectory's source —
via the committed helper-form Leibniz lemma
`intervalCoupledDuhamel_grad_integral_hasDerivAt` and the
`intervalSemigroupOperator_Linfty_bound` domination.

`C_each` is the per-trajectory source sup (used only to discharge the Leibniz
HasDerivAt internally); the conclusion is the residual `hDg_le` shape with the
explicit `L_u = Cgrad · 2√T · source_Lip`. -/
theorem grad_integral_hDg_le_value_clean
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {F₁ F₂ : ℝ → ℝ → ℝ}
    {D source_Lip C_each : ℝ}
    (hD : 0 ≤ D) (hsLnn : 0 ≤ source_Lip) (hC_each_nn : 0 ≤ C_each)
    (hF₁_ae : AEStronglyMeasurable (Function.uncurry F₁)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (hF₂_ae : AEStronglyMeasurable (Function.uncurry F₂)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (hFdiff_ae : AEStronglyMeasurable
      (Function.uncurry (fun s y => F₁ s y - F₂ s y))
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)))
    (hF₁_int : ∀ s, Integrable (F₁ s) (intervalMeasure 1))
    (hF₂_int : ∀ s, Integrable (F₂ s) (intervalMeasure 1))
    (hF₁_sup : ∀ s, ∀ y : ℝ, |F₁ s y| ≤ C_each)
    (hF₂_sup : ∀ s, ∀ y : ℝ, |F₂ s y| ≤ C_each)
    (hF_diff_sup : ∀ s, ∀ y : ℝ, |F₁ s y - F₂ s y| ≤ source_Lip * D)
    (x₀ : ℝ) :
    |deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₁ s) x) x₀
      - deriv (fun x : ℝ =>
        ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F₂ s) x) x₀|
      ≤ gradDuhamelLuConstant T source_Lip * D := by
  -- Internal helper: from `(hF_ae, hF_int, hF_sup)` build the Leibniz HasDerivAt
  -- and the value-integrand interval-integrability for one trajectory.
  have hbuild : ∀ (F : ℝ → ℝ → ℝ),
      AEStronglyMeasurable (Function.uncurry F)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) →
      (∀ s, Integrable (F s) (intervalMeasure 1)) →
      (∀ s, ∀ y : ℝ, |F s y| ≤ C_each) →
      HasDerivAt
        (fun x : ℝ => ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F s) x)
        (deriv (fun x : ℝ =>
          ∫ s in (0 : ℝ)..t, intervalSemigroupOperator 1 (t - s) (F s) x) x₀) x₀
      ∧ (∀ x : ℝ, IntervalIntegrable
          (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F s) x) volume 0 t) := by
    intro F hF_ae hF_int hF_sup
    have hF_meas : ∀ x : ℝ,
        AEStronglyMeasurable
          (fun s : ℝ => intervalSemigroupOperator 1 (t - s) (F s) x)
          (volume.restrict (Set.uIoc (0 : ℝ) t)) := fun x =>
      intervalSemigroupOperator_s_dependent_aestronglyMeasurable_x ht hF_ae x
    have hF'_meas :
        AEStronglyMeasurable
          (fun s : ℝ => deriv (fun z : ℝ =>
            intervalSemigroupOperator 1 (t - s) (F s) z) x₀)
          (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
      intervalSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
        ht hF_ae hF_int x₀
    have hDom_int :
        IntervalIntegrable
          (fun s : ℝ => heatGradientLinftyLinftyConstant
            * C_each * (t - s) ^ (-(1/2 : ℝ))) volume (0 : ℝ) t :=
      intervalCoupledDuhamel_grad_envelope_intervalIntegrable ht C_each
    have hHD := intervalCoupledDuhamel_grad_integral_hasDerivAt
        ht hF_int hC_each_nn hF_sup x₀ hF_meas hF'_meas hDom_int
    refine ⟨hHD.deriv ▸ hHD, ?_⟩
    -- value-integrand interval-integrability, dominated by `C_each`.
    intro x
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    refine IntervalIntegrable.mono_fun'
      (g := fun _ : ℝ => C_each) _root_.intervalIntegrable_const
      (hF_meas x) ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Set.uIoc_of_le ht.le] at hs_mem
    have htms_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
    have h := ShenWork.IntervalDomain.intervalSemigroupOperator_Linfty_bound
      (L := 1) (t := t - s) htms_pos (M := C_each) hC_each_nn (hF_sup s) x
    simpa [Real.norm_eq_abs] using h
  obtain ⟨hHD₁, hII₁⟩ := hbuild F₁ hF₁_ae hF₁_int hF₁_sup
  obtain ⟨hHD₂, hII₂⟩ := hbuild F₂ hF₂_ae hF₂_int hF₂_sup
  exact grad_integral_hDg_le_value ht htT hD hsLnn hFdiff_ae hF₁_int hF₂_int
    hF_diff_sup x₀ hHD₁ hHD₂ hII₁ hII₂

end ShenWork.IntervalChemDivFluxHDgWiring

