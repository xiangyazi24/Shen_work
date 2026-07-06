import ShenWork.Paper2.IntervalChiNegH1PhysicalReactionBound
import ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine

/-!
# Source chemotaxis factor bounds for the physical H¹ sqrt route

This file isolates the fixed-before-`T` chemotaxis-side factor estimates left
after the logistic reaction estimate has been discharged.  It intentionally
does not derive uniform constants from per-time classical resolver bounds.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1LiftDeriv2Transfer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalScalarContinuity
open ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
open ShenWork.Paper2.IntervalChiNegH1PhysicalReactionBound

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds

/-- Source-side fixed-before-`T` bounds for the two physical chemotaxis factors
that remain in the H¹ sqrt estimate. -/
structure H1PhysicalChemFactorBoundsBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M : ℝ) : Prop where
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  taxis_factor_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |H1PhysicalChemTaxisPart p u v τ x| ≤
        V₁ * |deriv (intervalDomainLift (u τ)) x|
  uvxx_factor_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |H1PhysicalChemUvxxPart p u v τ x| ≤ M * V₂

/-- A lower-level source residual phrased in terms of fixed-before-`T`
resolver and physical core bounds.  Producing these constants is the genuine
uniform analytic input; this file only lowers them to the physical factors. -/
structure H1PhysicalChemResolverSupBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M : ℝ) : Prop where
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  u_abs_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift (u τ) x| ≤ M
  resolver_grad_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |resolverGradReal p (u τ) x| ≤ V₁
  uvxx_core_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |(p.μ * intervalDomainLift (v τ) x -
          p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
          (1 + intervalDomainLift (v τ) x) ^ p.β -
        p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
          (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)| ≤ V₂

private theorem H1PhysicalChemTaxisPart_le_of_resolverGrad
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T V₁ τ x : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hV1 : 0 ≤ V₁)
    (hgrad : |resolverGradReal p (u τ) x| ≤ V₁) :
    |H1PhysicalChemTaxisPart p u v τ x| ≤
      V₁ * |deriv (intervalDomainLift (u τ)) x| := by
  set ux : ℝ := deriv (intervalDomainLift (u τ)) x with hux
  set vx : ℝ := deriv (intervalDomainLift (v τ)) x with hvx
  set den : ℝ := (1 + intervalDomainLift (v τ) x) ^ p.β with hden_def
  have hv_eq : vx = resolverGradReal p (u τ) x := by
    rw [hvx]
    exact solution_lift_v_deriv_eq_resolverGrad_Icc hsol hτ hx
  have hv_bound : |vx| ≤ V₁ := by
    simpa [hv_eq] using hgrad
  have hvnn : 0 ≤ intervalDomainLift (v τ) x :=
    solution_lift_v_nonneg_Icc hsol hτ x hx
  have hbase : 1 ≤ 1 + intervalDomainLift (v τ) x := by linarith
  have hden_ge : 1 ≤ den := by
    rw [hden_def]
    exact Real.one_le_rpow hbase p.hβ
  have hden_pos : 0 < den := lt_of_lt_of_le zero_lt_one hden_ge
  have hnum : |ux * vx| ≤ |ux| * V₁ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hv_bound (abs_nonneg ux)
  calc
    |H1PhysicalChemTaxisPart p u v τ x|
        = |ux * vx / den| := by
            simp [H1PhysicalChemTaxisPart, ux, vx, den]
    _ = |ux * vx| / den := by
        rw [abs_div, abs_of_pos hden_pos]
    _ ≤ (|ux| * V₁) / den :=
        div_le_div_of_nonneg_right hnum hden_pos.le
    _ ≤ |ux| * V₁ := by
        have hcoef_nonneg : 0 ≤ |ux| * V₁ :=
          mul_nonneg (abs_nonneg ux) hV1
        have hone_pos : (0 : ℝ) < 1 := zero_lt_one
        simpa using
          div_le_div_of_nonneg_left hcoef_nonneg hone_pos hden_ge
    _ = V₁ * |deriv (intervalDomainLift (u τ)) x| := by
        rw [hux]
        ring

private theorem H1PhysicalChemUvxxPart_le_of_core
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {V₂ M τ x : ℝ}
    (hM : 0 ≤ M)
    (hu : |intervalDomainLift (u τ) x| ≤ M)
    (hcore :
      |(p.μ * intervalDomainLift (v τ) x -
          p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
          (1 + intervalDomainLift (v τ) x) ^ p.β -
        p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
          (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)| ≤ V₂) :
    |H1PhysicalChemUvxxPart p u v τ x| ≤ M * V₂ := by
  set U : ℝ := intervalDomainLift (u τ) x with hU
  set core : ℝ :=
    (p.μ * intervalDomainLift (v τ) x -
        p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
        (1 + intervalDomainLift (v τ) x) ^ p.β -
      p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
        (1 + intervalDomainLift (v τ) x) ^ (p.β + 1) with hcore_def
  have hcore_bound : |core| ≤ V₂ := by
    simpa [core, hcore_def] using hcore
  have hpart_eq : H1PhysicalChemUvxxPart p u v τ x = U * core := by
    simp [H1PhysicalChemUvxxPart, U, core]
    ring_nf
  calc
    |H1PhysicalChemUvxxPart p u v τ x|
        = |U * core| := by rw [hpart_eq]
    _ = |U| * |core| := abs_mul _ _
    _ ≤ M * V₂ :=
        mul_le_mul hu hcore_bound (abs_nonneg core) hM

/-- Fixed-before-`T` resolver/core sup data lower to the source-side physical
chemotaxis factor bounds. -/
theorem H1PhysicalChemFactorBoundsBefore_of_resolverSup
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T V₁ V₂ M : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (h : H1PhysicalChemResolverSupBefore p u v T V₁ V₂ M) :
    H1PhysicalChemFactorBoundsBefore p u v T V₁ V₂ M := by
  refine
    { hV1 := h.hV1
      hV2 := h.hV2
      hM := h.hM
      taxis_factor_le := ?_
      uvxx_factor_le := ?_ }
  · intro τ hτ x hx
    exact
      H1PhysicalChemTaxisPart_le_of_resolverGrad
        (p := p) (u := u) (v := v) (T := T)
        (V₁ := V₁) (τ := τ) (x := x)
        hsol hτ hx h.hV1 (h.resolver_grad_le τ hτ x hx)
  · intro τ hτ x hx
    exact
      H1PhysicalChemUvxxPart_le_of_core
        (p := p) (u := u) (v := v)
        (V₂ := V₂) (M := M) (τ := τ) (x := x)
        h.hM (h.u_abs_le τ hτ x hx)
        (h.uvxx_core_le τ hτ x hx)

private theorem continuousOn_slice_of_uncurry
    {F : ℝ → ℝ → ℝ} {r : ℝ} {s : Set ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc r r ×ˢ s)) :
    ContinuousOn (F r) s := by
  have hpair : ContinuousOn (fun x : ℝ => ((r, x) : ℝ × ℝ)) s :=
    continuousOn_const.prodMk continuousOn_id
  have hmaps :
      Set.MapsTo (fun x : ℝ => ((r, x) : ℝ × ℝ)) s
        (Set.Icc r r ×ˢ s) := by
    intro x hx
    exact ⟨⟨le_rfl, le_rfl⟩, hx⟩
  simpa [Function.uncurry] using hF.comp hpair hmaps

private theorem ae_uIoc_zero_one_mem_Ioo :
    ∀ᵐ x : ℝ ∂volume,
      x ∈ Set.uIoc (0 : ℝ) 1 → x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  filter_upwards [hne1] with x hx_ne1 hxmem
  rw [Set.uIoc_of_le zero_le_one] at hxmem
  exact ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx_ne1⟩

private theorem square_intervalIntegrable_of_uncurry_continuousOn_slice
    {part : ℝ → ℝ → ℝ} {r : ℝ}
    (hCont :
      ContinuousOn (Function.uncurry part)
        (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun x => (part r x) ^ 2) volume (0 : ℝ) 1 := by
  exact ContinuousOn.intervalIntegrable_of_Icc
    (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((continuousOn_slice_of_uncurry
      (F := part) (r := r) (s := Set.Icc (0 : ℝ) 1) hCont).pow 2)

private theorem liftDeriv2_sq_intervalIntegrable_of_rep_cont
    {u : ℝ → intervalDomainPoint → ℝ}
    {F : ℝ → ℝ → ℝ} {r : ℝ}
    (hCont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Ioo (0 : ℝ) 1)) :
    IntervalIntegrable (fun x => (liftDeriv2 u r x) ^ 2)
      volume (0 : ℝ) 1 := by
  have hSlice :
      ContinuousOn (fun x => (F r x) ^ 2) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_slice_of_uncurry
      (F := F) (r := r) (s := Set.Icc (0 : ℝ) 1) hCont).pow 2
  have hRepInt :
      IntervalIntegrable (fun x => (F r x) ^ 2) volume (0 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc
      (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hSlice
  refine hRepInt.congr_ae ?_
  rw [Set.uIoc_of_le zero_le_one]
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_uIoc_zero_one_mem_Ioo] with x hxIoo hxIoc
  have hx : x ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le zero_le_one] using hxIoo (by
      simpa [Set.uIoc_of_le zero_le_one] using hxIoc)
  have hEq := hEqInterior (x := (r, x))
    (Set.mem_prod.mpr ⟨⟨le_rfl, le_rfl⟩, hx⟩)
  simp only [Function.uncurry_apply_pair] at hEq
  rw [← hEq]

private theorem abs_liftDeriv2_mul_part_intervalIntegrable_of_rep_product_cont
    {u : ℝ → intervalDomainPoint → ℝ}
    {F part : ℝ → ℝ → ℝ} {r : ℝ}
    (hCont :
      ContinuousOn (Function.uncurry (fun t x => F t x * part t x))
        (Set.Icc r r ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior :
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc r r ×ˢ Set.Ioo (0 : ℝ) 1)) :
    IntervalIntegrable (fun x => |liftDeriv2 u r x * part r x|)
      volume (0 : ℝ) 1 := by
  have hSlice :
      ContinuousOn (fun x => |F r x * part r x|) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_slice_of_uncurry
      (F := fun t x => F t x * part t x)
      (r := r) (s := Set.Icc (0 : ℝ) 1) hCont).abs
  have hRepInt :
      IntervalIntegrable (fun x => |F r x * part r x|) volume (0 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc
      (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hSlice
  refine hRepInt.congr_ae ?_
  rw [Set.uIoc_of_le zero_le_one]
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_uIoc_zero_one_mem_Ioo] with x hxIoo hxIoc
  have hx : x ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le zero_le_one] using hxIoo (by
      simpa [Set.uIoc_of_le zero_le_one] using hxIoc)
  have hEq := hEqInterior (x := (r, x))
    (Set.mem_prod.mpr ⟨⟨le_rfl, le_rfl⟩, hx⟩)
  simp only [Function.uncurry_apply_pair] at hEq
  simp [hEq]

private theorem grad_sq_intervalIntegrable_of_classicalSolution
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    IntervalIntegrable
      (fun x => (deriv (intervalDomainLift (u τ)) x) ^ 2)
      volume (0 : ℝ) 1 := by
  exact
    ((solution_deriv_lift_continuousOn_Icc hsol hτ).pow 2).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)

private theorem H1PhysicalChemTaxisPart_l2_bound_of_factorBound
    {p : CM2Params} {V₁ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hgrad_sq :
      IntervalIntegrable
        (fun x => (deriv (intervalDomainLift (u τ)) x) ^ 2)
        volume (0 : ℝ) 1)
    (hpart_sq :
      IntervalIntegrable
        (fun x => (H1PhysicalChemTaxisPart p u v τ x) ^ 2)
        volume (0 : ℝ) 1)
    (hV1 : 0 ≤ V₁)
    (hfactor : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |H1PhysicalChemTaxisPart p u v τ x| ≤
        V₁ * |deriv (intervalDomainLift (u τ)) x|) :
    Real.sqrt
        (∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2)
      ≤ V₁ * H1gradL2Norm u τ := by
  have hright_int :
      IntervalIntegrable
        (fun x => V₁ ^ 2 * (deriv (intervalDomainLift (u τ)) x) ^ 2)
        volume (0 : ℝ) 1 :=
    hgrad_sq.const_mul (V₁ ^ 2)
  have hmono :
      (∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2) ≤
        ∫ x in (0 : ℝ)..1,
          V₁ ^ 2 * (deriv (intervalDomainLift (u τ)) x) ^ 2 := by
    refine intervalIntegral.integral_mono_on
      (by norm_num : (0 : ℝ) ≤ 1) hpart_sq hright_int ?_
    intro x hx
    have hfac := hfactor x hx
    have hright_nonneg :
        0 ≤ V₁ * |deriv (intervalDomainLift (u τ)) x| :=
      mul_nonneg hV1 (abs_nonneg _)
    calc
      (H1PhysicalChemTaxisPart p u v τ x) ^ 2
          = |H1PhysicalChemTaxisPart p u v τ x| ^ 2 := by
              rw [sq_abs]
      _ ≤ (V₁ * |deriv (intervalDomainLift (u τ)) x|) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) hright_nonneg).2 hfac
      _ = V₁ ^ 2 * (deriv (intervalDomainLift (u τ)) x) ^ 2 := by
          rw [mul_pow, sq_abs]
  have hright_eval :
      (∫ x in (0 : ℝ)..1,
          V₁ ^ 2 * (deriv (intervalDomainLift (u τ)) x) ^ 2) =
        V₁ ^ 2 * (H1gradL2Norm u τ) ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    rw [H1grad_sq_integral_eq_H1gradL2Norm_sq]
  have hsqrt :
      Real.sqrt
          (∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2)
        ≤ Real.sqrt (V₁ ^ 2 * (H1gradL2Norm u τ) ^ 2) := by
    exact Real.sqrt_le_sqrt (by simpa [hright_eval] using hmono)
  have hprod_nonneg : 0 ≤ V₁ * H1gradL2Norm u τ :=
    mul_nonneg hV1 (H1gradL2Norm_nonneg u τ)
  have hsq : V₁ ^ 2 * (H1gradL2Norm u τ) ^ 2 =
      (V₁ * H1gradL2Norm u τ) ^ 2 := by ring
  calc
    Real.sqrt
        (∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2)
        ≤ Real.sqrt (V₁ ^ 2 * (H1gradL2Norm u τ) ^ 2) := hsqrt
    _ = V₁ * H1gradL2Norm u τ := by
        rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hprod_nonneg]

private theorem H1PhysicalChemUvxxPart_l2_bound_of_factorBound
    {p : CM2Params} {M V₂ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {τ : ℝ}
    (hpart_sq :
      IntervalIntegrable
        (fun x => (H1PhysicalChemUvxxPart p u v τ x) ^ 2)
        volume (0 : ℝ) 1)
    (hM : 0 ≤ M) (hV2 : 0 ≤ V₂)
    (hfactor : ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |H1PhysicalChemUvxxPart p u v τ x| ≤ M * V₂) :
    Real.sqrt
        (∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2)
      ≤ M * V₂ := by
  have hcoef_nonneg : 0 ≤ M * V₂ := mul_nonneg hM hV2
  have hright_int :
      IntervalIntegrable (fun _x : ℝ => (M * V₂) ^ 2) volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hmono :
      (∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2) ≤
        ∫ _x in (0 : ℝ)..1, (M * V₂) ^ 2 := by
    refine intervalIntegral.integral_mono_on
      (by norm_num : (0 : ℝ) ≤ 1) hpart_sq hright_int ?_
    intro x hx
    have hfac := hfactor x hx
    calc
      (H1PhysicalChemUvxxPart p u v τ x) ^ 2
          = |H1PhysicalChemUvxxPart p u v τ x| ^ 2 := by
              rw [sq_abs]
      _ ≤ (M * V₂) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) hcoef_nonneg).2 hfac
  have hright_eval :
      (∫ _x in (0 : ℝ)..1, (M * V₂) ^ 2) = (M * V₂) ^ 2 := by
    rw [intervalIntegral.integral_const]
    norm_num
  have hsqrt :
      Real.sqrt
          (∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2)
        ≤ Real.sqrt ((M * V₂) ^ 2) := by
    exact Real.sqrt_le_sqrt (by simpa [hright_eval] using hmono)
  calc
    Real.sqrt
        (∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2)
        ≤ Real.sqrt ((M * V₂) ^ 2) := hsqrt
    _ = M * V₂ := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hcoef_nonneg]

/-- Classical fixed-time regularity plus source-side chem factor bounds produce
the chemotaxis-side L² sqrt data package.  This is still a source-side theorem:
the fixed-before-`T` constants are supplied by `hchem`, not derived from
per-time classical bounds. -/
theorem H1PhysicalChemL2SqrtBoundDataBefore_of_classical_factorBounds
    {p : CM2Params} {T V₁ V₂ M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hchem : H1PhysicalChemFactorBoundsBefore p u v T V₁ V₂ M) :
    H1PhysicalChemL2SqrtBoundDataBefore p u v T V₁ V₂ M := by
  have hRep :=
    H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol
  refine
    { hchi := hchi
      hV1 := hchem.hV1
      hV2 := hchem.hV2
      hM := hchem.hM
      lap_sq_int := ?_
      taxis_sq_int := ?_
      uvxx_sq_int := ?_
      taxis_prod_int := ?_
      uvxx_prod_int := ?_
      taxis_l2_bound := ?_
      uvxx_l2_bound := ?_ }
  · intro τ hτ
    exact
      liftDeriv2_sq_intervalIntegrable_of_rep_cont
        (u := u)
        (F := liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v))
        (r := τ)
        (hRep.uxx_cont (a := τ) (b := τ) hτ.1 le_rfl hτ.2)
        (hRep.uxx_eqInterior (a := τ) (b := τ) hτ.1 le_rfl hτ.2)
  · intro τ hτ
    exact
      square_intervalIntegrable_of_uncurry_continuousOn_slice
        (part := H1PhysicalChemTaxisPart p u v)
        (r := τ)
        (H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
          (p := p) (T := T) (u := u) (v := v)
          hsol hτ.1 le_rfl hτ.2)
  · intro τ hτ
    exact
      square_intervalIntegrable_of_uncurry_continuousOn_slice
        (part := H1PhysicalChemUvxxPart p u v)
        (r := τ)
        (H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
          (p := p) (T := T) (u := u) (v := v)
          hsol hτ.1 le_rfl hτ.2)
  · intro τ hτ
    have hCont :
        ContinuousOn
          (Function.uncurry
            (fun t x =>
              liftDeriv2PhysicalRHSWithChemRep p u
                (liftChemotaxisDivPhysicalRep p u v) t x *
              H1PhysicalChemTaxisPart p u v t x))
          (Set.Icc τ τ ×ˢ Set.Icc (0 : ℝ) 1) := by
      simpa [H1PhysicalTaxisRepIntegrand] using
        hRep.taxis_cont (a := τ) (b := τ) hτ.1 le_rfl hτ.2
    exact
      abs_liftDeriv2_mul_part_intervalIntegrable_of_rep_product_cont
        (u := u)
        (F := liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v))
        (part := H1PhysicalChemTaxisPart p u v)
        (r := τ)
        hCont
        (hRep.uxx_eqInterior (a := τ) (b := τ) hτ.1 le_rfl hτ.2)
  · intro τ hτ
    have hCont :
        ContinuousOn
          (Function.uncurry
            (fun t x =>
              liftDeriv2PhysicalRHSWithChemRep p u
                (liftChemotaxisDivPhysicalRep p u v) t x *
              H1PhysicalChemUvxxPart p u v t x))
          (Set.Icc τ τ ×ˢ Set.Icc (0 : ℝ) 1) := by
      simpa [H1PhysicalUvxxRepIntegrand] using
        hRep.uvxx_cont (a := τ) (b := τ) hτ.1 le_rfl hτ.2
    exact
      abs_liftDeriv2_mul_part_intervalIntegrable_of_rep_product_cont
        (u := u)
        (F := liftDeriv2PhysicalRHSWithChemRep p u
          (liftChemotaxisDivPhysicalRep p u v))
        (part := H1PhysicalChemUvxxPart p u v)
        (r := τ)
        hCont
        (hRep.uxx_eqInterior (a := τ) (b := τ) hτ.1 le_rfl hτ.2)
  · intro τ hτ
    exact
      H1PhysicalChemTaxisPart_l2_bound_of_factorBound
        (p := p) (V₁ := V₁) (u := u) (v := v)
        (τ := τ)
        (grad_sq_intervalIntegrable_of_classicalSolution
          (p := p) (T := T) (τ := τ) (u := u) (v := v) hsol hτ)
        (square_intervalIntegrable_of_uncurry_continuousOn_slice
          (part := H1PhysicalChemTaxisPart p u v)
          (r := τ)
          (H1PhysicalChemTaxisPart_continuousOn_strictSlab_of_classicalSolution
            (p := p) (T := T) (u := u) (v := v)
            hsol hτ.1 le_rfl hτ.2))
        hchem.hV1
        (hchem.taxis_factor_le τ hτ)
  · intro τ hτ
    exact
      H1PhysicalChemUvxxPart_l2_bound_of_factorBound
        (p := p) (M := M) (V₂ := V₂) (u := u) (v := v)
        (τ := τ)
        (square_intervalIntegrable_of_uncurry_continuousOn_slice
          (part := H1PhysicalChemUvxxPart p u v)
          (r := τ)
          (H1PhysicalChemUvxxPart_continuousOn_strictSlab_of_classicalSolution
            (p := p) (T := T) (u := u) (v := v)
            hsol hτ.1 le_rfl hτ.2))
        hchem.hM hchem.hV2
        (hchem.uvxx_factor_le τ hτ)

/-- Classical fixed-time regularity and source-side chem factor bounds, together
with the classical logistic reaction reducer, produce the concrete physical H¹
sqrt-bound frontier. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_classical_factorBounds
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (hchem : H1PhysicalChemFactorBoundsBefore p u v T V₁ V₂ M) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_chemL2SqrtBoundData_and_classical_reaction
    hsol hL
    (H1PhysicalChemL2SqrtBoundDataBefore_of_classical_factorBounds
      (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M)
      (u := u) (v := v) hsol hchi hchem)

/-- Resolver/core fixed-before-`T` source bounds produce the chemotaxis-side
L² sqrt data package under classical fixed-time regularity. -/
theorem H1PhysicalChemL2SqrtBoundDataBefore_of_classical_resolverSup
    {p : CM2Params} {T V₁ V₂ M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hres : H1PhysicalChemResolverSupBefore p u v T V₁ V₂ M) :
    H1PhysicalChemL2SqrtBoundDataBefore p u v T V₁ V₂ M :=
  H1PhysicalChemL2SqrtBoundDataBefore_of_classical_factorBounds
    (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M)
    (u := u) (v := v) hsol hchi
    (H1PhysicalChemFactorBoundsBefore_of_resolverSup
      (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M)
      (u := u) (v := v) hsol hres)

/-- Resolver/core fixed-before-`T` source bounds, plus the classical logistic
reaction reducer, produce the concrete physical H¹ sqrt-bound frontier. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_classical_resolverSup
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (hres : H1PhysicalChemResolverSupBefore p u v T V₁ V₂ M) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_classical_factorBounds
    (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M) (L := L)
    (u := u) (v := v) hsol hchi hL
    (H1PhysicalChemFactorBoundsBefore_of_resolverSup
      (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M)
      (u := u) (v := v) hsol hres)

#print axioms H1PhysicalChemTaxisPart_le_of_resolverGrad
#print axioms H1PhysicalChemUvxxPart_le_of_core
#print axioms H1PhysicalChemFactorBoundsBefore_of_resolverSup
#print axioms H1PhysicalChemL2SqrtBoundDataBefore_of_classical_factorBounds
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_classical_factorBounds
#print axioms H1PhysicalChemL2SqrtBoundDataBefore_of_classical_resolverSup
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_classical_resolverSup

end ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
