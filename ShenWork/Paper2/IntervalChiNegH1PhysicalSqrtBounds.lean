import ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
import ShenWork.PDE.GagliardoNirenberg

/-!
# Source-side reducers for the concrete physical H¹ sqrt bounds

This file keeps the remaining analytic estimates explicit.  It proves that
fixed-time L² controls for the two non-lap physical RHS factors, together with
the reaction scalar estimate, are sufficient to build
`H1PhysicalRHSSqrtBoundsBefore`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalSqrtBounds

/-- The exact pointwise physical estimates needed by
`H1PhysicalRHSSqrtBoundsBefore`. -/
structure H1PhysicalRHSSqrtPointwiseEstimatesBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  hchi : 0 ≤ -p.χ₀
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  hL : 0 ≤ L
  taxis_abs : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    |H1PhysicalTaxisX p u v τ| ≤
      V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ)
  uvxx_abs : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    |H1PhysicalUvxxX p u v τ| ≤ M * (V₂ * H1lapL2Norm u τ)
  react_bound : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    H1PhysicalReactX p u τ ≤ L * (H1gradL2Norm u τ) ^ 2

/-- Fixed-before-`T` L² estimates sufficient for the concrete physical H¹
square-root bounds.

These are source-side estimates for the physical scalar triple.  They are not
zero-window Young majorants and they do not include the downstream H¹ route
packages. -/
structure H1PhysicalRHSL2SqrtBoundDataBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  hchi : 0 ≤ -p.χ₀
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  hL : 0 ≤ L
  lap_sq_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1
  taxis_sq_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => (H1PhysicalChemTaxisPart p u v τ x) ^ 2) volume (0 : ℝ) 1
  uvxx_sq_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => (H1PhysicalChemUvxxPart p u v τ x) ^ 2) volume (0 : ℝ) 1
  taxis_prod_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x|)
      volume (0 : ℝ) 1
  uvxx_prod_int : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x|)
      volume (0 : ℝ) 1
  taxis_l2_bound : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    Real.sqrt
        (∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2)
      ≤ V₁ * H1gradL2Norm u τ
  uvxx_l2_bound : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    Real.sqrt
        (∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2)
      ≤ M * V₂
  react_bound : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    H1PhysicalReactX p u τ ≤ L * (H1gradL2Norm u τ) ^ 2

private theorem H1PhysicalTaxisX_le_of_l2_bound
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {τ V₁ : ℝ}
    (hlap : IntervalIntegrable
      (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1)
    (htaxis : IntervalIntegrable
      (fun x => (H1PhysicalChemTaxisPart p u v τ x) ^ 2) volume (0 : ℝ) 1)
    (hprod : IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x|)
      volume (0 : ℝ) 1)
    (hbound :
      Real.sqrt
          (∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2)
        ≤ V₁ * H1gradL2Norm u τ) :
    H1PhysicalTaxisX p u v τ ≤
      V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ) := by
  have hcs :=
    ShenWork.GagliardoNirenberg.integral_abs_mul_le_sqrt
      (L := (1 : ℝ))
      (f := fun x => liftDeriv2 u τ x)
      (g := fun x => H1PhysicalChemTaxisPart p u v τ x)
      (by norm_num) hlap htaxis hprod
  have habs :
      |∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x| ≤
        ∫ x in (0 : ℝ)..1,
          |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x| :=
    intervalIntegral.abs_integral_le_integral_abs
      (by norm_num : (0 : ℝ) ≤ 1)
  calc
    H1PhysicalTaxisX p u v τ
        = -(∫ x in (0 : ℝ)..1,
            liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x) := rfl
    _ ≤ |∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x| :=
        neg_le_abs _
    _ ≤ ∫ x in (0 : ℝ)..1,
          |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x| :=
        habs
    _ ≤ H1lapL2Norm u τ *
          Real.sqrt
            (∫ x in (0 : ℝ)..1,
              (H1PhysicalChemTaxisPart p u v τ x) ^ 2) := by
        simpa [H1lapL2Norm, lapL2sq] using hcs
    _ ≤ H1lapL2Norm u τ * (V₁ * H1gradL2Norm u τ) :=
        mul_le_mul_of_nonneg_left hbound (H1lapL2Norm_nonneg u τ)
    _ = V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ) := by
        ring

private theorem H1PhysicalUvxxX_le_of_l2_bound
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {τ V₂ M : ℝ}
    (hlap : IntervalIntegrable
      (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1)
    (huvxx : IntervalIntegrable
      (fun x => (H1PhysicalChemUvxxPart p u v τ x) ^ 2) volume (0 : ℝ) 1)
    (hprod : IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x|)
      volume (0 : ℝ) 1)
    (hbound :
      Real.sqrt
          (∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2)
        ≤ M * V₂) :
    H1PhysicalUvxxX p u v τ ≤ M * (V₂ * H1lapL2Norm u τ) := by
  have hcs :=
    ShenWork.GagliardoNirenberg.integral_abs_mul_le_sqrt
      (L := (1 : ℝ))
      (f := fun x => liftDeriv2 u τ x)
      (g := fun x => H1PhysicalChemUvxxPart p u v τ x)
      (by norm_num) hlap huvxx hprod
  have habs :
      |∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x| ≤
        ∫ x in (0 : ℝ)..1,
          |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x| :=
    intervalIntegral.abs_integral_le_integral_abs
      (by norm_num : (0 : ℝ) ≤ 1)
  calc
    H1PhysicalUvxxX p u v τ
        = -(∫ x in (0 : ℝ)..1,
            liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x) := rfl
    _ ≤ |∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x| :=
        neg_le_abs _
    _ ≤ ∫ x in (0 : ℝ)..1,
          |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x| :=
        habs
    _ ≤ H1lapL2Norm u τ *
          Real.sqrt
            (∫ x in (0 : ℝ)..1,
              (H1PhysicalChemUvxxPart p u v τ x) ^ 2) := by
        simpa [H1lapL2Norm, lapL2sq] using hcs
    _ ≤ H1lapL2Norm u τ * (M * V₂) :=
        mul_le_mul_of_nonneg_left hbound (H1lapL2Norm_nonneg u τ)
    _ = M * (V₂ * H1lapL2Norm u τ) := by
        ring

/-- The physical taxis scalar admits the sign-agnostic absolute-value bound
obtained directly from the spatial Cauchy--Schwarz estimate.  In particular,
this estimate does not use the sign of `p.χ₀`; that coefficient only enters
when the H¹ identity is assembled downstream. -/
theorem H1PhysicalTaxisX_abs_le_of_l2_bound
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {τ V₁ : ℝ}
    (hlap : IntervalIntegrable
      (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1)
    (htaxis : IntervalIntegrable
      (fun x => (H1PhysicalChemTaxisPart p u v τ x) ^ 2) volume (0 : ℝ) 1)
    (hprod : IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x|)
      volume (0 : ℝ) 1)
    (hbound :
      Real.sqrt
          (∫ x in (0 : ℝ)..1, (H1PhysicalChemTaxisPart p u v τ x) ^ 2)
        ≤ V₁ * H1gradL2Norm u τ) :
    |H1PhysicalTaxisX p u v τ| ≤
      V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ) := by
  have hcs :=
    ShenWork.GagliardoNirenberg.integral_abs_mul_le_sqrt
      (L := (1 : ℝ))
      (f := fun x => liftDeriv2 u τ x)
      (g := fun x => H1PhysicalChemTaxisPart p u v τ x)
      (by norm_num) hlap htaxis hprod
  have habs :
      |∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x| ≤
        ∫ x in (0 : ℝ)..1,
          |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x| :=
    intervalIntegral.abs_integral_le_integral_abs
      (by norm_num : (0 : ℝ) ≤ 1)
  calc
    |H1PhysicalTaxisX p u v τ|
        = |∫ x in (0 : ℝ)..1,
            liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x| := by
          simp [H1PhysicalTaxisX]
    _ ≤ ∫ x in (0 : ℝ)..1,
          |liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x| :=
        habs
    _ ≤ H1lapL2Norm u τ *
          Real.sqrt
            (∫ x in (0 : ℝ)..1,
              (H1PhysicalChemTaxisPart p u v τ x) ^ 2) := by
        simpa [H1lapL2Norm, lapL2sq] using hcs
    _ ≤ H1lapL2Norm u τ * (V₁ * H1gradL2Norm u τ) :=
        mul_le_mul_of_nonneg_left hbound (H1lapL2Norm_nonneg u τ)
    _ = V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ) := by
        ring

/-- The physical `u vₓₓ` scalar admits the corresponding sign-agnostic
absolute-value bound. -/
theorem H1PhysicalUvxxX_abs_le_of_l2_bound
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {τ V₂ M : ℝ}
    (hlap : IntervalIntegrable
      (fun x => (liftDeriv2 u τ x) ^ 2) volume (0 : ℝ) 1)
    (huvxx : IntervalIntegrable
      (fun x => (H1PhysicalChemUvxxPart p u v τ x) ^ 2) volume (0 : ℝ) 1)
    (hprod : IntervalIntegrable
      (fun x => |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x|)
      volume (0 : ℝ) 1)
    (hbound :
      Real.sqrt
          (∫ x in (0 : ℝ)..1, (H1PhysicalChemUvxxPart p u v τ x) ^ 2)
        ≤ M * V₂) :
    |H1PhysicalUvxxX p u v τ| ≤ M * (V₂ * H1lapL2Norm u τ) := by
  have hcs :=
    ShenWork.GagliardoNirenberg.integral_abs_mul_le_sqrt
      (L := (1 : ℝ))
      (f := fun x => liftDeriv2 u τ x)
      (g := fun x => H1PhysicalChemUvxxPart p u v τ x)
      (by norm_num) hlap huvxx hprod
  have habs :
      |∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x| ≤
        ∫ x in (0 : ℝ)..1,
          |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x| :=
    intervalIntegral.abs_integral_le_integral_abs
      (by norm_num : (0 : ℝ) ≤ 1)
  calc
    |H1PhysicalUvxxX p u v τ|
        = |∫ x in (0 : ℝ)..1,
            liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x| := by
          simp [H1PhysicalUvxxX]
    _ ≤ ∫ x in (0 : ℝ)..1,
          |liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x| :=
        habs
    _ ≤ H1lapL2Norm u τ *
          Real.sqrt
            (∫ x in (0 : ℝ)..1,
              (H1PhysicalChemUvxxPart p u v τ x) ^ 2) := by
        simpa [H1lapL2Norm, lapL2sq] using hcs
    _ ≤ H1lapL2Norm u τ * (M * V₂) :=
        mul_le_mul_of_nonneg_left hbound (H1lapL2Norm_nonneg u τ)
    _ = M * (V₂ * H1lapL2Norm u τ) := by
        ring

/-- Pointwise physical scalar estimates produce the concrete physical H¹
sqrt-bound frontier.  This is only a thin wrapper around
`H1SqrtTermBoundsBefore`; the analytic estimates remain explicit. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hchi : 0 ≤ -p.χ₀)
    (hV1 : 0 ≤ V₁) (hV2 : 0 ≤ V₂) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (htaxis_abs : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      |H1PhysicalTaxisX p u v τ| ≤
        V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ))
    (huvxx_abs : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      |H1PhysicalUvxxX p u v τ| ≤ M * (V₂ * H1lapL2Norm u τ))
    (hreact : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1PhysicalReactX p u τ ≤ L * (H1gradL2Norm u τ) ^ 2) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L := by
  refine ⟨?_⟩
  refine
    { hchi := hchi
      hV1 := hV1
      hV2 := hV2
      hM := hM
      hL := hL
      htaxis := ?_
      huvxx := ?_
      hreact := hreact }
  · intro τ hτ
    have hle :
        H1PhysicalTaxisX p u v τ ≤
          V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ) :=
      le_trans (le_abs_self _) (htaxis_abs τ hτ)
    exact mul_le_mul_of_nonneg_left hle hchi
  · intro τ hτ
    have hle :
        H1PhysicalUvxxX p u v τ ≤ M * (V₂ * H1lapL2Norm u τ) :=
      le_trans (le_abs_self _) (huvxx_abs τ hτ)
    exact mul_le_mul_of_nonneg_left hle hchi

/-- Named pointwise physical estimates produce the concrete physical H¹
sqrt-bound frontier. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_pointwiseEstimates
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSSqrtPointwiseEstimatesBefore p u v T V₁ V₂ M L) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds
    h.hchi h.hV1 h.hV2 h.hM h.hL h.taxis_abs h.uvxx_abs h.react_bound

/-- Fixed-time L² factor estimates produce the concrete physical H¹ sqrt-bound
frontier. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_L2SqrtBoundData
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSL2SqrtBoundDataBefore p u v T V₁ V₂ M L) :
    H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L := by
  refine ⟨?_⟩
  refine
    { hchi := h.hchi
      hV1 := h.hV1
      hV2 := h.hV2
      hM := h.hM
      hL := h.hL
      htaxis := ?_
      huvxx := ?_
      hreact := ?_ }
  · intro τ hτ
    have ht :
        H1PhysicalTaxisX p u v τ ≤
          V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ) :=
      H1PhysicalTaxisX_le_of_l2_bound
        (p := p) (u := u) (v := v) (τ := τ) (V₁ := V₁)
        (h.lap_sq_int τ hτ)
        (h.taxis_sq_int τ hτ)
        (h.taxis_prod_int τ hτ)
        (h.taxis_l2_bound τ hτ)
    exact mul_le_mul_of_nonneg_left ht h.hchi
  · intro τ hτ
    have hu :
        H1PhysicalUvxxX p u v τ ≤ M * (V₂ * H1lapL2Norm u τ) :=
      H1PhysicalUvxxX_le_of_l2_bound
        (p := p) (u := u) (v := v) (τ := τ) (V₂ := V₂) (M := M)
        (h.lap_sq_int τ hτ)
        (h.uvxx_sq_int τ hτ)
        (h.uvxx_prod_int τ hτ)
        (h.uvxx_l2_bound τ hτ)
    exact mul_le_mul_of_nonneg_left hu h.hchi
  · intro τ hτ
    exact h.react_bound τ hτ

#print axioms H1PhysicalTaxisX_le_of_l2_bound
#print axioms H1PhysicalUvxxX_le_of_l2_bound
#print axioms H1PhysicalTaxisX_abs_le_of_l2_bound
#print axioms H1PhysicalUvxxX_abs_le_of_l2_bound
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_pointwise_norm_bounds
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_pointwiseEstimates
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_L2SqrtBoundData

end ShenWork.Paper2.IntervalChiNegH1PhysicalSqrtBounds
