import ShenWork.Paper2.IntervalChiNegH1PhysicalReactionBound
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
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
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

#print axioms H1PhysicalChemTaxisPart_le_of_resolverGrad
#print axioms H1PhysicalChemUvxxPart_le_of_core
#print axioms H1PhysicalChemFactorBoundsBefore_of_resolverSup

end ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
