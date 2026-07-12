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
open ShenWork.Paper2.IntervalChiNegH1PhysicalSqrtBounds

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

/-- Sign-agnostic fixed-time L² data for the two physical chemotaxis
scalars.  This is the absolute-value analogue of
`H1PhysicalChemL2SqrtBoundDataBefore`, with no hypothesis on `p.χ₀`. -/
structure H1PhysicalChemL2AbsBoundDataBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M : ℝ) : Prop where
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
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

/-- The three sign-agnostic physical H¹ scalar bounds consumed by the
`|χ₀|` absorption route. -/
structure H1PhysicalRHSAbsTermBoundsBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
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

/-- Explicit source-side bound for the `u v_xx`/denominator-derivative core
once `u`, `v`, and the resolver gradient have fixed-before-`T` sup bounds. -/
def H1PhysicalChemUvxxCoreSupConstant (p : CM2Params) (M V G : ℝ) : ℝ :=
  p.μ * V + p.ν * M ^ p.γ + p.β * G ^ 2

/-- A more primitive fixed-before-`T` source residual: `u` is nonnegative and
bounded by `M`, `v` is bounded by `V`, and the resolver gradient is bounded by
`G`.  This is still source-facing; producing these constants uniformly is not
done here. -/
structure H1PhysicalChemValueGradSupBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T M V G : ℝ) : Prop where
  hM : 0 ≤ M
  hV : 0 ≤ V
  hG : 0 ≤ G
  u_nonneg_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ intervalDomainLift (u τ) x ∧ intervalDomainLift (u τ) x ≤ M
  v_abs_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift (v τ) x| ≤ V
  resolver_grad_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |resolverGradReal p (u τ) x| ≤ G

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

private theorem H1PhysicalChemUvxxCore_le_of_valueGradSup
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    {T M V G τ x : ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hG : 0 ≤ G)
    (hu : 0 ≤ intervalDomainLift (u τ) x ∧
      intervalDomainLift (u τ) x ≤ M)
    (hv : |intervalDomainLift (v τ) x| ≤ V)
    (hg : |resolverGradReal p (u τ) x| ≤ G) :
    |(p.μ * intervalDomainLift (v τ) x -
        p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
        (1 + intervalDomainLift (v τ) x) ^ p.β -
      p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
        (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)|
      ≤ H1PhysicalChemUvxxCoreSupConstant p M V G := by
  set U : ℝ := intervalDomainLift (u τ) x with hU
  set W : ℝ := intervalDomainLift (v τ) x with hW
  set vx : ℝ := deriv (intervalDomainLift (v τ)) x with hvx
  set denβ : ℝ := (1 + W) ^ p.β with hdenβ
  set denβ1 : ℝ := (1 + W) ^ (p.β + 1) with hdenβ1
  have hvx_eq : vx = resolverGradReal p (u τ) x := by
    rw [hvx]
    exact solution_lift_v_deriv_eq_resolverGrad_Icc hsol hτ hx
  have hg_vx : |vx| ≤ G := by
    simpa [hvx_eq] using hg
  have hW_nonneg : 0 ≤ W := by
    rw [hW]
    exact solution_lift_v_nonneg_Icc hsol hτ x hx
  have hbase : 1 ≤ 1 + W := by linarith
  have hdenβ_ge : 1 ≤ denβ := by
    rw [hdenβ]
    exact Real.one_le_rpow hbase p.hβ
  have hdenβ1_ge : 1 ≤ denβ1 := by
    rw [hdenβ1]
    exact Real.one_le_rpow hbase (by linarith [p.hβ] : 0 ≤ p.β + 1)
  have hdenβ_pos : 0 < denβ := lt_of_lt_of_le zero_lt_one hdenβ_ge
  have hdenβ1_pos : 0 < denβ1 := lt_of_lt_of_le zero_lt_one hdenβ1_ge
  have hUpow_nonneg : 0 ≤ U ^ p.γ := Real.rpow_nonneg hu.1 p.γ
  have hUpow_le : U ^ p.γ ≤ M ^ p.γ :=
    Real.rpow_le_rpow hu.1 hu.2 p.hγ.le
  have hUpow_abs_le : |U ^ p.γ| ≤ M ^ p.γ := by
    rw [abs_of_nonneg hUpow_nonneg]
    exact hUpow_le
  have hMpow_nonneg : 0 ≤ M ^ p.γ := Real.rpow_nonneg hM p.γ
  have hnum₁ :
      |p.μ * W - p.ν * U ^ p.γ| ≤ p.μ * V + p.ν * M ^ p.γ := by
    calc
      |p.μ * W - p.ν * U ^ p.γ|
          = |p.μ * W + -(p.ν * U ^ p.γ)| := by rw [sub_eq_add_neg]
      _ ≤ |p.μ * W| + |-(p.ν * U ^ p.γ)| := abs_add_le _ _
      _ = |p.μ * W| + |p.ν * U ^ p.γ| := by rw [abs_neg]
      _ = p.μ * |W| + p.ν * |U ^ p.γ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg p.hμ.le,
            abs_of_nonneg p.hν.le]
      _ ≤ p.μ * V + p.ν * M ^ p.γ :=
          add_le_add
            (mul_le_mul_of_nonneg_left (by simpa [W, hW] using hv) p.hμ.le)
            (mul_le_mul_of_nonneg_left hUpow_abs_le p.hν.le)
  have hnum₁_nonneg : 0 ≤ p.μ * V + p.ν * M ^ p.γ :=
    add_nonneg (mul_nonneg p.hμ.le hV) (mul_nonneg p.hν.le hMpow_nonneg)
  have hterm₁ :
      |(p.μ * W - p.ν * U ^ p.γ) / denβ|
        ≤ p.μ * V + p.ν * M ^ p.γ := by
    calc
      |(p.μ * W - p.ν * U ^ p.γ) / denβ|
          = |p.μ * W - p.ν * U ^ p.γ| / denβ := by
              rw [abs_div, abs_of_pos hdenβ_pos]
      _ ≤ (p.μ * V + p.ν * M ^ p.γ) / denβ :=
          div_le_div_of_nonneg_right hnum₁ hdenβ_pos.le
      _ ≤ (p.μ * V + p.ν * M ^ p.γ) / 1 :=
          div_le_div_of_nonneg_left hnum₁_nonneg zero_lt_one hdenβ_ge
      _ = p.μ * V + p.ν * M ^ p.γ := by rw [div_one]
  have hvx_sq_le : vx ^ 2 ≤ G ^ 2 := by
    calc
      vx ^ 2 = |vx| ^ 2 := by rw [sq_abs]
      _ ≤ G ^ 2 := (sq_le_sq₀ (abs_nonneg vx) hG).2 hg_vx
  have hnum₂ :
      |p.β * vx ^ 2| ≤ p.β * G ^ 2 := by
    calc
      |p.β * vx ^ 2| = p.β * vx ^ 2 := by
          rw [abs_of_nonneg (mul_nonneg p.hβ (sq_nonneg vx))]
      _ ≤ p.β * G ^ 2 := mul_le_mul_of_nonneg_left hvx_sq_le p.hβ
  have hnum₂_nonneg : 0 ≤ p.β * G ^ 2 :=
    mul_nonneg p.hβ (sq_nonneg G)
  have hterm₂ :
      |p.β * vx ^ 2 / denβ1| ≤ p.β * G ^ 2 := by
    calc
      |p.β * vx ^ 2 / denβ1|
          = |p.β * vx ^ 2| / denβ1 := by
              rw [abs_div, abs_of_pos hdenβ1_pos]
      _ ≤ (p.β * G ^ 2) / denβ1 :=
          div_le_div_of_nonneg_right hnum₂ hdenβ1_pos.le
      _ ≤ (p.β * G ^ 2) / 1 :=
          div_le_div_of_nonneg_left hnum₂_nonneg zero_lt_one hdenβ1_ge
      _ = p.β * G ^ 2 := by rw [div_one]
  have hsum :
      |(p.μ * W - p.ν * U ^ p.γ) / denβ -
          p.β * vx ^ 2 / denβ1| ≤
        |(p.μ * W - p.ν * U ^ p.γ) / denβ| +
          |p.β * vx ^ 2 / denβ1| := by
    calc
      |(p.μ * W - p.ν * U ^ p.γ) / denβ -
          p.β * vx ^ 2 / denβ1|
          = |(p.μ * W - p.ν * U ^ p.γ) / denβ +
              -(p.β * vx ^ 2 / denβ1)| := by rw [sub_eq_add_neg]
      _ ≤ |(p.μ * W - p.ν * U ^ p.γ) / denβ| +
            |-(p.β * vx ^ 2 / denβ1)| := abs_add_le _ _
      _ = |(p.μ * W - p.ν * U ^ p.γ) / denβ| +
            |p.β * vx ^ 2 / denβ1| := by rw [abs_neg]
  calc
    |(p.μ * intervalDomainLift (v τ) x -
        p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
        (1 + intervalDomainLift (v τ) x) ^ p.β -
      p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
        (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)|
        = |(p.μ * W - p.ν * U ^ p.γ) / denβ -
            p.β * vx ^ 2 / denβ1| := by
          simp [U, W, vx, denβ, denβ1]
    _ ≤ |(p.μ * W - p.ν * U ^ p.γ) / denβ| +
          |p.β * vx ^ 2 / denβ1| := hsum
    _ ≤ (p.μ * V + p.ν * M ^ p.γ) + p.β * G ^ 2 :=
        add_le_add hterm₁ hterm₂
    _ = H1PhysicalChemUvxxCoreSupConstant p M V G := by
        simp [H1PhysicalChemUvxxCoreSupConstant, add_assoc]

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

/-- Fixed-before-`T` value/gradient sup data lower to the resolver/core residual
needed by the physical H¹ sqrt route. -/
theorem H1PhysicalChemResolverSupBefore_of_valueGradSup
    {p : CM2Params} {T M V G : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (h : H1PhysicalChemValueGradSupBefore p u v T M V G) :
    H1PhysicalChemResolverSupBefore p u v T G
      (H1PhysicalChemUvxxCoreSupConstant p M V G) M := by
  refine
    { hV1 := h.hG
      hV2 := ?_
      hM := h.hM
      u_abs_le := ?_
      resolver_grad_le := h.resolver_grad_le
      uvxx_core_le := ?_ }
  · exact
      add_nonneg
        (add_nonneg
          (mul_nonneg p.hμ.le h.hV)
          (mul_nonneg p.hν.le (Real.rpow_nonneg h.hM p.γ)))
        (mul_nonneg p.hβ (sq_nonneg G))
  · intro τ hτ x hx
    have hu := h.u_nonneg_le τ hτ x hx
    rw [abs_of_nonneg hu.1]
    exact hu.2
  · intro τ hτ x hx
    exact
      H1PhysicalChemUvxxCore_le_of_valueGradSup
        (p := p) (T := T) (M := M) (V := V) (G := G)
        (u := u) (v := v) hsol hτ hx
        h.hM h.hV h.hG
        (h.u_nonneg_le τ hτ x hx)
        (h.v_abs_le τ hτ x hx)
        (h.resolver_grad_le τ hτ x hx)

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
the sign-agnostic chemotaxis-side L² data package.  The fixed-before-`T`
constants are supplied by `hchem`, and no sign of `p.χ₀` is used. -/
theorem H1PhysicalChemL2AbsBoundDataBefore_of_classical_factorBounds
    {p : CM2Params} {T V₁ V₂ M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchem : H1PhysicalChemFactorBoundsBefore p u v T V₁ V₂ M) :
    H1PhysicalChemL2AbsBoundDataBefore p u v T V₁ V₂ M := by
  have hRep :=
    H1PhysicalRHSRepIntegrandsContinuousStrictBefore_of_classicalSolution
      (p := p) (u := u) (v := v) (T := T) hsol
  refine
    { hV1 := hchem.hV1
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

/-- Add the downstream `χ₀ ≤ 0` sign hypothesis to the sign-agnostic L² data,
recovering the older square-root route package. -/
theorem H1PhysicalChemL2SqrtBoundDataBefore_of_classical_factorBounds
    {p : CM2Params} {T V₁ V₂ M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hchem : H1PhysicalChemFactorBoundsBefore p u v T V₁ V₂ M) :
    H1PhysicalChemL2SqrtBoundDataBefore p u v T V₁ V₂ M := by
  have h :=
    H1PhysicalChemL2AbsBoundDataBefore_of_classical_factorBounds
      (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M)
      (u := u) (v := v) hsol hchem
  exact
    { hchi := hchi
      hV1 := h.hV1
      hV2 := h.hV2
      hM := h.hM
      lap_sq_int := h.lap_sq_int
      taxis_sq_int := h.taxis_sq_int
      uvxx_sq_int := h.uvxx_sq_int
      taxis_prod_int := h.taxis_prod_int
      uvxx_prod_int := h.uvxx_prod_int
      taxis_l2_bound := h.taxis_l2_bound
      uvxx_l2_bound := h.uvxx_l2_bound }

/-- Sign-agnostic L² chemotaxis data and the classical reaction estimate
produce exactly the three absolute term bounds used by the positive-`χ₀`
H¹ absorption route. -/
theorem H1PhysicalRHSAbsTermBoundsBefore_of_chemL2AbsBoundData
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hL : p.a ≤ L)
    (hchem : H1PhysicalChemL2AbsBoundDataBefore p u v T V₁ V₂ M) :
    H1PhysicalRHSAbsTermBoundsBefore p u v T V₁ V₂ M L := by
  refine
    { hV1 := hchem.hV1
      hV2 := hchem.hV2
      hM := hchem.hM
      hL := le_trans p.ha hL
      taxis_abs := ?_
      uvxx_abs := ?_
      react_bound := ?_ }
  · intro τ hτ
    exact
      H1PhysicalTaxisX_abs_le_of_l2_bound
        (p := p) (u := u) (v := v) (τ := τ) (V₁ := V₁)
        (hchem.lap_sq_int τ hτ)
        (hchem.taxis_sq_int τ hτ)
        (hchem.taxis_prod_int τ hτ)
        (hchem.taxis_l2_bound τ hτ)
  · intro τ hτ
    exact
      H1PhysicalUvxxX_abs_le_of_l2_bound
        (p := p) (u := u) (v := v) (τ := τ) (V₂ := V₂) (M := M)
        (hchem.lap_sq_int τ hτ)
        (hchem.uvxx_sq_int τ hτ)
        (hchem.uvxx_prod_int τ hτ)
        (hchem.uvxx_l2_bound τ hτ)
  · intro τ hτ
    exact
      H1PhysicalReactX_le_L_H1gradL2Norm_sq_of_classicalSolution
        (p := p) (T := T) (τ := τ) (L := L)
        (u := u) (v := v) hsol hτ hL

/-- Classical regularity and pointwise chemotaxis factor bounds produce the
three sign-agnostic physical H¹ term estimates. -/
theorem H1PhysicalRHSAbsTermBoundsBefore_of_classical_factorBounds
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hL : p.a ≤ L)
    (hchem : H1PhysicalChemFactorBoundsBefore p u v T V₁ V₂ M) :
    H1PhysicalRHSAbsTermBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSAbsTermBoundsBefore_of_chemL2AbsBoundData
    (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M) (L := L)
    (u := u) (v := v) hsol hL
    (H1PhysicalChemL2AbsBoundDataBefore_of_classical_factorBounds
      (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M)
      (u := u) (v := v) hsol hchem)

/-- Resolver/core sup bounds lower directly to the three sign-agnostic
physical H¹ term estimates. -/
theorem H1PhysicalRHSAbsTermBoundsBefore_of_classical_resolverSup
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hL : p.a ≤ L)
    (hres : H1PhysicalChemResolverSupBefore p u v T V₁ V₂ M) :
    H1PhysicalRHSAbsTermBoundsBefore p u v T V₁ V₂ M L :=
  H1PhysicalRHSAbsTermBoundsBefore_of_classical_factorBounds
    (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M) (L := L)
    (u := u) (v := v) hsol hL
    (H1PhysicalChemFactorBoundsBefore_of_resolverSup
      (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M)
      (u := u) (v := v) hsol hres)

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
#print axioms H1PhysicalChemUvxxCore_le_of_valueGradSup
#print axioms H1PhysicalChemFactorBoundsBefore_of_resolverSup
#print axioms H1PhysicalChemResolverSupBefore_of_valueGradSup
#print axioms H1PhysicalChemL2AbsBoundDataBefore_of_classical_factorBounds
#print axioms H1PhysicalRHSAbsTermBoundsBefore_of_chemL2AbsBoundData
#print axioms H1PhysicalRHSAbsTermBoundsBefore_of_classical_factorBounds
#print axioms H1PhysicalRHSAbsTermBoundsBefore_of_classical_resolverSup
#print axioms H1PhysicalChemL2SqrtBoundDataBefore_of_classical_factorBounds
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_classical_factorBounds
#print axioms H1PhysicalChemL2SqrtBoundDataBefore_of_classical_resolverSup
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_classical_resolverSup

end ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
