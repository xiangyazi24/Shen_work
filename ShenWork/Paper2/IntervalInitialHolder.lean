/-
  ShenWork/Paper2/IntervalInitialHolder.lean

  Small geometry package for the zero-time initial-leg Holder route.

  The eventual faithful producer should show that the Neumann heat semigroup
  preserves the initial Holder modulus.  This file only records the datum-level
  Holder predicate and period-2 circle distance facts needed by the reflected
  coupling route; it does not assert semigroup preservation.
-/
import ShenWork.Paper2.ChemMildHolderBootstrap
import Mathlib.Analysis.Normed.Group.AddCircle

open Metric
open MeasureTheory
open scoped Real

namespace ShenWork.Paper2

noncomputable section

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)

/-- Initial-data spatial Holder modulus on the genuine interval domain. -/
def InitialDatumHolder
    (u₀ : intervalDomainPoint → ℝ) (θ H₀ : ℝ) : Prop :=
  ∀ x y : intervalDomainPoint,
    |u₀ x - u₀ y| ≤ H₀ * |x.1 - y.1| ^ θ

/-- Contractive coupling interface for the Neumann heat leg started from two
points.  This is deliberately a consumer-facing interface: the actual
probabilistic construction of such a coupling is a separate analytic task. -/
structure NeumannHeatContractiveCouplingFor
    (t : ℝ) (x y : intervalDomainPoint) (f : ℝ → ℝ) where
  μ : Measure (ℝ × ℝ)
  prob : IsProbabilityMeasure μ
  support : ∀ᵐ z ∂μ, z.1 ∈ Set.Icc (0 : ℝ) 1 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1
  dist_le : ∀ᵐ z ∂μ, |z.1 - z.2| ≤ |x.1 - y.1|
  diff_integrable : Integrable (fun z : ℝ × ℝ => f z.1 - f z.2) μ
  semigroup_diff_eq :
    intervalFullSemigroupOperator t f x.1 -
        intervalFullSemigroupOperator t f y.1 =
      ∫ z : ℝ × ℝ, f z.1 - f z.2 ∂μ

/-- If the Neumann heat leg admits interval-supported couplings whose coordinate
distance is contractive, then initial-data Holder regularity propagates to the
zero-time initial-leg Holder frontier. -/
theorem InitialLegUniformHolderAtZero_of_contracting_couplings
    {u₀ : intervalDomainPoint → ℝ} {T θ H₀ : ℝ}
    (_hθ0 : 0 < θ) (_hH₀ : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor t x y (intervalDomainLift u₀)) :
    InitialLegUniformHolderAtZero u₀ T θ H₀ := by
  intro t htpos htT x y
  rcases hplan t htpos htT x y with ⟨μ, hprob, hsupp, hdist, hint, hdiff⟩
  haveI : IsProbabilityMeasure μ := hprob
  rw [hdiff]
  have hpoint :
      (fun z : ℝ × ℝ => |intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2|)
        ≤ᵐ[μ]
      fun _z : ℝ × ℝ => H₀ * |x.1 - y.1| ^ θ := by
    filter_upwards [hsupp, hdist] with z hz hdist_z
    have hholder_z :
        |intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2|
          ≤ H₀ * |z.1 - z.2| ^ θ := by
      simpa [intervalDomainLift, hz.1, hz.2] using
        hholder ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩
    exact hholder_z.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hdist_z _hθ0.le) _hH₀)
  calc
    |∫ z : ℝ × ℝ,
        intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2 ∂μ|
        = ‖∫ z : ℝ × ℝ,
            intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2 ∂μ‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ z : ℝ × ℝ,
          ‖intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ = ∫ z : ℝ × ℝ,
          |intervalDomainLift u₀ z.1 - intervalDomainLift u₀ z.2| ∂μ := by
        simp [Real.norm_eq_abs]
    _ ≤ ∫ _z : ℝ × ℝ, H₀ * |x.1 - y.1| ^ θ ∂μ :=
        integral_mono_ae hint.abs (integrable_const _) hpoint
    _ = H₀ * |x.1 - y.1| ^ θ := by
        simp

/-- On the period-2 additive circle, real representatives whose ordinary
distance is at most half the period have the same circle distance. -/
theorem addCircle_two_dist_coe_eq_abs_of_abs_le_one {x y : ℝ}
    (hxy : |x - y| ≤ 1) :
    dist ((x : AddCircle (2 : ℝ))) (y : AddCircle (2 : ℝ)) = |x - y| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  have hp : (2 : ℝ) ≠ 0 := by norm_num
  have hhalf : |x - y| ≤ |(2 : ℝ)| / 2 := by
    norm_num at hxy ⊢
    exact hxy
  simpa using
    (AddCircle.norm_coe_eq_abs_iff (p := (2 : ℝ)) (x := x - y) hp).2 hhalf

/-- Points in the interval `[0,1]` embed isometrically into the period-2 circle. -/
theorem addCircle_two_dist_coe_eq_abs_Icc {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    dist ((x : AddCircle (2 : ℝ))) (y : AddCircle (2 : ℝ)) = |x - y| := by
  apply addCircle_two_dist_coe_eq_abs_of_abs_le_one
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Common translation on the period-2 circle preserves distance.  This is the
pure metric part of the reflected Brownian coupling argument. -/
theorem addCircle_two_dist_translate (x y z : ℝ) :
    dist (((x + z : ℝ) : AddCircle (2 : ℝ)))
        ((y + z : ℝ) : AddCircle (2 : ℝ)) =
      dist ((x : AddCircle (2 : ℝ))) (y : AddCircle (2 : ℝ)) := by
  rw [dist_eq_norm, dist_eq_norm, ← QuotientAddGroup.mk_sub,
    ← QuotientAddGroup.mk_sub]
  congr 1
  ring_nf

end

end ShenWork.Paper2
