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
open scoped Real

namespace ShenWork.Paper2

noncomputable section

open ShenWork.IntervalDomain (intervalDomainPoint)

/-- Initial-data spatial Holder modulus on the genuine interval domain. -/
def InitialDatumHolder
    (u₀ : intervalDomainPoint → ℝ) (θ H₀ : ℝ) : Prop :=
  ∀ x y : intervalDomainPoint,
    |u₀ x - u₀ y| ≤ H₀ * |x.1 - y.1| ^ θ

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
