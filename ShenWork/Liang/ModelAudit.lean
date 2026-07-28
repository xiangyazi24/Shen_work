/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic audit of the shifting-habitat competition model

This file isolates facts that can be checked before any compactness or
spreading argument is attempted.  The local Beverton--Holt-type response
printed in the proposal is

`((1 + ρ) * u) / (1 + ρ * (u + α * v))`.

For negative `ρ`, this expression is not nonnegative on the whole positive
cone and it is increasing, rather than decreasing, in the competitor.  The
invariant-simplex hypothesis `u + αv ≤ 1` repairs positivity but does not
repair that reversal of competitive order.
-/

open Filter Topology

namespace ShenWork.Liang

noncomputable section

/-- The local, pre-dispersal response appearing in the proposal. -/
def localResponse (ρ α u v : ℝ) : ℝ :=
  ((1 + ρ) * u) / (1 + ρ * (u + α * v))

@[simp]
theorem localResponse_zero_focal (ρ α v : ℝ) :
    localResponse ρ α 0 v = 0 := by
  simp [localResponse]

/-- On the natural simplex, the denominator stays strictly positive whenever
the low-density multiplier `1 + ρ` is positive. -/
theorem localResponse_denominator_pos
    {ρ α u v : ℝ} (hρ : -1 < ρ) (hα : 0 ≤ α)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsimplex : u + α * v ≤ 1) :
    0 < 1 + ρ * (u + α * v) := by
  have hq0 : 0 ≤ u + α * v := by positivity
  by_cases hρ0 : 0 ≤ ρ
  · have hprod : 0 ≤ ρ * (u + α * v) := mul_nonneg hρ0 hq0
    linarith
  · have hρneg : ρ < 0 := lt_of_not_ge hρ0
    have hmul : ρ ≤ ρ * (u + α * v) := by
      simpa using mul_le_mul_of_nonpos_left hsimplex hρneg.le
    linarith

/-- The printed response is nonnegative on the natural invariant simplex. -/
theorem localResponse_nonneg
    {ρ α u v : ℝ} (hρ : -1 < ρ) (hα : 0 ≤ α)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsimplex : u + α * v ≤ 1) :
    0 ≤ localResponse ρ α u v := by
  unfold localResponse
  exact div_nonneg
    (mul_nonneg (by linarith) hu)
    (localResponse_denominator_pos hρ hα hu hv hsimplex).le

/-- The natural simplex also bounds the response by one. -/
theorem localResponse_le_one
    {ρ α u v : ℝ} (hρ : -1 < ρ) (hα : 0 ≤ α)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsimplex : u + α * v ≤ 1) :
    localResponse ρ α u v ≤ 1 := by
  have hden :=
    localResponse_denominator_pos hρ hα hu hv hsimplex
  have hαv : 0 ≤ α * v := mul_nonneg hα hv
  have hdiff :
      0 ≤ (1 + ρ * (u + α * v)) - (1 + ρ) * u := by
    rw [show
        (1 + ρ * (u + α * v)) - (1 + ρ) * u =
          (1 - (u + α * v)) + (1 + ρ) * (α * v) by ring]
    exact add_nonneg (sub_nonneg.mpr hsimplex)
      (mul_nonneg (by linarith) hαv)
  unfold localResponse
  apply (div_le_iff₀ hden).2
  nlinarith

/-- In an unfavorable region (`ρ ≤ 0`), the response does not exceed the
current focal-species density, provided the state lies in the simplex. -/
theorem localResponse_le_self_of_nonpos
    {ρ α u v : ℝ} (hρ : -1 < ρ) (hρ0 : ρ ≤ 0)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsimplex : u + α * v ≤ 1) :
    localResponse ρ α u v ≤ u := by
  have hden :=
    localResponse_denominator_pos hρ hα hu hv hsimplex
  have hgain :
      0 ≤ (-ρ) * u * (1 - (u + α * v)) :=
    mul_nonneg (mul_nonneg (neg_nonneg.mpr hρ0) hu)
      (sub_nonneg.mpr hsimplex)
  unfold localResponse
  apply (div_le_iff₀ hden).2
  nlinarith

/-- In a favorable region (`ρ ≥ 0`), the nonlinear response is bounded by its
linearization at zero. -/
theorem localResponse_le_linear_of_nonneg
    {ρ α u v : ℝ} (hρ : 0 ≤ ρ)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    localResponse ρ α u v ≤ (1 + ρ) * u := by
  have hq0 : 0 ≤ u + α * v := by positivity
  have hden : 0 < 1 + ρ * (u + α * v) := by positivity
  have hnum : 0 ≤ (1 + ρ) * u := by positivity
  have hgain :
      0 ≤ (1 + ρ) * u * (ρ * (u + α * v)) := by positivity
  unfold localResponse
  apply (div_le_iff₀ hden).2
  nlinarith

/-! ## Exact obstructions in the printed model -/

/-- The assumptions printed in the proposal do not preserve nonnegativity on
the whole positive cone: `ρ = -1/2`, `u = 3` produces `-3`. -/
theorem printed_hypotheses_do_not_preserve_nonnegativity :
    localResponse (-(1 / 2 : ℝ)) 0 3 0 = -3 := by
  norm_num [localResponse]

/-- With negative `ρ`, increasing the competitor can increase the focal
species response, even while both states lie in the natural simplex. -/
theorem unfavorable_region_reverses_competition :
    localResponse (-(1 / 2 : ℝ)) 1 (1 / 2) 0 <
      localResponse (-(1 / 2 : ℝ)) 1 (1 / 2) (1 / 2) := by
  norm_num [localResponse]

/-! ## Weak-competition coexistence equilibrium -/

/-- First coordinate of the positive coexistence equilibrium. -/
def coexistenceU (α₁ α₂ : ℝ) : ℝ :=
  (1 - α₁) / (1 - α₁ * α₂)

/-- Second coordinate of the positive coexistence equilibrium. -/
def coexistenceV (α₁ α₂ : ℝ) : ℝ :=
  (1 - α₂) / (1 - α₁ * α₂)

theorem coexistence_denominator_pos
    {α₁ α₂ : ℝ} (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1) :
    0 < 1 - α₁ * α₂ := by
  have hprod0 : 0 < α₁ * α₂ := mul_pos hα₁0 hα₂0
  have hprod : α₁ * α₂ < 1 := calc
    α₁ * α₂ < 1 * α₂ := mul_lt_mul_of_pos_right hα₁1 hα₂0
    _ = α₂ := one_mul α₂
    _ < 1 := hα₂1
  linarith

theorem coexistenceU_pos
    {α₁ α₂ : ℝ} (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1) :
    0 < coexistenceU α₁ α₂ := by
  exact div_pos (sub_pos.mpr hα₁1)
    (coexistence_denominator_pos hα₁0 hα₁1 hα₂0 hα₂1)

theorem coexistenceV_pos
    {α₁ α₂ : ℝ} (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1) :
    0 < coexistenceV α₁ α₂ := by
  exact div_pos (sub_pos.mpr hα₂1)
    (coexistence_denominator_pos hα₁0 hα₁1 hα₂0 hα₂1)

/-- The coexistence formula lies on the first zero-growth nullcline. -/
theorem coexistence_first_nullcline
    {α₁ α₂ : ℝ} (hden : α₁ * α₂ ≠ 1) :
    coexistenceU α₁ α₂ + α₁ * coexistenceV α₁ α₂ = 1 := by
  unfold coexistenceU coexistenceV
  field_simp
  ring

/-- The coexistence formula lies on the second zero-growth nullcline. -/
theorem coexistence_second_nullcline
    {α₁ α₂ : ℝ} (hden : α₁ * α₂ ≠ 1) :
    coexistenceV α₁ α₂ + α₂ * coexistenceU α₁ α₂ = 1 := by
  have hden' : α₂ * α₁ ≠ 1 := by
    simpa [mul_comm] using hden
  simpa [coexistenceU, coexistenceV, mul_comm] using
    (coexistence_first_nullcline (α₁ := α₂) (α₂ := α₁) hden')

/-- Every point of the zero-growth nullcline is fixed by the local response
whenever `1 + ρ` is nonzero. -/
theorem localResponse_eq_self_of_nullcline
    {ρ α u v : ℝ} (hρ : ρ ≠ -1) (hnull : u + α * v = 1) :
    localResponse ρ α u v = u := by
  have hone : 1 + ρ ≠ 0 := by
    intro hzero
    apply hρ
    linarith
  unfold localResponse
  rw [hnull]
  field_simp

theorem coexistenceU_fixed
    {ρ α₁ α₂ : ℝ} (hρ : ρ ≠ -1) (hden : α₁ * α₂ ≠ 1) :
    localResponse ρ α₁ (coexistenceU α₁ α₂) (coexistenceV α₁ α₂) =
      coexistenceU α₁ α₂ := by
  apply localResponse_eq_self_of_nullcline hρ
  exact coexistence_first_nullcline hden

theorem coexistenceV_fixed
    {ρ α₁ α₂ : ℝ} (hρ : ρ ≠ -1) (hden : α₁ * α₂ ≠ 1) :
    localResponse ρ α₂ (coexistenceV α₁ α₂) (coexistenceU α₁ α₂) =
      coexistenceV α₁ α₂ := by
  apply localResponse_eq_self_of_nullcline hρ
  exact coexistence_second_nullcline hden

/-! ## Moving-coordinate geometry -/

/-- The environment coordinate sampled by an observer moving at speed `s`
when the habitat moves at speed `c`. -/
def movingCoordinate (c s : ℝ) (n : ℕ) : ℝ :=
  (s - c) * (n : ℝ)

/-- An observer slower than the habitat samples the far-left environment. -/
theorem slowerObserver_tendsto_atBot
    {c s : ℝ} (hs : s < c) :
    Tendsto (movingCoordinate c s) atTop atBot := by
  have hlinear :
      Tendsto (fun x : ℝ => (s - c) * x) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hs)
  exact hlinear.comp tendsto_natCast_atTop_atTop

/-- Consequently, a profile with a far-left limit converges to that limit
along every observer slower than the habitat. -/
theorem environmentAlongSlowerObserver
    {ρ : ℝ → ℝ} {ρminus c s : ℝ}
    (hρ : Tendsto ρ atBot (𝓝 ρminus)) (hs : s < c) :
    Tendsto (fun n : ℕ => ρ (movingCoordinate c s n))
      atTop (𝓝 ρminus) :=
  hρ.comp (slowerObserver_tendsto_atBot hs)

/-- An observer faster than the habitat samples the far-right environment. -/
theorem fasterObserver_tendsto_atTop
    {c s : ℝ} (hs : c < s) :
    Tendsto (movingCoordinate c s) atTop atTop := by
  have hlinear :
      Tendsto (fun x : ℝ => (s - c) * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (sub_pos.mpr hs)).2 tendsto_id
  exact hlinear.comp tendsto_natCast_atTop_atTop

/-- A profile with a far-right limit converges to that limit along every
observer faster than the habitat. -/
theorem environmentAlongFasterObserver
    {ρ : ℝ → ℝ} {ρplus c s : ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρplus)) (hs : c < s) :
    Tendsto (fun n : ℕ => ρ (movingCoordinate c s n))
      atTop (𝓝 ρplus) :=
  hρ.comp (fasterObserver_tendsto_atTop hs)

section AxiomAudit

#print axioms printed_hypotheses_do_not_preserve_nonnegativity
#print axioms unfavorable_region_reverses_competition
#print axioms coexistenceU_fixed
#print axioms environmentAlongSlowerObserver

end AxiomAudit

end

end ShenWork.Liang
