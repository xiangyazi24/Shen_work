/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.CorrectedModel

/-!
# Favorable-response algebra for the corrected model

This file contains the homogeneous algebra used by the weak-competition
proof:

* growth and decay relative to the favorable nullcline;
* the four-inequality squeeze to the coexistence equilibrium.

Admissible variational speeds, including exponential-moment integrability,
are defined in the theorem files that use them.
-/

namespace ShenWork.Liang

noncomputable section

/-! ## Favorable nullcline -/

/-- In a strictly favorable environment, a positive focal density grows in
one local step exactly on the sub-nullcline side. -/
theorem self_le_correctedResponse_iff
    {ρ α u v : ℝ}
    (hρ : 0 < ρ) (hα : 0 ≤ α) (hu : 0 < u) (hv : 0 ≤ v) :
    u ≤ correctedResponse ρ α u v ↔ u + α * v ≤ 1 := by
  rw [correctedResponse_eq_localResponse_of_nonneg hρ.le]
  have hden : 0 < 1 + ρ * (u + α * v) := by positivity
  constructor
  · intro h
    unfold localResponse at h
    have hmul :
        u * (1 + ρ * (u + α * v)) ≤ (1 + ρ) * u :=
      (le_div_iff₀ hden).mp h
    have hdenle :
        1 + ρ * (u + α * v) ≤ 1 + ρ := by
      apply (mul_le_mul_iff_of_pos_left hu).mp
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hrho : ρ * (u + α * v) ≤ ρ * 1 := by
      linarith
    exact (mul_le_mul_iff_of_pos_left hρ).mp (by simpa using hrho)
  · intro hnull
    unfold localResponse
    apply (le_div_iff₀ hden).2
    have hrho : ρ * (u + α * v) ≤ ρ * 1 :=
      mul_le_mul_of_nonneg_left hnull hρ.le
    have hdenle :
        1 + ρ * (u + α * v) ≤ 1 + ρ := by
      linarith
    have hmul :
        u * (1 + ρ * (u + α * v)) ≤ u * (1 + ρ) :=
      (mul_le_mul_iff_of_pos_left hu).2 hdenle
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- In a strictly favorable environment, a positive focal density decreases
in one local step exactly on the super-nullcline side. -/
theorem correctedResponse_le_self_iff
    {ρ α u v : ℝ}
    (hρ : 0 < ρ) (hα : 0 ≤ α) (hu : 0 < u) (hv : 0 ≤ v) :
    correctedResponse ρ α u v ≤ u ↔ 1 ≤ u + α * v := by
  rw [correctedResponse_eq_localResponse_of_nonneg hρ.le]
  have hden : 0 < 1 + ρ * (u + α * v) := by positivity
  constructor
  · intro h
    unfold localResponse at h
    have hmul :
        (1 + ρ) * u ≤ u * (1 + ρ * (u + α * v)) :=
      (div_le_iff₀ hden).mp h
    have hdenle :
        1 + ρ ≤ 1 + ρ * (u + α * v) := by
      apply (mul_le_mul_iff_of_pos_left hu).mp
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hrho : ρ * 1 ≤ ρ * (u + α * v) := by
      linarith
    exact (mul_le_mul_iff_of_pos_left hρ).mp (by simpa using hrho)
  · intro hnull
    unfold localResponse
    apply (div_le_iff₀ hden).2
    have hrho : ρ * 1 ≤ ρ * (u + α * v) :=
      mul_le_mul_of_nonneg_left hnull hρ.le
    have hdenle :
        1 + ρ ≤ 1 + ρ * (u + α * v) := by
      linarith
    have hmul :
        u * (1 + ρ) ≤ u * (1 + ρ * (u + α * v)) :=
      (mul_le_mul_iff_of_pos_left hu).2 hdenle
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The four nullcline inequalities arising from positive interior
liminf/limsup bounds squeeze a weak-competition rectangle to the unique
coexistence equilibrium. -/
theorem weakCompetition_rectangle_squeeze
    {α₁ α₂ uLower uUpper vLower vUpper : ℝ}
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1)
    (huOrder : uLower ≤ uUpper) (hvOrder : vLower ≤ vUpper)
    (huUpperNull : uUpper + α₁ * vLower ≤ 1)
    (huLowerNull : 1 ≤ uLower + α₁ * vUpper)
    (hvUpperNull : vUpper + α₂ * uLower ≤ 1)
    (hvLowerNull : 1 ≤ vLower + α₂ * uUpper) :
    uLower = coexistenceU α₁ α₂ ∧
    uUpper = coexistenceU α₁ α₂ ∧
    vLower = coexistenceV α₁ α₂ ∧
    vUpper = coexistenceV α₁ α₂ := by
  have hden :
      0 < 1 - α₁ * α₂ :=
    coexistence_denominator_pos hα₁0 hα₁1 hα₂0 hα₂1
  have huLowerRaw :
      1 - α₁ ≤ (1 - α₁ * α₂) * uLower := by
    have hmul :=
      mul_le_mul_of_nonneg_left hvUpperNull hα₁0.le
    nlinarith
  have huStar_le : coexistenceU α₁ α₂ ≤ uLower := by
    unfold coexistenceU
    exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using huLowerRaw)
  have huUpperRaw :
      (1 - α₁ * α₂) * uUpper ≤ 1 - α₁ := by
    have hmul :=
      mul_le_mul_of_nonneg_left hvLowerNull hα₁0.le
    nlinarith
  have huUpper_le : uUpper ≤ coexistenceU α₁ α₂ := by
    unfold coexistenceU
    exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using huUpperRaw)
  have huLowerEq : uLower = coexistenceU α₁ α₂ :=
    le_antisymm (huOrder.trans huUpper_le) huStar_le
  have huUpperEq : uUpper = coexistenceU α₁ α₂ :=
    le_antisymm huUpper_le (huStar_le.trans huOrder)
  have hvLowerRaw :
      1 - α₂ ≤ (1 - α₁ * α₂) * vLower := by
    have hmul :=
      mul_le_mul_of_nonneg_left huUpperNull hα₂0.le
    nlinarith [show α₂ * α₁ = α₁ * α₂ by ring]
  have hvStar_le : coexistenceV α₁ α₂ ≤ vLower := by
    unfold coexistenceV
    exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hvLowerRaw)
  have hvUpperRaw :
      (1 - α₁ * α₂) * vUpper ≤ 1 - α₂ := by
    have hmul :=
      mul_le_mul_of_nonneg_left huLowerNull hα₂0.le
    nlinarith [show α₂ * α₁ = α₁ * α₂ by ring]
  have hvUpper_le : vUpper ≤ coexistenceV α₁ α₂ := by
    unfold coexistenceV
    exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hvUpperRaw)
  have hvLowerEq : vLower = coexistenceV α₁ α₂ :=
    le_antisymm (hvOrder.trans hvUpper_le) hvStar_le
  have hvUpperEq : vUpper = coexistenceV α₁ α₂ :=
    le_antisymm hvUpper_le (hvStar_le.trans hvOrder)
  exact ⟨huLowerEq, huUpperEq, hvLowerEq, hvUpperEq⟩

section AxiomAudit

#print axioms self_le_correctedResponse_iff
#print axioms correctedResponse_le_self_iff
#print axioms weakCompetition_rectangle_squeeze

end AxiomAudit

end

end ShenWork.Liang
