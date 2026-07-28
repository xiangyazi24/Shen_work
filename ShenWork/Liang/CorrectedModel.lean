/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.ModelAudit
import Mathlib.Tactic.GCongr

/-!
# A competitive correction of the shifting-habitat response

The signed environmental increment `ρ` should control low-density growth, but
it should not make density dependence change sign.  The smallest correction
that leaves the proposal unchanged in the favorable region is

`((1 + ρ) * u) / (1 + max ρ 0 * (u + αv))`.

Thus the unfavorable region is linear and subcritical, while the favorable
region retains the proposed Beverton--Holt competition map.  This file proves
the properties needed before comparison and spreading theory can begin:
global positivity, the unit-interval bound, monotonicity in the focal species,
antitonicity in the competitor, and preservation of the proposed favorable
coexistence equilibrium.
-/

namespace ShenWork.Liang

noncomputable section

/-- Recommended local response: signed low-density growth with nonnegative
density dependence. -/
def correctedResponse (ρ α u v : ℝ) : ℝ :=
  ((1 + ρ) * u) / (1 + max ρ 0 * (u + α * v))

@[simp]
theorem correctedResponse_zero_focal (ρ α v : ℝ) :
    correctedResponse ρ α 0 v = 0 := by
  simp [correctedResponse]

theorem correctedResponse_denominator_pos
    {ρ α u v : ℝ} (hα : 0 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < 1 + max ρ 0 * (u + α * v) := by
  have hb : 0 ≤ max ρ 0 := le_max_right ρ 0
  have hq : 0 ≤ u + α * v := by positivity
  nlinarith [mul_nonneg hb hq]

/-- The corrected response is globally nonnegative on the positive cone. -/
theorem correctedResponse_nonneg
    {ρ α u v : ℝ} (hρ : -1 < ρ)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ correctedResponse ρ α u v := by
  unfold correctedResponse
  exact div_nonneg (mul_nonneg (by linarith) hu)
    (correctedResponse_denominator_pos hα hu hv).le

/-- On the favorable side, the correction is exactly the response printed in
the proposal. -/
theorem correctedResponse_eq_localResponse_of_nonneg
    {ρ α u v : ℝ} (hρ : 0 ≤ ρ) :
    correctedResponse ρ α u v = localResponse ρ α u v := by
  simp [correctedResponse, localResponse, max_eq_left hρ]

/-- On the unfavorable side, the response is subcritical linear growth. -/
theorem correctedResponse_eq_linear_of_nonpos
    {ρ α u v : ℝ} (hρ : ρ ≤ 0) :
    correctedResponse ρ α u v = (1 + ρ) * u := by
  simp [correctedResponse, max_eq_right hρ]

/-- The corrected nonlinear map is bounded by its low-density linearization
throughout the habitat. -/
theorem correctedResponse_le_linear
    {ρ α u v : ℝ} (hρ : -1 < ρ)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    correctedResponse ρ α u v ≤ (1 + ρ) * u := by
  let b := max ρ 0
  let q := u + α * v
  have hb : 0 ≤ b := le_max_right ρ 0
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hden : 0 < 1 + b * q := by
    nlinarith [mul_nonneg hb hq]
  have hnum : 0 ≤ (1 + ρ) * u :=
    mul_nonneg (by linarith) hu
  have hgain : 0 ≤ ((1 + ρ) * u) * (b * q) :=
    mul_nonneg hnum (mul_nonneg hb hq)
  change ((1 + ρ) * u) / (1 + b * q) ≤ (1 + ρ) * u
  apply (div_le_iff₀ hden).2
  nlinarith

/-- If the focal density starts in `[0,1]`, one corrected local step stays at
most one, with no simplex restriction on the competitor. -/
theorem correctedResponse_le_one
    {ρ α u v : ℝ} (_hρ : -1 < ρ)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) :
    correctedResponse ρ α u v ≤ 1 := by
  by_cases hρ0 : 0 ≤ ρ
  · rw [correctedResponse_eq_localResponse_of_nonneg hρ0]
    have hden : 0 < 1 + ρ * (u + α * v) := by positivity
    have hdiff :
        0 ≤ (1 + ρ * (u + α * v)) - (1 + ρ) * u := by
      rw [show
          (1 + ρ * (u + α * v)) - (1 + ρ) * u =
            (1 - u) + ρ * (α * v) by ring]
      positivity
    unfold localResponse
    apply (div_le_iff₀ hden).2
    nlinarith
  · have hρnonpos : ρ ≤ 0 := le_of_not_ge hρ0
    rw [correctedResponse_eq_linear_of_nonpos hρnonpos]
    calc
      (1 + ρ) * u ≤ 1 * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu
      _ = u := one_mul u
      _ ≤ 1 := hu1

/-- Increasing the competitor decreases the corrected response everywhere. -/
theorem correctedResponse_antitone_competitor
    {ρ α u v₁ v₂ : ℝ} (hρ : -1 < ρ)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hv₁ : 0 ≤ v₁) (hv₁₂ : v₁ ≤ v₂) :
    correctedResponse ρ α u v₂ ≤ correctedResponse ρ α u v₁ := by
  have hv₂ : 0 ≤ v₂ := hv₁.trans hv₁₂
  have hden₁ :=
    correctedResponse_denominator_pos (ρ := ρ) hα hu hv₁
  have hden₂ :=
    correctedResponse_denominator_pos (ρ := ρ) hα hu hv₂
  have hdenle :
      1 + max ρ 0 * (u + α * v₁) ≤
        1 + max ρ 0 * (u + α * v₂) := by
    gcongr
  have hnum : 0 ≤ (1 + ρ) * u :=
    mul_nonneg (by linarith) hu
  unfold correctedResponse
  apply (div_le_div_iff₀ hden₂ hden₁).2
  exact mul_le_mul_of_nonneg_left hdenle hnum

/-- Increasing the focal density increases the corrected response. -/
theorem correctedResponse_monotone_focal
    {ρ α u₁ u₂ v : ℝ} (hρ : -1 < ρ)
    (hα : 0 ≤ α) (hu₁ : 0 ≤ u₁) (hu₁₂ : u₁ ≤ u₂) (hv : 0 ≤ v) :
    correctedResponse ρ α u₁ v ≤ correctedResponse ρ α u₂ v := by
  have hu₂ : 0 ≤ u₂ := hu₁.trans hu₁₂
  have hden₁ :=
    correctedResponse_denominator_pos (ρ := ρ) hα hu₁ hv
  have hden₂ :=
    correctedResponse_denominator_pos (ρ := ρ) hα hu₂ hv
  have hb : 0 ≤ max ρ 0 := le_max_right ρ 0
  have hαv : 0 ≤ α * v := mul_nonneg hα hv
  have hcore :
      u₁ * (1 + max ρ 0 * (u₂ + α * v)) ≤
        u₂ * (1 + max ρ 0 * (u₁ + α * v)) := by
    have hid :
        u₂ * (1 + max ρ 0 * (u₁ + α * v)) -
            u₁ * (1 + max ρ 0 * (u₂ + α * v)) =
          (u₂ - u₁) * (1 + max ρ 0 * (α * v)) := by ring
    have hnonneg :
        0 ≤ (u₂ - u₁) * (1 + max ρ 0 * (α * v)) := by
      positivity
    linarith
  have hmult :
      ((1 + ρ) * u₁) *
          (1 + max ρ 0 * (u₂ + α * v)) ≤
        ((1 + ρ) * u₂) *
          (1 + max ρ 0 * (u₁ + α * v)) := by
    calc
      ((1 + ρ) * u₁) *
          (1 + max ρ 0 * (u₂ + α * v)) =
        (1 + ρ) *
          (u₁ * (1 + max ρ 0 * (u₂ + α * v))) := by ring
      _ ≤ (1 + ρ) *
          (u₂ * (1 + max ρ 0 * (u₁ + α * v))) :=
        mul_le_mul_of_nonneg_left hcore (by linarith)
      _ = ((1 + ρ) * u₂) *
          (1 + max ρ 0 * (u₁ + α * v)) := by ring
  unfold correctedResponse
  exact (div_le_div_iff₀ hden₁ hden₂).2 hmult

/-- Continuous environmental and population profiles give a continuous
corrected local response as soon as the denominator is kept positive by the
positive-cone hypotheses. -/
theorem correctedResponse_comp_continuous
    {ρ u v : ℝ → ℝ} {α : ℝ}
    (hρcont : Continuous ρ) (hucont : Continuous u) (hvcont : Continuous v)
    (hα : 0 ≤ α) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    Continuous (fun x => correctedResponse (ρ x) α (u x) (v x)) := by
  have hnum : Continuous (fun x => (1 + ρ x) * u x) :=
    (continuous_const.add hρcont).mul hucont
  have hmax : Continuous (fun x => max (ρ x) 0) :=
    hρcont.max continuous_const
  have hsum : Continuous (fun x => u x + α * v x) :=
    hucont.add (continuous_const.mul hvcont)
  have hden :
      Continuous (fun x => 1 + max (ρ x) 0 * (u x + α * v x)) :=
    continuous_const.add (hmax.mul hsum)
  unfold correctedResponse
  exact hnum.div hden
    (fun x => ne_of_gt (correctedResponse_denominator_pos hα (hu x) (hv x)))

/-- In the favorable constant environment, the correction preserves every
point on the proposed zero-growth nullcline. -/
theorem correctedResponse_eq_self_of_nullcline
    {ρ α u v : ℝ} (hρ : 0 ≤ ρ) (hnull : u + α * v = 1) :
    correctedResponse ρ α u v = u := by
  rw [correctedResponse_eq_localResponse_of_nonneg hρ]
  exact localResponse_eq_self_of_nullcline (by linarith) hnull

/-- The first component of the proposed weak-competition coexistence state is
fixed by the corrected favorable response. -/
theorem corrected_coexistenceU_fixed
    {ρ α₁ α₂ : ℝ} (hρ : 0 ≤ ρ) (hden : α₁ * α₂ ≠ 1) :
    correctedResponse ρ α₁
        (coexistenceU α₁ α₂) (coexistenceV α₁ α₂) =
      coexistenceU α₁ α₂ := by
  apply correctedResponse_eq_self_of_nullcline hρ
  exact coexistence_first_nullcline hden

/-- The second component of the proposed weak-competition coexistence state is
fixed by the corrected favorable response. -/
theorem corrected_coexistenceV_fixed
    {ρ α₁ α₂ : ℝ} (hρ : 0 ≤ ρ) (hden : α₁ * α₂ ≠ 1) :
    correctedResponse ρ α₂
        (coexistenceV α₁ α₂) (coexistenceU α₁ α₂) =
      coexistenceV α₁ α₂ := by
  apply correctedResponse_eq_self_of_nullcline hρ
  exact coexistence_second_nullcline hden

/-! ## Invasion multipliers at the semi-trivial equilibria -/

/-- Low-density multiplier of a rare focal species when the resident
competitor has favorable equilibrium density one. -/
def rareSpeciesMultiplier (ρ α : ℝ) : ℝ :=
  (1 + ρ) / (1 + ρ * α)

theorem rareSpeciesMultiplier_pos
    {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 ≤ α) :
    0 < rareSpeciesMultiplier ρ α := by
  unfold rareSpeciesMultiplier
  positivity

/-- Under weak competition, a rare species can increase in the favorable
homogeneous environment. -/
theorem one_lt_rareSpeciesMultiplier_of_weak_competition
    {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 ≤ α) (hα1 : α < 1) :
    1 < rareSpeciesMultiplier ρ α := by
  have hden : 0 < 1 + ρ * α := by positivity
  unfold rareSpeciesMultiplier
  apply (lt_div_iff₀ hden).2
  have hmul : ρ * α < ρ * 1 :=
    mul_lt_mul_of_pos_left hα1 hρ
  nlinarith

/-- Under strong competition, a rare species decreases at the resident-only
equilibrium.  Thus empty-habitat speed ordering alone cannot decide which
resident wins. -/
theorem rareSpeciesMultiplier_lt_one_of_strong_competition
    {ρ α : ℝ} (hρ : 0 < ρ) (hα1 : 1 < α) :
    rareSpeciesMultiplier ρ α < 1 := by
  have hden : 0 < 1 + ρ * α := by positivity
  unfold rareSpeciesMultiplier
  apply (div_lt_iff₀ hden).2
  have hmul : ρ * 1 < ρ * α :=
    mul_lt_mul_of_pos_left hα1 hρ
  nlinarith

section AxiomAudit

#print axioms correctedResponse_nonneg
#print axioms correctedResponse_le_one
#print axioms correctedResponse_antitone_competitor
#print axioms correctedResponse_monotone_focal
#print axioms correctedResponse_comp_continuous
#print axioms corrected_coexistenceU_fixed
#print axioms one_lt_rareSpeciesMultiplier_of_weak_competition
#print axioms rareSpeciesMultiplier_lt_one_of_strong_competition

end AxiomAudit

end

end ShenWork.Liang
