/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.IDEComparison
import ShenWork.Paper1.WaveRotheTrap

/-!
# Bounded-continuous state space for the corrected IDE

This file makes the reuse of ShenWork concrete.  The local corrected response
is packaged as a bounded continuous function, and the next-generation profile
is constructed with ShenWork's existing `greenConvBCF` convolution engine.
The probability-kernel estimate then proves that the two-component unit square
is invariant under every generation.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

namespace ShenWork.Liang

noncomputable section

/-- Analytic data needed to define one corrected two-species IDE step. -/
structure CorrectedIDEData where
  kernel₁ : ℝ → ℝ
  kernel₂ : ℝ → ℝ
  environment₁ : ℝ → ℝ
  environment₂ : ℝ → ℝ
  competition₁ : ℝ
  competition₂ : ℝ
  habitatSpeed : ℝ
  kernel₁_continuous : Continuous kernel₁
  kernel₂_continuous : Continuous kernel₂
  kernel₁_integrable : Integrable kernel₁
  kernel₂_integrable : Integrable kernel₂
  kernel₁_nonnegative : ∀ x, 0 ≤ kernel₁ x
  kernel₂_nonnegative : ∀ x, 0 ≤ kernel₂ x
  kernel₁_mass : ∫ x, kernel₁ x = 1
  kernel₂_mass : ∫ x, kernel₂ x = 1
  environment₁_continuous : Continuous environment₁
  environment₂_continuous : Continuous environment₂
  environment₁_gt_neg_one : ∀ x, -1 < environment₁ x
  environment₂_gt_neg_one : ∀ x, -1 < environment₂ x
  competition₁_nonnegative : 0 ≤ competition₁
  competition₂_nonnegative : 0 ≤ competition₂

/-- A pair of bounded continuous profiles taking values in the unit square. -/
structure UnitIDEState where
  u : ℝ →ᵇ ℝ
  v : ℝ →ᵇ ℝ
  u_nonnegative : ∀ x, 0 ≤ u x
  u_le_one : ∀ x, u x ≤ 1
  v_nonnegative : ∀ x, 0 ≤ v x
  v_le_one : ∀ x, v x ≤ 1

/-- The standard competitive product order: the first component is ordered
normally and the second component in reverse. -/
def CompetitivelyLE (s t : UnitIDEState) : Prop :=
  (∀ x, s.u x ≤ t.u x) ∧ (∀ x, t.v x ≤ s.v x)

/-- The corrected local source as a genuine bounded continuous function. -/
def correctedSourceBCF
    (ρ : ℝ → ℝ) (hρcont : Continuous ρ) (hρlow : ∀ x, -1 < ρ x)
    (α : ℝ) (hα : 0 ≤ α) (c : ℝ) (n : ℕ)
    (u v : ℝ →ᵇ ℝ)
    (hu : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1)
    (hv : ∀ x, 0 ≤ v x) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y =>
      correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y))
    (correctedResponse_comp_continuous
      (hρcont.comp (continuous_id.sub continuous_const))
      u.continuous v.continuous hα hu hv)
    1
    (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (correctedResponse_nonneg (hρlow _) hα (hu y) (hv y))]
      exact correctedResponse_le_one
        (hρlow _) hα (hu y) (hu1 y) (hv y))

@[simp]
theorem correctedSourceBCF_apply
    (ρ : ℝ → ℝ) (hρcont : Continuous ρ) (hρlow : ∀ x, -1 < ρ x)
    (α : ℝ) (hα : 0 ≤ α) (c : ℝ) (n : ℕ)
    (u v : ℝ →ᵇ ℝ)
    (hu : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1)
    (hv : ∀ x, 0 ≤ v x) (y : ℝ) :
    correctedSourceBCF ρ hρcont hρlow α hα c n u v hu hu1 hv y =
      correctedResponse (ρ (y - c * (n : ℝ))) α (u y) (v y) :=
  rfl

/-- One corrected component step, constructed directly by ShenWork's
bounded-continuous convolution engine. -/
def correctedStepBCF
    (K ρ : ℝ → ℝ)
    (hKcont : Continuous K) (hKint : Integrable K)
    (hρcont : Continuous ρ) (hρlow : ∀ x, -1 < ρ x)
    (α : ℝ) (hα : 0 ≤ α) (c : ℝ) (n : ℕ)
    (u v : ℝ →ᵇ ℝ)
    (hu : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1)
    (hv : ∀ x, 0 ≤ v x) : ℝ →ᵇ ℝ :=
  ShenWork.Paper1.greenConvBCF hKcont hKint
    (correctedSourceBCF ρ hρcont hρlow α hα c n u v hu hu1 hv)

@[simp]
theorem correctedStepBCF_apply
    (K ρ : ℝ → ℝ)
    (hKcont : Continuous K) (hKint : Integrable K)
    (hρcont : Continuous ρ) (hρlow : ∀ x, -1 < ρ x)
    (α : ℝ) (hα : 0 ≤ α) (c : ℝ) (n : ℕ)
    (u v : ℝ →ᵇ ℝ)
    (hu : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1)
    (hv : ∀ x, 0 ≤ v x) (x : ℝ) :
    correctedStepBCF K ρ hKcont hKint hρcont hρlow
        α hα c n u v hu hu1 hv x =
      heterogeneousCorrectedStep K ρ α c n
        (fun y => u y) (fun y => v y) x :=
  rfl

/-- ShenWork's existing bounded-continuous convolution construction, combined
with the corrected local bounds, keeps one component in `[0,1]`. -/
theorem correctedStepBCF_mem_unitInterval
    (K ρ : ℝ → ℝ)
    (hKcont : Continuous K) (hKint : Integrable K)
    (hK : ∀ x, 0 ≤ K x) (hKmass : ∫ x, K x = 1)
    (hρcont : Continuous ρ) (hρlow : ∀ x, -1 < ρ x)
    (α : ℝ) (hα : 0 ≤ α) (c : ℝ) (n : ℕ)
    (u v : ℝ →ᵇ ℝ)
    (hu : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1)
    (hv : ∀ x, 0 ≤ v x) (x : ℝ) :
    correctedStepBCF K ρ hKcont hKint hρcont hρlow
        α hα c n u v hu hu1 hv x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [correctedStepBCF_apply]
  apply heterogeneousCorrectedStep_mem_unitInterval
    hKint hK hKmass hρlow hα hu hu1 hv
  simpa only [correctedSourceBCF_apply] using
    ShenWork.Paper1.kernelConv_integrand_integrable
      hKcont hKint
      (correctedSourceBCF ρ hρcont hρlow α hα c n u v hu hu1 hv) x

/-- First next-generation profile. -/
def nextU (p : CorrectedIDEData) (n : ℕ) (s : UnitIDEState) : ℝ →ᵇ ℝ :=
  correctedStepBCF
    p.kernel₁ p.environment₁
    p.kernel₁_continuous p.kernel₁_integrable
    p.environment₁_continuous p.environment₁_gt_neg_one
    p.competition₁ p.competition₁_nonnegative p.habitatSpeed n
    s.u s.v s.u_nonnegative s.u_le_one s.v_nonnegative

/-- Second next-generation profile. -/
def nextV (p : CorrectedIDEData) (n : ℕ) (s : UnitIDEState) : ℝ →ᵇ ℝ :=
  correctedStepBCF
    p.kernel₂ p.environment₂
    p.kernel₂_continuous p.kernel₂_integrable
    p.environment₂_continuous p.environment₂_gt_neg_one
    p.competition₂ p.competition₂_nonnegative p.habitatSpeed n
    s.v s.u s.v_nonnegative s.v_le_one s.u_nonnegative

theorem nextU_mem_unitInterval
    (p : CorrectedIDEData) (n : ℕ) (s : UnitIDEState) (x : ℝ) :
    nextU p n s x ∈ Set.Icc (0 : ℝ) 1 :=
  correctedStepBCF_mem_unitInterval
    p.kernel₁ p.environment₁
    p.kernel₁_continuous p.kernel₁_integrable
    p.kernel₁_nonnegative p.kernel₁_mass
    p.environment₁_continuous p.environment₁_gt_neg_one
    p.competition₁ p.competition₁_nonnegative p.habitatSpeed n
    s.u s.v s.u_nonnegative s.u_le_one s.v_nonnegative x

theorem nextV_mem_unitInterval
    (p : CorrectedIDEData) (n : ℕ) (s : UnitIDEState) (x : ℝ) :
    nextV p n s x ∈ Set.Icc (0 : ℝ) 1 :=
  correctedStepBCF_mem_unitInterval
    p.kernel₂ p.environment₂
    p.kernel₂_continuous p.kernel₂_integrable
    p.kernel₂_nonnegative p.kernel₂_mass
    p.environment₂_continuous p.environment₂_gt_neg_one
    p.competition₂ p.competition₂_nonnegative p.habitatSpeed n
    s.v s.u s.v_nonnegative s.v_le_one s.u_nonnegative x

/-- The first component respects the competitive product order. -/
theorem nextU_competitive_mono
    (p : CorrectedIDEData) (n : ℕ) {s t : UnitIDEState}
    (hst : CompetitivelyLE s t) (x : ℝ) :
    nextU p n s x ≤ nextU p n t x := by
  simp only [nextU, correctedStepBCF_apply]
  apply heterogeneousCorrectedStep_competitive_mono
    p.kernel₁_nonnegative p.environment₁_gt_neg_one
    p.competition₁_nonnegative
    s.u_nonnegative t.v_nonnegative hst.1 hst.2
  · exact heterogeneousCorrectedIntegrable
      p.kernel₁_integrable p.kernel₁_continuous
      p.environment₁_continuous p.environment₁_gt_neg_one
      p.competition₁_nonnegative
      s.u.continuous s.u_nonnegative s.u_le_one
      s.v.continuous s.v_nonnegative
  · exact heterogeneousCorrectedIntegrable
      p.kernel₁_integrable p.kernel₁_continuous
      p.environment₁_continuous p.environment₁_gt_neg_one
      p.competition₁_nonnegative
      t.u.continuous t.u_nonnegative t.u_le_one
      t.v.continuous t.v_nonnegative

/-- The second component respects the reversed half of the competitive
product order. -/
theorem nextV_competitive_mono
    (p : CorrectedIDEData) (n : ℕ) {s t : UnitIDEState}
    (hst : CompetitivelyLE s t) (x : ℝ) :
    nextV p n t x ≤ nextV p n s x := by
  simp only [nextV, correctedStepBCF_apply]
  apply heterogeneousCorrectedStep_competitive_mono
    p.kernel₂_nonnegative p.environment₂_gt_neg_one
    p.competition₂_nonnegative
    t.v_nonnegative s.u_nonnegative hst.2 hst.1
  · exact heterogeneousCorrectedIntegrable
      p.kernel₂_integrable p.kernel₂_continuous
      p.environment₂_continuous p.environment₂_gt_neg_one
      p.competition₂_nonnegative
      t.v.continuous t.v_nonnegative t.v_le_one
      t.u.continuous t.u_nonnegative
  · exact heterogeneousCorrectedIntegrable
      p.kernel₂_integrable p.kernel₂_continuous
      p.environment₂_continuous p.environment₂_gt_neg_one
      p.competition₂_nonnegative
      s.v.continuous s.v_nonnegative s.v_le_one
      s.u.continuous s.u_nonnegative

/-- The corrected two-species IDE is a self-map of bounded continuous
unit-square states at every generation. -/
def correctedIDEStateStep
    (p : CorrectedIDEData) (n : ℕ) (s : UnitIDEState) : UnitIDEState where
  u := nextU p n s
  v := nextV p n s
  u_nonnegative := fun x => (nextU_mem_unitInterval p n s x).1
  u_le_one := fun x => (nextU_mem_unitInterval p n s x).2
  v_nonnegative := fun x => (nextV_mem_unitInterval p n s x).1
  v_le_one := fun x => (nextV_mem_unitInterval p n s x).2

/-- An absent second species remains identically absent after one state step. -/
theorem nextV_eq_zero_of_v_eq_zero
    (p : CorrectedIDEData) (n : ℕ) (s : UnitIDEState)
    (hv : s.v = 0) :
    nextV p n s = 0 := by
  apply BoundedContinuousFunction.ext
  intro x
  simp only [nextV, correctedStepBCF_apply]
  have hvx : ∀ y, s.v y = 0 := fun y => by
    simpa using congrArg (fun f : ℝ →ᵇ ℝ => f y) hv
  simpa only [hvx] using
    heterogeneousCorrectedStep_zero_focal
      p.kernel₂ p.environment₂ (fun y => s.u y)
      p.competition₂ p.habitatSpeed x n

/-- The nonautonomous corrected IDE orbit, with generation `n` using the
environment shifted by `c n`. -/
def correctedIDEOrbit
    (p : CorrectedIDEData) (s₀ : UnitIDEState) : ℕ → UnitIDEState
  | 0 => s₀
  | n + 1 => correctedIDEStateStep p n (correctedIDEOrbit p s₀ n)

@[simp]
theorem correctedIDEOrbit_zero
    (p : CorrectedIDEData) (s₀ : UnitIDEState) :
    correctedIDEOrbit p s₀ 0 = s₀ :=
  rfl

@[simp]
theorem correctedIDEOrbit_succ
    (p : CorrectedIDEData) (s₀ : UnitIDEState) (n : ℕ) :
    correctedIDEOrbit p s₀ (n + 1) =
      correctedIDEStateStep p n (correctedIDEOrbit p s₀ n) :=
  rfl

/-- Therefore any theorem claiming persistence of species two must assume
that species two is initially nonzero. -/
theorem correctedIDEOrbit_v_eq_zero
    (p : CorrectedIDEData) (s₀ : UnitIDEState) (hv : s₀.v = 0) :
    ∀ n, (correctedIDEOrbit p s₀ n).v = 0 := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
      change nextV p n (correctedIDEOrbit p s₀ n) = 0
      exact nextV_eq_zero_of_v_eq_zero p n _ ih

/-- Every generation preserves the competitive product order. -/
theorem correctedIDEStateStep_competitive_mono
    (p : CorrectedIDEData) (n : ℕ) {s t : UnitIDEState}
    (hst : CompetitivelyLE s t) :
    CompetitivelyLE
      (correctedIDEStateStep p n s) (correctedIDEStateStep p n t) := by
  constructor
  · exact nextU_competitive_mono p n hst
  · exact nextV_competitive_mono p n hst

section AxiomAudit

#print axioms correctedStepBCF_mem_unitInterval
#print axioms nextU_mem_unitInterval
#print axioms nextV_mem_unitInterval
#print axioms correctedIDEStateStep
#print axioms correctedIDEOrbit_v_eq_zero
#print axioms correctedIDEStateStep_competitive_mono

end AxiomAudit

end

end ShenWork.Liang
