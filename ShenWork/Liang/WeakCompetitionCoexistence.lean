/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.GlobalDynamicsTools
import ShenWork.Liang.LinearDeterminacy
import ShenWork.Liang.MovingCorridor
import ShenWork.Liang.SeededEnvelope
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Weak-competition coexistence for the corrected model

This file isolates the finite-dimensional squeezing argument behind a
corrected version of Theorem 2.3.  There are two logically separate inputs:

* the homogeneous favorable response has a unique positive weak-competition
  equilibrium;
* a spatial corridor argument must eventually trap the two species between
  homogeneous lower and upper envelopes.

The first input, including convergence of the canonical coupled envelope
iteration, is proved here.  The final section packages the exact comparison
interface needed from the spatial spreading argument.  In particular, the
spatial persistence estimate is not hidden inside the conclusion.
-/

open Filter Set Topology

namespace ShenWork.Liang

noncomputable section

/-! ## Growth inequalities and nullclines -/

/-- The corrected favorable response is strictly positive at positive focal
density. -/
theorem correctedResponse_pos
    {ρ α u v : ℝ} (hρ : -1 < ρ) (hu : 0 < u)
    (hα : 0 ≤ α) (hv : 0 ≤ v) :
    0 < correctedResponse ρ α u v := by
  unfold correctedResponse
  exact div_pos (mul_pos (by linarith) hu)
    (correctedResponse_denominator_pos hα hu.le hv)

/-! ## The algebraic endpoint of the squeezing argument -/

/-- Two weak-competition nullclines have only the stated coexistence
intersection. -/
theorem eq_coexistence_of_nullclines
    {α₁ α₂ u v : ℝ}
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (_hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1)
    (hnull₁ : u + α₁ * v = 1)
    (hnull₂ : v + α₂ * u = 1) :
    u = coexistenceU α₁ α₂ ∧ v = coexistenceV α₁ α₂ := by
  have hprod : α₁ * α₂ < 1 := by
    by_cases hα₁ : α₁ = 0
    · simp [hα₁]
    · have hα₁pos : 0 < α₁ := lt_of_le_of_ne hα₁0 (Ne.symm hα₁)
      calc
        α₁ * α₂ < α₁ * 1 := mul_lt_mul_of_pos_left hα₂1 hα₁pos
        _ = α₁ := mul_one α₁
        _ < 1 := hα₁1
  have hden : 1 - α₁ * α₂ ≠ 0 := by linarith
  have hu :
      u * (1 - α₁ * α₂) = 1 - α₁ := by
    linear_combination hnull₁ - α₁ * hnull₂
  have hv :
      v * (1 - α₁ * α₂) = 1 - α₂ := by
    linear_combination hnull₂ - α₂ * hnull₁
  constructor
  · unfold coexistenceU
    exact (eq_div_iff hden).2 hu
  · unfold coexistenceV
    exact (eq_div_iff hden).2 hv

/-- Four limiting envelope values collapse to the unique coexistence
equilibrium.  These are precisely the inequalities produced by a competitive
liminf/limsup squeezing argument. -/
theorem weak_competition_envelope_collapse
    {α₁ α₂ uLower uUpper vLower vUpper : ℝ}
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1)
    (huOrder : uLower ≤ uUpper) (hvOrder : vLower ≤ vUpper)
    (huUpper : uUpper + α₁ * vLower ≤ 1)
    (huLower : 1 ≤ uLower + α₁ * vUpper)
    (hvUpper : vUpper + α₂ * uLower ≤ 1)
    (hvLower : 1 ≤ vLower + α₂ * uUpper) :
    uLower = coexistenceU α₁ α₂ ∧
      uUpper = coexistenceU α₁ α₂ ∧
      vLower = coexistenceV α₁ α₂ ∧
      vUpper = coexistenceV α₁ α₂ := by
  have hdu0 : 0 ≤ uUpper - uLower := sub_nonneg.mpr huOrder
  have hdv0 : 0 ≤ vUpper - vLower := sub_nonneg.mpr hvOrder
  have hdu : uUpper - uLower ≤ α₁ * (vUpper - vLower) := by
    linarith
  have hdv : vUpper - vLower ≤ α₂ * (uUpper - uLower) := by
    linarith
  have hprod : α₁ * α₂ < 1 := by
    by_cases hα₁ : α₁ = 0
    · simp [hα₁]
    · have hα₁pos : 0 < α₁ := lt_of_le_of_ne hα₁0 (Ne.symm hα₁)
      calc
        α₁ * α₂ < α₁ * 1 := mul_lt_mul_of_pos_left hα₂1 hα₁pos
        _ = α₁ := mul_one α₁
        _ < 1 := hα₁1
  have hdu' :
      uUpper - uLower ≤ (α₁ * α₂) * (uUpper - uLower) := by
    calc
      uUpper - uLower ≤ α₁ * (vUpper - vLower) := hdu
      _ ≤ α₁ * (α₂ * (uUpper - uLower)) :=
        mul_le_mul_of_nonneg_left hdv hα₁0
      _ = (α₁ * α₂) * (uUpper - uLower) := by ring
  have hduZero : uUpper - uLower = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hprod.le) hdu0]
  have huEq : uUpper = uLower := by linarith
  have hdvZero : vUpper - vLower = 0 := by
    have : vUpper - vLower ≤ 0 := by simpa [hduZero] using hdv
    linarith
  have hvEq : vUpper = vLower := by linarith
  have hnull₁ : uLower + α₁ * vLower = 1 := by
    simp only [huEq, hvEq] at huUpper huLower
    exact le_antisymm huUpper huLower
  have hnull₂ : vLower + α₂ * uLower = 1 := by
    simp only [huEq, hvEq] at hvUpper hvLower
    exact le_antisymm hvUpper hvLower
  obtain ⟨huStar, hvStar⟩ :=
    eq_coexistence_of_nullclines
      hα₁0 hα₁1 hα₂0 hα₂1 hnull₁ hnull₂
  exact ⟨huStar, huEq.trans huStar, hvStar, hvEq.trans hvStar⟩

/-- Response inequalities at positive envelope values imply the four linear
nullcline inequalities needed by `weak_competition_envelope_collapse`. -/
theorem weak_competition_response_envelope_collapse
    {ρ₁ ρ₂ α₁ α₂ uLower uUpper vLower vUpper : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1)
    (huLowerPos : 0 < uLower) (huOrder : uLower ≤ uUpper)
    (hvLowerPos : 0 < vLower) (hvOrder : vLower ≤ vUpper)
    (huUpperStep :
      uUpper ≤ correctedResponse ρ₁ α₁ uUpper vLower)
    (huLowerStep :
      correctedResponse ρ₁ α₁ uLower vUpper ≤ uLower)
    (hvUpperStep :
      vUpper ≤ correctedResponse ρ₂ α₂ vUpper uLower)
    (hvLowerStep :
      correctedResponse ρ₂ α₂ vLower uUpper ≤ vLower) :
    uLower = coexistenceU α₁ α₂ ∧
      uUpper = coexistenceU α₁ α₂ ∧
      vLower = coexistenceV α₁ α₂ ∧
      vUpper = coexistenceV α₁ α₂ := by
  have huUpperPos : 0 < uUpper := huLowerPos.trans_le huOrder
  have hvUpperPos : 0 < vUpper := hvLowerPos.trans_le hvOrder
  apply weak_competition_envelope_collapse
      hα₁0 hα₁1 hα₂0 hα₂1 huOrder hvOrder
  · exact (self_le_correctedResponse_iff
      hρ₁ hα₁0 huUpperPos hvLowerPos.le).1 huUpperStep
  · exact (correctedResponse_le_self_iff
      hρ₁ hα₁0 huLowerPos hvUpperPos.le).1 huLowerStep
  · exact (self_le_correctedResponse_iff
      hρ₂ hα₂0 hvUpperPos huLowerPos.le).1 hvUpperStep
  · exact (correctedResponse_le_self_iff
      hρ₂ hα₂0 hvLowerPos huUpperPos.le).1 hvLowerStep

/-! ## Quantitative rare-species lower growth -/

/-- A uniform lower multiplier valid while the focal species is at most
`δ` and the resident competitor is at most one. -/
def invasionLowerMultiplier (ρ α δ : ℝ) : ℝ :=
  (1 + ρ) / (1 + ρ * (α + δ))

/-- At zero focal cutoff, the quantitative lower multiplier is exactly the
rare-species multiplier used in the reduced spreading speed. -/
@[simp]
theorem invasionLowerMultiplier_zero (ρ α : ℝ) :
    invasionLowerMultiplier ρ α 0 = rareSpeciesMultiplier ρ α := by
  simp [invasionLowerMultiplier, rareSpeciesMultiplier]

/-- A positive weak-competition margin leaves a genuinely supercritical
lower multiplier. -/
theorem one_lt_invasionLowerMultiplier
    {ρ α δ : ℝ} (hρ : 0 < ρ) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) (hmargin : α + δ < 1) :
    1 < invasionLowerMultiplier ρ α δ := by
  have hden : 0 < 1 + ρ * (α + δ) := by positivity
  unfold invasionLowerMultiplier
  apply (lt_div_iff₀ hden).2
  nlinarith [mul_lt_mul_of_pos_left hmargin hρ]

/-- In the favorable homogeneous environment, the corrected nonlinear
response dominates the quantitative rare-species linearization whenever
`u ≤ δ` and the resident density is at most one. -/
theorem invasionLowerMultiplier_mul_le_correctedResponse
    {ρ α δ u v : ℝ} (hρ : 0 < ρ) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) (hu : 0 ≤ u) (huδ : u ≤ δ)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    invasionLowerMultiplier ρ α δ * u ≤
      correctedResponse ρ α u v := by
  rw [correctedResponse_eq_localResponse_of_nonneg hρ.le]
  have hdenActual : 0 < 1 + ρ * (u + α * v) := by positivity
  have hdenBound : 0 < 1 + ρ * (α + δ) := by positivity
  have hsum : u + α * v ≤ α + δ := by
    nlinarith [mul_le_mul_of_nonneg_left hv1 hα]
  have hden :
      1 + ρ * (u + α * v) ≤ 1 + ρ * (α + δ) := by
    nlinarith [mul_le_mul_of_nonneg_left hsum hρ.le]
  have hnum : 0 ≤ (1 + ρ) * u := by positivity
  unfold invasionLowerMultiplier localResponse
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff₀ hdenBound hdenActual).2
    (mul_le_mul_of_nonneg_left hden hnum)

/-- An exponential weight at which the rare-species linearization is
analytically meaningful.  Finiteness of the weighted kernel and positivity
of the full linear multiplier are part of the speed domain, rather than
silently being inferred from the unweighted kernel assumptions. -/
structure InvasionWeight (K : ℝ → ℝ) (ρ α : ℝ) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  weightedKernel_integrable :
    MeasureTheory.Integrable
      (fun z => K z * Real.exp (exponent * z))
  linearMultiplier_pos :
    0 <
      rareSpeciesMultiplier ρ α *
        ShenWork.Analysis.kernelMoment K exponent

/-- The reduced critical speed is taken only over admissible invasion
weights.  Its growth multiplier is the rare-species multiplier, not the
empty-habitat multiplier. -/
def reducedCriticalSpeed (K : ℝ → ℝ) (ρ α : ℝ) : ℝ :=
  ⨅ η : InvasionWeight K ρ α,
    kernelSpeedAt K (rareSpeciesMultiplier ρ α) η.exponent

/-- The corrected two-species coexistence threshold is the smaller of the
two admissible rare-species speeds. -/
def coexistenceCriticalSpeed
    (K₁ K₂ : ℝ → ℝ) (ρ₁ ρ₂ α₁ α₂ : ℝ) : ℝ :=
  min (reducedCriticalSpeed K₁ ρ₁ α₁)
    (reducedCriticalSpeed K₂ ρ₂ α₂)

/-- The repaired observer range is strictly ahead of the habitat and
strictly behind the reduced coexistence speed. -/
theorem exists_interior_coexistence_frame
    {K₁ K₂ : ℝ → ℝ} {ρ₁ ρ₂ α₁ α₂ c : ℝ}
    (_hweights₁ : Nonempty (InvasionWeight K₁ ρ₁ α₁))
    (_hweights₂ : Nonempty (InvasionWeight K₂ ρ₂ α₂))
    (hc :
      c < coexistenceCriticalSpeed K₁ K₂ ρ₁ ρ₂ α₁ α₂) :
    ∃ s : ℝ,
      c < s ∧
        s < coexistenceCriticalSpeed K₁ K₂ ρ₁ ρ₂ α₁ α₂ := by
  refine ⟨(c +
    coexistenceCriticalSpeed K₁ K₂ ρ₁ ρ₂ α₁ α₂) / 2, ?_, ?_⟩
  · linarith
  · linarith

/-! ## Canonical homogeneous upper and lower envelopes -/

/-- A competitive rectangle, with lower and upper endpoints for both
species. -/
structure HomogeneousEnvelope where
  uLower : ℝ
  uUpper : ℝ
  vLower : ℝ
  vUpper : ℝ

/-- The rectangle is a positive subrectangle of the invariant unit square. -/
def HomogeneousEnvelope.Valid (e : HomogeneousEnvelope) : Prop :=
  0 < e.uLower ∧ e.uLower ≤ e.uUpper ∧ e.uUpper ≤ 1 ∧
    0 < e.vLower ∧ e.vLower ≤ e.vUpper ∧ e.vUpper ≤ 1

/-- `f` refines `e` when both lower endpoints increase and both upper
endpoints decrease. -/
def EnvelopeRefines (e f : HomogeneousEnvelope) : Prop :=
  e.uLower ≤ f.uLower ∧ f.uUpper ≤ e.uUpper ∧
    e.vLower ≤ f.vLower ∧ f.vUpper ≤ e.vUpper

/-- One coupled homogeneous envelope step.  Lower focal endpoints see upper
competitor endpoints, and upper focal endpoints see lower competitors. -/
def homogeneousEnvelopeStep
    (ρ₁ ρ₂ α₁ α₂ : ℝ) (e : HomogeneousEnvelope) :
    HomogeneousEnvelope where
  uLower := correctedResponse ρ₁ α₁ e.uLower e.vUpper
  uUpper := correctedResponse ρ₁ α₁ e.uUpper e.vLower
  vLower := correctedResponse ρ₂ α₂ e.vLower e.uUpper
  vUpper := correctedResponse ρ₂ α₂ e.vUpper e.uLower

/-- The canonical initial rectangle has upper endpoint one and a strictly
positive lower endpoint halfway between zero and each nullcline intercept. -/
def canonicalInitialEnvelope (α₁ α₂ : ℝ) : HomogeneousEnvelope where
  uLower := (1 - α₁) / 2
  uUpper := 1
  vLower := (1 - α₂) / 2
  vUpper := 1

theorem canonicalInitialEnvelope_valid
    {α₁ α₂ : ℝ}
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    (canonicalInitialEnvelope α₁ α₂).Valid := by
  unfold HomogeneousEnvelope.Valid canonicalInitialEnvelope
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · linarith
  · norm_num

/-- A valid envelope remains valid after one homogeneous weak-competition
step. -/
theorem homogeneousEnvelopeStep_valid
    {ρ₁ ρ₂ α₁ α₂ : ℝ} {e : HomogeneousEnvelope}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (he : e.Valid) :
    (homogeneousEnvelopeStep ρ₁ ρ₂ α₁ α₂ e).Valid := by
  rcases he with ⟨hlu, hluu, huu, hlv, hlvu, huv⟩
  have hlu0 : 0 ≤ e.uLower := hlu.le
  have huu0 : 0 ≤ e.uUpper := hlu0.trans hluu
  have hlv0 : 0 ≤ e.vLower := hlv.le
  have huv0 : 0 ≤ e.vUpper := hlv0.trans hlvu
  unfold HomogeneousEnvelope.Valid homogeneousEnvelopeStep
  constructor
  · exact correctedResponse_pos (by linarith) hlu hα₁ huv0
  constructor
  · calc
      correctedResponse ρ₁ α₁ e.uLower e.vUpper ≤
          correctedResponse ρ₁ α₁ e.uLower e.vLower :=
        correctedResponse_antitone_competitor
          (by linarith) hα₁ hlu0 hlv0 hlvu
      _ ≤ correctedResponse ρ₁ α₁ e.uUpper e.vLower :=
        correctedResponse_monotone_focal
          (by linarith) hα₁ hlu0 hluu hlv0
  constructor
  · exact correctedResponse_le_one
      (by linarith) hα₁ huu0 huu hlv0
  constructor
  · exact correctedResponse_pos (by linarith) hlv hα₂ huu0
  constructor
  · calc
      correctedResponse ρ₂ α₂ e.vLower e.uUpper ≤
          correctedResponse ρ₂ α₂ e.vLower e.uLower :=
        correctedResponse_antitone_competitor
          (by linarith) hα₂ hlv0 hlu0 hluu
      _ ≤ correctedResponse ρ₂ α₂ e.vUpper e.uLower :=
        correctedResponse_monotone_focal
          (by linarith) hα₂ hlv0 hlvu hlu0
  · exact correctedResponse_le_one
      (by linarith) hα₂ huv0 huv hlu0

/-- The homogeneous envelope step is monotone for rectangle refinement. -/
theorem homogeneousEnvelopeStep_refines_mono
    {ρ₁ ρ₂ α₁ α₂ : ℝ} {e f : HomogeneousEnvelope}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (he : e.Valid) (hf : f.Valid)
    (hef : EnvelopeRefines e f) :
    EnvelopeRefines
      (homogeneousEnvelopeStep ρ₁ ρ₂ α₁ α₂ e)
      (homogeneousEnvelopeStep ρ₁ ρ₂ α₁ α₂ f) := by
  rcases he with ⟨helu, heluu, _, helv, helvu, _⟩
  rcases hf with ⟨hflu, hfluu, _, hflv, hflvu, _⟩
  rcases hef with ⟨hlu, huu, hlv, huv⟩
  have helu0 := helu.le
  have helv0 := helv.le
  have hflu0 := hflu.le
  have hflv0 := hflv.le
  have heuu0 : 0 ≤ e.uUpper := helu0.trans heluu
  have hevu0 : 0 ≤ e.vUpper := helv0.trans helvu
  have hfuu0 : 0 ≤ f.uUpper := hflu0.trans hfluu
  have hfvu0 : 0 ≤ f.vUpper := hflv0.trans hflvu
  unfold EnvelopeRefines homogeneousEnvelopeStep
  constructor
  · calc
      correctedResponse ρ₁ α₁ e.uLower e.vUpper ≤
          correctedResponse ρ₁ α₁ e.uLower f.vUpper :=
        correctedResponse_antitone_competitor
          (by linarith) hα₁ helu0 hfvu0 huv
      _ ≤ correctedResponse ρ₁ α₁ f.uLower f.vUpper :=
        correctedResponse_monotone_focal
          (by linarith) hα₁ helu0 hlu hfvu0
  constructor
  · calc
      correctedResponse ρ₁ α₁ f.uUpper f.vLower ≤
          correctedResponse ρ₁ α₁ f.uUpper e.vLower :=
        correctedResponse_antitone_competitor
          (by linarith) hα₁ hfuu0 helv0 hlv
      _ ≤ correctedResponse ρ₁ α₁ e.uUpper e.vLower :=
        correctedResponse_monotone_focal
          (by linarith) hα₁ hfuu0 huu helv0
  constructor
  · calc
      correctedResponse ρ₂ α₂ e.vLower e.uUpper ≤
          correctedResponse ρ₂ α₂ e.vLower f.uUpper :=
        correctedResponse_antitone_competitor
          (by linarith) hα₂ helv0 hfuu0 huu
      _ ≤ correctedResponse ρ₂ α₂ f.vLower f.uUpper :=
        correctedResponse_monotone_focal
          (by linarith) hα₂ helv0 hlv hfuu0
  · calc
      correctedResponse ρ₂ α₂ f.vUpper f.uLower ≤
          correctedResponse ρ₂ α₂ f.vUpper e.uLower :=
        correctedResponse_antitone_competitor
          (by linarith) hα₂ hfvu0 helu0 hlu
      _ ≤ correctedResponse ρ₂ α₂ e.vUpper e.uLower :=
        correctedResponse_monotone_focal
          (by linarith) hα₂ hfvu0 huv helu0

/-- The canonical first step refines the canonical initial rectangle. -/
theorem canonicalInitialEnvelope_step_refines
    {ρ₁ ρ₂ α₁ α₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    EnvelopeRefines
      (canonicalInitialEnvelope α₁ α₂)
      (homogeneousEnvelopeStep ρ₁ ρ₂ α₁ α₂
        (canonicalInitialEnvelope α₁ α₂)) := by
  unfold EnvelopeRefines homogeneousEnvelopeStep canonicalInitialEnvelope
  have huLowerPos : 0 < (1 - α₁) / 2 := by linarith
  have hvLowerPos : 0 < (1 - α₂) / 2 := by linarith
  constructor
  · apply (self_le_correctedResponse_iff
      hρ₁ hα₁0 huLowerPos (by norm_num)).2
    linarith
  constructor
  · apply (correctedResponse_le_self_iff
      hρ₁ hα₁0 (by norm_num) hvLowerPos.le).2
    nlinarith [mul_nonneg hα₁0 hvLowerPos.le]
  constructor
  · apply (self_le_correctedResponse_iff
      hρ₂ hα₂0 hvLowerPos (by norm_num)).2
    linarith
  · apply (correctedResponse_le_self_iff
      hρ₂ hα₂0 (by norm_num) huLowerPos.le).2
    nlinarith [mul_nonneg hα₂0 huLowerPos.le]

/-- Iteration of the canonical coupled envelope map. -/
def homogeneousEnvelopeOrbit
    (ρ₁ ρ₂ α₁ α₂ : ℝ) : ℕ → HomogeneousEnvelope
  | 0 => canonicalInitialEnvelope α₁ α₂
  | n + 1 =>
      homogeneousEnvelopeStep ρ₁ ρ₂ α₁ α₂
        (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n)

@[simp]
theorem homogeneousEnvelopeOrbit_zero
    (ρ₁ ρ₂ α₁ α₂ : ℝ) :
    homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ 0 =
      canonicalInitialEnvelope α₁ α₂ :=
  rfl

@[simp]
theorem homogeneousEnvelopeOrbit_succ
    (ρ₁ ρ₂ α₁ α₂ : ℝ) (n : ℕ) :
    homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ (n + 1) =
      homogeneousEnvelopeStep ρ₁ ρ₂ α₁ α₂
        (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n) :=
  rfl

theorem homogeneousEnvelopeOrbit_valid
    {ρ₁ ρ₂ α₁ α₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    ∀ n, (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).Valid := by
  intro n
  induction n with
  | zero =>
      exact canonicalInitialEnvelope_valid hα₁0 hα₁1 hα₂0 hα₂1
  | succ n ih =>
      exact homogeneousEnvelopeStep_valid hρ₁ hρ₂ hα₁0 hα₂0 ih

theorem homogeneousEnvelopeOrbit_refines_succ
    {ρ₁ ρ₂ α₁ α₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    ∀ n,
      EnvelopeRefines
        (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n)
        (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact canonicalInitialEnvelope_step_refines
        hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
  | succ n ih =>
      exact homogeneousEnvelopeStep_refines_mono
        hρ₁ hρ₂ hα₁0 hα₂0
        (homogeneousEnvelopeOrbit_valid
          hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1 n)
        (homogeneousEnvelopeOrbit_valid
          hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1 (n + 1))
        ih

theorem homogeneousEnvelopeOrbit_uLower_monotone
    {ρ₁ ρ₂ α₁ α₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    Monotone
      (fun n => (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).uLower) :=
  monotone_nat_of_le_succ fun n =>
    (homogeneousEnvelopeOrbit_refines_succ
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1 n).1

theorem homogeneousEnvelopeOrbit_uUpper_antitone
    {ρ₁ ρ₂ α₁ α₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    Antitone
      (fun n => (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).uUpper) :=
  antitone_nat_of_succ_le fun n =>
    (homogeneousEnvelopeOrbit_refines_succ
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1 n).2.1

theorem homogeneousEnvelopeOrbit_vLower_monotone
    {ρ₁ ρ₂ α₁ α₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    Monotone
      (fun n => (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).vLower) :=
  monotone_nat_of_le_succ fun n =>
    (homogeneousEnvelopeOrbit_refines_succ
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1 n).2.2.1

theorem homogeneousEnvelopeOrbit_vUpper_antitone
    {ρ₁ ρ₂ α₁ α₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    Antitone
      (fun n => (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).vUpper) :=
  antitone_nat_of_succ_le fun n =>
    (homogeneousEnvelopeOrbit_refines_succ
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1 n).2.2.2

theorem continuousAt_correctedResponse_pair
    {ρ α u v : ℝ} (hα : 0 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ContinuousAt
      (fun p : ℝ × ℝ => correctedResponse ρ α p.1 p.2) (u, v) := by
  unfold correctedResponse
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact ne_of_gt (correctedResponse_denominator_pos hα hu hv)

/-- The canonical coupled homogeneous lower and upper envelopes all converge
to the positive coexistence equilibrium. -/
theorem homogeneousEnvelopeOrbit_tendsto_coexistence
    {ρ₁ ρ₂ α₁ α₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 ≤ α₂) (hα₂1 : α₂ < 1) :
    Tendsto
        (fun n =>
          (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).uLower)
        atTop (𝓝 (coexistenceU α₁ α₂)) ∧
      Tendsto
        (fun n =>
          (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).uUpper)
        atTop (𝓝 (coexistenceU α₁ α₂)) ∧
      Tendsto
        (fun n =>
          (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).vLower)
        atTop (𝓝 (coexistenceV α₁ α₂)) ∧
      Tendsto
        (fun n =>
          (homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ n).vUpper)
        atTop (𝓝 (coexistenceV α₁ α₂)) := by
  let orbit := homogeneousEnvelopeOrbit ρ₁ ρ₂ α₁ α₂
  let uLowerLimit : ℝ := ⨆ n, (orbit n).uLower
  let uUpperLimit : ℝ := ⨅ n, (orbit n).uUpper
  let vLowerLimit : ℝ := ⨆ n, (orbit n).vLower
  let vUpperLimit : ℝ := ⨅ n, (orbit n).vUpper
  have hvalid : ∀ n, (orbit n).Valid := by
    intro n
    exact homogeneousEnvelopeOrbit_valid
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1 n
  have huLowerBdd : BddAbove (range fun n => (orbit n).uLower) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hvalid n).2.1.trans (hvalid n).2.2.1
  have huUpperBdd : BddBelow (range fun n => (orbit n).uUpper) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hvalid n).1.le.trans (hvalid n).2.1
  have hvLowerBdd : BddAbove (range fun n => (orbit n).vLower) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hvalid n).2.2.2.2.1.trans (hvalid n).2.2.2.2.2
  have hvUpperBdd : BddBelow (range fun n => (orbit n).vUpper) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hvalid n).2.2.2.1.le.trans (hvalid n).2.2.2.2.1
  have huLowerMono :
      Monotone (fun n => (orbit n).uLower) := by
    exact homogeneousEnvelopeOrbit_uLower_monotone
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
  have huUpperAnti :
      Antitone (fun n => (orbit n).uUpper) := by
    exact homogeneousEnvelopeOrbit_uUpper_antitone
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
  have hvLowerMono :
      Monotone (fun n => (orbit n).vLower) := by
    exact homogeneousEnvelopeOrbit_vLower_monotone
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
  have hvUpperAnti :
      Antitone (fun n => (orbit n).vUpper) := by
    exact homogeneousEnvelopeOrbit_vUpper_antitone
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
  have huLowerTendsto :
      Tendsto (fun n => (orbit n).uLower)
        atTop (𝓝 uLowerLimit) :=
    tendsto_atTop_ciSup huLowerMono huLowerBdd
  have huUpperTendsto :
      Tendsto (fun n => (orbit n).uUpper)
        atTop (𝓝 uUpperLimit) :=
    tendsto_atTop_ciInf huUpperAnti huUpperBdd
  have hvLowerTendsto :
      Tendsto (fun n => (orbit n).vLower)
        atTop (𝓝 vLowerLimit) :=
    tendsto_atTop_ciSup hvLowerMono hvLowerBdd
  have hvUpperTendsto :
      Tendsto (fun n => (orbit n).vUpper)
        atTop (𝓝 vUpperLimit) :=
    tendsto_atTop_ciInf hvUpperAnti hvUpperBdd
  have huLowerPos : 0 < uLowerLimit := by
    have hinit : 0 < (orbit 0).uLower := (hvalid 0).1
    have hle : (orbit 0).uLower ≤ uLowerLimit :=
      ge_of_tendsto' huLowerTendsto fun n =>
        huLowerMono (Nat.zero_le n)
    exact hinit.trans_le hle
  have hvLowerPos : 0 < vLowerLimit := by
    have hinit : 0 < (orbit 0).vLower := (hvalid 0).2.2.2.1
    have hle : (orbit 0).vLower ≤ vLowerLimit :=
      ge_of_tendsto' hvLowerTendsto fun n =>
        hvLowerMono (Nat.zero_le n)
    exact hinit.trans_le hle
  have huUpperNonneg : 0 ≤ uUpperLimit :=
    ge_of_tendsto' huUpperTendsto fun n =>
      (hvalid n).1.le.trans (hvalid n).2.1
  have hvUpperNonneg : 0 ≤ vUpperLimit :=
    ge_of_tendsto' hvUpperTendsto fun n =>
      (hvalid n).2.2.2.1.le.trans (hvalid n).2.2.2.2.1
  have huOrder : uLowerLimit ≤ uUpperLimit :=
    le_of_tendsto_of_tendsto huLowerTendsto huUpperTendsto
      (Eventually.of_forall fun n => (hvalid n).2.1)
  have hvOrder : vLowerLimit ≤ vUpperLimit :=
    le_of_tendsto_of_tendsto hvLowerTendsto hvUpperTendsto
      (Eventually.of_forall fun n => (hvalid n).2.2.2.2.1)
  have huLowerPair :
      Tendsto
        (fun n => ((orbit n).uLower, (orbit n).vUpper))
        atTop (𝓝 (uLowerLimit, vUpperLimit)) := by
    rw [nhds_prod_eq]
    exact huLowerTendsto.prodMk hvUpperTendsto
  have huUpperPair :
      Tendsto
        (fun n => ((orbit n).uUpper, (orbit n).vLower))
        atTop (𝓝 (uUpperLimit, vLowerLimit)) := by
    rw [nhds_prod_eq]
    exact huUpperTendsto.prodMk hvLowerTendsto
  have hvLowerPair :
      Tendsto
        (fun n => ((orbit n).vLower, (orbit n).uUpper))
        atTop (𝓝 (vLowerLimit, uUpperLimit)) := by
    rw [nhds_prod_eq]
    exact hvLowerTendsto.prodMk huUpperTendsto
  have hvUpperPair :
      Tendsto
        (fun n => ((orbit n).vUpper, (orbit n).uLower))
        atTop (𝓝 (vUpperLimit, uLowerLimit)) := by
    rw [nhds_prod_eq]
    exact hvUpperTendsto.prodMk huLowerTendsto
  have huLowerResponse :
      Tendsto
        (fun n =>
          correctedResponse ρ₁ α₁
            (orbit n).uLower (orbit n).vUpper)
        atTop
        (𝓝 (correctedResponse ρ₁ α₁ uLowerLimit vUpperLimit)) :=
    (continuousAt_correctedResponse_pair
      hα₁0 huLowerPos.le hvUpperNonneg).tendsto.comp huLowerPair
  have huUpperResponse :
      Tendsto
        (fun n =>
          correctedResponse ρ₁ α₁
            (orbit n).uUpper (orbit n).vLower)
        atTop
        (𝓝 (correctedResponse ρ₁ α₁ uUpperLimit vLowerLimit)) :=
    (continuousAt_correctedResponse_pair
      hα₁0 huUpperNonneg hvLowerPos.le).tendsto.comp huUpperPair
  have hvLowerResponse :
      Tendsto
        (fun n =>
          correctedResponse ρ₂ α₂
            (orbit n).vLower (orbit n).uUpper)
        atTop
        (𝓝 (correctedResponse ρ₂ α₂ vLowerLimit uUpperLimit)) :=
    (continuousAt_correctedResponse_pair
      hα₂0 hvLowerPos.le huUpperNonneg).tendsto.comp hvLowerPair
  have hvUpperResponse :
      Tendsto
        (fun n =>
          correctedResponse ρ₂ α₂
            (orbit n).vUpper (orbit n).uLower)
        atTop
        (𝓝 (correctedResponse ρ₂ α₂ vUpperLimit uLowerLimit)) :=
    (continuousAt_correctedResponse_pair
      hα₂0 hvUpperNonneg huLowerPos.le).tendsto.comp hvUpperPair
  have huLowerFixed :
      uLowerLimit =
        correctedResponse ρ₁ α₁ uLowerLimit vUpperLimit := by
    apply tendsto_nhds_unique
      (huLowerTendsto.comp (tendsto_add_atTop_nat 1))
    simpa [orbit, homogeneousEnvelopeOrbit_succ,
      homogeneousEnvelopeStep] using huLowerResponse
  have huUpperFixed :
      uUpperLimit =
        correctedResponse ρ₁ α₁ uUpperLimit vLowerLimit := by
    apply tendsto_nhds_unique
      (huUpperTendsto.comp (tendsto_add_atTop_nat 1))
    simpa [orbit, homogeneousEnvelopeOrbit_succ,
      homogeneousEnvelopeStep] using huUpperResponse
  have hvLowerFixed :
      vLowerLimit =
        correctedResponse ρ₂ α₂ vLowerLimit uUpperLimit := by
    apply tendsto_nhds_unique
      (hvLowerTendsto.comp (tendsto_add_atTop_nat 1))
    simpa [orbit, homogeneousEnvelopeOrbit_succ,
      homogeneousEnvelopeStep] using hvLowerResponse
  have hvUpperFixed :
      vUpperLimit =
        correctedResponse ρ₂ α₂ vUpperLimit uLowerLimit := by
    apply tendsto_nhds_unique
      (hvUpperTendsto.comp (tendsto_add_atTop_nat 1))
    simpa [orbit, homogeneousEnvelopeOrbit_succ,
      homogeneousEnvelopeStep] using hvUpperResponse
  obtain ⟨huLowerEq, huUpperEq, hvLowerEq, hvUpperEq⟩ :=
    weak_competition_response_envelope_collapse
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
      huLowerPos huOrder hvLowerPos hvOrder
      huUpperFixed.le huLowerFixed.ge hvUpperFixed.le hvLowerFixed.ge
  constructor
  · simpa [orbit, huLowerEq] using huLowerTendsto
  constructor
  · simpa [orbit, huUpperEq] using huUpperTendsto
  constructor
  · simpa [orbit, hvLowerEq] using hvLowerTendsto
  · simpa [orbit, hvUpperEq] using hvUpperTendsto

/-! ## Interface to the spatial corridor argument -/

/-- Standard finite-stage asymptotic comparison with the homogeneous
competitive envelopes.  For every *fixed* number of homogeneous comparison
steps and every positive tolerance, the spatially observed pair eventually
lies in that enlarged rectangle.

This is strictly weaker than convergence: no envelope stage is required to
track the physical generation, and the tolerance need not have a prescribed
rate.  It is the natural conclusion of a finite-step comparison argument
after positive corridor floors and environmental errors have been controlled.
-/
def EventuallyTrappedByEverySeededEnvelope
    (ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ) (u v : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ) (ε : ℝ), 0 < ε →
    ∀ᶠ n in atTop,
      (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).uLower - ε ≤ u n ∧
        u n ≤
          (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).uUpper + ε ∧
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).vLower - ε ≤ v n ∧
        v n ≤
          (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).vUpper + ε

/-- Finite-stage asymptotic comparison with every homogeneous envelope forces
convergence to coexistence.  This is the fluctuation/squeezing endpoint of the
spatial theorem and does not assume a same-generation trap. -/
theorem tendsto_coexistence_of_eventually_trapped_by_every_seeded_envelope
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1)
    {u v : ℕ → ℝ}
    (htrap :
      EventuallyTrappedByEverySeededEnvelope
        ρ₁ ρ₂ α₁ α₂ ℓu ℓv u v) :
    Tendsto u atTop (𝓝 (coexistenceU α₁ α₂)) ∧
      Tendsto v atTop (𝓝 (coexistenceV α₁ α₂)) := by
  have henvelope :=
    seededEnvelopeOrbit_tendsto_coexistence
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
      hℓu hℓv huFloor hvFloor
  constructor
  · rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨m, hm⟩ :=
        (henvelope.1.eventually_const_lt ha).exists
      let ε :=
        ((seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).uLower - a) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      filter_upwards [htrap m ε hε] with n hn
      dsimp [ε] at hn
      linarith [hn.1]
    · intro a ha
      obtain ⟨m, hm⟩ :=
        (henvelope.2.1.eventually_lt_const ha).exists
      let ε :=
        (a - (seededEnvelopeOrbit
          ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).uUpper) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      filter_upwards [htrap m ε hε] with n hn
      dsimp [ε] at hn
      linarith [hn.2.1]
  · rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨m, hm⟩ :=
        (henvelope.2.2.1.eventually_const_lt ha).exists
      let ε :=
        ((seededEnvelopeOrbit
          ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).vLower - a) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      filter_upwards [htrap m ε hε] with n hn
      dsimp [ε] at hn
      linarith [hn.2.2.1]
    · intro a ha
      obtain ⟨m, hm⟩ :=
        (henvelope.2.2.2.eventually_lt_const ha).exists
      let ε :=
        (a - (seededEnvelopeOrbit
          ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).vUpper) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      filter_upwards [htrap m ε hε] with n hn
      dsimp [ε] at hn
      linarith [hn.2.2.2]

/-- Uniform fixed-stage comparison on a moving family of spatial sets. -/
def EventuallyUniformlyTrappedByEverySeededEnvelope
    (ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ)
    (u v : ℕ → ℝ → ℝ) (region : ℕ → Set ℝ) : Prop :=
  ∀ (m : ℕ) (ε : ℝ), 0 < ε →
    ∀ᶠ n in atTop, ∀ x ∈ region n,
      (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).uLower - ε ≤ u n x ∧
        u n x ≤
          (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).uUpper + ε ∧
        (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).vLower - ε ≤ v n x ∧
        v n x ≤
          (seededEnvelopeOrbit ρ₁ ρ₂ α₁ α₂ ℓu ℓv m).vUpper + ε

/-- Uniform convergence on a moving family of spatial sets. -/
def UniformlyTendstoOnMovingSets
    (f : ℕ → ℝ → ℝ) (region : ℕ → Set ℝ) (limit : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ region n, |f n x - limit| < ε

/-- Uniform finite-stage trapping on a moving corridor implies uniform
coexistence convergence throughout that corridor. -/
theorem uniformly_tendsto_coexistence_of_fixed_depth_comparison
    {ρ₁ ρ₂ α₁ α₂ ℓu ℓv : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1)
    (hℓu : 0 < ℓu) (hℓv : 0 < ℓv)
    (huFloor : ℓu + α₁ ≤ 1)
    (hvFloor : ℓv + α₂ ≤ 1)
    {u v : ℕ → ℝ → ℝ} {region : ℕ → Set ℝ}
    (htrap :
      EventuallyUniformlyTrappedByEverySeededEnvelope
        ρ₁ ρ₂ α₁ α₂ ℓu ℓv u v region) :
    UniformlyTendstoOnMovingSets u region (coexistenceU α₁ α₂) ∧
      UniformlyTendstoOnMovingSets v region (coexistenceV α₁ α₂) := by
  have henvelope :=
    seededEnvelopeOrbit_tendsto_coexistence
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
      hℓu hℓv huFloor hvFloor
  constructor
  · intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    obtain ⟨mLower, hmLower⟩ :=
      (henvelope.1.eventually_const_lt
        (show coexistenceU α₁ α₂ - ε / 2 <
          coexistenceU α₁ α₂ by linarith)).exists
    obtain ⟨mUpper, hmUpper⟩ :=
      (henvelope.2.1.eventually_lt_const
        (show coexistenceU α₁ α₂ <
          coexistenceU α₁ α₂ + ε / 2 by linarith)).exists
    filter_upwards
      [htrap mLower (ε / 2) hhalf,
        htrap mUpper (ε / 2) hhalf] with n hnLower hnUpper
    intro x hx
    rw [abs_lt]
    constructor
    · linarith [(hnLower x hx).1]
    · linarith [(hnUpper x hx).2.1]
  · intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    obtain ⟨mLower, hmLower⟩ :=
      (henvelope.2.2.1.eventually_const_lt
        (show coexistenceV α₁ α₂ - ε / 2 <
          coexistenceV α₁ α₂ by linarith)).exists
    obtain ⟨mUpper, hmUpper⟩ :=
      (henvelope.2.2.2.eventually_lt_const
        (show coexistenceV α₁ α₂ <
          coexistenceV α₁ α₂ + ε / 2 by linarith)).exists
    filter_upwards
      [htrap mLower (ε / 2) hhalf,
        htrap mUpper (ε / 2) hhalf] with n hnLower hnUpper
    intro x hx
    rw [abs_lt]
    constructor
    · linarith [(hnLower x hx).2.2.1]
    · linarith [(hnUpper x hx).2.2.2]

/-- Uniform convergence on a moving corridor gives convergence along every
eventually corridor-contained observer. -/
theorem observer_tendsto_of_uniformly_tendsto_on_moving_sets
    {f : ℕ → ℝ → ℝ} {region : ℕ → Set ℝ}
    {limit : ℝ} {observer : ℕ → ℝ}
    (huniform : UniformlyTendstoOnMovingSets f region limit)
    (hobserver : ∀ᶠ n in atTop, observer n ∈ region n) :
    Tendsto (fun n => f n (observer n)) atTop (𝓝 limit) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [huniform ε hε, hobserver] with n hn hobs
  simpa [Real.dist_eq] using hn (observer n) hobs

/-- Corrected uniform weak-competition corridor theorem.  The positive
persistence floors are shrunk to admissible seeded-envelope floors.  The
global spatial input is the standard fixed-depth comparison property, not a
same-generation trap and not the desired convergence itself.

The two `Nonempty InvasionWeight` clauses prevent the reduced speed from
being interpreted as an infimum over an empty or analytically invalid
exponential-moment domain.  Deriving `hglobal.2.2` from the speed inequality
still requires the scalar subcritical spreading/linear-determinacy theorem;
that analytic implication is deliberately not asserted here.
-/
theorem corrected_weak_competition_uniform_corridor_convergence
    {K₁ K₂ : ℝ → ℝ}
    {ρ₁ ρ₂ α₁ α₂ c margin persistenceU persistenceV : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ < 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ < 1)
    (hcorridor :
      0 < margin ∧
        c + 2 * margin ≤
          coexistenceCriticalSpeed K₁ K₂ ρ₁ ρ₂ α₁ α₂)
    (hpersistenceU : 0 < persistenceU)
    (hpersistenceV : 0 < persistenceV)
    (u v : ℕ → ℝ → ℝ)
    (hglobal :
      Nonempty (InvasionWeight K₁ ρ₁ α₁) ∧
        Nonempty (InvasionWeight K₂ ρ₂ α₂) ∧
        ∀ (ℓu ℓv : ℝ),
          0 < ℓu → ℓu ≤ persistenceU → ℓu + α₁ ≤ 1 →
          0 < ℓv → ℓv ≤ persistenceV → ℓv + α₂ ≤ 1 →
          EventuallyUniformlyTrappedByEverySeededEnvelope
            ρ₁ ρ₂ α₁ α₂ ℓu ℓv u v
            (favorableCorridor c
              (coexistenceCriticalSpeed K₁ K₂ ρ₁ ρ₂ α₁ α₂)
              margin)) :
    (∀ n,
      (favorableCorridor c
        (coexistenceCriticalSpeed K₁ K₂ ρ₁ ρ₂ α₁ α₂)
        margin n).Nonempty) ∧
      UniformlyTendstoOnMovingSets u
        (favorableCorridor c
          (coexistenceCriticalSpeed K₁ K₂ ρ₁ ρ₂ α₁ α₂)
          margin)
        (coexistenceU α₁ α₂) ∧
      UniformlyTendstoOnMovingSets v
        (favorableCorridor c
          (coexistenceCriticalSpeed K₁ K₂ ρ₁ ρ₂ α₁ α₂)
          margin)
        (coexistenceV α₁ α₂) := by
  obtain ⟨ℓu, hℓu, hℓuPersistence, huFloor⟩ :=
    exists_admissible_seed_floor hα₁1 hpersistenceU
  obtain ⟨ℓv, hℓv, hℓvPersistence, hvFloor⟩ :=
    exists_admissible_seed_floor hα₂1 hpersistenceV
  have htrap :=
    hglobal.2.2 ℓu ℓv
      hℓu hℓuPersistence huFloor
      hℓv hℓvPersistence hvFloor
  have hconv :=
    uniformly_tendsto_coexistence_of_fixed_depth_comparison
      hρ₁ hρ₂ hα₁0 hα₁1 hα₂0 hα₂1
      hℓu hℓv huFloor hvFloor htrap
  exact ⟨fun n => favorableCorridor_nonempty hcorridor.2 n,
    hconv.1, hconv.2⟩

/-- Uniform convergence on a one-sided favorable corridor gives convergence
along every constant-speed frame inside that same shrunken corridor. -/
theorem constant_speed_observer_tendsto_of_uniform_corridor
    {c front margin s : ℝ} {u v : ℕ → ℝ → ℝ}
    {uLimit vLimit : ℝ}
    (hleft : c + margin ≤ s) (hright : s ≤ front - margin)
    (hu :
      UniformlyTendstoOnMovingSets u
        (favorableCorridor c front margin) uLimit)
    (hv :
      UniformlyTendstoOnMovingSets v
        (favorableCorridor c front margin) vLimit) :
    Tendsto (fun n => u n (s * (n : ℝ))) atTop (𝓝 uLimit) ∧
      Tendsto (fun n => v n (s * (n : ℝ))) atTop (𝓝 vLimit) := by
  have hmember :
      ∀ᶠ n in atTop,
        s * (n : ℝ) ∈ favorableCorridor c front margin n := by
    apply Eventually.of_forall
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact ⟨mul_le_mul_of_nonneg_right hleft hn,
      mul_le_mul_of_nonneg_right hright hn⟩
  exact ⟨
    observer_tendsto_of_uniformly_tendsto_on_moving_sets hu hmember,
    observer_tendsto_of_uniformly_tendsto_on_moving_sets hv hmember⟩

section AxiomAudit

#print axioms invasionLowerMultiplier_mul_le_correctedResponse
#print axioms homogeneousEnvelopeOrbit_tendsto_coexistence
#print axioms tendsto_coexistence_of_eventually_trapped_by_every_seeded_envelope
#print axioms uniformly_tendsto_coexistence_of_fixed_depth_comparison
#print axioms corrected_weak_competition_uniform_corridor_convergence
#print axioms constant_speed_observer_tendsto_of_uniform_corridor

end AxiomAudit

end

end ShenWork.Liang
