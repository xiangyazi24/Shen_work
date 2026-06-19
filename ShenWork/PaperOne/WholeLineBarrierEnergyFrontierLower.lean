import ShenWork.PaperOne.WholeLineConstantBarrierEnergy
open MeasureTheory

noncomputable section

namespace ShenWork.PaperOne

def wholeLineLowerBarrierTest (U : ℝ → ℝ → ℝ) (lo t x : ℝ) : ℝ :=
  max (lo - U t x) 0

def wholeLineLowerBarrierTimeTerm (U : ℝ → ℝ → ℝ) (lo t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineLowerBarrierTest U lo t x * deriv (fun τ => U τ x) t

def wholeLineLowerBarrierDiffusionTerm (U : ℝ → ℝ → ℝ) (lo t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineLowerBarrierTest U lo t x * iteratedDeriv 2 (U t) x

def wholeLineLowerBarrierChemotaxisTerm
    (p : CMParams) (U V : ℝ → ℝ → ℝ) (lo t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineLowerBarrierTest U lo t x *
    deriv (fun y => (U t y) ^ p.m * deriv (V t) y) x

def wholeLineLowerBarrierReactionTerm
    (p : CMParams) (U : ℝ → ℝ → ℝ) (lo t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineLowerBarrierTest U lo t x *
    wholeLineReaction p (U t) x

theorem wholeLineLowerBarrierReactionTerm_nonneg_of_le_one
    (p : CMParams) (U : ℝ → ℝ → ℝ) {lo t : ℝ}
    (hU_nonneg : ∀ x, 0 ≤ U t x) (hlo : lo ≤ 1) :
    0 ≤ wholeLineLowerBarrierReactionTerm p U lo t := by
  unfold wholeLineLowerBarrierReactionTerm
  refine integral_nonneg fun x => ?_
  unfold wholeLineLowerBarrierTest wholeLineReaction
  by_cases h : lo - U t x ≤ 0
  · simp [max_eq_right h]
  · have hUlo : U t x ≤ lo := by linarith
    have hU1 : U t x ≤ 1 := le_trans hUlo hlo
    have hpow : (U t x) ^ p.α ≤ 1 :=
      Real.rpow_le_one (hU_nonneg x) hU1 (by linarith [p.hα])
    exact mul_nonneg (le_max_right _ _)
      (mul_nonneg (hU_nonneg x) (sub_nonneg.mpr hpow))

structure WholeLineLowerBarrierEnergySteps
    (p : CMParams) (T : ℝ) (U V : ℝ → ℝ → ℝ) (lo : ℝ) where
  K : ℝ
  K_nonneg : 0 ≤ K
  U_nonneg : ∀ t x, 0 ≤ U t x
  lo_le_one : lo ≤ 1
  nonneg : ∀ t, 0 < t → t < T → 0 ≤ wholeLineLowerDeficitEnergy U lo t
  cont : ∀ s t, 0 < s → s ≤ t → t < T →
    ContinuousOn (wholeLineLowerDeficitEnergy U lo) (Set.Icc s t)
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    wholeLineLowerDeficitEnergy U lo s < ε
  timeLeibniz : ∀ t, 0 < t → t < T →
    HasDerivWithinAt (wholeLineLowerDeficitEnergy U lo)
      (-2 * wholeLineLowerBarrierTimeTerm U lo t) (Set.Ici t) t
  pdeSubstitution : ∀ t, 0 < t → t < T →
    wholeLineLowerBarrierTimeTerm U lo t =
      wholeLineLowerBarrierDiffusionTerm U lo t -
        p.χ * wholeLineLowerBarrierChemotaxisTerm p U V lo t +
      wholeLineLowerBarrierReactionTerm p U lo t
  diffusionIBP_decay : ∀ t, 0 < t → t < T →
    0 ≤ wholeLineLowerBarrierDiffusionTerm U lo t
  chemotaxisCrossControl : ∀ t, 0 < t → t < T →
    2 * (p.χ * wholeLineLowerBarrierChemotaxisTerm p U V lo t) ≤
      K * wholeLineLowerDeficitEnergy U lo t

def wholeLine_lowerBarrierEnergyFrontierOfSteps
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {lo : ℝ}
    (H : WholeLineLowerBarrierEnergySteps p T U V lo) :
    WholeLineBarrierEnergyFrontier (wholeLineLowerDeficitEnergy U lo) T where
  Eprime := fun t => -2 * wholeLineLowerBarrierTimeTerm U lo t
  K := H.K
  K_nonneg := H.K_nonneg
  nonneg := H.nonneg
  cont := H.cont
  initial_vanishes := H.initial_vanishes
  diffIneq := by
    intro t ht0 htT
    refine ⟨H.timeLeibniz t ht0 htT, ?_⟩
    have hpde := H.pdeSubstitution t ht0 htT
    have hdiff := H.diffusionIBP_decay t ht0 htT
    have hreact := wholeLineLowerBarrierReactionTerm_nonneg_of_le_one p U
      (H.U_nonneg t) H.lo_le_one (t := t)
    have hchem := H.chemotaxisCrossControl t ht0 htT
    have hmain :
        -2 * wholeLineLowerBarrierTimeTerm U lo t ≤
          2 * (p.χ * wholeLineLowerBarrierChemotaxisTerm p U V lo t) := by
      rw [hpde]
      linarith
    exact le_trans hmain hchem

theorem wholeLine_lowerBarrierEnergyFrontier_of_steps
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {lo : ℝ}
    (H : WholeLineLowerBarrierEnergySteps p T U V lo) :
    Nonempty (WholeLineBarrierEnergyFrontier (wholeLineLowerDeficitEnergy U lo) T) :=
  ⟨wholeLine_lowerBarrierEnergyFrontierOfSteps H⟩

#print axioms wholeLine_lowerBarrierEnergyFrontier_of_steps
end ShenWork.PaperOne
