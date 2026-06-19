import ShenWork.PaperOne.WholeLineConstantBarrierEnergy

open MeasureTheory

noncomputable section

namespace ShenWork.PaperOne

def wholeLineUpperBarrierTest (U : ℝ → ℝ → ℝ) (hi t x : ℝ) : ℝ :=
  max (U t x - hi) 0

def wholeLineUpperBarrierTimeTerm (U : ℝ → ℝ → ℝ) (hi t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineUpperBarrierTest U hi t x * deriv (fun τ => U τ x) t

def wholeLineUpperBarrierDiffusionTerm (U : ℝ → ℝ → ℝ) (hi t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineUpperBarrierTest U hi t x * iteratedDeriv 2 (U t) x

def wholeLineUpperBarrierChemotaxisTerm
    (p : CMParams) (U V : ℝ → ℝ → ℝ) (hi t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineUpperBarrierTest U hi t x *
    deriv (fun y => (U t y) ^ p.m * deriv (V t) y) x

def wholeLineUpperBarrierReactionTerm
    (p : CMParams) (U : ℝ → ℝ → ℝ) (hi t : ℝ) : ℝ :=
  ∫ x : ℝ, wholeLineUpperBarrierTest U hi t x *
    wholeLineReaction p (U t) x

theorem wholeLineUpperBarrierReactionTerm_nonpos_of_one_le
    (p : CMParams) (U : ℝ → ℝ → ℝ) {hi t : ℝ} (hhi : 1 ≤ hi) :
    wholeLineUpperBarrierReactionTerm p U hi t ≤ 0 := by
  unfold wholeLineUpperBarrierReactionTerm
  refine integral_nonpos fun x => ?_
  unfold wholeLineUpperBarrierTest wholeLineReaction
  by_cases h : U t x - hi ≤ 0
  · simp [max_eq_right h]
  · have hU1 : 1 ≤ U t x := by linarith
    have hpow : 1 ≤ (U t x) ^ p.α :=
      Real.one_le_rpow hU1 (by linarith [p.hα])
    exact mul_nonpos_of_nonneg_of_nonpos (le_max_right _ _)
      (mul_nonpos_of_nonneg_of_nonpos (le_trans zero_le_one hU1)
        (sub_nonpos.mpr hpow))

structure WholeLineUpperBarrierEnergySteps
    (p : CMParams) (T : ℝ) (U V : ℝ → ℝ → ℝ) (hi : ℝ) where
  K : ℝ
  K_nonneg : 0 ≤ K
  hi_one_le : 1 ≤ hi
  nonneg : ∀ t, 0 < t → t < T → 0 ≤ wholeLineUpperExcessEnergy U hi t
  cont : ∀ s t, 0 < s → s ≤ t → t < T →
    ContinuousOn (wholeLineUpperExcessEnergy U hi) (Set.Icc s t)
  initial_vanishes : ∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → s < T →
    wholeLineUpperExcessEnergy U hi s < ε
  timeLeibniz : ∀ t, 0 < t → t < T →
    HasDerivWithinAt (wholeLineUpperExcessEnergy U hi)
      (2 * wholeLineUpperBarrierTimeTerm U hi t) (Set.Ici t) t
  pdeSubstitution : ∀ t, 0 < t → t < T →
    wholeLineUpperBarrierTimeTerm U hi t =
      wholeLineUpperBarrierDiffusionTerm U hi t -
        p.χ * wholeLineUpperBarrierChemotaxisTerm p U V hi t +
      wholeLineUpperBarrierReactionTerm p U hi t
  diffusionIBP_decay : ∀ t, 0 < t → t < T →
    wholeLineUpperBarrierDiffusionTerm U hi t ≤ 0
  chemotaxisCrossControl : ∀ t, 0 < t → t < T →
    2 * (-p.χ * wholeLineUpperBarrierChemotaxisTerm p U V hi t) ≤
      K * wholeLineUpperExcessEnergy U hi t

def wholeLine_upperBarrierEnergyFrontierOfSteps
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {hi : ℝ}
    (H : WholeLineUpperBarrierEnergySteps p T U V hi) :
    WholeLineBarrierEnergyFrontier (wholeLineUpperExcessEnergy U hi) T where
  Eprime := fun t => 2 * wholeLineUpperBarrierTimeTerm U hi t
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
    have hreact := wholeLineUpperBarrierReactionTerm_nonpos_of_one_le p U H.hi_one_le
      (t := t)
    have hchem := H.chemotaxisCrossControl t ht0 htT
    have hmain :
        2 * wholeLineUpperBarrierTimeTerm U hi t ≤
          2 * (-p.χ * wholeLineUpperBarrierChemotaxisTerm p U V hi t) := by
      rw [hpde]
      linarith
    exact le_trans hmain hchem

theorem wholeLine_upperBarrierEnergyFrontier_of_steps
    {p : CMParams} {T : ℝ} {U V : ℝ → ℝ → ℝ} {hi : ℝ}
    (H : WholeLineUpperBarrierEnergySteps p T U V hi) :
    Nonempty (WholeLineBarrierEnergyFrontier (wholeLineUpperExcessEnergy U hi) T) :=
  ⟨wholeLine_upperBarrierEnergyFrontierOfSteps H⟩

#print axioms wholeLine_upperBarrierEnergyFrontier_of_steps

end ShenWork.PaperOne
