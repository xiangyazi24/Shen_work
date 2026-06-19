import ShenWork.PaperOne.WholeLineWaveTrap
import ShenWork.PaperOne.WholeLineSchauderFixedPoint

noncomputable section

open Set

namespace ShenWork.PaperOne

/-- The upper exponential barrier is a member of the whole-line wave trap. -/
theorem waveTrap_upper_mem {κ κt D : ℝ}
    (hκ : 0 < κ) (hκt : κ < κt) (hD : 1 ≤ D) :
    upperBarrier κ ∈ WaveTrap κ κt D := by
  constructor
  · intro x
    exact ⟨lowerBarrier_le_upper hκ.le hκt hD, le_rfl⟩
  · exact upperBarrier_antitone hκ

/-- Nonemptiness of the whole-line wave trap, witnessed by `U⁺`. -/
theorem waveTrap_nonempty {κ κt D : ℝ}
    (hκ : 0 < κ) (hκt : κ < κt) (hD : 1 ≤ D) :
    (WaveTrap κ κt D).Nonempty :=
  ⟨upperBarrier κ, waveTrap_upper_mem hκ hκt hD⟩

/--
Schauder fixed point for the whole-line wave trap.

The current whole-line Schauder interface is the local-uniform abstract
principle `LocalUniformSchauderFixedPointPrinciple`; the convexity,
local-uniform closedness, and nonemptiness of `WaveTrap` are available as
separate trap facts.
-/
theorem wholeLine_wave_fixedPoint_exists {κ κt D : ℝ}
    {T : (ℝ → ℝ) → ℝ → ℝ}
    (hprinciple :
      ShenWork.Paper1.LocalUniformSchauderFixedPointPrinciple
        (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D))
    (hmapsTo : MapsTo T (WaveTrap κ κt D) (WaveTrap κ κt D))
    (hcont :
      ShenWork.Paper1.LocalUniformContinuousOn
        (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D) T)
    (hcompact :
      ShenWork.Paper1.LocalUniformSequentiallyCompactRange
        (fun U : ℝ → ℝ => U ∈ WaveTrap κ κt D) T) :
    ∃ Ustar : ℝ → ℝ, Ustar ∈ WaveTrap κ κt D ∧ T Ustar = Ustar := by
  exact ShenWork.Paper1.wholeLineSchauderFixedPoint
    hprinciple (fun U hU => hmapsTo hU) hcont hcompact

#print axioms waveTrap_upper_mem
#print axioms waveTrap_nonempty
#print axioms wholeLine_wave_fixedPoint_exists

end ShenWork.PaperOne
