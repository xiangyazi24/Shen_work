import ShenWork.Paper2.IntervalBFormLinearDriftComparisonRegularDischarge
import ShenWork.PDE.IntervalSemigroupAtZero

open Filter Topology Set

open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-!
This additive file records the exact obstruction to assembling the requested
regular squared-heat barrier package with the current concrete semigroup
definition.

The blocker is not a missing `HasDerivAt` lemma.  The full-kernel semigroup in
this tree has value `0` at time `0` (`intervalFullSemigroupOperator_zero`), so
the squared barrier also has value `0` at time `0`.  Consequently the current
`SquareHeatSubsolutionCalculus.initial_eq` field,

`squareHeatBarrier M f 0 x = f x ^ 2`,

forces `f x = 0` on `[0,1]`.  This contradicts the positive seed field
`SquareHeatSeed.pos_somewhere`.
-/

theorem squareHeatBarrier_at_zero_eq_zero
    (M : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    squareHeatBarrier M f 0 x = 0 := by
  simp [squareHeatBarrier,
    ShenWork.IntervalSemigroupAtZero.intervalFullSemigroupOperator_zero]

theorem squareHeatSubsolutionCalculus_initial_forces_seed_zero
    {T M : ℝ} {f : ℝ → ℝ} {B C : ℝ → ℝ → ℝ}
    (hcalc : SquareHeatSubsolutionCalculus T M f B C)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    f x = 0 := by
  have h := hcalc.initial_eq x hx
  rw [squareHeatBarrier_at_zero_eq_zero] at h
  exact sq_eq_zero_iff.mp h.symm

theorem no_squareHeatSubsolutionCalculus_with_positive_seed
    {T M : ℝ} {u₀ f : ℝ → ℝ} {B C : ℝ → ℝ → ℝ}
    (hcalc : SquareHeatSubsolutionCalculus T M f B C)
    (hseed : SquareHeatSeed u₀ f) :
    False := by
  rcases hseed.pos_somewhere with ⟨y, hy, hypos⟩
  have hyzero :
      f y = 0 :=
    squareHeatSubsolutionCalculus_initial_forces_seed_zero hcalc hy
  linarith

end ShenWork.Paper2.BFormPositiveDatumNegPart