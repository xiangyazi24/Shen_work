import ShenWork.Paper1.WholeLineCauchyBUC
import ShenWork.Paper1.WholeLineCauchyDuhamel

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Imported maximal BUC Cauchy theory

This file records the minimal operational projection of the whole-line
maximal BUC theory used by the large-critical branch of Proposition 1.1.
The cited local theory is stronger; only the orbit data and the continuation
implication consumed downstream are retained here.
-/

/--
A maximal `BUC(ℝ)` orbit for one nonnegative initial datum, together with
the finite-subhorizon classical and mild solution interfaces and the weak
projection of the blow-up alternative needed for continuation.
-/
def WholeLineMaximalBUCSolution
    (p : CMParams) (u₀ : ℝ → ℝ) : Prop :=
  ∃ Tmax : WithTop ℝ, ∃ U : ℝ → WholeLineBUC,
    let u : ℝ → ℝ → ℝ := fun t x => (U t).1 x
    let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t)
    0 < Tmax ∧
      HasInitialDatum u u₀ ∧
      HasUniformInitialTrace u u₀ ∧
      (∀ T : ℝ, 0 ≤ T → (T : WithTop ℝ) < Tmax →
        ContinuousOn U (Set.Icc (0 : ℝ) T)) ∧
      (∀ T : ℝ, 0 < T → (T : WithTop ℝ) < Tmax →
        IsClassicalSolution p T u v) ∧
      (∀ T : ℝ, 0 < T → (T : WithTop ℝ) < Tmax →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
          u t x = wholeLineCauchyMildMap p u₀ u t x) ∧
      (∀ (t x : ℝ), 0 ≤ t → (t : WithTop ℝ) < Tmax → 0 ≤ u t x) ∧
      ((∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
          (t : WithTop ℝ) < Tmax → ‖U t‖ ≤ C) →
        Tmax = ⊤)

/--
The single imported input used by the continuation argument: every
paper-admissible nonnegative datum has a maximal orbit satisfying
`WholeLineMaximalBUCSolution`.
-/
def WholeLineMaximalBUCImport (p : CMParams) : Prop :=
  ∀ u₀ : ℝ → ℝ, PaperNonnegativeInitialDatum u₀ →
    WholeLineMaximalBUCSolution p u₀

end ShenWork.Paper1
