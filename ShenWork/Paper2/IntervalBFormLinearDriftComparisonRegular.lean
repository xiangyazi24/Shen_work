import ShenWork.Paper2.IntervalBFormSquareHeatSubsolution
import ShenWork.PDE.ParabolicMaxPrinciple

open Set

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Boundedness on the finite Neumann strip `[0,T] × [0,1]`. -/
def BoundedOnIntervalStrip (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Icc (0 : ℝ) 1, |u t x| ≤ M

/-- Coefficient assumptions for the interval linear drift-reaction operator.

The reaction entry is the uniform Lipschitz bound for
`z ↦ C t x * z` on the strip. -/
structure NeumannLinearDriftCoefficientsRegular
    (T : ℝ) (B C : ℝ → ℝ → ℝ) : Prop where
  drift_bounded : BoundedOnIntervalStrip T B
  reaction_bounded : BoundedOnIntervalStrip T C
  reaction_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ ⦃t x a b : ℝ⦄,
        t ∈ Set.Icc (0 : ℝ) T →
          x ∈ Set.Icc (0 : ℝ) 1 →
            |C t x * a - C t x * b| ≤ L * |a - b|

/-- Regularity fields shared by classical interval subsolutions. -/
structure NeumannLinearDriftSubSolutionRegularity
    (T : ℝ) (_B _C : ℝ → ℝ → ℝ) (w : ℝ → ℝ → ℝ) : Prop where
  continuousOn_rect :
    ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  time_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivAt (fun τ : ℝ => w τ x)
          (ShenWork.PDE.ParabolicMaxPrinciple.dt w t x) t
  space_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivAt (fun y : ℝ => w t y)
          (ShenWork.PDE.ParabolicMaxPrinciple.dx w t x) x
  space_second_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
        HasDerivAt
          (fun y : ℝ => ShenWork.PDE.ParabolicMaxPrinciple.dx w t y)
          (ShenWork.PDE.ParabolicMaxPrinciple.dxx w t x) x
  neumann :
    ∀ t, 0 < t → t < T →
      ShenWork.PDE.ParabolicMaxPrinciple.dx w t 0 = 0 ∧
        ShenWork.PDE.ParabolicMaxPrinciple.dx w t 1 = 0
  bounded : BoundedOnIntervalStrip T w

/-- Classical interval subsolution of
`w_t = w_xx + B w_x + C w` with homogeneous Neumann data. -/
structure IsClassicalNeumannLinearDriftSubSolution
    (T : ℝ) (B C : ℝ → ℝ → ℝ) (w : ℝ → ℝ → ℝ) : Prop
    extends NeumannLinearDriftSubSolutionRegularity T B C w where
  pde_le :
    ∀ ⦃t x : ℝ⦄,
      0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
        neumannLinearDriftResidual B C w t x ≤ 0

/-- Classical interval supersolution of
`u_t = u_xx + B u_x + C u` with homogeneous Neumann data. -/
structure IsClassicalNeumannLinearDriftSuperSolution
    (T : ℝ) (B C : ℝ → ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  continuousOn_rect :
    ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)
  time_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivAt (fun τ : ℝ => u τ x)
          (ShenWork.PDE.ParabolicMaxPrinciple.dt u t x) t
  space_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivAt (fun y : ℝ => u t y)
          (ShenWork.PDE.ParabolicMaxPrinciple.dx u t x) x
  space_second_hasDerivAt :
    ∀ ⦃t x : ℝ⦄,
      0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
        HasDerivAt
          (fun y : ℝ => ShenWork.PDE.ParabolicMaxPrinciple.dx u t y)
          (ShenWork.PDE.ParabolicMaxPrinciple.dxx u t x) x
  pde_ge :
    ∀ ⦃t x : ℝ⦄,
      0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
        0 ≤ neumannLinearDriftResidual B C u t x
  neumann :
    ∀ t, 0 < t → t < T →
      ShenWork.PDE.ParabolicMaxPrinciple.dx u t 0 = 0 ∧
        ShenWork.PDE.ParabolicMaxPrinciple.dx u t 1 = 0
  bounded : BoundedOnIntervalStrip T u

/-- Build the subsolution package once the analytic regularity and residual
inequality have both been supplied. -/
def NeumannLinearDriftSubSolutionRegularity.toSubSolution
    {T : ℝ} {B C w : ℝ → ℝ → ℝ}
    (hreg : NeumannLinearDriftSubSolutionRegularity T B C w)
    (hpde :
      ∀ ⦃t x : ℝ⦄,
        0 < t → t < T → x ∈ Set.Ioo (0 : ℝ) 1 →
          neumannLinearDriftResidual B C w t x ≤ 0) :
    IsClassicalNeumannLinearDriftSubSolution T B C w where
  continuousOn_rect := hreg.continuousOn_rect
  time_hasDerivAt := hreg.time_hasDerivAt
  space_hasDerivAt := hreg.space_hasDerivAt
  space_second_hasDerivAt := hreg.space_second_hasDerivAt
  neumann := hreg.neumann
  bounded := hreg.bounded
  pde_le := hpde

/-- Regular, non-bare Neumann comparison interface for the interval
drift-reaction equation. -/
def NeumannLinearDriftComparisonRegular
    (T : ℝ) (B C : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ)
    (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ w : ℝ → ℝ → ℝ,
    0 < T →
    NeumannLinearDriftCoefficientsRegular T B C →
    IsClassicalNeumannLinearDriftSuperSolution T B C u →
    (∀ x ∈ Set.Icc (0 : ℝ) 1, u 0 x = u₀ x) →
    IsClassicalNeumannLinearDriftSubSolution T B C w →
    (∀ x ∈ Set.Icc (0 : ℝ) 1, w 0 x ≤ u₀ x) →
    ∀ t x, 0 < t → t < T → x ∈ Set.Icc (0 : ℝ) 1 →
      w t x ≤ u t x

/-- The exact data an even-reflection reduction would have to produce in order
to use the existing whole-line tree comparison theorem. -/
structure EvenReflectionTreeComparisonData
    (T : ℝ) (_B _C : ℝ → ℝ → ℝ) (_u₀ : ℝ → ℝ)
    (u w : ℝ → ℝ → ℝ) : Type where
  g : ℝ → ℝ
  uRef : ℝ → ℝ → ℝ
  wRef : ℝ → ℝ → ℝ
  hg : ShenWork.PDE.ParabolicMaxPrinciple.LocallyLipschitzReal g
  hsub : ShenWork.PDE.ParabolicMaxPrinciple.IsClassicalSubSolution g T wRef
  hsuper : ShenWork.PDE.ParabolicMaxPrinciple.IsClassicalSuperSolution g T uRef
  hinit : ∀ x : ℝ, wRef 0 x ≤ uRef 0 x
  restrict_w :
    ∀ t x, t ∈ Set.Icc (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
      wRef t x = w t x
  restrict_u :
    ∀ t x, t ∈ Set.Icc (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
      uRef t x = u t x

/-- Once the reflected whole-line sub/super-solution data exists, the interval
comparison follows directly from the tree comparison principle. -/
theorem comparison_on_interval_of_evenReflectionTreeComparisonData
    {T : ℝ} {B C : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u w : ℝ → ℝ → ℝ}
    (hT : 0 < T)
    (hdata : EvenReflectionTreeComparisonData T B C u₀ u w) :
    ∀ t x, 0 ≤ t → t ≤ T → x ∈ Set.Icc (0 : ℝ) 1 →
      w t x ≤ u t x := by
  intro t x ht0 htT hx
  have ht : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0, htT⟩
  have hline :
      hdata.wRef t x ≤ hdata.uRef t x :=
    ShenWork.PDE.ParabolicMaxPrinciple.comparison_principle
      (g := hdata.g) (T := T) (u := hdata.wRef) (v := hdata.uRef)
      hT hdata.hg hdata.hsub hdata.hsuper hdata.hinit t ht x
  simpa [hdata.restrict_w t x ht hx, hdata.restrict_u t x ht hx] using hline

/-- Conditional closure of the regular comparison from a genuine even-reflection
bridge into the tree theorem. -/
theorem NeumannLinearDriftComparisonRegular.of_evenReflectionTreeData
    {T : ℝ} {B C : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ}
    (hreflect :
      ∀ w : ℝ → ℝ → ℝ,
        NeumannLinearDriftCoefficientsRegular T B C →
        IsClassicalNeumannLinearDriftSuperSolution T B C u →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, u 0 x = u₀ x) →
        IsClassicalNeumannLinearDriftSubSolution T B C w →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, w 0 x ≤ u₀ x) →
          EvenReflectionTreeComparisonData T B C u₀ u w) :
    NeumannLinearDriftComparisonRegular T B C u₀ u := by
  intro w hT hcoeff hsuper hinit_u hsub hinit_w t x ht0 htT hx
  exact
    comparison_on_interval_of_evenReflectionTreeComparisonData
      (T := T) (B := B) (C := C) (u₀ := u₀) (u := u) (w := w)
      hT (hreflect w hcoeff hsuper hinit_u hsub hinit_w)
      t x (le_of_lt ht0) (le_of_lt htT) hx

/-- The reflected drift-reaction right hand side still depends on the spatial
derivative of the reflected solution. -/
def reflectedDriftReactionRHS (b c value slope : ℝ) : ℝ :=
  b * slope + c * value

/-- A nonzero drift coefficient cannot be absorbed into a reaction term that
depends only on the solution value. -/
theorem no_reaction_absorbs_nonzero_drift_at_fixed_value
    {b c value : ℝ} (hb : b ≠ 0) :
    ¬ ∃ g : ℝ → ℝ,
      ∀ slope : ℝ, reflectedDriftReactionRHS b c value slope = g value := by
  rintro ⟨g, hg⟩
  have h0 := hg 0
  have h1 := hg 1
  have hb0 : b = 0 := by
    unfold reflectedDriftReactionRHS at h0 h1
    linarith
  exact hb hb0

end ShenWork.Paper2.BFormPositiveDatumNegPart
