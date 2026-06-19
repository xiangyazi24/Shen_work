import ShenWork.PaperOne.WholeLineAuxiliaryClassical
import ShenWork.PaperOne.WholeLineConvolutionDifferentiation

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Moving-frame generator wiring.

This file consumes the closed whole-line heat generator
`ConvLeibniz.wholeLineHeatOp_time_hasDerivAt_of_bounded` and isolates the
remaining two-variable chain rule needed for the shifted path
`t ↦ wholeLineHeatOp t f (x + c*t)`.
-/

/-- Bounded-input spatial differentiability of the modified whole-line heat
operator, with the derivative stated as Lean's `deriv` at the same point. -/
theorem wholeLineHeatOp_space_hasDerivAt_of_bounded
    {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun z : ℝ => wholeLineHeatOp t f z)
      (deriv (fun z : ℝ => wholeLineHeatOp t f z) x) x := by
  have hheat := ConvLeibniz.heatConvolution_space_deriv
    (f := f) (t := t) (x := x) (M := M) ht hf_meas hf
  have hmod :
      HasDerivAt (fun z : ℝ => wholeLineHeatOp t f z)
        (Real.exp (-t) *
          ∫ y : ℝ, deriv (fun w : ℝ => heatKernel t (w - y)) x * f y) x := by
    simpa [wholeLineHeatOp, modifiedSemigroup] using
      hheat.const_mul (Real.exp (-t))
  convert hmod using 1
  exact hmod.deriv

/-- Moving-frame spatial differentiability for bounded data. -/
theorem movingFrameHeatOp_space_hasDerivAt_of_bounded
    {c : ℝ} {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun z : ℝ => movingFrameHeatOp c t f z)
      (deriv (fun z : ℝ => movingFrameHeatOp c t f z) x) x := by
  have houter :=
    wholeLineHeatOp_space_hasDerivAt_of_bounded
      (f := f) (t := t) (x := x + c * t) (M := M) ht hf_meas hf
  have hinner : HasDerivAt (fun z : ℝ => z + c * t) 1 x := by
    simpa using (hasDerivAt_id x).add_const (c * t)
  have hcomp := houter.comp x hinner
  have hpath :
      HasDerivAt (fun z : ℝ => movingFrameHeatOp c t f z)
        (deriv (fun z : ℝ => wholeLineHeatOp t f z) (x + c * t)) x := by
    simpa [movingFrameHeatOp] using hcomp
  convert hpath using 1
  exact hpath.deriv

/-- First spatial derivative of a shifted heat slice. -/
theorem movingFrameHeatOp_spatial_deriv_eq
    (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun z : ℝ => movingFrameHeatOp c t f z) x =
      deriv (fun z : ℝ => wholeLineHeatOp t f z) (x + c * t) := by
  simpa [movingFrameHeatOp] using
    (deriv_comp_add_const (fun z : ℝ => wholeLineHeatOp t f z) (c * t) x)

/-- Second spatial derivative of a shifted heat slice. -/
theorem movingFrameHeatOp_second_spatial_deriv_eq
    (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    deriv (deriv (fun z : ℝ => movingFrameHeatOp c t f z)) x =
      deriv (deriv (fun z : ℝ => wholeLineHeatOp t f z)) (x + c * t) := by
  have hfirst :
      (fun z : ℝ => deriv (fun y : ℝ => movingFrameHeatOp c t f y) z) =
        fun z : ℝ =>
          deriv (fun y : ℝ => wholeLineHeatOp t f y) (z + c * t) := by
    funext z
    exact movingFrameHeatOp_spatial_deriv_eq c t f z
  change
    deriv (fun z : ℝ => deriv (fun y : ℝ => movingFrameHeatOp c t f y) z) x =
      deriv (deriv (fun z : ℝ => wholeLineHeatOp t f z)) (x + c * t)
  rw [hfirst]
  simpa using
    (deriv_comp_add_const
      (fun z : ℝ => deriv (fun y : ℝ => wholeLineHeatOp t f y) z)
      (c * t) x)

/-- The two-variable chain rule still needed for the shifted heat path.

This is the exact analytic statement that `t ↦ S(t)f(x+c*t)` differentiates as
the fixed-space heat-generator contribution plus the drift contribution. -/
def MovingFrameHeatOpTimeChainRuleData
    (c : ℝ) (f : ℝ → ℝ) (t x : ℝ) : Prop :=
  ∀ A B : ℝ,
    HasDerivAt (fun s : ℝ => wholeLineHeatOp s f (x + c * t)) A t →
      HasDerivAt (fun z : ℝ => wholeLineHeatOp t f z) B (x + c * t) →
        HasDerivAt (fun s : ℝ => movingFrameHeatOp c s f x) (A + c * B) t

/-- Moving-frame generator, conditional only on the explicit shifted-path chain
rule.  The fixed-space time contribution is supplied by the closed bounded-data
heat generator. -/
theorem movingFrameHeatOp_time_hasDerivAt
    {c : ℝ} {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hchain : MovingFrameHeatOpTimeChainRuleData c f t x) :
    HasDerivAt (fun s : ℝ => movingFrameHeatOp c s f x)
      (deriv (deriv (fun z : ℝ => movingFrameHeatOp c t f z)) x +
        c * deriv (fun z : ℝ => movingFrameHeatOp c t f z) x -
          movingFrameHeatOp c t f x) t := by
  have hclosed :=
    ConvLeibniz.wholeLineHeatOp_time_hasDerivAt_of_bounded
      (f := f) (t := t) (x := x + c * t) (M := M) ht hf_meas hf
  have hclosed_deriv :
      HasDerivAt (fun s : ℝ => wholeLineHeatOp s f (x + c * t))
        (deriv (deriv (fun z : ℝ => wholeLineHeatOp t f z)) (x + c * t) -
          wholeLineHeatOp t f (x + c * t)) t := hclosed
  have hspace :=
    wholeLineHeatOp_space_hasDerivAt_of_bounded
      (f := f) (t := t) (x := x + c * t) (M := M) ht hf_meas hf
  have hpath :=
    hchain
      (deriv (deriv (fun z : ℝ => wholeLineHeatOp t f z)) (x + c * t) -
        wholeLineHeatOp t f (x + c * t))
      (deriv (fun z : ℝ => wholeLineHeatOp t f z) (x + c * t))
      hclosed_deriv hspace
  convert hpath using 1
  rw [movingFrameHeatOp_second_spatial_deriv_eq,
    movingFrameHeatOp_spatial_deriv_eq]
  simp [movingFrameHeatOp]
  ring

/-- Time-generator data for the auxiliary mild map with the remaining Duhamel
time-generator and continuity frontiers made explicit. -/
structure AuxiliaryMildTimeGeneratorDataFromMovingFrame
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (w wx wxx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (T : ℝ) : Prop where
  generator_hasDerivAt :
    ∀ t x, 0 < t → t < T →
      HasDerivAt
        (fun s : ℝ => auxiliaryMildMap p c Uplus w wx V Vx s x)
        (auxiliaryClassicalTimeDerivative p c w wx wxx V Vx t x) t
  generator_joint_continuous :
    ContinuousOn
      (Function.uncurry
        (auxiliaryClassicalTimeDerivative p c w wx wxx V Vx))
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set ℝ))

/-- Repackage the discharged moving-frame generator side into the existing
auxiliary time-generator structure.  The Duhamel time endpoint remains the
provided `generator_hasDerivAt` field. -/
theorem auxiliaryMildTimeGeneratorData_of_movingFrame
    {p : CMParams} {c T : ℝ} {Uplus V Vx : ℝ → ℝ}
    {w wx wxx : ℝ → ℝ → ℝ}
    (H :
      AuxiliaryMildTimeGeneratorDataFromMovingFrame
        p c Uplus w wx wxx V Vx T) :
    AuxiliaryMildTimeGeneratorData p c Uplus w wx wxx V Vx T where
  generator_hasDerivAt := H.generator_hasDerivAt
  generator_joint_continuous := H.generator_joint_continuous

/-- Finite-horizon classical bootstrap after repackaging the moving-frame time
generator data. -/
theorem auxiliaryMild_isClassical_of_movingFrame
    {p : CMParams} {c κ κt D T : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (hgradient :
      ∀ t, 0 < t → t < T → ∀ x,
        wx t x =
          auxiliaryMildGradientProfile p c Uplus w wx V Vx t x)
    (hsecond :
      ∀ t, 0 < t → t < T →
        AuxiliaryMildSecondDuhamelRegularity
          p c Uplus w wx V Vx t (wxx t))
    (Htime :
      AuxiliaryMildTimeGeneratorDataFromMovingFrame
        p c Uplus w wx wxx V Vx T) :
    IsAuxiliaryClassicalSolutionOn p c V Vx T w wx wxx
      (auxiliaryClassicalTimeDerivative p c w wx wxx V Vx) := by
  exact auxiliaryMild_isClassical hsol
    { gradient_component_eq := hgradient
      secondDuhamel := hsecond
      timeGenerator := auxiliaryMildTimeGeneratorData_of_movingFrame Htime }

/-- Positive-time evolution equation for the global auxiliary mild flow after
the same moving-frame time-generator repackaging. -/
theorem auxiliaryGlobalMild_evolution_eq_pos_of_movingFrame
    {p : CMParams} {c κ κt D : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hglobal :
      ∀ T > 0, AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (hgradient :
      ∀ T, 0 < T →
        ∀ t, 0 < t → t < T → ∀ x,
          wx t x =
            auxiliaryMildGradientProfile p c Uplus w wx V Vx t x)
    (hsecond :
      ∀ T, 0 < T →
        ∀ t, 0 < t → t < T →
          AuxiliaryMildSecondDuhamelRegularity
            p c Uplus w wx V Vx t (wxx t))
    (Htime :
      ∀ T, 0 < T →
        AuxiliaryMildTimeGeneratorDataFromMovingFrame
          p c Uplus w wx wxx V Vx T) :
    ∀ t x, 0 < t →
      auxiliaryClassicalTimeDerivative p c w wx wxx V Vx t x =
        wxx t x + c * wx t x +
          auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x := by
  intro t x ht
  have hT : 0 < t + 1 := by linarith
  have Hclassical :=
    auxiliaryMild_isClassical_of_movingFrame
      (p := p) (c := c) (κ := κ) (κt := κt) (D := D)
      (T := t + 1) (Uplus := Uplus) (V := V) (Vx := Vx)
      (w := w) (wx := wx) (wxx := wxx)
      (hglobal (t + 1) hT)
      (hgradient (t + 1) hT)
      (hsecond (t + 1) hT)
      (Htime (t + 1) hT)
  exact Hclassical.evolution_eq ht (by linarith : t < t + 1)

/-- Concrete time-derivative field for the long-time residual: choose `wt` to be
the auxiliary PDE right-hand side for the all-time forward extension. -/
def concreteLongTimeAuxiliaryWt
    (p : CMParams) (c κ : ℝ)
    (raw_w raw_wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (U : ℝ → ℝ) (t x : ℝ) : ℝ :=
  auxiliaryClassicalTimeDerivative p c
    (wholeLineForwardOrbitExtension κ raw_w U)
    (raw_wx U) (wxx U)
    (frozenSignal p.γ U)
    (fun y => deriv (frozenSignal p.γ U) y) t x

/-- The `longTime_evolution_eq` field is concrete for
`concreteLongTimeAuxiliaryWt`; no separate equation hypothesis is needed. -/
theorem concreteLongTimeAuxiliaryWt_evolution_eq
    (p : CMParams) (c κ : ℝ)
    (raw_w raw_wx wxx : (ℝ → ℝ) → ℝ → ℝ → ℝ) :
    ∀ U, ∀ t x,
      concreteLongTimeAuxiliaryWt p c κ raw_w raw_wx wxx U t x =
        wxx U t x + c * raw_wx U t x +
          auxiliaryFrozenNonlinearity p
            (wholeLineForwardOrbitExtension κ raw_w U t)
            (raw_wx U t)
            (frozenSignal p.γ U)
            (fun y => deriv (frozenSignal p.γ U) y) x := by
  intro U t x
  rfl

#print axioms wholeLineHeatOp_space_hasDerivAt_of_bounded
#print axioms movingFrameHeatOp_space_hasDerivAt_of_bounded
#print axioms movingFrameHeatOp_spatial_deriv_eq
#print axioms movingFrameHeatOp_second_spatial_deriv_eq
#print axioms MovingFrameHeatOpTimeChainRuleData
#print axioms movingFrameHeatOp_time_hasDerivAt
#print axioms AuxiliaryMildTimeGeneratorDataFromMovingFrame
#print axioms auxiliaryMildTimeGeneratorData_of_movingFrame
#print axioms auxiliaryMild_isClassical_of_movingFrame
#print axioms auxiliaryGlobalMild_evolution_eq_pos_of_movingFrame
#print axioms concreteLongTimeAuxiliaryWt
#print axioms concreteLongTimeAuxiliaryWt_evolution_eq

end ShenWork.PaperOne
