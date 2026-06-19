import ShenWork.PaperOne.WholeLineDuhamelDifferentiation
import ShenWork.PaperOne.WholeLineProfileRegularity

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Auxiliary mild-to-classical bootstrap for the whole-line moving-frame problem.

This file mirrors the Paper-2 pattern: the already closed mild identity and
first spatial Duhamel bridge are separated from the remaining frontier data.
The two genuine analytic frontiers are:

* second spatial differentiation of the whole-line Duhamel term;
* the heat-semigroup generator identity in time for
  `e^{t(Δ+c∂x-I)}` and the corresponding Duhamel term.

No axiom, `sorry`, or `admit` is introduced here.
-/

/-- Pointwise right-hand side of the auxiliary parabolic equation (4.12). -/
def auxiliaryClassicalTimeDerivative (p : CMParams) (c : ℝ)
    (w wx wxx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  wxx t x + c * wx t x + auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x

/-- Classical solution predicate for the auxiliary whole-line equation on
`0 < t < T`.

The fields are pointwise: spatial `C²`, time differentiability with a jointly
continuous time-derivative representative, identification of the carried
`wx/wxx` fields with the actual spatial derivatives, and the PDE itself. -/
structure IsAuxiliaryClassicalSolutionOn
    (p : CMParams) (c : ℝ) (V Vx : ℝ → ℝ) (T : ℝ)
    (w wx wxx wt : ℝ → ℝ → ℝ) : Prop where
  hT_pos : 0 < T
  spatialC2 :
    ∀ t, 0 < t → t < T → ContDiff ℝ 2 (w t)
  timeDeriv :
    ∀ t x, 0 < t → t < T →
      HasDerivAt (fun s : ℝ => w s x) (wt t x) t
  timeDeriv_joint_continuous :
    ContinuousOn (Function.uncurry wt)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set ℝ))
  wx_eq_deriv :
    ∀ t x, 0 < t → t < T → wx t x = deriv (w t) x
  wxx_eq_second :
    ∀ t x, 0 < t → t < T → wxx t x = deriv (deriv (w t)) x
  pde :
    ∀ t x, 0 < t → t < T →
      wt t x =
        wxx t x + c * wx t x +
          auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x

namespace IsAuxiliaryClassicalSolutionOn

/-- Positive-time evolution equation extracted from the classical predicate. -/
theorem evolution_eq
    {p : CMParams} {c T : ℝ} {V Vx : ℝ → ℝ}
    {w wx wxx wt : ℝ → ℝ → ℝ}
    (H : IsAuxiliaryClassicalSolutionOn p c V Vx T w wx wxx wt)
    {t x : ℝ} (ht : 0 < t) (htT : t < T) :
    wt t x =
      wxx t x + c * wx t x +
        auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x :=
  H.pde t x ht htT

end IsAuxiliaryClassicalSolutionOn

/-- Time-generator frontier for the auxiliary mild map.

This is the hard semigroup-generator input:
`∂t Φ(t) = (Δ + c∂x - I) Φ(t) + frozenSource(t)`, after the spatial
second-derivative profile has been identified as `wxx`. -/
structure AuxiliaryMildTimeGeneratorData
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

/-- Frontier package left after the mild fixed-point equation is known.

`gradient_component_eq` is needed because `AuxiliaryMildSolutionOn` stores the
value fixed point but does not itself record that the carried `wx` component is
the gradient mild map. `secondDuhamel` is the second spatial Duhamel
differentiation frontier. `timeGenerator` is the generator-action frontier. -/
structure AuxiliaryMildClassicalFrontierData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (V Vx : ℝ → ℝ) (T : ℝ) (w wx wxx : ℝ → ℝ → ℝ) : Prop where
  gradient_component_eq :
    ∀ t, 0 < t → t < T → ∀ x,
      wx t x =
        auxiliaryMildGradientProfile p c Uplus w wx V Vx t x
  secondDuhamel :
    ∀ t, 0 < t → t < T →
      AuxiliaryMildSecondDuhamelRegularity
        p c Uplus w wx V Vx t (wxx t)
  timeGenerator :
    AuxiliaryMildTimeGeneratorData p c Uplus w wx wxx V Vx T

/-- Closed first-spatial-derivative bridge from the existing Duhamel
differentiation theorem plus continuity of the gradient profile. -/
theorem auxiliaryMildGradientDuhamelRegularity_of_bridges
    {p : CMParams} {c t : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hinit :
      ∀ x,
        HasDerivAt
          (fun y : ℝ => movingFrameHeatOp c t Uplus y)
          (movingFrameHeatGradOp c t Uplus x) x)
    (hduh :
      ∀ x,
        HasDerivAt
          (fun y : ℝ => auxiliaryDuhamel p c W Wx V Vx t y)
          (auxiliaryGradDuhamel p c W Wx V Vx t x) x)
    (hcont :
      Continuous (auxiliaryMildGradientProfile p c Uplus W Wx V Vx t)) :
    AuxiliaryMildGradientDuhamelRegularity p c Uplus W Wx V Vx t where
  hasDerivAt := by
    intro x
    simpa [auxiliaryMildSpatialSlice, auxiliaryMildGradientProfile] using
      auxiliaryMildMap_hasDerivAt_of_duhamel_bridge
        (p := p) (c := c) (t := t) (x := x)
        (Uplus := Uplus) (W := W) (Wx := Wx) (V := V) (Vx := Vx)
        (hinit x) (hduh x)
  continuous_gradient := hcont

private theorem auxiliaryMild_spatialSlice_eq
    {p : CMParams} {c κ κt D T t : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx : ℝ → ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (ht : 0 < t) (htT : t < T) :
    w t = auxiliaryMildSpatialSlice p c Uplus w wx V Vx t := by
  funext x
  exact hsol.2.1 t ⟨le_of_lt ht, le_of_lt htT⟩ x

theorem auxiliaryMild_spatialC2
    {p : CMParams} {c κ κt D T t : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (F : AuxiliaryMildClassicalFrontierData p c Uplus V Vx T w wx wxx)
    (ht : 0 < t) (htT : t < T) :
    ContDiff ℝ 2 (w t) := by
  have hslice :=
    auxiliaryMildSpatialSlice_contDiff_two_of_secondDuhamel
      (F.secondDuhamel t ht htT)
  rw [auxiliaryMild_spatialSlice_eq hsol ht htT]
  exact hslice

theorem auxiliaryMild_wx_eq_deriv
    {p : CMParams} {c κ κt D T t x : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (F : AuxiliaryMildClassicalFrontierData p c Uplus V Vx T w wx wxx)
    (ht : 0 < t) (htT : t < T) :
    wx t x = deriv (w t) x := by
  have hfun := auxiliaryMild_spatialSlice_eq hsol ht htT
  have hderiv_mild :=
    (F.secondDuhamel t ht htT).gradient.hasDerivAt x
  have hderiv_w :
      HasDerivAt (w t)
        (auxiliaryMildGradientProfile p c Uplus w wx V Vx t x) x := by
    simpa [hfun] using hderiv_mild
  calc
    wx t x = auxiliaryMildGradientProfile p c Uplus w wx V Vx t x :=
      F.gradient_component_eq t ht htT x
    _ = deriv (w t) x := hderiv_w.deriv.symm

theorem auxiliaryMild_wxx_eq_second
    {p : CMParams} {c κ κt D T t x : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (F : AuxiliaryMildClassicalFrontierData p c Uplus V Vx T w wx wxx)
    (ht : 0 < t) (htT : t < T) :
    wxx t x = deriv (deriv (w t)) x := by
  have hfun := auxiliaryMild_spatialSlice_eq hsol ht htT
  have hsecond_mild :=
    (F.secondDuhamel t ht htT).hasSecondDerivAt x
  have hsecond_w : HasDerivAt (deriv (w t)) (wxx t x) x := by
    simpa [hfun] using hsecond_mild
  exact hsecond_w.deriv.symm

theorem auxiliaryMild_time_hasDerivAt
    {p : CMParams} {c κ κt D T t x : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (F : AuxiliaryMildClassicalFrontierData p c Uplus V Vx T w wx wxx)
    (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun s : ℝ => w s x)
      (auxiliaryClassicalTimeDerivative p c w wx wxx V Vx t x) t := by
  have hgen := F.timeGenerator.generator_hasDerivAt t x ht htT
  refine hgen.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds isOpen_Ioo ⟨ht, htT⟩] with s hs
  exact hsol.2.1 s ⟨le_of_lt hs.1, le_of_lt hs.2⟩ x

/-- Main finite-horizon mild-to-classical bootstrap.

All already formalized pieces are consumed here. The remaining analytic gaps are
exactly the fields of `AuxiliaryMildClassicalFrontierData`. -/
theorem auxiliaryMild_isClassical
    {p : CMParams} {c κ κt D T : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (F : AuxiliaryMildClassicalFrontierData p c Uplus V Vx T w wx wxx) :
    IsAuxiliaryClassicalSolutionOn p c V Vx T w wx wxx
      (auxiliaryClassicalTimeDerivative p c w wx wxx V Vx) where
  hT_pos := hsol.1
  spatialC2 := by
    intro t ht htT
    exact auxiliaryMild_spatialC2 hsol F ht htT
  timeDeriv := by
    intro t x ht htT
    exact auxiliaryMild_time_hasDerivAt hsol F ht htT
  timeDeriv_joint_continuous :=
    F.timeGenerator.generator_joint_continuous
  wx_eq_deriv := by
    intro t x ht htT
    exact auxiliaryMild_wx_eq_deriv hsol F ht htT
  wxx_eq_second := by
    intro t x ht htT
    exact auxiliaryMild_wxx_eq_second hsol F ht htT
  pde := by
    intro t x ht htT
    rfl

/-- Global frontier data: the finite-horizon frontier package is available on
every positive horizon. -/
def AuxiliaryGlobalMildClassicalFrontierData
    (p : CMParams) (c : ℝ) (Uplus : ℝ → ℝ)
    (V Vx : ℝ → ℝ) (w wx wxx : ℝ → ℝ → ℝ) : Prop :=
  ∀ T, 0 < T →
    AuxiliaryMildClassicalFrontierData p c Uplus V Vx T w wx wxx

/-- Global positive-time bootstrap, obtained by applying the finite-horizon
bootstrap on each `[0,T]`. -/
theorem auxiliaryGlobalMild_isClassical
    {p : CMParams} {c κ κt D : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hglobal :
      ∀ T > 0, AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (F : AuxiliaryGlobalMildClassicalFrontierData p c Uplus V Vx w wx wxx) :
    ∀ T > 0,
      IsAuxiliaryClassicalSolutionOn p c V Vx T w wx wxx
        (auxiliaryClassicalTimeDerivative p c w wx wxx V Vx) := by
  intro T hT
  exact auxiliaryMild_isClassical (hglobal T hT) (F T hT)

/-- The positive-time evolution equation in the all-horizon form needed by the
long-time route. The current whole-line residual asks for an all-`t` statement;
this theorem supplies the genuine classical statement on `t > 0`. -/
theorem auxiliaryGlobalMild_evolution_eq_pos
    {p : CMParams} {c κ κt D : ℝ}
    {Uplus V Vx : ℝ → ℝ} {w wx wxx : ℝ → ℝ → ℝ}
    (hglobal :
      ∀ T > 0, AuxiliaryMildSolutionOn p c Uplus V Vx κ κt D T w wx)
    (F : AuxiliaryGlobalMildClassicalFrontierData p c Uplus V Vx w wx wxx) :
    ∀ t x, 0 < t →
      auxiliaryClassicalTimeDerivative p c w wx wxx V Vx t x =
        wxx t x + c * wx t x +
          auxiliaryFrozenNonlinearity p (w t) (wx t) V Vx x := by
  intro t x ht
  have hT : 0 < t + 1 := by linarith
  have H :=
    (auxiliaryGlobalMild_isClassical
      (p := p) (c := c) (κ := κ) (κt := κt) (D := D)
      (Uplus := Uplus) (V := V) (Vx := Vx)
      (w := w) (wx := wx) (wxx := wxx) hglobal F)
      (t + 1) hT
  exact H.evolution_eq ht (by linarith : t < t + 1)

#print axioms auxiliaryClassicalTimeDerivative
#print axioms IsAuxiliaryClassicalSolutionOn.evolution_eq
#print axioms auxiliaryMildGradientDuhamelRegularity_of_bridges
#print axioms auxiliaryMild_spatialC2
#print axioms auxiliaryMild_wx_eq_deriv
#print axioms auxiliaryMild_wxx_eq_second
#print axioms auxiliaryMild_time_hasDerivAt
#print axioms auxiliaryMild_isClassical
#print axioms auxiliaryGlobalMild_isClassical
#print axioms auxiliaryGlobalMild_evolution_eq_pos

end ShenWork.PaperOne
