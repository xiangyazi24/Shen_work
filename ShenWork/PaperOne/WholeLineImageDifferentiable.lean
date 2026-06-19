import ShenWork.PaperOne.WholeLineDuhamelDifferentiation
import ShenWork.PaperOne.WholeLineAuxiliaryExistence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

/-!
Long-time image differentiability from the finite-time Leibniz bridge.

The finite-time part consumes the Duhamel differentiation bridge.  The
long-time passage uses Mathlib's uniform-limit theorem for derivatives, so it
keeps the necessary derivative local-uniform convergence as an explicit input.
A uniform derivative bound alone only gives a Lipschitz limit, not
differentiability of the limit.
-/

/-- A finite-horizon auxiliary mild solution inherits the spatial derivative
formula supplied by the Leibniz bridge. -/
theorem auxiliaryMildSolutionOn_hasDerivAt_of_duhamel_bridge
    {p : CMParams} {c kappa kappat D T t x : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx kappa kappat D T W Wx)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hinit_deriv :
      ∀ x,
        HasDerivAt
          (fun y : ℝ => movingFrameHeatOp c t Uplus y)
          (movingFrameHeatGradOp c t Uplus x) x)
    (hduh_deriv :
      ∀ x,
        HasDerivAt
          (fun y : ℝ => auxiliaryDuhamel p c W Wx V Vx t y)
          (auxiliaryGradDuhamel p c W Wx V Vx t x) x) :
    HasDerivAt
      (fun y : ℝ => W t y)
      (movingFrameHeatGradOp c t Uplus x +
        auxiliaryGradDuhamel p c W Wx V Vx t x) x := by
  have hw :
      (fun y : ℝ => W t y) =
        fun y : ℝ => auxiliaryMildMap p c Uplus W Wx V Vx t y := by
    funext y
    exact hsol.2.1 t ht y
  rw [hw]
  exact auxiliaryMildMap_hasDerivAt_of_duhamel_bridge
    (p := p) (c := c) (t := t) (x := x)
    (Uplus := Uplus) (W := W) (Wx := Wx) (V := V) (Vx := Vx)
    (hinit_deriv x) (hduh_deriv x)

/-- A finite-horizon auxiliary mild solution inherits the derivative bound
supplied by the Leibniz bridge. -/
theorem auxiliaryMildSolutionOn_deriv_abs_le_from_duhamel_bridge
    {p : CMParams} {c kappa kappat D T t B0 BD : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hsol : AuxiliaryMildSolutionOn p c Uplus V Vx kappa kappat D T W Wx)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hinit_deriv :
      ∀ x,
        HasDerivAt
          (fun y : ℝ => movingFrameHeatOp c t Uplus y)
          (movingFrameHeatGradOp c t Uplus x) x)
    (hduh_deriv :
      ∀ x,
        HasDerivAt
          (fun y : ℝ => auxiliaryDuhamel p c W Wx V Vx t y)
          (auxiliaryGradDuhamel p c W Wx V Vx t x) x)
    (hinit_bound : ∀ x, |movingFrameHeatGradOp c t Uplus x| ≤ B0)
    (hduh_bound : ∀ x, |auxiliaryGradDuhamel p c W Wx V Vx t x| ≤ BD) :
    ∀ x,
      |deriv (fun y : ℝ => W t y) x| ≤ B0 + BD := by
  intro x
  have hw :
      (fun y : ℝ => W t y) =
        fun y : ℝ => auxiliaryMildMap p c Uplus W Wx V Vx t y := by
    funext y
    exact hsol.2.1 t ht y
  rw [hw]
  exact auxiliaryMildMap_deriv_abs_le_from_duhamel_bridge
    (p := p) (c := c) (B0 := B0) (BD := BD) (t := t)
    (Uplus := Uplus) (W := W) (Wx := Wx) (V := V) (Vx := Vx)
    hinit_deriv hduh_deriv hinit_bound hduh_bound x

/-- A pointwise absolute bound passes to a locally-uniform limit. -/
theorem abs_le_of_tendstoLocallyUniformlyOn_of_uniform_abs_le
    {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {B : ℝ}
    (hlim : TendstoLocallyUniformlyOn fs f atTop (Set.univ : Set ℝ))
    (hbound : ∀ n x, |fs n x| ≤ B) :
    ∀ x, |f x| ≤ B := by
  intro x
  have hlim_abs :
      Tendsto (fun n : ℕ => |fs n x|) atTop (𝓝 |f x|) :=
    (continuous_abs.tendsto (f x)).comp
      (hlim.tendsto_at (Set.mem_univ x))
  exact le_of_tendsto' hlim_abs (fun n => hbound n x)

/-- Long-time `HasDerivAt` from finite-time derivatives and local-uniform
derivative convergence. -/
theorem longTime_image_hasDerivAt_of_bridge
    {w : (ℝ → ℝ) → ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {time : ℕ → ℝ} {dlim : ℝ → ℝ} {x : ℝ}
    (hderiv_loc :
      TendstoLocallyUniformlyOn
        (fun n y => deriv (w U (time n)) y) dlim atTop
        (Set.univ : Set ℝ))
    (hfinite_hasDeriv :
      ∀ n y, HasDerivAt (w U (time n))
        (deriv (w U (time n)) y) y)
    (hvalue :
      ∀ y, Tendsto (fun n : ℕ => w U (time n) y) atTop
        (𝓝 (longTimeMap w U y))) :
    HasDerivAt (longTimeMap w U) (dlim x) x := by
  refine
    hasDerivAt_of_tendstoLocallyUniformlyOn
      (𝕜 := ℝ) (l := atTop) (s := Set.univ)
      (f := fun n => w U (time n))
      (f' := fun n y => deriv (w U (time n)) y)
      (g := longTimeMap w U) (g' := dlim)
      isOpen_univ hderiv_loc ?_ ?_ (Set.mem_univ x)
  · exact Eventually.of_forall fun n y _hy => hfinite_hasDeriv n y
  · intro y _hy
    exact hvalue y

/--
The long-time image is differentiable once the finite-time bridge is available,
the finite-time values converge to the long-time map, and the finite-time
derivatives converge locally uniformly.
-/
theorem longTime_image_differentiable_of_bridge
    {kappa kappat D : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {time : (ℝ → ℝ) → ℕ → ℝ}
    {dlim : (ℝ → ℝ) → ℝ → ℝ}
    (hderiv_loc :
      ∀ U, U ∈ WaveTrap kappa kappat D →
        TendstoLocallyUniformlyOn
          (fun n x => deriv (w U (time U n)) x) (dlim U) atTop
          (Set.univ : Set ℝ))
    (hfinite_hasDeriv :
      ∀ U, U ∈ WaveTrap kappa kappat D →
        ∀ n x, HasDerivAt (w U (time U n))
          (deriv (w U (time U n)) x) x)
    (hvalue :
      ∀ U, U ∈ WaveTrap kappa kappat D →
        ∀ x, Tendsto (fun n : ℕ => w U (time U n) x) atTop
          (𝓝 (longTimeMap w U x))) :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap kappa kappat D) →
        ∀ n, Differentiable ℝ (longTimeMap w (seq n)) := by
  intro seq hseq n x
  exact
    (longTime_image_hasDerivAt_of_bridge
      (w := w) (U := seq n) (time := time (seq n))
      (dlim := dlim (seq n)) (x := x)
      (hderiv_loc (seq n) (hseq n))
      (hfinite_hasDeriv (seq n) (hseq n))
      (hvalue (seq n) (hseq n))).differentiableAt

/--
The derivative bound passes to the long-time image once the finite-time bridge
gives the uniform bound and the derivatives converge locally uniformly.
-/
theorem longTime_image_deriv_bound_of_bridge
    {kappa kappat D Lambda : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ}
    {time : (ℝ → ℝ) → ℕ → ℝ}
    {dlim : (ℝ → ℝ) → ℝ → ℝ}
    (hderiv_loc :
      ∀ U, U ∈ WaveTrap kappa kappat D →
        TendstoLocallyUniformlyOn
          (fun n x => deriv (w U (time U n)) x) (dlim U) atTop
          (Set.univ : Set ℝ))
    (hfinite_hasDeriv :
      ∀ U, U ∈ WaveTrap kappa kappat D →
        ∀ n x, HasDerivAt (w U (time U n))
          (deriv (w U (time U n)) x) x)
    (hfinite_bound :
      ∀ U, U ∈ WaveTrap kappa kappat D →
        ∀ n x, |deriv (w U (time U n)) x| ≤ Lambda)
    (hvalue :
      ∀ U, U ∈ WaveTrap kappa kappat D →
        ∀ x, Tendsto (fun n : ℕ => w U (time U n) x) atTop
          (𝓝 (longTimeMap w U x))) :
    ∀ seq : ℕ → ℝ → ℝ,
      (∀ n, seq n ∈ WaveTrap kappa kappat D) →
        ∀ n x, |deriv (longTimeMap w (seq n)) x| ≤ Lambda := by
  intro seq hseq n x
  have hhas :
      HasDerivAt (longTimeMap w (seq n)) (dlim (seq n) x) x :=
    longTime_image_hasDerivAt_of_bridge
      (w := w) (U := seq n) (time := time (seq n))
      (dlim := dlim (seq n)) (x := x)
      (hderiv_loc (seq n) (hseq n))
      (hfinite_hasDeriv (seq n) (hseq n))
      (hvalue (seq n) (hseq n))
  have hlim_bound : |dlim (seq n) x| ≤ Lambda :=
    abs_le_of_tendstoLocallyUniformlyOn_of_uniform_abs_le
      (hderiv_loc (seq n) (hseq n))
      (hfinite_bound (seq n) (hseq n)) x
  simpa [hhas.deriv] using hlim_bound

#print axioms auxiliaryMildSolutionOn_hasDerivAt_of_duhamel_bridge
#print axioms auxiliaryMildSolutionOn_deriv_abs_le_from_duhamel_bridge
#print axioms abs_le_of_tendstoLocallyUniformlyOn_of_uniform_abs_le
#print axioms longTime_image_hasDerivAt_of_bridge
#print axioms longTime_image_differentiable_of_bridge
#print axioms longTime_image_deriv_bound_of_bridge

end ShenWork.PaperOne
