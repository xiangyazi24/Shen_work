import ShenWork.PaperOne.WholeLineAuxiliaryMildMap
import ShenWork.PaperOne.WholeLineLongTimeMap
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.Paper1.WaveRotheC1
import Mathlib.Topology.MetricSpace.UniformConvergence

open MeasureTheory Filter Topology Real Set
open scoped Topology
open intervalIntegral

noncomputable section

namespace ShenWork.PaperOne

/-!
This file isolates the part of Shen Claim 1 that is already formalizable from
the banked layer-1 estimates:

* the whole-line modified heat-gradient kernel maps a bounded source to a
  pointwise `t^{-1/2}` bound;
* an abstract Duhamel integrand satisfying that `t^{-1/2}` bound has a
  `2√t` gradient-Duhamel bound;
* a uniform spatial derivative bound gives equicontinuity on compact sets, and
  hence the `LongTimeMapParabolicEquicontinuity` interface.

The genuinely missing analytic bridge is the Leibniz/differentiation theorem
identifying the spatial derivative of the auxiliary value-Duhamel term with the
gradient-kernel Duhamel integral below.
-/

/-- Moving-frame gradient heat operator, i.e. the translated
`∂ₓ e^{t(Δ-I)}` kernel. -/
def movingFrameHeatGradOp (c t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  wholeLineHeatGradOp t f (x + c * t)

/-- Gradient-form moving-frame Duhamel integral.  This is the integrand-level
object; identifying it with the derivative of `movingFrameDuhamel` is the
separate Leibniz-under-the-singular-integral bridge. -/
def movingFrameGradDuhamel (c : ℝ) (F : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, movingFrameHeatGradOp c (t - s) (F s) x

/-- Auxiliary frozen-source gradient Duhamel term. -/
def auxiliaryGradDuhamel (p : CMParams) (c : ℝ)
    (W Wx : ℝ → ℝ → ℝ) (V Vx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  movingFrameGradDuhamel c
    (fun s y => auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y) t x

/-- Layer-1 whole-line modified heat-gradient bound for bounded inputs, in the
kernel-gradient form that does not require the input itself to be `L¹`. -/
theorem wholeLineHeatGradOp_abs_le {f : ℝ → ℝ} {M t : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |wholeLineHeatGradOp t f x| ≤
      Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) := by
  simpa [wholeLineHeatGradOp] using
    modifiedHeatKernel_deriv_convolution_bounded_abs_le
      (t := t) (M := M) ht hM (f := f) hf x

/-- Moving-frame version of the layer-1 heat-gradient bound. -/
theorem movingFrameHeatGradOp_abs_le {c : ℝ} {f : ℝ → ℝ} {M t : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |movingFrameHeatGradOp c t f x| ≤
      Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) := by
  simpa [movingFrameHeatGradOp] using
    wholeLineHeatGradOp_abs_le (t := t) (M := M) ht hM hf (x + c * t)

/-- Duhamel absorption of an abstract layer-1 gradient bound.  If the
gradient-Duhamel integrand is bounded pointwise by
`A · (t-s)^(-1/2)` away from the endpoint, then its interval integral is bounded
by `A · 2√t`. -/
theorem movingFrameGradDuhamel_abs_le_sqrt_of_slice_bound
    {c A t : ℝ} {F : ℝ → ℝ → ℝ} (ht : 0 < t) (x : ℝ)
    (hgrad_int : IntervalIntegrable
      (fun s : ℝ => movingFrameHeatGradOp c (t - s) (F s) x) volume 0 t)
    (hslice :
      ∀ s, 0 ≤ s → s < t →
        |movingFrameHeatGradOp c (t - s) (F s) x| ≤
          A * (t - s) ^ (-(1 / 2 : ℝ))) :
    |movingFrameGradDuhamel c F t x| ≤ A * (2 * Real.sqrt t) := by
  have hdom_int : IntervalIntegrable
      (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul A
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hae :
      (fun s : ℝ => |movingFrameHeatGradOp c (t - s) (F s) x|)
        ≤ᵐ[volume.restrict (Set.Icc 0 t)]
      (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [hne] with s hs_ne hs_mem
    exact hslice s hs_mem.1 (lt_of_le_of_ne hs_mem.2 hs_ne)
  calc
    |movingFrameGradDuhamel c F t x|
        = |∫ s in (0 : ℝ)..t, movingFrameHeatGradOp c (t - s) (F s) x| := rfl
    _ ≤ ∫ s in (0 : ℝ)..t, |movingFrameHeatGradOp c (t - s) (F s) x| :=
        intervalIntegral.abs_integral_le_integral_abs ht.le
    _ ≤ ∫ s in (0 : ℝ)..t, A * (t - s) ^ (-(1 / 2 : ℝ)) :=
        intervalIntegral.integral_mono_ae_restrict ht.le hgrad_int.abs hdom_int hae
    _ = A * (2 * Real.sqrt t) := by
        rw [intervalIntegral.integral_const_mul,
          ShenWork.IntervalGradDuhamelBound.integral_sub_rpow_neg_half ht.le]

/-- Auxiliary frozen-source version of the abstract gradient-Duhamel bound. -/
theorem auxiliaryGradDuhamel_abs_le_sqrt_of_slice_bound
    {p : CMParams} {c A t : ℝ} {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (ht : 0 < t) (x : ℝ)
    (hgrad_int : IntervalIntegrable
      (fun s : ℝ => movingFrameHeatGradOp c (t - s)
        (fun y => auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y) x) volume 0 t)
    (hslice :
      ∀ s, 0 ≤ s → s < t →
        |movingFrameHeatGradOp c (t - s)
          (fun y => auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y) x| ≤
          A * (t - s) ^ (-(1 / 2 : ℝ))) :
    |auxiliaryGradDuhamel p c W Wx V Vx t x| ≤ A * (2 * Real.sqrt t) := by
  simpa [auxiliaryGradDuhamel] using
    movingFrameGradDuhamel_abs_le_sqrt_of_slice_bound
      (c := c) (A := A) (t := t)
      (F := fun s y => auxiliaryFrozenNonlinearity p (W s) (Wx s) V Vx y)
      ht x hgrad_int hslice

/-- If the auxiliary mild map has the expected differentiated mild
representation, then separately bounded initial and Duhamel gradient legs give
the advertised pointwise gradient bound. -/
theorem auxiliaryMildMap_deriv_abs_le_of_gradient_bounds
    {p : CMParams} {c B0 BD t : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hinit : ∀ x, |movingFrameHeatGradOp c t Uplus x| ≤ B0)
    (hduh : ∀ x, |auxiliaryGradDuhamel p c W Wx V Vx t x| ≤ BD)
    (hrepr : ∀ x,
      deriv (fun z : ℝ => auxiliaryMildMap p c Uplus W Wx V Vx t z) x =
        movingFrameHeatGradOp c t Uplus x +
          auxiliaryGradDuhamel p c W Wx V Vx t x) :
    ∀ x, |deriv (fun z : ℝ => auxiliaryMildMap p c Uplus W Wx V Vx t z) x|
      ≤ B0 + BD := by
  intro x
  rw [hrepr x]
  calc
    |movingFrameHeatGradOp c t Uplus x +
        auxiliaryGradDuhamel p c W Wx V Vx t x|
        ≤ |movingFrameHeatGradOp c t Uplus x| +
            |auxiliaryGradDuhamel p c W Wx V Vx t x| := abs_add_le _ _
    _ ≤ B0 + BD := add_le_add (hinit x) (hduh x)

/-- A uniform derivative bound on a real family gives equicontinuity on every
subset, hence on every compact subset. -/
theorem equicontinuousOn_of_uniform_deriv_bound
    {ι : Type*} {F : ι → ℝ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hdiff : ∀ i, Differentiable ℝ (F i))
    (hderiv : ∀ i x, |deriv (F i) x| ≤ Λ) (K : Set ℝ) :
    EquicontinuousOn F K := by
  have hLip : ∀ i, LipschitzWith (Real.toNNReal Λ) (F i) := by
    intro i
    exact ShenWork.Paper1.crossImplicitStep_lipschitz hΛ (hdiff i) (hderiv i)
  exact
    (LipschitzWith.uniformEquicontinuous F (Real.toNNReal Λ) hLip).equicontinuous.equicontinuousOn K

/-- The `LongTimeMapParabolicEquicontinuity` field follows immediately from a
sequence-uniform derivative bound on the long-time images. -/
theorem longTimeMap_parabolic_equicontinuity_of_uniform_deriv_bound
    {κ κt D Λ : ℝ} {w : (ℝ → ℝ) → ℝ → ℝ → ℝ} (hΛ : 0 ≤ Λ)
    (hdiff :
      ∀ seq : ℕ → ℝ → ℝ, (∀ n, seq n ∈ WaveTrap κ κt D) →
        ∀ n, Differentiable ℝ (longTimeMap w (seq n)))
    (hderiv :
      ∀ seq : ℕ → ℝ → ℝ, (∀ n, seq n ∈ WaveTrap κ κt D) →
        ∀ n x, |deriv (longTimeMap w (seq n)) x| ≤ Λ) :
    LongTimeMapParabolicEquicontinuity κ κt D w := by
  intro seq hseq K _hK
  exact equicontinuousOn_of_uniform_deriv_bound hΛ
    (fun n => hdiff seq hseq n)
    (fun n x => hderiv seq hseq n x) K

#print axioms movingFrameHeatGradOp
#print axioms movingFrameGradDuhamel
#print axioms auxiliaryGradDuhamel
#print axioms wholeLineHeatGradOp_abs_le
#print axioms movingFrameHeatGradOp_abs_le
#print axioms movingFrameGradDuhamel_abs_le_sqrt_of_slice_bound
#print axioms auxiliaryGradDuhamel_abs_le_sqrt_of_slice_bound
#print axioms auxiliaryMildMap_deriv_abs_le_of_gradient_bounds
#print axioms equicontinuousOn_of_uniform_deriv_bound
#print axioms longTimeMap_parabolic_equicontinuity_of_uniform_deriv_bound

end ShenWork.PaperOne
