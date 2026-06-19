import ShenWork.PaperOne.WholeLineParabolicEquicontinuity
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

open MeasureTheory Filter Topology Real Set
open scoped Topology Interval
open intervalIntegral

noncomputable section

namespace ShenWork.PaperOne

/-!
Spatial differentiation under the whole-line Duhamel time integral.

The endpoint `s = t` is the only singular point.  All dominated hypotheses below
are stated on the interval integral measure, so Mathlib discards that singleton
through the usual `uIoc`/a.e. convention.
-/

/-- Whole-line value Duhamel term for a time-dependent source. -/
def wholeLineValueDuhamel (t : ℝ) (F : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, wholeLineHeatOp (t - s) (F s) x

/-- Whole-line gradient Duhamel term for a time-dependent source. -/
def wholeLineGradientDuhamel (t : ℝ) (F : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, wholeLineHeatGradOp (t - s) (F s) x

/-- Algebraic rewrite of the one-dimensional heat-gradient constant. -/
lemma two_div_sqrt_four_pi_mul_eq_rpow {τ : ℝ} (hτ : 0 < τ) :
    2 / Real.sqrt (4 * Real.pi * τ) =
      (2 / Real.sqrt (4 * Real.pi)) * τ ^ (-(1 / 2 : ℝ)) := by
  have h4pi : 0 < 4 * Real.pi := by positivity
  have hsqrt4pi : Real.sqrt (4 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr h4pi)
  have hsqrtt : Real.sqrt τ ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hτ)
  rw [show 4 * Real.pi * τ = (4 * Real.pi) * τ by ring,
    Real.sqrt_mul h4pi.le τ]
  rw [Real.rpow_neg hτ.le, Real.sqrt_eq_rpow]
  field_simp [hsqrt4pi, hsqrtt]
  rw [Real.sqrt_eq_rpow]

/--
Layer-1 whole-line gradient bound in the `τ^(-1/2)` form needed by Duhamel.
-/
theorem wholeLineHeatGradOp_norm_le_rpow {f : ℝ → ℝ} {M τ : ℝ}
    (hτ : 0 < τ) (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    ‖wholeLineHeatGradOp τ f x‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) * M) * τ ^ (-(1 / 2 : ℝ)) := by
  rw [Real.norm_eq_abs]
  have hbase := wholeLineHeatGradOp_abs_le (t := τ) (M := M) hτ hM hf x
  have hexp_le : Real.exp (-τ) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hinner_nonneg : 0 ≤ (2 / Real.sqrt (4 * Real.pi * τ)) * M := by
    positivity
  calc
    |wholeLineHeatGradOp τ f x|
        ≤ Real.exp (-τ) * ((2 / Real.sqrt (4 * Real.pi * τ)) * M) := hbase
    _ ≤ 1 * ((2 / Real.sqrt (4 * Real.pi * τ)) * M) :=
        mul_le_mul_of_nonneg_right hexp_le hinner_nonneg
    _ = ((2 / Real.sqrt (4 * Real.pi)) * M) * τ ^ (-(1 / 2 : ℝ)) := by
        rw [two_div_sqrt_four_pi_mul_eq_rpow hτ]
        ring

/-- Moving-frame version of `wholeLineHeatGradOp_norm_le_rpow`. -/
theorem movingFrameHeatGradOp_norm_le_rpow {c : ℝ} {f : ℝ → ℝ} {M τ : ℝ}
    (hτ : 0 < τ) (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    ‖movingFrameHeatGradOp c τ f x‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) * M) * τ ^ (-(1 / 2 : ℝ)) := by
  simpa [movingFrameHeatGradOp] using
    wholeLineHeatGradOp_norm_le_rpow
      (τ := τ) (M := M) (f := f) hτ hM hf (x + c * τ)

/-- Interval-integral form of the moving-frame value Duhamel term. -/
def movingFrameValueDuhamel (c : ℝ) (F : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, movingFrameHeatOp c (t - s) (F s) x

/-- The existing `Set.Icc` Duhamel definition agrees with the interval-integral form. -/
theorem movingFrameDuhamel_eq_movingFrameValueDuhamel
    {c t : ℝ} {F : ℝ → ℝ → ℝ} (ht : 0 ≤ t) (x : ℝ) :
    movingFrameDuhamel c F t x = movingFrameValueDuhamel c F t x := by
  unfold movingFrameDuhamel movingFrameValueDuhamel
  rw [intervalIntegral.integral_of_le ht, ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/--
Abstract dominated spatial-Leibniz bridge for the whole-line Duhamel term.

This is exactly Mathlib's dominated differentiation-under-the-integral theorem,
specialized to the Duhamel integrand.  Concrete wrappers below provide the
parabolic `(t-s)^(-1/2)` domination from `wholeLineHeatGradOp_abs_le`.
-/
theorem wholeLineDuhamel_hasDerivAt_of_dominated
    {t x₀ : ℝ} {F : ℝ → ℝ → ℝ} {s : Set ℝ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 x₀)
    (hF_meas :
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun r : ℝ => wholeLineHeatOp (t - r) (F r) x)
          (volume.restrict (Ι (0 : ℝ) t)))
    (hF_int :
      IntervalIntegrable
        (fun r : ℝ => wholeLineHeatOp (t - r) (F r) x₀) volume (0 : ℝ) t)
    (hF'_meas :
      AEStronglyMeasurable
        (fun r : ℝ => wholeLineHeatGradOp (t - r) (F r) x₀)
        (volume.restrict (Ι (0 : ℝ) t)))
    (h_bound :
      ∀ᵐ r ∂volume, r ∈ Ι (0 : ℝ) t →
        ∀ x ∈ s, ‖wholeLineHeatGradOp (t - r) (F r) x‖ ≤ bound r)
    (hbound_int : IntervalIntegrable bound volume (0 : ℝ) t)
    (h_diff :
      ∀ᵐ r ∂volume, r ∈ Ι (0 : ℝ) t →
        ∀ x ∈ s,
          HasDerivAt
            (fun y : ℝ => wholeLineHeatOp (t - r) (F r) y)
            (wholeLineHeatGradOp (t - r) (F r) x) x) :
    HasDerivAt
      (fun y : ℝ => wholeLineValueDuhamel t F y)
      (wholeLineGradientDuhamel t F x₀) x₀ := by
  simpa [wholeLineValueDuhamel, wholeLineGradientDuhamel] using
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := t)
      (F := fun x r => wholeLineHeatOp (t - r) (F r) x)
      (F' := fun x r => wholeLineHeatGradOp (t - r) (F r) x)
      (x₀ := x₀) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/--
The whole-line Duhamel spatial Leibniz bridge with the parabolic
`(t-s)^(-1/2)` dominating function.

The hypotheses `hgrad_bound` and `h_diff` are required only for `0 ≤ s < t`.
The proof converts them to the a.e. hypotheses of Mathlib's dominated Leibniz
rule, discarding the singular endpoint `s = t`.
-/
theorem wholeLineDuhamel_hasDerivAt
    {t x₀ A : ℝ} {F : ℝ → ℝ → ℝ} {s : Set ℝ}
    (ht : 0 < t) (hs : s ∈ 𝓝 x₀)
    (hF_meas :
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun r : ℝ => wholeLineHeatOp (t - r) (F r) x)
          (volume.restrict (Ι (0 : ℝ) t)))
    (hF_int :
      IntervalIntegrable
        (fun r : ℝ => wholeLineHeatOp (t - r) (F r) x₀) volume (0 : ℝ) t)
    (hF'_meas :
      AEStronglyMeasurable
        (fun r : ℝ => wholeLineHeatGradOp (t - r) (F r) x₀)
        (volume.restrict (Ι (0 : ℝ) t)))
    (hgrad_bound :
      ∀ r, 0 ≤ r → r < t →
        ∀ x ∈ s,
          ‖wholeLineHeatGradOp (t - r) (F r) x‖ ≤
            A * (t - r) ^ (-(1 / 2 : ℝ)))
    (h_diff :
      ∀ r, 0 ≤ r → r < t →
        ∀ x ∈ s,
          HasDerivAt
            (fun y : ℝ => wholeLineHeatOp (t - r) (F r) y)
            (wholeLineHeatGradOp (t - r) (F r) x) x) :
    HasDerivAt
      (fun y : ℝ => wholeLineValueDuhamel t F y)
      (wholeLineGradientDuhamel t F x₀) x₀ := by
  have hne : ∀ᵐ r : ℝ ∂volume, r ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  refine wholeLineDuhamel_hasDerivAt_of_dominated
    (t := t) (x₀ := x₀) (F := F) (s := s)
    (bound := fun r : ℝ => A * (t - r) ^ (-(1 / 2 : ℝ)))
    hs hF_meas hF_int hF'_meas ?h_bound ?hbound_int ?h_diff
  · filter_upwards [hne] with r hr_ne hr_mem x hx
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hr_mem
    exact hgrad_bound r hr_mem.1.le (lt_of_le_of_ne hr_mem.2 hr_ne) x hx
  · exact
      (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul A
  · filter_upwards [hne] with r hr_ne hr_mem x hx
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hr_mem
    exact h_diff r hr_mem.1.le (lt_of_le_of_ne hr_mem.2 hr_ne) x hx

/--
Bounded-source version of `wholeLineDuhamel_hasDerivAt`.

The source bound supplies the `((2 / sqrt (4π)) * M) * (t-s)^(-1/2)`
dominating function.  The remaining hypotheses are the genuine regularity side
conditions for Mathlib's parametric-integral theorem: value/gradient
measurability and the per-slice spatial derivative formula.
-/
theorem wholeLineDuhamel_hasDerivAt_of_bounded_source
    {t x₀ M : ℝ} {F : ℝ → ℝ → ℝ} {s : Set ℝ}
    (ht : 0 < t) (hs : s ∈ 𝓝 x₀) (hM : 0 ≤ M)
    (hF_meas :
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun r : ℝ => wholeLineHeatOp (t - r) (F r) x)
          (volume.restrict (Ι (0 : ℝ) t)))
    (hF_int :
      IntervalIntegrable
        (fun r : ℝ => wholeLineHeatOp (t - r) (F r) x₀) volume (0 : ℝ) t)
    (hF'_meas :
      AEStronglyMeasurable
        (fun r : ℝ => wholeLineHeatGradOp (t - r) (F r) x₀)
        (volume.restrict (Ι (0 : ℝ) t)))
    (hF_bound :
      ∀ r, 0 ≤ r → r < t → ∀ y, |F r y| ≤ M)
    (h_diff :
      ∀ r, 0 ≤ r → r < t →
        ∀ x ∈ s,
          HasDerivAt
            (fun y : ℝ => wholeLineHeatOp (t - r) (F r) y)
            (wholeLineHeatGradOp (t - r) (F r) x) x) :
    HasDerivAt
      (fun y : ℝ => wholeLineValueDuhamel t F y)
      (wholeLineGradientDuhamel t F x₀) x₀ := by
  refine wholeLineDuhamel_hasDerivAt
    (t := t) (x₀ := x₀) (A := (2 / Real.sqrt (4 * Real.pi)) * M)
    (F := F) (s := s) ht hs hF_meas hF_int hF'_meas ?hgrad_bound h_diff
  intro r hr0 hrt x _hx
  exact wholeLineHeatGradOp_norm_le_rpow
    (τ := t - r) (M := M) (f := F r)
    (sub_pos.mpr hrt) hM (hF_bound r hr0 hrt) x

/--
Moving-frame Duhamel spatial Leibniz bridge in interval-integral form.
-/
theorem movingFrameValueDuhamel_hasDerivAt_of_bounded_source
    {c t x₀ M : ℝ} {F : ℝ → ℝ → ℝ} {s : Set ℝ}
    (ht : 0 < t) (hs : s ∈ 𝓝 x₀) (hM : 0 ≤ M)
    (hF_meas :
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun r : ℝ => movingFrameHeatOp c (t - r) (F r) x)
          (volume.restrict (Ι (0 : ℝ) t)))
    (hF_int :
      IntervalIntegrable
        (fun r : ℝ => movingFrameHeatOp c (t - r) (F r) x₀) volume (0 : ℝ) t)
    (hF'_meas :
      AEStronglyMeasurable
        (fun r : ℝ => movingFrameHeatGradOp c (t - r) (F r) x₀)
        (volume.restrict (Ι (0 : ℝ) t)))
    (hF_bound :
      ∀ r, 0 ≤ r → r < t → ∀ y, |F r y| ≤ M)
    (h_diff :
      ∀ r, 0 ≤ r → r < t →
        ∀ x ∈ s,
          HasDerivAt
            (fun y : ℝ => movingFrameHeatOp c (t - r) (F r) y)
            (movingFrameHeatGradOp c (t - r) (F r) x) x) :
    HasDerivAt
      (fun y : ℝ => movingFrameValueDuhamel c F t y)
      (movingFrameGradDuhamel c F t x₀) x₀ := by
  have hne : ∀ᵐ r : ℝ ∂volume, r ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  refine
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := t)
      (F := fun x r => movingFrameHeatOp c (t - r) (F r) x)
      (F' := fun x r => movingFrameHeatGradOp c (t - r) (F r) x)
      (x₀ := x₀) (s := s)
      (bound := fun r : ℝ =>
        ((2 / Real.sqrt (4 * Real.pi)) * M) * (t - r) ^ (-(1 / 2 : ℝ)))
      hs hF_meas hF_int hF'_meas ?h_bound ?hbound_int ?h_diff).2
  · filter_upwards [hne] with r hr_ne hr_mem x hx
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hr_mem
    exact movingFrameHeatGradOp_norm_le_rpow
      (c := c) (τ := t - r) (M := M) (f := F r)
      (sub_pos.mpr (lt_of_le_of_ne hr_mem.2 hr_ne)) hM
      (hF_bound r hr_mem.1.le (lt_of_le_of_ne hr_mem.2 hr_ne)) x
  · exact
      (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
        ((2 / Real.sqrt (4 * Real.pi)) * M)
  · filter_upwards [hne] with r hr_ne hr_mem x hx
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hr_mem
    exact h_diff r hr_mem.1.le (lt_of_le_of_ne hr_mem.2 hr_ne) x hx

/--
Moving-frame Duhamel spatial Leibniz bridge for the existing `Set.Icc` value
Duhamel definition.
-/
theorem movingFrameDuhamel_hasDerivAt_of_bounded_source
    {c t x₀ M : ℝ} {F : ℝ → ℝ → ℝ} {s : Set ℝ}
    (ht : 0 < t) (hs : s ∈ 𝓝 x₀) (hM : 0 ≤ M)
    (hF_meas :
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun r : ℝ => movingFrameHeatOp c (t - r) (F r) x)
          (volume.restrict (Ι (0 : ℝ) t)))
    (hF_int :
      IntervalIntegrable
        (fun r : ℝ => movingFrameHeatOp c (t - r) (F r) x₀) volume (0 : ℝ) t)
    (hF'_meas :
      AEStronglyMeasurable
        (fun r : ℝ => movingFrameHeatGradOp c (t - r) (F r) x₀)
        (volume.restrict (Ι (0 : ℝ) t)))
    (hF_bound :
      ∀ r, 0 ≤ r → r < t → ∀ y, |F r y| ≤ M)
    (h_diff :
      ∀ r, 0 ≤ r → r < t →
        ∀ x ∈ s,
          HasDerivAt
            (fun y : ℝ => movingFrameHeatOp c (t - r) (F r) y)
            (movingFrameHeatGradOp c (t - r) (F r) x) x) :
    HasDerivAt
      (fun y : ℝ => movingFrameDuhamel c F t y)
      (movingFrameGradDuhamel c F t x₀) x₀ := by
  have hmain :=
    movingFrameValueDuhamel_hasDerivAt_of_bounded_source
      (c := c) (t := t) (x₀ := x₀) (M := M) (F := F) (s := s)
      ht hs hM hF_meas hF_int hF'_meas hF_bound h_diff
  convert hmain using 1
  ext y
  exact (movingFrameDuhamel_eq_movingFrameValueDuhamel
    (c := c) (t := t) (F := F) ht.le y)

/--
Auxiliary frozen-source Duhamel bridge: the derivative of the value Duhamel is
the gradient Duhamel.
-/
theorem auxiliaryDuhamel_hasDerivAt_of_bounded_source
    {p : CMParams} {c t x₀ M : ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ} {s : Set ℝ}
    (ht : 0 < t) (hs : s ∈ 𝓝 x₀) (hM : 0 ≤ M)
    (hF_meas :
      ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun r : ℝ =>
            movingFrameHeatOp c (t - r)
              (fun y => auxiliaryFrozenNonlinearity p (W r) (Wx r) V Vx y) x)
          (volume.restrict (Ι (0 : ℝ) t)))
    (hF_int :
      IntervalIntegrable
        (fun r : ℝ =>
          movingFrameHeatOp c (t - r)
            (fun y => auxiliaryFrozenNonlinearity p (W r) (Wx r) V Vx y) x₀)
        volume (0 : ℝ) t)
    (hF'_meas :
      AEStronglyMeasurable
        (fun r : ℝ =>
          movingFrameHeatGradOp c (t - r)
            (fun y => auxiliaryFrozenNonlinearity p (W r) (Wx r) V Vx y) x₀)
        (volume.restrict (Ι (0 : ℝ) t)))
    (hF_bound :
      ∀ r, 0 ≤ r → r < t → ∀ y,
        |auxiliaryFrozenNonlinearity p (W r) (Wx r) V Vx y| ≤ M)
    (h_diff :
      ∀ r, 0 ≤ r → r < t →
        ∀ x ∈ s,
          HasDerivAt
            (fun z : ℝ =>
              movingFrameHeatOp c (t - r)
                (fun y => auxiliaryFrozenNonlinearity p (W r) (Wx r) V Vx y) z)
            (movingFrameHeatGradOp c (t - r)
              (fun y => auxiliaryFrozenNonlinearity p (W r) (Wx r) V Vx y) x) x) :
    HasDerivAt
      (fun y : ℝ => auxiliaryDuhamel p c W Wx V Vx t y)
      (auxiliaryGradDuhamel p c W Wx V Vx t x₀) x₀ := by
  simpa [auxiliaryDuhamel, auxiliaryGradDuhamel] using
    movingFrameDuhamel_hasDerivAt_of_bounded_source
      (c := c) (t := t) (x₀ := x₀) (M := M)
      (F := fun r y => auxiliaryFrozenNonlinearity p (W r) (Wx r) V Vx y)
      (s := s) ht hs hM hF_meas hF_int hF'_meas hF_bound h_diff

/-- The differentiated auxiliary mild-map representation from the Duhamel bridge. -/
theorem auxiliaryMildMap_hasDerivAt_of_duhamel_bridge
    {p : CMParams} {c t x : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hinit :
      HasDerivAt
        (fun y : ℝ => movingFrameHeatOp c t Uplus y)
        (movingFrameHeatGradOp c t Uplus x) x)
    (hduh :
      HasDerivAt
        (fun y : ℝ => auxiliaryDuhamel p c W Wx V Vx t y)
        (auxiliaryGradDuhamel p c W Wx V Vx t x) x) :
    HasDerivAt
      (fun y : ℝ => auxiliaryMildMap p c Uplus W Wx V Vx t y)
      (movingFrameHeatGradOp c t Uplus x +
        auxiliaryGradDuhamel p c W Wx V Vx t x) x := by
  simpa [auxiliaryMildMap] using hinit.add hduh

/-- Derivative equality form of `auxiliaryMildMap_hasDerivAt_of_duhamel_bridge`. -/
theorem auxiliaryMildMap_deriv_eq_of_duhamel_bridge
    {p : CMParams} {c t x : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
    (hinit :
      HasDerivAt
        (fun y : ℝ => movingFrameHeatOp c t Uplus y)
        (movingFrameHeatGradOp c t Uplus x) x)
    (hduh :
      HasDerivAt
        (fun y : ℝ => auxiliaryDuhamel p c W Wx V Vx t y)
        (auxiliaryGradDuhamel p c W Wx V Vx t x) x) :
    deriv (fun y : ℝ => auxiliaryMildMap p c Uplus W Wx V Vx t y) x =
      movingFrameHeatGradOp c t Uplus x +
        auxiliaryGradDuhamel p c W Wx V Vx t x :=
  (auxiliaryMildMap_hasDerivAt_of_duhamel_bridge
    (p := p) (c := c) (t := t) (x := x)
    (Uplus := Uplus) (W := W) (Wx := Wx) (V := V) (Vx := Vx)
    hinit hduh).deriv

/--
Derivative-bound consumer for the auxiliary mild map after the Leibniz bridge
identifies the value-Duhamel derivative with the gradient Duhamel.
-/
theorem auxiliaryMildMap_deriv_abs_le_from_duhamel_bridge
    {p : CMParams} {c B0 BD t : ℝ} {Uplus : ℝ → ℝ}
    {W Wx : ℝ → ℝ → ℝ} {V Vx : ℝ → ℝ}
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
      |deriv (fun y : ℝ => auxiliaryMildMap p c Uplus W Wx V Vx t y) x|
        ≤ B0 + BD := by
  refine auxiliaryMildMap_deriv_abs_le_of_gradient_bounds
    (p := p) (c := c) (B0 := B0) (BD := BD) (t := t)
    (Uplus := Uplus) (W := W) (Wx := Wx) (V := V) (Vx := Vx)
    hinit_bound hduh_bound ?hrepr
  intro x
  exact auxiliaryMildMap_deriv_eq_of_duhamel_bridge
    (p := p) (c := c) (t := t) (x := x)
    (Uplus := Uplus) (W := W) (Wx := Wx) (V := V) (Vx := Vx)
    (hinit_deriv x) (hduh_deriv x)

#print axioms wholeLineValueDuhamel
#print axioms wholeLineGradientDuhamel
#print axioms two_div_sqrt_four_pi_mul_eq_rpow
#print axioms wholeLineHeatGradOp_norm_le_rpow
#print axioms movingFrameHeatGradOp_norm_le_rpow
#print axioms movingFrameValueDuhamel
#print axioms movingFrameDuhamel_eq_movingFrameValueDuhamel
#print axioms wholeLineDuhamel_hasDerivAt_of_dominated
#print axioms wholeLineDuhamel_hasDerivAt
#print axioms wholeLineDuhamel_hasDerivAt_of_bounded_source
#print axioms movingFrameValueDuhamel_hasDerivAt_of_bounded_source
#print axioms movingFrameDuhamel_hasDerivAt_of_bounded_source
#print axioms auxiliaryDuhamel_hasDerivAt_of_bounded_source
#print axioms auxiliaryMildMap_hasDerivAt_of_duhamel_bridge
#print axioms auxiliaryMildMap_deriv_eq_of_duhamel_bridge
#print axioms auxiliaryMildMap_deriv_abs_le_from_duhamel_bridge

end ShenWork.PaperOne
