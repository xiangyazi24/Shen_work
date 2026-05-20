/-
  ShenWork/PDE/IntervalDomain.lean

  Concrete bounded-domain infrastructure: the interval [0, L].
  This is the first audit-passing bounded-domain file.

  All definitions use Mathlib primitives (volume.restrict, Set.Icc).
  No abstract structure fields. No assumed estimates.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ShenWork.PDE.HeatSemigroup

open MeasureTheory Set

noncomputable section

namespace ShenWork.IntervalDomain

def intervalSet (L : ℝ) : Set ℝ := Set.Icc 0 L

def intervalMeasure (L : ℝ) : Measure ℝ :=
  volume.restrict (intervalSet L)

def intervalVolume (L : ℝ) : ℝ :=
  (intervalMeasure L Set.univ).toReal

theorem intervalVolume_eq {L : ℝ} (hL : 0 ≤ L) :
    intervalVolume L = L := by
  unfold intervalVolume intervalMeasure intervalSet
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  simpa using ENNReal.toReal_ofReal hL

theorem intervalVolume_pos {L : ℝ} (hL : 0 < L) :
    0 < intervalVolume L := by
  rw [intervalVolume_eq hL.le]
  exact hL

theorem intervalIntegral_const {L c : ℝ} :
    ∫ _ in (0 : ℝ)..L, c = c * L := by
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

theorem intervalIntegral_nonneg {L : ℝ} {f : ℝ → ℝ}
    (hL : 0 ≤ L) (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) :
    0 ≤ ∫ x in (0 : ℝ)..L, f x :=
  intervalIntegral.integral_nonneg hL hf

theorem intervalIntegral_mono {L : ℝ} {f g : ℝ → ℝ}
    (hL : 0 ≤ L) (hfg : ∀ x ∈ Set.Icc 0 L, f x ≤ g x)
    (hf : IntervalIntegrable f volume 0 L)
    (hg : IntervalIntegrable g volume 0 L) :
    ∫ x in (0 : ℝ)..L, f x ≤ ∫ x in (0 : ℝ)..L, g x :=
  intervalIntegral.integral_mono_on hL hf hg hfg

theorem intervalIntegral_add {L : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 L)
    (hg : IntervalIntegrable g volume 0 L) :
    ∫ x in (0 : ℝ)..L, (f x + g x) =
      (∫ x in (0 : ℝ)..L, f x) + ∫ x in (0 : ℝ)..L, g x :=
  intervalIntegral.integral_add hf hg

/-- The identity operator on interval functions preserves mass (trivially). -/
theorem identity_preserves_intervalIntegral {L : ℝ} (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..L, (id f) x = ∫ x in (0 : ℝ)..L, f x := by
  rfl

/-- Constant functions are interval-integrable. -/
theorem const_intervalIntegrable {L c : ℝ} :
    IntervalIntegrable (fun _ => c) volume 0 L :=
  intervalIntegrable_const

/-- The average of a function on [0,L]. This is the zeroth Neumann mode. -/
def intervalAverage (L : ℝ) (f : ℝ → ℝ) : ℝ :=
  (1 / L) * ∫ x in (0 : ℝ)..L, f x

/-- The constant-mode projection: maps f to its average on [0,L]. -/
def constantModeProjection (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun _ => intervalAverage L f

/-- The constant-mode projection preserves mass. -/
theorem constantModeProjection_preserves_mass {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..L, constantModeProjection L f x =
      ∫ x in (0 : ℝ)..L, f x := by
  unfold constantModeProjection intervalAverage
  rw [intervalIntegral_const]
  field_simp [ne_of_gt hL]

/-- The constant-mode projection maps nonneg-average functions to nonneg. -/
theorem constantModeProjection_nonneg {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : 0 ≤ ∫ x in (0 : ℝ)..L, f x) :
    ∀ x, 0 ≤ constantModeProjection L f x := by
  intro x
  unfold constantModeProjection intervalAverage
  exact mul_nonneg (div_nonneg one_pos.le hL.le) hf

/-- The average of a constant is itself. -/
theorem intervalAverage_const {L c : ℝ} (hL : 0 < L) :
    intervalAverage L (fun _ => c) = c := by
  unfold intervalAverage
  rw [intervalIntegral_const]
  field_simp [ne_of_gt hL]

/-- The Neumann heat kernel on [0,L] via method of images (reflected kernel).
For t > 0 and x, y ∈ [0,L]:
  K_N(t, x, y) = G(t, x-y) + G(t, x+y) + G(t, 2L-x-y) + ...
where G is the Gaussian. The zeroth-order approximation uses just the
first two terms (direct + one reflection), which already satisfies
Neumann BC at x=0. -/
def neumannHeatKernel_zerothReflection (_L t x y : ℝ) : ℝ :=
  heatKernel t (x - y) + heatKernel t (x + y)

/-- The zeroth-reflection Neumann kernel is nonneg. -/
theorem neumannHeatKernel_zerothReflection_nonneg
    {t : ℝ} (ht : 0 < t) (L x y : ℝ) :
    0 ≤ neumannHeatKernel_zerothReflection L t x y := by
  unfold neumannHeatKernel_zerothReflection
  exact add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _)

/-- The zeroth-reflection kernel is even in x: K(t, -x, y) = K(t, x, y).
This symmetry implies the Neumann boundary condition ∂K/∂x|_{x=0} = 0. -/
theorem neumannHeatKernel_zerothReflection_even
    (L t x y : ℝ) :
    neumannHeatKernel_zerothReflection L t (-x) y =
      neumannHeatKernel_zerothReflection L t x y := by
  unfold neumannHeatKernel_zerothReflection
  rw [show -x - y = -(x + y) from by ring,
    show -x + y = -(x - y) from by ring,
    heatKernel_neg, heatKernel_neg]
  ring

/-- ∫ G(t, x+y) dy = 1, by substitution z = x+y. -/
theorem heatKernel_integral_add {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y, heatKernel t (x + y) = 1 := by
  have h : (fun y : ℝ => heatKernel t (x + y)) =
      (fun y => heatKernel t (y + x)) := by ext y; ring_nf
  rw [h, integral_add_right_eq_self, heatKernel_integral_eq_one ht]

/-- The reflected kernel integrates to 2 over y:
∫ [G(t,x-y) + G(t,x+y)] dy = 2. -/
theorem neumannHeatKernel_zerothReflection_integral
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    ∫ y, neumannHeatKernel_zerothReflection L t x y = 2 := by
  unfold neumannHeatKernel_zerothReflection
  rw [show (fun y => heatKernel t (x - y) + heatKernel t (x + y)) =
      (fun y => heatKernel t (x - y)) + (fun y => heatKernel t (x + y)) from by
    ext y; rfl]
  rw [Pi.add_def, MeasureTheory.integral_add
    (heatKernel_translated_integrable ht x)
    ((heatKernel_integrable ht).comp_add_left x)]
  rw [heatKernel_integral_translated ht x, heatKernel_integral_add ht x]
  norm_num

/-- Candidate half-line reflected-kernel operator: integrate the two-term
reflected kernel against `f` on `(0,∞)`.  No PDE or semigroup property is
claimed here. -/
def halfLineReflectedKernelOperator (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Set.Ioi 0, neumannHeatKernel_zerothReflection 0 t x y * f y

/-- L^∞ bound for the reflected full-line kernel integral:
if |f| ≤ M, then |∫ K_N f| ≤ 2M. -/
theorem reflectedKernelIntegral_Linfty_bound
    {f : ℝ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (_hf_meas : AEStronglyMeasurable f volume) :
    |∫ y, neumannHeatKernel_zerothReflection 0 t x y * f y| ≤ 2 * M := by
  unfold neumannHeatKernel_zerothReflection
  have hplus_int : Integrable (fun y : ℝ => heatKernel t (x + y)) :=
    (heatKernel_integrable ht).comp_add_left x
  have hsum_int :
      Integrable (fun y : ℝ => heatKernel t (x - y) + heatKernel t (x + y)) :=
    (heatKernel_translated_integrable ht x).add hplus_int
  have hmajor_int :
      Integrable
        (fun y : ℝ => (heatKernel t (x - y) + heatKernel t (x + y)) * M) :=
    hsum_int.mul_const M
  have hkernel_integral :
      ∫ y, heatKernel t (x - y) + heatKernel t (x + y) = 2 := by
    have := neumannHeatKernel_zerothReflection_integral ht 0 x
    simp only [neumannHeatKernel_zerothReflection] at this
    exact this
  calc |∫ y, (heatKernel t (x - y) + heatKernel t (x + y)) * f y|
      ≤ ∫ y, ‖(heatKernel t (x - y) + heatKernel t (x + y)) * f y‖ := by
        rw [← Real.norm_eq_abs]
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, |(heatKernel t (x - y) + heatKernel t (x + y)) * f y| := by
        simp [Real.norm_eq_abs]
    _ = ∫ y, (heatKernel t (x - y) + heatKernel t (x + y)) * |f y| := by
        congr 1; ext y
        rw [abs_mul, abs_of_nonneg
          (add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))]
    _ ≤ ∫ y, (heatKernel t (x - y) + heatKernel t (x + y)) * M := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y =>
            mul_nonneg
              (add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))
              (abs_nonneg _)
        · exact hmajor_int
        · exact Filter.Eventually.of_forall fun y =>
            mul_le_mul_of_nonneg_left (hf y)
              (add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))
    _ = M * ∫ y, (heatKernel t (x - y) + heatKernel t (x + y)) := by
        rw [show (fun y => (heatKernel t (x - y) + heatKernel t (x + y)) * M) =
            (fun y => M * (heatKernel t (x - y) + heatKernel t (x + y))) from by
          ext y; ring]
        exact MeasureTheory.integral_const_mul _ _
    _ = M * 2 := by
        rw [hkernel_integral]
    _ = 2 * M := by ring

/-- Full-line mass-normalized version of the two-term reflected kernel.  This
is still only a helper kernel, not the interval Neumann heat kernel. -/
def normalizedZerothReflectionKernel (L t x y : ℝ) : ℝ :=
  (1 / 2) * neumannHeatKernel_zerothReflection L t x y

theorem normalizedZerothReflectionKernel_nonneg
    {t : ℝ} (ht : 0 < t) (L x y : ℝ) :
    0 ≤ normalizedZerothReflectionKernel L t x y := by
  unfold normalizedZerothReflectionKernel
  exact mul_nonneg (by norm_num)
    (neumannHeatKernel_zerothReflection_nonneg ht L x y)

theorem normalizedZerothReflectionKernel_even
    (L t x y : ℝ) :
    normalizedZerothReflectionKernel L t (-x) y =
      normalizedZerothReflectionKernel L t x y := by
  unfold normalizedZerothReflectionKernel
  rw [neumannHeatKernel_zerothReflection_even]

theorem normalizedZerothReflectionKernel_integral
    {t : ℝ} (ht : 0 < t) (L x : ℝ) :
    ∫ y, normalizedZerothReflectionKernel L t x y = 1 := by
  unfold normalizedZerothReflectionKernel
  rw [MeasureTheory.integral_const_mul]
  rw [neumannHeatKernel_zerothReflection_integral ht L x]
  norm_num

theorem normalizedReflectedKernelIntegral_Linfty_bound
    {f : ℝ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_meas : AEStronglyMeasurable f volume) :
    |∫ y, normalizedZerothReflectionKernel 0 t x y * f y| ≤ M := by
  have hbound :=
    reflectedKernelIntegral_Linfty_bound hf ht x hf_meas
  have hrewrite :
      (∫ y, normalizedZerothReflectionKernel 0 t x y * f y) =
        (1 / 2) *
          ∫ y, neumannHeatKernel_zerothReflection 0 t x y * f y := by
    unfold normalizedZerothReflectionKernel
    rw [show
        (fun y : ℝ =>
          ((1 / 2) * neumannHeatKernel_zerothReflection 0 t x y) * f y) =
        (fun y : ℝ =>
          (1 / 2) * (neumannHeatKernel_zerothReflection 0 t x y * f y)) by
        ext y
        ring]
    exact MeasureTheory.integral_const_mul _ _
  rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  calc
    (1 / 2) * |∫ y, neumannHeatKernel_zerothReflection 0 t x y * f y|
        ≤ (1 / 2) * (2 * M) := by
          exact mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = M := by ring

end ShenWork.IntervalDomain

end
