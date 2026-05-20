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

end ShenWork.IntervalDomain

end
