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

end ShenWork.IntervalDomain

#print axioms ShenWork.IntervalDomain.intervalIntegral_nonneg
#print axioms ShenWork.IntervalDomain.intervalIntegral_mono
#print axioms ShenWork.IntervalDomain.intervalIntegral_add
#print axioms ShenWork.IntervalDomain.identity_preserves_intervalIntegral
#print axioms ShenWork.IntervalDomain.const_intervalIntegrable

end
