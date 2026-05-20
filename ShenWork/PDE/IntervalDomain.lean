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

end ShenWork.IntervalDomain

end
