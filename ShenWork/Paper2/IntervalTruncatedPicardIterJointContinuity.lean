/-
  Positive-time joint continuity of the truncated Picard iterates.

  The base iterate is the homogeneous Neumann heat evolution.  We pass from
  the subtype datum to its globally continuous constant extension, apply the
  existing spectral joint-continuity theorem, and transfer back on [0,1].
-/
import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard
import ShenWork.Paper2.IntervalChiNegLegContinuity
import ShenWork.PDE.IntervalDomainContinuousExtension

open Filter Topology Set
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainConstExtend
    constExtend_continuous constExtend_eq_lift_on_Icc
    semigroupOperator_constExtend_eq_lift)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.Paper2.IntervalChiNegLegContinuity
  (homLeg_continuousOn_slab)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- The zeroth truncated Picard iterate is jointly continuous on every
positive-time slab. -/
theorem truncatedConjugatePicardIter_zero_jointContinuousOn_Ioc
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀) {B : ℝ} (hB : 0 ≤ B)
    (hu₀_bound : ∀ x, |u₀ x| ≤ B) {T : ℝ} (hT : 0 < T) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦
        intervalDomainLift (truncatedConjugatePicardIter p u₀ 0 q.1) q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let f : ℝ → ℝ := intervalDomainConstExtend u₀
  have hf_cont : Continuous f := by
    simpa [f] using constExtend_continuous hu₀_cont
  have hf_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B := by
    intro x hx
    rw [show f x = intervalDomainLift u₀ x by
      simpa [f] using constExtend_eq_lift_on_Icc (f := u₀) hx]
    simp only [intervalDomainLift, dif_pos hx]
    exact hu₀_bound ⟨x, hx⟩
  have hcoeff : ∀ n, |cosineCoeffs f n| ≤ 2 * B :=
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hf_cont.continuousOn hB hf_bound
  have hT' : 0 < T + 1 := by linarith
  have hhom := homLeg_continuousOn_slab hf_cont hcoeff hT'
  have hsub :
      Set.Ioc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        Set.Ioo (0 : ℝ) (T + 1) ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    exact ⟨⟨hq.1.1, lt_of_le_of_lt hq.1.2 (by linarith)⟩, hq.2⟩
  refine (hhom.mono hsub).congr ?_
  intro q hq
  simp only [truncatedConjugatePicardIter, intervalDomainLift, dif_pos hq.2]
  exact semigroupOperator_constExtend_eq_lift.symm

end ShenWork.Paper2.BFormPositiveDatumNegPart
