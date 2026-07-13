/-
  Initial trace for the faithful general-m positive-strip mild solution.
  Both nonlinear Duhamel legs vanish uniformly as t tends to zero; the
  chemotaxis leg uses the existing square-root kernel bound on the same
  positive strip.
-/
import ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
import ShenWork.Paper2.IntervalBFormInitialTrace

open MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainM)
open ShenWork.IntervalMildPicard (HasContinuousSlices)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.IntervalConjugateBallSupBound (valueDuhamel_sup_bound_of_ball)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted intervalConjugateDuhamelMapM
    chemFluxMLifted_abs_le_of_pos_slice)
open ShenWork.Paper2.IntervalDomainMConjugateMapBounds
  (conjugateMDuhamel_sup_bound_of_positive_cone_univ)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)

/-- The faithful general-m mild map approaches its initial datum uniformly
on the closed interval. -/
theorem intervalConjugateDuhamelMapM_initialApproach
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ ε, 0 < ε → ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalConjugateDuhamelMapM p u₀ D.u t x - u₀ x| < ε := by
  intro ε hε
  set C_Q : ℝ := D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)))
  have hCQ : 0 ≤ C_Q := by
    dsimp [C_Q]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  set C_L : ℝ := D.M * (p.a + p.b * D.M ^ p.α)
  have hCL : 0 ≤ C_L := by
    dsimp [C_L]
    exact mul_nonneg D.hM.le
      (add_nonneg p.ha
        (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))
  set A : ℝ := 2 * |p.χ₀| * heatGradientLinftyLinftyConstant * C_Q
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg p.χ₀))
        heatGradientLinftyLinftyConstant_nonneg) hCQ
  obtain ⟨δS, hδS, hSclose⟩ :=
    ShenWork.IntervalPicardIterateInitialApproach.semigroup_initialApproach
      p hu₀_cont (ε / 2) (by linarith)
  obtain ⟨δD, hδD, hDsmall⟩ :=
    exists_small_contraction_time_target hA hCL
      (show 0 < ε / 2 by linarith)
  refine ⟨min (min δS δD) D.T, lt_min (lt_min hδS hδD) D.hT, ?_⟩
  intro t ht htδ x
  have htδS : t < δS :=
    lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_left _ _))
  have htδD : t < δD :=
    lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_right _ _))
  have htT : t ≤ D.T :=
    (le_of_lt htδ).trans (min_le_right _ _)
  have hbound_t : ∀ s, 0 < s → s ≤ t → ∀ y, |D.u s y| ≤ D.M :=
    fun s hs hst ↦ D.hbound s hs (hst.trans htT)
  have hfloor_t : ∀ s, 0 < s → s ≤ t → ∀ y, D.c ≤ D.u s y :=
    fun s hs hst ↦ D.hfloor s hs (hst.trans htT)
  have hcont_t : HasContinuousSlices t D.u :=
    fun s hs hst ↦ D.hcont s hs (hst.trans htT)
  have hQbound : ∀ s, 0 < s → s ≤ t → ∀ y,
      |chemFluxMLifted p (D.u s) y| ≤ C_Q := by
    intro s hs hst y
    exact chemFluxMLifted_abs_le_of_pos_slice p D.hc D.floor_le_bound
      (hbound_t s hs hst) (hfloor_t s hs hst) (hcont_t s hs hst) y
  have hLbound : ∀ s, 0 < s → s ≤ t → ∀ y,
      |logisticLifted p (D.u s) y| ≤ C_L := by
    intro s hs hst y
    exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
      p D.hM (hbound_t s hs hst) y
  have hchem :
      |∫ s in (0 : ℝ)..t, intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) x.1| ≤
        heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * C_Q :=
    conjugateMDuhamel_sup_bound_of_positive_cone_univ
      p D.hc D.floor_le_bound hCQ hbound_t hfloor_t hcont_t hQbound
        ht le_rfl x
  have hval :
      |∫ s in (0 : ℝ)..t, intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) x.1| ≤ t * C_L :=
    valueDuhamel_sup_bound_of_ball p D.hM hCL hbound_t hLbound ht le_rfl x
  have hcorr :
      |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s)
            (chemFluxMLifted p (D.u s)) x.1) +
        ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1| ≤
        A * Real.sqrt t + C_L * t := by
    calc
      _ ≤ |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) x.1)| +
          |∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) x.1| := abs_add_le _ _
      _ ≤ |p.χ₀| *
            (heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * C_Q) +
          t * C_L := by
        simpa [abs_mul, abs_neg] using
          add_le_add (mul_le_mul_of_nonneg_left hchem (abs_nonneg p.χ₀)) hval
      _ = A * Real.sqrt t + C_L * t := by
        dsimp [A]
        ring
  have hcorr_small : A * Real.sqrt t + C_L * t < ε / 2 := by
    have hsqrt : Real.sqrt t ≤ Real.sqrt δD :=
      Real.sqrt_le_sqrt htδD.le
    have hA' := mul_le_mul_of_nonneg_left hsqrt hA
    have hL' := mul_le_mul_of_nonneg_left htδD.le hCL
    linarith
  have hS := hSclose t ht htδS x
  dsimp [intervalConjugateDuhamelMapM]
  calc
    |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 +
          (-p.χ₀) * (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (chemFluxMLifted p (D.u s)) x.1) +
          (∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) x.1) - u₀ x|
        = |(intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x) +
            ((-p.χ₀) * (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (D.u s)) x.1) +
            ∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) x.1)| := by congr 1 <;> ring
    _ ≤ |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x| +
          |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (D.u s)) x.1) +
            ∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) x.1| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hS (hcorr.trans_lt hcorr_small)
    _ = ε := by ring

/-- Initial trace of the faithful general-m mild fixed point. -/
theorem conjugateMildSolutionDataM_initialTrace
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (D : ConjugateMildSolutionDataM p u₀) :
    InitialTrace intervalDomainM u₀ D.u := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hsmall⟩ :=
    intervalConjugateDuhamelMapM_initialApproach p hu₀_cont D
      (ε / 2) (by linarith)
  refine ⟨min δ₀ D.T, lt_min hδ₀ D.hT, ?_⟩
  intro t ht htδ
  have htδ₀ : t < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have htT : t ≤ D.T := (le_of_lt htδ).trans (min_le_right _ _)
  change ShenWork.IntervalDomain.intervalDomainSupNorm
    (fun x ↦ D.u t x - u₀ x) < ε
  unfold ShenWork.IntervalDomain.intervalDomainSupNorm
  have hpt : ∀ x : intervalDomainPoint, |D.u t x - u₀ x| < ε / 2 := by
    intro x
    rw [D.hmild t ht htT x]
    exact hsmall t ht htδ₀ x
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, by constructor <;> norm_num⟩⟩
  have hle : sSup (Set.range (fun x : intervalDomainPoint ↦ |D.u t x - u₀ x|)) ≤
      ε / 2 := by
    apply csSup_le (Set.range_nonempty _)
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact (hpt x).le
  linarith

section AxiomAudit

#print axioms intervalConjugateDuhamelMapM_initialApproach
#print axioms conjugateMildSolutionDataM_initialTrace

end AxiomAudit

end ShenWork.Paper2
