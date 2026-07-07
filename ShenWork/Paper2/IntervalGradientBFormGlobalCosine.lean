/-
  Global B-form cosine representation for a gradient mild solution, with the
  honest gradient-to-B Duhamel-leg equality exposed.

  This is a core field producer for the general-chi `Hsource` route.  It does
  not assert that the gradient mild map and the B-form map are definitionally
  the same; the required equality of their chemotaxis Duhamel legs is carried as
  an explicit analytic input.
-/
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalMildPicard

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalGradientBFormGlobalCosine

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted intervalGradientDuhamelMap)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.CosineSpectrum (cosineMode)

/-- Global B-form cosine representation of a gradient mild solution, assuming the
gradient chemotaxis Duhamel leg has been identified with the B-kernel leg and the
usual B-form source bridge holds.

The explicit `hgradB` hypothesis is the real analytic gradient-to-B conversion
still to be produced; the rest is wiring through
`intervalConjugateDuhamelMap_cosineSeries`. -/
theorem gradientMildSolution_bForm_global_cosine_of_gradB_sourceBridge
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {M₀ : ℝ}
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p D.u))
    (hB_int : ∀ t, 0 < t → t ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (D.u s)) x)
        volume 0 t)
    (hlog_int : ∀ t, 0 < t → t ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) x)
        volume 0 t)
    (hgradB : ∀ t, 0 < t → t ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..t,
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (t - s) (chemFluxLifted p (D.u s)) z) x)
        =
      ∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (D.u s)) x)
    (hsource_bridge : ∀ t, 0 < t → t ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        (-p.χ₀) * intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p (D.u s)) x
          + intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) x
        = unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p D.u s) x) :
    ∀ t, 0 < t → t ≤ D.T →
      Set.EqOn (intervalDomainLift (D.u t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p D.u) t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT x hx
  have hmild := D.hmild t ht htT ⟨x, hx⟩
  have hmap :
      intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩ =
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap
          p u₀ D.u t ⟨x, hx⟩ := by
    unfold intervalGradientDuhamelMap
    unfold ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap
    rw [hgradB t ht htT x hx]
  calc
    intervalDomainLift (D.u t) x = D.u t ⟨x, hx⟩ := by
      simp [intervalDomainLift, hx]
    _ = intervalGradientDuhamelMap p u₀ D.u t ⟨x, hx⟩ := hmild
    _ = ShenWork.IntervalConjugateDuhamelMap.intervalConjugateDuhamelMap
          p u₀ D.u t ⟨x, hx⟩ := hmap
    _ = ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p D.u) t n * cosineMode n x :=
      ShenWork.IntervalConjugateCosineSeries.intervalConjugateDuhamelMap_cosineSeries
        (p := p) (u₀ := u₀) (u := D.u) (t := t) (x := x) (M₀ := M₀)
        ht hx hu₀_cont hu₀_bound hsrcB
        (hB_int t ht htT x hx)
        (hlog_int t ht htT x hx)
        (hsource_bridge t ht htT x hx)

#print axioms gradientMildSolution_bForm_global_cosine_of_gradB_sourceBridge

end ShenWork.IntervalGradientBFormGlobalCosine
