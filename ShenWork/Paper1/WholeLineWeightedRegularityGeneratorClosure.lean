import ShenWork.Paper1.WholeLineWeightedRegularityL2Semigroup
import ShenWork.Paper1.WholeLineWeightedRegularityH2

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-! A concrete specialization of the endpoint-safe generator cancellation to
the weighted whole-line heat operators.  The source hypotheses are explicit:
the theorem is a wiring lemma, not an assumption package hidden in a field. -/

theorem weightedMovingHeatL2_generatorDuhamel_truncated_tendsto
    {eta c h t theta C H : ℝ}
    (htheta : 0 < theta) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    {eps : ℕ → ℝ}
    (heps_pos : ∀ n, 0 < eps n)
    (hepsh : ∀ n, eps n ≤ h)
    (heps : Tendsto eps atTop (𝓝 0))
    {F : ℝ → WholeLineRealL2}
    (hA : ∀ r ∈ Ioc (0 : ℝ) h,
      ‖weightedMovingHeatL2Generator eta c r‖ ≤ C * r ^ (-(1 : ℝ)))
    (hF : ∀ r ∈ Icc (0 : ℝ) h,
      ‖F (t - r) - F t‖ ≤ H * r ^ theta)
    (hmeas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r
        (F (t - r) - F t))
      (volume.restrict (uIoc (0 : ℝ) h)))
    (hfull : ∀ n, IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r (F (t - r)))
      volume (eps n) h)
    (hconst : ∀ n, IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r (F t))
      volume (eps n) h)
    (horbit : ∀ n, ∀ r ∈ Icc (eps n) h,
      HasDerivAt
        (fun q => weightedMovingHeatL2Semigroup eta c q (F t))
        (weightedMovingHeatL2Generator eta c r (F t)) r)
    (hSzero : Tendsto
      (fun n => weightedMovingHeatL2Semigroup eta c (eps n) (F t))
      atTop (𝓝 (F t))) :
    Tendsto
      (fun n => ∫ r in eps n..h,
        weightedMovingHeatL2Generator eta c r (F (t - r)))
      atTop
      (𝓝 ((∫ r in (0 : ℝ)..h,
        weightedMovingHeatL2Generator eta c r
          (F (t - r) - F t)) +
        (weightedMovingHeatL2Semigroup eta c h - 1) (F t))) := by
  have hrem : IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r
        (F (t - r) - F t)) volume 0 h := by
    exact intervalIntegrable_generator_holder_remainder
      htheta hh hC hH hA hF hmeas
  exact tendsto_truncated_generator_duhamel_integral
    hh heps_pos hepsh heps hrem hfull hconst horbit hSzero

section AxiomAudit

#print axioms weightedMovingHeatL2_generatorDuhamel_truncated_tendsto

end AxiomAudit

end ShenWork.Paper1
