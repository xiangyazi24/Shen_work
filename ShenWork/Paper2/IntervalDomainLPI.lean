import ShenWork.Paper2.IntervalDomainLemma21
import ShenWork.Paper2.IntervalDomainMoserClosure

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLPI

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainLemma21
open ShenWork.Paper2.IntervalDomainMoserClosure

/-!
This file is the LPI lane bridge: it exposes the already-proved interval
Neumann heat-helper `L^p -> L^infty` smoothing estimate at the Paper2
interval-domain interface.  It does not manufacture `prop25`; the remaining
Moser endpoint data are recorded explicitly below.
-/

/-- Pointwise interval Neumann heat-helper `L^p -> L^infty` smoothing on
`[0,1]`, stated for interval-domain point functions. -/
theorem intervalDomainHeat_Lp_Linfty_pointwise_from_memLp
    {t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1))
    (x : intervalDomain.Point) :
    ‖intervalDomainHeatSemigroup t u x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
        intervalDomainLpNorm p u := by
  exact intervalSemigroupOperator_Lp_Linfty_pointwise
    (L := 1) (t := t) (p := p) (r := r)
    ht hrp (f := intervalDomainLift u) hu_mem x.1

/-- Interval Neumann heat-helper `L^p -> L^infty` smoothing in real
`lpNorm` notation, stated for interval-domain point functions. -/
theorem intervalDomainHeat_Lp_Linfty_bound_from_memLp
    {t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm (intervalDomainLift (intervalDomainHeatSemigroup t u)) ∞
        (intervalMeasure 1) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
        intervalDomainLpNorm p u := by
  have hraw :
      lpNorm
          (fun x : ℝ =>
            intervalSemigroupOperator 1 t (intervalDomainLift u) x)
          ∞ (intervalMeasure 1) ≤
        (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
          intervalDomainLpNorm p u := by
    exact intervalHeatSemigroup_Lp_Linfty_bound
      (L := 1) (t := t) (p := p) (r := r)
      ht hrp (f := intervalDomainLift u) hu_mem
  have hlift :
      lpNorm (intervalDomainLift (intervalDomainHeatSemigroup t u)) ∞
          (intervalMeasure 1) =
        lpNorm
          (fun x : ℝ =>
            intervalSemigroupOperator 1 t (intervalDomainLift u) x)
          ∞ (intervalMeasure 1) := by
    exact lpNorm_congr_ae_real
      (intervalDomainHeatSemigroup_lift_ae_eq t u)
  rw [hlift]
  exact hraw

/-- The same `L^p -> L^infty` endpoint routed through the concrete
`SemigroupEstimateData` value used by the interval-domain statement layer. -/
theorem intervalDomainSemigroupEstimateData_Lp_Linfty_bound_from_memLp
    {t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {u : intervalDomain.Point → ℝ}
    (hu_mem :
      MemLp (intervalDomainLift u) (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm
        (intervalDomainLift
          (intervalDomainSemigroupEstimateData.semigroup t u))
        ∞ (intervalMeasure 1) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
        intervalDomainSemigroupEstimateData.lpNorm p u := by
  simpa [intervalDomainSemigroupEstimateData] using
    intervalDomainHeat_Lp_Linfty_bound_from_memLp
      (t := t) (p := p) (r := r) ht hrp (u := u) hu_mem

/-- What `prop25` still needs after the heat-kernel endpoint is available:
a solution-structured Moser data producer.  This is not a `prop25` hypothesis
in disguise; the bundled data are the energy, dissipation, interpolation,
Lp-monotonicity, and quantitative endpoint pieces used by `MoserClosure`. -/
theorem Proposition_2_5_intervalDomain_of_structured_moser_data
    {p : CM2Params}
    (hdata : ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      ∀ {Tmax : ℝ}, 0 < Tmax →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
        ∀ pExp,
          max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
          LpPowerBoundedBefore intervalDomain pExp Tmax u →
            IntervalDomainStructuredMoserBootstrapData u Tmax) :
    Proposition_2_5 intervalDomain p := by
  intro u₀ hu₀ Tmax hTmax u v hsol htrace pExp hpExp hLp
  exact (hdata hu₀ hTmax hsol htrace pExp hpExp hLp).boundedBefore

/-- A global `BranchData` record still cannot be produced from the abstract
bounded-domain API; the `prop25` counterexample remains a precise obstruction
outside the concrete interval solution structure. -/
theorem not_forall_branchData_after_lpi :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2BootstrapEstimateBranchData D p) := by
  intro h
  exact not_forall_Proposition_2_5 (fun D p => (h D p).prop25)

end ShenWork.Paper2.IntervalDomainLPI

end
