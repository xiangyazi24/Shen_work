import ShenWork.PDE.P3MoserFirstCrossingContinuation

open Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserShortTimeBounded

open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation

/-- At each fixed interior time, the closed-space continuity field in
`intervalDomainClassicalRegularity` makes the interval slice pointwise bounded. -/
theorem intervalDomain_slice_bounded_of_classical
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ∃ M, ∀ x : intervalDomain.Point, |u t x| ≤ M := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hreg := hsol.regularity
  change intervalDomainClassicalRegularity T u v at hreg
  obtain ⟨_, _, _, _, _, _, hfield⟩ := hreg
  have hslice :
      ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    have hc := hfield.1 (t, y) ⟨htmem, hy⟩
    exact
      (hc.comp
        (Continuous.continuousWithinAt
          (by fun_prop : Continuous fun z : ℝ => (t, z)))
        (fun z hz => ⟨htmem, hz⟩) :
        ContinuousWithinAt (fun z : ℝ => intervalDomainLift (u t) z)
          (Set.Icc (0 : ℝ) 1) y)
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hslice
  refine ⟨M, ?_⟩
  intro x
  have hx : (x.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.2
  have hMx := hM x.1 hx
  simpa [Real.norm_eq_abs, intervalDomainLift, hx] using hMx

/-- Residual A for the concrete interval domain.  The short interval is
`(0, T/2)`, and the bound at each fixed time comes from compactness of `[0,1]`
and the closed-space continuity conjunct of classical regularity. -/
theorem intervalDomain_shortTimeBoundedBeforeResidual
    (p : CM2Params) :
    ShortTimeBoundedBeforeResidual intervalDomain p := by
  intro T u v hsol
  refine ⟨T / 2, half_pos hsol.T_pos, ?_⟩
  refine ⟨?_, ?_⟩
  · linarith [hsol.T_pos]
  · intro t ht0 htτ
    exact intervalDomain_slice_bounded_of_classical
      (p := p) (T := T) (v := v) hsol ht0 (by linarith)

#print axioms intervalDomain_slice_bounded_of_classical
#print axioms intervalDomain_shortTimeBoundedBeforeResidual

end ShenWork.IntervalDomainExistence.P3MoserShortTimeBounded

end
