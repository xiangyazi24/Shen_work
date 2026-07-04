import ShenWork.PDE.P3MoserActualWiring

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainMoserClosure

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserBoundedBeforeProducer

open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-!
Task 21 investigation report.

The assembly filler asks for the hypothesis

```
∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
  IsPaper2ClassicalSolution intervalDomain p T u v →
  CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
  AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
    IsPaper2BoundedBefore intervalDomain T u
```

The requested direct route from only `(hsol, hcross, hboot)` is not present in
the current producer chain.

What exists:

* `IntervalDomainExistence.lean` obtains a bounded-before term inside the
  a-priori route from the old statement interfaces `Corollary_2_1` and
  `Proposition_2_5`, after first producing an L² bootstrap seed.  That route is
  not local to an arbitrary `(rho,p0,hboot)` and it uses global route inputs.
* `IntervalDomainMoserLadderAtoms.lean` has route packages whose Moser fields
  are explicit atoms: either old physical-`B` dissipation plus relative
  interpolation, or a supplied `IntegratedMoserFirstCrossingStep`, together
  with the quantitative endpoint/root tower.
* `IntervalDomainLpBootstrapEnergyInequality.lean` supplies the energy
  inequality from `(hsol,hcross,hboot)`.
* `P3MoserDissipationShape.lean` closes bounded-before from energy,
  physical-`B` dissipation, relative interpolation, downward Lp monotonicity,
  and the quantitative endpoint.
* `P3MoserIntegratedClosure.lean` gives the preferred replacement:
  a supplied integrated first-crossing step plus downward Lp monotonicity and
  the quantitative endpoint imply bounded-before.

The circular point is exactly the one noted in the spec.  The assembly uses
`hBoundedBefore` to build relative mass-gradient interpolation; that relative
interpolation then feeds the integrated dissipation/frontier machinery.  Thus
the current files do not derive `hBoundedBefore` from only
`(hsol,hcross,hboot)` without carrying an independent Moser step/dissipation
and endpoint.

The theorems below are the maximal non-circular wiring currently available:

* `intervalDomain_hBoundedBefore_of_integrated_step_and_endpoint` carries the
  preferred `IntegratedMoserFirstCrossingStep` and the quantitative endpoint.
* `intervalDomain_hBoundedBefore_of_nonnegB_dissipation_and_endpoint` records
  the older physical-`B` dissipation + relative interpolation route.
* The two supplier theorems package those pointwise producers into exactly the
  assembly filler's `hBoundedBefore` function shape, with the missing atoms
  made explicit as independent suppliers.
-/

/-- Downward finite-time Lp monotonicity available from a classical interval
solution. -/
theorem intervalDomain_LpPowerBoundedBefore_mono_of_classical
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ {p q : ℝ}, 1 < p → p ≤ q →
      LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u := by
  intro p q hp hpq hq
  exact intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
    hp hpq
    (fun t ht0 htT x =>
      (IsPaper2ClassicalSolution.u_pos' hsol ht0 htT (x := x)).le)
    (fun t ht0 htT =>
      intervalDomain_u_rpow_intervalIntegrable_of_regularity
        (q := p) hsol ht0 htT)
    (fun t ht0 htT =>
      intervalDomain_u_rpow_intervalIntegrable_of_regularity
        (q := q) hsol ht0 htT)
    hq

/-- Preferred non-circular producer: from the local solution/bootstrap data,
an independently supplied integrated first-crossing step, and a quantitative
endpoint, produce the assembly filler's bounded-before conclusion. -/
theorem intervalDomain_hBoundedBefore_of_integrated_step_and_endpoint
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (_hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  exact intervalDomain_boundedBefore_of_integrated_first_crossing_step
    hboot hstep
    (intervalDomain_LpPowerBoundedBefore_mono_of_classical hsol)
    hEndpoint

/-- Supplier-shaped version of the preferred route.  This has exactly the
assembly filler's `hBoundedBefore` output shape; the independent carried data
are the integrated crossing-step supplier and the quantitative endpoint
supplier. -/
theorem intervalDomain_hBoundedBeforeSupplier_of_integrated_step_and_endpoint
    {params : CM2Params}
    (hstep :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hEndpoint :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain params T u v →
      CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0 →
        IsPaper2BoundedBefore intervalDomain T u := by
  intro T rho p0 u v hsol hcross hboot
  rcases hEndpoint hsol hcross hboot with ⟨pSeq, rootBound, hQuantEndpoint⟩
  exact intervalDomain_hBoundedBefore_of_integrated_step_and_endpoint
    hsol hcross hboot (hstep hsol hcross hboot) hQuantEndpoint

/-- Older physical-`B` route: from local solution/bootstrap data, the regularity
energy inequality, physical-`B` dissipation, relative interpolation, and a
quantitative endpoint, produce bounded-before. -/
theorem intervalDomain_hBoundedBefore_of_nonnegB_dissipation_and_endpoint
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0)
    (hdiss : MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  exact intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
    hboot
    (intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot)
    hdiss hrel
    (intervalDomain_LpPowerBoundedBefore_mono_of_classical hsol)
    hEndpoint

/-- Supplier-shaped version of the older physical-`B` route. -/
theorem intervalDomain_hBoundedBeforeSupplier_of_nonnegB_dissipation_and_endpoint
    {params : CM2Params}
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0)
    (hrel :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hEndpoint :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain params T u v →
      CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0 →
        IsPaper2BoundedBefore intervalDomain T u := by
  intro T rho p0 u v hsol hcross hboot
  rcases hEndpoint hsol hcross hboot with ⟨pSeq, rootBound, hQuantEndpoint⟩
  exact intervalDomain_hBoundedBefore_of_nonnegB_dissipation_and_endpoint
    hsol hcross hboot
    (hdiss hsol hcross hboot)
    (hrel hsol hcross hboot)
    hQuantEndpoint

#print axioms intervalDomain_LpPowerBoundedBefore_mono_of_classical
#print axioms intervalDomain_hBoundedBefore_of_integrated_step_and_endpoint
#print axioms intervalDomain_hBoundedBeforeSupplier_of_integrated_step_and_endpoint
#print axioms intervalDomain_hBoundedBefore_of_nonnegB_dissipation_and_endpoint
#print axioms intervalDomain_hBoundedBeforeSupplier_of_nonnegB_dissipation_and_endpoint

end ShenWork.IntervalDomainExistence.P3MoserBoundedBeforeProducer

end
