/-
  ShenWork/PDE/IntervalFullKernelResolverFull.lean

  **T2 — `_resolver_full`: the full-kernel hmap specialized to the Neumann
  elliptic resolver `R = intervalNeumannResolverR p`.**

  Full-Neumann-kernel mirror of
  `intervalCoupledClassicalC1BallEstimates_hmap_dirichlet_initial_resolver`: the
  terminal form of the `_clean_full → _cleaner_full → _resolver_full` chain, with
  the coupling `R` specialized to the Paper-2 elliptic resolver.  `hGradEq` is
  discharged on the full Neumann kernel (`_clean_full`), and the Leibniz bridges
  `hSplit`/`hLeibniz`/`hGrad_int` are discharged internally (`_cleaner_full`).

  The per-slice joint measurability `hF_meas`/`hF'_meas` is carried as hypotheses
  (the lattice `s_dependent` measurability — joint measurability of `K_full` and
  `∂ₓK_full` in `(s,y)` via a 2-D `continuousOn_tsum`, the resolver source field's
  joint measurability via the ROUND-14 `intervalCoupledSource_resolver_lift_
  aestronglyMeasurable` — is the one documented analytic residual).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelCleanerFull
import ShenWork.PDE.IntervalChemDivAEMeasurable

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain ShenWork.IntervalDomainExistence
open ShenWork.IntervalCoupledClassicalBallEstimates ShenWork.Paper2 ShenWork.PDE

/-- **`_resolver_full`.**  The full-kernel snapshot hmap specialized to
`R = intervalNeumannResolverR p`. -/
theorem intervalFullKernelClassicalC1BallEstimates_hmap_dirichlet_initial_resolver
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    {u₀_ext u₀'_ext : ℝ → ℝ}
    {T M G_u G_u_init C_source H Cu₀ : ℝ}
    (hT : 0 < T) (hH_nn : 0 ≤ H) (hC_nn : 0 ≤ C_source)
    (hG_init_nn : 0 ≤ G_u_init)
    (hM_eq : M = H + C_source * T)
    (hG_u_eq : G_u = G_u_init +
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt T) * C_source)
    (hu₀_sup : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hext_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y = u₀_ext y)
    (hu₀_ext_int : MeasureTheory.Integrable u₀_ext (intervalMeasure 1))
    (hu₀_ext_bound : ∀ y, |u₀_ext y| ≤ Cu₀)
    (hu₀_ext_C1 : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u₀_ext (u₀'_ext y) y)
    (hu₀_ext'_int : IntervalIntegrable u₀'_ext MeasureTheory.volume 0 1)
    (hu₀_ext_one : u₀_ext 1 = 0)
    (hu₀_ext'_sup : ∀ y : ℝ, |u₀'_ext y| ≤ G_u_init)
    (hSol : ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IsPaper2ClassicalSolution intervalDomain p T
          (fun τ : ℝ => fun y : intervalDomainPoint =>
            intervalFullKernelCoupledDuhamelOperator p (intervalNeumannResolverR p) u₀ u τ y) v)
    (hSource_sup_local :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s, 0 ≤ s → s ≤ T → ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s))) y| ≤ C_source)
    (hSource_sup_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ, ∀ y : ℝ,
            |intervalDomainLift
              (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s))) y| ≤ C_source)
    (hint :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ (t : ℝ) (x : intervalDomainPoint), 0 < t → t ≤ T →
            MeasureTheory.IntegrableOn
              (fun s => intervalFullSemigroupOperator (t - s)
                (intervalDomainLift
                  (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s)))) x.1)
              (Set.Icc 0 t) MeasureTheory.volume)
    (hSource_int_global :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IntervalDomainClassicalC1Snapshot p T M G_u u v →
          ∀ s : ℝ,
            MeasureTheory.Integrable
              (intervalDomainLift
                (intervalCoupledSource p (u s) (intervalNeumannResolverR p (u s))))
              (intervalMeasure 1))
    :
    ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IntervalDomainClassicalC1Snapshot p T M G_u u v →
        IntervalDomainClassicalC1Snapshot p T M G_u
          (fun t : ℝ => fun x : intervalDomainPoint =>
            intervalFullKernelCoupledDuhamelOperator p (intervalNeumannResolverR p) u₀ u t x) v :=
  intervalFullKernelClassicalC1BallEstimates_hmap_dirichlet_initial_cleaner
    (R := intervalNeumannResolverR p)
    hT hH_nn hC_nn hG_init_nn hM_eq hG_u_eq hu₀_sup hext_eq
    hu₀_ext_int hu₀_ext_bound hu₀_ext_C1 hu₀_ext'_int hu₀_ext_one hu₀_ext'_sup
    hSol hSource_sup_local hSource_sup_global hint hSource_int_global
    (fun u v hsnap τ hτ =>
      ShenWork.intervalCoupledSource_resolver_lift_aestronglyMeasurable
        hsnap.isSolution hτ.1 (le_of_lt hτ.2))

end ShenWork.IntervalNeumannFullKernel
