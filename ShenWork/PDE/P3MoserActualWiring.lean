import ShenWork.PDE.IntervalDomainMoserActualAtoms
import ShenWork.PDE.P3MoserDissipationShape
import ShenWork.Paper2.IntervalDomainCrossDiffusionBootstrap

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainMoserClosure

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserActualWiring

open ShenWork.IntervalDomainExistence.P3MoserDissipationShape

theorem abstract_prop25_bootstrap_two_gamma
    {params : CM2Params} {T pExp : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hpExp :
      max (params.N : ℝ)
          (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
        pExp)
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u) :
    AbstractLpBootstrapHypothesis intervalDomain u
      (params.N : ℝ) T (2 * params.γ) pExp := by
  refine ⟨?_, hT, ?_, hLp⟩
  · nlinarith [params.hγ]
  · have hN_lt : (params.N : ℝ) < pExp :=
      lt_of_le_of_lt (le_max_left _ _) hpExp
    have hN_ge_one_nat : 1 ≤ params.N := Nat.succ_le_of_lt params.hN
    have hN_ge_one : (1 : ℝ) ≤ (params.N : ℝ) := by
      exact_mod_cast hN_ge_one_nat
    have h1_lt : (1 : ℝ) < pExp := lt_of_le_of_lt hN_ge_one hN_lt
    have hgammaN_le :
        params.γ * (params.N : ℝ) ≤
          max (params.N : ℝ)
            (max (params.m * (params.N : ℝ))
              (params.γ * (params.N : ℝ))) := by
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hgammaN_lt : params.γ * (params.N : ℝ) < pExp :=
      lt_of_le_of_lt hgammaN_le hpExp
    have hrho_half :
        (2 * params.γ) * (params.N : ℝ) / 2 =
          params.γ * (params.N : ℝ) := by
      ring
    exact max_lt h1_lt (by simpa [hrho_half] using hgammaN_lt)

theorem intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
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
          RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain params :=
  intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB
    hdiss hrel

theorem intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
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
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (params.N : ℝ)
            (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
          pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    Proposition_2_5 intervalDomain params := by
  intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
  have hcross :
      CrossDiffusionBootstrapEstimate intervalDomain params T
        (2 * params.γ) u v :=
    intervalDomain_crossDiffusionBootstrapEstimate_of_classical hsol
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T (2 * params.γ) pExp :=
    abstract_prop25_bootstrap_two_gamma hT hpExp hLp
  rcases hEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨pSeq, rootBound, hQuantEndpoint⟩
  have hLpMono :
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
  exact
    intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
      hboot
      (intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross
        hboot)
      (hdiss hsol hcross hboot)
      (hrel hsol hcross hboot)
      hLpMono
      hQuantEndpoint

#print axioms abstract_prop25_bootstrap_two_gamma
#print axioms intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
#print axioms intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
#print axioms dyadic_root_tower_bound

end ShenWork.IntervalDomainExistence.P3MoserActualWiring

end
