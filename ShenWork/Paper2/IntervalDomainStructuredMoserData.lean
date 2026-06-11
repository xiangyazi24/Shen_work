import ShenWork.Paper2.IntervalDomainEnergyStep
import ShenWork.Paper2.IntervalDomainLPI

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2.IntervalDomainLPI

noncomputable section

namespace ShenWork.Paper2.IntervalDomainStructuredMoserData

structure Prop25MoserFrontiers
    (u : ℝ → intervalDomain.Point → ℝ) (T pExp : ℝ) where
  pSeq : ℕ → ℝ
  rootBound : ℕ → ℝ
  energy : LpBootstrapEnergyInequality intervalDomain u T 1 pExp
  dissipation : MoserDissipationDropBefore intervalDomain u T 1 pExp
  relative : RelativeMoserInterpolationBefore intervalDomain u T 1 pExp
  powerIntegrable :
    ∀ r : ℝ, 1 < r → ∀ t, 0 < t → t < T →
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
        MeasureTheory.volume 0 1
  endpoint :
    (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
      IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

theorem abstractBootstrapHypothesis_of_prop25_exponent
    {params : CM2Params} {T pExp : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hpExp :
      max (params.N : ℝ)
          (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
        pExp)
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u) :
    AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T 1 pExp := by
  refine ⟨one_pos, hT, ?_, hLp⟩
  have hN_lt : (params.N : ℝ) < pExp := lt_of_le_of_lt (le_max_left _ _) hpExp
  have hN_ge_one_nat : 1 ≤ params.N := Nat.succ_le_of_lt params.hN
  have hN_ge_one : (1 : ℝ) ≤ (params.N : ℝ) := by
    exact_mod_cast hN_ge_one_nat
  have hN_pos : 0 < (params.N : ℝ) := by exact_mod_cast params.hN
  have h1_lt : (1 : ℝ) < pExp := lt_of_le_of_lt hN_ge_one hN_lt
  have hhalf_lt : 1 * (params.N : ℝ) / 2 < pExp := by
    nlinarith
  exact max_lt h1_lt hhalf_lt

theorem lpMono_of_classical_solution_power_integrable
    {params : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1) :
    ∀ {p q : ℝ}, 1 < p → p ≤ q →
      LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u := by
  intro p q hp hpq hq
  exact intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
    (p := p) (q := q) hp hpq
    (fun t ht0 htT x =>
      le_of_lt (IsPaper2ClassicalSolution.u_pos' (x := x) hsol ht0 htT))
    (hpow_int p hp)
    (hpow_int q (lt_of_lt_of_le hp hpq))
    hq

def structuredMoserBootstrapData_of_solution_frontiers
    {params : CM2Params} {N T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hdiss : MoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hpow_int :
      ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
          MeasureTheory.volume 0 1)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IntervalDomainStructuredMoserBootstrapData u T :=
  intervalDomain_structuredMoserBootstrapData_of_energy_interfaces
    hboot henergy hdiss hrel
    (lpMono_of_classical_solution_power_integrable hsol hpow_int)
    hEndpoint

def structuredMoserBootstrapData_of_prop25_frontiers
    {params : CM2Params} {T pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {pSeq rootBound : ℕ → ℝ}
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hpExp :
      max (params.N : ℝ)
          (max (params.m * (params.N : ℝ)) (params.γ * (params.N : ℝ))) <
        pExp)
    (hLp : LpPowerBoundedBefore intervalDomain pExp T u)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T 1 pExp)
    (hdiss : MoserDissipationDropBefore intervalDomain u T 1 pExp)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T 1 pExp)
    (hpow_int :
      ∀ r : ℝ, 1 < r → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ r))
          MeasureTheory.volume 0 1)
    (hEndpoint :
      (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IntervalDomainStructuredMoserBootstrapData u T :=
  structuredMoserBootstrapData_of_solution_frontiers hsol
    (abstractBootstrapHypothesis_of_prop25_exponent hT hpExp hLp)
    henergy hdiss hrel hpow_int hEndpoint

theorem Proposition_2_5_intervalDomain_of_prop25_moser_frontiers
    {params : CM2Params}
    (hfront :
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
          Prop25MoserFrontiers u T pExp) :
    Proposition_2_5 intervalDomain params := by
  refine Proposition_2_5_intervalDomain_of_structured_moser_data ?_
  intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
  let H := hfront hu₀ hT hsol htrace pExp hpExp hLp
  exact structuredMoserBootstrapData_of_prop25_frontiers
    (pSeq := H.pSeq) (rootBound := H.rootBound)
    hT hsol hpExp hLp H.energy H.dissipation H.relative
    H.powerIntegrable H.endpoint

end ShenWork.Paper2.IntervalDomainStructuredMoserData

end
