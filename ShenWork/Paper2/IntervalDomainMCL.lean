import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainStructuredMoserPower
import ShenWork.PDE.IntervalDomainAPrioriGlobal

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2.IntervalDomainStructuredMoserData
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMCL

/-- Legacy power estimate previously used to feed the relative Moser
interpolation field.

This statement is false for constant functions: the left side scales like
`A^(p+rho)` while the lower-order term scales only like `A^p`.  It is kept
under an explicit `Old` name for the older conditional route and for the
counterexample module. -/
def OldUnitIntervalPowerGNYoungForMoser : Prop :=
  ∀ rho p eps : ℝ, 0 < rho → 0 < p → 0 < eps →
    ∃ Ceps, 0 ≤ Ceps ∧
      ∀ f : intervalDomain.Point → ℝ,
        ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
        (∀ x, 0 ≤ f x) →
          intervalDomain.integral (fun x => f x ^ (p + rho)) ≤
            eps * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => f y ^ (p / 2)) x) ^ 2) +
            Ceps * intervalDomain.integral (fun x => f x ^ p)

/-- The proved classical-slice unit-interval GN/Agmon package.

This is the satisfiable replacement for the false arbitrary-power Moser
frontier above.  It is intentionally slice-level: the caller supplies
nonnegativity, boundedness, integrability, and the classical derivative data
needed by `agmon_inequality_interval`. -/
def UnitIntervalPowerGNYoungForMoser : Prop :=
  ∀ pExp : ℝ, 1 ≤ pExp →
    ∀ f : intervalDomain.Point → ℝ,
      (∀ x : intervalDomain.Point, 0 ≤ f x) →
      BddAbove (Set.range fun x : intervalDomain.Point => |f x|) →
      IntervalIntegrable (intervalDomainLift f) MeasureTheory.volume 0 1 →
      IntervalIntegrable
        (fun y : ℝ => intervalDomainLift
          (fun x : intervalDomain.Point => (f x) ^ pExp) y)
        MeasureTheory.volume 0 1 →
      ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
      ∀ f' : ℝ → ℝ,
        (∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (intervalDomainLift f) (f' x) x) →
        IntervalIntegrable f' MeasureTheory.volume 0 1 →
        IntervalIntegrable (fun y : ℝ => (intervalDomainLift f y) ^ 2)
          MeasureTheory.volume 0 1 →
        IntervalIntegrable (fun y : ℝ => f' y ^ 2) MeasureTheory.volume 0 1 →
        IntervalIntegrable (fun y : ℝ => intervalDomainLift f y * f' y)
          MeasureTheory.volume 0 1 →
          intervalDomain.integral (fun x : intervalDomain.Point => (f x) ^ pExp) ≤
              (intervalDomainSupNorm f) ^ (pExp - 1) * intervalDomain.integral f ∧
            ∀ x ∈ Set.Icc (0 : ℝ) 1,
              (intervalDomainLift f x) ^ 2 ≤
                (2 / (1 : ℝ)) *
                    (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ 2) +
                  2 * Real.sqrt
                      (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ 2) *
                    Real.sqrt (∫ y in (0 : ℝ)..1, f' y ^ 2)

/-- The classical-slice GN/Agmon package is proved from the interval-domain
slice estimate and `agmon_inequality_interval`. -/
theorem unitIntervalPowerGNYoungForMoser_proved :
    UnitIntervalPowerGNYoungForMoser := by
  intro pExp hpExp f hf_nonneg hf_bdd hf_int hfp_int hf_cont f'
    hf_deriv hf'_int hf_sq_int hf'_sq_int hff'_int
  exact ShenWork.IntervalDomainExistence.intervalDomain_Lp_interpolation_classicalSlice
    (pExp := pExp) hpExp (f := f) hf_nonneg hf_bdd hf_int hfp_int
    hf_cont (f' := f') hf_deriv hf'_int hf_sq_int hf'_sq_int hff'_int

theorem relativeMoserInterpolationBefore_of_unitIntervalPowerGNYoung
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hGN : OldUnitIntervalPowerGNYoungForMoser) :
    RelativeMoserInterpolationBefore intervalDomain u T rho p0 := by
  intro p hp eps heps
  have hrho := AbstractLpBootstrapHypothesis.rho_pos hboot
  have hp_pos : 0 < p := by
    have hp0_gt_one : 1 < p0 := by
      have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
      have hone_le : (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
        le_max_left _ _
      linarith
    linarith
  rcases hGN rho p eps hrho hp_pos heps with ⟨Ceps, hCeps, hineq⟩
  refine ⟨Ceps, hCeps, ?_⟩
  intro t ht0 htT
  have htI : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  rcases hsol.regularity with ⟨_, _, _, _, hclosed, _, _⟩
  have hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    ((hclosed t htI).1.1).continuousOn
  exact hineq (u t) hcont
    (fun x => (IsPaper2ClassicalSolution.u_pos' hsol ht0 htT (x := x)).le)

/-- Regularity now supplies energy, power-integrability, and Lp monotonicity.
The remaining inputs are the committed relative interpolation, the committed
dissipation/drop condition, and the quantitative root-tower endpoint. -/
def structuredMoserBootstrapData_of_regularity_MCL
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {pSeq rootBound : ℕ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hdiss : MoserDissipationDropBefore intervalDomain u T rho p0)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IntervalDomainStructuredMoserBootstrapData u T :=
  intervalDomain_structuredMoserBootstrapData_of_regularity hsol hcross hboot
    hdiss hrel
    (lpMono_of_classical_solution_power_integrable hsol
      (intervalDomain_classical_solution_powerIntegrable hsol))
    hEndpoint

/-- Proposition 2.5 on the concrete interval domain from the non-tautological
Moser inputs.

The proof constructs the bootstrap seed from the assumed `L^p` bound, derives
the relative interpolation from the unit-interval GN/Young frontier, derives
the `LpBootstrapEnergyInequality` through
`intervalDomain_LpBootstrapEnergyInequality_of_regularity`, runs the exponent
chain, and closes with the quantitative root-tower endpoint. -/
theorem Proposition_2_5_intervalDomain_of_MCL_frontiers
    {params : CM2Params}
    (hcross :
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
          CrossDiffusionBootstrapEstimate intervalDomain params T 1 u v)
    (hdiss :
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
          MoserDissipationDropBefore intervalDomain u T 1 pExp)
    (hGN : OldUnitIntervalPowerGNYoungForMoser)
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
  have hboot :
      AbstractLpBootstrapHypothesis
        intervalDomain u (params.N : ℝ) T 1 pExp :=
    abstractBootstrapHypothesis_of_prop25_exponent hT hpExp hLp
  have hrel : RelativeMoserInterpolationBefore intervalDomain u T 1 pExp :=
    relativeMoserInterpolationBefore_of_unitIntervalPowerGNYoung
      hsol hboot hGN
  rcases hEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨pSeq, rootBound, hend⟩
  exact
    (structuredMoserBootstrapData_of_regularity_MCL
      hsol
      (hcross hu₀ hT hsol htrace pExp hpExp hLp)
      hboot hrel
      (hdiss hu₀ hT hsol htrace pExp hpExp hLp)
      hend).boundedBefore

end ShenWork.Paper2.IntervalDomainMCL

end