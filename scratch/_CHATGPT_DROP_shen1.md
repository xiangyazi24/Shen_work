# Q2942 (shen1) — P3MoserAgmonDirectRoute sorry audit

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Pinned audit ref: `fcf449d0`  
Scope: source-level audit and Lean implementation guidance; no project source edits in this drop.

## Executive answer

At the pinned ref `fcf449d0`, the two true `sorry`s in `ShenWork/PDE/P3MoserAgmonDirectRoute.lean` are:

1. `intervalDomain_all_Lp_of_agmon_bootstrap_no_drop`, the no-drop all-`Lp` chain theorem.
2. `intervalDomain_Proposition_2_5_of_agmon_no_drop`, the Proposition 2.5 wrapper that depends on the no-drop chain.

The first is **not closable by wiring to the existing theorems visible at that ref**. It asks for a new no-drop Gronwall / integrated-energy chain: from the full pointwise differential inequality

```lean
(1 / p) * deriv Y_p t + A * G_p t + B * Y_p t ≤ K * Z_p t + L
```

together with Agmon interpolation, derive a usable pointwise Moser-gradient step or a direct all-`Lp` chain. The existing `IntervalDomainChain.moser_iteration_chain` consumes an already-dropped step

```lean
A * G_p t ≤ K * Z_p t + L
```

and the visible drop route obtains that step only through `MoserDissipationDropBeforeNonnegB`. The integrated route in `P3MoserIntegratedClosure` is the honest replacement, but it is a different first-crossing/frontier route, not a proof of this direct Agmon no-drop theorem.

The second sorry is routine **once** the first theorem is available. It is basically the old `intervalDomain_Proposition_2_5_of_agmon` proof with the call switched from `intervalDomain_all_Lp_of_agmon_bootstrap` to the no-drop chain. But because the first theorem is not currently derivable from existing APIs, the original second statement is not independently closable either.

Important source-state note: connector-visible current `main` has already applied the safe repair: it replaces the original no-drop claim by an explicit frontier `AgmonNoDropEnergyReductionBefore`, adds that frontier as `hreduce`, and closes both theorem bodies. So if your local checkout is still exactly `fcf449d0`, cherry-pick that change or apply the patch shape below. If your checkout is connector-visible `main`, there should no longer be true sorries in this file.

## Why the first sorry is not theorem-wiring

The relevant existing theorem chain is:

```lean
IntervalDomainChain.lp_bootstrap_single_step_abstract
IntervalDomainChain.moser_iteration_chain
```

These require the dropped pointwise energy input

```lean
∀ t, 0 < t → t < T →
  A * D.integral (fun x => (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
    K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const
```

The theorem

```lean
intervalDomain_LpBootstrapEnergyInequality_of_regularity
```

only gives the full differential inequality, still containing the derivative and `B * Y_p`. The old proof with drop does exactly:

```lean
have henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
  intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
...
rcases henergy p hp with ⟨A, hA, B, hB, K, hK, L_const, hfull⟩
...
have hdrop_t := hdiss p hp A B K L_const hB.le hfull t ht0 htT
linarith
```

Without `hdiss` or a new integrated/Gronwall lemma, there is no visible theorem that converts `hfull` into the dropped `hstep` demanded by `moser_iteration_chain`.

## Minimal honest patch

This is the patch shape already present on connector-visible current `main`. It does **not** prove the missing Gronwall step. It records it as an explicit frontier and then reuses the existing chain machinery.

```lean
import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.Paper2.IntervalDomainChain
import ShenWork.PDE.P3MoserDissipationShape

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

/-- The missing no-drop reduction needed by the direct Agmon route.

`LpBootstrapEnergyInequality` provides the full pointwise energy inequality with
a time derivative and lower-order term.  The direct no-drop route needs an
additional Gronwall/integrated-energy argument before it can feed
`moser_iteration_chain`: namely, a pointwise Moser-gradient step
`A G_p(t) <= K Z_p(t) + L`.  This predicate records exactly that remaining
frontier, without asserting it follows from the current abstract API. -/
def AgmonNoDropEnergyReductionBefore
    (u : ℝ → intervalDomain.Point → ℝ) (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    ∃ A > 0, ∃ K > 0, ∃ L_const,
      ∀ t, 0 < t → t < T →
        A * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) ≤
        K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) +
          L_const

/-- Version WITHOUT `MoserDissipationDropBeforeNonnegB`, conditional on the
honest no-drop energy-reduction frontier. -/
theorem intervalDomain_all_Lp_of_agmon_bootstrap_no_drop
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hreduce : AgmonNoDropEnergyReductionBefore u T rho p0)
    (hinterp : AgmonAbsorbedInterpolationBefore u T rho p0)
    (hrho : 0 < rho) :
    ∀ n : ℕ, LpPowerBoundedBefore intervalDomain (p0 + n * rho) T u := by
  have _henergy :
      LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
  refine IntervalDomainChain.moser_iteration_chain
    (D := intervalDomain) (u := u) (T := T) (p0 := p0) (rho := rho)
    hrho (AbstractLpBootstrapHypothesis.initial_lp_bound hboot) ?_
  intro p hp
  rcases hreduce p hp with ⟨A, hA, K, hK, L_const, hstep⟩
  refine ⟨A, hA, K, hK, L_const, hstep, ?_⟩
  exact intervalDomain_gn_absorbed_interpolation_of_agmon hinterp hp

/-- Proposition 2.5 WITHOUT `MoserDissipationDropBeforeNonnegB`, conditional on
the explicit no-drop energy-reduction frontier. -/
theorem intervalDomain_Proposition_2_5_of_agmon_no_drop
    (params : CM2Params)
    (hreduce :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          AgmonNoDropEnergyReductionBefore u T rho p0)
    (hinterp :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          AgmonAbsorbedInterpolationBefore u T rho p0)
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
  have hrho : 0 < 2 * params.γ := by
    nlinarith [params.hγ]
  have hchain :
      ∀ n : ℕ,
        LpPowerBoundedBefore intervalDomain (pExp + n * (2 * params.γ)) T u :=
    intervalDomain_all_Lp_of_agmon_bootstrap_no_drop
      hsol hcross hboot (hreduce hsol hcross hboot)
      (hinterp hsol hcross hboot) hrho
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
  have hAll :
      ∀ r > 1, LpPowerBoundedBefore intervalDomain r T u :=
    all_exponents_of_chain_and_lp_mono hrho hchain hLpMono
  rcases hEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
    ⟨pSeq, rootBound, hQuantEndpoint⟩
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hQuantEndpoint hAll)

end ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute
```

## Repository action recommendation

Best action for the `fcf449d0` state: **do not keep the original sorry theorems as WIP in an active `.lean` file**. Either:

1. apply the explicit-frontier patch above, which is what connector-visible current `main` already does; or
2. move the direct Agmon file to a deprecated/scratch markdown note if the route is not intended to remain a maintained conditional API.

Keeping the original `sorry`s in a Lean file does not preserve an honest 0-sorry headline audit. Replacing them by `AgmonNoDropEnergyReductionBefore` does preserve honesty because the missing Gronwall/no-drop content is now a named hypothesis, not hidden in a proof hole. Since code search shows no Lean file imports `P3MoserAgmonDirectRoute` and `ShenWork.lean` does not import it, moving/deprecating is also low risk. But the explicit-frontier patch is the least disruptive if you want to keep the route for comparison.

## Remaining real residual/frontier assumptions visible from inspected sources

### Paper 1

* `Paper1PropositionFrontierData` / `Proposition11FrontierAudit.FrontierFields`: global Cauchy existence, negative-sensitivity max/limsup bound, and positive-sensitivity boundedness/limsup remain genuine frontiers.
* `paper1_Theorem_1_1_of_constructionNegSMPProvider`: still conditional on `ConstructionNegSMPProvider` and the positive critical frozen-stationary branch.
* `Paper1PositiveCriticalFrozenStationaryBranch`: requires `FrozenStationaryWaveProfile`, `ShenUpperBoundPositive`, and right-tail asymptotics for the positive critical branch.
* Theorem 1.2/1.3 mainline wrappers consume `Paper1MainlineExistence`; they do not construct it.

### Paper 2

* Generic `Paper2BootstrapEstimateBranchData`: `lemma26`, `lemma27`, `prop22`, `prop23`, `prop24MassDeriv`, `prop24Compare`, and `prop25` are statement-layer branch inputs.
* Generic `Paper2MainSolutionBranchData`: `nonminimal`, `minimal`, `slowDiffusion`, `critical`, `localBranch`, and `globalBranch` are assumed solution branches.
* `IntervalDomainPaper2BootstrapEstimateThinFrontierData`: still asks for Lemma 2.6, Lemma 2.7, Proposition 2.2, and Proposition 2.3 branches; Proposition 2.4 is closed for the interval domain in that route.
* `IntervalDomainPaper2Prop25ActualAtomFrontierData`: `moserDissipation`, `relativeMoserInterpolation`, and `quantitativeEndpoint` are the actual Prop. 2.5 atoms.
* `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData`: lowers relative Moser to `relativeMassGradient`, but still carries `moserDissipation` and `quantitativeEndpoint`.
* `IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData`: lowers the endpoint to `terminalEndpoint`, but still carries the nonnegative-B dissipation atom and mass-gradient interpolation data.
* `IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData`: lowers dissipation to `rawMoserDrop`, but that raw drop is still a frontier.
* `IntervalDomainPaper2Prop25IntegratedStepFrontierData`: `integratedStep` and `quantitativeEndpoint` remain frontiers.
* `IntervalDomainPaper2Prop25IntegratedMoserFrontierData`: `classicalRegularity`, `integratedDissipation`, `relativeMoserInterpolation`, and `quantitativeEndpoint` remain frontiers.
* `IntervalDomainPaper2Prop25LowerUpperFrontierData`: `lowerUpperFrontiers` and `quantitativeEndpoint` remain frontiers.
* The positive-solution interpolation routes prove the interpolation component, but still rely on the common dissipation/gradient/mass/power/energy-from-cross-diffusion and endpoint/global-extension/bootstrap/eventual-bound fields visible in the frontier records.
* The `χ₀ = 0` local-free actual-atom routes discharge local existence internally, but still retain `globalExtension`, slow/critical/strong bootstrap, critical/strong eventual sup-bound, and the selected Prop. 2.5 atom package.

### Paper 3

* `IntervalDomainPaper3NegativeSensitivityFrontierData`: `globalSolution` and `eventualSupBound` are residuals.
* `IntervalDomainPaper3Proposition1FrontierData`: `negativeBound` and `criticalExistence` are residuals.
* `IntervalDomainPaper3Proposition1WithTheorem13FrontierData`: `proposition12And14` and `theorem13` are inputs.
* `IntervalDomainPaper3Proposition1FromPaper2TheoremsData`: `negativeBound`, `theorem12`, and `theorem13` are inputs.
* `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData`: `negativeBound` and `paper2Main` are inputs.
* `intervalDomain_paper3_coreStatementTargets_of_coreExistence`: the remaining inputs are `IntervalDomainInitialContinuityRaw p` and `IntervalDomainSectorialMainlineCoreExistence p uBar`.
* `IntervalDomainPaper3CoreStatementLinear22Data`: the separated inputs are `initialContinuity`, `persistence`, `theorem22Nonminimal`, and `theorem22Minimal`.

## Bottom line

For the pinned sorry state, the honest answer is: the first original no-drop theorem is a missing analytic theorem, not a wiring bug; the second is routine after the first. The safe 0-sorry-preserving implementation is to make the missing no-drop reduction an explicit frontier, as connector-visible current `main` already does.
