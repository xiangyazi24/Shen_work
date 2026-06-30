# Q2437 shen1 — next honest patch after integrated Moser Stage 1

Repo: `xiangyazi24/Shen_work`

Audited ref: `main` at `830352766089c95945fc741ccc208762862c54c6`

## Verdict

Yes.  It is useful and honest to add routine actual-atom consumers in

```text
ShenWork/PDE/P3MoserActualWiring.lean
```

that take a supplied

```lean
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

directly.

This does **not** hide the hard theorem.  It simply creates the consumer side of the integrated-Moser route, parallel to the existing nonnegative-`B` consumers.  The hard theorem remains the production of the supplied step from

```lean
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
RelativeMoserInterpolationBefore intervalDomain u T rho p0
IntegratedMoserFirstCrossingRegularity intervalDomain u T p0
```

or a future equivalent regularity package.

The Stage 1 file already proves the routine ladder/endpoint closure from a supplied step:

```lean
ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.IntegratedMoserFirstCrossingStep
ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.moser_iteration_chain_of_integrated_first_crossing_step
ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.all_exponents_of_integrated_first_crossing_step_lpmono
ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.intervalDomain_boundedBefore_of_integrated_first_crossing_step
```

The existing `P3MoserActualWiring` file already has the same consumer pattern for pointwise/nonnegative-`B` atoms:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

so the new integrated-step consumers are a natural, minimal next patch.

## Why this is honest

The proposed consumers do not mention or consume

```lean
IntegratedMoserDissipationDropBefore
```

at all.  Their input is already the one-step result:

```lean
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

Therefore they do not create the forbidden false route

```lean
IntegratedMoserDissipationDropBefore → MoserDissipationDropBeforeNonnegB
```

and they do not claim the first-crossing theorem has been proved.  They merely say: *once a producer supplies the first-crossing step for a classical solution/cross-diffusion/bootstrap triple, the existing Moser closure gives Corollary 2.1 and Proposition 2.5.*

This is exactly analogous to the current nonnegative-`B` route, except the supplied atom is now closer to the faithful integrated route.

## Minimal patch

Patch file:

```text
ShenWork/PDE/P3MoserActualWiring.lean
```

### Import change

Add the Stage 1 import:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

The top of the file should become:

```lean
import ShenWork.PDE.IntervalDomainMoserActualAtoms
import ShenWork.PDE.P3MoserDissipationShape
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainCrossDiffusionBootstrap
```

### Namespace open

Add:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

near the existing open block, for example:

```lean
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

### New consumer theorems

Place these after `abstract_prop25_bootstrap_two_gamma` and before the existing nonnegative-`B` consumers, or after the existing nonnegative-`B` consumers.  I prefer after `abstract_prop25_bootstrap_two_gamma`, because both endpoint consumers reuse that bootstrap helper.

```lean
/-- Corollary 2.1 from a supplied integrated first-crossing Moser step.

This is the routine consumer side of the integrated-Moser route.  The hard
analytic theorem is not proved here: it is the supplied `hstep` field. -/
theorem intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    {params : CM2Params}
    (hstep :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          IntegratedMoserFirstCrossingStep intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain params := by
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0, hp0Lp⟩
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0, hp0Lp⟩
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
    all_exponents_of_integrated_first_crossing_step_lpmono
      hboot (hstep hsol hcross hboot) hLpMono pExp hpExp

/-- Proposition 2.5 from a supplied integrated first-crossing Moser step and the
existing quantitative endpoint.

This does not produce the first-crossing step from integrated dissipation; it
only consumes the step as an atom. -/
theorem intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    {params : CM2Params}
    (hstep :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
          IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
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
    intervalDomain_boundedBefore_of_integrated_first_crossing_step
      hboot (hstep hsol hcross hboot) hLpMono hQuantEndpoint
```

### Optional axiom print checks

Add these beside the existing `#print axioms` block:

```lean
#print axioms intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
#print axioms intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

They should be routine wrappers over existing theorems.  I did not run Lean here; the code is source-derived from the current APIs and mirrors the existing nonnegative-`B` consumers.

## Why not add Paper2 statement wrappers yet?

The two `P3MoserActualWiring` consumers are the right first patch.  They stabilize the new integrated-step consumer API without duplicating the large `IntervalDomainStatementAssembly.lean` route family.

After these build, the next optional wrapper layer can introduce a Paper2 Prop25 atom package such as:

```lean
structure IntervalDomainPaper2Prop25IntegratedStepTerminalEndpointFrontierData
    (p : CM2Params) : Prop where
  firstCrossingStep :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
  terminalEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ q R : ℝ,
          0 < q ∧ 0 ≤ R ∧
            ((∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserPointwisePowerControlBefore u T q R)
```

But that wrapper is slightly more bookkeeping, and it is better to first land the two consumers above in `P3MoserActualWiring`.

## Non-goals and no-go routes

Do not add a theorem producing:

```lean
IntegratedMoserFirstCrossingStep
```

from

```lean
IntegratedMoserDissipationDropBefore
RelativeMoserInterpolationBefore
IntegratedMoserFirstCrossingRegularity
```

in this patch.  That is the hard analytic theorem.

Do not route through:

```lean
MoserDissipationDropBeforeNonnegB
MoserDissipationDropBefore
OldUnitIntervalPowerGNYoungForMoser
IntervalDomainLemma41.IntervalDomainInterpolation
```

unless a separate theorem genuinely proves the needed hypothesis.  The point of the proposed patch is to avoid the pointwise/nonnegative-`B` bridge entirely.

## Better small patch?

I do not see a better small patch than these two consumers.  The Stage 1 closure already exists; `P3MoserActualWiring` is exactly the file where solution/cross/bootstrap atoms are turned into Paper2 Corollary 2.1 and Proposition 2.5.  Adding these consumers makes the integrated-step route available to the rest of the statement assembly without pretending that the first-crossing theorem is done.
