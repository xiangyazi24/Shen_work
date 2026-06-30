# Q2445 shen1 — Paper3 integrated-step wrapper honesty audit

Repo: `xiangyazi24/Shen_work`

Audited upstream ref: `main` at `830352766089c95945fc741ccc208762862c54c6`

Subject: proposed local patch adding integrated-step consumers plus a Paper3 actual-linear wrapper route.

## Verdict

The proposed Paper3 wrapper layer is **not logically honest** if it converts a supplied

```lean
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

into the old residual surface by first proving

```lean
hcor : Corollary_2_1 intervalDomain p
```

and then using theorem names of the form

```lean
moserDissipationDropBeforeNonnegB_of_corollary21 hcor hsol hcross hboot
relativeMoserInterpolationBefore_of_corollary21 hcor hsol hcross hboot
```

to fill the old `moserDissipation` / `relativeMoserInterpolation` fields.

That route is backwards.  `Corollary_2_1` is the all-`Lp` conclusion produced by Moser closure.  The old residual fields are local analytic inputs used to produce that conclusion in the old route.  Deriving those inputs from the conclusion creates a misleading circular interface, even if a local theorem with that name can be made to typecheck by carrying an overstrong or hidden premise.

The honest patch is: keep the integrated-step consumers in `P3MoserActualWiring.lean`, then wire Paper3 to `IntervalDomainMassLpSmoothingRouteResiduals` **directly** using those consumers.  Do not convert the integrated route back into `MoserDissipationDropBeforeNonnegB` or `RelativeMoserInterpolationBefore`.

## Why the Corollary-to-old-residual route is bad

Current upstream source has the old actual-atom consumers:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

and the old Paper3 route ultimately feeds old-style fields through

```lean
IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals
```

where:

```lean
allLpBoundFromBootstrap := h.corollary21
endpointBoundFromLp := h.proposition25
```

The old `corollary21` and `proposition25` are produced from:

```lean
h.moserDissipation
h.relativeMoserInterpolation
h.quantitativeEndpoint
```

This old direction is honest.

The proposed direction:

```lean
integratedStep
  -> Corollary_2_1
  -> MoserDissipationDropBeforeNonnegB
  -> old route
```

is not.  It reverses the proof dependencies.  In particular:

- `Corollary_2_1` says that under cross-diffusion bootstrap and one initial `Lp` seed, all finite exponents are bounded.
- `MoserDissipationDropBeforeNonnegB` is a pointwise-in-time lower bound on the derivative-plus-mass term after a PDE energy inequality is supplied.
- `RelativeMoserInterpolationBefore` is a local interpolation estimate involving the Moser gradient and the lower-order `Y_p` term.

The first statement does not contain the derivative/gradient information of the latter two.  The source already treats pointwise drop as a stronger/different shape: `P3MoserDissipationShape.lean` has `unitLinearDrop_not_MoserDissipationDropBeforeNonnegB` and documents the integrated predicate as the faithful replacement for pointwise drop.  A theorem deriving pointwise drop from `Corollary_2_1` would therefore be a red flag unless it has substantial additional analytic hypotheses; if it has those hypotheses, it should not be named as a projection from Corollary 2.1.

The same concern applies to a theorem deriving `RelativeMoserInterpolationBefore` from `Corollary_2_1`: all-`Lp` bounds do not by themselves provide a gradient interpolation estimate of the form

```lean
Y_{p+rho}(t) ≤ eps * G_p(t) + Ceps * Y_p(t)
```

uniformly on the open time slab.

## What should be committed now

Commit the integrated-step consumers and a direct integrated-step residual surface.  Leave out all Corollary-to-old-residual conversions.

### 1. Keep/add the consumers in `P3MoserActualWiring.lean`

This part is good.  The file should import Stage 1:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

and open:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Then add:

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

Optional checks:

```lean
#print axioms intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
#print axioms intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
```

### 2. Add a direct integrated-step route residual surface

Do this in:

```text
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

near `IntervalDomainMassLpSmoothingMoserLadderResiduals`, because this is exactly where lower-level Moser atoms are turned into `IntervalDomainMassLpSmoothingRouteResiduals`.

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Lower-level Moser inputs where the analytic first-crossing theorem has
already supplied the integrated one-step Moser ladder step.

This deliberately bypasses the old `MoserDissipationDropBeforeNonnegB` and
`RelativeMoserInterpolationBefore` fields. -/
structure IntervalDomainMassLpSmoothingIntegratedStepResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  integratedStep :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingIntegratedStepResiduals

theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    h.integratedStep

theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    h.integratedStep h.quantitativeEndpoint

/-- Build the old route-residual package without deriving old Moser atoms.  The
only outputs needed by `IntervalDomainMassLpSmoothingRouteResiduals` are
Corollary 2.1 and Proposition 2.5, so they are supplied directly from the
integrated-step consumers. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  driftBoundFromMass := by
    intro u₀ hu₀ T hT u v hsol htrace hmass
    have hCor21 : Corollary_2_1 intervalDomain p := h.corollary21
    have hProp25 : Proposition_2_5 intervalDomain p := h.proposition25
    have hspatial :
        IntervalDomainL2SpatialAbsorptionEstimate p T u v hsol hmass :=
      intervalDomainL2SpatialAbsorptionEstimate_of_classical
        h.boundednessHyp hsol hmass
    have huniform :
        IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequalityUniformCeps_of_classicalSolution
        hsol
    have hhalf :
        IntervalDomainL2HalfEnergyDifferentialInequality p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequality_of_classicalSolution hsol
    have habsorbing :
        IntervalDomainL2AbsorbingDifferentialInequalityResult p T u :=
      IntervalDomainL2AbsorbingDifferentialInequality
        h.boundednessHyp.1 hsol hmass hspatial huniform
    have hregularity : IntervalDomainL2SeedRegularityFrontier T u :=
      h.l2SeedRegularity u₀ hu₀ T hT u v hsol htrace
    have hintegrated :
        IntervalDomainL2AbsorbingIntegratedInequalityResult p T u :=
      IntervalDomainL2AbsorbingIntegratedInequality
        h.boundednessHyp.2.1 hsol habsorbing hregularity
    have hL2 :
        LpPowerBoundedBefore intervalDomain 2 T u :=
      intervalDomainL2PowerBoundedBefore_of_absorbingIntegratedInequality
        hsol hintegrated hregularity
    have hbootstrap :
        ∃ rho > 0,
          CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
            ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
              LpPowerBoundedBefore intervalDomain p0 T u :=
      intervalDomainL2BootstrapSeed_of_L2PowerBoundedBefore
        h.boundednessHyp hu₀ hT hsol htrace hhalf hL2
    have hbounded :
        IsPaper2BoundedBefore intervalDomain T u :=
      intervalDomainBoundedBefore_of_corollary21_and_proposition25
        hCor21 hProp25 hu₀ hT hsol htrace hbootstrap
    have hpoint : PointwiseBoundedBefore T u :=
      pointwiseBoundedBefore_of_boundedBefore_and_supNormControls hbounded
        (supNormControlsPointwiseBefore_of_classicalSolution hsol)
    exact IntervalDomainChemotacticDriftBound_of_LinfBound hsol hpoint
  l2SeedRegularity := h.l2SeedRegularity
  allLpBoundFromBootstrap := h.corollary21
  endpointBoundFromLp := h.proposition25

def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_routeResiduals.aprioriBound

end IntervalDomainMassLpSmoothingIntegratedStepResiduals
```

This copies the already-honest `driftBoundFromMass` proof pattern, but the Moser outputs come directly from the integrated-step consumers.

### 3. Paper3 actual-linear wrapper: use the direct route

In `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`, do **not** convert to `IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals` or `...CERawGradResiduals` by fabricating old Moser fields from Corollary 2.1.

Instead add a closed-energy integrated-step residual and convert it to `IntervalDomainMassLpSmoothingIntegratedStepResiduals`:

```lean
/-- Closed-energy actual-linear-small residuals using a supplied integrated
first-crossing step.  This route bypasses the old pointwise drop and relative
Moser residual fields. -/
structure IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals
    (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  closedEnergyTrace :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        Nonempty
          (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u)
  integratedStep :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals

def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  integratedStep := h.integratedStep
  quantitativeEndpoint := h.quantitativeEndpoint

end IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals
```

Then a minimal sectorial facts wrapper:

```lean
/-- Sectorial mainline facts using closed energy and a supplied integrated
first-crossing step. -/
structure IntervalDomainSectorialMainlineMoserActualLinearSmallCEIntegratedStepFacts
    (p : CM2Params) : Prop where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  continuation :
    IntervalDomainStandardContinuationGluingData p
  massLpSmoothing :
    IntervalDomainMassLpSmoothingMoserActualLinearSmallCEIntegratedStepResiduals p

namespace IntervalDomainSectorialMainlineMoserActualLinearSmallCEIntegratedStepFacts

def to_aprioriActualLinearSmallFacts
    {p : CM2Params}
    (h : IntervalDomainSectorialMainlineMoserActualLinearSmallCEIntegratedStepFacts p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainSectorialMainlineAprioriActualLinearSmallFacts p where
  spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
  continuation := h.continuation
  massLpSmoothing :=
    (h.massLpSmoothing.to_integratedStepResiduals ha hχ0).to_routeResiduals

end IntervalDomainSectorialMainlineMoserActualLinearSmallCEIntegratedStepFacts
```

Then the Paper3 mainline wrapper can reuse the existing a-priori actual-linear route:

```lean
/-- Concrete interval-domain Paper3 mainline frontiers using closed energy and a
supplied integrated first-crossing step. -/
structure IntervalDomainPaper3MainlineMoserActualLinearSmallCEIntegratedStepFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core : IntervalDomainSectorialMainlineMoserActualLinearSmallCEIntegratedStepFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability :
    IntervalDomainPaper3Stability23To25FrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Assemble the concrete interval-domain Paper3 mainline from the closed-energy
integrated-step route. -/
theorem intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEIntegratedStepFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallCEIntegratedStepFrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_aprioriActualLinearSmallFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    { core := hData.core.to_aprioriActualLinearSmallFacts ha hχ0
      compactness := hData.compactness
      stability := hData.stability }
```

The `hb` argument is still present because the surrounding actual-linear wrapper family has it; this direct route above does not need to synthesize `boundednessHyp` from a boundedness core, because the proposed integrated-step residual already carries `boundednessHyp` explicitly.

Add statement wrappers only if the local patch needs them immediately.  The pattern is direct and honest:

```lean
structure IntervalDomainPaper3StatementMoserActualLinearSmallCEIntegratedStepFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallCEIntegratedStepFrontierData
      p M0 uBar vLower K

theorem intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCEIntegratedStepFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallCEIntegratedStepFrontierData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_frontierData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCEIntegratedStepFrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩
```

## What to leave out

Do **not** commit any of the following in this patch:

```lean
moserDissipationDropBeforeNonnegB_of_corollary21
relativeMoserInterpolationBefore_of_corollary21
```

Do **not** commit a conversion from the new integrated-step residual package to:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallCEGradResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals
```

if that conversion fills old Moser fields from `Corollary_2_1`.

Do **not** commit any theorem producing:

```lean
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

from integrated dissipation and relative interpolation yet.  That is the hard theorem and should remain as a frontier.

## Recommended commit split

Commit now:

1. `P3MoserActualWiring.lean` integrated-step consumers.
2. `IntervalDomainMoserLadderAtoms.lean` direct `IntervalDomainMassLpSmoothingIntegratedStepResiduals` route, if the Paper3 wrapper needs a common route-residual surface.
3. `IntervalDomainActualLinearStatementAssembly.lean` direct CE-integrated-step wrappers as above, if you want the Paper3 name now.

Leave out:

1. All Corollary-to-old-residual conversions.
2. The proposed conversion of the new package to the old actual-linear Moser residual package via Corollary 2.1.
3. Any theorem claiming to derive the first-crossing step from `IntegratedMoserDissipationDropBefore`.

This keeps the dependency graph honest:

```text
integratedStep supplier
  -> P3MoserActualWiring integrated consumers
  -> Corollary_2_1 / Proposition_2_5
  -> IntervalDomainMassLpSmoothingRouteResiduals
  -> Paper3 mainline
```

not:

```text
integratedStep supplier
  -> Corollary_2_1
  -> fake old Moser atoms
  -> old Moser route
  -> Paper3 mainline
```
