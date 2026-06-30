# Q2410 shen1 — post raw-drop headline frontier audit

Repo: `xiangyazi24/Shen_work`

Audited ref: `main` at `c89c01043b5ae73d61089da2631f7e53a49d65cf`

Scope: current Paper1/Paper2/Paper3 headline statement wrappers after the Paper2 raw-drop mass-gradient terminal-endpoint actual-atom route.

## Verdict

The new Paper2 raw-drop route is correctly wired through the preferred `χ₀ = 0` headline and full-statement wrappers.  After this commit, I do **not** see another honest Paper2 statement-layer reduction that is buildable from existing proved code without changing the Moser consumer theorem family.

The smallest honest next reduction that is still buildable as a no-axiom/no-`sorry` patch is a **Paper1 wrapper cleanup** in

```text
ShenWork/Paper1/PositiveRawRouteAAssembly.lean
```

It should add a direct conversion

```lean
Paper1PositiveLowerRawCapRouteARemainingParamData →
  Paper1PositiveLowerPinnedRawRemainingContactBranchData
```

and the corresponding hmk-aware alias

```lean
Paper1PositiveLowerRawCapRouteAHmkConstParamData →
  Paper1PositiveLowerPinnedRawRemainingContactBranchData
```

This is not new analysis.  It preserves the already-exposed `RawRemainingContact` residual label instead of immediately converting through

```lean
paper1_routeASmoothParamData_of_routeARemainingParamData
paper1_positiveRawSmoothContactData_of_routeARemainingParamData
```

The currently deeper Paper2 next step is the integrated-first-crossing Moser chain, but that is **not** a wrapper-only patch: existing consumers are pointwise/nonnegative-`B` consumers and must be replaced by new integrated consumers.  Do not add an integrated-to-pointwise adapter.

## Current Paper2 status at `c89c0104`

The raw-drop actual-atom package is present:

```lean
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
```

with fields

```lean
rawMoserDrop
relativeMassGradient
terminalEndpoint
```

and the proved conversion

```lean
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.toTerminalEndpoint
```

which packages `rawMoserDrop` using

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.moserDissipationDropBeforeNonnegB_of_raw_drop
```

The raw-drop route has the expected local targets:

```lean
intervalDomainPaper2_Proposition_2_5_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData
intervalDomainPaper2_Corollary_2_1_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData
intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomRawDropMassGradientTerminalEndpointFrontierData
```

It is also threaded through the `χ₀ = 0` Theorem 1.2/1.3 route:

```lean
IntervalDomainPaper2Theorem12And13ChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
IntervalDomainPaper2Theorem12And13ChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData.toTerminalEndpointCor21
intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
```

and through the main-theorem route:

```lean
IntervalDomainPaper2MainTheoremChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomRawDropMassGradientTerminalEndpointCor21LocalFreeFrontierData
```

The preferred headline alias requested in the prompt is present:

```lean
IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomRawDropMassGradientTerminalEndpointCor21FrontierData
intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomRawDropMassGradientTerminalEndpointCor21FrontierData
```

The preferred full-statement solution-interpolation alias is also present:

```lean
IntervalDomainPaper2PreferredChiZeroStatementActualAtomRawDropMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData
intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomRawDropMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData
```

and its underlying full-statement data route is

```lean
IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinSolutionInterpolationFrontierData
IntervalDomainPaper2StatementChiZeroActualAtomRawDropMassGradientTerminalEndpointCor21Section2ThinSolutionInterpolationFrontierData.toTerminalEndpoint
```

So the current best Paper2 wrapper route has already lowered:

```lean
MoserDissipationDropBeforeNonnegB
RelativeMoserInterpolationBefore
IntervalDomainMoserQuantitativeEndpoint pSeq rootBound
```

to:

```lean
rawMoserDrop
relativeMassGradient
terminalEndpoint
```

and uses positive solution-slice interpolation, not the refuted global interpolation premise, for the full-statement a-priori package.

## Paper2 residuals that remain genuine

The current preferred Paper2 route still honestly carries:

```lean
IntervalDomainPaper2BootstrapEstimateThinFrontierData
IntervalDomainPaper2Proposition11ChiZeroFrontierData.finiteHorizonAlternative
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
IntervalDomainPaper2GlobalExtensionFrontier
slowBootstrap
criticalBootstrap
criticalEventualSupBound
strongBootstrap
strongEventualSupBound
rawMoserDrop
relativeMassGradient
terminalEndpoint
```

None of these is currently discharged by a proved generic wrapper of the same kind as the raw-drop bridge.

In particular, do not add a theorem of the following form:

```lean
-- no-go adapter: do not add this as a claimed consequence of current code
theorem MoserDissipationDropBeforeNonnegB_of_integratedMoserDissipationDropBefore
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ} :
    IntegratedMoserDissipationDropBefore D u T rho p0 →
      MoserDissipationDropBeforeNonnegB D u T rho p0 :=
  ...
```

That would be the same wrong direction as the pointwise-drop diagnosis: the integrated estimate is a different consumer shape, not a producer of the current pointwise `Y' + B Y ≥ 0` atom.

## Why Paper2 integrated-first-crossing is not the next buildable wrapper

The source already defines the honest integrated shape:

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.IntegratedMoserDissipationDropBefore
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.integratedMoserDissipationDropBefore_of_integrated_energy
```

but the current consumers still require

```lean
MoserDissipationDropBeforeNonnegB
```

through the chain:

```lean
moser_step_of_energy_nonnegB_relative_interpolation
moser_iteration_chain_of_energy_nonnegB_relative_interpolation
all_exponents_of_energy_nonnegB_relative_interpolation_lpmono
intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation
intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation_inside
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB
intervalDomain_endpointBoundFromLp_of_quantitative_root_tower_nonnegB
```

and then in `P3MoserActualWiring`:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

Therefore the integrated-first-crossing route is the next real **Paper2 analytic/Moser closure project**, not a small statement-level patch.  The minimal theorem family should be new parallel consumers, not adapters to the old pointwise consumer.  The family should look like this in `ShenWork/PDE/P3MoserDissipationShape.lean` or a new imported file if it becomes large:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserDissipationShape

/-- Integrated first-crossing Moser step.  This is the real replacement for
`moser_step_of_energy_nonnegB_relative_interpolation`; it should produce the
next Lp bound directly, not a pointwise nonnegative-B drop. -/
theorem moser_step_of_integrated_dissipation_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 p : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hLp : LpPowerBoundedBefore D p T u) :
    LpPowerBoundedBefore D (p + rho) T u := by
  -- real first-crossing proof: use integrated energy on `[t₁,t₂]`,
  -- relative interpolation, and the crossing argument.
  -- Do not derive `MoserDissipationDropBeforeNonnegB`.
  -- no sorry in final patch
  admit

/-- Integrated Moser iteration chain. -/
theorem moser_iteration_chain_of_integrated_dissipation_relative_interpolation
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  -- induction using the integrated step
  admit

/-- All exponents from integrated dissipation plus Lp monotonicity. -/
theorem all_exponents_of_integrated_dissipation_relative_interpolation_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  admit

/-- Interval-domain boundedness from integrated dissipation and terminal endpoint. -/
theorem intervalDomain_boundedBefore_of_integrated_dissipation_relative_interpolation
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hinteg : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  admit

end ShenWork.IntervalDomainExistence.P3MoserDissipationShape
```

The `admit`s above are placeholders in the theorem-family sketch only; the point is that this route is real proof work.  A buildable patch cannot include these until the first-crossing proof is actually formalized.

Once the core family exists, add parallel actual-atom endpoints in `P3MoserActualWiring.lean`, for example:

```lean
intervalDomain_allLpBoundFromBootstrap_of_integrated_atoms
intervalDomain_endpointBoundFromLp_of_integrated_atoms
```

and only then add Paper2 statement wrappers whose Prop25 atom is

```lean
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

instead of `rawMoserDrop` or `MoserDissipationDropBeforeNonnegB`.

## Smallest buildable patch now: Paper1 Route-A remaining-contact cleanup

Current Paper1 source already has the target residual interface:

```lean
Paper1PositiveLowerPinnedRawRemainingContactBranchData
paper1_positiveLowerPinnedRawSmoothContactData_of_remainingContactData
paper1_positiveContactBranch_of_lowerPinnedRawRemainingContactData
paper1_positiveStrictBarrierBranch_of_lowerPinnedRawRemainingContactData
Paper1MainStatementLowerPinnedRawRemainingContactData
Paper1CombinedLowerPinnedRawRemainingContactStatementData
```

and `PositiveRawRouteAAssembly.lean` already has the Route-A source package:

```lean
Paper1PositiveLowerRawCapRouteARemainingParamData
```

but it currently jumps from that source package to the smooth-contact package via

```lean
paper1_routeASmoothParamData_of_routeARemainingParamData
paper1_positiveRawSmoothContactData_of_routeARemainingParamData
```

Add the direct remaining-contact production.  This is a pure wrapper, copied from the existing `paper1_positiveRawSmoothContactData_of_routeAParamData` proof shape, but stopping before the smooth-contact conversion.

### Patch location

Put the following in:

```text
ShenWork/Paper1/PositiveRawRouteAAssembly.lean
```

after

```lean
paper1_routeARemainingParamData_of_routeAHmkConstParamData
```

and before

```lean
paper1_routeASmoothParamData_of_routeARemainingParamData
```

No imports are needed beyond the file's existing imports:

```lean
import ShenWork.Paper1.UpperBarrierContact
import ShenWork.Paper1.WaveLemma42ParamCore
```

### Patch code

```lean
/-- Route-A remaining-contact param data produces the raw lower-pinned
remaining-contact package directly.  This preserves the thinner residual label
before the existing smooth-contact conversion is applied. -/
theorem paper1_positiveRawRemainingContactData_of_routeARemainingParamData
    (hData : Paper1PositiveLowerRawCapRouteARemainingParamData) :
    Paper1PositiveLowerPinnedRawRemainingContactBranchData := by
  refine ⟨?_⟩
  intro p hα hχ_nonneg hχ_small c hc
  let hcond :
      PositivePaperLemma42ExactConditions p c (kappa c)
        (positiveBranchTailCap p c) (MChi p) :=
    positivePaperLemma42ExactConditions_of_branchCap
      p hα hχ_nonneg hχ_small hc
  rcases hData.produce p hα hχ_nonneg hχ_small c hc with
    ⟨lam, D, Λ, hpar, hD_ge_one, hD_gt, hΛ0, hΛM, hconv, hsmp,
      hreg, hres⟩
  obtain ⟨U, hpin, hprofile⟩ :=
    b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
      p c lam (MChi p) (kappa c) (positiveBranchTailCap p c) D Λ
      hcond hD_gt hD_ge_one hΛ0 hΛM hpar hconv hsmp
  exact
    ⟨positiveBranchTailCap p c, D, U,
      le_trans zero_le_one hD_ge_one,
      le_rfl,
      hprofile,
      hpin,
      hres U hpin hprofile,
      hreg⟩

/-- hmk-aware constant-branch Route-A data also produces the raw remaining-contact
package directly. -/
theorem paper1_positiveRawRemainingContactData_of_routeAHmkConstParamData
    (hData : Paper1PositiveLowerRawCapRouteAHmkConstParamData) :
    Paper1PositiveLowerPinnedRawRemainingContactBranchData :=
  paper1_positiveRawRemainingContactData_of_routeARemainingParamData
    (paper1_routeARemainingParamData_of_routeAHmkConstParamData hData)
```

Optional downstream aliases, if you want the names to appear at the same level as the existing smooth/contact aliases:

```lean
/-- Main Paper1 statement targets from Route-A remaining-contact cap data. -/
theorem paper1_mainStatementTargets_of_routeARemainingParamData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hneg : ConstructionNegSMPProvider)
    (hpos : Paper1PositiveLowerRawCapRouteARemainingParamData)
    (hmainline : Paper1MainlineExistence cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_lowerPinnedRawRemainingContactData
    { constructionNeg := hneg
      positiveLowerPinnedRawRemainingContact :=
        paper1_positiveRawRemainingContactData_of_routeARemainingParamData hpos
      mainline := hmainline }

/-- Combined Paper1 statement targets from Route-A remaining-contact cap data. -/
theorem paper1_combinedStatementTargets_of_routeARemainingParamData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hneg : ConstructionNegSMPProvider)
    (hpos : Paper1PositiveLowerRawCapRouteARemainingParamData)
    (hmainline : Paper1MainlineExistence cStarStarFn)
    (hprops : Paper1PropositionFrontierData)
    (h51 : Paper1Lemma51FrontierData)
    (h52 : Paper1Lemma52FrontierData) :
    Paper1CombinedStatementTargets :=
  paper1_combinedStatementTargets_of_lowerPinnedRawRemainingContactData
    { main :=
        { constructionNeg := hneg
          positiveLowerPinnedRawRemainingContact :=
            paper1_positiveRawRemainingContactData_of_routeARemainingParamData hpos
          mainline := hmainline }
      propositions := hprops
      lemma51 := h51
      lemma52 := h52 }
```

The first two theorems are the recommended minimal patch.  The optional aliases are grep-visible convenience wrappers; they do not reduce additional analytic content.

## Why this Paper1 patch is the best next buildable reduction

It is small, local, and uses only existing proved data:

```lean
positivePaperLemma42ExactConditions_of_branchCap
b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
Paper1PositiveLowerRawCapRouteARemainingParamData.produce
Paper1PositiveLowerPinnedRawRemainingContactBranchData
paper1_routeARemainingParamData_of_routeAHmkConstParamData
```

It does not touch Paper2, Paper3, or any Moser analytic theorem.  It introduces no new assumption; it only exposes an already available route at the sharper residual label.

## Genuine frontiers after this cleanup

After this Paper1 cleanup, the remaining work is analytic rather than wrapper-level:

### Paper1

```lean
ConstructionNegSMPProvider
Paper1MainlineExistence
Paper1PropositionFrontierData
Paper1Lemma51FrontierData
Paper1Lemma52FrontierData
Paper1PositiveLowerRawCapRouteARemainingParamData.produce
Paper1PositiveLowerRawCapRouteAHmkConstParamData.produce
```

plus the actual Route-A/Schauder/stationarity/flat/SMP inputs hidden inside those producer packages.

### Paper2

```lean
rawMoserDrop
relativeMassGradient
terminalEndpoint
IntervalDomainPaper2BootstrapEstimateThinFrontierData
IntervalDomainPaper2Proposition11ChiZeroFrontierData.finiteHorizonAlternative
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
IntervalDomainPaper2GlobalExtensionFrontier
slowBootstrap
criticalBootstrap
criticalEventualSupBound
strongBootstrap
strongEventualSupBound
```

The integrated-first-crossing Moser route is the next serious Paper2 reduction, but only after new integrated consumers replace the pointwise/nonnegative-`B` consumer chain.

### Paper3

The actual-linear-small terminal route is already using the raw-drop/CEGrad/terminal-pointwise pattern:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals
IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts
IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData
```

The remaining Paper3 frontiers are still genuine:

```lean
NegativeSensitivityGlobalEventualBound intervalDomain p
IntervalDomainPaper3NegativeSensitivityFrontierData.globalSolution
IntervalDomainPaper3NegativeSensitivityFrontierData.eventualSupBound
IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
IntervalDomainStandardContinuationGluingData p
P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData
IntervalDomainPaper3ConcreteCompactnessRegularizationData
IntervalDomainPaper3Stability23To25FrontierData
```

Paper2 main targets can continue to discharge the Paper3 Proposition 1.3/1.4 side through

```lean
IntervalDomainPaper3Proposition1FromPaper2MainTargetsData
```

but they still do not discharge the independent negative-sensitivity Proposition 1.2 residual.
