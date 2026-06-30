# Q2392 shen1 — Paper1--Paper3 headline wrapper frontier audit

Repo: `xiangyazi24/Shen_work`

Audited ref: `main` at `ceba98b2dbba1fcf46ca19c658133985893f6c66`

Scope: `UNDERSTANDING.md`, Paper1 statement/contact/Route-A wrappers, Paper2 interval-domain `StatementAssembly`, Paper3 interval-domain statement and actual-linear statement assemblies.

## Verdict

The next smallest honest residual/frontier reduction is **Paper2 Moser-dissipation packaging for the new terminal-endpoint / mass-gradient actual-atom route**.

Concretely, Paper2 now has the preferred `χ₀ = 0` full-statement route

```lean
IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData
intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData
```

This already removes the refuted global `IntervalDomainInterpolation` premise from the full-statement route by using positive solution-slice interpolation for the a-priori package, and it lowers the Prop25 endpoint from a quantitative `pSeq/rootBound` tower to one terminal pointwise power-control estimate.

The remaining actual Prop25 Moser atoms at this level are:

```lean
MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
relativeMassGradient ...
terminalEndpoint ...
```

The smallest further reduction available from proved code is to replace the carried

```lean
MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
```

field by the stronger raw pointwise physical-drop input

```lean
∀ pExp, p0 ≤ pExp → ∀ B, 0 ≤ B → ∀ t, 0 < t → t < T →
  0 ≤
    (1 / pExp) * deriv
      (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
    B * intervalDomain.integral (fun x => (u t x) ^ pExp)
```

and convert it using the existing proved bridge

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.moserDissipationDropBeforeNonnegB_of_raw_drop
```

This is honest and small: it is exactly the Paper3 CETerminal strategy already used in

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.to_CERawGradResiduals
```

but Paper2 has not yet exposed the corresponding raw-drop terminal/mass-gradient actual-atom wrapper. It does **not** prove the raw drop; the raw drop remains a genuine PDE/Moser analytic frontier. It only removes a wrapper-level black box by using a proved conversion already in the repo.

## What not to do

Do **not** route Paper2 or Paper3 headline wrappers through:

```lean
ShenWork.Paper2.IntervalDomainLemma41.IntervalDomainInterpolation
ShenWork.Paper2.IntervalDomainMCL.OldUnitIntervalPowerGNYoungForMoser
```

The current preferred Paper2 full-statement route correctly avoids the first by using

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
```

and the actual-atom Moser route avoids the second. Also do not claim that a generic `LpBootstrapEnergyInequality` implies `MoserDissipationDropBeforeNonnegB`; the diagnostic counterexample

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

is exactly the warning against that move.

## Paper-by-paper audit

### Paper1

The Paper1 statement assembly is already a set of conditional wrappers around explicit construction/frontier records:

```lean
Paper1MainStatementTargets
paper1_mainStatementTargets_of_mainResultsData
paper1_mainStatementTargets_of_lowerPinnedRawSmoothContactData
paper1_mainStatementTargets_of_lowerPinnedRawRemainingContactData
paper1_combinedStatementTargets_of_lowerPinnedRawSmoothContactData
paper1_combinedStatementTargets_of_lowerPinnedRawRemainingContactData
```

`UpperBarrierContact.lean` has already reduced the upper-barrier contact interface from full contact to smooth-branch or remaining-contact residuals:

```lean
Paper1PositiveLowerPinnedRawSmoothContactBranchData
Paper1PositiveLowerPinnedRawRemainingContactBranchData
paper1_positiveLowerPinnedRawSmoothContactData_of_remainingContactData
paper1_positiveLowerPinnedRawContactData_of_smoothContactData
```

`PositiveRawRouteAAssembly.lean` then exposes Route-A cap packages:

```lean
Paper1PositiveLowerRawCapRouteARemainingParamData
Paper1PositiveLowerRawCapRouteAHmkConstParamData
paper1_routeARemainingParamData_of_routeAHmkConstParamData
paper1_routeASmoothParamData_of_routeARemainingParamData
paper1_positiveRawSmoothContactData_of_routeARemainingParamData
paper1_positiveContactBranch_of_routeARemainingParamData
paper1_positiveStrictBarrierBranch_of_routeARemainingParamData
```

A tiny Paper1 wrapper could preserve the semantic label `RawRemainingContact` one step longer by producing

```lean
Paper1PositiveLowerPinnedRawRemainingContactBranchData
```

directly from

```lean
Paper1PositiveLowerRawCapRouteARemainingParamData
```

before routing onward to the existing main/combined statement wrappers. This is buildable pure packaging, but it is less strategically central than the Paper2 raw-drop patch: it does not reduce a headline Paper1 analytic frontier beyond the contact residual already exposed. The genuine Paper1 frontiers remain the construction floors: negative construction/SMP, positive Route-A/Schauder/stationarity/flat/SMP inputs, remaining contact outside the already-handled `hmκ` subroute, `Paper1MainlineExistence`, proposition frontiers, and Lemma 5.1/5.2 frontiers.

### Paper2

The newest preferred full-statement route is now the right headline route:

```lean
IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData
intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData
```

It combines three real reductions:

1. `Corollary_2_1` and `Proposition_2_5` are both supplied by the common-free actual-atom path.
2. Relative Moser interpolation is lowered to the mass-gradient/lower-order interface by
   ```lean
   ShenWork.IntervalDomainExistence.P3MoserLemmas.intervalDomain_relativeMoserInterpolationBefore_of_massGradient
   ```
3. The endpoint tower is lowered to one terminal pointwise estimate by constant sequences in
   ```lean
   IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData.toMassGradient
   ```

What remains reducible by existing code is the dissipation-side wrapper: use the already-proved raw-drop-to-nonnegative-`B` conversion. This gives a thinner honest actual-atom package without using axioms, `sorry`, global interval interpolation, or old GN.

The remaining Paper2 analytic frontiers after that wrapper are still real:

```lean
-- still analytic after the proposed wrapper
raw pointwise physical Moser drop
relativeMassGradient subfields
terminal pointwise power-control endpoint
Positive solution-slice interpolation for the a-priori package
IntervalDomainPaper2Proposition11ChiZeroFrontierData.finiteHorizonAlternative
IntervalDomainPaper2BootstrapEstimateThinFrontierData
IntervalDomainPaper2GlobalExtensionFrontier
slow/critical/strong bootstrap and eventual-sup frontiers
```

For non-`χ₀ = 0` routes, the local/uniform existence and Picard/restart frontiers remain genuine analytic work.

### Paper3

Paper3 already has the corresponding terminal/raw/mass-gradient Moser-ladder reduction in the actual-linear small-sensitivity route:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals
IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts
IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalP2MainData
```

The P2-main route correctly reduces the Proposition 1.3/1.4 side to

```lean
IntervalDomainPaper3Proposition1FromPaper2MainTargetsData
```

but keeps the independent Proposition 1.2 residual

```lean
NegativeSensitivityGlobalEventualBound intervalDomain p
```

as `negativeBound`. That is not discharged by Paper2 main targets.

There is no further small cross-paper plug-in from the new Paper2 `χ₀ = 0` terminal route into this Paper3 actual-linear-small headline: Paper3 actual-linear-small assumes

```lean
0 < p.χ₀
```

while the new Paper2 preferred route assumes

```lean
p.χ₀ = 0
```

So a wrapper consuming `IntervalDomainPaper2PreferredChiZero...` inside the actual-linear-small Paper3 route would be vacuous or wrongly parameterized. The Paper3 remaining inputs are genuine: negative-sensitivity eventual bound, sectorial spectral orbit bound, continuation/gluing, terminal Moser atoms, closed-energy trace, compactness/regularization, and Theorem 2.3--2.5 stability packages.

## Recommended buildable patch: Paper2 raw-drop terminal actual atoms

Place this in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` after the existing terminal-endpoint mass-gradient actual-atom package. The file already imports the needed declarations through

```lean
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserLemmas
```

and `P3MoserActualWiring` imports the dissipation-shape bridge. An isolated check file can use:

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper2

noncomputable section

/-- Actual-atom Proposition 2.5 frontier with relative Moser lowered to
mass-gradient data, the endpoint lowered to terminal pointwise power control, and
nonnegative-`B` dissipation supplied by the raw pointwise physical drop.

The raw drop is still an analytic residual.  This structure only exposes the
proved wrapper
`moserDissipationDropBeforeNonnegB_of_raw_drop` at the Paper2 actual-atom
boundary. -/
structure
    IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
    (p : CM2Params) : Prop where
  rawMoserDrop :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ∀ pExp, p0 ≤ pExp → ∀ B, 0 ≤ B →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / pExp) *
              deriv (fun τ =>
                intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ pExp)
  relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∃ cGrad : ℝ → ℝ,
          (∀ q, p0 ≤ q → 0 < cGrad q) ∧
          (∀ q, p0 ≤ q → ∀ eta > 0, ∃ Ceta,
            LpMassGradientInterpolationEstimate intervalDomain
              (q + rho) eta Ceta T u) ∧
          (∀ q, p0 ≤ q → ∀ t, 0 < t → t < T →
            intervalDomain.integral (fun x =>
                (u t x) ^ (q + rho - 2) *
                  (intervalDomain.gradNorm (u t) x) ^ 2) ≤
              cGrad q * intervalDomain.integral (fun x =>
                (intervalDomain.gradNorm
                  (fun y => (u t y) ^ (q / 2)) x) ^ 2)) ∧
          MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0
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

/-- Convert the raw-drop terminal/mass-gradient package to the existing terminal
actual-atom package. -/
def
    IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.toTerminalEndpoint
    {p : CM2Params}
    (h :
      IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
        p) :
    IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData
      p where
  moserDissipation := by
    intro T rho p0 u v hsol hcross hboot
    exact
      ShenWork.IntervalDomainExistence.P3MoserDissipationShape.moserDissipationDropBeforeNonnegB_of_raw_drop
        (h.rawMoserDrop hsol hcross hboot)
  relativeMassGradient := h.relativeMassGradient
  terminalEndpoint := h.terminalEndpoint

/-- Raw-drop/mass-gradient/terminal-endpoint actual atoms produce interval-domain
Proposition 2.5. -/
theorem
    intervalDomainPaper2_Proposition_2_5_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData
    (p : CM2Params)
    (hData :
      IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
        p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientTerminalEndpointFrontierData
    p hData.toTerminalEndpoint

/-- Raw-drop/mass-gradient/terminal-endpoint actual atoms produce interval-domain
Corollary 2.1. -/
theorem
    intervalDomainPaper2_Corollary_2_1_of_actualAtomRawDropMassGradientTerminalEndpointFrontierData
    (p : CM2Params)
    (hData :
      IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
        p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientTerminalEndpointFrontierData
    p hData.toTerminalEndpoint

/-- Section-2 targets from thin frontiers and raw-drop/mass-gradient/terminal
actual atoms. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomRawDropMassGradientTerminalEndpointFrontierData
    (p : CM2Params)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hAtoms :
      IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
        p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomMassGradientTerminalEndpointFrontierData
    p hThin hAtoms.toTerminalEndpoint

end

end ShenWork.Paper2
```

### Optional headline aliases after the core patch

If a grep-visible full-statement route is desired, mirror only the existing terminal-endpoint structures and replace the atom carrier by the new raw-drop package. The exact existing structures to mirror are:

```lean
IntervalDomainPaper2MainTheoremChiZeroActualAtomMassGradientTerminalEndpointCor21LocalFreeFrontierData
IntervalDomainPaper2LocalAndMainChiZeroActualAtomMassGradientTerminalEndpointCor21FrontierData
IntervalDomainPaper2StatementChiZeroActualAtomMassGradientTerminalEndpointCor21Section2ThinSolutionInterpolationFrontierData
IntervalDomainPaper2PreferredChiZeroStatementActualAtomMassGradientTerminalEndpointCor21SolutionInterpolationFrontierData
```

The conversion target should always be the already-existing terminal package via

```lean
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData.toTerminalEndpoint
```

so downstream wrappers remain unchanged. This avoids import cycles because all code can live in `IntervalDomainStatementAssembly.lean`; no new file has to import Paper3.

## Secondary optional Paper1 packaging patch

This is smaller syntactically but lower priority. It preserves the `RawRemainingContact` label from Route-A data before routing to the existing smooth/contact wrappers.

Place in `ShenWork/Paper1/PositiveRawRouteAAssembly.lean` after `Paper1PositiveLowerRawCapRouteARemainingParamData` and before or near the existing smooth-data conversion:

```lean
import ShenWork.Paper1.PositiveRawRouteAAssembly

namespace ShenWork.Paper1

noncomputable section

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

end

end ShenWork.Paper1
```

This Paper1 patch is honest but not the main recommendation: it is a semantic-wrapper cleanup. The real Paper1 construction inputs are still analytic.

## Genuine remaining frontiers after the recommended patch

After adding the Paper2 raw-drop wrapper, no other small cross-paper headline reduction is apparent from existing proved code.

Remaining analytic frontiers are:

- **Paper1:** construction negative/SMP package, positive Route-A/Schauder/stationarity/flat/SMP producers, remaining upper-contact residuals outside already-proved subroutes, `Paper1MainlineExistence`, proposition frontiers, Lemma 5.1/5.2 frontiers.
- **Paper2:** raw pointwise Moser drop, mass-gradient interpolation/lower-order data, terminal pointwise endpoint, finite-horizon alternative, positive solution-slice interpolation for the a-priori target, global extension, section-2 thin estimates, and the bootstrap/eventual-sup packages for Theorems 1.2/1.3.
- **Paper3:** `NegativeSensitivityGlobalEventualBound`, or its decomposed global-solution/eventual-sup producers; sectorial spectral orbit bound; continuation/gluing; closed-energy trace and terminal Moser atoms; compactness/regularization; and Theorem 2.3--2.5 stability packages.

The key point is that all of these are now explicit residual packages, not hidden proof holes. The next wrapper reduction should be Paper2 raw-drop packaging; the next mathematical work is proving one of those analytic residuals.
