# Q2212 R2 infrastructure audit

Audited current `main` at commit `5fc60d48`.

## 1. Existing theorem chains

The CETerminal route already reduces several fields by pure packaging:

- `boundednessCore` closes the old boundedness bundle through `IntervalDomainMoserActualLinearSmallBoundednessCore.to_boundednessHyp hb`.
- `closedEnergyTrace` reduces to `IntervalDomainL2SeedRegularityFrontier` through `P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData`, used in `IntervalDomainMassLpSmoothingMoserActualLinearSmallClosedEnergyResiduals.to_actualLinearSmallResiduals`.
- `rawMoserDrop` reduces to `MoserDissipationDropBeforeNonnegB` through `moserDissipationDropBeforeNonnegB_of_raw_drop`, used in `IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals.to_CEGradResiduals`.
- `relativeMassGradient` reduces to `RelativeMoserInterpolationBefore` through `P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient`.
- `terminalPointwise` reduces to the old `quantitativeEndpoint` field inside `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.to_CERawGradResiduals hb` by choosing constant endpoint sequences.

The sectorial orbit field has this downstream chain once supplied: `intervalDomain_spectralSemigroupOrbitBoundRaw_of_sectorialConcrete` → `intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound` → `intervalDomain_Lemma_A_1_of_spectralSemigroupOrbitBound` → `intervalDomain_Theorem_2_2_of_spectralSemigroupOrbitBound_frontiers`.

Continuation is consumed by `intervalDomainGlobalSolutionExists_of_standardContinuation_gluing_and_massLpSmoothing`, then by `intervalDomain_smallDataGlobal_of_globalSolutionExists` and `intervalDomain_massConstrainedSmallDataGlobal_of_globalSolutionExists`. Compactness and stability are routed by `intervalDomain_paper3_concreteCompactnessRegularizationTargets_of_frontiers` and `intervalDomain_paper3_stability23To25Targets_of_frontiers`. On the proposition side, `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData` uses `paper2Main` but still carries `negativeBound` separately.

## 2. Genuine frontiers

I found no existing producer for the nonlinear sectorial orbit bound, standard continuation/gluing, the closed energy trace, pointwise Moser drop, the mass-gradient package, terminal pointwise endpoint control, compactness/regularization subfields, stability subfields, or `negativeBound`. These are reduced and routed, not proved away.

## 3. Smallest faithful next Lean edit

The best next edit is to name the currently inline terminal bridge. Add a helper theorem named `intervalDomainMoserQuantitativeEndpoint_of_terminalPointwisePowerControl` whose assumption is exactly the current `terminalPointwise` field and whose conclusion is exactly the old `quantitativeEndpoint` field. Its proof is already present inline: destruct the witness into `q` and `R`, set `pSeq := fun _ => q`, set `rootBound := fun _ => R`, and return the existing pointwise power-control witness.

Then replace the inline `quantitativeEndpoint := by ...` block in `IntervalDomainMassLpSmoothingMoserActualLinearSmallCETerminalResiduals.to_CERawGradResiduals` with a call to that helper. This is a faithful infrastructure cleanup, not a new PDE proof.

## 4. Negative-bound caveat

Do not derive `negativeBound` from Paper2 Theorem 1.1 or from `paper2Main`. The P2Main data still carries both `negativeBound` and `paper2Main`, and `not_paper2_theorem_1_1_implies_paper3_proposition_1_2` blocks that shortcut unless it is reconciled.
