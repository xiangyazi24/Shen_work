# Q2925 (shen1) — RAW first-crossing through anchored initial slice

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Scope: concrete Lean implementation advice; no project source edits.

## Status caveat

The connector-visible repository state does not expose the newest local additions named in the prompt, so I cannot mechanically check their exact binder order. I am treating the following local declarations as already proved and available:

```lean
EqOnPositiveTimesBefore
LpPowerBoundedBefore_congr_pos
AbstractLpBootstrapHypothesis_congr_pos
IntegratedMoserFirstCrossingStep_congr_pos
intervalDomainWithInitialSlice
intervalDomainWithInitialSlice_eq_raw_of_pos
intervalDomainWithInitialSlice_eq_raw_of_pos_apply
intervalDomain_integratedMoserRegularityAnchored_of_rawGradient
intervalDomain_abstractLpBootstrapHypothesis_anchored_of_raw
intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
```

The visible existing stack confirms the important consumer shape: `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData` already packages `regularity`, `energyNonneg`, `dissipation`, `relative`, `rho_pos`, `p0_nonneg`, `lowerAverage`, and `upperDataGap`, and `integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData` consumes that package directly. That is the cleanest route for an anchored representative.

## Recommendation

Add exactly one thin wrapper in `ShenWork/PDE/P3MoserRegularityProducer.lean`, just before the `AxiomAudit` section. It should not try to prove any raw closed-time regularity, raw FTC, or raw dissipation. It should:

1. set `uA := intervalDomainWithInitialSlice u0 u`;
2. use the anchored regularity already produced by `intervalDomain_integratedMoserRegularityAnchored_of_rawGradient` at the call site;
3. build anchored nonnegativity from an anchored classical solution;
4. consume the anchored dissipation / relative / lower-average / upper-data-gap frontiers;
5. run `integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData` on `uA`;
6. transport the result back to raw `u` using `intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored`.

The key point about the classical solution is: **do not pass `hglobal.classical hT` directly to an anchored producer**, because that has type for raw `u`. First form the anchored global solution with `intervalDomain_globalClassical_withInitialSlice`, then call `.classical hT` on that. In the current visible API, the accessor syntax is `hglobal.classical hT`, not `hglobal.classical T hT`.

## Code to add

```lean
-- No new import should be needed when this is inserted into
-- ShenWork/PDE/P3MoserRegularityProducer.lean, because that file already imports
-- P3MoserIntegratedClosure, P3MoserEnergyContinuity, and
-- P3MoserThresholdPlanProducer.
--
-- For a standalone scratch checker, use:
-- import ShenWork.PDE.P3MoserRegularityProducer

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- Produce the raw first-crossing step by running the preferred lower-average /
upper-data-gap route on the anchored initial-slice representative
`intervalDomainWithInitialSlice u0 u`, then transporting the result back to the
raw positive-time solution `u`.

This wrapper is intentionally thin.  It does not assert raw closed-time
regularity, raw FTC, or raw dissipation.  All PDE-content inputs after
`hregA` are anchored-frontier inputs for the representative `uA`. -/
theorem intervalDomain_firstCrossingStep_raw_of_anchoredRegularity_and_upperDataGapFrontiers
    {params : CM2Params} {T rho p0 : ℝ}
    {u0 : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hregA :
      IntegratedMoserFirstCrossingRegularity
        intervalDomain (intervalDomainWithInitialSlice u0 u) T p0)
    (hdissA :
      IntegratedMoserDissipationDropBefore
        intervalDomain (intervalDomainWithInitialSlice u0 u) T rho p0)
    (hrelA :
      RelativeMoserInterpolationBefore
        intervalDomain (intervalDomainWithInitialSlice u0 u) T rho p0)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlowerA :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore
          intervalDomain p T (intervalDomainWithInitialSlice u0 u) →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                intervalDomain
                (intervalDomainWithInitialSlice u0 u) T rho p0 p Cnext))
    (hupperDataGapA :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier
              intervalDomain
              (intervalDomainWithInitialSlice u0 u) T rho p0 p)) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  let uA : ℝ → intervalDomain.Point → ℝ :=
    intervalDomainWithInitialSlice u0 u
  have hglobalA :
      IsPaper2GlobalClassicalSolution intervalDomain params uA v := by
    simpa [uA] using
      (intervalDomain_globalClassical_withInitialSlice
        (u0 := u0) (u := u) (v := v) hglobal)
  have hsolA : IsPaper2ClassicalSolution intervalDomain params T uA v :=
    hglobalA.classical hT
  have hdataA :
      IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
        intervalDomain uA T rho p0 := by
    refine
      { regularity := ?_
        energyNonneg := ?_
        dissipation := ?_
        relative := ?_
        rho_pos := hrho
        p0_nonneg := hp0_nonneg
        lowerAverage := ?_
        upperDataGap := ?_ }
    · simpa [uA] using hregA
    · exact
        intervalDomain_integratedMoserEnergyNonnegativity_of_classical
          (T := T) (p0 := p0) hsolA
    · simpa [uA] using hdissA
    · simpa [uA] using hrelA
    · simpa [uA] using hlowerA
    · simpa [uA] using hupperDataGapA
  have hstepA : IntegratedMoserFirstCrossingStep intervalDomain uA T rho p0 :=
    integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData hdataA
  exact
    intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
      (u0 := u0) (u := u) (T := T) (rho := rho) (p0 := p0)
      (by simpa [uA] using hstepA)

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
```

## How to use it with the raw-gradient producer

At the call site, do not make a second theorem that restates every raw trace/datum/gradient input unless you need a prettier final API. Instead, feed the output of the existing anchored-regularity producer into `hregA`:

```lean
have hregA :
    IntegratedMoserFirstCrossingRegularity
      intervalDomain (intervalDomainWithInitialSlice u0 u) T p0 :=
  intervalDomain_integratedMoserRegularityAnchored_of_rawGradient
    -- use the exact local argument order here:
    -- hT hglobal htrace hdatum hrawGradient ...

exact
  intervalDomain_firstCrossingStep_raw_of_anchoredRegularity_and_upperDataGapFrontiers
    (hT := hT)
    (hglobal := hglobal)
    (hregA := hregA)
    (hdissA := hdissA)
    (hrelA := hrelA)
    (hrho := hrho)
    (hp0_nonneg := hp0_nonneg)
    (hlowerA := hlowerA)
    (hupperDataGapA := hupperDataGapA)
```

If your local `intervalDomain_integratedMoserRegularityAnchored_of_rawGradient` returns `IntervalDomainIntegratedMoserRegularityFrontierDataLite` rather than `IntegratedMoserFirstCrossingRegularity`, use the already existing producer instead of assembling `hdataA` manually:

```lean
have hstepA :
    IntegratedMoserFirstCrossingStep
      intervalDomain (intervalDomainWithInitialSlice u0 u) T rho p0 :=
  intervalDomain_firstCrossingStep_of_lite_classical_and_upperDataGapFrontiers
    hregA_lite
    ((intervalDomain_globalClassical_withInitialSlice
      (u0 := u0) (u := u) (v := v) hglobal).classical hT)
    hdissA hrelA hrho hp0_nonneg hlowerA hupperDataGapA

exact
  intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
    (u0 := u0) (u := u) (T := T) (rho := rho) (p0 := p0)
    hstepA
```

## Caveats

- This wrapper is an ergonomics theorem, not new analysis. The honest residuals remain anchored dissipation, anchored relative interpolation, anchored lower average, anchored upper-data gap, plus whatever raw trace/datum/gradient hypotheses your `intervalDomain_integratedMoserRegularityAnchored_of_rawGradient` already requires.
- `intervalDomain_abstractLpBootstrapHypothesis_anchored_of_raw` is not needed by the first-crossing step wrapper itself unless one of the anchored frontier producers upstream asks for the anchored bootstrap package.
- If `intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored` has the anchored step argument first or has an explicit equality/congruence argument in your local file, the final `exact` line is the only line to adjust. The theorem shape above remains the right minimal interface.
