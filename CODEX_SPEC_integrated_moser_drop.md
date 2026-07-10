# Task: Replace unsatisfiable rawMoserDrop with IntegratedMoserDissipationDropBefore

## Context

The leaf-level residual `IntervalDomainMassLpSmoothingMoserActualLinearSmallCERawGradResiduals`
(in `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean:1318`) carries a
`rawMoserDrop` field that is **provably unsatisfiable**. A formal counterexample exists at
`ShenWork/PDE/P3MoserDissipationShape.lean:188`.

The codebase already has a correct replacement route via `IntegratedMoserDissipationDropBefore`
→ `IntegratedMoserFirstCrossingStep` → `IntervalDomainMassLpSmoothingIntegratedStepResiduals`
→ `Corollary_2_1` + `Proposition_2_5` + `to_routeResiduals`.

## Goal

Create a new file `ShenWork/Paper3/IntervalDomainIntegratedMoserAssembly.lean` that:

1. Defines a new leaf-level structure replacing `rawMoserDrop` with `IntegratedMoserDissipationDropBefore`
2. Wires it through the EXISTING integrated step route to produce
   `IntervalDomainMassLpSmoothingIntegratedStepResiduals`

## The new structure

```lean
structure IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals
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
  integratedMoserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
  relativeMassGradient :
    -- SAME as CERawGradResiduals.relativeMassGradient (copy verbatim from line 1343-1360)
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∃ cGrad : ℝ → ℝ,
          (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
          (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
            LpMassGradientInterpolationEstimate intervalDomain
              (pExp + rho) eta Ceta T u) ∧
          (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
            intervalDomain.integral (fun x =>
              (u t x) ^ (pExp + rho - 2) *
                (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad pExp * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
          MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0
  quantitativeEndpoint :
    -- SAME as CERawGradResiduals.quantitativeEndpoint (copy verbatim from line 1361-1374)
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
```

## The wiring theorem

```lean
def IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals.to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
      (Classical.choice (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  integratedStep := by
    -- Wire: integratedMoserDissipation → IntegratedMoserFirstCrossingStep
    -- via intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
    intro T rho p0 u v hsol hcross hboot
    -- 1. Get regularity from classical solution
    have hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
      intervalDomain_integratedMoserFirstCrossingRegularity_of_classical hsol
    -- 2. Get nonnegativity from classical solution
    have hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
      intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol
    -- 3. Get integrated dissipation from the residual
    have hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
      h.integratedMoserDissipation hsol hcross hboot
    -- 4. Get relative interpolation from massGradient
    have hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0 := by
      rcases h.relativeMassGradient hsol hcross hboot with ⟨cGrad, hcGrad, hMG, hgrad, hmassToLp⟩
      exact P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient
        cGrad hcGrad hMG hgrad hmassToLp
    -- 5. Assemble
    have hrho : 0 < rho := hboot.rho_pos
    have hp0_nonneg : 0 ≤ p0 := le_of_lt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
      (le_of_lt (AbstractLpBootstrapHypothesis.p0_gt_threshold hboot)))
    exact intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
      hreg hnonneg hdiss hrel hrho hp0_nonneg
  quantitativeEndpoint := h.quantitativeEndpoint
```

## What to look up FIRST

Before writing code, read:
1. `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean:257-330` — the EXISTING `IntegratedStepResiduals` structure
2. `ShenWork/PDE/P3MoserThresholdPlanProducer.lean:178-191` — `intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data`
3. `ShenWork/PDE/P3MoserRegularityProducer.lean:443-475` — regularity producer from classical solution
4. `ShenWork/PDE/P3MoserIntegratedClosure.lean:1614-1621` — energy nonnegativity from classical solution
5. `ShenWork/PDE/P3MoserLemmaDischarge.lean:115-129` — `relativeMoserInterpolationBefore_of_massGradient`
6. `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean:1318-1394` — OLD `CERawGradResiduals`
7. `ShenWork/PDE/P3MoserDissipationShape.lean:67-78` — `IntegratedMoserDissipationDropBefore` definition

Find the exact theorem names by grepping. Some names I wrote above may have slight errors.
In particular, find:
- The theorem that produces `IntegratedMoserFirstCrossingRegularity` from `IsPaper2ClassicalSolution`
- How `AbstractLpBootstrapHypothesis.rho_pos` or equivalent gives `0 < rho`
- How to extract `0 ≤ p0` from the bootstrap hypothesis

## Import strategy

The file will need to import:
```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
import ShenWork.PDE.IntervalDomainMoserLadderAtoms
import ShenWork.PDE.P3MoserThresholdPlanProducer
import ShenWork.PDE.P3MoserRegularityProducer
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.PDE.P3MoserLemmaDischarge
import ShenWork.PDE.P3MoserDissipationShape
```

Some of these may be transitively imported. Start with a minimal set and add as needed.

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/Paper3/IntervalDomainIntegratedMoserAssembly.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- File ≤ 300 lines
- The structure and wiring theorem above are PSEUDOCODE — adapt to what actually compiles
- If `intervalDomain_integratedMoserFirstCrossingRegularity_of_classical` doesn't exist by that name, grep for the actual name
- If stuck, deliver what compiles + precise stall report
- Work only in /Users/huangx/repos/Shen_work/
