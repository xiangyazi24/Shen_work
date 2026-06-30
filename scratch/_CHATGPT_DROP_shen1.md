# Q2372 shen1 — Paper2 remaining Prop25 actual atoms audit

Repo: `xiangyazi24/Shen_work`

Audited target: `main` at commit `cbeb0de224bdfd72cdf70e63f0baae3fd5e23067` (`Add Paper2 mass-gradient actual atom headline route`).

Scope: re-audit the remaining actual Prop25 atoms after the committed mass-gradient reduction of the `relativeMoserInterpolation` field in `IntervalDomainPaper2Prop25ActualAtomFrontierData`.

## Current state after `cbeb0de2`

The new mass-gradient route is real wiring.  In `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`, the structure

```lean
IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData
```

keeps only these hard Prop25 actual atoms:

```lean
moserDissipation :
  ... → MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0

quantitativeEndpoint :
  ... → ∃ pSeq rootBound : ℕ → ℝ,
    (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
      IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

and lowers the relative-Moser field to mass-gradient data through

```lean
ShenWork.IntervalDomainExistence.P3MoserLemmas.intervalDomain_relativeMoserInterpolationBefore_of_massGradient
```

in

```lean
IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms
```

So the audit boundary is now correctly: physical-`B` dissipation and terminal endpoint/root-tower control.

## 1. Existing theorem chain?

There is **no existing theorem chain in the current repo that honestly derives either remaining atom from lower-level PDE facts**.

### A. `MoserDissipationDropBeforeNonnegB`

Relevant existing names:

```lean
-- file: ShenWork/PDE/P3MoserDissipationShape.lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.MoserDissipationDropBeforeNonnegB
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.moserDissipationDropBeforeNonnegB_of_raw_drop
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.IntegratedMoserDissipationDropBefore
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.integratedMoserDissipationDropBefore_of_integrated_energy
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

The only producer of `MoserDissipationDropBeforeNonnegB` is

```lean
moserDissipationDropBeforeNonnegB_of_raw_drop
```

but its input is the stronger pointwise raw drop:

```lean
∀ p, p0 ≤ p → ∀ B, 0 ≤ B → ∀ t, 0 < t → t < T →
  0 ≤ (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
    B * D.integral (fun x => (u t x) ^ p)
```

That is not a lower-level PDE derivation; it is a stronger wrapper around the same pointwise sign content.  The repo also defines the faithful integrated shape

```lean
IntegratedMoserDissipationDropBefore
```

and packages it via

```lean
integratedMoserDissipationDropBefore_of_integrated_energy
```

but that integrated shape is not consumed by the current Moser closure.  The current consumers still require pointwise `MoserDissipationDropBeforeNonnegB`:

```lean
-- file: ShenWork/PDE/P3MoserDissipationShape.lean
moser_step_of_energy_nonnegB_relative_interpolation
moser_iteration_chain_of_energy_nonnegB_relative_interpolation
all_exponents_of_energy_nonnegB_relative_interpolation_lpmono
intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation
intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation_inside
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB
intervalDomain_endpointBoundFromLp_of_quantitative_root_tower_nonnegB

-- file: ShenWork/PDE/P3MoserActualWiring.lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

The counterexample

```lean
unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

is exactly the warning not to derive the pointwise `NonnegB` atom abstractly from a generic energy inequality.  Therefore the next faithful dissipation reduction cannot be a wrapper from `LpBootstrapEnergyInequality` to `MoserDissipationDropBeforeNonnegB`.  It would need a new integrated-first-crossing Moser consumer.

### B. `quantitativeEndpoint`

Relevant existing names:

```lean
-- file: ShenWork/Paper2/IntervalDomainMoserClosure.lean
ShenWork.Paper2.IntervalDomainMoserClosure.IntervalDomainMoserPointwisePowerControlBefore
ShenWork.Paper2.IntervalDomainMoserClosure.IntervalDomainMoserQuantitativeEndpoint
ShenWork.Paper2.IntervalDomainMoserClosure.intervalDomain_boundedBefore_of_pointwise_power_control
ShenWork.Paper2.IntervalDomainMoserClosure.intervalDomain_boundedBefore_of_moser_quantitative_endpoint
ShenWork.Paper2.IntervalDomainMoserClosure.intervalDomain_boundedBefore_of_moser_iteration_chain_and_quantitative_endpoint

-- file: ShenWork/PDE/IntervalDomainMoserActualAtoms.lean
ShenWork.IntervalDomainExistence.dyadic_root_tower_bound
ShenWork.IntervalDomainExistence.intervalDomain_endpointBoundFromLp_of_quantitative_root_tower

-- file: ShenWork/PDE/P3MoserDissipationShape.lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.intervalDomain_endpointBoundFromLp_of_quantitative_root_tower_nonnegB

-- file: ShenWork/PDE/P3MoserActualWiring.lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

`IntervalDomainMoserQuantitativeEndpoint` is already very close to the final consumer.  It says that for some `M` and some index `n`, one has a positive exponent, a nonnegative root bound below `M`, and terminal pointwise power control:

```lean
∃ M, 0 ≤ M ∧ ∃ n : ℕ,
  0 < pSeq n ∧ 0 ≤ rootBound n ∧ rootBound n ≤ M ∧
    IntervalDomainMoserPointwisePowerControlBefore u T (pSeq n) (rootBound n)
```

The dyadic root-tower lemmas are algebraic only:

```lean
dyadic_inv_sum_Icc_le_one
dyadic_k_inv_sum_Icc_eq
dyadic_k_inv_sum_Icc_le_two
dyadic_root_tower_product_bound
dyadic_root_tower_iterate_bound
dyadic_root_tower_bound
```

They do not construct the terminal pointwise control required by `IntervalDomainMoserQuantitativeEndpoint`.  The current endpoint producers all still take the endpoint as an explicit hypothesis.

So there is no honest current theorem chain from lower PDE/GN facts to the `quantitativeEndpoint` field either.

## 2. Smallest faithful next frontier package

The safest next reduction is **not** dissipation-first.  It is the endpoint packaging reduction:

> Replace the sequence/root-tower-shaped `quantitativeEndpoint` field by a smaller terminal pointwise endpoint frontier, then build the old `quantitativeEndpoint` shape by constant sequences.

This is faithful because `IntervalDomainMoserClosure` ultimately consumes only terminal pointwise power control through

```lean
intervalDomain_boundedBefore_of_moser_quantitative_endpoint
```

The `pSeq/rootBound` pair is bookkeeping for a Moser construction, but the current consumer does not inspect a full sequence.  It only needs one index with pointwise power control.  Therefore a terminal frontier of the form

```lean
∃ q R : ℝ,
  0 < q ∧ 0 ≤ R ∧
    ((∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
      IntervalDomainMoserPointwisePowerControlBefore u T q R)
```

is strictly smaller than the current endpoint atom and is buildable with existing APIs.

### Existing consumers affected

For the endpoint-terminal reduction, **no deep Moser consumer has to change**.  Add one conversion wrapper in `IntervalDomainStatementAssembly.lean`:

```lean
TerminalPointwiseEndpoint → quantitativeEndpoint
```

Then all existing consumers can still run through:

```lean
IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms
intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierData
intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientFrontierData
```

For a dissipation-integrated reduction, by contrast, the existing consumers **would need new theorem variants**.  In particular, the pointwise-drop closure chain in `P3MoserDissipationShape.lean` would need an integrated-first-crossing analogue of at least:

```lean
moser_step_of_energy_nonnegB_relative_interpolation
moser_iteration_chain_of_energy_nonnegB_relative_interpolation
all_exponents_of_energy_nonnegB_relative_interpolation_lpmono
intervalDomain_all_exponents_of_energy_nonnegB_relative_interpolation_inside
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
intervalDomain_allLpBoundFromBootstrap_of_relative_moser_step_nonnegB
```

and `P3MoserActualWiring.lean` would need corresponding actual-atom entry points that consume `IntegratedMoserDissipationDropBefore` instead of `MoserDissipationDropBeforeNonnegB`.  That is real new analysis/closure work, not just a statement-level wrapper.

## 3. No-go routes

Do not use these routes:

```lean
-- false legacy relative-Moser power route
ShenWork.Paper2.IntervalDomainMCL.OldUnitIntervalPowerGNYoungForMoser
ShenWork.Paper2.IntervalDomainGNYObstruction.not_oldUnitIntervalPowerGNYoungForMoser

-- false global interpolation route
ShenWork.Paper2.IntervalDomainLemma41.IntervalDomainInterpolation
ShenWork.Paper2.IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation

-- invalid abstract derivation of pointwise physical-B drop
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

Also do not claim that

```lean
LpBootstrapEnergyInequality D u T rho p0
```

implies either old or nonnegative-`B` Moser dissipation.  The repo also has the older diagnostic

```lean
ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge.LpBootstrapEnergyInequality_does_not_imply_MoserDissipationDropBefore
```

for the old drop shape.

## 4. Buildable Lean patch outline

This outline is buildable with current APIs because it only repackages terminal pointwise control into the existing `IntervalDomainMoserQuantitativeEndpoint` shape.  It does **not** try to derive the terminal pointwise estimate.

Place after `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData` in:

```text
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
```

The file already imports all required modules at `cbeb0de2`; for an isolated check file, use:

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper2

noncomputable section

/-- Actual-atom Proposition 2.5 frontier with relative Moser already lowered to
mass-gradient data and the endpoint lowered from `pSeq/rootBound` bookkeeping to
one terminal pointwise power-control estimate.

The dissipation field remains the honest physical-`B` pointwise drop atom. -/
structure IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData
    (p : CM2Params) : Prop where
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ShenWork.IntervalDomainExistence.P3MoserDissipationShape.MoserDissipationDropBeforeNonnegB
          intervalDomain u T rho p0
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

/-- Convert the terminal endpoint package to the existing mass-gradient actual
atom frontier by using constant `pSeq/rootBound` sequences. -/
def
    IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData.toMassGradient
    {p : CM2Params}
    (h :
      IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData
        p) :
    IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p where
  moserDissipation := h.moserDissipation
  relativeMassGradient := h.relativeMassGradient
  quantitativeEndpoint := by
    intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
    rcases h.terminalEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
      ⟨q, R, hq, hR, hpoint⟩
    refine ⟨fun _ : ℕ => q, fun _ : ℕ => R, ?_⟩
    intro hAllLp
    refine ⟨R, hR, 0, hq, hR, le_rfl, ?_⟩
    exact hpoint hAllLp

/-- Proposition 2.5 from mass-gradient actual atoms and terminal pointwise
endpoint control. -/
theorem
    intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientTerminalEndpointFrontierData
    (p : CM2Params)
    (hData :
      IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData
        p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierData
    p hData.toMassGradient

/-- Corollary 2.1 from mass-gradient actual atoms and terminal pointwise endpoint
control.  The endpoint field is not used for Corollary 2.1 but is retained so the
same package can feed Proposition 2.5 and all headline wrappers. -/
theorem
    intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientTerminalEndpointFrontierData
    (p : CM2Params)
    (hData :
      IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData
        p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientFrontierData
    p hData.toMassGradient

end

end ShenWork.Paper2
```

This is the recommended next patch if the goal is the safest incremental reduction.  It shrinks the endpoint atom without pretending to prove the terminal Moser pointwise estimate.

## Bottom line

After `cbeb0de2`, neither remaining actual Prop25 atom has an honest lower-level derivation chain in the repo.  The next safest reduction is a **terminal endpoint package** that replaces `pSeq/rootBound` construction by a direct terminal pointwise power-control frontier and converts it back to `IntervalDomainMoserQuantitativeEndpoint` with constant sequences.

The dissipation atom should remain as-is until a new integrated-first-crossing Moser closure is proved; do not derive `MoserDissipationDropBeforeNonnegB` abstractly from the energy inequality.
