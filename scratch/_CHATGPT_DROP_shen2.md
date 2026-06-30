# Q2358 shen2: Paper2 Prop25 actual-atom frontier audit

Repo target: `xiangyazi24/Shen_work`, `main` at commit `69e2c9cc` (`Add Paper2 actual-atom Prop25 frontiers`).

## Executive answer

The new frontier

```lean
IntervalDomainPaper2Prop25ActualAtomFrontierData p
```

is already a real net-reduction compared with carrying

```lean
Proposition_2_5 intervalDomain p
```

or old

```lean
Paper2BootstrapEstimateBranchData intervalDomain p
```

because the wrapper

```lean
intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
```

routes through:

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring
  .intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

and that theorem internally produces:

```lean
CrossDiffusionBootstrapEstimate intervalDomain p T (2 * p.γ) u v
AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T (2 * p.γ) pExp
LpBootstrapEnergyInequality intervalDomain u T (2 * p.γ) pExp
Lp monotonicity from positivity + regularity
```

The three remaining actual atoms have different statuses:

| Field | Can reduce right now? | Best current replacement |
|---|---:|---|
| `moserDissipation` | only to a stronger raw pointwise drop; no honest PDE producer yet | usually keep it; optionally replace by a raw-drop frontier using `moserDissipationDropBeforeNonnegB_of_raw_drop` |
| `relativeMoserInterpolation` | yes | replace by mass-gradient + gradient-chain + lower-order mass-to-Lp frontiers using `intervalDomain_relativeMoserInterpolationBefore_of_massGradient` |
| `quantitativeEndpoint` | no real producer yet | keep as is; dyadic root-tower lemmas only prove algebraic subpieces |

## Current actual-atom frontier in `IntervalDomainStatementAssembly.lean`

File:

```text
ShenWork/Paper2/IntervalDomainStatementAssembly.lean
```

Current structure:

```lean
structure IntervalDomainPaper2Prop25ActualAtomFrontierData
    (p : CM2Params) : Prop where
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ShenWork.IntervalDomainExistence.P3MoserDissipationShape.MoserDissipationDropBeforeNonnegB
          intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

Current producer:

```lean
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    hData.moserDissipation
    hData.relativeMoserInterpolation
    hData.quantitativeEndpoint
```

This wrapper is good.  The next reduction should target the fields, not the wrapper.

## Atom 1: `moserDissipation`

### Existing APIs

File:

```text
ShenWork/PDE/P3MoserDissipationShape.lean
```

Current field target:

```lean
def MoserDissipationDropBeforeNonnegB
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∀ A B K L_const, 0 ≤ B →
    (∀ t, 0 < t → t < T →
      (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
        A * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
        B * D.integral (fun x => (u t x) ^ p) ≤
      K * D.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
    ∀ t, 0 < t → t < T →
      0 ≤
        (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
          B * D.integral (fun x => (u t x) ^ p)
```

Existing packaging theorem:

```lean
theorem moserDissipationDropBeforeNonnegB_of_raw_drop
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (hdrop :
      ∀ p, p0 ≤ p → ∀ B, 0 ≤ B → ∀ t, 0 < t → t < T →
        0 ≤
          (1 / p) * deriv (fun τ => D.integral (fun x => (u τ x) ^ p)) t +
            B * D.integral (fun x => (u t x) ^ p)) :
    MoserDissipationDropBeforeNonnegB D u T rho p0
```

There is also an integrated shape:

```lean
def IntegratedMoserDissipationDropBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T _rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      D.integral (fun x => (u t2 x) ^ p) -
          D.integral (fun x => (u t1 x) ^ p) +
        2 * ∫ s in t1..t2,
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      C * p * ∫ s in t1..t2,
        max 1 (D.integral (fun x => (u s x) ^ p))
```

and its packaging theorem:

```lean
theorem integratedMoserDissipationDropBefore_of_integrated_energy
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (henergy :
      ∀ p, p0 ≤ p → ∃ C, 0 ≤ C ∧
        ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
          D.integral (fun x => (u t2 x) ^ p) -
              D.integral (fun x => (u t1 x) ^ p) +
            2 * ∫ s in t1..t2,
              D.integral (fun x =>
                (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
          C * p * ∫ s in t1..t2,
            max 1 (D.integral (fun x => (u s x) ^ p))) :
    IntegratedMoserDissipationDropBefore D u T rho p0
```

### Audit verdict

There is **no existing honest theorem** that derives

```lean
MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
```

from PDE regularity, from the integrated dissipation shape, or from lower-level energy frontiers.

The raw-drop theorem is a packaging theorem only.  It is a reduction in syntax, but not a PDE proof.  More importantly, the file itself contains a no-go warning:

```lean
theorem unitLinearDrop_not_MoserDissipationDropBeforeNonnegB :
    ¬ MoserDissipationDropBeforeNonnegB
      unitLinearDropDomain unitLinearDropU 1 1 1
```

So do **not** try to derive this field abstractly.  The integrated shape is probably the mathematically faithful future direction, but current Prop25 Moser closure consumes the pointwise `NonnegB` predicate, not `IntegratedMoserDissipationDropBefore`.

### Optional smaller input structure

Only add this if you have a genuine raw pointwise drop proof.  It is stronger than the current field but packages through an existing theorem:

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly
import ShenWork.PDE.P3MoserDissipationShape

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape

noncomputable section

namespace ShenWork.Paper2

structure IntervalDomainPaper2Prop25RawDropDissipationFrontierData
    (p : CM2Params) : Prop where
  rawDrop :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ B, 0 ≤ B → ∀ t, 0 < t → t < T →
          0 ≤
            (1 / q) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ q)) t +
              B * intervalDomain.integral (fun x => (u t x) ^ q)

end ShenWork.Paper2
```

Use it via:

```lean
moserDissipation := by
  intro T rho p0 u v hsol hcross hboot
  exact moserDissipationDropBeforeNonnegB_of_raw_drop
    (hRaw.rawDrop hsol hcross hboot)
```

Recommended status: **do not replace the current field globally** unless the team commits to this raw pointwise proof shape.  It is not an established lower-level PDE producer.

## Atom 2: `relativeMoserInterpolation`

### Existing reduction

This field has a genuine existing lower-level route.

File:

```text
ShenWork/PDE/P3MoserLemmas.lean
```

General theorem:

```lean
theorem relativeMoserInterpolationBefore_of_massGradient
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate D (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      D.integral (fun x =>
          (u t x) ^ (p + rho - 2) * (D.gradNorm (u t) x) ^ 2) ≤
        cGrad p * D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp : MoserMassPowerToCurrentLpLowerOrder D u T rho p0) :
    RelativeMoserInterpolationBefore D u T rho p0
```

Interval specialization:

```lean
theorem intervalDomain_relativeMoserInterpolationBefore_of_massGradient
    {u : ℝ → intervalDomain.Point → ℝ} {T rho p0 : ℝ}
    (cGrad : ℝ → ℝ)
    (hcGrad : ∀ p, p0 ≤ p → 0 < cGrad p)
    (hMG : ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain (p + rho) eta Ceta T u)
    (hgrad : ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (p + rho - 2) *
            (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad p * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmassToLp :
      MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0) :
    RelativeMoserInterpolationBefore intervalDomain u T rho p0
```

There is also a rho-one specialization:

```lean
intervalDomain_relativeMoserInterpolationBefore_rho_one_of_massGradient
```

but the actual Prop25 route in `P3MoserActualWiring.lean` chooses

```lean
rho = 2 * params.γ
```

so the general theorem is the right one.

### Recommended replacement field

Replace the current `relativeMoserInterpolation` field by a lower-level mass-gradient frontier.

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly
import ShenWork.PDE.P3MoserLemmas

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserLemmas

noncomputable section

namespace ShenWork.Paper2

structure IntervalDomainPaper2RelativeMoserMassGradientFrontierData
    (p : CM2Params) : Prop where
  relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
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

end ShenWork.Paper2
```

### Wrapper using the reduced relative field

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly
import ShenWork.PDE.P3MoserLemmas

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserLemmas

noncomputable section

namespace ShenWork.Paper2

structure IntervalDomainPaper2Prop25ActualAtomWithMassGradientFrontierData
    (p : CM2Params) : Prop where
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
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
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

def IntervalDomainPaper2Prop25ActualAtomWithMassGradientFrontierData.toActualAtoms
    {p : CM2Params}
    (h : IntervalDomainPaper2Prop25ActualAtomWithMassGradientFrontierData p) :
    IntervalDomainPaper2Prop25ActualAtomFrontierData p where
  moserDissipation := h.moserDissipation
  relativeMoserInterpolation := by
    intro T rho p0 u v hsol hcross hboot
    rcases h.relativeMassGradient hsol hcross hboot with
      ⟨cGrad, hcGrad, hMG, hgrad, hmassToLp⟩
    exact intervalDomain_relativeMoserInterpolationBefore_of_massGradient
      cGrad hcGrad hMG hgrad hmassToLp
  quantitativeEndpoint := h.quantitativeEndpoint

theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomWithMassGradientFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    p hData.toActualAtoms

end ShenWork.Paper2
```

This is the cleanest immediate net-reduction.

## Atom 3: `quantitativeEndpoint`

### Existing endpoint/dyadic APIs

File:

```text
ShenWork/Paper2/IntervalDomainMoserClosure.lean
```

Endpoint definition:

```lean
def IntervalDomainMoserQuantitativeEndpoint
    (u : ℝ → intervalDomain.Point → ℝ) (T : ℝ)
    (pSeq rootBound : ℕ → ℝ) : Prop :=
  ∃ M, 0 ≤ M ∧ ∃ n : ℕ,
    0 < pSeq n ∧ 0 ≤ rootBound n ∧ rootBound n ≤ M ∧
      IntervalDomainMoserPointwisePowerControlBefore u T (pSeq n) (rootBound n)
```

Endpoint consumer:

```lean
theorem intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    {u : ℝ → intervalDomain.Point → ℝ} {T : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hEndpoint : IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u
```

File:

```text
ShenWork/PDE/IntervalDomainMoserActualAtoms.lean
```

Dyadic algebra already proved:

```lean
theorem dyadic_root_tower_product_bound
    (n : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    (∏ k ∈ Finset.Icc 1 n, dyadicMoserFactor C k) ≤ 4 * C

theorem dyadic_root_tower_iterate_bound
    {C : ℝ} {M : ℕ → ℝ} (hC : 1 ≤ C)
    (hrec : ∀ k, 1 ≤ k →
      M (k + 1) ≤ dyadicMoserFactor C k * M k) :
    ∀ n,
      M (n + 1) ≤
        (∏ k ∈ Finset.Icc 1 n, dyadicMoserFactor C k) * M 1

theorem dyadic_root_tower_bound
    {C : ℝ} {M : ℕ → ℝ} (hC : 1 ≤ C) (hM1 : 0 ≤ M 1)
    (hrec : ∀ k, 1 ≤ k →
      M (k + 1) ≤ dyadicMoserFactor C k * M k) :
    ∀ n, M (n + 1) ≤ 4 * C * M 1
```

### Audit verdict

There is **no existing theorem** that constructs

```lean
∃ pSeq rootBound, (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
  IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

from the dyadic root-tower lemmas plus solution data.  The dyadic lemmas are real and useful, but they only bound an abstract recurrence.  They do not provide the pointwise power control field:

```lean
IntervalDomainMoserPointwisePowerControlBefore u T (pSeq n) (rootBound n)
```

Therefore the current `quantitativeEndpoint` field should **not** be replaced yet.  The honest future replacement would need a new endpoint producer whose input exposes:

```lean
pSeq rootBound : ℕ → ℝ
pSeq positivity at some n
rootBound recurrence controlled by dyadic_root_tower_bound
pointwise power control from the Moser/Agmon terminal step
```

but no such theorem exists now.

## Existing lower-level facts already consumed internally by actual-atom Prop25

The actual-atom wrapper already performs several reductions internally, so these should not be reintroduced as fields:

File:

```text
ShenWork/PDE/P3MoserActualWiring.lean
```

Internally used theorem:

```lean
theorem intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

Internal steps:

```lean
-- cross diffusion bootstrap from classical solution
intervalDomain_crossDiffusionBootstrapEstimate_of_classical hsol

-- bootstrap seed with rho = 2 * params.γ
abstract_prop25_bootstrap_two_gamma hT hpExp hLp

-- energy inequality from regularity
intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot

-- Lp monotonicity from positivity + power integrability
intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg
intervalDomain_u_rpow_intervalIntegrable_of_regularity

-- final Moser closure
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
```

So do not make `CrossDiffusionBootstrapEstimate`, `LpBootstrapEnergyInequality`, power-integrability, or Lp monotonicity fields of the Paper2 Prop25 statement frontier again.

## No-go / avoid-list

### Do not use `OldUnitIntervalPowerGNYoungForMoser`

File:

```text
ShenWork/Paper2/IntervalDomainMCL.lean
```

Legacy false predicate:

```lean
def OldUnitIntervalPowerGNYoungForMoser : Prop := ...
```

The file itself says it is false for constant functions.  This is formally confirmed in:

```text
ShenWork/Paper2/IntervalDomainGNYObstruction.lean
```

by:

```lean
theorem not_oldUnitIntervalPowerGNYoungForMoser :
    ¬ OldUnitIntervalPowerGNYoungForMoser
```

Therefore avoid:

```lean
Proposition_2_5_intervalDomain_of_MCL_frontiers
relativeMoserInterpolationBefore_of_unitIntervalPowerGNYoung
```

as headline routes, because they use the old false predicate.

The proved replacement:

```lean
def UnitIntervalPowerGNYoungForMoser : Prop := ...

theorem unitIntervalPowerGNYoungForMoser_proved :
    UnitIntervalPowerGNYoungForMoser
```

is real, but it is **not yet wired** into the Prop25 actual-atom route.  A future theorem can use it to prove the mass-gradient inputs for

```lean
intervalDomain_relativeMoserInterpolationBefore_of_massGradient
```

but that bridge is not present now.

### Do not use global `IntervalDomainInterpolation`

The global interpolation premise is refuted by:

```lean
ShenWork.Paper2.IntervalDomainInterpolationCounterexample
  .not_intervalDomainInterpolation
```

Routes depending on global `IntervalDomainInterpolation` remain unsupported/vacuous for headline accounting.

### Do not derive `MoserDissipationDropBeforeNonnegB` abstractly

The file `P3MoserDissipationShape.lean` proves:

```lean
unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

so the pointwise drop shape is not an abstract consequence of the bounded-domain interface.  It is a genuine PDE/Moser atom unless replaced by a new integrated-first-crossing Moser closure theorem.

## Recommended immediate patch

Add only the relative-interpolation reduction now.  Keep `moserDissipation` and `quantitativeEndpoint` as current actual atoms.

Suggested patch file:

```text
ShenWork/Paper2/IntervalDomainProp25MassGradientFrontier.lean
```

Patch outline:

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly
import ShenWork.PDE.P3MoserLemmas

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserLemmas

noncomputable section

namespace ShenWork.Paper2

structure IntervalDomainPaper2Prop25ActualAtomWithMassGradientFrontierData
    (p : CM2Params) : Prop where
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
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
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

def IntervalDomainPaper2Prop25ActualAtomWithMassGradientFrontierData.toActualAtoms
    {p : CM2Params}
    (h : IntervalDomainPaper2Prop25ActualAtomWithMassGradientFrontierData p) :
    IntervalDomainPaper2Prop25ActualAtomFrontierData p where
  moserDissipation := h.moserDissipation
  relativeMoserInterpolation := by
    intro T rho p0 u v hsol hcross hboot
    rcases h.relativeMassGradient hsol hcross hboot with
      ⟨cGrad, hcGrad, hMG, hgrad, hmassToLp⟩
    exact intervalDomain_relativeMoserInterpolationBefore_of_massGradient
      cGrad hcGrad hMG hgrad hmassToLp
  quantitativeEndpoint := h.quantitativeEndpoint

theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomWithMassGradientFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    p hData.toActualAtoms

end ShenWork.Paper2
```

## Priority order after this audit

1. Add the mass-gradient-relative frontier wrapper above.  This is the only safe immediate net-reduction among the three fields.
2. Do not replace `quantitativeEndpoint` until a theorem constructs `IntervalDomainMoserQuantitativeEndpoint` from dyadic recurrence plus pointwise terminal control.
3. Do not replace `moserDissipation` with the integrated shape until a new integrated-first-crossing Moser closure theorem consumes `IntegratedMoserDissipationDropBefore` directly.
4. Keep `OldUnitIntervalPowerGNYoungForMoser` and global `IntervalDomainInterpolation` out of all headline Prop25 routes.
