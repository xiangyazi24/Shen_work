# Q2411 shen2: integrated-first-crossing Moser closure API audit

Repo target: `xiangyazi24/Shen_work`, `main` at commit `c89c01043b5ae73d61089da2631f7e53a49d65cf`.

## Verdict

The current source still has no theorem that consumes

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.IntegratedMoserDissipationDropBefore
```

inside the Proposition 2.5 / Corollary 2.1 Moser route.  The only current consumers are still pointwise-step consumers requiring

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.MoserDissipationDropBeforeNonnegB
```

The minimal honest API layer is therefore:

1. add a new file `ShenWork/PDE/P3MoserIntegratedClosure.lean` with a **buildable step-consumer closure**;
2. isolate one future analytic theorem that turns integrated energy + first-crossing regularity + relative interpolation into the step;
3. only after that theorem is proved, add routine actual-atom and statement-layer wrappers.

The real analytic proof is exactly the production of the one-step bound

```lean
LpPowerBoundedBefore D p T u → LpPowerBoundedBefore D (p + rho) T u
```

from `IntegratedMoserDissipationDropBefore` and `RelativeMoserInterpolationBefore`.  Everything downstream of that one-step theorem is a routine copy of the existing pointwise Moser chain.

## Current source audit

### `P3MoserDissipationShape.lean`

Current facts:

* `MoserDissipationDropBeforeNonnegB` is the physical-`B` pointwise predicate.
* `moserDissipationDropBeforeNonnegB_of_raw_drop` packages raw pointwise drop data into that predicate.
* `IntegratedMoserDissipationDropBefore` is already defined with the intended integrated shape:

```lean
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

* `integratedMoserDissipationDropBefore_of_integrated_energy` only packages a same-shape integrated estimate into the predicate.
* `unitLinearDrop_not_MoserDissipationDropBeforeNonnegB` proves that the pointwise nonnegative-`B` predicate is not a harmless consequence of abstract energy information.
* The current closure theorem `moser_step_of_energy_nonnegB_relative_interpolation` performs a local subtraction using

```lean
have hdrop_t := hdiss p hp A B K L_const hB.le hfull t ht0 htT
```

so it cannot consume the integrated predicate.

### `P3MoserActualWiring.lean`

Current actual-atom consumers are:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

Both require an `hdiss` producing `MoserDissipationDropBeforeNonnegB`.  The endpoint consumer constructs the Prop. 2.5 seed at `rho = 2 * params.γ` via

```lean
abstract_prop25_bootstrap_two_gamma
```

then calls

```lean
intervalDomain_boundedBefore_of_energy_nonnegB_relative_interpolation
```

with the pointwise nonnegative-`B` dissipation field.

### `P3MoserLemmas.lean`

Useful nearby facts:

* `intervalDomain_relativeMoserInterpolationBefore_of_massGradient` already lowers the relative Moser field from the mass-gradient inputs.
* `ClosedEnergyIdentityTraceData` and `closedEnergyTrace_to_l2SeedRegularityFrontier` are a useful precedent for closed-time continuity/trace packaging, but they only target the L² seed regularity frontier.  They do not provide all-exponent continuity or any integrated first-crossing Moser step.

Gap: the integrated ladder needs closed-time information for each exponent used in the iteration, not only the L² seed.

### `IntervalDomainMoserClosure.lean`

Useful existing routine lemmas:

```lean
all_exponents_of_chain_and_lp_mono
intervalDomain_boundedBefore_of_moser_quantitative_endpoint
```

These already prove the exponent-lattice part and final endpoint handoff once a chain

```lean
∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u
```

is available.

Gap: all existing Moser-chain producers are pointwise.  The route

```lean
moser_step_of_energy_dissipation_relative_interpolation
moser_iteration_chain_of_energy_dissipation_relative_interpolation
intervalDomain_boundedBefore_of_energy_dissipation_relative_interpolation
```

uses `MoserDissipationDropBefore`, while the newer route in `P3MoserDissipationShape` uses `MoserDissipationDropBeforeNonnegB`.  Neither consumes `IntegratedMoserDissipationDropBefore`.

### `IntervalDomainStatementAssembly.lean`

Current statement-layer status at this commit:

* `IntervalDomainPaper2Prop25ActualAtomFrontierData` carries `MoserDissipationDropBeforeNonnegB`.
* `IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms` keeps `moserDissipation := h.moserDissipation` and only lowers the relative field.
* `IntervalDomainPaper2Prop25ActualAtomMassGradientTerminalEndpointFrontierData.toMassGradient` keeps `moserDissipation := h.moserDissipation` and only lowers the endpoint.
* New raw-drop route:

```lean
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
```

packages `rawMoserDrop` to `MoserDissipationDropBeforeNonnegB` using

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape.moserDissipationDropBeforeNonnegB_of_raw_drop
```

This is buildable and useful, but it is still the pointwise route.  It does not address the integrated PDE energy shape.

## Minimal API layer

### Stage 1: buildable integrated closure skeleton

Add a new file:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

with the following buildable content.  This file does not prove the integrated first-crossing estimate; it isolates the exact step needed and proves the routine chain/endpoint consequences from that step.

```lean
import ShenWork.PDE.P3MoserDissipationShape

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Closed-time and time-integrability data needed by an integrated
first-crossing Moser step.  The existing L² closed-energy bridge is not enough:
this data is indexed by every exponent `p >= p0` used in the ladder. -/
structure IntegratedMoserFirstCrossingRegularity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  initialPowerBound :
    ∀ p, p0 ≤ p →
      ∃ C0, 0 ≤ C0 ∧
        D.integral (fun x => (u 0 x) ^ p) ≤ C0
  powerTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => D.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- The one-step output needed from the integrated first-crossing argument. -/
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u

/-- Routine: iterate a supplied integrated first-crossing step along the
arithmetic Moser ladder. -/
theorem moser_iteration_chain_of_integrated_first_crossing_step
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 rho : ℝ}
    (hrho : 0 < rho)
    (hbase : LpPowerBoundedBefore D p0 T u)
    (hstep : IntegratedMoserFirstCrossingStep D u T rho p0) :
    ∀ n : ℕ, LpPowerBoundedBefore D (p0 + n * rho) T u := by
  intro n
  induction n with
  | zero =>
      simp only [CharP.cast_eq_zero, zero_mul, add_zero]
      exact hbase
  | succ n ih =>
      have hexp_eq :
          p0 + (↑(n + 1) : ℝ) * rho = (p0 + ↑n * rho) + rho := by
        push_cast
        ring
      rw [hexp_eq]
      have hp_ge : p0 ≤ p0 + ↑n * rho :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hrho.le)
      exact hstep (p0 + ↑n * rho) hp_ge ih

/-- Routine: a supplied integrated first-crossing step plus downward Lp
monotonicity gives all finite exponents. -/
theorem all_exponents_of_integrated_first_crossing_step_lpmono
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {N T rho p0 : ℝ}
    (hboot : AbstractLpBootstrapHypothesis D u N T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep D u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore D q T u → LpPowerBoundedBefore D p T u) :
    ∀ pExp > 1, LpPowerBoundedBefore D pExp T u := by
  exact all_exponents_of_chain_and_lp_mono
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (moser_iteration_chain_of_integrated_first_crossing_step
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (AbstractLpBootstrapHypothesis.initial_lp_bound hboot)
      hstep)
    hLpMono

/-- Routine: interval-domain finite-horizon boundedness from a supplied
integrated first-crossing step and the existing quantitative endpoint. -/
theorem intervalDomain_boundedBefore_of_integrated_first_crossing_step
    {u : ℝ → intervalDomain.Point → ℝ} {N T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u N T rho p0)
    (hstep : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0)
    (hLpMono :
      ∀ {p q : ℝ}, 1 < p → p ≤ q →
        LpPowerBoundedBefore intervalDomain q T u →
        LpPowerBoundedBefore intervalDomain p T u)
    (hEndpoint :
      (∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u) →
        IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAll : ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u :=
    all_exponents_of_integrated_first_crossing_step_lpmono
      hboot hstep hLpMono
  exact intervalDomain_boundedBefore_of_moser_quantitative_endpoint
    (hEndpoint hAll)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

This stage is buildable because it does not claim the integrated PDE estimate implies the step.  It only states and consumes the step.

### Stage 2: the one real analytic theorem

After Stage 1, add the following theorem to `P3MoserIntegratedClosure.lean`.  This is the actual integrated-first-crossing proof.  It is not a routine wrapper.

Signature:

```lean
/-- REAL ANALYTIC PROOF: integrated first-crossing Moser step.
This is the only non-routine theorem in the proposed layer. -/
theorem integratedMoserFirstCrossingStep_of_integrated_dissipation_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hT : 0 < T)
    (hrho : 0 < rho)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0
```

Expected proof shape:

* fix `p >= p0` and assume `LpPowerBoundedBefore D p T u`;
* use `hdiss p hp` to get the integrated inequality for `Y_p` and `G_p`;
* use `hrel p hp` plus the current `Y_p` bound to convert relative interpolation into an integrated estimate for `Y_{p+rho}`;
* run a first-crossing/continuity argument using `hreg.energyContinuous p hp`, the closed-time initial bound, and time integrability;
* conclude `LpPowerBoundedBefore D (p + rho) T u`.

This theorem is exactly where the faithful PDE integrated shape enters.  No current theorem nearly proves it.  The closest existing theorem is

```lean
moser_step_of_energy_nonnegB_relative_interpolation
```

but that theorem uses a pointwise drop to subtract `Y'_p + B Y_p` at a fixed time.  The integrated theorem must avoid that subtraction entirely.

### Stage 3: routine actual-atom consumers once Stage 2 exists

After `integratedMoserFirstCrossingStep_of_integrated_dissipation_relative` is proved, add this import to `P3MoserActualWiring.lean`:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
```

Then add these routine consumers in namespace
`ShenWork.IntervalDomainExistence.P3MoserActualWiring`.

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Integrated actual atoms produce Corollary 2.1.  Routine after the integrated
first-crossing step theorem exists. -/
theorem intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_atoms
    {params : CM2Params}
    (hreg :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain params := by
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0, hp0Lp⟩
  have hboot :
      AbstractLpBootstrapHypothesis intervalDomain u
        (params.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0, hp0Lp⟩
  have hstep :
      IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
    integratedMoserFirstCrossingStep_of_integrated_dissipation_relative
      hT hrho
      (hreg hsol hcross hboot)
      (hdiss hsol hcross hboot)
      (hrel hsol hcross hboot)
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
      hboot hstep hLpMono pExp hpExp

/-- Integrated actual atoms plus the quantitative endpoint produce Proposition
2.5.  Routine after the integrated first-crossing step theorem exists. -/
theorem intervalDomain_endpointBoundFromLp_of_actual_integrated_atoms
    {params : CM2Params}
    (hreg :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hdiss :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hrel :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain params T u v →
        CrossDiffusionBootstrapEstimate intervalDomain params T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (params.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0)
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
  have hrho : 0 < 2 * params.γ := by
    nlinarith [params.hγ]
  have hstep :
      IntegratedMoserFirstCrossingStep intervalDomain u T
        (2 * params.γ) pExp :=
    integratedMoserFirstCrossingStep_of_integrated_dissipation_relative
      hT hrho
      (hreg hsol hcross hboot)
      (hdiss hsol hcross hboot)
      (hrel hsol hcross hboot)
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
      hboot hstep hLpMono hQuantEndpoint
```

The proof structure is copied from `intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB`; the only new dependency is the Stage 2 integrated step theorem.

### Stage 4: statement-layer integrated actual-atom packages

After Stage 3, add to `IntervalDomainStatementAssembly.lean`:

```lean
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

#### Basic integrated actual-atom frontier

```lean
/-- Integrated actual-atom frontier for interval-domain Proposition 2.5 and
Corollary 2.1.  This is the faithful replacement for the pointwise
nonnegative-`B` dissipation atom once the integrated first-crossing closure is
proved. -/
structure IntervalDomainPaper2Prop25ActualIntegratedAtomFrontierData
    (p : CM2Params) : Prop where
  firstCrossingRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      IntegratedMoserFirstCrossingRegularity intervalDomain u T p0
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ShenWork.IntervalDomainExistence.P3MoserDissipationShape.IntegratedMoserDissipationDropBefore
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

/-- Integrated actual atoms produce interval-domain Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_actualIntegratedAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualIntegratedAtomFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_integrated_atoms
    hData.firstCrossingRegularity
    hData.integratedDissipation
    hData.relativeMoserInterpolation
    hData.quantitativeEndpoint

/-- Integrated actual atoms produce interval-domain Corollary 2.1. -/
theorem intervalDomainPaper2_Corollary_2_1_of_actualIntegratedAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualIntegratedAtomFrontierData p) :
    Corollary_2_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_atoms
    hData.firstCrossingRegularity
    hData.integratedDissipation
    hData.relativeMoserInterpolation
```

#### Preferred terminal-endpoint / mass-gradient integrated frontier

This mirrors the current
`IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData`, replacing `rawMoserDrop` by the integrated-frontier pair.

```lean
/-- Integrated-dissipation version of the terminal-endpoint, mass-gradient
actual-atom frontier. -/
structure
    IntervalDomainPaper2Prop25ActualIntegratedAtomMassGradientTerminalEndpointFrontierData
    (p : CM2Params) : Prop where
  firstCrossingRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      IntegratedMoserFirstCrossingRegularity intervalDomain u T p0
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ShenWork.IntervalDomainExistence.P3MoserDissipationShape.IntegratedMoserDissipationDropBefore
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

/-- Convert integrated terminal-endpoint/mass-gradient data to the basic
integrated actual-atom frontier. -/
def
    IntervalDomainPaper2Prop25ActualIntegratedAtomMassGradientTerminalEndpointFrontierData.toIntegratedAtoms
    {p : CM2Params}
    (h :
      IntervalDomainPaper2Prop25ActualIntegratedAtomMassGradientTerminalEndpointFrontierData
        p) :
    IntervalDomainPaper2Prop25ActualIntegratedAtomFrontierData p where
  firstCrossingRegularity := h.firstCrossingRegularity
  integratedDissipation := h.integratedDissipation
  relativeMoserInterpolation := by
    intro T rho p0 u v hsol hcross hboot
    rcases h.relativeMassGradient hsol hcross hboot with
      ⟨cGrad, hcGrad, hMG, hgrad, hmassToLp⟩
    exact
      ShenWork.IntervalDomainExistence.P3MoserLemmas.intervalDomain_relativeMoserInterpolationBefore_of_massGradient
        cGrad hcGrad hMG hgrad hmassToLp
  quantitativeEndpoint := by
    intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
    rcases h.terminalEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
      ⟨q, R, hq, hR, hpoint⟩
    refine ⟨fun _ : ℕ => q, fun _ : ℕ => R, ?_⟩
    intro hAllLp
    exact ⟨R, hR, 0, hq, hR, le_rfl, hpoint hAllLp⟩

/-- Integrated terminal-endpoint mass-gradient atoms produce Proposition 2.5. -/
theorem
    intervalDomainPaper2_Proposition_2_5_of_actualIntegratedAtomMassGradientTerminalEndpointFrontierData
    (p : CM2Params)
    (hData :
      IntervalDomainPaper2Prop25ActualIntegratedAtomMassGradientTerminalEndpointFrontierData
        p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualIntegratedAtomFrontierData
    p hData.toIntegratedAtoms

/-- Integrated terminal-endpoint mass-gradient atoms produce Corollary 2.1. -/
theorem
    intervalDomainPaper2_Corollary_2_1_of_actualIntegratedAtomMassGradientTerminalEndpointFrontierData
    (p : CM2Params)
    (hData :
      IntervalDomainPaper2Prop25ActualIntegratedAtomMassGradientTerminalEndpointFrontierData
        p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_actualIntegratedAtomFrontierData
    p hData.toIntegratedAtoms
```

Thin section-2 and preferred headline wrappers can then be cloned from the current raw-drop terminal-endpoint mass-gradient wrappers by replacing

```lean
IntervalDomainPaper2Prop25ActualAtomRawDropMassGradientTerminalEndpointFrontierData
```

with

```lean
IntervalDomainPaper2Prop25ActualIntegratedAtomMassGradientTerminalEndpointFrontierData
```

and replacing calls to `.toTerminalEndpoint` by `.toIntegratedAtoms`.

## Existing theorems that nearly prove parts of the route

* `all_exponents_of_chain_and_lp_mono`: already proves the non-analytic exponent-lattice closure once a chain is available.  No gap for this part.
* `intervalDomain_boundedBefore_of_moser_quantitative_endpoint`: already proves finite-horizon boundedness from all finite Lp bounds plus the quantitative endpoint.  No gap for this part.
* `intervalDomain_relativeMoserInterpolationBefore_of_massGradient`: already lowers mass-gradient data to `RelativeMoserInterpolationBefore`.  No gap for this conversion.
* `abstract_prop25_bootstrap_two_gamma`: already builds the Prop. 2.5 bootstrap seed at `rho = 2 * params.γ`.  No gap for this seed.
* `intervalDomain_LpPowerBoundedBefore_mono_of_integrable_nonneg` plus `intervalDomain_u_rpow_intervalIntegrable_of_regularity`: already provide downward Lp monotonicity for classical positive interval solutions.  No gap for this part.
* `ClosedEnergyIdentityTraceData.energyContinuous` / `closedEnergyTrace_to_l2SeedRegularityFrontier`: useful pattern for closed-time continuity and trace packaging, but only for L² seed data.  Gap: the integrated first-crossing ladder needs all-exponent time continuity and integrability, captured above by `IntegratedMoserFirstCrossingRegularity`.
* `moser_step_of_energy_nonnegB_relative_interpolation`: closest old Moser step.  Gap: it depends on pointwise nonnegative-`B` subtraction, so it cannot consume `IntegratedMoserDissipationDropBefore`.

## Build order

1. Add `P3MoserIntegratedClosure.lean` with `IntegratedMoserFirstCrossingRegularity`, `IntegratedMoserFirstCrossingStep`, and the three routine consumer theorems.  This is buildable immediately.
2. Prove `integratedMoserFirstCrossingStep_of_integrated_dissipation_relative`.  This is the only real analytic proof in the proposed layer.
3. Add the two routine actual-atom consumers to `P3MoserActualWiring.lean`.
4. Add `IntervalDomainPaper2Prop25ActualIntegratedAtomFrontierData` and the terminal-endpoint/mass-gradient integrated frontier to `IntervalDomainStatementAssembly.lean`.
5. Add thin/preferred headline wrappers by cloning the current raw-drop terminal-endpoint mass-gradient wrappers and swapping in the integrated frontier.

Until step 2 is proved, the integrated predicate should remain a named frontier and should not be converted to `MoserDissipationDropBeforeNonnegB`.
