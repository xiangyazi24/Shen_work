import ShenWork.Paper2.IntervalLemma31Closure
/-
  Paper2 interval-domain statement-target assembly.

  This file only packages already-proved interval-domain bridges and existing
  statement-layer branch-data wrappers.  It adds no analytic estimate.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
import ShenWork.Paper2.IntervalDomainMass
import ShenWork.Paper2.IntervalDomainStructuredMoserData
import ShenWork.Paper2.IntervalDomainTheorem12
import ShenWork.Paper2.IntervalDomainTheorem13
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserLemmas

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper2

noncomputable section

/-! ## Section 2 statement targets -/

/-- Interval-domain Paper 2 section-2 targets covered by the existing bundled
bootstrap/estimate branch-data record. -/
def IntervalDomainPaper2BootstrapEstimateTargets (p : CM2Params) : Prop :=
  Lemma_2_6 intervalDomain ∧
    Lemma_2_7 intervalDomain ∧
      Proposition_2_2 intervalDomain p ∧
        Proposition_2_3 intervalDomain p ∧
          Proposition_2_4 intervalDomain p ∧
            Proposition_2_5 intervalDomain p

/-- Interval-domain wrapper for Lemmas 2.6--2.7 and Propositions 2.2--2.5
from the statement-layer branch-data package. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  lemma_2_6_2_7_and_propositions_2_2_to_2_5_of_branchData hData

/-- Instance-facing interval-domain wrapper for the section-2 target bundle. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_branchData p hData.out

/-- Thinner interval-domain section-2 bootstrap data for routes that already
produce Proposition 2.4 and Proposition 2.5 elsewhere. -/
structure IntervalDomainPaper2BootstrapEstimateThinFrontierData
    (p : CM2Params) : Prop where
  lemma26 :
    ∀ N > 0, ∀ u : ℝ → intervalDomain.Point → ℝ, ∀ T rho p0,
      AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
          ∀ pExp > 1, LpPowerBoundedBefore intervalDomain pExp T u
  lemma27 :
    ∀ u : ℝ → intervalDomain.Point → ℝ, ∀ T pExp C1 C2 C3 C4 eps alpha,
      0 < T → 1 < pExp →
        0 ≤ C1 → 0 ≤ C2 → 0 ≤ C3 → 0 < C4 →
          0 < eps → eps ≤ alpha →
            (∀ t, 0 < t → t < T →
              deriv (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
                  C3 * intervalDomain.integral (fun x => (u t x) ^ (pExp + alpha - eps)) ≤
                C1 + C2 * intervalDomain.integral (fun x => (u t x) ^ pExp) -
                  C4 * intervalDomain.integral (fun x => (u t x) ^ (pExp + alpha))) →
              LpPowerBoundedBefore intervalDomain pExp T u
  prop22 :
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
        ∀ pExp > 1, ∃ Mstar > 0,
          WeightedGradientEstimate intervalDomain pExp p.β p.γ Mstar T u v
  prop23 :
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
        ∀ pExp, max 1 p.β < pExp →
          ∀ eps > 0, ∃ Ceps > 0,
            WeightedSignalEstimate intervalDomain pExp p.β p.γ eps Ceps T u v

/-- Structured-Moser frontier for interval-domain Proposition 2.5.

This is thinner than carrying `Proposition_2_5 intervalDomain p` directly:
for each solution/exponent seed it supplies the Moser bootstrap record used by
`IntervalDomainStructuredMoserData.Proposition_2_5_intervalDomain_of_prop25_moser_frontiers`.
-/
structure IntervalDomainPaper2Prop25StructuredMoserFrontierData
    (p : CM2Params) : Prop where
  frontiers :
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
          LpBootstrapEnergyInequality intervalDomain u T 1 pExp ∧
          MoserDissipationDropBefore intervalDomain u T 1 pExp ∧
          RelativeMoserInterpolationBefore intervalDomain u T 1 pExp ∧
          (∀ r : ℝ, 1 < r → ∀ t, 0 < t → t < T →
            IntervalIntegrable
              (intervalDomainLift
                (fun x : intervalDomain.Point => (u t x) ^ r))
              MeasureTheory.volume 0 1) ∧
          ((∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound)

/-- Produce interval-domain Proposition 2.5 from the structured-Moser frontier. -/
theorem intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25StructuredMoserFrontierData p) :
    Proposition_2_5 intervalDomain p := by
  classical
  refine
    IntervalDomainStructuredMoserData.Proposition_2_5_intervalDomain_of_prop25_moser_frontiers
      ?_
  intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
  let hFrontiers := hData.frontiers hu₀ hT hsol htrace pExp hpExp hLp
  let pSeq : ℕ → ℝ := Classical.choose hFrontiers
  let hRootExists := Classical.choose_spec hFrontiers
  let rootBound : ℕ → ℝ := Classical.choose hRootExists
  let hSpec := Classical.choose_spec hRootExists
  exact
    { pSeq := pSeq
      rootBound := rootBound
      energy := hSpec.1
      dissipation := hSpec.2.1
      relative := hSpec.2.2.1
      powerIntegrable := hSpec.2.2.2.1
      endpoint := hSpec.2.2.2.2 }

/-- Instance-facing structured-Moser Proposition 2.5 wrapper. -/
theorem intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25StructuredMoserFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierData
    p hData.out

/-- Actual-atom frontier for interval-domain Proposition 2.5.

This is thinner than `IntervalDomainPaper2Prop25StructuredMoserFrontierData`:
the cross-diffusion seed, energy inequality, power-integrability, and Lp
monotonicity are produced inside
`intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB`; the carried atoms
are only the nonnegative-B dissipation, relative Moser interpolation, and the
quantitative root-tower endpoint.
-/
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

/-- Produce interval-domain Proposition 2.5 from the actual-atom frontier. -/
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    hData.moserDissipation
    hData.relativeMoserInterpolation
    hData.quantitativeEndpoint

/-- Instance-facing actual-atom Proposition 2.5 wrapper. -/
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25ActualAtomFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData p hData.out

/-- Actual-atom Proposition 2.5 frontier with the relative-Moser field reduced
to the mass-gradient inputs used by `P3MoserLemmas`.

The dissipation and quantitative endpoint fields remain the honest actual
atoms; this wrapper only lowers the relative-interpolation boundary. -/
structure IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData
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

/-- Convert the mass-gradient relative-Moser frontier to the actual-atom
frontier consumed by the existing Prop. 2.5 and Corollary 2.1 routes. -/
def IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms
    {p : CM2Params}
    (h : IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p) :
    IntervalDomainPaper2Prop25ActualAtomFrontierData p where
  moserDissipation := h.moserDissipation
  relativeMoserInterpolation := by
    intro T rho p0 u v hsol hcross hboot
    rcases h.relativeMassGradient hsol hcross hboot with
      ⟨cGrad, hcGrad, hMG, hgrad, hmassToLp⟩
    exact
      ShenWork.IntervalDomainExistence.P3MoserLemmas.intervalDomain_relativeMoserInterpolationBefore_of_massGradient
        cGrad hcGrad hMG hgrad hmassToLp
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Mass-gradient relative-Moser frontier produces interval-domain Proposition
2.5 via the actual-atom route. -/
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    p hData.toActualAtoms

/-- Instance-facing mass-gradient relative-Moser Proposition 2.5 wrapper. -/
theorem
    intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierDataFact
    (p : CM2Params)
    [hData :
      Fact (IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierData
    p hData.out

/-- Actual-atom frontier produces interval-domain Corollary 2.1. -/
theorem intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Corollary_2_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
    hData.moserDissipation hData.relativeMoserInterpolation

/-- Instance-facing actual-atom Corollary 2.1 wrapper. -/
theorem intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25ActualAtomFrontierData p)] :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData
    p hData.out

/-- Actual-atom frontier produces both Tier-1 inputs used by Theorems 1.2 and
1.3. -/
theorem
    intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p :=
  ⟨intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData p hData,
    intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData p hData⟩

/-- Mass-gradient relative-Moser frontier produces interval-domain Corollary
2.1 via the actual-atom route. -/
theorem
    intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData
    p hData.toActualAtoms

/-- Instance-facing mass-gradient relative-Moser Corollary 2.1 wrapper. -/
theorem
    intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientFrontierDataFact
    (p : CM2Params)
    [hData :
      Fact (IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p)] :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientFrontierData
    p hData.out

/-- Section-2 target wrapper from the thinner branch data, with Proposition
2.4 supplied by the interval-domain mass proof and Proposition 2.5 supplied by
the current theorem-level route. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hProp25 : Proposition_2_5 intervalDomain p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  ⟨Lemma_2_6.of_assumed_bound_branch hData.lemma26,
    Lemma_2_7.of_assumed_bound_branch hData.lemma27,
    Proposition_2_2.of_assumed_estimate_branch hData.prop22,
    Proposition_2_3.of_assumed_estimate_branch hData.prop23,
    intervalDomain_Proposition_2_4 p,
    hProp25⟩

/-- Instance-facing section-2 target wrapper from the thinner branch data. -/
theorem intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2BootstrapEstimateThinFrontierData p)]
    [hProp25 : Fact (Proposition_2_5 intervalDomain p)] :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
    p hData.out hProp25.out

/-- Section-2 targets from the thin frontiers and the structured-Moser
Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinStructuredMoserFrontierData
    (p : CM2Params)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hMoser : IntervalDomainPaper2Prop25StructuredMoserFrontierData p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
    p hThin
    (intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierData
      p hMoser)

/-- Instance-facing section-2 wrapper from thin frontiers and the
structured-Moser Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinStructuredMoserFrontierDataFact
    (p : CM2Params)
    [hThin : Fact (IntervalDomainPaper2BootstrapEstimateThinFrontierData p)]
    [hMoser :
      Fact (IntervalDomainPaper2Prop25StructuredMoserFrontierData p)] :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinStructuredMoserFrontierData
    p hThin.out hMoser.out

/-- Section-2 targets from the thin frontiers and the actual-atom Proposition
2.5 frontier. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierData
    (p : CM2Params)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hAtoms : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
    p hThin
    (intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
      p hAtoms)

/-- Instance-facing section-2 wrapper from thin frontiers and the actual-atom
Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierDataFact
    (p : CM2Params)
    [hThin : Fact (IntervalDomainPaper2BootstrapEstimateThinFrontierData p)]
    [hAtoms : Fact (IntervalDomainPaper2Prop25ActualAtomFrontierData p)] :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierData
    p hThin.out hAtoms.out

/-- Section-2 targets from the thin frontiers and the actual-atom Proposition
2.5 frontier with relative Moser interpolation supplied by mass-gradient data. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomMassGradientFrontierData
    (p : CM2Params)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hAtoms :
      IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p) :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierData
    p hThin hAtoms.toActualAtoms

/-- Instance-facing section-2 wrapper from thin frontiers and the actual-atom
mass-gradient Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomMassGradientFrontierDataFact
    (p : CM2Params)
    [hThin : Fact (IntervalDomainPaper2BootstrapEstimateThinFrontierData p)]
    [hAtoms :
      Fact (IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p)] :
    IntervalDomainPaper2BootstrapEstimateTargets p :=
  intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomMassGradientFrontierData
    p hThin.out hAtoms.out

/-- Single-target interval-domain wrapper for Lemma 2.6. -/
theorem intervalDomainPaper2_Lemma_2_6_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Lemma_2_6 intervalDomain :=
  Lemma_2_6.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Lemma 2.6. -/
theorem intervalDomainPaper2_Lemma_2_6_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Lemma_2_6 intervalDomain :=
  intervalDomainPaper2_Lemma_2_6_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Lemma 2.7. -/
theorem intervalDomainPaper2_Lemma_2_7_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Lemma_2_7 intervalDomain :=
  Lemma_2_7.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Lemma 2.7. -/
theorem intervalDomainPaper2_Lemma_2_7_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Lemma_2_7 intervalDomain :=
  intervalDomainPaper2_Lemma_2_7_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Proposition 2.2. -/
theorem intervalDomainPaper2_Proposition_2_2_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_2 intervalDomain p :=
  Proposition_2_2.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Proposition
2.2. -/
theorem intervalDomainPaper2_Proposition_2_2_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Proposition_2_2 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_2_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Proposition 2.3. -/
theorem intervalDomainPaper2_Proposition_2_3_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_3 intervalDomain p :=
  Proposition_2_3.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Proposition
2.3. -/
theorem intervalDomainPaper2_Proposition_2_3_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Proposition_2_3 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_3_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Proposition 2.4. -/
theorem intervalDomainPaper2_Proposition_2_4_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_4 intervalDomain p :=
  Proposition_2_4.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Proposition
2.4. -/
theorem intervalDomainPaper2_Proposition_2_4_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Proposition_2_4 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_4_of_branchData p hData.out

/-- Single-target interval-domain wrapper for Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_branchData
    (p : CM2Params)
    (hData : Paper2BootstrapEstimateBranchData intervalDomain p) :
    Proposition_2_5 intervalDomain p :=
  Proposition_2_5.of_branchData hData

/-- Instance-facing single-target interval-domain wrapper for Proposition
2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_branchDataFact
    (p : CM2Params)
    [hData : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_branchData p hData.out

/-- Frontier data for interval-domain Corollary 2.1 assembled from the
statement-layer Moser branch and the PDE energy derivation. -/
structure IntervalDomainPaper2Corollary21FrontierData
    (p : CM2Params) : Prop where
  bootstrap : Paper2BootstrapEstimateBranchData intervalDomain p
  energyFromCrossDiffusion :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0

/-- Interval-domain Corollary 2.1 from the Moser branch and PDE energy
frontier. -/
theorem intervalDomainPaper2_Corollary_2_1_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Corollary21FrontierData p) :
    Corollary_2_1 intervalDomain p :=
  IntervalDomainCorollary21.Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
    p (Lemma_2_6.of_branchData hData.bootstrap)
    hData.energyFromCrossDiffusion

/-- Instance-facing interval-domain Corollary 2.1 wrapper. -/
theorem intervalDomainPaper2_Corollary_2_1_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Corollary21FrontierData p)] :
    Corollary_2_1 intervalDomain p :=
  intervalDomainPaper2_Corollary_2_1_of_frontierData p hData.out

/-- Bundle of interval-domain Corollary 2.1 with the section-2 targets already
available from the same bootstrap/estimate data. -/
def IntervalDomainPaper2Corollary21BootstrapTargets (p : CM2Params) : Prop :=
  Corollary_2_1 intervalDomain p ∧
    IntervalDomainPaper2BootstrapEstimateTargets p

/-- Combined interval-domain section-2 target wrapper including Corollary 2.1. -/
theorem intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Corollary21FrontierData p) :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  ⟨intervalDomainPaper2_Corollary_2_1_of_frontierData p hData,
    intervalDomainPaper2_bootstrapEstimateTargets_of_branchData
      p hData.bootstrap⟩

/-- Instance-facing combined section-2 target wrapper including Corollary 2.1. -/
theorem intervalDomainPaper2_corollary21BootstrapTargets_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Corollary21FrontierData p)] :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
    p hData.out

/-! ## Section 3 and 4 a priori statement targets -/

/-- Interval-domain Paper 2 a priori statement targets already available from
the maximum-principle branch and the interval GN frontier. -/
def IntervalDomainPaper2AprioriTargets (p : CM2Params) : Prop :=
  Lemma_3_1 intervalDomain p ∧ Lemma_4_1 intervalDomain p

/-- Single-target interval-domain wrapper for Lemma 3.1. -/
theorem intervalDomainPaper2_Lemma_3_1
    (p : CM2Params) :
    Lemma_3_1 intervalDomain p :=
  Lemma31Closure.Lemma_3_1_intervalDomain p

/-- Single-target interval-domain wrapper for Lemma 4.1 from the concrete GN
frontier.

Deprecated as a headline route: this consumes
`IntervalDomainLemma41.IntervalDomainInterpolation`, which is refuted as
literally stated by
`IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.
Use the solution-slice or positive-solution-slice interpolation routes instead
until the global interpolation statement is repaired. -/
theorem intervalDomainPaper2_Lemma_4_1_of_GN_frontier
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation) :
    Lemma_4_1 intervalDomain p :=
  IntervalDomainTheorem11Composite.Lemma_4_1_intervalDomain_of_GN_frontier
    p hGN

/-- Instance-facing interval-domain wrapper for Lemma 4.1. -/
theorem intervalDomainPaper2_Lemma_4_1_of_GN_frontierFact
    (p : CM2Params)
    [hGN : Fact IntervalDomainLemma41.IntervalDomainInterpolation] :
    Lemma_4_1 intervalDomain p :=
  intervalDomainPaper2_Lemma_4_1_of_GN_frontier p hGN.out

/-- Assemble the interval-domain Lemma 3.1 and Lemma 4.1 targets from the GN
frontier.

Deprecated as a headline route for the same reason as
`intervalDomainPaper2_Lemma_4_1_of_GN_frontier`: the global
`IntervalDomainInterpolation` premise is currently refuted. -/
theorem intervalDomainPaper2_aprioriTargets_of_GN_frontier
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation) :
    IntervalDomainPaper2AprioriTargets p :=
  ⟨intervalDomainPaper2_Lemma_3_1 p,
    intervalDomainPaper2_Lemma_4_1_of_GN_frontier p hGN⟩

/-- Instance-facing assembly wrapper for interval-domain Lemma 3.1 and Lemma
4.1. -/
theorem intervalDomainPaper2_aprioriTargets_of_GN_frontierFact
    (p : CM2Params)
    [hGN : Fact IntervalDomainLemma41.IntervalDomainInterpolation] :
    IntervalDomainPaper2AprioriTargets p :=
  intervalDomainPaper2_aprioriTargets_of_GN_frontier p hGN.out

/-- Single-target interval-domain wrapper for Lemma 4.1 from the
solution-slice interpolation frontier. -/
theorem intervalDomainPaper2_Lemma_4_1_of_solutionInterpolationFrontier
    (p : CM2Params)
    (hSlice :
      IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
        p) :
    Lemma_4_1 intervalDomain p :=
  IntervalDomainTheorem11Composite.Lemma_4_1_intervalDomain_of_solution_interpolation_frontier
    p hSlice

/-- Assemble the interval-domain Lemma 3.1 and Lemma 4.1 targets from the
solution-slice interpolation frontier. -/
theorem intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
    (p : CM2Params)
    (hSlice :
      IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
        p) :
    IntervalDomainPaper2AprioriTargets p :=
  ⟨intervalDomainPaper2_Lemma_3_1 p,
    intervalDomainPaper2_Lemma_4_1_of_solutionInterpolationFrontier
      p hSlice⟩

/-- Instance-facing assembly wrapper for interval-domain Lemma 3.1 and Lemma
4.1 from the solution-slice interpolation frontier. -/
theorem intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontierFact
    (p : CM2Params)
    [hSlice : Fact
      (IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
        p)] :
    IntervalDomainPaper2AprioriTargets p :=
  intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
    p hSlice.out

/-! ## Proposition 1.1 local-existence target -/

/-- Frontier data for interval-domain Paper 2 Proposition 1.1.  The first
field is the closed local-existence branch; the second is the genuine
maximal-time finite-horizon alternative. -/
structure IntervalDomainPaper2Proposition11FrontierData
    (p : CM2Params) : Prop where
  localExistence :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  finiteHorizonAlternative :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v →
      InitialTrace intervalDomain u₀ u →
        FiniteHorizonAlternative intervalDomain Tmax u ∧
        (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)

/-- Interval-domain Paper 2 Proposition 1.1 from local existence plus the
finite-horizon alternative frontier. -/
theorem intervalDomainPaper2_Proposition_1_1_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Proposition11FrontierData p) :
    Proposition_1_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.Proposition_1_1_intervalDomain_of_localExistence_and_finiteHorizonAlternative
    p hData.localExistence hData.finiteHorizonAlternative

/-- Instance-facing interval-domain Paper 2 Proposition 1.1 wrapper. -/
theorem intervalDomainPaper2_Proposition_1_1_of_frontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Proposition11FrontierData p)] :
    Proposition_1_1 intervalDomain p :=
  intervalDomainPaper2_Proposition_1_1_of_frontierData p hData.out

/-- Thinner interval-domain Paper 2 Proposition 1.1 frontier for the proved
`χ₀ = 0` route.  Local existence is produced internally by
`intervalDomain_localExistence_chiZero_unconditional`; only the independent
finite-horizon alternative remains. -/
structure IntervalDomainPaper2Proposition11ChiZeroFrontierData
    (p : CM2Params) : Prop where
  finiteHorizonAlternative :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v →
      InitialTrace intervalDomain u₀ u →
        FiniteHorizonAlternative intervalDomain Tmax u ∧
        (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)

/-- Interval-domain Paper 2 Proposition 1.1 in the proved `χ₀ = 0` route,
with local existence discharged internally. -/
theorem intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
    (p : CM2Params)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2Proposition11ChiZeroFrontierData p) :
    Proposition_1_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.Proposition_1_1_intervalDomain_of_localExistence_and_finiteHorizonAlternative
    p
    (fun _u₀ hu₀ =>
      intervalDomain_localExistence_chiZero_unconditional
        p hχ0 ha hb hα hγ hu₀)
    hData.finiteHorizonAlternative

/-- Instance-facing interval-domain Paper 2 Proposition 1.1 wrapper for the
proved `χ₀ = 0` route. -/
theorem intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierDataFact
    (p : CM2Params)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact (IntervalDomainPaper2Proposition11ChiZeroFrontierData p)] :
    Proposition_1_1 intervalDomain p :=
  intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
    p hχ0 ha hb hα hγ hData.out

/-! ## Theorem 1.1 statement targets -/

/-- Interval-domain Paper 2 Theorem 1.1 in the proved `χ₀ = 0` regime.

This entry point consumes no half-step frontier package; the local and uniform
existence inputs are produced internally by
`intervalDomain_theorem_1_1_chiZero_unconditional`. -/
theorem intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiZero_unconditional p hχ0 ha hb hα hγ

/-- Instance-facing interval-domain Paper 2 Theorem 1.1 in the proved
`χ₀ = 0` regime. -/
theorem intervalDomainPaper2_Theorem_1_1_chiZero_unconditionalFact
    (p : CM2Params) [hχ0 : Fact (p.χ₀ = 0)] [ha : Fact (0 < p.a)]
    [hb : Fact (0 < p.b)] [hα : Fact (1 ≤ p.α)] [hγ : Fact (1 ≤ p.γ)] :
    Theorem_1_1 intervalDomain p :=
  intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
    p hχ0.out ha.out hb.out hα.out hγ.out

/-- Paper 2 Theorem 1.1 from half-step H2-source Picard data, routed through
the existing gamma >= 1 interval-domain umbrella. -/
theorem intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
        p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepH2SourceFrontierCoreLocalData_bundled
    p hχ ha hb hγ_ge_one hData

/-- Instance-facing Theorem 1.1 wrapper from half-step H2-source Picard data. -/
theorem intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierDataFact
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
        p)] :
    Theorem_1_1 intervalDomain p :=
  intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierData
    p hχ ha hb hγ_ge_one hData.out

/-- Paper 2 Theorem 1.1 from half-step logistic-source Picard data, routed
through the existing gamma >= 1 interval-domain umbrella. -/
theorem intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
        p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepLogisticSourceFrontierCoreLocalData_bundled
    p hχ ha hb hγ_ge_one hData

/-- Instance-facing Theorem 1.1 wrapper from half-step logistic-source data. -/
theorem intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierDataFact
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
        p)] :
    Theorem_1_1 intervalDomain p :=
  intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierData
    p hχ ha hb hγ_ge_one hData.out

/-! ## Theorems 1.2 and 1.3 statement targets -/

/-- Joint frontier record for the interval-domain Theorem 1.2 and Theorem 1.3
statement targets. -/
structure IntervalDomainPaper2Theorem12And13FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  theorem12 : IntervalDomainTheorem12.IntervalDomainTheorem12FrontierData p S
  theorem13 : IntervalDomainTheorem13.IntervalDomainTheorem13FrontierData p C S

/-- Shared bootstrap conclusion used by the thinner Theorem 1.2/1.3
interpolation-frontier route. -/
abbrev IntervalDomainPaper2BootstrapOutput
    (p : CM2Params) (T : ℝ)
    (u v : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∃ rho > 0,
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
      ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
        LpPowerBoundedBefore intervalDomain p0 T u

/-- Dissipation-side input for the thinner interval-domain Theorem 1.2/1.3
route. -/
abbrev IntervalDomainPaper2DissipationFrontier : Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp, p0 ≤ pExp → ∀ A B K L_const,
      (∀ t, 0 < t → t < T →
        (1 / pExp) * deriv
            (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
          A * intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤
        K * intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) + L_const) →
      ∀ t, 0 < t → t < T →
        0 ≤
          (1 / pExp) * deriv
              (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
            B * intervalDomain.integral (fun x => (u t x) ^ pExp)

/-- Positivity of the gradient-conversion coefficient in the thinner
Theorem 1.2/1.3 route. -/
abbrev IntervalDomainPaper2GradientConstantPositive
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp, p0 ≤ pExp → 0 < cGrad u T rho p0 pExp

/-- Chain-rule gradient comparison in the thinner Theorem 1.2/1.3 route. -/
abbrev IntervalDomainPaper2GradientChainFrontier
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x =>
          (u t x) ^ (pExp + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad u T rho p0 pExp * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)

/-- Mass-control input in the thinner Theorem 1.2/1.3 route. -/
abbrev IntervalDomainPaper2MassControlFrontier : Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp, p0 ≤ pExp → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
      Ceta * (intervalDomain.integral (u t)) ^ (pExp + rho) ≤ Cmass

/-- Power-integrability input in the thinner Theorem 1.2/1.3 route. -/
abbrev IntervalDomainPaper2PowerIntegrabilityFrontier : Prop :=
  ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
    AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
    LpBootstrapEnergyInequality intervalDomain u T rho p0 →
    ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
        MeasureTheory.volume 0 1

/-- PDE bridge from cross-diffusion bootstrap to the Lp energy inequality. -/
abbrev IntervalDomainPaper2EnergyFromCrossDiffusionFrontier
    (p : CM2Params) : Prop :=
  ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
      LpBootstrapEnergyInequality intervalDomain u T rho p0

/-- Per-datum interval-domain local existence input. -/
abbrev IntervalDomainPaper2LocalExistenceFrontier
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u

/-- Continuation input turning bounded finite-time solutions into global
classical solutions. -/
abbrev IntervalDomainPaper2GlobalExtensionFrontier
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
  ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
    IsPaper2ClassicalSolution intervalDomain p Tmax u v →
    InitialTrace intervalDomain u₀ u →
      IsPaper2BoundedBefore intervalDomain Tmax u →
        1 ≤ p.m →
          IsPaper2GlobalClassicalSolution intervalDomain p u v

/-- Common interpolation/energy inputs shared by the thinner interval-domain
Theorem 1.2 and Theorem 1.3 route.

Legacy/no-go headline interface: the `interpolation` field is the global
`IntervalDomainInterpolation` premise, refuted as literally stated by
`IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.
Prefer `IntervalDomainPaper2SolutionInterpolationEnergyFrontierData` or the
positive solution-slice variant for current headline routes. -/
structure IntervalDomainPaper2InterpolationEnergyFrontierData
    (p : CM2Params)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  dissipation : IntervalDomainPaper2DissipationFrontier
  gradConstantPositive :
    IntervalDomainPaper2GradientConstantPositive cGrad
  gradientChain : IntervalDomainPaper2GradientChainFrontier cGrad
  massControl : IntervalDomainPaper2MassControlFrontier
  powerIntegrability : IntervalDomainPaper2PowerIntegrabilityFrontier
  energyFromCrossDiffusion :
    IntervalDomainPaper2EnergyFromCrossDiffusionFrontier p

/-- Common solution-slice interpolation/energy inputs shared by the thinner
interval-domain Theorem 1.2 and Theorem 1.3 route.

This is weaker than `IntervalDomainPaper2InterpolationEnergyFrontierData` in
the important soundness direction: it does not assume the false global
`IntervalDomainInterpolation` statement for arbitrary positive functions.
Instead, it assumes the mass-gradient interpolation estimate only for
classical solution slices. -/
structure IntervalDomainPaper2SolutionInterpolationEnergyFrontierData
    (p : CM2Params)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  solutionInterpolation :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionInterpolation
      p
  dissipation : IntervalDomainPaper2DissipationFrontier
  gradConstantPositive :
    IntervalDomainPaper2GradientConstantPositive cGrad
  gradientChain : IntervalDomainPaper2GradientChainFrontier cGrad
  massControl : IntervalDomainPaper2MassControlFrontier
  powerIntegrability : IntervalDomainPaper2PowerIntegrabilityFrontier
  energyFromCrossDiffusion :
    IntervalDomainPaper2EnergyFromCrossDiffusionFrontier p

/-- Positive-constant version of the solution-slice interpolation/energy
frontier.  This single package can feed both Lemma 4.1 and Corollary 2.1. -/
structure IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
    (p : CM2Params)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  solutionInterpolation :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      p
  dissipation : IntervalDomainPaper2DissipationFrontier
  gradConstantPositive :
    IntervalDomainPaper2GradientConstantPositive cGrad
  gradientChain : IntervalDomainPaper2GradientChainFrontier cGrad
  massControl : IntervalDomainPaper2MassControlFrontier
  powerIntegrability : IntervalDomainPaper2PowerIntegrabilityFrontier
  energyFromCrossDiffusion :
    IntervalDomainPaper2EnergyFromCrossDiffusionFrontier p

/-- Drop the positive-constant field when only Corollary 2.1 is being
assembled. -/
def IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData.toSolution
    {p : CM2Params}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
        p cGrad) :
    IntervalDomainPaper2SolutionInterpolationEnergyFrontierData p cGrad where
  solutionInterpolation :=
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionInterpolation_of_positive
      p h.solutionInterpolation
  dissipation := h.dissipation
  gradConstantPositive := h.gradConstantPositive
  gradientChain := h.gradientChain
  massControl := h.massControl
  powerIntegrability := h.powerIntegrability
  energyFromCrossDiffusion := h.energyFromCrossDiffusion

/-- Thinner joint frontier for interval-domain Theorems 1.2 and 1.3.

Compared with `IntervalDomainPaper2Theorem12And13FrontierData`, this route no
longer carries `SemigroupEstimateData`, Lemma 2.1, Lemma 2.6, Lemma 4.1, or
Corollary 2.1 as theorem fields.  It exposes the interpolation/energy/positivity
route used by the existing Theorem 1.2/1.3 assemblies and replaces global
boundedness fields by eventual sup-norm frontiers.

Because the nested common data includes the false global
`IntervalDomainInterpolation` premise, prefer the solution-slice or positive
solution-slice routes below for current headline accounting. -/
structure IntervalDomainPaper2Theorem12And13InterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  common : IntervalDomainPaper2InterpolationEnergyFrontierData p cGrad
  prop25 : Proposition_2_5 intervalDomain p
  localExistence : IntervalDomainPaper2LocalExistenceFrontier p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Joint frontier for interval-domain Theorems 1.2 and 1.3 using only the
solution-slice interpolation input for the Corollary 2.1 step.

This is the preferred headline route over
`IntervalDomainPaper2Theorem12And13InterpolationFrontierData`: it avoids the
globally quantified interpolation premise that is refuted by the step-function
counterexample. -/
structure IntervalDomainPaper2Theorem12And13SolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  common : IntervalDomainPaper2SolutionInterpolationEnergyFrontierData p cGrad
  prop25 : Proposition_2_5 intervalDomain p
  localExistence : IntervalDomainPaper2LocalExistenceFrontier p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Positive-constant solution-slice version of the Theorem 1.2/1.3
frontier.  This is the version suitable for full statement-target assembly
because its common interpolation field also proves Lemma 4.1. -/
structure
    IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  common :
    IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
  prop25 : Proposition_2_5 intervalDomain p
  localExistence : IntervalDomainPaper2LocalExistenceFrontier p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Forget the positive constant when assembling only Theorems 1.2 and 1.3. -/
def
    IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData.toSolution
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2Theorem12And13SolutionInterpolationFrontierData
      p C cGrad where
  common := h.common.toSolution
  prop25 := h.prop25
  localExistence := h.localExistence
  globalExtension := h.globalExtension
  slowBootstrap := h.slowBootstrap
  criticalBootstrap := h.criticalBootstrap
  criticalEventualSupBound := h.criticalEventualSupBound
  strongBootstrap := h.strongBootstrap
  strongEventualSupBound := h.strongEventualSupBound

/-- `χ₀ = 0` version of the positive solution-slice Theorem 1.2/1.3
frontier with local existence discharged by the proved interval-domain
local-existence producer. -/
structure
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  common :
    IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
  prop25 : Proposition_2_5 intervalDomain p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Fill the local-existence slot of the local-free `χ₀ = 0` positive
solution-slice frontier using `intervalDomain_localExistence_chiZero_unconditional`. -/
def
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData.toPositive
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
        p C cGrad)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
      p C cGrad where
  common := h.common
  prop25 := h.prop25
  localExistence := by
    intro u₀ hu₀
    exact intervalDomain_localExistence_chiZero_unconditional
      p hχ0 ha hb hα hγ hu₀
  globalExtension := h.globalExtension
  slowBootstrap := h.slowBootstrap
  criticalBootstrap := h.criticalBootstrap
  criticalEventualSupBound := h.criticalEventualSupBound
  strongBootstrap := h.strongBootstrap
  strongEventualSupBound := h.strongEventualSupBound

/-- Actual-atom version of the preferred `χ₀ = 0` local-free positive
solution-slice Theorem 1.2/1.3 frontier.  It replaces the direct
`Proposition_2_5 intervalDomain p` field by the smaller actual-atom frontier. -/
structure
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  common :
    IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
  prop25Actual : IntervalDomainPaper2Prop25ActualAtomFrontierData p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Convert the actual-atom local-free frontier to the existing local-free
frontier by producing Proposition 2.5 internally. -/
def
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData.toLocalFree
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad where
  common := h.common
  prop25 :=
    intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
      p h.prop25Actual
  globalExtension := h.globalExtension
  slowBootstrap := h.slowBootstrap
  criticalBootstrap := h.criticalBootstrap
  criticalEventualSupBound := h.criticalEventualSupBound
  strongBootstrap := h.strongBootstrap
  strongEventualSupBound := h.strongEventualSupBound

/-- Common-free actual-atom frontier for interval-domain Theorems 1.2 and 1.3
in the proved `χ₀ = 0` local-free route.

Compared with the positive solution-slice local-free route, this removes
`IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData` and the
`cGrad` parameter from the main-theorem path.  Both `Corollary_2_1` and
`Proposition_2_5` are produced from `prop25Actual`. -/
structure
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  prop25Actual : IntervalDomainPaper2Prop25ActualAtomFrontierData p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Common-free actual-atom frontier for Theorems 1.2 and 1.3 with the
relative-Moser atom reduced to mass-gradient data. -/
structure
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  prop25MassGradient :
    IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Convert the mass-gradient common-free route to the actual-atom common-free
route. -/
def
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomMassGradientCor21LocalFreeFrontierData.toActualAtomCor21
    {p : CM2Params} {C : Paper2Constants p}
    (h :
      IntervalDomainPaper2Theorem12And13ChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
        p C) :
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
      p C where
  prop25Actual := h.prop25MassGradient.toActualAtoms
  globalExtension := h.globalExtension
  slowBootstrap := h.slowBootstrap
  criticalBootstrap := h.criticalBootstrap
  criticalEventualSupBound := h.criticalEventualSupBound
  strongBootstrap := h.strongBootstrap
  strongEventualSupBound := h.strongEventualSupBound

/-- Assemble the interval-domain Theorem 1.2 and Theorem 1.3 statement targets
from their existing frontier-data records. -/
theorem intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hData : IntervalDomainPaper2Theorem12And13FrontierData p C S) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  ⟨IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_frontierData
      p S hData.theorem12,
    IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_frontierData
      p C S hData.theorem13⟩

/-- Instance-facing joint wrapper for interval-domain Theorems 1.2 and 1.3. -/
theorem intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    [hData : Fact (IntervalDomainPaper2Theorem12And13FrontierData p C S)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
    p C S hData.out

/-- Assemble the interval-domain Theorem 1.2 and Theorem 1.3 statement targets
from the thinner interpolation/energy/positivity frontiers. -/
theorem intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13InterpolationFrontierData p C cGrad) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  ⟨IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_interpolation_frontier_solution_positivity
      p hData.common.interpolation cGrad
      hData.common.dissipation hData.common.gradConstantPositive
      hData.common.gradientChain hData.common.massControl
      hData.common.powerIntegrability
      hData.common.energyFromCrossDiffusion hData.prop25
      hData.localExistence hData.globalExtension
      hData.slowBootstrap hData.criticalBootstrap
      hData.criticalEventualSupBound,
    IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_interpolation_frontier_solution_positivity
      p C hData.common.interpolation cGrad
      hData.common.dissipation hData.common.gradConstantPositive
      hData.common.gradientChain hData.common.massControl
      hData.common.powerIntegrability
      hData.common.energyFromCrossDiffusion hData.prop25
      hData.localExistence hData.globalExtension
      hData.strongBootstrap hData.strongEventualSupBound⟩

/-- Instance-facing joint wrapper for interval-domain Theorems 1.2 and 1.3
from the thinner interpolation frontiers. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    [hData :
      Fact
        (IntervalDomainPaper2Theorem12And13InterpolationFrontierData
          p C cGrad)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
    p C cGrad hData.out

/-- Assemble the interval-domain Theorem 1.2 and Theorem 1.3 headline targets
from the solution-slice interpolation/energy frontiers. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13SolutionInterpolationFrontierData
        p C cGrad) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_solution_interpolation_frontier
      p hData.common.solutionInterpolation cGrad
      hData.common.dissipation hData.common.gradConstantPositive
      hData.common.gradientChain hData.common.massControl
      hData.common.powerIntegrability
      hData.common.energyFromCrossDiffusion
  exact
    ⟨IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_parameter_fields_and_eventual_sup_bound
        p hCor21 hData.prop25
        hData.localExistence hData.globalExtension
        hData.slowBootstrap hData.criticalBootstrap
        hData.criticalEventualSupBound,
      IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
        p C hCor21 hData.prop25
        hData.localExistence hData.globalExtension
        hData.strongBootstrap hData.strongEventualSupBound⟩

/-- Instance-facing joint wrapper for interval-domain Theorems 1.2 and 1.3
from the solution-slice interpolation frontiers. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    [hData :
      Fact
        (IntervalDomainPaper2Theorem12And13SolutionInterpolationFrontierData
          p C cGrad)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData
    p C cGrad hData.out

/-- Assemble the interval-domain Theorem 1.2 and Theorem 1.3 headline targets
from the positive-constant solution-slice interpolation/energy frontiers. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
        p C cGrad) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData
    p C cGrad hData.toSolution

/-- Assemble interval-domain Theorems 1.2 and 1.3 in the `χ₀ = 0` regime from
the positive solution-slice route with local existence produced internally. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
        p C cGrad) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
    p C cGrad (hData.toPositive hχ0 ha hb hα hγ)

/-- Assemble interval-domain Theorems 1.2 and 1.3 in the `χ₀ = 0` regime from
the local-free positive solution-slice route with Proposition 2.5 produced by
the actual Moser atoms. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.toLocalFree

/-- Instance-facing wrapper for interval-domain Theorems 1.2 and 1.3 in the
actual-atom local-free `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
          p C cGrad)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Theorems 1.2 and 1.3 in the `χ₀ = 0` regime from
the common-free actual-atom route. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
        p C) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C := by
  have hTier :
      Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p :=
    intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_actualAtomFrontierData
      p hData.prop25Actual
  let hlocal : IntervalDomainPaper2LocalExistenceFrontier p :=
    fun u₀ hu₀ =>
      intervalDomain_localExistence_chiZero_unconditional
        p hχ0 ha hb hα hγ hu₀
  exact
    ⟨IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_parameter_fields_and_eventual_sup_bound
        p hTier.1 hTier.2 hlocal hData.globalExtension
        hData.slowBootstrap hData.criticalBootstrap
        hData.criticalEventualSupBound,
      IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
        p C hTier.1 hTier.2 hlocal hData.globalExtension
        hData.strongBootstrap hData.strongEventualSupBound⟩

/-- Instance-facing wrapper for interval-domain Theorems 1.2 and 1.3 in the
common-free actual-atom `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomCor21LocalFreeFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
          p C)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Theorems 1.2 and 1.3 in the `χ₀ = 0` regime from
the common-free actual-atom route, with the relative-Moser atom reduced to
mass-gradient data. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2Theorem12And13ChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
        p C) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData.toActualAtomCor21

/-- Instance-facing wrapper for interval-domain Theorems 1.2 and 1.3 in the
common-free mass-gradient actual-atom `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomMassGradientCor21LocalFreeFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2Theorem12And13ChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
          p C)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData.out

/-- Instance-facing joint wrapper for interval-domain Theorems 1.2 and 1.3
from the positive-constant solution-slice interpolation frontiers. -/
theorem
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    [hData :
      Fact
        (IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
          p C cGrad)] :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
    p C cGrad hData.out

/-- Assemble the section-2 Corollary 2.1/bootstrap target bundle with
Corollary 2.1 produced from the positive solution-slice interpolation common
frontier.  The only remaining section-2 input is the bootstrap/estimate branch
data needed for Lemma 2.7 and Propositions 2.2--2.5. -/
theorem
    intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
        p C cGrad)
    (hBootstrap : Paper2BootstrapEstimateBranchData intervalDomain p) :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  ⟨IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_solution_interpolation_frontier
      p
      (IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionInterpolation_of_positive
        p hData.common.solutionInterpolation)
      cGrad hData.common.dissipation hData.common.gradConstantPositive
      hData.common.gradientChain hData.common.massControl
      hData.common.powerIntegrability
      hData.common.energyFromCrossDiffusion,
    intervalDomainPaper2_bootstrapEstimateTargets_of_branchData
      p hBootstrap⟩

/-- Instance-facing section-2 Corollary 2.1/bootstrap wrapper from the
positive solution-slice interpolation common frontier. -/
theorem
    intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    [hData : Fact
      (IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
        p C cGrad)]
    [hBootstrap : Fact (Paper2BootstrapEstimateBranchData intervalDomain p)] :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationFrontierData
    p C cGrad hData.out hBootstrap.out

/-- Assemble the section-2 Corollary 2.1/bootstrap bundle from the positive
solution-slice common frontier and the thinner section-2 branch data. -/
theorem
    intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
        p C cGrad)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p) :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  ⟨IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_solution_interpolation_frontier
      p
      (IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionInterpolation_of_positive
        p hData.common.solutionInterpolation)
      cGrad hData.common.dissipation hData.common.gradConstantPositive
      hData.common.gradientChain hData.common.massControl
      hData.common.powerIntegrability
      hData.common.energyFromCrossDiffusion,
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
      p hThin hData.prop25⟩

/-- Instance-facing section-2 wrapper from positive solution-slice common data
and thinner branch data. -/
theorem
    intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    [hData : Fact
      (IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
        p C cGrad)]
    [hThin : Fact (IntervalDomainPaper2BootstrapEstimateThinFrontierData p)] :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierData
    p C cGrad hData.out hThin.out

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.2. -/
theorem intervalDomainPaper2_Theorem_1_2_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hData : IntervalDomainPaper2Theorem12And13FrontierData p C S) :
    Theorem_1_2 intervalDomain p :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
    p C S hData).1

/-- Instance-facing interval-domain wrapper for Paper2 Theorem 1.2. -/
theorem intervalDomainPaper2_Theorem_1_2_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    [hData : Fact (IntervalDomainPaper2Theorem12And13FrontierData p C S)] :
    Theorem_1_2 intervalDomain p :=
  intervalDomainPaper2_Theorem_1_2_of_frontierData
    p C S hData.out

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.3. -/
theorem intervalDomainPaper2_Theorem_1_3_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hData : IntervalDomainPaper2Theorem12And13FrontierData p C S) :
    Theorem_1_3 intervalDomain p C :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
    p C S hData).2

/-- Instance-facing interval-domain wrapper for Paper2 Theorem 1.3. -/
theorem intervalDomainPaper2_Theorem_1_3_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    [hData : Fact (IntervalDomainPaper2Theorem12And13FrontierData p C S)] :
    Theorem_1_3 intervalDomain p C :=
  intervalDomainPaper2_Theorem_1_3_of_frontierData
    p C S hData.out

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.2 from the
thinner interpolation frontiers. -/
theorem intervalDomainPaper2_Theorem_1_2_of_interpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13InterpolationFrontierData p C cGrad) :
    Theorem_1_2 intervalDomain p :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
    p C cGrad hData).1

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.3 from the
thinner interpolation frontiers. -/
theorem intervalDomainPaper2_Theorem_1_3_of_interpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13InterpolationFrontierData p C cGrad) :
    Theorem_1_3 intervalDomain p C :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
    p C cGrad hData).2

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.2 from the
solution-slice interpolation frontiers. -/
theorem intervalDomainPaper2_Theorem_1_2_of_solutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13SolutionInterpolationFrontierData
        p C cGrad) :
    Theorem_1_2 intervalDomain p :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData
    p C cGrad hData).1

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.3 from the
solution-slice interpolation frontiers. -/
theorem intervalDomainPaper2_Theorem_1_3_of_solutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13SolutionInterpolationFrontierData
        p C cGrad) :
    Theorem_1_3 intervalDomain p C :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData
    p C cGrad hData).2

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.2 from the
positive-constant solution-slice interpolation frontiers. -/
theorem intervalDomainPaper2_Theorem_1_2_of_positiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
        p C cGrad) :
    Theorem_1_2 intervalDomain p :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
    p C cGrad hData).1

/-- Single-target interval-domain wrapper for Paper2 Theorem 1.3 from the
positive-constant solution-slice interpolation frontiers. -/
theorem intervalDomainPaper2_Theorem_1_3_of_positiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hData :
      IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
        p C cGrad) :
    Theorem_1_3 intervalDomain p C :=
  (intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
    p C cGrad hData).2

/-! ## Main theorem bundles -/

/-- Concrete interval-domain Paper 2 main theorem targets. -/
def IntervalDomainPaper2MainTheoremTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Theorem_1_1 intervalDomain p ∧
    Theorem_1_2 intervalDomain p ∧
      Theorem_1_3 intervalDomain p C

/-- Main-theorem frontier record for the `χ₀ = 0` route.  Theorem 1.1 is
proved internally; only the independent Theorem 1.2/1.3 frontier remains. -/
structure IntervalDomainPaper2MainTheoremChiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13FrontierData p C S

/-- Main-theorem frontier record for the proved `χ₀ = 0` route using the
thinner interpolation-frontier Theorem 1.2/1.3 assembly.  This route carries
no `SemigroupEstimateData` package. -/
structure IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13InterpolationFrontierData p C cGrad

/-- Main-theorem frontier record for the proved `χ₀ = 0` route using the
solution-slice interpolation Theorem 1.2/1.3 assembly. -/
structure IntervalDomainPaper2MainTheoremChiZeroSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13SolutionInterpolationFrontierData
      p C cGrad

/-- Main-theorem frontier record for the proved `χ₀ = 0` route using the
positive-constant solution-slice interpolation Theorem 1.2/1.3 assembly. -/
structure
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Main-theorem frontier record for the proved `χ₀ = 0` route using the
positive solution-slice Theorem 1.2/1.3 assembly with local existence produced
internally. -/
structure
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad

/-- Main-theorem frontier record for the proved `χ₀ = 0` route using the
actual-atom local-free positive solution-slice Theorem 1.2/1.3 assembly. -/
structure
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
      p C cGrad

/-- Main-theorem frontier record for the proved `χ₀ = 0` route using the
common-free actual-atom Theorem 1.2/1.3 assembly. -/
structure
    IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
      p C

/-- Main-theorem frontier record for the proved `χ₀ = 0` route using the
common-free actual-atom Theorem 1.2/1.3 assembly, with relative Moser reduced
to mass-gradient data. -/
structure
    IntervalDomainPaper2MainTheoremChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
      p C

/-- Convert the mass-gradient common-free main-theorem route to the actual-atom
common-free main-theorem route. -/
def
    IntervalDomainPaper2MainTheoremChiZeroActualAtomMassGradientCor21LocalFreeFrontierData.toActualAtomCor21
    {p : CM2Params} {C : Paper2Constants p}
    (h :
      IntervalDomainPaper2MainTheoremChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
        p C) :
    IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
      p C where
  theorem12And13 := h.theorem12And13.toActualAtomCor21

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 in the proved `χ₀ = 0`
route.  Compared with the H2/logistic-source routes, this carries no Theorem
1.1 local-existence frontier package. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2MainTheoremChiZeroFrontierData p C S) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
      p C S hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle in the proved
`χ₀ = 0` route. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact (IntervalDomainPaper2MainTheoremChiZeroFrontierData p C S)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 in the proved `χ₀ = 0`
route, with Theorems 1.2/1.3 supplied by the thinner interpolation-frontier
assembly. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
      p C cGrad hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle in the proved
`χ₀ = 0` route using the thinner interpolation-frontier Theorem 1.2/1.3
assembly. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 in the proved
`χ₀ = 0` route, with Theorems 1.2/1.3 supplied by the solution-slice
interpolation-frontier assembly. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData
      p C cGrad hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle in the proved
`χ₀ = 0` route using the solution-slice interpolation-frontier Theorem 1.2/1.3
assembly. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremChiZeroSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroSolutionInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 in the proved
`χ₀ = 0` route, with Theorems 1.2/1.3 supplied by the positive-constant
solution-slice interpolation-frontier assembly. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
      p C cGrad hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle in the proved
`χ₀ = 0` route using the positive-constant solution-slice interpolation
frontier. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 in the proved
`χ₀ = 0` route, with both Theorem 1.1 and the Theorem 1.2/1.3 local-existence
slot discharged by the proved local-existence producer. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.theorem12And13⟩

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 in the proved
`χ₀ = 0` route, with Proposition 2.5 produced from the actual Moser atoms. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.theorem12And13⟩

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 from the common-free
actual-atom Theorem 1.2/1.3 route. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomCor21LocalFreeFrontierData
      p C hχ0 ha hb hα hγ hData.theorem12And13⟩

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 from the common-free
mass-gradient actual-atom Theorem 1.2/1.3 route. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData.toActualAtomCor21

/-- Instance-facing interval-domain main-theorem bundle for the local-free
positive solution-slice `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
        p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Instance-facing interval-domain main-theorem bundle for the actual-atom
local-free positive solution-slice `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Instance-facing interval-domain main-theorem bundle for the common-free
actual-atom `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomCor21LocalFreeFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
        p C)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData.out

/-- Instance-facing interval-domain main-theorem bundle for the common-free
mass-gradient actual-atom `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomMassGradientCor21LocalFreeFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
        p C)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData.out

/-- Main-theorem frontier record using the half-step H2-source Theorem 1.1
route. -/
structure IntervalDomainPaper2MainTheoremH2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  theorem11 :
    IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
      p
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13FrontierData p C S

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 from the H2-source
local-existence route plus the existing Theorem 1.2/1.3 frontiers. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_H2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremH2SourceFrontierData p C S) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierData
      p hχ ha hb hγ_ge_one hData.theorem11,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
      p C S hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle from the H2-source
route. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_H2SourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremH2SourceFrontierData p C S)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_H2SourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Main-theorem frontier record using the half-step H2-source Theorem 1.1
route and the positive-constant solution-slice Theorem 1.2/1.3 route. -/
structure
    IntervalDomainPaper2MainTheoremH2SourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem11 :
    IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
      p
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 from the H2-source
local-existence route plus the positive-constant solution-slice Theorem
1.2/1.3 frontiers. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremH2SourcePositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_of_halfStepH2SourceFrontierData
      p hχ ha hb hγ_ge_one hData.theorem11,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
      p C cGrad hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle from the H2-source
route plus the positive-constant solution-slice Theorem 1.2/1.3 route. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremH2SourcePositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-- Main-theorem frontier record using the half-step logistic-source Theorem
1.1 route. -/
structure IntervalDomainPaper2MainTheoremLogisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  theorem11 :
    IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
      p
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13FrontierData p C S

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 from the
logistic-source local-existence route plus the existing Theorem 1.2/1.3
frontiers. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_logisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremLogisticSourceFrontierData p C S) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierData
      p hχ ha hb hγ_ge_one hData.theorem11,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_frontierData
      p C S hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle from the
logistic-source route. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_logisticSourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremLogisticSourceFrontierData p C S)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_logisticSourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Main-theorem frontier record using the half-step logistic-source Theorem
1.1 route and the positive-constant solution-slice Theorem 1.2/1.3 route. -/
structure
    IntervalDomainPaper2MainTheoremLogisticSourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem11 :
    IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
      p
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13PositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Assemble interval-domain Paper 2 Theorems 1.1--1.3 from the logistic-source
local-existence route plus the positive-constant solution-slice Theorem
1.2/1.3 frontiers. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremLogisticSourcePositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_of_halfStepLogisticSourceFrontierData
      p hχ ha hb hγ_ge_one hData.theorem11,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
      p C cGrad hData.theorem12And13⟩

/-- Instance-facing interval-domain main-theorem bundle from the logistic-source
route plus the positive-constant solution-slice Theorem 1.2/1.3 route. -/
theorem
    intervalDomainPaper2_mainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2MainTheoremLogisticSourcePositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-- Concrete interval-domain Paper 2 Proposition 1.1 together with the main
Theorems 1.1--1.3. -/
def IntervalDomainPaper2LocalAndMainTheoremTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Proposition_1_1 intervalDomain p ∧
    IntervalDomainPaper2MainTheoremTargets p C

/-- Local-plus-main frontier record for the proved `χ₀ = 0` Theorem 1.1
route. -/
structure IntervalDomainPaper2LocalAndMainChiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  proposition11 : IntervalDomainPaper2Proposition11FrontierData p
  main : IntervalDomainPaper2MainTheoremChiZeroFrontierData p C S

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
with Theorem 1.1 supplied by the proved `χ₀ = 0` route. -/
theorem intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2LocalAndMainChiZeroFrontierData p C S) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_frontierData
      p hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
      p C S hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper for the proved
`χ₀ = 0` Theorem 1.1 route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroFrontierData p C S)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Thinner local-plus-main frontier record for the proved `χ₀ = 0` route.
The Proposition 1.1 local-existence field is produced internally, so the local
side only carries the finite-horizon alternative. -/
structure IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  main : IntervalDomainPaper2MainTheoremChiZeroFrontierData p C S

/-- Local-plus-main frontier record for the proved `χ₀ = 0` route using the
thinner interpolation-frontier Theorem 1.2/1.3 assembly.  The Proposition 1.1
local-existence field is produced internally, and the main theorem route
carries no `SemigroupEstimateData`. -/
structure IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  main : IntervalDomainPaper2MainTheoremChiZeroInterpolationFrontierData
    p C cGrad

/-- Local-plus-main frontier record for the proved `χ₀ = 0` route using the
solution-slice interpolation-frontier Theorem 1.2/1.3 assembly. -/
structure
    IntervalDomainPaper2LocalAndMainChiZeroSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  main :
    IntervalDomainPaper2MainTheoremChiZeroSolutionInterpolationFrontierData
      p C cGrad

/-- Local-plus-main frontier record for the proved `χ₀ = 0` route using the
positive-constant solution-slice interpolation-frontier Theorem 1.2/1.3
assembly. -/
structure
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  main :
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Local-plus-main frontier record for the proved `χ₀ = 0` route using the
positive solution-slice Theorem 1.2/1.3 route with local existence produced
internally. -/
structure
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  main :
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
in the proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData p C S) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
      p hχ0 ha hb hα hγ hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
      p C S hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper for the thinner
proved `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData p C S)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
in the proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally and Theorems 1.2/1.3 routed through the thinner interpolation
frontiers. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
      p hχ0 ha hb hα hγ hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper for the proved
`χ₀ = 0` route using the thinner interpolation-frontier Theorem 1.2/1.3
assembly. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
in the proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally and Theorems 1.2/1.3 routed through the solution-slice
interpolation frontiers. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainChiZeroSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
      p hχ0 ha hb hα hγ hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroSolutionInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper for the proved
`χ₀ = 0` route using the solution-slice interpolation-frontier Theorem 1.2/1.3
assembly. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroSolutionInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
in the proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally and Theorems 1.2/1.3 routed through the positive-constant
solution-slice interpolation frontiers. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
      p hχ0 ha hb hα hγ hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper for the proved
`χ₀ = 0` route using the positive-constant solution-slice interpolation
frontiers. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
in the proved `χ₀ = 0` route, with all local-existence uses in this bundle
discharged internally. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
        p C cGrad) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
      p hχ0 ha hb hα hγ hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.main⟩

/-- Instance-facing local-plus-main wrapper for the local-free positive
solution-slice `χ₀ = 0` route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
        p C cGrad)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Local-plus-main frontier record using the half-step H2-source Theorem 1.1
route. -/
structure IntervalDomainPaper2LocalAndMainH2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  proposition11 : IntervalDomainPaper2Proposition11FrontierData p
  main : IntervalDomainPaper2MainTheoremH2SourceFrontierData p C S

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
from the H2-source local-existence route. -/
theorem intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainH2SourceFrontierData p C S) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_frontierData
      p hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_H2SourceFrontierData
      p C S hχ ha hb hγ_ge_one hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper from the H2-source
route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainH2SourceFrontierData p C S)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Local-plus-main frontier record using the half-step H2-source Theorem 1.1
route and the positive-constant solution-slice Theorem 1.2/1.3 route. -/
structure
    IntervalDomainPaper2LocalAndMainH2SourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  proposition11 : IntervalDomainPaper2Proposition11FrontierData p
  main :
    IntervalDomainPaper2MainTheoremH2SourcePositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
from the H2-source local-existence route plus the positive-constant
solution-slice Theorem 1.2/1.3 route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainH2SourcePositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_frontierData
      p hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
      p C cGrad hχ ha hb hγ_ge_one hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper from the H2-source
route plus the positive-constant solution-slice Theorem 1.2/1.3 route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainH2SourcePositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-- Local-plus-main frontier record using the half-step logistic-source
Theorem 1.1 route. -/
structure IntervalDomainPaper2LocalAndMainLogisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  proposition11 : IntervalDomainPaper2Proposition11FrontierData p
  main : IntervalDomainPaper2MainTheoremLogisticSourceFrontierData p C S

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
from the logistic-source local-existence route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainLogisticSourceFrontierData p C S) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_frontierData
      p hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_logisticSourceFrontierData
      p C S hχ ha hb hγ_ge_one hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper from the
logistic-source route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainLogisticSourceFrontierData p C S)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Local-plus-main frontier record using the half-step logistic-source
Theorem 1.1 route and the positive-constant solution-slice Theorem 1.2/1.3
route. -/
structure
    IntervalDomainPaper2LocalAndMainLogisticSourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  proposition11 : IntervalDomainPaper2Proposition11FrontierData p
  main :
    IntervalDomainPaper2MainTheoremLogisticSourcePositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Assemble interval-domain Paper 2 Proposition 1.1 and Theorems 1.1--1.3
from the logistic-source local-existence route plus the positive-constant
solution-slice Theorem 1.2/1.3 route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2LocalAndMainLogisticSourcePositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Proposition_1_1_of_frontierData
      p hData.proposition11,
    intervalDomainPaper2_mainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
      p C cGrad hχ ha hb hγ_ge_one hData.main⟩

/-- Instance-facing interval-domain local-plus-main wrapper from the
logistic-source route plus the positive-constant solution-slice Theorem
1.2/1.3 route. -/
theorem
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2LocalAndMainLogisticSourcePositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2LocalAndMainTheoremTargets p C :=
  intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-! ## Combined interval-domain statement targets -/

/-- Concrete interval-domain Paper 2 statement targets assembled from the
section-2 bootstrap/corollary package, the section-3/4 a priori package, and
the local-plus-main theorem package. -/
def IntervalDomainPaper2StatementTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2Corollary21BootstrapTargets p ∧
    IntervalDomainPaper2AprioriTargets p ∧
      IntervalDomainPaper2LocalAndMainTheoremTargets p C

/-- Interval-domain Paper 2 statement-frontier record for the proved
`χ₀ = 0` Theorem 1.1 route. -/
structure IntervalDomainPaper2StatementChiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain : IntervalDomainPaper2LocalAndMainChiZeroFrontierData p C S

/-- Assemble the concrete interval-domain Paper 2 statement targets with
Theorem 1.1 supplied by the proved `χ₀ = 0` route. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2StatementChiZeroFrontierData p C S) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroFrontierData
      p C S hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
proved `χ₀ = 0` Theorem 1.1 route. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact (IntervalDomainPaper2StatementChiZeroFrontierData p C S)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Thinner interval-domain Paper 2 statement-frontier record for the proved
`χ₀ = 0` route.  The Proposition 1.1 local-existence field is produced from
`intervalDomain_localExistence_chiZero_unconditional`. -/
structure IntervalDomainPaper2StatementChiZeroThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroThinFrontierData p C S

/-- Thinner interval-domain Paper 2 statement-frontier record for the proved
`χ₀ = 0` route using the interpolation-frontier Theorem 1.2/1.3 assembly.
This removes the statement-level `SemigroupEstimateData` package from the
main theorem component. -/
structure IntervalDomainPaper2StatementChiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroInterpolationFrontierData
      p C cGrad

/-- Statement-frontier record for the proved `χ₀ = 0` route using the
positive-constant solution-slice interpolation Theorem 1.2/1.3 assembly.

Unlike `IntervalDomainPaper2StatementChiZeroInterpolationFrontierData`, this
record does not contain the false global `IntervalDomainInterpolation`
premise.  The nested positive solution-slice interpolation field proves both
Lemma 4.1 and the Corollary 2.1 route used by Theorems 1.2/1.3. -/
structure
    IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Thinner statement-frontier record for the proved `χ₀ = 0` route using the
positive solution-slice interpolation assembly.  Unlike
`IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationFrontierData`,
this record does not carry the Corollary 2.1 energy frontier separately:
Corollary 2.1 is produced from the nested positive solution-slice common data,
while the section-2 branch data supplies Lemma 2.7 and Propositions 2.2--2.5. -/
structure
    IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationBootstrapFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  bootstrap : Paper2BootstrapEstimateBranchData intervalDomain p
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Thinnest current `χ₀ = 0` positive solution-slice statement route for the
section-2 component.  The section-2 input omits Proposition 2.4 and Proposition
2.5; those are supplied by the interval-domain mass proof and the nested
Theorem 1.2/1.3 data. -/
structure
    IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Local-existence-free variant of the thinnest current `χ₀ = 0` positive
solution-slice statement route.  The section-2 input remains thin, and the
Theorem 1.2/1.3 local-existence field is supplied by the proved `χ₀ = 0`
local-existence producer. -/
structure
    IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad

/-- Assemble the concrete interval-domain Paper 2 statement targets in the
proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2StatementChiZeroThinFrontierData p C S) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierData
      p C S hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
thinner proved `χ₀ = 0` route. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroThinFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact (IntervalDomainPaper2StatementChiZeroThinFrontierData p C S)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroThinFrontierData
    p C S hχ0 ha hb hα hγ hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets in the
proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally and Theorems 1.2/1.3 routed through the thinner interpolation
frontiers. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroInterpolationFrontierData p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
proved `χ₀ = 0` route using the thinner interpolation-frontier Theorem 1.2/1.3
assembly. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2StatementChiZeroInterpolationFrontierData
          p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets in the
proved `χ₀ = 0` route, with Proposition 1.1 local existence discharged
internally and all uses of the false global interpolation frontier removed
from this route. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
proved `χ₀ = 0` route using positive-constant solution-slice interpolation. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets in the
proved `χ₀ = 0` route from the positive solution-slice route, with Corollary
2.1 derived from the nested common data instead of carried separately. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationBootstrapFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationBootstrapFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationFrontierData
      p C cGrad hData.localAndMain.main.theorem12And13 hData.bootstrap,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
proved `χ₀ = 0` route from the thinner positive solution-slice/bootstrap data. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationBootstrapFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationBootstrapFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationBootstrapFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets in the
proved `χ₀ = 0` route from the positive solution-slice route and thin
section-2 data. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierData
      p C cGrad hData.localAndMain.main.theorem12And13 hData.section2,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for the
proved `χ₀ = 0` route from positive solution-slice and thin section-2 data. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets in the
proved `χ₀ = 0` route from positive solution-slice and thin section-2 data,
with the Theorem 1.2/1.3 local-existence field produced internally.

This is the preferred current interval-domain `χ₀ = 0` statement route: it uses
solution-slice interpolation and the local-free Theorem 1.2/1.3 interface,
rather than the deprecated global `IntervalDomainInterpolation` premise
refuted by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierData
      p C cGrad
      (hData.localAndMain.main.theorem12And13.toPositive hχ0 ha hb hα hγ)
      hData.section2,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad hχ0 ha hb hα hγ hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper for
the local-free `χ₀ = 0` positive solution-slice and thin section-2 route. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Preferred `χ₀ = 0` interval-domain Paper2 statement-frontier package.

This is a transparent alias for
`IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.
It avoids the refuted global `IntervalDomainInterpolation` route by using the
positive solution-slice interpolation package.  It remains conditional on the
thin section-2 frontiers, the finite-horizon alternative, the positive
solution-slice interpolation/energy package, `Proposition_2_5`, global
extension, bootstrap, and eventual-sup frontiers. -/
abbrev IntervalDomainPaper2PreferredChiZeroStatementFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    p C cGrad

/-- Preferred `χ₀ = 0` interval-domain Paper2 full-statement wrapper.

Pure wiring alias for
`intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.
It does not construct any residual package; it only gives the current preferred
route a shorter, grep-visible name. -/
theorem intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroStatementFrontierData p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData

/-- Instance-facing alias for the preferred `χ₀ = 0` interval-domain Paper2
full-statement route. -/
theorem intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact (IntervalDomainPaper2PreferredChiZeroStatementFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem frontier package.

This is the headline route for Theorems 1.1--1.3 only.  It avoids the refuted
global `IntervalDomainInterpolation` premise by using the positive
solution-slice route, and it uses the local-free `χ₀ = 0` interface for
Theorem 1.2/1.3.  It intentionally does not carry Proposition 1.1 or section-2
target frontiers. -/
abbrev IntervalDomainPaper2PreferredChiZeroMainTheoremFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem wrapper. -/
theorem intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroMainTheoremFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData

/-- Instance-facing alias for the preferred `χ₀ = 0` main-theorem route. -/
theorem intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2PreferredChiZeroMainTheoremFrontierData
          p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_frontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem frontier package
with Proposition 2.5 produced from the actual Moser atoms. -/
abbrev IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    p C cGrad

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem wrapper using the
actual-atom Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    p C cGrad hχ0 ha hb hα hγ hData

/-- Instance-facing alias for the preferred `χ₀ = 0` actual-atom
main-theorem route. -/
theorem
    intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomFrontierData
          p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem frontier package
with both Corollary 2.1 and Proposition 2.5 produced from the actual Moser
atoms.  This is the common-free headline route and has no `cGrad` parameter. -/
abbrev IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
    p C

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem wrapper using the
common-free actual-atom Corollary 2.1 / Proposition 2.5 route. -/
theorem
    intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData

/-- Instance-facing alias for the preferred `χ₀ = 0` common-free actual-atom
main-theorem route. -/
theorem
    intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
          p C)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
    p C hχ0 ha hb hα hγ hData.out

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem frontier package
with both Corollary 2.1 and Proposition 2.5 produced from actual Moser atoms,
and relative Moser reduced to mass-gradient data. -/
abbrev
    IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomMassGradientCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2MainTheoremChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    p C

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem wrapper using the
common-free mass-gradient actual-atom Corollary 2.1 / Proposition 2.5 route. -/
theorem
    intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomMassGradientCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomMassGradientCor21FrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData

/-- Instance-facing alias for the preferred `χ₀ = 0` common-free mass-gradient
actual-atom main-theorem route. -/
theorem
    intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomMassGradientCor21FrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomMassGradientCor21FrontierData
          p C)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomMassGradientCor21FrontierData
    p C hχ0 ha hb hα hγ hData.out

/-- Preferred `χ₀ = 0` statement-frontier package with Proposition 2.5
produced from structured Moser data instead of carried as a theorem field.

This is the current preferred route with the nested
`prop25 : Proposition_2_5 intervalDomain p` field split into the smaller
`IntervalDomainPaper2Prop25StructuredMoserFrontierData` interface. -/
structure IntervalDomainPaper2PreferredChiZeroStatementStructuredMoserFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  common :
    IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
      p cGrad
  prop25Moser : IntervalDomainPaper2Prop25StructuredMoserFrontierData p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Convert the structured-Moser preferred package back to the current
preferred package by producing Proposition 2.5 internally. -/
def IntervalDomainPaper2PreferredChiZeroStatementStructuredMoserFrontierData.toPreferred
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2PreferredChiZeroStatementStructuredMoserFrontierData
        p C cGrad) :
    IntervalDomainPaper2PreferredChiZeroStatementFrontierData p C cGrad where
  section2 := h.section2
  localAndMain :=
    { proposition11 := h.proposition11
      main :=
        { theorem12And13 :=
          { common := h.common
            prop25 :=
              intervalDomainPaper2_Proposition_2_5_of_structuredMoserFrontierData
                p h.prop25Moser
            globalExtension := h.globalExtension
            slowBootstrap := h.slowBootstrap
            criticalBootstrap := h.criticalBootstrap
            criticalEventualSupBound := h.criticalEventualSupBound
            strongBootstrap := h.strongBootstrap
            strongEventualSupBound := h.strongEventualSupBound } } }

/-- Preferred `χ₀ = 0` full-statement wrapper using the structured-Moser
Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_preferredChiZeroStatementTargets_of_structuredMoserFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroStatementStructuredMoserFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
    p C cGrad hχ0 ha hb hα hγ hData.toPreferred

/-- Instance-facing preferred `χ₀ = 0` full-statement wrapper using the
structured-Moser Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_preferredChiZeroStatementTargets_of_structuredMoserFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2PreferredChiZeroStatementStructuredMoserFrontierData
          p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_preferredChiZeroStatementTargets_of_structuredMoserFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Preferred `χ₀ = 0` statement-frontier package with Proposition 2.5
produced from the actual Moser atoms instead of carried as a theorem field. -/
structure IntervalDomainPaper2PreferredChiZeroStatementActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  common :
    IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
      p cGrad
  prop25Atoms : IntervalDomainPaper2Prop25ActualAtomFrontierData p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Convert the actual-atom preferred package back to the current preferred
package by producing Proposition 2.5 internally. -/
def IntervalDomainPaper2PreferredChiZeroStatementActualAtomFrontierData.toPreferred
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2PreferredChiZeroStatementActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2PreferredChiZeroStatementFrontierData p C cGrad where
  section2 := h.section2
  localAndMain :=
    { proposition11 := h.proposition11
      main :=
        { theorem12And13 :=
          { common := h.common
            prop25 :=
              intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
                p h.prop25Atoms
            globalExtension := h.globalExtension
            slowBootstrap := h.slowBootstrap
            criticalBootstrap := h.criticalBootstrap
            criticalEventualSupBound := h.criticalEventualSupBound
            strongBootstrap := h.strongBootstrap
            strongEventualSupBound := h.strongEventualSupBound } } }

/-- Preferred `χ₀ = 0` full-statement wrapper using the actual-atom
Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroStatementActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
    p C cGrad hχ0 ha hb hα hγ hData.toPreferred

/-- Instance-facing preferred `χ₀ = 0` full-statement wrapper using the
actual-atom Proposition 2.5 frontier. -/
theorem
    intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2PreferredChiZeroStatementActualAtomFrontierData
          p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out

/-- Interval-domain Paper 2 statement-frontier record using the half-step
H2-source local-existence route.

Legacy/no-go headline interface as written: the `interpolation` field is the
refuted global `IntervalDomainInterpolation` premise.  Prefer the
`...PositiveSolutionInterpolation...` H2-source statement routes. -/
structure IntervalDomainPaper2StatementH2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain : IntervalDomainPaper2LocalAndMainH2SourceFrontierData p C S

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
H2-source local-existence route. -/
theorem intervalDomainPaper2_statementTargets_of_H2SourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementH2SourceFrontierData p C S) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourceFrontierData
      p C S hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the H2-source local-existence route. -/
theorem intervalDomainPaper2_statementTargets_of_H2SourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementH2SourceFrontierData p C S)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_H2SourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Interval-domain Paper 2 statement-frontier record using the half-step
H2-source local-existence route and the positive-constant solution-slice
Theorem 1.2/1.3 route. -/
structure
    IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainH2SourcePositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Thinner H2-source statement-frontier record using the positive
solution-slice route.  It carries only the section-2 bootstrap branch data;
Corollary 2.1 is produced from the nested positive solution-slice common data. -/
structure
    IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationBootstrapFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  bootstrap : Paper2BootstrapEstimateBranchData intervalDomain p
  localAndMain :
    IntervalDomainPaper2LocalAndMainH2SourcePositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Thinner H2-source positive solution-slice statement route whose section-2
input omits Proposition 2.4 and Proposition 2.5. -/
structure
    IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationSection2ThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainH2SourcePositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
H2-source local-existence route, using positive-constant solution-slice
interpolation instead of the false global interpolation frontier. -/
theorem
    intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
      p C cGrad hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the H2-source local-existence route using positive-constant solution-slice
interpolation. -/
theorem
    intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
H2-source positive solution-slice route, with Corollary 2.1 derived from the
nested common data instead of carried separately. -/
theorem
    intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationBootstrapFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationBootstrapFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationFrontierData
      p C cGrad hData.localAndMain.main.theorem12And13 hData.bootstrap,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
      p C cGrad hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the H2-source thinner positive solution-slice/bootstrap data. -/
theorem
    intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationBootstrapFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationBootstrapFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationBootstrapFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
H2-source positive solution-slice route and thin section-2 data. -/
theorem
    intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationSection2ThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationSection2ThinFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierData
      p C cGrad hData.localAndMain.main.theorem12And13 hData.section2,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
      p C cGrad hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the H2-source positive solution-slice route and thin section-2 data. -/
theorem
    intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationSection2ThinFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementH2SourcePositiveSolutionInterpolationSection2ThinFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationSection2ThinFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-- Interval-domain Paper 2 statement-frontier record using the half-step
logistic-source local-existence route.

Legacy/no-go headline interface as written: the `interpolation` field is the
refuted global `IntervalDomainInterpolation` premise.  Prefer the
`...PositiveSolutionInterpolation...` logistic-source statement routes. -/
structure IntervalDomainPaper2StatementLogisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain) : Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  interpolation : IntervalDomainLemma41.IntervalDomainInterpolation
  localAndMain :
    IntervalDomainPaper2LocalAndMainLogisticSourceFrontierData p C S

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
logistic-source local-existence route. -/
theorem intervalDomainPaper2_statementTargets_of_logisticSourceFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementLogisticSourceFrontierData p C S) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_GN_frontier
      p hData.interpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourceFrontierData
      p C S hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the logistic-source local-existence route. -/
theorem intervalDomainPaper2_statementTargets_of_logisticSourceFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementLogisticSourceFrontierData p C S)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_logisticSourceFrontierData
    p C S hχ ha hb hγ_ge_one hData.out

/-- Interval-domain Paper 2 statement-frontier record using the half-step
logistic-source local-existence route and the positive-constant solution-slice
Theorem 1.2/1.3 route. -/
structure
    IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  corollary : IntervalDomainPaper2Corollary21FrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainLogisticSourcePositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Thinner logistic-source statement-frontier record using the positive
solution-slice route.  It carries only the section-2 bootstrap branch data;
Corollary 2.1 is produced from the nested positive solution-slice common data. -/
structure
    IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationBootstrapFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  bootstrap : Paper2BootstrapEstimateBranchData intervalDomain p
  localAndMain :
    IntervalDomainPaper2LocalAndMainLogisticSourcePositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Thinner logistic-source positive solution-slice statement route whose
section-2 input omits Proposition 2.4 and Proposition 2.5. -/
structure
    IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationSection2ThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainLogisticSourcePositiveSolutionInterpolationFrontierData
      p C cGrad

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
logistic-source local-existence route, using positive-constant solution-slice
interpolation instead of the false global interpolation frontier. -/
theorem
    intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_frontierData
      p hData.corollary,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
      p C cGrad hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the logistic-source local-existence route using positive-constant
solution-slice interpolation. -/
theorem
    intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
logistic-source positive solution-slice route, with Corollary 2.1 derived from
the nested common data instead of carried separately. -/
theorem
    intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationBootstrapFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationBootstrapFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationFrontierData
      p C cGrad hData.localAndMain.main.theorem12And13 hData.bootstrap,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
      p C cGrad hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the logistic-source thinner positive solution-slice/bootstrap data. -/
theorem
    intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationBootstrapFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationBootstrapFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationBootstrapFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

/-- Assemble the concrete interval-domain Paper 2 statement targets from the
logistic-source positive solution-slice route and thin section-2 data. -/
theorem
    intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationSection2ThinFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationSection2ThinFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_positiveSolutionInterpolationThinFrontierData
      p C cGrad hData.localAndMain.main.theorem12And13 hData.section2,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.localAndMain.main.theorem12And13.common.solutionInterpolation,
    intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
      p C cGrad hχ ha hb hγ_ge_one hData.localAndMain⟩

/-- Instance-facing concrete interval-domain Paper 2 statement wrapper from
the logistic-source positive solution-slice route and thin section-2 data. -/
theorem
    intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationSection2ThinFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2StatementLogisticSourcePositiveSolutionInterpolationSection2ThinFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationSection2ThinFrontierData
    p C cGrad hχ ha hb hγ_ge_one hData.out

section AxiomAudit

#print axioms intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
#print axioms intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
#print axioms intervalDomainPaper2_Theorems_1_2_and_1_3_of_interpolationFrontierData
#print axioms
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_positiveSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
#print axioms intervalDomainPaper2_mainTheoremTargets_of_chiZeroFrontierData
#print axioms intervalDomainPaper2_mainTheoremTargets_of_chiZeroInterpolationFrontierData
#print axioms
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
#print axioms
  intervalDomainPaper2_mainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_mainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
#print axioms intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroThinFrontierData
#print axioms intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroInterpolationFrontierData
#print axioms
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_localAndMainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
#print axioms
  intervalDomainPaper2_localAndMainTheoremTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_localAndMainTheoremTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
#print axioms intervalDomainPaper2_statementTargets_of_chiZeroFrontierData
#print axioms intervalDomainPaper2_statementTargets_of_chiZeroThinFrontierData
#print axioms intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationBootstrapFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationBootstrapFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_H2SourcePositiveSolutionInterpolationSection2ThinFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationBootstrapFrontierData
#print axioms
  intervalDomainPaper2_statementTargets_of_logisticSourcePositiveSolutionInterpolationSection2ThinFrontierData

end AxiomAudit

end

end ShenWork.Paper2
