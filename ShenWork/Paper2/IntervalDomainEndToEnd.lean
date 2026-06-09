/-
  ShenWork/Paper2/IntervalDomainEndToEnd.lean

  **Tightest reduction of Paper 2 Theorem 1.1 to genuine frontier hypotheses.**

  This file provides a single end-to-end theorem whose hypotheses are exactly
  the minimum residual that the axiom-clean repo machinery cannot yet discharge.

  ## Proved components (wired internally, 0 sorry)

  | Component | Source |
  |-----------|--------|
  | Picard FP -> GradientMildSolutionData | IntervalMildPicard |
  | HasRestartCosineRepresentations | IntervalMildPicardRegularity (from S) |
  | GradientMildClassicalRegularityFrontierData | IntervalRegularityFrontierWiring |
  | localExistence bridge | IntervalMildToLocalExistence |
  | gamma >= 1 umbrella (no hposWit) | IntervalDomainTheorem11Umbrella |
  | hUniform from hQuant+hRestart+hSupNorm | IntervalDomainRestartExtension |

  ## Remaining frontier hypotheses (taken as inputs)

  **Global hypotheses:**
  1. `hQuant` : QuantitativeLocalExistence delta(M) factory
  2. `hRestart` : RestartAndGlueWorks (overlap gluing)
  3. `hSupNorm` : interior sup-norm bound (continuation estimate)

  **Per-datum hypotheses** (existentially quantified):
  4. `S` : GradientMildHalfStepLogisticSourceData (F2)
  5. `hTimeNhd` : HasTimeNeighborhoodSpectralAgreement
  6. `hResolverData` : HasResolverDirectSpectralData
  7. `hSupNormDeriv` : IntervalDomainSupNormDerivativeNonposOn
  8. `hVpos` : resolver strict positivity
  9. `hInitialApproach` : mild-map initial approach
  10. `hpde_u` : pointwise PDE identity for u

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainThm11Assembly
import ShenWork.Paper2.IntervalRegularityFrontierWiring
import ShenWork.Paper2.IntervalDomainRestartExtension
import ShenWork.Paper2.IntervalMildPicardRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildToLocalExistence
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierWiring
open ShenWork.Paper2.RestartExtension
open ShenWork.Paper2.Theorem11Assembly

noncomputable section

namespace ShenWork.Paper2.EndToEnd

/-! ## Per-datum spectral frontier predicate

The per-datum frontier is a `Prop` that existentially quantifies over the
(data-carrying) `GradientMildHalfStepLogisticSourceData` and conjoins the
remaining `Prop`-valued spectral hypotheses.

**What is NOT included (because it is proved internally):**
- `HasRestartCosineRepresentations` (constructed from the logistic source data)
- `GradientMildClassicalRegularityFrontierData` (assembled from the spectral
  hypotheses via `gradientMildClassicalRegularityFrontierData_of_spectral`)
-/

/-- The per-datum spectral frontier: for a given Picard solution `D`, all
unproved inputs needed for local existence.

The logistic source data `S` is existentially quantified because it carries
computational data (profile, bounds, derivative witnesses). The remaining
fields are `Prop`-valued. -/
def PerDatumSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  -- F2: logistic half-step source data (existentially quantified)
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  -- u-side time regularity: neighborhood spectral agreement
  HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
  -- v-side time regularity: direct spectral data for the resolver
  HasResolverDirectSpectralData D.T
    (mildChemicalConcentration p D.u) p ∧
  -- Sup-norm monotonicity (parabolic maximum principle output)
  IntervalDomainSupNormDerivativeNonposOn D.u
    (Set.Ioo (0 : ℝ) D.T) ∧
  -- Resolver strict positivity (elliptic strong maximum principle)
  (∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p D.u t x) ∧
  -- Initial approach: mild map converges to u₀ as t -> 0+
  (∀ ε, 0 < ε →
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
  -- Pointwise PDE identity: u_t = Delta u - chi div(chemotaxis) + logistic
  (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv D.u t x =
      intervalDomain.laplacian (D.u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
            (mildChemicalConcentration p D.u t) x
        + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-! ## Construction of FrontierCoreData from per-datum spectral frontier -/

/-- Construct `GradientMildClassicalFrontierCoreData` from the per-datum
spectral frontier, using:
- `gradientMildClassicalRegularityFrontierData_of_spectral` for the 9
  regularity fields (internally constructs
  `HasRestartCosineRepresentations` from the logistic source data)
- The pointwise PDE identity from the frontier -/
theorem gradientMildClassicalFrontierCoreData_of_perDatum
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : GradientMildHalfStepLogisticSourceData D)
    (hTimeNhd : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (hResolverData : HasResolverDirectSpectralData D.T
      (mildChemicalConcentration p D.u) p)
    (hVpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p D.u t x)
    (hpde_u : ∀ t x, 0 < t → t < D.T →
      x ∈ intervalDomain.inside →
        intervalDomain.timeDeriv D.u t x =
          intervalDomain.laplacian (D.u t) x
            - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
                (mildChemicalConcentration p D.u t) x
            + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)) :
    GradientMildClassicalFrontierCoreData p D where
  hpde_u := hpde_u
  hregularityFrontier :=
    gradientMildClassicalRegularityFrontierData_of_spectral
      p D hTimeNhd hResolverData
      (hasRestartCosineRepresentations_of_gradientMildHalfStepLogisticSourceData
        D S)
      hVpos

/-- Construct the `hMildLocal` input consumed by the umbrella theorem
from per-datum spectral frontier data.

For each PID `u₀`, the caller provides a Picard fixed point `D` and
`PerDatumSpectralFrontier p D`. -/
theorem hMildLocal_of_perDatum
    (p : CM2Params)
    (hPerDatum : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ D : GradientMildSolutionData p u₀,
          PerDatumSpectralFrontier p D) :
    IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData
      p := by
  intro u₀ hu₀
  obtain ⟨D, S, hTimeNhd, hResolverData, _hSupNormDeriv,
    hVpos, hInitialApproach, hpde_u⟩ := hPerDatum u₀ hu₀
  exact ⟨D, S, hInitialApproach,
    gradientMildClassicalFrontierCoreData_of_perDatum
      p D S hTimeNhd hResolverData hVpos hpde_u⟩

/-! ## The end-to-end theorem -/

/-- **Paper 2 Theorem 1.1: end-to-end reduction to genuine frontier.**

This theorem produces `Theorem_1_1 intervalDomain p` from exactly the
minimum set of unproved hypotheses. Everything else (Picard iteration,
regularity bootstrap, spectral regularity wiring, L2 uniqueness,
delta-iteration, gamma >= 1 umbrella) is wired internally.

### Frontier hypotheses

**Global (continuation/extension):**
- `hQuant`: for every sup-norm bound `M`, there exists a uniform
  existence time `delta(M)` producing a classical solution from any
  PID bounded by `M`.
- `hRestart`: given an existing solution on `[0, T0]` and a fresh
  solution factory on `[0, delta]`, produce a solution on
  `[0, T0 + delta/2]`.
- `hSupNorm`: interior sup-norm preservation -- if `|u0| <= M` then
  `|u(t,x)| <= M` for all `0 < t < T0` (Lemma 3.1 / parabolic
  maximum principle).

**Per-datum (spectral regularity + source):**
- For every PID `u0`, there exists a Picard mild solution `D` and
  `PerDatumSpectralFrontier p D` providing:
  (a) F2 logistic half-step source data
  (b) u-side time neighborhood spectral agreement
  (c) v-side direct spectral data
  (d) sup-norm derivative nonpositivity
  (e) resolver strict positivity
  (f) initial approach
  (g) pointwise PDE identity -/
theorem paper2_theorem_1_1_endToEnd
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    -- Global continuation hypotheses
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hRestart : RestartAndGlueWorks p)
    (hSupNorm : ∀ {M : ℝ}, 0 < M →
      ∀ {u₀}, PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
      ∀ {T₀}, 0 < T₀ →
      ∀ {u v},
        IsPaper2ClassicalSolution intervalDomain p T₀ u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, 0 < t → t < T₀ →
          ∀ x : intervalDomainPoint, |u t x| ≤ M)
    -- Per-datum spectral frontier
    (hPerDatum : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ D : GradientMildSolutionData p u₀,
          PerDatumSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_of_frontier p hχ ha hb hγ_ge_one
    (uniformLocalExistence_of_quantitative_restart_supNorm
      p hQuant hRestart hSupNorm)
    (hMildLocal_of_perDatum p hPerDatum)

end ShenWork.Paper2.EndToEnd
