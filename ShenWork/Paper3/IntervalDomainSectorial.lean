/-
  Paper3 intervalDomain sectorial-semigroup bridge.

  This file does not prove sectoriality of the interval Neumann linearized
  operator.  It records the exact H3.1 hypothesis needed on the concrete
  interval domain and routes it through the existing raw Paper3 stability API.
-/
import ShenWork.PDE.SectorialOperator
import ShenWork.PDE.SpectralDecay
import ShenWork.Paper3.Statements

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE.SectorialOperator
open ShenWork.PDE.SpectralDecay

noncomputable section

/-- Concrete Paper3 constants used by the sectorial interval bridge.

The critical threshold is fixed to the unit-interval Neumann spectral formula.
The parameters `M0`, `uBar`, and `vLower` keep the global-stability frontiers
visible without exposing arbitrary `Paper3Constants` field projections in the
main interval wrappers below. -/
def intervalDomainSectorialPaper3Constants
    (p : CM2Params) (M0 uBar vLower : ℝ) :
    Paper3Constants intervalDomain p where
  chiCritical := fun uStar =>
    paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
      (p.ν / p.μ * uStar ^ p.γ)
  chiStrong1 := fun uStar =>
    chiStrong1Formula p uStar (p.ν / p.μ * uStar ^ p.γ)
  chiStrong2 := fun uStar => chiStrong2Formula p uStar
  chiStrong3 := fun uStar =>
    chiStrong3Formula p M0 uStar (p.ν / p.μ * uStar ^ p.γ)
  chiStrong4 := fun uStar => chiStrong4Formula p M0 uStar
  chiMinimal1 := fun uStar => chiMinimal1Formula p 1 uStar uBar vLower
  chiMinimal2 := fun _uStar => chiMinimal2Formula p uBar vLower
  eventualMinimalUBound := fun _uStar => uBar
  gaussianLowerConst := 1
  gaussianLowerConst_pos := by norm_num

/-- The sectorial interval constants use exactly the unit-interval Neumann
critical spectrum. -/
theorem intervalDomainSectorialPaper3Constants_usesCriticalSpectrum
    (p : CM2Params) (M0 uBar vLower : ℝ) :
    Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) := by
  intro uStar _huStar
  rfl

/-- Concrete `C¹` distance on the interval for the sectorial mainline. -/
def intervalDomainSectorialC1Distance
    (f g : intervalDomain.Point → ℝ) : ℝ :=
  intervalDomain.supNorm (fun x => f x - g x) +
    intervalDomain.supNorm
      (fun x => intervalDomain.gradNorm (fun y => f y - g y) x)

/-- Concrete `X^σ_p` gauge used by the sectorial interval bridge.

At this abstraction level it is the primitive sup-distance gauge; this makes
the `sup`-small to `X^σ_p`-small condition definitional for the concrete
mainline theorem. -/
def intervalDomainSectorialXpSigmaDistance
    (_sigma _pNorm : ℝ) (f g : intervalDomain.Point → ℝ) : ℝ :=
  intervalDomain.supNorm (fun x => f x - g x)

/-- Concrete stability norm package for the interval sectorial bridge. -/
def intervalDomainSectorialStabilityNorms :
    StabilityNorms intervalDomain where
  c1Distance := intervalDomainSectorialC1Distance
  xpSigmaDistance := intervalDomainSectorialXpSigmaDistance

@[simp] theorem intervalDomainSectorialStabilityNorms_c1Distance
    (f g : intervalDomain.Point → ℝ) :
    intervalDomainSectorialStabilityNorms.c1Distance f g =
      intervalDomainSectorialC1Distance f g := rfl

@[simp] theorem intervalDomainSectorialStabilityNorms_xpSigmaDistance
    (sigma pNorm : ℝ) (f g : intervalDomain.Point → ℝ) :
    intervalDomainSectorialStabilityNorms.xpSigmaDistance sigma pNorm f g =
      intervalDomain.supNorm (fun x => f x - g x) := rfl

/-- Concrete sectorial `X^σ_p` control by the primitive sup norm. -/
theorem intervalDomainSectorialStabilityNorms_xpSigma_le_supNorm
    (sigma pNorm uStar : ℝ) (u₀ : intervalDomain.Point → ℝ) :
    intervalDomainSectorialStabilityNorms.xpSigmaDistance sigma pNorm u₀
        (fun _ => uStar) ≤
      intervalDomain.supNorm (fun x => u₀ x - uStar) := by
  rfl

/-- The concrete sectorial norm-control bridge for the interval. -/
theorem intervalDomainSectorialStabilityNorms_supControlsXpSigmaDistance
    (sigma pNorm uStar : ℝ) :
    SupControlsXpSigmaDistance intervalDomain
      intervalDomainSectorialStabilityNorms sigma pNorm uStar :=
  SupControlsXpSigmaDistance.of_xpSigma_le_supNorm
    (intervalDomainSectorialStabilityNorms_xpSigma_le_supNorm
      sigma pNorm uStar)

/-- Concrete nonlinear orbit-control frontier for the interval sectorial
mainline.  This is the same remaining Duhamel/small-data comparison as
`IntervalDomainSpectralSemigroupOrbitBoundRaw`, but stated with the concrete
sectorial gauges rather than abstract `StabilityNorms` field projections. -/
def IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw
    (p : CM2Params) : Prop :=
  ∀ sigma pNorm uStar vStar,
    1 / 2 < sigma → sigma < 1 → 1 < pNorm →
    LinearlyStable unitIntervalNeumannSpectrum p uStar vStar →
      ∃ eps > 0, ∃ C > 0,
        ∀ u₀ : intervalDomain.Point → ℝ, PositiveInitialDatum intervalDomain u₀ →
          intervalDomainSectorialXpSigmaDistance sigma pNorm u₀
              (fun _ => uStar) ≤ eps →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution intervalDomain p u v →
              InitialTrace intervalDomain u₀ u →
                ∀ t, (ht : 0 ≤ t) →
                  intervalDomainSectorialC1Distance (u t) (fun _ => uStar) +
                    intervalDomainSectorialC1Distance (v t) (fun _ => vStar) ≤
                      C * ‖unitIntervalNeumannHeatSemigroupP0Compl t ht‖

/-- The remaining nonlinear orbit-control input after the concrete
unit-interval analytic-semigroup spectral decay has been separated out.

This is deliberately weaker than assuming `SectorialLocalExponentialRaw`
directly: it asks for a Duhamel/small-data comparison of nonlinear classical
solutions to the concrete Neumann heat semigroup with the constant mode
removed.  The exponential time decay of that semigroup is proved in
`PDE/SpectralDecay.lean` and is applied below.

Point 17 status: conditional theorem frontier, state ③.  The spectral-decay
subblock is discharged by `unitIntervalNeumannHeatSemigroupP0Compl_opNorm_le`;
the remaining named frontier is the nonlinear orbit comparison encoded here. -/
def IntervalDomainSpectralSemigroupOrbitBoundRaw
    (p : CM2Params) (N : StabilityNorms intervalDomain) : Prop :=
  ∀ sigma pNorm uStar vStar,
    1 / 2 < sigma → sigma < 1 → 1 < pNorm →
    LinearlyStable unitIntervalNeumannSpectrum p uStar vStar →
      ∃ eps > 0, ∃ C > 0,
        ∀ u₀ : intervalDomain.Point → ℝ, PositiveInitialDatum intervalDomain u₀ →
          N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤ eps →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution intervalDomain p u v →
              InitialTrace intervalDomain u₀ u →
                ∀ t, (ht : 0 ≤ t) →
                  N.c1Distance (u t) (fun _ => uStar) +
                    N.c1Distance (v t) (fun _ => vStar) ≤
                      C * ‖unitIntervalNeumannHeatSemigroupP0Compl t ht‖

/-- Convert the concrete sectorial orbit frontier to the generic raw frontier
used by the existing Paper3 API. -/
theorem intervalDomain_spectralSemigroupOrbitBoundRaw_of_sectorialConcrete
    (p : CM2Params)
    (h : IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p) :
    IntervalDomainSpectralSemigroupOrbitBoundRaw p
      intervalDomainSectorialStabilityNorms := by
  intro sigma pNorm uStar vStar hsigma_low hsigma_high hpNorm hstable
  rcases h sigma pNorm uStar vStar hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, C, hC, hbound⟩
  refine ⟨eps, heps, C, hC, ?_⟩
  intro u₀ hu₀ hsmall u v hglobal htrace t ht
  exact hbound u₀ hu₀ hsmall u v hglobal htrace t ht

/-- The concrete analytic-semigroup spectral decay discharges the exponential
part of `SectorialLocalExponentialRaw` on `intervalDomain`.

The proof uses the physical `L²(0,1)` estimate
`‖e^{tΔ_N}(I-P₀)‖ ≤ exp(-π² t)` from `PDE/SpectralDecay.lean`.  What remains
outside this theorem is the genuine nonlinear Duhamel/orbit-control estimate
`IntervalDomainSpectralSemigroupOrbitBoundRaw`; this file does not fake that
as a consequence of linear spectral decay alone. -/
theorem intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
    (p : CM2Params) (N : StabilityNorms intervalDomain)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N) :
    SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
      N.c1Distance N.xpSigmaDistance := by
  intro sigma pNorm uStar vStar hsigma_low hsigma_high hpNorm hstable
  rcases horbit sigma pNorm uStar vStar
      hsigma_low hsigma_high hpNorm hstable with
    ⟨eps, heps, C, hC, hbound⟩
  refine ⟨eps, heps, C, hC, Real.pi ^ 2, ?_, ?_⟩
  · exact sq_pos_of_ne_zero (ne_of_gt Real.pi_pos)
  · intro u₀ hu₀ hsmall u v hglobal htrace t ht
    have hsemigroup :=
      hbound u₀ hu₀ hsmall u v hglobal htrace t ht
    have hop :
        ‖unitIntervalNeumannHeatSemigroupP0Compl t ht‖ ≤
          Real.exp (-(Real.pi ^ 2) * t) :=
      unitIntervalNeumannHeatSemigroupP0Compl_opNorm_le ht
    have hmul :
        C * ‖unitIntervalNeumannHeatSemigroupP0Compl t ht‖ ≤
          C * Real.exp (-(Real.pi ^ 2) * t) :=
      mul_le_mul_of_nonneg_left hop hC.le
    exact le_trans hsemigroup hmul

/-- Lemma A.1 on the concrete interval once the remaining nonlinear
orbit-comparison frontier has been supplied.

This is the raw-free theorem-level interface used below for Theorem 2.2's
`X^σ_p` local exponential branch.  The proof is definitional after the
spectral-decay discharge above, since `Lemma_A_1` and
`SectorialLocalExponentialRaw` have the same exposed estimate for
`StabilityNorms`. -/
theorem intervalDomain_Lemma_A_1_of_spectralSemigroupOrbitBound
    (p : CM2Params) (N : StabilityNorms intervalDomain)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N) :
    Lemma_A_1 intervalDomain p unitIntervalNeumannSpectrum N :=
  intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
    p N horbit

/-- Theorem 2.2's `X^σ_p` local exponential branch on the interval with the
old `SectorialLocalExponentialRaw` input discharged through the concrete
spectral-decay theorem.

Point 17 status: conditional theorem, state ③.  The linear spectral decay is
proved in `PDE/SpectralDecay.lean`; the remaining assumption is the named
nonlinear orbit-comparison frontier, not the raw sectorial package. -/
theorem
intervalDomain_Theorem_2_2_xpSigma_local_exponential_branch_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N) :
    (∀ sigma pNorm, 1 / 2 < sigma → sigma < 1 → 1 < pNorm →
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        p.χ₀ < C.chiCritical eq.1 →
          ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
            ∀ u₀ : intervalDomain.Point → ℝ,
              PositiveInitialDatum intervalDomain u₀ →
              N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
                ∀ u v : ℝ → intervalDomain.Point → ℝ,
                  IsPaper2GlobalClassicalSolution intervalDomain p u v →
                  InitialTrace intervalDomain u₀ u →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate) ∧
    (∀ sigma pNorm, 1 / 2 < sigma → sigma < 1 → 1 < pNorm →
      p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          p.χ₀ < C.chiCritical uStar →
            ∃ eps > 0, ∃ A > 0, ∃ rate > 0,
              ∀ u₀ : intervalDomain.Point → ℝ,
                PositiveInitialDatum intervalDomain u₀ →
                N.xpSigmaDistance sigma pNorm u₀ (fun _ => eq.1) ≤ eps →
                  ∀ u v : ℝ → intervalDomain.Point → ℝ,
                    IsPaper2GlobalClassicalSolution intervalDomain p u v →
                    InitialTrace intervalDomain u₀ u →
                      ExponentialC1ConvergenceWith intervalDomain N u v
                        eq.1 eq.2 A rate) :=
  Theorem_2_2_xpSigma_local_exponential_branch_of_Lemma_A_1
    intervalDomain unitIntervalNeumannSpectrum p N C
    unitIntervalNeumannSpectrum_hasNeumannSpectrum hC
    (intervalDomain_Lemma_A_1_of_spectralSemigroupOrbitBound p N horbit)

/-- Interval-domain Paper3 Theorem 2.2 with the old raw sectorial blocker
replaced by a nonlinear orbit-control frontier plus the proved spectral decay.

Point 17 status: conditional theorem, state ③.  Compared with the earlier
`...of_sectorial_frontiers` wrappers, this theorem no longer assumes
`SectorialLocalExponentialRaw` directly.  The analytic-semigroup decay part is
proved by `PDE/SpectralDecay.lean`; the remaining frontiers are the nonlinear
orbit comparison, `X^σ_p`/sup control, and small-data global existence. -/
theorem intervalDomain_Theorem_2_2_of_spectralSemigroupOrbitBound_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hcontrol :
      ∀ uStar, SupControlsXpSigmaDistance intervalDomain N sigma pNorm uStar)
    (hexist :
      ∀ uStar, ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p uStar delta)
    (hmexist :
      ∀ uStar, ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N C := by
  exact
    Theorem_2_2_full_by_chi_sign_of_raw
      unitIntervalNeumannSpectrum_hasNeumannSpectrum hC
      (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
        p N horbit)
      hsigma_low hsigma_high hpNorm hcontrol hexist hmexist

/-- H3.1 interval-domain local exponential bridge with
`SectorialLocalExponentialRaw` removed from the assumptions.

The proof first derives the raw estimate from the orbit-comparison frontier
and the proved unit-interval spectral decay, then uses the existing Paper3
sup-to-`X^σ_p` bridge. -/
theorem intervalDomain_locallyExponentiallyStableFromSup_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar vStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist : ∀ delta > 0, SmallDataGlobalExistence intervalDomain p uStar delta) :
    LocallyExponentiallyStableFromSup intervalDomain p N uStar vStar :=
  (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
    p N horbit).locally_from_xpSigma_le_supNorm
      hsigma_low hsigma_high hpNorm hstable hxp hexist

/-- Mass-constrained version of
`intervalDomain_locallyExponentiallyStableFromSup_of_spectralSemigroupOrbitBound`. -/
theorem
intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar vStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta) :
    MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
      uStar vStar :=
  (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
    p N horbit).massConstrained_from_xpSigma_le_supNorm
      hsigma_low hsigma_high hpNorm hstable hxp hexist

/-- Spectral-gap-to-local-stability bridge with the raw sectorial input
removed from the assumptions. -/
theorem
intervalDomain_locallyExponentiallyStableFromSup_of_spectralGap_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar vStar rate : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist : ∀ delta > 0, SmallDataGlobalExistence intervalDomain p uStar delta) :
    LocallyExponentiallyStableFromSup intervalDomain p N uStar vStar :=
  intervalDomain_locallyExponentiallyStableFromSup_of_spectralSemigroupOrbitBound
    p N hsigma_low hsigma_high hpNorm horbit hgap.linearlyStable hxp hexist

/-- Mass-constrained spectral-gap-to-local-stability bridge with the raw
sectorial input removed from the assumptions. -/
theorem
intervalDomain_massConstrainedLocalExp_of_spectralGap_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar vStar rate : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta) :
    MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
      uStar vStar :=
  intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_spectralSemigroupOrbitBound
    p N hsigma_low hsigma_high hpNorm horbit hgap.linearlyStable hxp hexist

/-- H3.1 interval-domain local exponential bridge from the honest raw
sectorial-semigroup hypothesis, plus the two explicit analytic side inputs
needed to use it from a sup-norm neighborhood. -/
theorem intervalDomain_locallyExponentiallyStableFromSup_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar vStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist : ∀ delta > 0, SmallDataGlobalExistence intervalDomain p uStar delta) :
    LocallyExponentiallyStableFromSup intervalDomain p N uStar vStar :=
  hsectorial.locally_from_xpSigma_le_supNorm
    hsigma_low hsigma_high hpNorm hstable hxp hexist

/-- H3.1 interval-domain mass-constrained local exponential bridge from the
same raw sectorial-semigroup hypothesis and explicit side inputs. -/
theorem intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar vStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hstable :
      LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta) :
    MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
      uStar vStar :=
  hsectorial.massConstrained_from_xpSigma_le_supNorm
    hsigma_low hsigma_high hpNorm hstable hxp hexist

/-- H3.1 bridge using the concrete unit-interval spectral-gap package.  The
spectral gap discharges the `LinearlyStable` input to the raw sectorial
interface; nonlinear sectoriality, the norm comparison, and small-data
existence remain explicit frontiers. -/
theorem intervalDomain_locallyExponentiallyStableFromSup_of_spectralGap_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar vStar rate : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist : ∀ delta > 0, SmallDataGlobalExistence intervalDomain p uStar delta) :
    LocallyExponentiallyStableFromSup intervalDomain p N uStar vStar :=
  intervalDomain_locallyExponentiallyStableFromSup_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm hsectorial hgap.linearlyStable hxp hexist

/-- Mass-constrained version of the spectral-gap-to-local-stability bridge. -/
theorem
intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_spectralGap_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar vStar rate : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hgap : UnitIntervalLinearSpectralGap p uStar vStar rate)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta) :
    MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
      uStar vStar :=
  intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm hsectorial hgap.linearlyStable hxp hexist

/-- Stronger nonpositive-sensitivity positive-equilibrium bridge: the linear
input is not merely `LinearlyStable`; it is the explicit unit-interval
spectral gap `p.a * p.α`.  The nonlinear sectorial/norm/small-data inputs
remain the honest H3.1 frontiers. -/
theorem
intervalDomain_positiveEquilibrium_localStability_chi_nonpos_of_spectralGap_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    UnitIntervalLinearSpectralGap p eq.1 eq.2 (p.a * p.α) ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 := by
  dsimp
  have hgap :
      UnitIntervalLinearSpectralGap p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 (p.a * p.α) := by
    simpa using
      positiveEquilibrium_UnitIntervalLinearSpectralGap_of_chi_nonpos
        p hχ ha hb
  exact
    ⟨hgap,
      intervalDomain_locallyExponentiallyStableFromSup_of_spectralGap_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hgap hxp hexist⟩

/-- Mass-constrained version of the explicit spectral-gap nonpositive branch. -/
theorem
intervalDomain_positiveEquilibrium_massStability_chi_nonpos_of_spectralGap_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    UnitIntervalLinearSpectralGap p eq.1 eq.2 (p.a * p.α) ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 := by
  dsimp
  have hgap :
      UnitIntervalLinearSpectralGap p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 (p.a * p.α) := by
    simpa using
      positiveEquilibrium_UnitIntervalLinearSpectralGap_of_chi_nonpos
        p hχ ha hb
  exact
    ⟨hgap,
      intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hgap.linearlyStable
        hxp hexist⟩

/-- Nonpositive-sensitivity positive-equilibrium interval branch: the linear
part is proved from the unit-interval Neumann spectrum; the nonlinear local
exponential conclusion remains conditional exactly on H3.1 and small-data
existence/norm-comparison inputs. -/
theorem intervalDomain_positiveEquilibrium_localStability_chi_nonpos_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 := by
  dsimp
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      hχ ha hb
  exact
    ⟨hstable,
      intervalDomain_locallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hstable hxp hexist⟩

/-- Mass-constrained version of the nonpositive-sensitivity
positive-equilibrium interval branch. -/
theorem intervalDomain_positiveEquilibrium_massStability_chi_nonpos_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 := by
  dsimp
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    positiveEquilibrium_linearlyStable_of_chi_nonpos_neumann
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      hχ ha hb
  exact
    ⟨hstable,
      intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hstable hxp hexist⟩

/-- Critical-threshold positive-equilibrium interval branch: the linear part is
proved from the concrete unit-interval Neumann spectrum; H3.1 remains exactly
the raw sectorial estimate plus norm-comparison and small-data existence. -/
theorem intervalDomain_positiveEquilibrium_localStability_of_chi_lt_critical_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 := by
  dsimp
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    unitInterval_positiveEquilibrium_linearlyStable_of_chi_lt_critical
      p ha hb hχ
  exact
    ⟨hstable,
      intervalDomain_locallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hstable hxp hexist⟩

/-- Mass-constrained version of the critical-threshold
positive-equilibrium interval branch. -/
theorem intervalDomain_positiveEquilibrium_massStability_of_chi_lt_critical_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 := by
  dsimp
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    unitInterval_positiveEquilibrium_linearlyStable_of_chi_lt_critical
      p ha hb hχ
  exact
    ⟨hstable,
      intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hstable hxp hexist⟩

/-- Nonpositive-sensitivity minimal-equilibrium interval branch: the linear
part is proved from the unit-interval Neumann spectrum, while the nonlinear
local exponential conclusion remains conditional on H3.1 and the explicit
small-data/norm-comparison frontiers. -/
theorem
intervalDomain_minimalEquilibrium_localStability_chi_nonpos_of_massSpectralGap_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (_hb : p.b = 0)
    (huStar : 0 < uStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    UnitIntervalLinearMassSpectralGap p eq.1 eq.2
        unitIntervalNeumannSpectrum.firstNonzero ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 := by
  dsimp
  have hgap :
      UnitIntervalLinearMassSpectralGap p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2
        unitIntervalNeumannSpectrum.firstNonzero := by
    simpa using
      minimalEquilibrium_UnitIntervalLinearMassSpectralGap_of_chi_nonpos
        p hχ ha huStar
  exact
    ⟨hgap,
      intervalDomain_locallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hgap.linearlyStable
        hxp hexist⟩

/-- Mass-constrained version of the explicit nonzero-mode minimal-branch gap. -/
theorem
intervalDomain_minimalEquilibrium_massStability_chi_nonpos_of_massSpectralGap_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (_hb : p.b = 0)
    (huStar : 0 < uStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    UnitIntervalLinearMassSpectralGap p eq.1 eq.2
        unitIntervalNeumannSpectrum.firstNonzero ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 := by
  dsimp
  have hgap :
      UnitIntervalLinearMassSpectralGap p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2
        unitIntervalNeumannSpectrum.firstNonzero := by
    simpa using
      minimalEquilibrium_UnitIntervalLinearMassSpectralGap_of_chi_nonpos
        p hχ ha huStar
  exact
    ⟨hgap,
      intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hgap.linearlyStable
        hxp hexist⟩

/-- Nonpositive-sensitivity minimal-equilibrium interval branch: the linear
part is proved from the unit-interval Neumann spectrum, while the nonlinear
local exponential conclusion remains conditional on H3.1 and the explicit
small-data/norm-comparison frontiers. -/
theorem intervalDomain_minimalEquilibrium_localStability_chi_nonpos_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (_hb : p.b = 0)
    (huStar : 0 < uStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 := by
  dsimp
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
    minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero_neumann
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      hχ ha huStar
  exact
    ⟨hstable,
      intervalDomain_locallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hstable hxp hexist⟩

/-- Mass-constrained version of the nonpositive-sensitivity minimal-equilibrium
interval branch. -/
theorem intervalDomain_minimalEquilibrium_massStability_chi_nonpos_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (_hb : p.b = 0)
    (huStar : 0 < uStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 := by
  dsimp
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
    minimalEquilibrium_linearlyStable_of_chi_nonpos_a_eq_zero_neumann
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
      hχ ha huStar
  exact
    ⟨hstable,
      intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hstable hxp hexist⟩

/-- Critical-threshold minimal-equilibrium interval branch.  The assumptions
`p.a = 0` and `p.b = 0` identify the branch used in Paper3, while the linear
stability proof itself is supplied by the concrete unit-interval critical
sensitivity. -/
theorem intervalDomain_minimalEquilibrium_localStability_of_chi_lt_critical_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (_ha : p.a = 0) (_hb : p.b = 0)
    (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 := by
  dsimp
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
    unitInterval_minimalEquilibrium_linearlyStable_of_chi_lt_critical
      p huStar hχ
  exact
    ⟨hstable,
      intervalDomain_locallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hstable hxp hexist⟩

/-- Mass-constrained version of the critical-threshold minimal-equilibrium
interval branch. -/
theorem intervalDomain_minimalEquilibrium_massStability_of_chi_lt_critical_of_sectorialHypothesis
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    (_ha : p.a = 0) (_hb : p.b = 0)
    (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 := by
  dsimp
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
    unitInterval_minimalEquilibrium_linearlyStable_of_chi_lt_critical
      p huStar hχ
  exact
    ⟨hstable,
      intervalDomain_massConstrainedLocallyExponentiallyStableFromSup_of_sectorialHypothesis
        p N hsigma_low hsigma_high hpNorm hsectorial hstable hxp hexist⟩

/-- Branch-specific raw Paper3 Theorem 2.2 local-stability interfaces for the
concrete interval domain.  Compared with the generic raw theorem, this exposes
only the analytic frontiers that are actually used by the two branches:
positive equilibria and minimal equilibria with `0 < uStar`. -/
theorem intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hxpPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        ∀ u₀ : intervalDomain.Point → ℝ,
          N.xpSigmaDistance sigma pNorm u₀
              (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
            intervalDomain.supNorm
              (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexistPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b), ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta)
    (hxpMinimal :
      ∀ uStar, 0 < uStar →
        ∀ u₀ : intervalDomain.Point → ℝ,
          N.xpSigmaDistance sigma pNorm u₀
              (fun _ => (minimalEquilibrium p uStar).1) ≤
            intervalDomain.supNorm
              (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hmexistMinimal :
      ∀ uStar, 0 < uStar → ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)) ∧
    LinearStabilityInstabilityMinimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)) := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    dsimp
    intro hχ
    have hstable :
        LinearlyStable unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      unitInterval_positiveEquilibrium_linearlyStable_of_chi_lt_critical
        p ha hb (by
          simpa [positiveEquilibrium] using hχ)
    have hlocal :
        LocallyExponentiallyStableFromSup intervalDomain p N
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      hsectorial.locally_from_xpSigma_le_supNorm
        hsigma_low hsigma_high hpNorm hstable
        (hxpPositive ha hb) (hexistPositive ha hb)
    rcases hlocal with ⟨δ, hδ, A, hA, rate, hrate, hmain⟩
    exact ⟨hstable, δ, hδ, A, hA, rate, hrate, hmain⟩
  · intro _ha _hb uStar huStar
    dsimp
    intro hχ
    have hstable :
        LinearlyStable unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      unitInterval_minimalEquilibrium_linearlyStable_of_chi_lt_critical
        p huStar (by
          simpa [minimalEquilibrium] using hχ)
    have hlocal :
        MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      hsectorial.massConstrained_from_xpSigma_le_supNorm
        hsigma_low hsigma_high hpNorm hstable
        (hxpMinimal uStar huStar) (hmexistMinimal uStar huStar)
    rcases hlocal with ⟨δ, hδ, A, hA, rate, hrate, hmain⟩
    exact ⟨hstable, δ, hδ, A, hA, rate, hrate, hmain⟩

/-- Constants-package version of the branch-specific interval raw
local-stability interfaces.  The only constants-package input is the audited
identification of `C.chiCritical` with the concrete unit-interval critical
spectrum; the sectorial, norm-comparison, and small-data frontiers remain
branch-specific. -/
theorem intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers_criticalSpectrum
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hsectorial :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hxpPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        ∀ u₀ : intervalDomain.Point → ℝ,
          N.xpSigmaDistance sigma pNorm u₀
              (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
            intervalDomain.supNorm
              (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexistPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b), ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta)
    (hxpMinimal :
      ∀ uStar, 0 < uStar →
        ∀ u₀ : intervalDomain.Point → ℝ,
          N.xpSigmaDistance sigma pNorm u₀
              (fun _ => (minimalEquilibrium p uStar).1) ≤
            intervalDomain.supNorm
              (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hmexistMinimal :
      ∀ uStar, 0 < uStar → ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance C.chiCritical ∧
    LinearStabilityInstabilityMinimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance C.chiCritical := by
  refine ⟨?_, ?_⟩
  · intro ha hb
    dsimp
    intro hχ
    have hstable :
        LinearlyStable unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      hC.positiveEquilibrium_linearlyStable
        unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hχ
    have hlocal :
        LocallyExponentiallyStableFromSup intervalDomain p N
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      hsectorial.locally_from_xpSigma_le_supNorm
        hsigma_low hsigma_high hpNorm hstable
        (hxpPositive ha hb) (hexistPositive ha hb)
    rcases hlocal with ⟨δ, hδ, A, hA, rate, hrate, hmain⟩
    exact ⟨hstable, δ, hδ, A, hA, rate, hrate, hmain⟩
  · intro _ha _hb uStar huStar
    dsimp
    intro hχ
    have hstable :
        LinearlyStable unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      hC.minimalEquilibrium_linearlyStable
        unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hχ
    have hlocal :
        MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      hsectorial.massConstrained_from_xpSigma_le_supNorm
        hsigma_low hsigma_high hpNorm hstable
        (hxpMinimal uStar huStar) (hmexistMinimal uStar huStar)
    rcases hlocal with ⟨δ, hδ, A, hA, rate, hrate, hmain⟩
    exact ⟨hstable, δ, hδ, A, hA, rate, hrate, hmain⟩

/-- Branch-specific Theorem 2.2 local-stability interfaces with the raw
sectorial input discharged through spectral decay plus the named nonlinear
orbit-comparison frontier. -/
theorem intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hxpPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        ∀ u₀ : intervalDomain.Point → ℝ,
          N.xpSigmaDistance sigma pNorm u₀
              (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
            intervalDomain.supNorm
              (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexistPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b), ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta)
    (hxpMinimal :
      ∀ uStar, 0 < uStar →
        ∀ u₀ : intervalDomain.Point → ℝ,
          N.xpSigmaDistance sigma pNorm u₀
              (fun _ => (minimalEquilibrium p uStar).1) ≤
            intervalDomain.supNorm
              (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hmexistMinimal :
      ∀ uStar, 0 < uStar → ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)) ∧
    LinearStabilityInstabilityMinimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)) :=
  intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers
    p N
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm hxpPositive hexistPositive
    hxpMinimal hmexistMinimal

/-- Critical-spectrum constants-package version of
`intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers_spectralSemigroupOrbitBound`. -/
theorem
intervalDomain_linearStabilityInstabilityRaw_criticalSpectrum_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hxpPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        ∀ u₀ : intervalDomain.Point → ℝ,
          N.xpSigmaDistance sigma pNorm u₀
              (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
            intervalDomain.supNorm
              (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexistPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b), ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta)
    (hxpMinimal :
      ∀ uStar, 0 < uStar →
        ∀ u₀ : intervalDomain.Point → ℝ,
          N.xpSigmaDistance sigma pNorm u₀
              (fun _ => (minimalEquilibrium p uStar).1) ≤
            intervalDomain.supNorm
              (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hmexistMinimal :
      ∀ uStar, 0 < uStar → ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    LinearStabilityInstabilityNonminimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance C.chiCritical ∧
    LinearStabilityInstabilityMinimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance C.chiCritical :=
  intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers_criticalSpectrum
    p N C hC
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm hxpPositive hexistPositive
    hxpMinimal hmexistMinimal

/-- Positive-equilibrium nonpositive-sensitivity branch with the old raw
sectorial input discharged through the concrete spectral-decay bridge. -/
theorem
intervalDomain_positiveEquilibrium_localStability_chi_nonpos_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 :=
  intervalDomain_positiveEquilibrium_localStability_chi_nonpos_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hχ ha hb hxp hexist

/-- Mass-constrained positive-equilibrium nonpositive branch with the
sectorial raw hypothesis replaced by the spectral-orbit frontier. -/
theorem
intervalDomain_positiveEquilibrium_massStability_chi_nonpos_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 :=
  intervalDomain_positiveEquilibrium_massStability_chi_nonpos_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hχ ha hb hxp hexist

/-- Positive-equilibrium critical-threshold branch with the sectorial raw
hypothesis replaced by the spectral-orbit frontier. -/
theorem
intervalDomain_positiveEquilibrium_localStability_of_chi_lt_critical_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 :=
  intervalDomain_positiveEquilibrium_localStability_of_chi_lt_critical_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    ha hb hχ hxp hexist

/-- Mass-constrained positive-equilibrium critical-threshold branch with the
sectorial raw hypothesis replaced by the spectral-orbit frontier. -/
theorem
intervalDomain_positiveEquilibrium_massStability_of_chi_lt_critical_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (positiveEquilibrium p ⟨ha, hb⟩).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (positiveEquilibrium p ⟨ha, hb⟩).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 :=
  intervalDomain_positiveEquilibrium_massStability_of_chi_lt_critical_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    ha hb hχ hxp hexist

/-- Minimal-equilibrium nonpositive-sensitivity branch with the sectorial raw
hypothesis replaced by the spectral-orbit frontier. -/
theorem
intervalDomain_minimalEquilibrium_localStability_chi_nonpos_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    (huStar : 0 < uStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 :=
  intervalDomain_minimalEquilibrium_localStability_chi_nonpos_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hχ ha hb huStar hxp hexist

/-- Mass-constrained minimal-equilibrium nonpositive branch with the sectorial
raw hypothesis replaced by the spectral-orbit frontier. -/
theorem
intervalDomain_minimalEquilibrium_massStability_chi_nonpos_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    (huStar : 0 < uStar)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 :=
  intervalDomain_minimalEquilibrium_massStability_chi_nonpos_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hχ ha hb huStar hxp hexist

/-- Minimal-equilibrium critical-threshold branch with the sectorial raw
hypothesis replaced by the spectral-orbit frontier. -/
theorem
intervalDomain_minimalEquilibrium_localStability_of_chi_lt_critical_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : p.a = 0) (hb : p.b = 0)
    (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 :=
  intervalDomain_minimalEquilibrium_localStability_of_chi_lt_critical_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    ha hb huStar hχ hxp hexist

/-- Mass-constrained minimal-equilibrium critical-threshold branch with the
sectorial raw hypothesis replaced by the spectral-orbit frontier. -/
theorem
intervalDomain_minimalEquilibrium_massStability_of_chi_lt_critical_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : p.a = 0) (hb : p.b = 0)
    (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    (hxp :
      ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀
            (fun _ => (minimalEquilibrium p uStar).1) ≤
          intervalDomain.supNorm
            (fun x => u₀ x - (minimalEquilibrium p uStar).1))
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 :=
  intervalDomain_minimalEquilibrium_massStability_of_chi_lt_critical_of_sectorialHypothesis
    p N hsigma_low hsigma_high hpNorm
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    ha hb huStar hχ hxp hexist

/-- Theorem 2.3 positive-equilibrium local branch with the sectorial raw
blocker replaced by the proved spectral-decay bridge plus orbit frontier. -/
theorem intervalDomain_T23_massLocal_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    SupControlsXpSigmaDistance intervalDomain N sigma pNorm eq.1 →
      (∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p eq.1 delta) →
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        eq.1 eq.2 :=
  Theorem_2_3_negative_sensitivity_mass_constrained_formula_branch_of_raw
    intervalDomain unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm hχ ha hb

/-- Ordinary local Theorem 2.3 positive-equilibrium branch with the sectorial
raw blocker replaced by the spectral-orbit frontier. -/
theorem intervalDomain_T23_local_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    SupControlsXpSigmaDistance intervalDomain N sigma pNorm eq.1 →
      (∀ delta > 0, SmallDataGlobalExistence intervalDomain p eq.1 delta) →
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 :=
  Theorem_2_3_negative_sensitivity_local_formula_branch_of_raw
    intervalDomain unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm hχ ha hb

/-- Theorem 2.4 mass-constrained formula branch with
`SectorialLocalExponentialRaw` discharged by the spectral-orbit frontier. -/
theorem intervalDomain_T24_fullFormulaLocal_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm eq.1 →
      (∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p eq.1 delta) →
        LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
        MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
          eq.1 eq.2 :=
  Theorem_2_4_full_stability_formula_branch_of_raw
    intervalDomain unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm ha hb M0

/-- Theorem 2.4 mass-constrained first-mode branch with the sectorial raw
blocker replaced by the spectral-orbit frontier. -/
theorem intervalDomain_T24_fullFirstModeLocal_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm eq.1 →
      (∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p eq.1 delta) →
        LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
        MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
          eq.1 eq.2 :=
  Theorem_2_4_full_stability_first_mode_branch_of_raw
    intervalDomain unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm ha hb M0

/-- Theorem 2.4 ordinary local formula branch with the sectorial raw blocker
replaced by the spectral-orbit frontier. -/
theorem intervalDomain_T24_formulaLocal_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p eq.1 eq.2 →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm eq.1 →
      (∀ delta > 0, SmallDataGlobalExistence intervalDomain p eq.1 delta) →
        LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
        LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 :=
  Theorem_2_4_local_stability_formula_branch_of_raw
    intervalDomain unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm ha hb M0

/-- Theorem 2.4 ordinary local first-mode branch with the sectorial raw blocker
replaced by the spectral-orbit frontier. -/
theorem intervalDomain_T24_firstModeLocal_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    max
        (max (chiStrong1Formula p eq.1 eq.2)
          (chiStrong2Formula p eq.1))
        (max (chiStrong3Formula p M0 eq.1 eq.2)
          (chiStrong4Formula p M0 eq.1)) ≤
      ((1 + eq.2) ^ p.β /
          (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm eq.1 →
      (∀ delta > 0, SmallDataGlobalExistence intervalDomain p eq.1 delta) →
        LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
        LocallyExponentiallyStableFromSup intervalDomain p N eq.1 eq.2 :=
  Theorem_2_4_local_stability_first_mode_branch_of_raw
    intervalDomain unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm ha hb M0

/-- Theorem 2.5 minimal-model mass-constrained formula branch with the
sectorial raw blocker replaced by the spectral-orbit frontier. -/
theorem intervalDomain_T25_fullFormulaLocal_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm
        (minimalEquilibrium p uStar).1 →
      (∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) →
        LinearlyStable unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 ∧
        MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
  Theorem_2_5_full_stability_formula_branch_of_raw
    intervalDomain unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm ha hb hm hβ huStar uBar vLower

/-- Theorem 2.5 minimal-model mass-constrained first-mode branch with the
sectorial raw blocker replaced by the spectral-orbit frontier. -/
theorem intervalDomain_T25_fullFirstModeLocal_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ) :
    chiBeta p ≤
      ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
          (p.ν * p.γ *
            (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
        (p.μ + Real.pi ^ 2) →
      MinimalGlobalStabilityFormulaCondition p uStar uBar vLower →
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm
        (minimalEquilibrium p uStar).1 →
      (∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) →
        LinearlyStable unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 ∧
        MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
  Theorem_2_5_full_stability_first_mode_branch_of_raw
    intervalDomain unitIntervalNeumannSpectrum p N
    unitIntervalNeumannSpectrum_hasNeumannSpectrum
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm ha hb hm hβ huStar uBar vLower

/-- Interval-domain nonminimal convergence-to-exponential upgrade from the
raw Corollary 5.1 exponential frontier.

Point 17 status: conditional theorem frontier.  This theorem does not prove
global convergence/persistence; it upgrades an already supplied
`UniformConvergesInSup` solution to `ExponentialC1Convergence`. -/
theorem intervalDomain_C51_nonminimalExponential_of_raw
    {p : CM2Params}
    {N : StabilityNorms intervalDomain}
    (hraw :
      ConvergenceToExponentialNonminimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hconv :
      UniformConvergesInSup intervalDomain u
        (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence intervalDomain N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  Corollary_5_1_nonminimal_exponential_formula_unitInterval_of_raw
    hraw hm ha hb hχ huv hconv

/-- Interval-domain minimal convergence-to-exponential upgrade from the raw
Corollary 5.1 exponential frontier.  The mass constraint and uniform
convergence assumptions remain explicit. -/
theorem intervalDomain_C51_minimalExponential_of_raw
    {p : CM2Params}
    {N : StabilityNorms intervalDomain}
    (hraw :
      ConvergenceToExponentialMinimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar)
    (hconv :
      UniformConvergesInSup intervalDomain u
        (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence intervalDomain N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  Corollary_5_1_minimal_exponential_formula_unitInterval_of_raw
    hraw hm ha hb huStar hχ huv hmass hconv

/-- Formula-condition nonminimal convergence-to-exponential upgrade on the
unit interval using the first nonzero Neumann mode.  Persistence/global
convergence still has to supply `hconv`; the exponential upgrade is exactly
the raw Corollary 5.1 frontier. -/
theorem intervalDomain_C51_nonminimalFormulaExponential_of_raw
    {p : CM2Params}
    {N : StabilityNorms intervalDomain}
    (hraw :
      ConvergenceToExponentialNonminimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b) (M0 : ℝ)
    (hfirst :
      let eq := positiveEquilibrium p ⟨ha, hb⟩
      max
          (max (chiStrong1Formula p eq.1 eq.2)
            (chiStrong2Formula p eq.1))
          (max (chiStrong3Formula p M0 eq.1 eq.2)
            (chiStrong4Formula p M0 eq.1)) ≤
        ((1 + eq.2) ^ p.β /
            (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
          (p.μ + Real.pi ^ 2))
    (hcond :
      NonminimalGlobalStabilityFormulaCondition p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 M0)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hconv :
      UniformConvergesInSup intervalDomain u
        (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence intervalDomain N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  Corollary_5_1_nonminimal_exponential_formula_condition_firstNonzero_of_raw
    (S := unitIntervalNeumannSpectrum)
    hraw unitIntervalNeumannSpectrum_hasNeumannSpectrum
    hm ha hb M0 hfirst hcond huv hconv

/-- Formula-condition minimal convergence-to-exponential upgrade on the unit
interval using the first nonzero Neumann mode.  This is the honest endpoint
after persistence has supplied uniform convergence. -/
theorem intervalDomain_C51_minimalFormulaExponential_of_raw
    {p : CM2Params}
    {N : StabilityNorms intervalDomain}
    (hraw :
      ConvergenceToExponentialMinimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm_le : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0) (hβ : 1 ≤ p.β)
    {uStar : ℝ} (huStar : 0 < uStar) (uBar vLower : ℝ)
    (hfirst :
      chiBeta p ≤
        ((1 + (minimalEquilibrium p uStar).2) ^ p.β /
            (p.ν * p.γ *
              (minimalEquilibrium p uStar).1 ^ (p.m + p.γ - 1))) *
          (p.μ + Real.pi ^ 2))
    (hcond : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar)
    (hconv :
      UniformConvergesInSup intervalDomain u
        (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence intervalDomain N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  Corollary_5_1_minimal_exponential_formula_condition_firstNonzero_of_raw
    (S := unitIntervalNeumannSpectrum)
    hraw unitIntervalNeumannSpectrum_hasNeumannSpectrum
    hm_le ha hb hβ huStar uBar vLower hfirst hcond huv hmass hconv

/-- Positive-equilibrium stable branch of Paper3 Theorem 2.2 with the full
local-exponential conclusion, not just the intermediate stability package.

The raw sectorial input is discharged by the concrete spectral decay plus the
named nonlinear orbit-comparison frontier. -/
theorem intervalDomain_T22_positiveComplete_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hcontrol :
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm
        (positiveEquilibrium p ⟨ha, hb⟩).1)
    (hexist :
      ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta) :
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    p.χ₀ < C.chiCritical eq.1 →
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
          SupCloseToConstant intervalDomain u₀ eq.1 δ →
            ∃ u v : ℝ → intervalDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
              InitialTrace intervalDomain u₀ u ∧
              ExponentialC1ConvergenceWith intervalDomain N u v
                eq.1 eq.2 A rate := by
  dsimp
  intro hχ
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    hC.positiveEquilibrium_linearlyStable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hχ
  have hlocal :
      LocallyExponentiallyStableFromSup intervalDomain p N
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 :=
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit).locally_from_sup_control
        hsigma_low hsigma_high hpNorm hstable hcontrol hexist
  exact ⟨hstable, hlocal⟩

/-- Minimal-equilibrium stable branch of Paper3 Theorem 2.2 with the full
mass-constrained local-exponential conclusion. -/
theorem intervalDomain_T22_minimalComplete_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    {sigma pNorm uStar : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    (_ha : p.a = 0) (_hb : p.b = 0) (huStar : 0 < uStar)
    (hcontrol :
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm
        (minimalEquilibrium p uStar).1)
    (hexist :
      ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    let eq := minimalEquilibrium p uStar
    p.χ₀ < C.chiCritical uStar →
      LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 ∧
      ∃ δ > 0, ∃ A > 0, ∃ rate > 0,
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
          SupCloseToConstant intervalDomain u₀ eq.1 δ →
          intervalDomain.integral u₀ = intervalDomain.volume * uStar →
            ∃ u v : ℝ → intervalDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
              InitialTrace intervalDomain u₀ u ∧
              ExponentialC1ConvergenceWith intervalDomain N u v
                eq.1 eq.2 A rate := by
  dsimp
  intro hχ
  have hstable :
      LinearlyStable unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
    hC.minimalEquilibrium_linearlyStable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hχ
  have hlocal :
      MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 :=
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit).massConstrained_from_sup_control
        hsigma_low hsigma_high hpNorm hstable hcontrol hexist
  exact ⟨hstable, hlocal⟩

/-- Full interval-domain Paper3 Theorem 2.2 from the audited
critical-spectrum constants and the spectral-orbit frontier. -/
theorem
intervalDomain_Theorem_2_2_criticalSpectrum_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hcontrol :
      ∀ uStar, SupControlsXpSigmaDistance intervalDomain N sigma pNorm uStar)
    (hexist :
      ∀ uStar, ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p uStar delta)
    (hmexist :
      ∀ uStar, ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N C :=
  Theorem_2_2_full_critical_spectrum_of_raw
    unitIntervalNeumannSpectrum_hasNeumannSpectrum hC
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm hcontrol hexist hmexist

/-- `m = 1` slice of the full interval-domain Theorem 2.2 conclusion with
the sectorial raw input discharged by the spectral-orbit frontier. -/
theorem intervalDomain_Theorem_2_2_m_eq_one_of_spectralSemigroupOrbitBound
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (horbit : IntervalDomainSpectralSemigroupOrbitBoundRaw p N)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hcontrol :
      ∀ uStar, SupControlsXpSigmaDistance intervalDomain N sigma pNorm uStar)
    (hexist :
      ∀ uStar, ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p uStar delta)
    (hmexist :
      ∀ uStar, ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta)
    (hm : p.m = 1) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N C :=
  Theorem_2_2_full_m_eq_one_of_raw
    unitIntervalNeumannSpectrum_hasNeumannSpectrum hC
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p N horbit)
    hsigma_low hsigma_high hpNorm hcontrol hexist hmexist hm

/-- Exact remaining local frontiers for a literally unconditional
interval-domain Theorem 2.2 after the linear spectral-decay block has been
discharged.

Point 17 status: conditional frontier.  The first field is the nonlinear
Duhamel/orbit comparison with the proved interval Neumann heat semigroup.  The
second is the interval `sup`-small to `X^σ_p`-small bridge.  The last two are
small-data global-existence frontiers, respectively without and with the mass
constraint. -/
def IntervalDomainTheorem22LocalFrontiers
    (p : CM2Params) (N : StabilityNorms intervalDomain) : Prop :=
  ∃ sigma pNorm : ℝ,
    1 / 2 < sigma ∧ sigma < 1 ∧ 1 < pNorm ∧
    IntervalDomainSpectralSemigroupOrbitBoundRaw p N ∧
    (∀ uStar,
      SupControlsXpSigmaDistance intervalDomain N sigma pNorm uStar) ∧
    (∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta) ∧
    (∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta)

/-- Concrete interval local frontiers for Theorem 2.2.

Compared with `IntervalDomainTheorem22LocalFrontiers`, the `StabilityNorms`
package and the `sup`-to-`X^σ_p` field projection are no longer exposed: the
sectorial interval `X^σ_p` gauge is the concrete sup-distance gauge, so that
control is discharged by
`intervalDomainSectorialStabilityNorms_supControlsXpSigmaDistance`. -/
def IntervalDomainSectorialTheorem22LocalFrontiers
    (p : CM2Params) : Prop :=
  ∃ sigma pNorm : ℝ,
    1 / 2 < sigma ∧ sigma < 1 ∧ 1 < pNorm ∧
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p ∧
    (∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta) ∧
    (∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta)

/-- Full interval-domain Theorem 2.2 from the precise named local frontiers.

This is the strongest theorem available in this file without importing a
nonlinear Duhamel/fixed-point proof.  It no longer assumes
`SectorialLocalExponentialRaw`; the only remaining hypotheses are the
frontiers named in `IntervalDomainTheorem22LocalFrontiers`. -/
theorem intervalDomain_Theorem_2_2_of_localFrontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hfront : IntervalDomainTheorem22LocalFrontiers p N) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N C := by
  rcases hfront with
    ⟨sigma, pNorm, hsigma_low, hsigma_high, hpNorm, horbit,
      hcontrol, hexist, hmexist⟩
  exact
    intervalDomain_Theorem_2_2_criticalSpectrum_of_spectralSemigroupOrbitBound
      p N C hC horbit hsigma_low hsigma_high hpNorm hcontrol hexist hmexist

/-- Concrete interval-domain Theorem 2.2 from the named sectorial local
frontiers.

This is the mainline local-exponential statement in this file: it uses the
unit-interval spectral constants and concrete sectorial stability gauges, and
therefore has no abstract `StabilityNorms` or `Paper3Constants` field
projection in its interface. -/
theorem intervalDomain_Theorem_2_2_sectorialMainline_of_localFrontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfront : IntervalDomainSectorialTheorem22LocalFrontiers p) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) := by
  rcases hfront with
    ⟨sigma, pNorm, hsigma_low, hsigma_high, hpNorm, horbit,
      hexist, hmexist⟩
  exact
    intervalDomain_Theorem_2_2_criticalSpectrum_of_spectralSemigroupOrbitBound
      p intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
      (intervalDomainSectorialPaper3Constants_usesCriticalSpectrum
        p M0 uBar vLower)
      (intervalDomain_spectralSemigroupOrbitBoundRaw_of_sectorialConcrete
        p horbit)
      hsigma_low hsigma_high hpNorm
      (fun uStar =>
        intervalDomainSectorialStabilityNorms_supControlsXpSigmaDistance
          sigma pNorm uStar)
      hexist hmexist

/-- Concrete persistence frontiers for Paper3 Theorem 2.1 on the sectorial
interval mainline.

Point 17 status: frontier.  These are the four raw uniform-persistence inputs
which are not proved by the sectorial/spectral-decay infrastructure in this
file.  The minimal branch uses the concrete constants
`gaussianLowerConst = 1` and `eventualMinimalUBound = fun _ => uBar`. -/
def IntervalDomainSectorialTheorem21PersistenceFrontiers
    (p : CM2Params) (uBar : ℝ) : Prop :=
  UniformPersistencePart1Raw intervalDomain p ∧
    UniformPersistencePart2Raw intervalDomain p ∧
    UniformPersistencePart3Raw intervalDomain p ∧
    UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1

/-- Paper3 Theorem 2.1 on the sectorial interval mainline from the exact
persistence frontiers.

This removes `Paper3Constants` field projections from the theorem interface;
the only remaining inputs are the raw persistence estimates themselves. -/
theorem intervalDomain_Theorem_2_1_sectorialMainline_of_persistenceFrontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfront : IntervalDomainSectorialTheorem21PersistenceFrontiers p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) := by
  rcases hfront with ⟨h1, h2, h3, h4⟩
  refine Theorem_2_1.of_parts h1 h2 h3 ?_
  intro ha hb hm hβ hχ0 hχ uStar huStar u v huv hmass
  have hbound :=
    h4 (by norm_num : (0 : ℝ) < 1) ha hb hm hβ hχ0 hχ
      uStar huStar u v huv hmass
  simpa [intervalDomainSectorialPaper3Constants, minimalVLowerFormula] using
    hbound

/-- Exact remaining frontiers for the user-facing sectorial interval mainline
`Theorem_2_2` local exponential stability together with `Theorem_2_1`
persistence.

The linear spectral-decay part has already been discharged in this file.
What remains here is precisely the nonlinear orbit comparison, small-data
global existence, and the four persistence estimates. -/
def IntervalDomainSectorialTheorem21And22Frontiers
    (p : CM2Params) (uBar : ℝ) : Prop :=
  IntervalDomainSectorialTheorem22LocalFrontiers p ∧
    IntervalDomainSectorialTheorem21PersistenceFrontiers p uBar

/-- Sectorial interval mainline closure: local exponential stability
(`Theorem_2_2`) and persistence (`Theorem_2_1`) from the exact remaining
frontiers.

This is the honest endpoint currently available in `IntervalDomainSectorial`.
A theorem with no frontier hypotheses would require proofs of
`IntervalDomainSectorialTheorem21And22Frontiers`, in particular nonlinear
Duhamel/orbit control and small-data global existence on `intervalDomain`. -/
theorem intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_frontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfront : IntervalDomainSectorialTheorem21And22Frontiers p uBar) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) ∧
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) := by
  rcases hfront with ⟨h22, h21⟩
  exact
    ⟨intervalDomain_Theorem_2_2_sectorialMainline_of_localFrontiers
        p M0 uBar vLower h22,
      intervalDomain_Theorem_2_1_sectorialMainline_of_persistenceFrontiers
        p M0 uBar vLower h21⟩

/-- The literal unconditional interval-domain target for the sectorial
mainline: Paper3 Theorem 2.2 local exponential stability together with Paper3
Theorem 2.1 persistence, both using the concrete interval constants and
sectorial stability gauges.

Point 17 status: target statement.  This definition has no hidden hypotheses;
the theorem below records the exact remaining frontiers whose proof would
close it. -/
def IntervalDomainSectorialTheorem21And22UnconditionalTarget
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop :=
  Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) ∧
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower)

/-- Closure of the literal unconditional target from the exact remaining
frontiers.

This is deliberately not stated without `hfront`: the current imported
interval-domain infrastructure still does not prove nonlinear Duhamel/orbit
control, small-data global existence, or the four uniform-persistence
frontiers. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_frontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfront : IntervalDomainSectorialTheorem21And22Frontiers p uBar) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_frontiers
    p M0 uBar vLower hfront

/-- The Theorem 2.2 component of the concrete interval mainline target once
the exact frontiers are closed. -/
theorem intervalDomain_Theorem_2_2_sectorialMainline_of_closedFrontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfront : IntervalDomainSectorialTheorem21And22Frontiers p uBar) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_sectorialMainline_unconditionalTarget_of_frontiers
    p M0 uBar vLower hfront).1

/-- The Theorem 2.1 component of the concrete interval mainline target once
the exact frontiers are closed. -/
theorem intervalDomain_Theorem_2_1_sectorialMainline_of_closedFrontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfront : IntervalDomainSectorialTheorem21And22Frontiers p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_sectorialMainline_unconditionalTarget_of_frontiers
    p M0 uBar vLower hfront).2

/-- Paper2-style existence/stability package for the interval-domain
Theorem 2.2 sectorial mainline.

This is not a theorem-shaped assumption: the fields are the concrete analytic
facts still missing after the spectral-decay bridge has been proved, namely
the nonlinear orbit comparison and the two small-data global Cauchy existence
branches. -/
structure IntervalDomainSectorialTheorem22Existence
    (p : CM2Params) where
  sigma : ℝ
  pNorm : ℝ
  sigma_low : 1 / 2 < sigma
  sigma_high : sigma < 1
  pNorm_gt_one : 1 < pNorm
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  smallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta
  massConstrainedSmallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta

/-- The Paper2-style Theorem 2.2 existence package supplies exactly the local
frontiers consumed by the lower-level sectorial wrapper. -/
theorem IntervalDomainSectorialTheorem22Existence.to_localFrontiers
    {p : CM2Params}
    (h : IntervalDomainSectorialTheorem22Existence p) :
    IntervalDomainSectorialTheorem22LocalFrontiers p :=
  ⟨h.sigma, h.pNorm, h.sigma_low, h.sigma_high, h.pNorm_gt_one,
    h.spectralSemigroupOrbitBound, h.smallDataGlobal,
    h.massConstrainedSmallDataGlobal⟩

/-- Paper2-style persistence package for the interval-domain Theorem 2.1
sectorial mainline.

Point 17 status: this is not discharged by the sectorial semigroup theory.
The four fields are the genuine uniform-persistence estimates needed by
Paper3 Theorem 2.1 on `intervalDomain`. -/
structure IntervalDomainSectorialTheorem21Persistence
    (p : CM2Params) (uBar : ℝ) where
  part1 : UniformPersistencePart1Raw intervalDomain p
  part2 : UniformPersistencePart2Raw intervalDomain p
  part3 : UniformPersistencePart3Raw intervalDomain p
  part4 : UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1

/-- The Paper2-style persistence package supplies the lower-level persistence
frontiers. -/
theorem IntervalDomainSectorialTheorem21Persistence.to_persistenceFrontiers
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialTheorem21Persistence p uBar) :
    IntervalDomainSectorialTheorem21PersistenceFrontiers p uBar :=
  ⟨h.part1, h.part2, h.part3, h.part4⟩

/-- Combined Paper3 interval-domain mainline package.

This is the Paper2-consistent reduction point for B4: Theorem 2.2 is reduced
to a concrete sectorial existence/stability package, and Theorem 2.1 is
reduced to the concrete persistence package.  A no-assumption theorem would
require constructing this package from PDE analysis. -/
structure IntervalDomainSectorialMainlineExistence
    (p : CM2Params) (uBar : ℝ) where
  localStability : IntervalDomainSectorialTheorem22Existence p
  persistence : IntervalDomainSectorialTheorem21Persistence p uBar

/-- The combined mainline package is exactly the lower-level frontier package
already consumed by the sectorial mainline theorem. -/
theorem IntervalDomainSectorialMainlineExistence.to_frontiers
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineExistence p uBar) :
    IntervalDomainSectorialTheorem21And22Frontiers p uBar :=
  ⟨h.localStability.to_localFrontiers,
    h.persistence.to_persistenceFrontiers⟩

/-- Interval-domain Paper3 Theorem 2.2 from the Paper2-style sectorial
existence/stability package. -/
theorem intervalDomain_Theorem_2_2_sectorialMainline_of_existence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hexist : IntervalDomainSectorialTheorem22Existence p) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_sectorialMainline_of_localFrontiers
    p M0 uBar vLower hexist.to_localFrontiers

/-- Interval-domain Paper3 Theorem 2.1 from the concrete persistence package. -/
theorem intervalDomain_Theorem_2_1_sectorialMainline_of_persistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hpersist : IntervalDomainSectorialTheorem21Persistence p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_sectorialMainline_of_persistenceFrontiers
    p M0 uBar vLower hpersist.to_persistenceFrontiers

/-- Paper2-consistent interval-domain endpoint for Paper3 Theorems 2.1 and
2.2: the user-facing sectorial mainline reduced to the concrete existence and
persistence packages. -/
theorem intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_existence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hexist : IntervalDomainSectorialMainlineExistence p uBar) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) ∧
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_frontiers
    p M0 uBar vLower hexist.to_frontiers

/-- The Theorem 2.2 component of the Paper2-style mainline existence
package. -/
theorem intervalDomain_Theorem_2_2_sectorialMainline_of_mainlineExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hexist : IntervalDomainSectorialMainlineExistence p uBar) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_existence
    p M0 uBar vLower hexist).1

/-- The Theorem 2.1 component of the Paper2-style mainline existence
package. -/
theorem intervalDomain_Theorem_2_1_sectorialMainline_of_mainlineExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hexist : IntervalDomainSectorialMainlineExistence p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  (intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_existence
    p M0 uBar vLower hexist).2

/-- The literal no-hidden-field target, reduced to the Paper2-style mainline
existence package. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_existence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hexist : IntervalDomainSectorialMainlineExistence p uBar) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_frontiers
    p M0 uBar vLower hexist.to_frontiers

/-- Audit record for the B4 interval-domain sectorial mainline.

Coverage:
* `StabilityNorms` is discharged in the main endpoint to the concrete
  `intervalDomainSectorialStabilityNorms`; no abstract norm package is an
  argument of the audited theorem.
* `Paper3Constants` is discharged in the main endpoint to
  `intervalDomainSectorialPaper3Constants p M0 uBar vLower`; the only
  remaining scalar parameters are the intended formula parameters
  `M0`, `uBar`, and `vLower`.
* `CompactnessData` does not occur in the interval-domain Theorem 2.1/2.2
  sectorial endpoint.  Compactness/upper-envelope inputs belong to the
  separate stability-chain/Lemma 3.4 path, not to this T2.1/T2.2 kernel.
* The remaining input is exactly `IntervalDomainSectorialMainlineExistence`:
  the spectral-orbit comparison, ordinary and mass-constrained small-data
  global existence, and the four uniform-persistence estimates. -/
structure IntervalDomainSectorialMainlineCoverage
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop where
  theorem22Concrete :
    ∀ _hexist : IntervalDomainSectorialMainlineExistence p uBar,
      Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
  theorem21Concrete :
    ∀ _hexist : IntervalDomainSectorialMainlineExistence p uBar,
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
  targetOnlyNeedsExistence :
    ∀ _hexist : IntervalDomainSectorialMainlineExistence p uBar,
      IntervalDomainSectorialTheorem21And22UnconditionalTarget
        p M0 uBar vLower

/-- Coverage proof for the audited interval-domain sectorial mainline.

This theorem is the precise reduces-to-existence kernel: the endpoint has
concrete interval norms and concrete interval Paper3 constants; the only
nontrivial premise is the `IntervalDomainSectorialMainlineExistence` package.
It deliberately does not claim that package has been constructed. -/
theorem intervalDomain_sectorialMainline_reducesToExistence_coverage
    (p : CM2Params) (M0 uBar vLower : ℝ) :
    IntervalDomainSectorialMainlineCoverage p M0 uBar vLower := by
  refine ⟨?_, ?_, ?_⟩
  · intro hexist
    exact
      intervalDomain_Theorem_2_2_sectorialMainline_of_mainlineExistence
        p M0 uBar vLower hexist
  · intro hexist
    exact
      intervalDomain_Theorem_2_1_sectorialMainline_of_mainlineExistence
        p M0 uBar vLower hexist
  · intro hexist
    exact
      intervalDomain_sectorialMainline_unconditionalTarget_of_existence
        p M0 uBar vLower hexist

/-- Canonical reduces-to-existence kernel for the B4 interval-domain sectorial
mainline.

Compared with `IntervalDomainSectorialMainlineExistence`, this package fixes
the harmless sectorial parameter witnesses to `sigma = 3/4` and `pNorm = 2`.
The fields left here are exactly the analytic content still needed for the
interval-domain Theorem 2.1/2.2 endpoint: nonlinear orbit control, ordinary
and mass-constrained small-data global existence, and the four persistence
estimates. -/
structure IntervalDomainSectorialMainlineCoreExistence
    (p : CM2Params) (uBar : ℝ) where
  spectralSemigroupOrbitBound :
    IntervalDomainSectorialSpectralSemigroupOrbitBoundRaw p
  smallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      SmallDataGlobalExistence intervalDomain p uStar delta
  massConstrainedSmallDataGlobal :
    ∀ uStar, ∀ delta > 0,
      MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta
  persistencePart1 : UniformPersistencePart1Raw intervalDomain p
  persistencePart2 : UniformPersistencePart2Raw intervalDomain p
  persistencePart3 : UniformPersistencePart3Raw intervalDomain p
  persistencePart4 :
    UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1

/-- Expand the canonical core package to the earlier Paper2-style mainline
existence package. -/
def IntervalDomainSectorialMainlineCoreExistence.to_mainlineExistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainSectorialMainlineExistence p uBar where
  localStability :=
    { sigma := (3 / 4 : ℝ)
      pNorm := (2 : ℝ)
      sigma_low := by norm_num
      sigma_high := by norm_num
      pNorm_gt_one := by norm_num
      spectralSemigroupOrbitBound := h.spectralSemigroupOrbitBound
      smallDataGlobal := h.smallDataGlobal
      massConstrainedSmallDataGlobal := h.massConstrainedSmallDataGlobal }
  persistence :=
    { part1 := h.persistencePart1
      part2 := h.persistencePart2
      part3 := h.persistencePart3
      part4 := h.persistencePart4 }

/-- The canonical core package supplies exactly the local-stability existence
package consumed by the Theorem 2.2 sectorial mainline. -/
def IntervalDomainSectorialMainlineCoreExistence.to_theorem22Existence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainSectorialTheorem22Existence p :=
  h.to_mainlineExistence.localStability

/-- The canonical core package supplies exactly the persistence package consumed
by the Theorem 2.1 sectorial mainline. -/
theorem IntervalDomainSectorialMainlineCoreExistence.to_theorem21Persistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainSectorialTheorem21Persistence p uBar :=
  h.to_mainlineExistence.persistence

/-- Explicit constructor for downstream files: the canonical core existence
kernel expands to the Paper2-style sectorial mainline existence package. -/
def intervalDomain_sectorialMainlineExistence_of_coreExistence
    {p : CM2Params} {uBar : ℝ}
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainSectorialMainlineExistence p uBar :=
  hcore.to_mainlineExistence

/-- Explicit core-fact handoff for downstream StabilityChain files.  This file cannot
state the `IntervalDomainStabilityChain...` target directly, because the
StabilityChain file imports this sectorial file.  The exported value is the
sectorial package that the downstream target already consumes. -/
def intervalDomain_sectorialMainlineExistence_of_coreExistenceFact
    {p : CM2Params} {uBar : ℝ}
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    IntervalDomainSectorialMainlineExistence p uBar :=
  hcore.out.to_mainlineExistence

/-- Sectorial-side handoff package for the downstream StabilityChain target.
It exposes the already-expanded mainline existence package and its two
components, while keeping the remaining frontier at the canonical core
existence level. -/
structure IntervalDomainSectorialStabilityChainHandoff
    (p : CM2Params) (uBar : ℝ) where
  mainlineExistence : IntervalDomainSectorialMainlineExistence p uBar
  localStability : IntervalDomainSectorialTheorem22Existence p
  persistence : IntervalDomainSectorialTheorem21Persistence p uBar

/-- Build the sectorial-to-StabilityChain handoff from the canonical core
existence kernel. -/
def intervalDomain_sectorialStabilityChainHandoff_of_coreExistence
    {p : CM2Params} {uBar : ℝ}
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainSectorialStabilityChainHandoff p uBar where
  mainlineExistence := hcore.to_mainlineExistence
  localStability := hcore.to_theorem22Existence
  persistence := hcore.to_theorem21Persistence

/-- Fact-facing version of the sectorial-to-StabilityChain handoff. -/
def intervalDomain_sectorialStabilityChainHandoff_of_coreExistenceFact
    {p : CM2Params} {uBar : ℝ}
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    IntervalDomainSectorialStabilityChainHandoff p uBar :=
  intervalDomain_sectorialStabilityChainHandoff_of_coreExistence hcore.out

/-- Theorem 2.2 on the interval from the canonical core existence kernel, with
all norms and constants concrete. -/
theorem intervalDomain_Theorem_2_2_sectorialMainline_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_sectorialMainline_of_mainlineExistence
    p M0 uBar vLower hcore.to_mainlineExistence

/-- Theorem 2.1 on the interval from the canonical core existence kernel, with
all constants concrete. -/
theorem intervalDomain_Theorem_2_1_sectorialMainline_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_sectorialMainline_of_mainlineExistence
    p M0 uBar vLower hcore.to_mainlineExistence

/-- Combined interval-domain Theorem 2.1/2.2 endpoint from the canonical core
existence kernel. -/
theorem intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) ∧
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_existence
    p M0 uBar vLower hcore.to_mainlineExistence

/-- The literal no-hidden-field target from the canonical core existence
kernel. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hcore : IntervalDomainSectorialMainlineCoreExistence p uBar) :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_existence
    p M0 uBar vLower hcore.to_mainlineExistence

/-- Instance-facing endpoint: once the canonical core existence kernel is
registered, the interval-domain Theorem 2.1/2.2 sectorial mainline has no
explicit frontier argument. -/
theorem intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) ∧
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_coreExistence
    p M0 uBar vLower hcore.out

/-- Instance-facing Theorem 2.2 component from the canonical core existence
kernel. -/
theorem intervalDomain_Theorem_2_2_sectorialMainline_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_sectorialMainline_of_coreExistence
    p M0 uBar vLower hcore.out

/-- Instance-facing Theorem 2.1 component from the canonical core existence
kernel. -/
theorem intervalDomain_Theorem_2_1_sectorialMainline_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    Theorem_2_1 intervalDomain p
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_sectorialMainline_of_coreExistence
    p M0 uBar vLower hcore.out

/-- Instance-facing literal target from the canonical core existence kernel.
This is the clean handoff point for a future sb-ode/existence import: once it
registers the core existence fact, this endpoint has no explicit frontier
argument and all norms/constants are concrete. -/
theorem intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistenceFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    [hcore : Fact (IntervalDomainSectorialMainlineCoreExistence p uBar)] :
    IntervalDomainSectorialTheorem21And22UnconditionalTarget
      p M0 uBar vLower :=
  intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
    p M0 uBar vLower hcore.out

/-- Clean B4 coverage record at the canonical core-existence level.

The theorem fields below have no abstract `StabilityNorms`,
`CompactnessData`, or `Paper3Constants` arguments.  They expose only the core
existence kernel as the remaining premise. -/
structure IntervalDomainSectorialCoreReductionCoverage
    (p : CM2Params) (M0 uBar vLower : ℝ) : Prop where
  theorem22 :
    ∀ _hcore : IntervalDomainSectorialMainlineCoreExistence p uBar,
      Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainSectorialStabilityNorms
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
  theorem21 :
    ∀ _hcore : IntervalDomainSectorialMainlineCoreExistence p uBar,
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
  combined :
    ∀ _hcore : IntervalDomainSectorialMainlineCoreExistence p uBar,
      Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
          intervalDomainSectorialStabilityNorms
          (intervalDomainSectorialPaper3Constants p M0 uBar vLower) ∧
        Theorem_2_1 intervalDomain p
          (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
  literalTarget :
    ∀ _hcore : IntervalDomainSectorialMainlineCoreExistence p uBar,
      IntervalDomainSectorialTheorem21And22UnconditionalTarget
        p M0 uBar vLower

/-- Proof that the interval-domain Theorem 2.1/2.2 sectorial endpoint is cleanly
reduced to canonical core existence. -/
theorem intervalDomain_sectorialMainline_coreReduction_coverage
    (p : CM2Params) (M0 uBar vLower : ℝ) :
    IntervalDomainSectorialCoreReductionCoverage p M0 uBar vLower := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcore
    exact
      intervalDomain_Theorem_2_2_sectorialMainline_of_coreExistence
        p M0 uBar vLower hcore
  · intro hcore
    exact
      intervalDomain_Theorem_2_1_sectorialMainline_of_coreExistence
        p M0 uBar vLower hcore
  · intro hcore
    exact
      intervalDomain_Theorem_2_1_and_2_2_sectorialMainline_of_coreExistence
        p M0 uBar vLower hcore
  · intro hcore
    exact
      intervalDomain_sectorialMainline_unconditionalTarget_of_coreExistence
        p M0 uBar vLower hcore

/-- Persistence plus the raw nonminimal exponential-upgrade frontier gives
the per-solution exponential conclusion of Corollary 5.1.

This deliberately does not claim the uniform constants required by
`Theorem_2_3`; `ConvergenceToExponentialNonminimalRaw` exposes constants
after a particular solution and its uniform convergence have been supplied. -/
theorem intervalDomain_C51_nonminimal_of_persistence_raw
    {p : CM2Params}
    {N : StabilityNorms intervalDomain}
    {ha : 0 < p.a} {hb : 0 < p.b}
    (hglobal :
      GloballyAsymptoticallyStableNonminimal intervalDomain p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hraw :
      ConvergenceToExponentialNonminimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ExponentialC1Convergence intervalDomain N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  intervalDomain_C51_nonminimalExponential_of_raw
    hraw hm ha hb hχ huv (hglobal u v huv)

/-- Minimal-model persistence plus the raw exponential-upgrade frontier gives
the per-solution exponential conclusion of Corollary 5.1. -/
theorem intervalDomain_C51_minimal_of_persistence_raw
    {p : CM2Params}
    {N : StabilityNorms intervalDomain}
    {uStar : ℝ}
    (hglobal :
      GloballyAsymptoticallyStableMinimal intervalDomain p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2)
    (hraw :
      ConvergenceToExponentialMinimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar) :
    ExponentialC1Convergence intervalDomain N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  intervalDomain_C51_minimalExponential_of_raw hraw hm ha hb huStar hχ huv
    hmass
    (hglobal u v huv (by
      simpa [minimalEquilibrium_fst_eq] using hmass))

/-- Theorem 2.1(1) extracted on the interval: any positive global bounded
solution is eventually uniformly positive in both components. -/
theorem intervalDomain_Theorem_2_1_part1_persistence
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h21 : Theorem_2_1 intervalDomain p C)
    (hm : 1 ≤ p.m)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∃ δu > 0, EventuallyLowerBound intervalDomain u δu ∧
      EventuallyLowerBound intervalDomain v (p.ν / p.μ * δu ^ p.γ) :=
  h21.1 hm u v huv

/-- Theorem 2.1(2) extracted on the interval for the `m = 1`, positive
logistic branch. -/
theorem intervalDomain_Theorem_2_1_part2_persistence
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h21 : Theorem_2_1 intervalDomain p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    let lowerU :=
      ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^
        (1 / p.α)
    EventuallyLowerBound intervalDomain u lowerU ∧
      EventuallyLowerBound intervalDomain v (p.ν / p.μ * lowerU ^ p.γ) :=
  h21.2.1 ha hb hχ0 hm hβ hχ u v huv

/-- Theorem 2.1(3) extracted on the interval for the superlinear positive
logistic branch. -/
theorem intervalDomain_Theorem_2_1_part3_persistence
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h21 : Theorem_2_1 intervalDomain p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : 1 < p.m) (hβ : 1 ≤ p.β)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    let lowerU :=
      min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
        max (1 / (p.m - 1)) (1 / p.α)
    EventuallyLowerBound intervalDomain u lowerU ∧
      EventuallyLowerBound intervalDomain v (p.ν / p.μ * lowerU ^ p.γ) :=
  h21.2.2.1 ha hb hχ0 hm hβ u v huv

/-- Theorem 2.1(4) extracted on the interval for the minimal model. -/
theorem intervalDomain_Theorem_2_1_part4_persistence
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    (h21 : Theorem_2_1 intervalDomain p C)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1)
    (hβ : 1 ≤ p.β) (hχ0 : 0 < p.χ₀)
    (hχ :
      p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {uStar : ℝ} (huStar : 0 < uStar)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar) :
    EventuallyLowerBound intervalDomain v
      (minimalVLowerFormula
        C.gaussianLowerConst p.γ uStar (C.eventualMinimalUBound uStar)) :=
  h21.2.2.2 ha hb hm hβ hχ0 hχ uStar huStar u v huv hmass

/-- Theorem 2.1 persistence plus the nonminimal global-convergence frontier
and raw Corollary 5.1 upgrade give persistence together with exponential
convergence for the same solution. -/
theorem intervalDomain_C51_nonminimal_of_T21_persistence_raw
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    {N : StabilityNorms intervalDomain}
    {ha : 0 < p.a} {hb : 0 < p.b}
    (h21 : Theorem_2_1 intervalDomain p C)
    (hglobal :
      GloballyAsymptoticallyStableNonminimal intervalDomain p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hraw :
      ConvergenceToExponentialNonminimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    (∃ δu > 0, EventuallyLowerBound intervalDomain u δu ∧
      EventuallyLowerBound intervalDomain v (p.ν / p.μ * δu ^ p.γ)) ∧
    ExponentialC1Convergence intervalDomain N u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  refine ⟨?_, ?_⟩
  · exact intervalDomain_Theorem_2_1_part1_persistence h21 hm huv
  · exact intervalDomain_C51_nonminimal_of_persistence_raw
      (ha := ha) (hb := hb) hglobal hraw hm hχ huv

/-- Theorem 2.1 persistence plus the minimal global-convergence frontier and
raw Corollary 5.1 upgrade give persistence together with exponential
convergence for the same mass-constrained solution. -/
theorem intervalDomain_C51_minimal_of_T21_persistence_raw
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    {N : StabilityNorms intervalDomain} {uStar : ℝ}
    (h21 : Theorem_2_1 intervalDomain p C)
    (hglobal :
      GloballyAsymptoticallyStableMinimal intervalDomain p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2)
    (hraw :
      ConvergenceToExponentialMinimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar) :
    (∃ δu > 0, EventuallyLowerBound intervalDomain u δu ∧
      EventuallyLowerBound intervalDomain v (p.ν / p.μ * δu ^ p.γ)) ∧
    ExponentialC1Convergence intervalDomain N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  refine ⟨?_, ?_⟩
  · exact intervalDomain_Theorem_2_1_part1_persistence h21 hm huv
  · exact intervalDomain_C51_minimal_of_persistence_raw
      (uStar := uStar) hglobal hraw hm ha hb huStar hχ huv hmass

/-- The minimal Theorem 2.1(4) lower bound paired with the raw Corollary 5.1
exponential upgrade.  This records the exact endpoint currently available
before proving the remaining global-convergence frontier. -/
theorem intervalDomain_C51_minimal_of_T21_part4_raw
    {p : CM2Params} {C : Paper3Constants intervalDomain p}
    {N : StabilityNorms intervalDomain} {uStar : ℝ}
    (h21 : Theorem_2_1 intervalDomain p C)
    (hglobal :
      GloballyAsymptoticallyStableMinimal intervalDomain p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2)
    (hraw :
      ConvergenceToExponentialMinimalRaw intervalDomain p N.c1Distance
        (fun uStar =>
          paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
            (p.ν / p.μ * uStar ^ p.γ)))
    (hm_le : 1 ≤ p.m)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1)
    (hβ : 1 ≤ p.β) (hχ0 : 0 < p.χ₀)
    (hχsmall :
      p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    (huStar : 0 < uStar)
    (hχcritical :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar) :
    EventuallyLowerBound intervalDomain v
      (minimalVLowerFormula
        C.gaussianLowerConst p.γ uStar (C.eventualMinimalUBound uStar)) ∧
    ExponentialC1Convergence intervalDomain N u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  refine ⟨?_, ?_⟩
  · exact
      intervalDomain_Theorem_2_1_part4_persistence h21 ha hb hm hβ hχ0
        hχsmall huStar huv hmass
  · exact
      intervalDomain_C51_minimal_of_persistence_raw
        (uStar := uStar) hglobal hraw hm_le ha hb huStar hχcritical huv
        hmass

/-- Concrete nonminimal convergence-to-exponential frontier for the sectorial
interval mainline. -/
def IntervalDomainSectorialConvergenceToExponentialNonminimalRaw
    (p : CM2Params) : Prop :=
  ConvergenceToExponentialNonminimalRaw intervalDomain p
    intervalDomainSectorialC1Distance
    (fun uStar =>
      paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
        (p.ν / p.μ * uStar ^ p.γ))

/-- Concrete minimal convergence-to-exponential frontier for the sectorial
interval mainline. -/
def IntervalDomainSectorialConvergenceToExponentialMinimalRaw
    (p : CM2Params) : Prop :=
  ConvergenceToExponentialMinimalRaw intervalDomain p
    intervalDomainSectorialC1Distance
    (fun uStar =>
      paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar
        (p.ν / p.μ * uStar ^ p.γ))

/-- Theorem 2.1(1) on the concrete sectorial interval constants. -/
theorem intervalDomain_Theorem_2_1_part1_sectorialMainline
    {p : CM2Params} {M0 uBar vLower : ℝ}
    (h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower))
    (hm : 1 ≤ p.m)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∃ δu > 0, EventuallyLowerBound intervalDomain u δu ∧
      EventuallyLowerBound intervalDomain v (p.ν / p.μ * δu ^ p.γ) :=
  intervalDomain_Theorem_2_1_part1_persistence h21 hm huv

/-- Theorem 2.1(4) on the concrete sectorial interval constants, with the
minimal lower-bound formula no longer projected from a `Paper3Constants`
field. -/
theorem intervalDomain_Theorem_2_1_part4_sectorialMainline
    {p : CM2Params} {M0 uBar vLower : ℝ}
    (h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower))
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1)
    (hβ : 1 ≤ p.β) (hχ0 : 0 < p.χ₀)
    (hχ :
      p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {uStar : ℝ} (huStar : 0 < uStar)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar) :
    EventuallyLowerBound intervalDomain v
      (minimalVLowerFormula 1 p.γ uStar uBar) := by
  simpa [intervalDomainSectorialPaper3Constants] using
    intervalDomain_Theorem_2_1_part4_persistence
      (C := intervalDomainSectorialPaper3Constants p M0 uBar vLower)
      h21 ha hb hm hβ hχ0 hχ huStar huv hmass

/-- Concrete C5.1 nonminimal exponential upgrade with no abstract
`StabilityNorms.c1Distance` projection in the hypothesis. -/
theorem intervalDomain_C51_nonminimalExponential_of_sectorialRaw
    {p : CM2Params}
    (hraw : IntervalDomainSectorialConvergenceToExponentialNonminimalRaw p)
    (hm : 1 ≤ p.m) (ha : 0 < p.a) (hb : 0 < p.b)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hconv :
      UniformConvergesInSup intervalDomain u
        (positiveEquilibrium p ⟨ha, hb⟩).1) :
    ExponentialC1Convergence intervalDomain
      intervalDomainSectorialStabilityNorms u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 :=
  intervalDomain_C51_nonminimalExponential_of_raw
    (N := intervalDomainSectorialStabilityNorms)
    hraw hm ha hb hχ huv hconv

/-- Concrete C5.1 minimal exponential upgrade with no abstract
`StabilityNorms.c1Distance` projection in the hypothesis. -/
theorem intervalDomain_C51_minimalExponential_of_sectorialRaw
    {p : CM2Params}
    (hraw : IntervalDomainSectorialConvergenceToExponentialMinimalRaw p)
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar)
    (hconv :
      UniformConvergesInSup intervalDomain u
        (minimalEquilibrium p uStar).1) :
    ExponentialC1Convergence intervalDomain
      intervalDomainSectorialStabilityNorms u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 :=
  intervalDomain_C51_minimalExponential_of_raw
    (N := intervalDomainSectorialStabilityNorms)
    hraw hm ha hb huStar hχ huv hmass hconv

/-- Concrete sectorial mainline: Theorem 2.1 persistence, nonminimal global
convergence, and the concrete raw C5.1 frontier give persistence plus
exponential convergence for the same solution. -/
theorem intervalDomain_C51_nonminimal_of_T21_sectorialMainline
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {ha : 0 < p.a} {hb : 0 < p.b}
    (h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower))
    (hglobal :
      GloballyAsymptoticallyStableNonminimal intervalDomain p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2)
    (hraw : IntervalDomainSectorialConvergenceToExponentialNonminimalRaw p)
    (hm : 1 ≤ p.m)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    (∃ δu > 0, EventuallyLowerBound intervalDomain u δu ∧
      EventuallyLowerBound intervalDomain v (p.ν / p.μ * δu ^ p.γ)) ∧
    ExponentialC1Convergence intervalDomain
      intervalDomainSectorialStabilityNorms u v
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 := by
  refine ⟨?_, ?_⟩
  · exact intervalDomain_Theorem_2_1_part1_sectorialMainline h21 hm huv
  · exact intervalDomain_C51_nonminimalExponential_of_sectorialRaw
      hraw hm ha hb hχ huv (hglobal u v huv)

/-- Concrete sectorial mainline for the minimal mass-constrained branch:
Theorem 2.1 persistence, minimal global convergence, and the concrete raw
C5.1 frontier give persistence plus exponential convergence. -/
theorem intervalDomain_C51_minimal_of_T21_sectorialMainline
    {p : CM2Params} {M0 uBar vLower uStar : ℝ}
    (h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower))
    (hglobal :
      GloballyAsymptoticallyStableMinimal intervalDomain p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2)
    (hraw : IntervalDomainSectorialConvergenceToExponentialMinimalRaw p)
    (hm : 1 ≤ p.m) (ha : p.a = 0) (hb : p.b = 0)
    (huStar : 0 < uStar)
    (hχ :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar) :
    (∃ δu > 0, EventuallyLowerBound intervalDomain u δu ∧
      EventuallyLowerBound intervalDomain v (p.ν / p.μ * δu ^ p.γ)) ∧
    ExponentialC1Convergence intervalDomain
      intervalDomainSectorialStabilityNorms u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  refine ⟨?_, ?_⟩
  · exact intervalDomain_Theorem_2_1_part1_sectorialMainline h21 hm huv
  · exact intervalDomain_C51_minimalExponential_of_sectorialRaw
      hraw hm ha hb huStar hχ huv hmass
      (hglobal u v huv (by
        simpa [minimalEquilibrium_fst_eq] using hmass))

/-- Concrete minimal Theorem 2.1(4) persistence paired with concrete C5.1
exponential convergence. -/
theorem intervalDomain_C51_minimal_of_T21_part4_sectorialMainline
    {p : CM2Params} {M0 uBar vLower uStar : ℝ}
    (h21 :
      Theorem_2_1 intervalDomain p
        (intervalDomainSectorialPaper3Constants p M0 uBar vLower))
    (hglobal :
      GloballyAsymptoticallyStableMinimal intervalDomain p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2)
    (hraw : IntervalDomainSectorialConvergenceToExponentialMinimalRaw p)
    (hm_le : 1 ≤ p.m)
    (ha : p.a = 0) (hb : p.b = 0) (hm : p.m = 1)
    (hβ : 1 ≤ p.β) (hχ0 : 0 < p.χ₀)
    (hχsmall :
      p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    (huStar : 0 < uStar)
    (hχcritical :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hmass : HasInitialMass intervalDomain u uStar) :
    EventuallyLowerBound intervalDomain v
      (minimalVLowerFormula 1 p.γ uStar uBar) ∧
    ExponentialC1Convergence intervalDomain
      intervalDomainSectorialStabilityNorms u v
      (minimalEquilibrium p uStar).1
      (minimalEquilibrium p uStar).2 := by
  refine ⟨?_, ?_⟩
  · exact
      intervalDomain_Theorem_2_1_part4_sectorialMainline h21 ha hb hm hβ
        hχ0 hχsmall huStar huv hmass
  · exact intervalDomain_C51_minimalExponential_of_sectorialRaw
      hraw hm_le ha hb huStar hχcritical huv hmass
      (hglobal u v huv (by
        simpa [minimalEquilibrium_fst_eq] using hmass))

/-- Theorem 2.3 from explicit persistence and uniform exponential-upgrade
frontiers on the interval.

The uniform `A, rate` frontier is stronger than the raw Corollary 5.1 upgrade;
it is kept explicit because raw convergence-to-exponential gives constants
only after a particular solution is supplied. -/
theorem intervalDomain_Theorem_2_3_of_persistence_exp_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (hglobalNonminimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          GloballyAsymptoticallyStableNonminimal intervalDomain p
            eq.1 eq.2)
    (hglobalMinimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          GloballyAsymptoticallyStableMinimal intervalDomain p
            eq.1 eq.2)
    (hExpNonminimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
              UniformConvergesInSup intervalDomain u eq.1 →
                ExponentialC1ConvergenceWith intervalDomain N u v
                  eq.1 eq.2 A rate)
    (hExpMinimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
              UniformConvergesInSup intervalDomain u eq.1 →
                ExponentialC1ConvergenceWith intervalDomain N u v
                  eq.1 eq.2 A rate) :
    Theorem_2_3 intervalDomain p N := by
  intro hχ hm
  refine ⟨?_, ?_⟩
  · intro ha hb
    dsimp
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    have hglobal :
        GloballyAsymptoticallyStableNonminimal intervalDomain p
          eq.1 eq.2 := by
      simpa [eq] using hglobalNonminimal hχ hm ha hb
    rcases hExpNonminimal hχ hm ha hb with
      ⟨A, hA, rate, hrate, hdecay⟩
    refine ⟨hglobal, A, hA, rate, hrate, ?_⟩
    intro u v huv
    exact hdecay u v huv (hglobal u v huv)
  · intro ha hb uStar huStar
    dsimp
    let eq := minimalEquilibrium p uStar
    have hglobal :
        GloballyAsymptoticallyStableMinimal intervalDomain p
          eq.1 eq.2 := by
      simpa [eq] using hglobalMinimal hχ hm ha hb uStar huStar
    rcases hExpMinimal hχ hm ha hb uStar huStar with
      ⟨A, hA, rate, hrate, hdecay⟩
    refine ⟨hglobal, A, hA, rate, hrate, ?_⟩
    intro u v huv hmass
    exact hdecay u v huv hmass (hglobal u v huv hmass)

/-- Theorem 2.4 from explicit persistence and uniform exponential-upgrade
frontiers. -/
theorem intervalDomain_Theorem_2_4_of_persistence_exp_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hglobal :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
            GloballyAsymptoticallyStableNonminimal intervalDomain p
              eq.1 eq.2)
    (hExp :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                UniformConvergesInSup intervalDomain u eq.1 →
                  ExponentialC1ConvergenceWith intervalDomain N u v
                    eq.1 eq.2 A rate) :
    Theorem_2_4 intervalDomain p N C := by
  intro ha_pos hb_pos hβ_nonneg hα_pos hγ_pos ha hb
  dsimp
  intro hcond
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  have hglobalBranch :
      GloballyAsymptoticallyStableNonminimal intervalDomain p
        eq.1 eq.2 := by
    simpa [eq] using
      hglobal ha_pos hb_pos hβ_nonneg hα_pos hγ_pos ha hb hcond
  rcases hExp ha_pos hb_pos hβ_nonneg hα_pos hγ_pos ha hb hcond with
    ⟨A, hA, rate, hrate, hdecay⟩
  refine ⟨hglobalBranch, A, hA, rate, hrate, ?_⟩
  intro u v huv
  exact hdecay u v huv (hglobalBranch u v huv)

/-- Theorem 2.5 from explicit minimal-model persistence and uniform
exponential-upgrade frontiers. -/
theorem intervalDomain_Theorem_2_5_of_persistence_exp_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hglobal :
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          MinimalGlobalStabilityCondition intervalDomain p C uStar →
            GloballyAsymptoticallyStableMinimal intervalDomain p
              eq.1 eq.2)
    (hExp :
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          MinimalGlobalStabilityCondition intervalDomain p C uStar →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                HasInitialMass intervalDomain u uStar →
                UniformConvergesInSup intervalDomain u eq.1 →
                  ExponentialC1ConvergenceWith intervalDomain N u v
                    eq.1 eq.2 A rate) :
    Theorem_2_5 intervalDomain p N C := by
  intro ha hb hm hβ uStar huStar
  dsimp
  intro hcond
  let eq := minimalEquilibrium p uStar
  have hglobalBranch :
      GloballyAsymptoticallyStableMinimal intervalDomain p
        eq.1 eq.2 := by
    simpa [eq] using hglobal ha hb hm hβ uStar huStar hcond
  rcases hExp ha hb hm hβ uStar huStar hcond with
    ⟨A, hA, rate, hrate, hdecay⟩
  refine ⟨hglobalBranch, A, hA, rate, hrate, ?_⟩
  intro u v huv hmass
  exact hdecay u v huv hmass (hglobalBranch u v huv hmass)

/-- Concrete sectorial Theorem 2.3 from explicit persistence/global
convergence and uniform exponential-upgrade frontiers. -/
theorem intervalDomain_Theorem_2_3_sectorialMainline_of_persistence_exp_frontiers
    (p : CM2Params)
    (hglobalNonminimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          GloballyAsymptoticallyStableNonminimal intervalDomain p
            eq.1 eq.2)
    (hglobalMinimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          GloballyAsymptoticallyStableMinimal intervalDomain p
            eq.1 eq.2)
    (hExpNonminimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
              UniformConvergesInSup intervalDomain u eq.1 →
                ExponentialC1ConvergenceWith intervalDomain
                  intervalDomainSectorialStabilityNorms u v
                  eq.1 eq.2 A rate)
    (hExpMinimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          ∃ A > 0, ∃ rate > 0,
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
              UniformConvergesInSup intervalDomain u eq.1 →
                ExponentialC1ConvergenceWith intervalDomain
                  intervalDomainSectorialStabilityNorms u v
                  eq.1 eq.2 A rate) :
    Theorem_2_3 intervalDomain p intervalDomainSectorialStabilityNorms :=
  intervalDomain_Theorem_2_3_of_persistence_exp_frontiers
    p intervalDomainSectorialStabilityNorms
    hglobalNonminimal hglobalMinimal hExpNonminimal hExpMinimal

/-- Concrete sectorial Theorem 2.4 from explicit persistence and uniform
exponential-upgrade frontiers, with the constants fixed to the interval
mainline package. -/
theorem intervalDomain_Theorem_2_4_sectorialMainline_of_persistence_exp_frontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hglobal :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityCondition intervalDomain p
            (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
            eq.1 →
            GloballyAsymptoticallyStableNonminimal intervalDomain p
              eq.1 eq.2)
    (hExp :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityCondition intervalDomain p
            (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
            eq.1 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                UniformConvergesInSup intervalDomain u eq.1 →
                  ExponentialC1ConvergenceWith intervalDomain
                    intervalDomainSectorialStabilityNorms u v
                    eq.1 eq.2 A rate) :
    Theorem_2_4 intervalDomain p intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_4_of_persistence_exp_frontiers
    p intervalDomainSectorialStabilityNorms
    (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
    hglobal hExp

/-- Concrete sectorial Theorem 2.5 from explicit minimal-model persistence and
uniform exponential-upgrade frontiers, with the constants fixed to the
interval mainline package. -/
theorem intervalDomain_Theorem_2_5_sectorialMainline_of_persistence_exp_frontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hglobal :
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          MinimalGlobalStabilityCondition intervalDomain p
            (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
            uStar →
            GloballyAsymptoticallyStableMinimal intervalDomain p
              eq.1 eq.2)
    (hExp :
      p.a = 0 → p.b = 0 → p.m = 1 → 1 ≤ p.β →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          MinimalGlobalStabilityCondition intervalDomain p
            (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
            uStar →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                HasInitialMass intervalDomain u uStar →
                UniformConvergesInSup intervalDomain u eq.1 →
                  ExponentialC1ConvergenceWith intervalDomain
                    intervalDomainSectorialStabilityNorms u v
                    eq.1 eq.2 A rate) :
    Theorem_2_5 intervalDomain p intervalDomainSectorialStabilityNorms
      (intervalDomainSectorialPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_5_of_persistence_exp_frontiers
    p intervalDomainSectorialStabilityNorms
    (intervalDomainSectorialPaper3Constants p M0 uBar vLower)
    hglobal hExp

end

end ShenWork.Paper3
