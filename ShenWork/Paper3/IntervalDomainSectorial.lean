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

end

end ShenWork.Paper3
