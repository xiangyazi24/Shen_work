/-
  Paper3 intervalDomain sectorial-semigroup bridge.

  This file does not prove sectoriality of the interval Neumann linearized
  operator.  It records the exact H3.1 hypothesis needed on the concrete
  interval domain and routes it through the existing raw Paper3 stability API.
-/
import ShenWork.Paper3.Statements

namespace ShenWork.Paper3

open ShenWork.IntervalDomain

noncomputable section

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

end

end ShenWork.Paper3
