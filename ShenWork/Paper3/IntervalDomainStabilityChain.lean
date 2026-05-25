/-
  Paper3 intervalDomain stability-chain composites.

  These theorems do not prove the missing analytic inputs.  They assemble the
  statement-level Paper3 stability theorems on `intervalDomain` from explicit
  frontiers: sectorial local exponential estimates, small-data existence,
  Lyapunov moment decay, moment-to-uniform convergence, and C¹ exponential
  upgrade.
-/
import ShenWork.Paper3.IntervalDomainSectorial
import ShenWork.Paper3.LyapunovFunction

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- Concrete Paper3 constants on the unit interval, with the critical threshold
and the strong/minimal thresholds fixed to the paper's explicit formulas.  The
parameters `M0`, `uBar`, and `vLower` keep the eventual-bound frontiers visible
instead of hiding them in an arbitrary constants package. -/
def intervalDomainPaper3Constants
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

/-- The concrete interval constants use exactly the unit-interval Neumann
critical spectrum. -/
theorem intervalDomainPaper3Constants_usesCriticalSpectrum
    (p : CM2Params) (M0 uBar vLower : ℝ) :
    Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p
      (intervalDomainPaper3Constants p M0 uBar vLower) := by
  intro uStar _huStar
  rfl

/-- `Lemma_A_7` for the concrete interval constants, reduced to the explicit
first-mode domination of the maximum strong threshold. -/
theorem intervalDomain_Lemma_A_7_of_firstMode_threshold
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hfirst :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2)) :
    Lemma_A_7 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) := by
  refine
    Lemma_A_7_of_firstNonzero_lower_and_formula_fields
      (D := intervalDomain) (p := p)
      (C := intervalDomainPaper3Constants p M0 uBar vLower)
      unitIntervalNeumannSpectrum M0
      unitIntervalNeumannSpectrum_hasNeumannSpectrum
      (intervalDomainPaper3Constants_usesCriticalSpectrum p M0 uBar vLower)
      ?_ ?_ ?_ ?_ ?_
  · intro ha hb
    simp [intervalDomainPaper3Constants, positiveEquilibrium]
  · intro ha hb
    simp [intervalDomainPaper3Constants]
  · intro ha hb
    simp [intervalDomainPaper3Constants, positiveEquilibrium]
  · intro ha hb
    simp [intervalDomainPaper3Constants]
  · intro ha hb
    simpa [unitIntervalNeumannSpectrum] using hfirst ha hb

/-- On the concrete interval constants, the package-shaped nonminimal
stability condition is exactly the explicit formula condition at a positive
equilibrium. -/
theorem intervalDomain_concrete_positiveEquilibrium_formulaCondition_of_condition
    (p : CM2Params) (M0 uBar vLower : ℝ)
    {ha : 0 < p.a} {hb : 0 < p.b}
    (hcond :
      NonminimalGlobalStabilityCondition intervalDomain p
        (intervalDomainPaper3Constants p M0 uBar vLower)
        (positiveEquilibrium p ⟨ha, hb⟩).1) :
    NonminimalGlobalStabilityFormulaCondition p
      (positiveEquilibrium p ⟨ha, hb⟩).1
      (positiveEquilibrium p ⟨ha, hb⟩).2 M0 := by
  rcases hcond with h | h | h | h
  · rcases h with ⟨hm, hrel, hχ0, hχ⟩
    exact Or.inl
      ⟨hm, hrel, hχ0,
        by
          simpa [intervalDomainPaper3Constants, positiveEquilibrium] using hχ⟩
  · rcases h with ⟨hm, hβ, hrel, hχ0, hχ⟩
    exact Or.inr (Or.inl
      ⟨hm, hβ, hrel, hχ0,
        by
          simpa [intervalDomainPaper3Constants] using hχ⟩)
  · rcases h with ⟨hm, hγ, hrel, hχ⟩
    exact Or.inr (Or.inr (Or.inl
      ⟨hm, hγ, hrel,
        by
          simpa [intervalDomainPaper3Constants, positiveEquilibrium] using
            hχ⟩))
  · rcases h with ⟨hm, hβ, hγ, hrel, hχ⟩
    exact Or.inr (Or.inr (Or.inr
      ⟨hm, hβ, hγ, hrel,
        by
          simpa [intervalDomainPaper3Constants] using hχ⟩))

/-- The Lyapunov theta-dissipation functional is definitionally the moment
functional used by `ThetaMomentConvergesToZero`. -/
theorem intervalDomain_thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
    {u : ℝ → intervalDomain.Point → ℝ} {uStar theta : ℝ}
    (h :
      Tendsto
        (fun t => chemotaxisThetaDissipation intervalDomain uStar theta (u t))
        atTop (𝓝 0)) :
    ThetaMomentConvergesToZero intervalDomain u uStar theta := by
  simpa [ThetaMomentConvergesToZero, chemotaxisThetaDissipation] using h

/-- Conditional interval-domain Paper3 Theorem 2.2.

This is the H4.1 statement-level composite.  The remaining frontiers are the
honest H3.1 inputs: the raw sectorial local exponential estimate, the
`X^σ_p`/sup-norm comparison, and small-data Cauchy/global existence in the
ordinary and mass-constrained neighborhoods. -/
theorem intervalDomain_Theorem_2_2_of_sectorial_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hraw :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
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
  Theorem_2_2_full_by_chi_sign_of_raw
    unitIntervalNeumannSpectrum_hasNeumannSpectrum hC hraw
    hsigma_low hsigma_high hpNorm hcontrol hexist hmexist

/-- Concrete-constants version of the interval-domain Paper3 Theorem 2.2
composite.  Compared with `intervalDomain_Theorem_2_2_of_sectorial_frontiers`,
this discharges the critical-spectrum package hypothesis by using the explicit
unit-interval constants above. -/
theorem intervalDomain_Theorem_2_2_of_concrete_constants_and_sectorial_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hraw :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
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
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_of_sectorial_frontiers
    p N (intervalDomainPaper3Constants p M0 uBar vLower)
    (intervalDomainPaper3Constants_usesCriticalSpectrum p M0 uBar vLower)
    hraw hsigma_low hsigma_high hpNorm hcontrol hexist hmexist

/-- Conditional interval-domain Paper3 Theorem 2.2 with the norm-control
frontier reduced to the primitive comparison `X^σ_p ≤ supNorm`. -/
theorem intervalDomain_Theorem_2_2_of_xpSigma_le_supNorm_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hraw :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hxp :
      ∀ uStar, ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist :
      ∀ uStar, ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p uStar delta)
    (hmexist :
      ∀ uStar, ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N C :=
  intervalDomain_Theorem_2_2_of_sectorial_frontiers
    p N C hC hraw hsigma_low hsigma_high hpNorm
    (fun uStar =>
      SupControlsXpSigmaDistance.of_xpSigma_le_supNorm
        (D := intervalDomain) (N := N) (sigma := sigma) (pNorm := pNorm)
        (uStar := uStar) (hxp uStar))
    hexist hmexist

/-- Concrete-constants interval-domain Paper3 Theorem 2.2.  This discharges
the constants-package and critical-spectrum identity inputs using
`intervalDomainPaper3Constants`. -/
theorem intervalDomain_Theorem_2_2_for_concrete_constants
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hraw :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        N.c1Distance N.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hxp :
      ∀ uStar, ∀ u₀ : intervalDomain.Point → ℝ,
        N.xpSigmaDistance sigma pNorm u₀ (fun _ => uStar) ≤
          intervalDomain.supNorm (fun x => u₀ x - uStar))
    (hexist :
      ∀ uStar, ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p uStar delta)
    (hmexist :
      ∀ uStar, ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p uStar delta) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_of_xpSigma_le_supNorm_frontiers
    p N (intervalDomainPaper3Constants p M0 uBar vLower)
    (intervalDomainPaper3Constants_usesCriticalSpectrum p M0 uBar vLower)
    hraw hsigma_low hsigma_high hpNorm hxp hexist hmexist

/-- Conditional interval-domain Paper3 Theorem 2.3.

The Lyapunov inputs are only moment-decay frontiers; uniform convergence is
derived through `MomentConvergenceToUniformRaw`, and the C¹ exponential
estimate is derived from the raw exponential-upgrade hypotheses plus the
strict positivity of the unit-interval critical sensitivity. -/
theorem intervalDomain_Theorem_2_3_of_lyapunov_moment_and_exponential_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (hmomentToUniform : MomentConvergenceToUniformRaw intervalDomain p)
    (hExpNonminimal :
      1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  UniformConvergesInSup intervalDomain u eq.1 →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate)
    (hExpMinimal :
      1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  HasInitialMass intervalDomain u uStar →
                    UniformConvergesInSup intervalDomain u eq.1 →
                      ExponentialC1ConvergenceWith intervalDomain N u v
                        eq.1 eq.2 A rate)
    (hLyapNonminimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              Tendsto
                (fun t =>
                  chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
                atTop (𝓝 0))
    (hLyapMinimal :
      p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
                Tendsto
                  (fun t =>
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
                  atTop (𝓝 0)) :
    Theorem_2_3 intervalDomain p N := by
  intro hχ hm
  refine ⟨?_, ?_⟩
  · intro ha hb
    dsimp
    let eq := positiveEquilibrium p ⟨ha, hb⟩
    have hglobal :
        GloballyAsymptoticallyStableNonminimal intervalDomain p eq.1 eq.2 := by
      intro u v huv
      exact hmomentToUniform hm eq.1 eq.2 p.α p.hα u v huv
        (intervalDomain_thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
          (by
            simpa [eq] using hLyapNonminimal hχ hm ha hb u v huv))
    have hcrit_pos :
        0 <
          paperCriticalSensitivity unitIntervalNeumannSpectrum p
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      paperCriticalSensitivity_positiveEquilibrium_pos
        unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
        ha hb
    have hχcrit :
        p.χ₀ <
          paperCriticalSensitivity unitIntervalNeumannSpectrum p
            (positiveEquilibrium p ⟨ha, hb⟩).1
            (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      lt_of_le_of_lt hχ hcrit_pos
    rcases hExpNonminimal hm ha hb hχcrit with
      ⟨A, hA, rate, hrate, hdecay⟩
    refine ⟨hglobal, A, hA, rate, hrate, ?_⟩
    intro u v huv
    exact hdecay u v huv (hglobal u v huv)
  · intro ha hb uStar huStar
    dsimp
    let eq := minimalEquilibrium p uStar
    have hglobal :
        GloballyAsymptoticallyStableMinimal intervalDomain p eq.1 eq.2 := by
      intro u v huv hmass
      exact hmomentToUniform hm eq.1 eq.2 p.α p.hα u v huv
        (intervalDomain_thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
          (by
            simpa [eq] using
              hLyapMinimal hχ hm ha hb uStar huStar u v huv hmass))
    have hcrit_pos :
        0 <
          paperCriticalSensitivity unitIntervalNeumannSpectrum p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 :=
      paperCriticalSensitivity_minimalEquilibrium_pos
        unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
        huStar
    have hχcrit :
        p.χ₀ <
          paperCriticalSensitivity unitIntervalNeumannSpectrum p
            (minimalEquilibrium p uStar).1
            (minimalEquilibrium p uStar).2 :=
      lt_of_le_of_lt hχ hcrit_pos
    rcases hExpMinimal hm ha hb uStar huStar hχcrit with
      ⟨A, hA, rate, hrate, hdecay⟩
    refine ⟨hglobal, A, hA, rate, hrate, ?_⟩
    intro u v huv hmass
    exact hdecay u v huv hmass (hglobal u v huv hmass)

/-- Conditional interval-domain Paper3 Theorem 2.4.

The global-attractor part is obtained from the Lyapunov moment-decay frontier
and the moment-to-uniform bridge.  The exponential C¹ upgrade is obtained from
the raw upgrade frontier after `Lemma_A_7` proves that the strong-logistic
condition lies below the critical sensitivity. -/
theorem intervalDomain_Theorem_2_4_of_lyapunov_moment_and_exponential_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hA7 : Lemma_A_7 intervalDomain p C)
    (hmomentToUniform : MomentConvergenceToUniformRaw intervalDomain p)
    (hExpNonminimal :
      1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  UniformConvergesInSup intervalDomain u eq.1 →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate)
    (hLyapStrong :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityCondition intervalDomain p C eq.1 →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
                Tendsto
                  (fun t =>
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
                  atTop (𝓝 0)) :
    Theorem_2_4 intervalDomain p N C := by
  intro ha_pos hb_pos hβ_nonneg hα_pos hγ_pos ha hb
  dsimp
  intro hcond
  let eq := positiveEquilibrium p ⟨ha, hb⟩
  have hm : 1 ≤ p.m :=
    hcond.m_ge_one
  have hglobal :
      GloballyAsymptoticallyStableNonminimal intervalDomain p eq.1 eq.2 := by
    intro u v huv
    exact hmomentToUniform hm eq.1 eq.2 p.α p.hα u v huv
      (intervalDomain_thetaMomentConvergesToZero_of_chemotaxisThetaDissipation
        (by
          simpa [eq] using
            hLyapStrong ha_pos hb_pos hβ_nonneg hα_pos hγ_pos
              ha hb hcond u v huv))
  have hχC :
      p.χ₀ < C.chiCritical (positiveEquilibrium p ⟨ha, hb⟩).1 :=
    hA7.nonminimal_condition_chi_lt_critical ha hb hcond
  have hχpaper :
      p.χ₀ <
        paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 := by
    simpa [hC.chiCritical_positiveEquilibrium ha hb] using hχC
  rcases hExpNonminimal hm ha hb hχpaper with
    ⟨A, hA, rate, hrate, hdecay⟩
  refine ⟨hglobal, A, hA, rate, hrate, ?_⟩
  intro u v huv
  exact hdecay u v huv (hglobal u v huv)

/-- Concrete-constants/first-mode version of the interval-domain Paper3
Theorem 2.4 composite.  This discharges both the critical-spectrum package
hypothesis and the `Lemma_A_7` package hypothesis, reducing them to the
explicit first-mode threshold domination. -/
theorem intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_and_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hfirst :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2))
    (hmomentToUniform : MomentConvergenceToUniformRaw intervalDomain p)
    (hExpNonminimal :
      1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  UniformConvergesInSup intervalDomain u eq.1 →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate)
    (hLyapStrong :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityCondition intervalDomain p
              (intervalDomainPaper3Constants p M0 uBar vLower) eq.1 →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
                Tendsto
                  (fun t =>
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
                  atTop (𝓝 0)) :
    Theorem_2_4 intervalDomain p N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_4_of_lyapunov_moment_and_exponential_frontiers
    p N (intervalDomainPaper3Constants p M0 uBar vLower)
    (intervalDomainPaper3Constants_usesCriticalSpectrum p M0 uBar vLower)
    (intervalDomain_Lemma_A_7_of_firstMode_threshold p M0 uBar vLower hfirst)
    hmomentToUniform hExpNonminimal hLyapStrong

/-- Concrete-constants/first-mode version of Theorem 2.4 whose Lyapunov
frontier is stated directly with the paper's explicit formula condition. -/
theorem intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_formula_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hfirst :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b),
        let eq := positiveEquilibrium p ⟨ha, hb⟩
        max
            (max (chiStrong1Formula p eq.1 eq.2)
              (chiStrong2Formula p eq.1))
            (max (chiStrong3Formula p M0 eq.1 eq.2)
              (chiStrong4Formula p M0 eq.1)) ≤
          ((1 + eq.2) ^ p.β /
              (p.ν * p.γ * eq.1 ^ (p.m + p.γ - 1))) *
            (p.μ + Real.pi ^ 2))
    (hmomentToUniform : MomentConvergenceToUniformRaw intervalDomain p)
    (hExpNonminimal :
      1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          p.χ₀ <
              paperCriticalSensitivity unitIntervalNeumannSpectrum p
                eq.1 eq.2 →
            ∃ A > 0, ∃ rate > 0,
              ∀ u v : ℝ → intervalDomain.Point → ℝ,
                PositiveGlobalBoundedSolution intervalDomain p u v →
                  UniformConvergesInSup intervalDomain u eq.1 →
                    ExponentialC1ConvergenceWith intervalDomain N u v
                      eq.1 eq.2 A rate)
    (hLyapStrongFormula :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
                Tendsto
                  (fun t =>
                    chemotaxisThetaDissipation intervalDomain eq.1 p.α (u t))
                  atTop (𝓝 0)) :
    Theorem_2_4 intervalDomain p N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_and_frontiers
    p N M0 uBar vLower hfirst hmomentToUniform hExpNonminimal
    (by
      intro ha_pos hb_pos hβ_nonneg hα_pos hγ_pos ha hb
      dsimp
      intro hcond u v huv
      exact hLyapStrongFormula ha_pos hb_pos hβ_nonneg hα_pos hγ_pos
        ha hb
        (intervalDomain_concrete_positiveEquilibrium_formulaCondition_of_condition
          p M0 uBar vLower (ha := ha) (hb := hb) hcond)
        u v huv)

end

end ShenWork.Paper3
