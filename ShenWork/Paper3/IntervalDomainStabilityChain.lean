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
open MeasureTheory
open ShenWork.IntervalDomain
open scoped Interval

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

/-- On the unit interval, nonnegativity on the open interior is enough for
nonnegativity of the concrete interval integral: the two endpoints are null
sets. -/
theorem intervalDomain_integral_nonneg_of_inside_nonneg
    (f : intervalDomain.Point → ℝ)
    (hf : ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ f x) :
    0 ≤ intervalDomain.integral f := by
  change 0 ≤ intervalDomainIntegral f
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_nonneg_of_ae_restrict
    (show (0 : ℝ) ≤ 1 by norm_num) ?_
  rw [Filter.EventuallyLE]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have h1 : ∀ᵐ x : ℝ, x ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h0, h1] with x hx0 hx1 hxIcc
  unfold intervalDomainLift
  simp only [hxIcc, dite_true]
  apply hf
  change x ∈ Set.Ioo (0 : ℝ) 1
  exact
    ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hx0),
      lt_of_le_of_ne hxIcc.2 hx1⟩

/-- Concrete theta-dissipation nonnegativity from positivity on the open
interval.  This removes endpoint side conditions, since the concrete integral
does not see the endpoints. -/
theorem intervalDomain_chemotaxisThetaDissipation_nonneg_of_inside_nonneg
    {uStar theta : ℝ} {uSlice : intervalDomain.Point → ℝ}
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (huSlice :
      ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ uSlice x) :
    0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta uSlice :=
  intervalDomain_integral_nonneg_of_inside_nonneg _ fun x hx =>
    thetaDissipationIntegrand_nonneg huStar htheta (huSlice x hx)

/-- A positive global bounded solution supplies the interior positivity needed
for concrete interval theta-dissipation nonnegativity. -/
theorem intervalDomain_chemotaxisThetaDissipation_nonneg_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta t : ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (ht : 0 < t) (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta) :
    0 ≤ chemotaxisThetaDissipation intervalDomain uStar theta (u t) :=
  intervalDomain_chemotaxisThetaDissipation_nonneg_of_inside_nonneg
    huStar htheta fun x hx => (huv.2.2 t x ht hx).le

/-- Direct differential decay of the interval-domain theta dissipation gives
the `Tendsto` form used by the stability composites.  This discharges the
post-processing from the analytic estimate
`D'(t) ≤ -rate * D(t)`; the PDE derivation of that estimate remains an explicit
frontier in the callers. -/
theorem intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul
    {u : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (hrate : 0 < rate) (hs : 0 < s)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hu_nonneg : ∀ t, s ≤ t → ∀ x, 0 ≤ u t x)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    Tendsto
      (fun t => chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      atTop (𝓝 0) := by
  have htheta :
      ThetaMomentConvergesToZero intervalDomain u uStar theta :=
    intervalDomain_thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul
      hrate hs huStar htheta hu_nonneg hderiv hle
  simpa [ThetaMomentConvergesToZero, chemotaxisThetaDissipation] using htheta

/-- Direct differential decay of theta dissipation for a positive global
bounded interval solution.  Compared with
`intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul`, the
eventual slice nonnegativity side condition is discharged from the solution's
interior positivity and the endpoint-null integral bridge above. -/
theorem intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul_of_solution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    {uStar theta rate s : ℝ} {momentSlope : ℝ → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hrate : 0 < rate) (hs : 0 < s)
    (huStar : 0 ≤ uStar) (htheta : 0 ≤ theta)
    (hderiv :
      ∀ t, 0 < t →
        HasDerivAt
          (fun tau =>
            chemotaxisThetaDissipation intervalDomain uStar theta (u tau))
          (momentSlope t) t)
    (hle :
      ∀ t, 0 < t →
        momentSlope t ≤
          -rate * chemotaxisThetaDissipation intervalDomain uStar theta (u t)) :
    Tendsto
      (fun t => chemotaxisThetaDissipation intervalDomain uStar theta (u t))
      atTop (𝓝 0) := by
  have htheta :
      ThetaMomentConvergesToZero intervalDomain u uStar theta :=
    thetaMomentConvergesToZero_of_hasDerivAt_le_neg_mul
      hrate hs hderiv hle
      (fun t ht =>
        intervalDomain_chemotaxisThetaDissipation_nonneg_of_positiveGlobalBoundedSolution
          huv (lt_of_lt_of_le hs ht) huStar htheta)
  simpa [ThetaMomentConvergesToZero, chemotaxisThetaDissipation] using htheta

/-- Corollary 5.1 contains the moment-to-uniform bridge as its first
conjunct.  This projection is useful for the global-stability composites,
where the exponential branch still requires the stronger theorem-level
uniform constants. -/
theorem intervalDomain_momentToUniform_of_corollary51
    {p : CM2Params} {N : StabilityNorms intervalDomain}
    {C : Paper3Constants intervalDomain p}
    (hCor51 : Corollary_5_1 intervalDomain p N C) :
    MomentConvergenceToUniformRaw intervalDomain p := by
  intro hm uStar vStar theta htheta u v huv hmoment
  exact (hCor51 hm).1 uStar vStar theta htheta u v huv hmoment

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

/-- Concrete-constants interval-domain Paper3 Theorem 2.2 with
branch-specific analytic frontiers.  This avoids requiring small-data
existence and `X^σ_p ≤ supNorm` for arbitrary real constants: the theorem only
uses positive equilibria and minimal equilibria with `uStar > 0`. -/
theorem intervalDomain_Theorem_2_2_for_concrete_constants_branch_frontiers
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hraw :
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
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N
      (intervalDomainPaper3Constants p M0 uBar vLower) := by
  have hC :
      Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p
        (intervalDomainPaper3Constants p M0 uBar vLower) :=
    intervalDomainPaper3Constants_usesCriticalSpectrum p M0 uBar vLower
  have hthreshold :=
    Theorem_2_2_linear_threshold_branch_direct
      unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
  refine Theorem_2_2.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    dsimp
    intro hχcrit
    have hstable :
        LinearlyStable unitIntervalNeumannSpectrum p
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      (hthreshold.1 ha hb).1
        (by
          simpa [hC.chiCritical_positiveEquilibrium ha hb] using hχcrit)
    have hlocal :
        LocallyExponentiallyStableFromSup intervalDomain p N
          (positiveEquilibrium p ⟨ha, hb⟩).1
          (positiveEquilibrium p ⟨ha, hb⟩).2 :=
      hraw.locally_from_xpSigma_le_supNorm
        hsigma_low hsigma_high hpNorm hstable
        (hxpPositive ha hb) (hexistPositive ha hb)
    rcases hlocal with ⟨δ, hδ, A, hA, rate, hrate, hmain⟩
    exact ⟨hstable, δ, hδ, A, hA, rate, hrate, hmain⟩
  · intro ha hb
    dsimp
    intro hχcrit
    exact hC.positiveEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hχcrit
  · intro ha hb uStar huStar
    dsimp
    intro hχcrit
    have hstable :
        LinearlyStable unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      (hthreshold.2 ha hb uStar huStar).1
        (by
          simpa [hC.chiCritical_minimalEquilibrium huStar,
            minimalEquilibrium] using hχcrit)
    have hlocal :
        MassConstrainedLocallyExponentiallyStableFromSup intervalDomain p N
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 :=
      hraw.massConstrained_from_xpSigma_le_supNorm
        hsigma_low hsigma_high hpNorm hstable
        (hxpMinimal uStar huStar) (hmexistMinimal uStar huStar)
    rcases hlocal with ⟨δ, hδ, A, hA, rate, hrate, hmain⟩
    exact ⟨hstable, δ, hδ, A, hA, rate, hrate, hmain⟩
  · intro ha hb uStar huStar
    dsimp
    intro hχcrit
    exact hC.minimalEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hχcrit

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

/-- Interval-domain Paper3 Theorem 2.3 with the Lyapunov moment-decay
frontier reduced to direct theta-dissipation differential decay estimates.

This keeps the analytic PDE work visible: callers must still prove the
HasDerivAt identities, the differential inequalities, eventual nonnegativity
of solution slices, moment-to-uniform convergence, and the uniform C¹
exponential upgrade. -/
theorem intervalDomain_Theorem_2_3_of_theta_derivative_frontiers
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
    (hLyapNonminimalDeriv :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                (∀ t, s ≤ t → ∀ x, 0 ≤ u t x) ∧
                (∀ t, 0 < t →
                  HasDerivAt
                    (fun tau =>
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u tau))
                    (momentSlope t) t) ∧
                (∀ t, 0 < t →
                  momentSlope t ≤
                    -rate *
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u t)))
    (hLyapMinimalDeriv :
      p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
                ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                  (∀ t, s ≤ t → ∀ x, 0 ≤ u t x) ∧
                  (∀ t, 0 < t →
                    HasDerivAt
                      (fun tau =>
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u tau))
                      (momentSlope t) t) ∧
                  (∀ t, 0 < t →
                    momentSlope t ≤
                      -rate *
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u t))) :
    Theorem_2_3 intervalDomain p N :=
  intervalDomain_Theorem_2_3_of_lyapunov_moment_and_exponential_frontiers
    p N hmomentToUniform hExpNonminimal hExpMinimal
    (by
      intro hχ hm ha hb
      dsimp
      intro u v huv
      rcases hLyapNonminimalDeriv hχ hm ha hb u v huv with
        ⟨rate, hrate, s, hs, momentSlope, hu_nonneg, hderiv, hle⟩
      exact
        intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul
          (uStar := (positiveEquilibrium p ⟨ha, hb⟩).1)
          (theta := p.α) (rate := rate) (s := s)
          (momentSlope := momentSlope) hrate hs
          (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le p.hα.le
          hu_nonneg hderiv hle)
    (by
      intro hχ hm ha hb uStar huStar
      dsimp
      intro u v huv hmass
      rcases hLyapMinimalDeriv hχ hm ha hb uStar huStar u v huv hmass with
        ⟨rate, hrate, s, hs, momentSlope, hu_nonneg, hderiv, hle⟩
      exact
        intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul
          (uStar := (minimalEquilibrium p uStar).1) (theta := p.α)
          (rate := rate) (s := s) (momentSlope := momentSlope)
          hrate hs (by simpa [minimalEquilibrium] using huStar.le) p.hα.le
          hu_nonneg hderiv hle)

/-- Interval-domain Paper3 Theorem 2.3 with the theta-dissipation
differential-decay frontiers and with eventual nonnegativity discharged from
`PositiveGlobalBoundedSolution`.  The remaining frontiers are the PDE
derivative/decay estimates, moment-to-uniform convergence, and the uniform C¹
exponential upgrade. -/
theorem intervalDomain_Theorem_2_3_of_theta_derivative_frontiers_from_solution_positivity
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
    (hLyapNonminimalDeriv :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                (∀ t, 0 < t →
                  HasDerivAt
                    (fun tau =>
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u tau))
                    (momentSlope t) t) ∧
                (∀ t, 0 < t →
                  momentSlope t ≤
                    -rate *
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u t)))
    (hLyapMinimalDeriv :
      p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
                ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                  (∀ t, 0 < t →
                    HasDerivAt
                      (fun tau =>
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u tau))
                      (momentSlope t) t) ∧
                  (∀ t, 0 < t →
                    momentSlope t ≤
                      -rate *
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u t))) :
    Theorem_2_3 intervalDomain p N :=
  intervalDomain_Theorem_2_3_of_lyapunov_moment_and_exponential_frontiers
    p N hmomentToUniform hExpNonminimal hExpMinimal
    (by
      intro hχ hm ha hb
      dsimp
      intro u v huv
      rcases hLyapNonminimalDeriv hχ hm ha hb u v huv with
        ⟨rate, hrate, s, hs, momentSlope, hderiv, hle⟩
      exact
        intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul_of_solution
          (p := p) (v := v)
          (uStar := (positiveEquilibrium p ⟨ha, hb⟩).1)
          (theta := p.α) (rate := rate) (s := s)
          (momentSlope := momentSlope) huv hrate (show 0 < s from hs)
          (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le p.hα.le
          hderiv hle)
    (by
      intro hχ hm ha hb uStar huStar
      dsimp
      intro u v huv hmass
      rcases hLyapMinimalDeriv hχ hm ha hb uStar huStar u v huv hmass with
        ⟨rate, hrate, s, hs, momentSlope, hderiv, hle⟩
      exact
        intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul_of_solution
          (p := p) (v := v)
          (uStar := (minimalEquilibrium p uStar).1) (theta := p.α)
          (rate := rate) (s := s) (momentSlope := momentSlope)
          huv hrate (show 0 < s from hs)
          (by simpa [minimalEquilibrium] using huStar.le)
          p.hα.le hderiv hle)

/-- Interval-domain Paper3 Theorem 2.3 with `MomentConvergenceToUniformRaw`
supplied by Corollary 5.1 and the Lyapunov frontier reduced to direct
theta-dissipation differential decay.  The remaining frontiers are the PDE
derivative/decay estimates and the theorem-level uniform C¹ exponential
constants. -/
theorem intervalDomain_Theorem_2_3_of_corollary51_theta_derivative_solution
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hCor51 :
      Corollary_5_1 intervalDomain p N
        (intervalDomainPaper3Constants p M0 uBar vLower))
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
    (hLyapNonminimalDeriv :
      p.χ₀ ≤ 0 → 1 ≤ p.m →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                (∀ t, 0 < t →
                  HasDerivAt
                    (fun tau =>
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u tau))
                    (momentSlope t) t) ∧
                (∀ t, 0 < t →
                  momentSlope t ≤
                    -rate *
                      chemotaxisThetaDissipation intervalDomain eq.1 p.α
                        (u t)))
    (hLyapMinimalDeriv :
      p.χ₀ ≤ 0 → 1 ≤ p.m → p.a = 0 → p.b = 0 →
        ∀ uStar > 0,
          let eq := minimalEquilibrium p uStar
          ∀ u v : ℝ → intervalDomain.Point → ℝ,
            PositiveGlobalBoundedSolution intervalDomain p u v →
              HasInitialMass intervalDomain u uStar →
                ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                  (∀ t, 0 < t →
                    HasDerivAt
                      (fun tau =>
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u tau))
                      (momentSlope t) t) ∧
                  (∀ t, 0 < t →
                    momentSlope t ≤
                      -rate *
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u t))) :
    Theorem_2_3 intervalDomain p N :=
  intervalDomain_Theorem_2_3_of_theta_derivative_frontiers_from_solution_positivity
    p N (intervalDomain_momentToUniform_of_corollary51 hCor51)
    hExpNonminimal hExpMinimal hLyapNonminimalDeriv hLyapMinimalDeriv

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

/-- Concrete-constants/first-mode Theorem 2.4 with the formula-level Lyapunov
frontier reduced to a direct theta-dissipation differential decay estimate.
The remaining assumptions are still honest frontiers: first-mode threshold
domination, moment-to-uniform convergence, uniform exponential upgrade, and the
PDE derivation of the direct differential decay estimate. -/
theorem intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_formula_derivative_frontiers
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
    (hLyapStrongFormulaDeriv :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
                ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                  (∀ t, s ≤ t → ∀ x, 0 ≤ u t x) ∧
                  (∀ t, 0 < t →
                    HasDerivAt
                      (fun tau =>
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u tau))
                      (momentSlope t) t) ∧
                  (∀ t, 0 < t →
                    momentSlope t ≤
                      -rate *
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u t))) :
    Theorem_2_4 intervalDomain p N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_formula_frontiers
    p N M0 uBar vLower hfirst hmomentToUniform hExpNonminimal
    (by
      intro ha_pos hb_pos hβ_nonneg hα_pos hγ_pos ha hb
      dsimp
      intro hcond u v huv
      rcases hLyapStrongFormulaDeriv ha_pos hb_pos hβ_nonneg hα_pos hγ_pos
          ha hb hcond u v huv with
        ⟨rate, hrate, s, hs, momentSlope, hu_nonneg, hderiv, hle⟩
      exact
        intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul
          (uStar := (positiveEquilibrium p ⟨ha, hb⟩).1)
          (theta := p.α) (rate := rate) (s := s)
          (momentSlope := momentSlope) hrate hs
          (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le hα_pos.le
          hu_nonneg hderiv hle)

/-- Concrete-constants/first-mode Theorem 2.4 with formula-level
theta-dissipation differential decay and solution positivity discharging the
nonnegativity side condition.  The remaining frontiers are still exactly the
PDE derivative/decay estimate, first-mode threshold domination,
moment-to-uniform convergence, and uniform exponential upgrade. -/
theorem intervalDomain_Theorem_2_4_formula_derivative_frontiers_from_solution_positivity
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
    (hLyapStrongFormulaDeriv :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
                ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                  (∀ t, 0 < t →
                    HasDerivAt
                      (fun tau =>
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u tau))
                      (momentSlope t) t) ∧
                  (∀ t, 0 < t →
                    momentSlope t ≤
                      -rate *
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u t))) :
    Theorem_2_4 intervalDomain p N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_4_of_concrete_constants_firstMode_formula_frontiers
    p N M0 uBar vLower hfirst hmomentToUniform hExpNonminimal
    (by
      intro ha_pos hb_pos hβ_nonneg hα_pos hγ_pos ha hb
      dsimp
      intro hcond u v huv
      rcases hLyapStrongFormulaDeriv ha_pos hb_pos hβ_nonneg hα_pos hγ_pos
          ha hb hcond u v huv with
        ⟨rate, hrate, s, hs, momentSlope, hderiv, hle⟩
      exact
        intervalDomain_thetaDissipation_tendsto_zero_of_hasDerivAt_le_neg_mul_of_solution
          (p := p) (v := v)
          (uStar := (positiveEquilibrium p ⟨ha, hb⟩).1)
          (theta := p.α) (rate := rate) (s := s)
          (momentSlope := momentSlope) huv hrate (show 0 < s from hs)
          (positiveEquilibrium_fst_pos p ⟨ha, hb⟩).le hα_pos.le
          hderiv hle)

/-- Concrete-constants/first-mode Theorem 2.4 with the moment-to-uniform
input supplied by Corollary 5.1 and the Lyapunov frontier reduced to direct
theta-dissipation differential decay.  The theorem-level uniform C¹
exponential constants remain an explicit stronger frontier. -/
theorem intervalDomain_Theorem_2_4_formula_derivative_solution_of_corollary51
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (M0 uBar vLower : ℝ)
    (hCor51 :
      Corollary_5_1 intervalDomain p N
        (intervalDomainPaper3Constants p M0 uBar vLower))
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
    (hLyapStrongFormulaDeriv :
      0 < p.a → 0 < p.b → 0 ≤ p.β → 0 < p.α → 0 < p.γ →
        ∀ (ha : 0 < p.a) (hb : 0 < p.b),
          let eq := positiveEquilibrium p ⟨ha, hb⟩
          NonminimalGlobalStabilityFormulaCondition p eq.1 eq.2 M0 →
            ∀ u v : ℝ → intervalDomain.Point → ℝ,
              PositiveGlobalBoundedSolution intervalDomain p u v →
                ∃ rate > 0, ∃ s : ℝ, 0 < s ∧ ∃ momentSlope : ℝ → ℝ,
                  (∀ t, 0 < t →
                    HasDerivAt
                      (fun tau =>
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u tau))
                      (momentSlope t) t) ∧
                  (∀ t, 0 < t →
                    momentSlope t ≤
                      -rate *
                        chemotaxisThetaDissipation intervalDomain eq.1 p.α
                          (u t))) :
    Theorem_2_4 intervalDomain p N
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_4_formula_derivative_frontiers_from_solution_positivity
    p N M0 uBar vLower hfirst
    (intervalDomain_momentToUniform_of_corollary51 hCor51)
    hExpNonminimal hLyapStrongFormulaDeriv

end

end ShenWork.Paper3
