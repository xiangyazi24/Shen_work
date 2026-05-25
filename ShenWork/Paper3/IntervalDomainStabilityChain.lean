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
open ShenWork.Paper2
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

/-! ### Concrete interval stability gauges -/

/-- Concrete `C¹` distance on the unit interval: sup distance plus sup norm of
the spatial derivative of the difference. -/
def intervalDomainC1Distance
    (f g : intervalDomain.Point → ℝ) : ℝ :=
  intervalDomain.supNorm (fun x => f x - g x) +
    intervalDomain.supNorm
      (fun x => intervalDomain.gradNorm (fun y => f y - g y) x)

/-- Concrete `X^σ_p` gauge used by the current interval stability chain.

This is the sup-distance gauge.  It is intentionally stronger than the abstract
neighborhood input expected by `SectorialLocalExponentialRaw`, and therefore
the sup-to-`X^σ_p` bridge is definitional rather than an extra hypothesis. -/
def intervalDomainXpSigmaDistance
    (_sigma _pNorm : ℝ) (f g : intervalDomain.Point → ℝ) : ℝ :=
  intervalDomain.supNorm (fun x => f x - g x)

/-- Concrete Paper3 stability norm package for `intervalDomain`. -/
def intervalDomainStabilityNorms :
    StabilityNorms intervalDomain where
  c1Distance := intervalDomainC1Distance
  xpSigmaDistance := intervalDomainXpSigmaDistance

@[simp] theorem intervalDomainStabilityNorms_c1Distance
    (f g : intervalDomain.Point → ℝ) :
    intervalDomainStabilityNorms.c1Distance f g =
      intervalDomainC1Distance f g := rfl

@[simp] theorem intervalDomainStabilityNorms_xpSigmaDistance
    (sigma pNorm : ℝ) (f g : intervalDomain.Point → ℝ) :
    intervalDomainStabilityNorms.xpSigmaDistance sigma pNorm f g =
      intervalDomain.supNorm (fun x => f x - g x) := rfl

/-- The concrete interval `X^σ_p` gauge is controlled by the primitive sup
distance by definition. -/
theorem intervalDomainStabilityNorms_xpSigma_le_supNorm
    (sigma pNorm uStar : ℝ) (u₀ : intervalDomain.Point → ℝ) :
    intervalDomainStabilityNorms.xpSigmaDistance sigma pNorm u₀
        (fun _ => uStar) ≤
      intervalDomain.supNorm (fun x => u₀ x - uStar) := by
  rfl

/-- Concrete norm-control bridge for the interval stability norms. -/
theorem intervalDomainStabilityNorms_supControlsXpSigmaDistance
    (sigma pNorm uStar : ℝ) :
    SupControlsXpSigmaDistance intervalDomain intervalDomainStabilityNorms
      sigma pNorm uStar :=
  SupControlsXpSigmaDistance.of_xpSigma_le_supNorm
    (intervalDomainStabilityNorms_xpSigma_le_supNorm sigma pNorm uStar)

/-! ### Concrete upper-envelope monotonicity -/

/-- The interval upper envelope can be taken to be the concrete sup norm.
Its monotonicity follows from Paper2 `Lemma_3_1_intervalDomain`, which was
proved from the certified interval parabolic max-principle certificate in
`intervalDomain.classicalRegularity`. -/
theorem intervalDomain_upperEnvelopeMonotonicityRaw_supNorm
    (p : CM2Params) :
    UpperEnvelopeMonotonicityRaw intervalDomain p intervalDomain.supNorm := by
  intro u v huv
  refine ⟨?_, ?_⟩
  · intro hχ ha hb t₀ ht₀ hlarge t₁ t₂ ht₁ h12 h2₀
    have hT : 0 < t₀ + 1 := by linarith
    have ht₀T : t₀ < t₀ + 1 := by linarith
    have hsol :
        IsPaper2ClassicalSolution intervalDomain p (t₀ + 1) u v :=
      huv.1 (t₀ + 1) hT
    have hmono :
        SupNormNonincreasingOn intervalDomain u (Set.Ioc (0 : ℝ) t₀) :=
      (ShenWork.Paper2.Lemma_3_1_intervalDomain p hχ).1
        ha hb (t₀ + 1) hT u v hsol t₀ ht₀ ht₀T hlarge
    have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ h12
    exact hmono t₁ ⟨ht₁, le_trans h12 h2₀⟩ t₂ ⟨ht₂, h2₀⟩ h12
  · intro hχ ha hb t₁ t₂ ht₁ h12
    let T : ℝ := t₂ + 1
    have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ h12
    have hT : 0 < T := by
      dsimp [T]
      linarith
    have ht₂T : t₂ < T := by
      dsimp [T]
      linarith
    have ht₁T : t₁ < T := lt_of_le_of_lt h12 ht₂T
    have hsol : IsPaper2ClassicalSolution intervalDomain p T u v :=
      huv.1 T hT
    have hmono :
        SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) T) :=
      (ShenWork.Paper2.Lemma_3_1_intervalDomain p hχ).2
        ha hb T hT u v hsol
    exact hmono t₁ ⟨ht₁, ht₁T⟩ t₂ ⟨ht₂, ht₂T⟩ h12

/-- Paper3 `Lemma_3_4` for any compactness package whose upper-envelope field is
the concrete interval sup norm.  No assumptions on the other `CompactnessData`
fields are used. -/
theorem intervalDomain_Lemma_3_4_of_upperEnvelope_eq_supNorm
    (p : CM2Params) (K : CompactnessData intervalDomain)
    (hupper : ∀ f : intervalDomain.Point → ℝ,
      K.upperEnvelope f = intervalDomain.supNorm f) :
    Lemma_3_4 intervalDomain p K := by
  intro u v huv
  have hraw := intervalDomain_upperEnvelopeMonotonicityRaw_supNorm p u v huv
  refine ⟨?_, ?_⟩
  · intro hχ ha hb t₀ ht₀ hlarge t₁ t₂ ht₁ h12 h2₀
    have hlarge' :
        (p.a / p.b) ^ (1 / p.α) < intervalDomain.supNorm (u t₀) := by
      simpa [hupper] using hlarge
    have hbound := hraw.1 hχ ha hb t₀ ht₀ hlarge' t₁ t₂ ht₁ h12 h2₀
    simpa [hupper] using hbound
  · intro hχ ha hb t₁ t₂ ht₁ h12
    have hbound := hraw.2 hχ ha hb t₁ t₂ ht₁ h12
    simpa [hupper] using hbound

/-! ### Concrete norm-continuity and persistence mainline -/

/-- Exact norm-continuity frontier for the concrete interval stability gauge.
The distance functional is exposed directly rather than hidden behind an
abstract `StabilityNorms` field. -/
def IntervalDomainInitialContinuityRaw (p : CM2Params) : Prop :=
  ∀ uStar > 0,
    InitialContinuityRaw intervalDomain p
      intervalDomainStabilityNorms.xpSigmaDistance uStar

/-- Paper3 `Lemma_3_3` for the concrete interval stability norms, routed from
the exposed raw initial-continuity frontier. -/
theorem intervalDomain_Lemma_3_3_for_concreteStabilityNorms_of_initialContinuityRaw
    (p : CM2Params)
    (hcont : IntervalDomainInitialContinuityRaw p) :
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms := by
  intro uStar huStar
  simpa [IntervalDomainInitialContinuityRaw, InitialContinuityRaw,
    InitialContinuityConclusion] using hcont uStar huStar

/-- Paper3 Theorem 2.1(1) on the interval, routed from the exposed raw
persistence frontier. -/
theorem intervalDomain_Theorem_2_1_part1_of_uniformPersistenceRaw
    (p : CM2Params)
    (h : UniformPersistencePart1Raw intervalDomain p) :
    Theorem_2_1_part1 intervalDomain p :=
  h

/-- Paper3 Theorem 2.1(2) on the interval, routed from the exposed raw
persistence frontier. -/
theorem intervalDomain_Theorem_2_1_part2_of_uniformPersistenceRaw
    (p : CM2Params)
    (h : UniformPersistencePart2Raw intervalDomain p) :
    Theorem_2_1_part2 intervalDomain p :=
  h

/-- Paper3 Theorem 2.1(3) on the interval, routed from the exposed raw
persistence frontier. -/
theorem intervalDomain_Theorem_2_1_part3_of_uniformPersistenceRaw
    (p : CM2Params)
    (h : UniformPersistencePart3Raw intervalDomain p) :
    Theorem_2_1_part3 intervalDomain p :=
  h

/-- Paper3 Theorem 2.1(4) for the concrete interval constants, routed from the
exposed raw minimal persistence frontier with `eventualMinimalUBound = uBar`
and Gaussian lower constant `1`. -/
theorem intervalDomain_Theorem_2_1_part4_for_concrete_constants_of_uniformPersistenceRaw
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (h : UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1) :
    Theorem_2_1_part4 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) := by
  intro ha hb hm hβ hχ0 hχ uStar huStar u v huv hmass
  have hbound :=
    h (by norm_num : (0 : ℝ) < 1) ha hb hm hβ hχ0 hχ
      uStar huStar u v huv hmass
  simpa [intervalDomainPaper3Constants, minimalVLowerFormula] using hbound

/-- Concrete-constants Paper3 Theorem 2.1 on the interval from the four
exposed persistence frontiers.  This removes the constants-package projection:
the minimal branch uses the literal `uBar` and Gaussian constant `1` from
`intervalDomainPaper3Constants`. -/
theorem intervalDomain_Theorem_2_1_for_concrete_constants_of_uniformPersistence_frontiers
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (h1 : UniformPersistencePart1Raw intervalDomain p)
    (h2 : UniformPersistencePart2Raw intervalDomain p)
    (h3 : UniformPersistencePart3Raw intervalDomain p)
    (h4 : UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1) :
    Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  Theorem_2_1.of_parts
    (intervalDomain_Theorem_2_1_part1_of_uniformPersistenceRaw p h1)
    (intervalDomain_Theorem_2_1_part2_of_uniformPersistenceRaw p h2)
    (intervalDomain_Theorem_2_1_part3_of_uniformPersistenceRaw p h3)
    (intervalDomain_Theorem_2_1_part4_for_concrete_constants_of_uniformPersistenceRaw
      p M0 uBar vLower h4)

/-- Paper2-style existence/frontier package for the StabilityChain Theorem 2.1
mainline.

This is the current honest reduction point: the interval norm-continuity input
is concrete, and persistence is the concrete interval package from the
sectorial bridge.  No `StabilityNorms`, `CompactnessData`, or
`Paper3Constants` field projection remains in the theorem interface. -/
structure IntervalDomainStabilityChainTheorem21Existence
    (p : CM2Params) (uBar : ℝ) where
  initialContinuity : IntervalDomainInitialContinuityRaw p
  persistence : IntervalDomainSectorialTheorem21Persistence p uBar

/-- The StabilityChain existence package supplies the lower-level persistence
frontiers used by the raw theorem assembler. -/
theorem IntervalDomainStabilityChainTheorem21Existence.to_persistenceFrontiers
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainStabilityChainTheorem21Existence p uBar) :
    IntervalDomainSectorialTheorem21PersistenceFrontiers p uBar :=
  h.persistence.to_persistenceFrontiers

/-- Paper3 Theorem 2.1 for the concrete StabilityChain constants, reduced to
the Paper2-style interval existence/frontier package. -/
theorem intervalDomain_Theorem_2_1_for_concrete_constants_of_existence
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hexist : IntervalDomainStabilityChainTheorem21Existence p uBar) :
    Theorem_2_1 intervalDomain p
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_1_for_concrete_constants_of_uniformPersistence_frontiers
    p M0 uBar vLower
    hexist.persistence.part1 hexist.persistence.part2
    hexist.persistence.part3 hexist.persistence.part4

/-- Combined concrete Paper3 mainline for the interval: norm-continuity is
specialized to `intervalDomainStabilityNorms`, upper-envelope monotonicity is
specialized to the concrete sup norm, and Theorem 2.1 is reduced to the
Paper2-style interval existence/frontier package. -/
theorem intervalDomain_norm_upperEnvelope_persistence_mainline
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hexist : IntervalDomainStabilityChainTheorem21Existence p uBar) :
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms ∧
      UpperEnvelopeMonotonicityRaw intervalDomain p intervalDomain.supNorm ∧
      Theorem_2_1 intervalDomain p
        (intervalDomainPaper3Constants p M0 uBar vLower) :=
  ⟨intervalDomain_Lemma_3_3_for_concreteStabilityNorms_of_initialContinuityRaw
      p hexist.initialContinuity,
    intervalDomain_upperEnvelopeMonotonicityRaw_supNorm p,
    intervalDomain_Theorem_2_1_for_concrete_constants_of_existence
      p M0 uBar vLower hexist⟩

/-- Concrete StabilityChain mainline for Paper3 Theorem 2.1 with no
`StabilityNorms` or `CompactnessData` projection left in the statement.

The norm-continuity component is specialized to
`intervalDomainStabilityNorms`; the upper-envelope component is the already
proved concrete `supNorm` monotonicity; and the persistence component is
reduced to the Paper2-style interval existence/frontier package and the
explicit interval constants. -/
theorem intervalDomain_Theorem_2_1_for_concreteStabilityNorms_mainline
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (hexist : IntervalDomainStabilityChainTheorem21Existence p uBar) :
    Lemma_3_3 intervalDomain p intervalDomainStabilityNorms ∧
      UpperEnvelopeMonotonicityRaw intervalDomain p intervalDomain.supNorm ∧
      Theorem_2_1 intervalDomain p
        (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_norm_upperEnvelope_persistence_mainline
    p M0 uBar vLower hexist

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
          huStar htheta huv (lt_of_lt_of_le hs ht))
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

/-- Concrete-norm version of the branch-specific Theorem 2.2 wrapper.  The
`X^σ_p ≤ supNorm` side conditions are discharged by
`intervalDomainStabilityNorms`. -/
theorem intervalDomain_Theorem_2_2_for_concreteStabilityNorms_branch_frontiers
    (p : CM2Params)
    (M0 uBar vLower : ℝ)
    (hraw :
      SectorialLocalExponentialRaw intervalDomain p unitIntervalNeumannSpectrum
        intervalDomainStabilityNorms.c1Distance
        intervalDomainStabilityNorms.xpSigmaDistance)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hexistPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b), ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta)
    (hmexistMinimal :
      ∀ uStar, 0 < uStar → ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_for_concrete_constants_branch_frontiers
    p intervalDomainStabilityNorms M0 uBar vLower hraw
    hsigma_low hsigma_high hpNorm
    (fun ha hb =>
      intervalDomainStabilityNorms_xpSigma_le_supNorm sigma pNorm
        (positiveEquilibrium p ⟨ha, hb⟩).1)
    hexistPositive
    (fun uStar _huStar =>
      intervalDomainStabilityNorms_xpSigma_le_supNorm sigma pNorm
        (minimalEquilibrium p uStar).1)
    hmexistMinimal

/-- Concrete-norm Theorem 2.2 wrapper with the raw sectorial package replaced by
the interval spectral-semigroup orbit frontier.  The exponential semigroup
decay is discharged in `IntervalDomainSectorial.lean`; this theorem removes the
abstract `StabilityNorms` and norm-control arguments from the StabilityChain
side. -/
theorem
intervalDomain_Theorem_2_2_for_concreteStabilityNorms_spectralSemigroup_frontiers
    (p : CM2Params)
    (M0 uBar vLower : ℝ)
    (horbit :
      IntervalDomainSpectralSemigroupOrbitBoundRaw p
        intervalDomainStabilityNorms)
    {sigma pNorm : ℝ}
    (hsigma_low : 1 / 2 < sigma) (hsigma_high : sigma < 1)
    (hpNorm : 1 < pNorm)
    (hexistPositive :
      ∀ (ha : 0 < p.a) (hb : 0 < p.b), ∀ delta > 0,
        SmallDataGlobalExistence intervalDomain p
          (positiveEquilibrium p ⟨ha, hb⟩).1 delta)
    (hmexistMinimal :
      ∀ uStar, 0 < uStar → ∀ delta > 0,
        MassConstrainedSmallDataGlobalExistence intervalDomain p
          (minimalEquilibrium p uStar).1 delta) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum
      intervalDomainStabilityNorms
      (intervalDomainPaper3Constants p M0 uBar vLower) :=
  intervalDomain_Theorem_2_2_for_concreteStabilityNorms_branch_frontiers
    p M0 uBar vLower
    (intervalDomain_sectorialLocalExponentialRaw_of_spectralSemigroupOrbitBound
      p intervalDomainStabilityNorms horbit)
    hsigma_low hsigma_high hpNorm hexistPositive hmexistMinimal

/-- Full interval-domain Paper3 Theorem 2.2 from the two raw local-stability
branches plus the audited unit-interval critical-spectrum identity.

The raw branches supply exactly the stable/local-exponential halves.  The
unstable halves are discharged from the concrete Neumann spectrum through
`Paper3ConstantsUsesCriticalSpectrum`, so this theorem is a genuine
statement-layer composition rather than a restatement of `Theorem_2_2`. -/
theorem intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw
    (p : CM2Params)
    (N : StabilityNorms intervalDomain)
    (C : Paper3Constants intervalDomain p)
    (hC : Paper3ConstantsUsesCriticalSpectrum unitIntervalNeumannSpectrum p C)
    (hNonminimal :
      LinearStabilityInstabilityNonminimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance C.chiCritical)
    (hMinimal :
      LinearStabilityInstabilityMinimalRaw intervalDomain p
        unitIntervalNeumannSpectrum N.c1Distance C.chiCritical) :
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N C := by
  refine Theorem_2_2.of_parts ?_ ?_ ?_ ?_
  · intro ha hb
    exact hNonminimal ha hb
  · intro ha hb
    dsimp
    intro hχcrit
    exact hC.positiveEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum ha hb hχcrit
  · intro ha hb uStar huStar
    exact hMinimal ha hb uStar huStar
  · intro _ha _hb uStar huStar
    dsimp
    intro hχcrit
    exact hC.minimalEquilibrium_linearlyUnstable
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar hχcrit

/-- Constants-package interval-domain Paper3 Theorem 2.2 assembled through
branch-specific H3.1 frontiers.

This version is more general than the concrete-constants wrapper: it works for
any `Paper3Constants` package whose `chiCritical` field is identified with the
unit-interval spectral critical sensitivity. -/
theorem intervalDomain_Theorem_2_2_of_branch_frontiers_criticalSpectrum
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
    Theorem_2_2 intervalDomain p unitIntervalNeumannSpectrum N C := by
  have hbranches :=
    intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers_criticalSpectrum
      p N C hC hraw hsigma_low hsigma_high hpNorm
      hxpPositive hexistPositive hxpMinimal hmexistMinimal
  exact
    intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw
      p N C hC hbranches.1 hbranches.2

/-- Concrete-constants interval-domain Paper3 Theorem 2.2 assembled through
the branch-specific `LinearStabilityInstabilityRaw` interface.

Compared with the direct branch theorem above, this records the H3.1/H4.1
boundary explicitly: `intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers`
provides the two stable local-exponential raw branches, and
`intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw` supplies the
full Theorem 2.2 unstable branches from the unit-interval spectral formula. -/
theorem intervalDomain_Theorem_2_2_for_concrete_constants_branch_frontiers_via_linearRaw
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
  have hbranches :=
    intervalDomain_linearStabilityInstabilityRaw_of_branch_frontiers
      p N hraw hsigma_low hsigma_high hpNorm hxpPositive hexistPositive
      hxpMinimal hmexistMinimal
  exact
    intervalDomain_Theorem_2_2_of_linearStabilityInstabilityRaw
      p N (intervalDomainPaper3Constants p M0 uBar vLower)
      (intervalDomainPaper3Constants_usesCriticalSpectrum p M0 uBar vLower)
      (by
        simpa [intervalDomainPaper3Constants] using hbranches.1)
      (by
        simpa [intervalDomainPaper3Constants] using hbranches.2)

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

/-! ### Concrete-norm global stability wrappers -/

/-- Concrete-norm Theorem 2.3 from the explicit persistence/global-convergence
and uniform exponential-upgrade frontiers. -/
theorem intervalDomain_Theorem_2_3_for_concreteStabilityNorms_of_persistence_exp_frontiers
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
                  intervalDomainStabilityNorms u v eq.1 eq.2 A rate)
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
                  intervalDomainStabilityNorms u v eq.1 eq.2 A rate) :
    Theorem_2_3 intervalDomain p intervalDomainStabilityNorms :=
  intervalDomain_Theorem_2_3_of_persistence_exp_frontiers
    p intervalDomainStabilityNorms
    hglobalNonminimal hglobalMinimal hExpNonminimal hExpMinimal

/-- Concrete-norm Theorem 2.4 from explicit persistence and uniform
exponential-upgrade frontiers. -/
theorem intervalDomain_Theorem_2_4_for_concreteStabilityNorms_of_persistence_exp_frontiers
    (p : CM2Params)
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
                  ExponentialC1ConvergenceWith intervalDomain
                    intervalDomainStabilityNorms u v eq.1 eq.2 A rate) :
    Theorem_2_4 intervalDomain p intervalDomainStabilityNorms C :=
  intervalDomain_Theorem_2_4_of_persistence_exp_frontiers
    p intervalDomainStabilityNorms C hglobal hExp

/-- Concrete-norm Theorem 2.5 from explicit minimal-model persistence and
uniform exponential-upgrade frontiers. -/
theorem intervalDomain_Theorem_2_5_for_concreteStabilityNorms_of_persistence_exp_frontiers
    (p : CM2Params)
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
                  ExponentialC1ConvergenceWith intervalDomain
                    intervalDomainStabilityNorms u v eq.1 eq.2 A rate) :
    Theorem_2_5 intervalDomain p intervalDomainStabilityNorms C :=
  intervalDomain_Theorem_2_5_of_persistence_exp_frontiers
    p intervalDomainStabilityNorms C hglobal hExp

end

end ShenWork.Paper3
