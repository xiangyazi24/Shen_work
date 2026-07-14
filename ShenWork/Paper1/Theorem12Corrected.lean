import ShenWork.Paper1.Theorem12WeightedResolver
import ShenWork.Paper1.CStarStarSpecSatisfiable
import ShenWork.Paper1.Theorem12CoordinateAudit
import ShenWork.Paper1.Theorem12Section5Budgets
import ShenWork.Paper1.WavePositiveConstruction
import ShenWork.Paper1.WaveStabilityUpgrade

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Faithful moving-coordinate form of Paper 1 Theorem 1.2

The paper's Section 5 proof is written after transforming the Cauchy solution
to the frame moving at speed `c`.  This file states that conclusion with the
weight in the same coordinate.  It also puts the regularity of a “traveling
wave solution” explicitly in the Lean signature: the bare repository
`IsTravelingWave` structure records pointwise `deriv` equations but does not
logically imply differentiability.
-/

/-- Laboratory solution observed in the coordinate moving at speed `c`. -/
def coMovingPath (c : ℝ) (u : ℝ → ℝ → ℝ) (t z : ℝ) : ℝ :=
  u t (z + c * t)

/-- Paper 1 Theorem 1.2 with all three statement defects repaired:

* the weighted norm is in the moving coordinate used in Section 5;
* the lower weight endpoint is the perturbed root from (5.31), not `kappa c`;
* classical wave regularity is explicit.

The budget is existential output of the theorem.  Its `cap_between` field
certifies that the corrected weight interval is nonempty at every admitted
speed. -/
def Theorem_1_2_amended : Prop :=
  ∀ p : CMParams, StableWaveParameterRegime p →
    ∃ cStarStar : ℝ → ℝ, ∃ budget : Paper531StabilityBudget p cStarStar,
      StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
      stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
      ∀ c : ℝ, cStarStar p.χ < c →
      ∀ U V : ℝ → ℝ,
        IsTravelingWave p c U V →
        TravelingWaveRegularity p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ, paper531RootMinus c budget.A budget.B < η →
          η < stabilityWeightCap p →
          ∀ u₀ : ℝ → ℝ,
            NonnegativeInitialDatum u₀ →
            StrictlyPositiveAtLeft u₀ →
            WeightedL2InitialCloseness η u₀ U →
            ∃ u v : ℝ → ℝ → ℝ,
              IsGlobalCauchySolutionFrom p u₀ u v ∧
              CoMovingWeightedL2Convergence η c u U ∧
              UniformMovingFrameConvergence c u U

/-! ## Closed scalar energy and Step 4 endpoints -/

theorem CoMovingWeightedL2Convergence.of_eventual_bound_tendsto_zero
    {η c : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {B : ℝ → ℝ}
    (hB : Tendsto B atTop (𝓝 0))
    (hbound : ∀ᶠ t in atTop, coMovingWeightedL2Energy η c u U t ≤ B t)
    (henergy_int : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * η * z) * |u t (z + c * t) - U z| ^ 2)) :
    CoMovingWeightedL2Convergence η c u U := by
  unfold CoMovingWeightedL2Convergence
  refine ⟨henergy_int, ?_⟩
  have hnonneg : ∀ᶠ t in atTop, 0 ≤ coMovingWeightedL2Energy η c u U t :=
    Eventually.of_forall fun t => integral_nonneg fun z =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  exact squeeze_zero' hnonneg hbound hB

theorem CoMovingWeightedL2Convergence.of_eventual_exponential_decay
    {η c lam A : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hlam : 0 < lam)
    (hdecay : ∀ᶠ t in atTop,
      coMovingWeightedL2Energy η c u U t ≤ A * Real.exp (-lam * t))
    (henergy_int : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * η * z) * |u t (z + c * t) - U z| ^ 2)) :
    CoMovingWeightedL2Convergence η c u U := by
  have hmul : Tendsto (fun t : ℝ => lam * t) atTop atTop := by
    simpa [mul_comm] using Filter.tendsto_id.atTop_mul_const hlam
  have hneg : Tendsto (fun t : ℝ => -(lam * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(lam * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hupper : Tendsto (fun t : ℝ => A * Real.exp (-lam * t)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hexp
  exact CoMovingWeightedL2Convergence.of_eventual_bound_tendsto_zero
    hupper hdecay henergy_int

theorem CoMovingWeightedL2Convergence.of_energy_dissipation
    {η c lam : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {E : ℝ → ℝ}
    (hlam : 0 < lam)
    (hcontrol : ∀ᶠ t in atTop, coMovingWeightedL2Energy η c u U t ≤ E t)
    (henergy_int : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * η * z) * |u t (z + c * t) - U z| ^ 2))
    (hcont : ∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T))
    (hderiv : ∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt E (deriv E t) (Set.Ici t) t)
    (hdiss : ∀ t : ℝ, 0 ≤ t → deriv E t ≤ -lam * E t) :
    CoMovingWeightedL2Convergence η c u U := by
  have hE_decay : ∀ᶠ t in atTop, E t ≤ E 0 * Real.exp (-lam * t) :=
    scalarEnergy_eventual_exponential_bound_of_deriv_le hcont hderiv hdiss
  have hdecay : ∀ᶠ t in atTop,
      coMovingWeightedL2Energy η c u U t ≤ E 0 * Real.exp (-lam * t) := by
    filter_upwards [hcontrol, hE_decay] with t hctrl hE
    exact hctrl.trans hE
  exact CoMovingWeightedL2Convergence.of_eventual_exponential_decay
    hlam hdecay henergy_int

/-- The scalar closure in the native coefficient of (5.31).  The PDE energy
calculation only has to prove `E' ≤ 2 q(eta) E`; negativity of the perturbed
quadratic supplies the positive decay rate `-2 q(eta)` internally. -/
theorem CoMovingWeightedL2Convergence.of_paper531_energy_inequality
    {η c A B : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {E : ℝ → ℝ}
    (hq : paper531Quadratic c A B η < 0)
    (hcontrol : ∀ᶠ t in atTop, coMovingWeightedL2Energy η c u U t ≤ E t)
    (henergy_int : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * η * z) * |u t (z + c * t) - U z| ^ 2))
    (hcont : ∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T))
    (hderiv : ∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt E (deriv E t) (Set.Ici t) t)
    (hdiss : ∀ t : ℝ, 0 ≤ t →
      deriv E t ≤ 2 * paper531Quadratic c A B η * E t) :
    CoMovingWeightedL2Convergence η c u U := by
  let lam : ℝ := -2 * paper531Quadratic c A B η
  have hlam : 0 < lam := by dsimp [lam]; linarith
  apply CoMovingWeightedL2Convergence.of_energy_dissipation
    (lam := lam) hlam hcontrol henergy_int hcont hderiv
  intro t ht
  have h := hdiss t ht
  dsimp [lam]
  convert h using 1 <;> ring

/-- The proved interval-localization upgrade applied in the stationary wave
coordinate.  All three extra hypotheses are genuine Step 4 inputs; weighted
`L²` decay alone is not enough at the left end. -/
theorem uniformMovingFrameConvergence_of_coMovingWeightedL2_of_step4
    {η c : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hη : 0 < η)
    (henergy_int :
      EventuallyIntegrableMovingFrameEnergy η 0 (coMovingPath c u) U)
    (hweighted : CoMovingWeightedL2Convergence η c u U)
    (hmod :
      EventuallyUniformMovingFrameSpatialModulus 0 (coMovingPath c u) U)
    (hleft : UniformMovingFrameLeftTailConvergence 0 (coMovingPath c u) U) :
    UniformMovingFrameConvergence c u U := by
  have hweighted_zero :
      WeightedL2MovingFrameConvergence η 0 (coMovingPath c u) U := by
    unfold CoMovingWeightedL2Convergence coMovingWeightedL2Energy at hweighted
    unfold WeightedL2MovingFrameConvergence
    simpa [coMovingPath] using hweighted.2
  have huniform_zero :
      UniformMovingFrameConvergence 0 (coMovingPath c u) U :=
    uniformMovingFrameConvergence_of_weightedL2_of_spatialModulus_of_leftTail
      hη (le_refl 0) henergy_int hweighted_zero hmod hleft
  intro ε hε
  rcases huniform_zero ε hε with ⟨T, hT⟩
  refine ⟨T, fun t x ht => ?_⟩
  have hz := hT t (x - c * t) ht
  simpa [coMovingPath] using hz

/-! ## The already-proved Section 5 signal block -/

/-- The exact profile/initial-datum signal estimate consumed by the nonlinear
energy calculation, at the theorem's canonical exponent `2`. -/
abbrev Section5ProfileInitialSignalBounds
    (p : CMParams) (U V u₀ : ℝ → ℝ) : Prop :=
  ∃ kMax > 0, ∃ C > 0,
    ∀ k : ℝ, 0 ≤ k → k < kMax →
    ∀ psi : ExponentialWeight,
      (∀ z, |deriv psi.weight z| ≤ k * psi.weight z) →
      (∀ z, |iteratedDeriv 2 psi.weight z| ≤ k * psi.weight z) →
      Integrable (fun x : ℝ => (U x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
      Integrable (fun x : ℝ => (u₀ x) ^ (p.γ * (2 : ℝ)) * psi.weight x) →
        (Integrable (fun x : ℝ => |deriv V x| ^ (2 : ℝ) * psi.weight x) ∧
          ∫ x : ℝ, |deriv V x| ^ (2 : ℝ) * psi.weight x ≤
            C * ∫ x : ℝ, (U x) ^ (p.γ * (2 : ℝ)) * psi.weight x) ∧
        (Integrable
            (fun x : ℝ =>
              |deriv (frozenElliptic p u₀) x| ^ (2 : ℝ) * psi.weight x) ∧
          ∫ x : ℝ, |deriv (frozenElliptic p u₀) x| ^ (2 : ℝ) * psi.weight x ≤
            C * ∫ x : ℝ, (u₀ x) ^ (p.γ * (2 : ℝ)) * psi.weight x)

theorem section5ProfileInitialSignalBounds_proved
    (p : CMParams) {c : ℝ} {U V u₀ : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hu₀ : NonnegativeInitialDatum u₀) :
    Section5ProfileInitialSignalBounds p U V u₀ :=
  Lemma_5_3_profile_initial_signal_derivative_from_Lemma_2_5
    p (by norm_num) hTW hreg hbound hu₀

/-! ## Honest one-core capstone

The remaining hypothesis below is deliberately not hidden in a structure and
does not contain either convergence conclusion.  It is the exact whole-line
Cauchy/perturbation/Step 4 analytic block still missing after Lemma 2.5,
Lemma 5.3, scalar Grönwall, and interval localization have been discharged.
-/

theorem paper1_Theorem_1_2_amended_of_wholeLineCauchyEnergyStep4
    (cStarStarFn : CMParams → ℝ → ℝ)
    (hcStarStar : ∀ p : CMParams, StableWaveParameterRegime p →
      StabilitySpeedThresholdFamilyAsymptotic p (cStarStarFn p) ∧
        stabilitySpeedBaseline p ≤ cStarStarFn p p.χ)
    (hbudget : ∀ p : CMParams,
      Paper531StabilityBudget p (cStarStarFn p))
    (hcore :
      ∀ p : CMParams, StableWaveParameterRegime p →
      ∀ c : ℝ, cStarStarFn p p.χ < c →
      ∀ U V u₀ : ℝ → ℝ,
        IsTravelingWave p c U V →
        TravelingWaveRegularity p c U V →
        HasStrictWaveUpperTailBound p c U →
        (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧ HasWaveRightTailAsymptotic c κ₁ U) →
        ∀ η : ℝ,
          paper531RootMinus c (hbudget p).A (hbudget p).B < η →
          η < stabilityWeightCap p →
          NonnegativeInitialDatum u₀ →
          StrictlyPositiveAtLeft u₀ →
          WeightedL2InitialCloseness η u₀ U →
          Section5ProfileInitialSignalBounds p U V u₀ →
          ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ,
            IsGlobalCauchySolutionFrom p u₀ u v ∧
            (∀ᶠ t in atTop, coMovingWeightedL2Energy η c u U t ≤ E t) ∧
            (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
            (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
              HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
            (∀ t : ℝ, 0 ≤ t → deriv E t ≤
              2 * paper531Quadratic c (hbudget p).A (hbudget p).B η * E t) ∧
            EventuallyIntegrableMovingFrameEnergy η 0 (coMovingPath c u) U ∧
            EventuallyUniformMovingFrameSpatialModulus 0 (coMovingPath c u) U ∧
            UniformMovingFrameLeftTailConvergence 0 (coMovingPath c u) U) :
    Theorem_1_2_amended := by
  intro p hregime
  rcases hcStarStar p hregime with ⟨hasymp, hbaseline⟩
  refine ⟨cStarStarFn p, hbudget p, hasymp, hbaseline, ?_⟩
  intro c hc U V hTW hreg hstrict htail η hroot heta u₀ hu₀ hleft hclose
  have hsignal : Section5ProfileInitialSignalBounds p U V u₀ :=
    section5ProfileInitialSignalBounds_proved p hTW hreg
      hstrict.hasWaveUpperTailBound hu₀
  rcases hcore p hregime c hc U V u₀ hTW hreg hstrict htail η hroot heta
      hu₀ hleft hclose hsignal with
    ⟨u, v, E, hsol, hcontrol, hcont, hderiv, hdiss,
      hint, hmod, hleftStep4⟩
  have hint_direct : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * η * z) * |u t (z + c * t) - U z| ^ 2) := by
    simpa [EventuallyIntegrableMovingFrameEnergy, movingFrameError,
      coMovingPath] using hint
  have hweighted : CoMovingWeightedL2Convergence η c u U :=
    CoMovingWeightedL2Convergence.of_paper531_energy_inequality
      ((hbudget p).quadratic_neg hc hroot heta)
      hcontrol hint_direct hcont hderiv hdiss
  have hη : 0 < η :=
    (hbudget p).rootMinus_pos hc |>.trans hroot
  exact ⟨u, v, hsol, hweighted,
    uniformMovingFrameConvergence_of_coMovingWeightedL2_of_step4
      hη hint hweighted hmod hleftStep4⟩

/-! ## Non-vacuity of the amended conclusion -/

theorem IsTravelingWave.coMovingWeightedL2Convergence_self
    {p : CMParams} {c η : ℝ} {U V : ℝ → ℝ}
    (_hTW : IsTravelingWave p c U V) :
    CoMovingWeightedL2Convergence η c
      (fun t x => U (x - c * t)) U := by
  unfold CoMovingWeightedL2Convergence coMovingWeightedL2Energy
  simp

theorem Theorem_1_2_amended_self_initial_data_nonvacuous
    {p : CMParams} {c η : ℝ} {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hstrict : HasStrictWaveUpperTailBound p c U)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V) :
    NonnegativeInitialDatum U ∧
      StrictlyPositiveAtLeft U ∧
      WeightedL2InitialCloseness η U U ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U u v ∧
        CoMovingWeightedL2Convergence η c u U ∧
        UniformMovingFrameConvergence c u U := by
  refine ⟨hstrict.nonnegativeInitialDatum_of_continuous hU_diff.continuous,
    IsTravelingWave.strictlyPositiveAtLeft hTW,
    WeightedL2InitialCloseness.refl η U, ?_⟩
  exact ⟨fun t x => U (x - c * t), fun t x => V (x - c * t),
    IsTravelingWave.to_globalCauchySolutionFrom hTW hU_diff hV_diff,
    IsTravelingWave.coMovingWeightedL2Convergence_self hTW,
    IsTravelingWave.uniformMovingFrameConvergence_self hTW⟩

/-- A concrete positive-attraction instance of the amended conclusion.
The wave and both `C²` profiles come from the genuine Paper 1 Schauder
construction, so none of the hypotheses in the preceding self-data lemma is
an abstract consistency assumption. -/
theorem Theorem_1_2_amended_self_initial_data_concrete_nonvacuous :
    ∃ p : CMParams, ∃ c η : ℝ, ∃ U V : ℝ → ℝ,
      0 < p.χ ∧ 2 < c ∧ StableWaveParameterRegime p ∧
      (∃ cStarStar : ℝ → ℝ,
        StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
        cStarStar p.χ < c) ∧
      IsTravelingWave p c U V ∧
      TravelingWaveRegularity p c U V ∧
      HasStrictWaveUpperTailBound p c U ∧
      (∃ κ₁, kappa c < κ₁ ∧ κ₁ < 1 ∧
        HasWaveRightTailAsymptotic c κ₁ U) ∧
      kappa c < η ∧
      η < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) ∧
      NonnegativeInitialDatum U ∧
      StrictlyPositiveAtLeft U ∧
      WeightedL2InitialCloseness η U U ∧
      ∃ u v : ℝ → ℝ → ℝ,
        IsGlobalCauchySolutionFrom p U u v ∧
        CoMovingWeightedL2Convergence η c u U ∧
        UniformMovingFrameConvergence c u U := by
  let p : CMParams :=
    { m := 1
      α := 1
      γ := 1
      χ := 1 / 4
      hm := by norm_num
      hα := by norm_num
      hγ := by norm_num }
  have hα : p.α = p.m + p.γ - 1 := by norm_num [p]
  have hχ0 : 0 ≤ p.χ := by norm_num [p]
  have hχpos : 0 < p.χ := by norm_num [p]
  have hχsmall : p.χ < min (1 / 2 : ℝ) (chiStar p) := by
    norm_num [p, chiStar]
  have hχstar : p.χ < chiStar p :=
    lt_of_lt_of_le hχsmall (min_le_right _ _)
  have hχ1 : p.χ < 1 := by norm_num [p]
  have hc : (2 : ℝ) < 3 := by norm_num
  have hpow_lt : |p.χ| ^ (1 / 6 : ℝ) < 1 := by
    apply Real.rpow_lt_one
    · positivity
    · norm_num [p]
    · norm_num
  have hcStarStar_lt : cStarStarWitness p p.χ < 3 := by
    unfold cStarStarWitness
    norm_num [p] at hpow_lt ⊢
    linarith
  have hthreshold :
      ∃ cStarStar : ℝ → ℝ,
        StabilitySpeedThresholdFamilyAsymptotic p cStarStar ∧
        stabilitySpeedBaseline p ≤ cStarStar p.χ ∧
        cStarStar p.χ < 3 :=
    ⟨cStarStarWitness p, cStarStarWitness_asymptotic p,
      stabilitySpeedBaseline_le_cStarStarWitness p, hcStarStar_lt⟩
  obtain ⟨U, hprofile, hU2, hV2, hreg, hupper, htail⟩ :=
    paper1_positiveConstruction_selfStep p hα hχ0 hχsmall 3 hc
  let V : ℝ → ℝ := frozenElliptic p U
  have hTW : IsTravelingWave p 3 U V := by
    simpa [V] using hprofile.to_travelingWave
  have hstrict : HasStrictWaveUpperTailBound p 3 U :=
    hupper.hasStrictWaveUpperTailBound hχ0 hχ1
  have hkappa_pos : 0 < kappa (3 : ℝ) :=
    kappa_pos_of_two_lt hc
  have hkappa_one : kappa (3 : ℝ) < 1 :=
    kappa_lt_one_of_two_lt hc
  have hkappa_tailCap :
      kappa (3 : ℝ) <
        min ((1 + p.α) * kappa 3)
          (min (p.m * kappa 3 + 1 / 2) 1) := by
    apply lt_min
    · norm_num [p]
      linarith
    · apply lt_min
      · norm_num [p]
      · exact hkappa_one
  obtain ⟨κ₁, hkappa_κ₁, hκ₁_cap⟩ := exists_between hkappa_tailCap
  have hκ₁_one : κ₁ < 1 :=
    lt_of_lt_of_le hκ₁_cap
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have htail_exists :
      ∃ κ₁, kappa (3 : ℝ) < κ₁ ∧ κ₁ < 1 ∧
        HasWaveRightTailAsymptotic 3 κ₁ U :=
    ⟨κ₁, hkappa_κ₁, hκ₁_one,
      htail κ₁ hkappa_κ₁ hκ₁_cap⟩
  have hkappa_half : kappa (3 : ℝ) < 1 / 2 := by
    unfold kappa
    have hsqrt_gt :
        (3 : ℝ) - 1 < Real.sqrt ((3 : ℝ) ^ 2 - 4) :=
      Real.lt_sqrt_of_sq_lt (by norm_num)
    norm_num at hsqrt_gt ⊢
    linarith
  have hhalf_cap :
      (1 / 2 : ℝ) < 1 / (1 + |p.χ| ^ (1 / 6 : ℝ)) := by
    have hden_pos : 0 < 1 + |p.χ| ^ (1 / 6 : ℝ) := by
      positivity
    rw [lt_div_iff₀ hden_pos]
    nlinarith
  have hself :=
    Theorem_1_2_amended_self_initial_data_nonvacuous
      (η := 1 / 2) hTW hstrict hU2 (by simpa [V] using hV2)
  exact ⟨p, 3, 1 / 2, U, V, hχpos, hc,
    StableWaveParameterRegime.of_positive hχ0 hχstar hα,
    hthreshold, hTW, by simpa [V] using hreg, hstrict, htail_exists,
      hkappa_half, hhalf_cap, hself⟩

section Theorem12CorrectedAxiomAudit
#print axioms CoMovingWeightedL2Convergence.of_energy_dissipation
#print axioms CoMovingWeightedL2Convergence.of_paper531_energy_inequality
#print axioms uniformMovingFrameConvergence_of_coMovingWeightedL2_of_step4
#print axioms section5ProfileInitialSignalBounds_proved
#print axioms paper1_Theorem_1_2_amended_of_wholeLineCauchyEnergyStep4
#print axioms Theorem_1_2_amended_self_initial_data_nonvacuous
#print axioms Theorem_1_2_amended_self_initial_data_concrete_nonvacuous
end Theorem12CorrectedAxiomAudit

end ShenWork.Paper1
