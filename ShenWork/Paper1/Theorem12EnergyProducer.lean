import ShenWork.Paper1.Theorem12ConcreteBudget

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Corrected Paper 1 stability-energy producer

This file connects the concrete corrected speed threshold to the actual
moving-frame energy and to the already-proved whole-line elliptic estimate.
It keeps only genuine Cauchy regularity, integrability, and continuation data
for the later parabolic producer.
-/

theorem remark5SpeedCondition_of_correctedCStarStar_lt
    (p : CMParams) {c : ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c) :
    remark5SpeedCondition p c paper5Sigma := by
  unfold remark5SpeedCondition
  exact (paper5CorrectedCStarStar_remark_le p).trans_lt hc

theorem barrierSpeed_lt_of_correctedCStarStar_lt
    (p : CMParams) {c : ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c) :
    paper52MonotoneBarrierSpeed p < c :=
  (paper5CorrectedCStarStar_barrier_le p).trans_lt hc

/-- Twice the natural half-energy is the scalar energy used by the theorem
statement. -/
def paper5WeightedEnergy
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * paper5WeightedHalfEnergy η c u U t

theorem paper5WeightedEnergy_eq_coMovingWeightedL2Energy
    (η c : ℝ) (u : ℝ → ℝ → ℝ) (U : ℝ → ℝ) (t : ℝ) :
    paper5WeightedEnergy η c u U t =
      coMovingWeightedL2Energy η c u U t := by
  unfold paper5WeightedEnergy paper5WeightedHalfEnergy
    ShenWork.PaperOne.wholeLineHalfEnergy coMovingWeightedL2Energy
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold paper5WeightedPopulation coMovingPath
  rw [sq_abs, mul_pow]
  have hexp : Real.exp (η * x) ^ 2 = Real.exp (2 * η * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Lemma 5.3 in the exact moving-frame signal fields used by the corrected
energy identity.  The two elliptic equalities are the canonical-resolver
property of the Cauchy solution and of the wave; after those identifications,
no signal estimate remains external. -/
theorem paper5WeightedSignal_resolver_bounds
    (p : CMParams) {M η c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 1 ≤ M) (hη : 0 < η) (hη1 : η < 1)
    (hu : IsCUnifBdd (coMovingPath c u t)) (hU : IsCUnifBdd U)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hVEq : V = frozenElliptic p U)
    (hvDiff : Differentiable ℝ (coMovingPath c v t))
    (hVDiff : Differentiable ℝ V)
    (hclose : Integrable (fun x =>
      Real.exp (2 * η * x) *
        |coMovingPath c u t x - U x| ^ 2)) :
    (∫ x : ℝ,
        (paper5WeightedSignal η (coMovingPath c v) V t x) ^ 2) ≤
        paper5WeightedResolverVFactor p M η *
          ∫ x : ℝ,
            (paper5WeightedPopulation η (coMovingPath c u) U t x) ^ 2 ∧
      (∫ x : ℝ,
        (paper5WeightedSignalX η (coMovingPath c v) V t x) ^ 2) ≤
        paper5WeightedResolverVxFactor p M η *
          ∫ x : ℝ,
            (paper5WeightedPopulation η (coMovingPath c u) U t x) ^ 2 := by
  have hraw := weighted_frozenElliptic_difference_l2_bound p hM hη hη1
    hU hu hUM huM hclose
  dsimp only at hraw
  have hZ :
      (fun x => Real.exp (η * x) *
        (frozenElliptic p (coMovingPath c u t) x -
          frozenElliptic p U x)) =
        paper5WeightedSignal η (coMovingPath c v) V t := by
    funext x
    simp only [paper5WeightedSignal]
    rw [hvEq, hVEq]
  have hZderiv :
      deriv (paper5WeightedSignal η (coMovingPath c v) V t) =
        paper5WeightedSignalX η (coMovingPath c v) V t := by
    funext x
    exact (paper5WeightedSignal_space_hasDerivAt
      (hvDiff x) (hVDiff x)).deriv
  constructor
  · simpa only [paper5WeightedPopulation, paper5WeightedSignal, hvEq, hVEq,
      paper5WeightedResolverVFactor, sq_abs] using hraw.1
  · have hrawx := hraw.2
    rw [hZ, hZderiv] at hrawx
    simpa only [paper5WeightedPopulation, paper5WeightedResolverVxFactor,
      sq_abs] using hrawx

/-- Lemma 5.3 with the two square-integrability facts needed by the
whole-line remainder integral. -/
theorem paper5WeightedSignal_resolver_data
    (p : CMParams) {M η c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 1 ≤ M) (hη : 0 < η) (hη1 : η < 1)
    (hu : IsCUnifBdd (coMovingPath c u t)) (hU : IsCUnifBdd U)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hVEq : V = frozenElliptic p U)
    (hvDiff : Differentiable ℝ (coMovingPath c v t))
    (hVDiff : Differentiable ℝ V)
    (hclose : Integrable (fun x =>
      Real.exp (2 * η * x) *
        |coMovingPath c u t x - U x| ^ 2)) :
    Integrable (fun x =>
        (paper5WeightedSignal η (coMovingPath c v) V t x) ^ 2) ∧
      Integrable (fun x =>
        (paper5WeightedSignalX η (coMovingPath c v) V t x) ^ 2) ∧
      (∫ x : ℝ,
        (paper5WeightedSignal η (coMovingPath c v) V t x) ^ 2) ≤
        paper5WeightedResolverVFactor p M η *
          ∫ x : ℝ,
            (paper5WeightedPopulation η (coMovingPath c u) U t x) ^ 2 ∧
      (∫ x : ℝ,
        (paper5WeightedSignalX η (coMovingPath c v) V t x) ^ 2) ≤
        paper5WeightedResolverVxFactor p M η *
          ∫ x : ℝ,
            (paper5WeightedPopulation η (coMovingPath c u) U t x) ^ 2 := by
  have hraw := weighted_frozenElliptic_difference_l2_data p hM hη hη1
    hU hu hUM huM hclose
  dsimp only at hraw
  have hZ :
      (fun x => Real.exp (η * x) *
        (frozenElliptic p (coMovingPath c u t) x -
          frozenElliptic p U x)) =
        paper5WeightedSignal η (coMovingPath c v) V t := by
    funext x
    simp only [paper5WeightedSignal]
    rw [hvEq, hVEq]
  have hZderiv :
      deriv (paper5WeightedSignal η (coMovingPath c v) V t) =
        paper5WeightedSignalX η (coMovingPath c v) V t := by
    funext x
    exact (paper5WeightedSignal_space_hasDerivAt
      (hvDiff x) (hVDiff x)).deriv
  have hVint : Integrable (fun x =>
      (paper5WeightedSignal η (coMovingPath c v) V t x) ^ 2) := by
    refine hraw.1.congr (Filter.Eventually.of_forall fun x => ?_)
    change (Real.exp (η * x) *
      (frozenElliptic p (coMovingPath c u t) x -
        frozenElliptic p U x)) ^ 2 =
      (paper5WeightedSignal η (coMovingPath c v) V t x) ^ 2
    rw [congrFun hZ x]
  have hVxint : Integrable (fun x =>
      (paper5WeightedSignalX η (coMovingPath c v) V t x) ^ 2) := by
    have hx := hraw.2.1
    rw [hZ, hZderiv] at hx
    exact hx
  have hbounds := paper5WeightedSignal_resolver_bounds p hM hη hη1
    hu hU huM hUM hvEq hVEq hvDiff hVDiff hclose
  exact ⟨hVint, hVxint, hbounds.1, hbounds.2⟩

/-- Fixed-positive-time corrected energy inequality for the actual Cauchy
solution.  The only remaining inputs are the time-Leibniz identity and the
standard whole-line integrability/decay conditions needed for integration by
parts.  Coefficient and signal estimates are produced internally. -/
theorem paper5WeightedHalfEnergy_deriv_le_concrete_of_timeLeibniz
    (p : CMParams) {T η c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hχ : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hη : 0 < η) (hηcap : η < stabilityWeightCap p)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) (MChi p))
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hclose : Integrable (fun x =>
      Real.exp (2 * η * x) *
        |coMovingPath c u t x - U x| ^ 2))
    (htime : deriv (paper5WeightedHalfEnergy η c u U) t =
      ∫ x, paper5WeightedPopulation η (coMovingPath c u) U t x *
        paper5WeightedPopulationT η
          (paper5CoMovingMaterialTime c u) t x)
    (hdiff_int : Integrable (fun x =>
      paper5WeightedPopulation η (coMovingPath c u) U t x *
        paper5WeightedPopulationXX η (coMovingPath c u) U t x))
    (hWx2 : Integrable (fun x =>
      (paper5WeightedPopulationX η (coMovingPath c u) U t x) ^ 2))
    (hdrift_int : Integrable (fun x =>
      paper5WeightedPopulationX η (coMovingPath c u) U t x *
        paper5WeightedPopulation η (coMovingPath c u) U t x))
    (hrem_int : Integrable
      (paper5CorrectedRemainderDensity p η c
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation η (coMovingPath c u) U t)
        (paper5WeightedPopulationX η (coMovingPath c u) U t)
        (paper5WeightedSignal η (coMovingPath c v) V t)
        (paper5WeightedSignalX η (coMovingPath c v) V t) t))
    (hdiff_decay_bot : Tendsto (fun x =>
      paper5WeightedPopulation η (coMovingPath c u) U t x *
        paper5WeightedPopulationX η (coMovingPath c u) U t x)
      atBot (𝓝 0))
    (hdiff_decay_top : Tendsto (fun x =>
      paper5WeightedPopulation η (coMovingPath c u) U t x *
        paper5WeightedPopulationX η (coMovingPath c u) U t x)
      atTop (𝓝 0))
    (hdrift_decay_bot : Tendsto (fun x =>
      paper5WeightedPopulation η (coMovingPath c u) U t x *
        paper5WeightedPopulation η (coMovingPath c u) U t x)
      atBot (𝓝 0))
    (hdrift_decay_top : Tendsto (fun x =>
      paper5WeightedPopulation η (coMovingPath c u) U t x *
        paper5WeightedPopulation η (coMovingPath c u) U t x)
      atTop (𝓝 0)) :
    deriv (paper5WeightedHalfEnergy η c u U) t ≤
      paper531Quadratic c (paper531ConcreteA p) (paper531ConcreteB p) η *
        ∫ x, (paper5WeightedPopulation η
          (coMovingPath c u) U t x) ^ 2 := by
  have hM1 : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hM0 : 0 ≤ MChi p := zero_le_one.trans hM1
  have hMpos : 0 < MChi p := zero_lt_one.trans_le hM1
  have huC : IsCUnifBdd (coMovingPath c u t) := by
    refine ⟨hu2.continuous, ⟨MChi p, fun x => ?_⟩⟩
    rw [abs_of_nonneg (huM x).1]
    exact (huM x).2
  have hUC : IsCUnifBdd U :=
    U_isCUnifBdd_of_continuous hbound hreg.U_cont
  have hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) (MChi p) :=
    fun x => ⟨(hTW.U_pos x).le, hbound.le_MChi x⟩
  have hVEq : V = frozenElliptic p U :=
    IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg
  have hγ0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
  have huγ : ∀ x, (coMovingPath c u t x) ^ p.γ ≤ (MChi p) ^ p.γ :=
    fun x => Real.rpow_le_rpow (huM x).1 (huM x).2 hγ0
  have hvUpper : ∀ x,
      coMovingPath c v t x ≤ (MChi p) ^ p.γ := by
    intro x
    rw [hvEq]
    exact frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM0 _)
      hu2.continuous (fun y => (huM y).1) huγ x
  have hvM : ∀ x,
      coMovingPath c v t x ∈ Set.Icc (0 : ℝ) ((MChi p) ^ p.γ) := by
    intro x
    constructor
    · rw [hvEq]
      exact frozenElliptic_nonneg p (fun y => (huM y).1) x
    · exact hvUpper x
  have hvDeriv : ∀ x,
      |deriv (coMovingPath c v t) x| ≤ (MChi p) ^ p.γ := by
    intro x
    have hvUpper' := hvUpper x
    rw [hvEq] at hvUpper'
    rw [hvEq]
    exact (frozenElliptic_deriv_abs_le p huC (fun y => (huM y).1) x).trans
      hvUpper'
  have hspeed := remark5SpeedCondition_of_correctedCStarStar_lt p hc
  have hbarrier := barrierSpeed_lt_of_correctedCStarStar_lt p hc
  have hcoeff : ∀ x,
      |paper5B1 p (coMovingPath c u) (coMovingPath c v) t x| ≤
          paper5ConcreteB1 p ∧
        |paper5B2 p (coMovingPath c u) (coMovingPath c v) U t x| ≤
          paper5ConcreteB2 p ∧
        |paper5B3 p U x| ≤ paper5ConcreteB3 p ∧
        |paper5B4 p U x| ≤ paper5ConcreteB4 p := by
    intro x
    have hx := paper5CoefficientBounds_of_barrier_speed_corrected_wave p
      (sigma := paper5Sigma) (t := t) (x := x)
      (by norm_num [paper5Sigma]) hχ hspeed hbarrier hTW hreg hbound
      (huM x) (hvDeriv x)
    simpa only [paper5ConcreteB1, paper5ConcreteB2, paper5ConcreteB3,
      paper5ConcreteB4, paper5ConcreteLu] using hx
  have hη1 : η < 1 := by
    have hcap1 : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    exact hηcap.trans_le hcap1
  have hsignal := paper5WeightedSignal_resolver_data p hM1 hη hη1
    huC hUC huM hUM hvEq hVEq
    (hv2.differentiable (by norm_num))
    (hV2.differentiable (by norm_num)) hclose
  have hW2 : Integrable (fun x =>
      (paper5WeightedPopulation η (coMovingPath c u) U t x) ^ 2) := by
    refine hclose.congr (Filter.Eventually.of_forall fun x => ?_)
    change Real.exp (2 * η * x) *
        |coMovingPath c u t x - U x| ^ 2 =
      (Real.exp (η * x) * (coMovingPath c u t x - U x)) ^ 2
    rw [mul_pow, sq_abs,
      show Real.exp (η * x) ^ 2 = Real.exp (2 * η * x) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring]
  have hpoint := paper5CorrectedWeightedDensity_identity_of_classical p
    (η := η)
    hsol ht0 htT hTW (fun x => (huM x).1)
    (hu2.of_le (by norm_num)) hv2
    (hU2.of_le (by norm_num)) hV2
  have hpde := paper5CorrectedWeightedTimeIntegral_eq p hpoint
    hdiff_int hdrift_int hrem_int
  have hgrad_int : Integrable (fun x =>
      paper5WeightedPopulationX η (coMovingPath c u) U t x *
        paper5WeightedPopulationX η (coMovingPath c u) U t x) := by
    simpa only [pow_two] using hWx2
  have hdiff := paper5WeightedPopulation_diffusion_ibp hu2 hU2
    hdiff_int hgrad_int hdiff_decay_bot hdiff_decay_top
  have hdrift := paper5WeightedPopulation_driftIntegral_eq_zero
    (hu2.of_le (by norm_num)) (hU2.of_le (by norm_num)) hdrift_int
    hdrift_decay_bot hdrift_decay_top
  obtain ⟨hB1, hB2, hB3, hB4, hK⟩ :=
    paper5ConcreteBounds_nonneg p hMpos
  have hraw0 := paper5CorrectedRemainderIntegral_le p hη.le hM0
    hB3 hB4 huM hUM hvM
    (fun x => (hcoeff x).1) (fun x => (hcoeff x).2.1)
    (fun x => (hcoeff x).2.2.1) (fun x => (hcoeff x).2.2.2)
    hrem_int hWx2 hW2 hsignal.2.1 hsignal.1
  have hresolved := paper5CorrectedRemainderIntegral_le_of_resolver p
    hη.le hB3 hB4 hraw0 hsignal.2.2.2 hsignal.2.2.1
  have hraw :
      (∫ x, paper5CorrectedRemainderDensity p η c
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation η (coMovingPath c u) U t)
        (paper5WeightedPopulationX η (coMovingPath c u) U t)
        (paper5WeightedSignal η (coMovingPath c v) V t)
        (paper5WeightedSignalX η (coMovingPath c v) V t) t x) ≤
      (1 / 2 : ℝ) * (∫ x,
        (paper5WeightedPopulationX η (coMovingPath c u) U t x) ^ 2) +
      paper5RawW2Coefficient p η c (MChi p)
        (paper5ConcreteB1 p) (paper5ConcreteB2 p)
        (paper5ConcreteB3 p) (paper5ConcreteB4 p) *
          (∫ x, (paper5WeightedPopulation η
            (coMovingPath c u) U t x) ^ 2) +
      (|p.χ| * paper5ConcreteB3 p / 2) *
        paper5WeightedResolverVxFactor p (MChi p) η *
          (∫ x, (paper5WeightedPopulation η
            (coMovingPath c u) U t x) ^ 2) +
      (|p.χ| * (η * paper5ConcreteB3 p + paper5ConcreteB4 p) / 2) *
        paper5WeightedResolverVFactor p (MChi p) η *
          (∫ x, (paper5WeightedPopulation η
            (coMovingPath c u) U t x) ^ 2) := by
    unfold paper5ResolvedW2Coefficient at hresolved
    convert hresolved using 1 <;> ring
  have hcaps := paper5WeightedResolverFactors_le_cap p hχ hM0 hη.le hηcap
  have hfinal := paper5CorrectedHalfEnergy_deriv_le_corrected531 p
    hη.le hB3 hB4 htime hpde hdiff hdrift hraw
    paper5WeightedPopulation_gradientIntegral_nonneg
    (integral_nonneg fun _ => sq_nonneg _)
    hcaps.1 hcaps.2
  simpa only [paper531ConcreteA, paper531ConcreteB,
    paper5ConcreteResolverK] using hfinal

section Theorem12EnergyProducerAxiomAudit

#print axioms remark5SpeedCondition_of_correctedCStarStar_lt
#print axioms barrierSpeed_lt_of_correctedCStarStar_lt
#print axioms paper5WeightedEnergy_eq_coMovingWeightedL2Energy
#print axioms paper5WeightedSignal_resolver_bounds
#print axioms paper5WeightedSignal_resolver_data
#print axioms paper5WeightedHalfEnergy_deriv_le_concrete_of_timeLeibniz

end Theorem12EnergyProducerAxiomAudit

end ShenWork.Paper1
