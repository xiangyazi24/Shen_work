import ShenWork.Paper1.WholeLineWeightedRegularityForcingHolderAssemblyNatural

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural coefficient data on a positive classical window

This file discharges the pointwise bounds and spatial measurability inputs of
the exact-weight forcing trajectory directly from the classical slices and
the corrected traveling-wave speed condition.
-/

/-- The five explicit coefficient budgets and their spatial measurability on
a closed positive-time window. -/
structure Paper5WeightedGeneratorForcingCoefficientWindowData
    (p : CMParams) (M eta c a b : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ) : Prop where
  hK₁ : 0 ≤ paper5CommonB1 p M
  hK₂ : 0 ≤ paper5CommonB2 p M +
    (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
      |eta| * paper5CommonB1 p M
  hK₃ : 0 ≤ paper5CommonB3 p M
  hK₄ : 0 ≤ paper5CommonB4 p M + |eta| * paper5CommonB3 p M
  hKR : 0 ≤ 1 + (1 + p.α) * M ^ p.α
  hB₁_bound : ∀ q ∈ Set.Icc a b, ∀ x,
    |paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| ≤
      paper5CommonB1 p M
  hB₂_bound : ∀ q ∈ Set.Icc a b, ∀ x,
    |paper5WeightedFluxPopulationCoefficient p eta
      (coMovingPath c u) (coMovingPath c v) U q x| ≤
        paper5CommonB2 p M +
          (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
            |eta| * paper5CommonB1 p M
  hB₃_bound : ∀ x, |paper5B3 p U x| ≤ paper5CommonB3 p M
  hB₄_bound : ∀ x,
    |paper5WeightedFluxSignalCoefficient p eta U x| ≤
      paper5CommonB4 p M + |eta| * paper5CommonB3 p M
  hR_bound : ∀ q ∈ Set.Icc a b, ∀ x,
    |1 - paper5A (1 + p.α) (coMovingPath c u) U q x| ≤
      1 + (1 + p.α) * M ^ p.α
  hB₁_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
    (paper5B1 p (coMovingPath c u) (coMovingPath c v) q) volume
  hB₂_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
    (paper5WeightedFluxPopulationCoefficient p eta
      (coMovingPath c u) (coMovingPath c v) U q) volume
  hB₃_meas : AEStronglyMeasurable (paper5B3 p U) volume
  hB₄_meas : AEStronglyMeasurable
    (paper5WeightedFluxSignalCoefficient p eta U) volume
  hR_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
    (fun x => 1 - paper5A (1 + p.α) (coMovingPath c u) U q x) volume

set_option maxHeartbeats 6000000 in
/-- Classical slices, resolver realization, and the corrected wave-speed
condition inhabit every coefficient field needed by the forcing estimate.
The constants are fixed explicitly rather than hidden behind existential
budgets. -/
theorem paper5WeightedGeneratorForcingCoefficientWindowData_of_classical_wave
    (p : CMParams) {M eta c a b : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hab : a ≤ b) (hM : 1 ≤ M)
    (_heta : 0 < eta) (_heta1 : eta < 1)
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChi : MChi p ≤ M)
    (hu2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c v q))
    (hU2 : ContDiff ℝ 2 U)
    (huM : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q ∈ Set.Icc a b,
      coMovingPath c v q = frozenElliptic p (coMovingPath c u q)) :
    Paper5WeightedGeneratorForcingCoefficientWindowData
      p M eta c a b u v U := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMChiPos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M := fun x =>
    ⟨(hTW.U_pos x).le, (hbound.le_MChi x).trans hMChi⟩
  have huC : ∀ q ∈ Set.Icc a b, IsCUnifBdd (coMovingPath c u q) := by
    intro q hq
    refine ⟨(hu2 q hq).continuous, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (huM q hq x).1]
    exact (huM q hq x).2
  have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
  have hvUpper : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c v q x ≤ M ^ p.γ := by
    intro q hq x
    rw [hvEq q hq]
    exact frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM0 _)
      (hu2 q hq).continuous (fun y => (huM q hq y).1)
      (fun y => Real.rpow_le_rpow (huM q hq y).1 (huM q hq y).2 hgamma0) x
  have hvM : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c v q x ∈ Set.Icc (0 : ℝ) (M ^ p.γ) := by
    intro q hq x
    constructor
    · rw [hvEq q hq]
      exact frozenElliptic_nonneg p (fun y => (huM q hq y).1) x
    · exact hvUpper q hq x
  have hvDeriv : ∀ q ∈ Set.Icc a b, ∀ x,
      |deriv (coMovingPath c v q) x| ≤ M ^ p.γ := by
    intro q hq x
    have hx := hvUpper q hq x
    rw [hvEq q hq] at hx ⊢
    exact (frozenElliptic_deriv_abs_le p (huC q hq)
      (fun y => (huM q hq y).1) x).trans hx
  have hspeed := remark5SpeedCondition_of_correctedCStarStar_lt p hc
  have hbarrier := barrierSpeed_lt_of_correctedCStarStar_lt p hc
  have hcoeff : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| ≤
          paper5CommonB1 p M ∧
        |paper5B2 p (coMovingPath c u) (coMovingPath c v) U q x| ≤
          paper5CommonB2 p M ∧
        |paper5B3 p U x| ≤ paper5CommonB3 p M ∧
        |paper5B4 p U x| ≤ paper5CommonB4 p M := by
    intro q hq x
    have hx := paper5CoefficientBounds_of_barrier_speed_common_bound p
      (sigma := paper5Sigma) (t := q) (x := x)
      (by norm_num [paper5Sigma]) hchi hspeed hbarrier hTW hreg hbound
      hMChi (huM q hq x) (hvDeriv q hq x)
    simpa only [paper5CommonB1, paper5CommonB2, paper5CommonB3,
      paper5CommonB4, paper5ConcreteLu] using hx
  obtain ⟨hK₁, hCommon2, hK₃, hCommon4, _hResolver⟩ :=
    paper5CommonBounds_nonneg p hM0 hMChiPos
  have hzeroBudget :
      0 ≤ (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) :=
    mul_nonneg (by linarith [p.hm, p.hγ]) (Real.rpow_nonneg hM0 _)
  have hK₂ : 0 ≤ paper5CommonB2 p M +
      (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
        |eta| * paper5CommonB1 p M := by positivity
  have hK₄ : 0 ≤ paper5CommonB4 p M + |eta| * paper5CommonB3 p M := by
    positivity
  have hKR : 0 ≤ 1 + (1 + p.α) * M ^ p.α :=
    add_nonneg zero_le_one
      (mul_nonneg (by linarith [p.hα]) (Real.rpow_nonneg hM0 _))
  have hB₁_bound := fun q hq x => (hcoeff q hq x).1
  have hB₂_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta
        (coMovingPath c u) (coMovingPath c v) U q x| ≤
          paper5CommonB2 p M +
            (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
              |eta| * paper5CommonB1 p M := by
    intro q hq x
    have hz := paper5CorrectedChemZeroCoefficient_abs_le p hM0
      (huM q hq x) (hUM x) (hvM q hq x)
    unfold paper5WeightedFluxPopulationCoefficient
    calc
      |paper5B2 p (coMovingPath c u) (coMovingPath c v) U q x +
            paper5CorrectedChemZeroCoefficient p
              (coMovingPath c u) (coMovingPath c v) U q x -
          eta * paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| ≤
          |paper5B2 p (coMovingPath c u) (coMovingPath c v) U q x| +
              |paper5CorrectedChemZeroCoefficient p
                (coMovingPath c u) (coMovingPath c v) U q x| +
            |eta * paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add (add_le_add (hcoeff q hq x).2.1 hz)
          (mul_le_mul_of_nonneg_left (hcoeff q hq x).1 (abs_nonneg eta))
  have hB₃_bound := fun x => (hcoeff a ⟨le_rfl, hab⟩ x).2.2.1
  have hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤
        paper5CommonB4 p M + |eta| * paper5CommonB3 p M := by
    intro x
    unfold paper5WeightedFluxSignalCoefficient
    calc
      |paper5B4 p U x - eta * paper5B3 p U x| ≤
          |paper5B4 p U x| + |eta * paper5B3 p U x| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add (hcoeff a ⟨le_rfl, hab⟩ x).2.2.2
          (mul_le_mul_of_nonneg_left
            (hcoeff a ⟨le_rfl, hab⟩ x).2.2.1 (abs_nonneg eta))
  have hR_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |1 - paper5A (1 + p.α) (coMovingPath c u) U q x| ≤
        1 + (1 + p.α) * M ^ p.α := by
    intro q hq x
    have hA := paper5MeanCoefficient_abs_le
      (show 1 ≤ 1 + p.α by linarith [p.hα]) hM0
      (huM q hq x) (hUM x)
    have hA' : |paper5A (1 + p.α) (coMovingPath c u) U q x| ≤
        (1 + p.α) * M ^ p.α := by
      simpa only [paper5A, add_sub_cancel_left] using hA
    calc
      |1 - paper5A (1 + p.α) (coMovingPath c u) U q x| ≤
          |(1 : ℝ)| + |paper5A (1 + p.α) (coMovingPath c u) U q x| :=
        abs_sub _ _
      _ ≤ _ := by rw [abs_one]; linarith
  have hB₁_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5B1 p (coMovingPath c u) (coMovingPath c v) q) volume := by
    intro q hq
    unfold paper5B1
    exact ((measurable_const.mul
      ((hv2 q hq).continuous_deriv (by norm_num)).measurable).mul
        ((Real.continuous_rpow_const (sub_nonneg.mpr p.hm)).comp
          (hu2 q hq).continuous).measurable).aestronglyMeasurable
  have hB₂_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta
        (coMovingPath c u) (coMovingPath c v) U q) volume := by
    intro q hq
    have hAm1 := paper5A_measurable_of_continuous_nonneg (p.m - 1)
      (hu2 q hq).continuous hU2.continuous
      (fun x => (huM q hq x).1) (fun x => (hUM x).1)
    have hAm := paper5A_measurable_of_continuous_nonneg p.m
      (hu2 q hq).continuous hU2.continuous
      (fun x => (huM q hq x).1) (fun x => (hUM x).1)
    have hAmg := paper5A_measurable_of_continuous_nonneg (p.m + p.γ)
      (hu2 q hq).continuous hU2.continuous
      (fun x => (huM q hq x).1) (fun x => (hUM x).1)
    have hB1m : Measurable
        (paper5B1 p (coMovingPath c u) (coMovingPath c v) q) := by
      unfold paper5B1
      exact (measurable_const.mul
        ((hv2 q hq).continuous_deriv (by norm_num)).measurable).mul
          ((Real.continuous_rpow_const (sub_nonneg.mpr p.hm)).comp
            (hu2 q hq).continuous).measurable
    have hB2m : Measurable
        (paper5B2 p (coMovingPath c u) (coMovingPath c v) U q) := by
      unfold paper5B2
      exact (((measurable_const.mul
        (hU2.continuous_deriv (by norm_num)).measurable).mul
          ((hv2 q hq).continuous_deriv (by norm_num)).measurable).mul hAm1)
    unfold paper5WeightedFluxPopulationCoefficient
    unfold paper5CorrectedChemZeroCoefficient
    exact ((hB2m.add
      (((hv2 q hq).continuous.measurable.mul hAm).sub hAmg)).sub
        (measurable_const.mul hB1m)).aestronglyMeasurable
  have hB₃_meas : AEStronglyMeasurable (paper5B3 p U) volume := by
    unfold paper5B3
    exact ((measurable_const.mul
      ((Real.continuous_rpow_const (sub_nonneg.mpr p.hm)).comp
        hU2.continuous).measurable).mul
          (hU2.continuous_deriv (by norm_num)).measurable).aestronglyMeasurable
  have hB₄_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume := by
    have hB3m : Measurable (paper5B3 p U) := by
      unfold paper5B3
      exact (measurable_const.mul
        (((Real.continuous_rpow_const (sub_nonneg.mpr p.hm)).comp
          hU2.continuous).measurable)).mul
            (hU2.continuous_deriv (by norm_num)).measurable
    have hB4m : Measurable (paper5B4 p U) := by
      unfold paper5B4
      exact ((Real.continuous_rpow_const (zero_le_one.trans p.hm)).comp
        hU2.continuous).measurable
    unfold paper5WeightedFluxSignalCoefficient
    exact (hB4m.sub (measurable_const.mul hB3m)).aestronglyMeasurable
  have hR_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) (coMovingPath c u) U q x) volume := by
    intro q hq
    exact (measurable_const.sub
      (paper5A_measurable_of_continuous_nonneg (1 + p.α)
        (hu2 q hq).continuous hU2.continuous
        (fun x => (huM q hq x).1) (fun x => (hUM x).1))).aestronglyMeasurable
  exact ⟨hK₁, hK₂, hK₃, hK₄, hKR, hB₁_bound, hB₂_bound,
    hB₃_bound, hB₄_bound, hR_bound, hB₁_meas, hB₂_meas,
    hB₃_meas, hB₄_meas, hR_meas⟩

set_option maxHeartbeats 6000000 in
/-- The canonical classical positive window and the corrected traveling wave
produce the exact-weight generator-forcing trajectory with its uniform time
modulus.  All five coefficient budgets are the explicit Section 5 common
budgets; no coefficient bound or measurability premise is carried by the
statement. -/
theorem
    exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_data_of_population_H1_trajectories_and_classical_wave
    (p : CMParams) {M T eta c a b Hu Blog : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {EW EWx HW HWx : ℝ}
    {W X : ℝ → WholeLineRealL2}
    (hab : a ≤ b) (hdiam : b - a ≤ 1)
    (ha : 0 < a) (hbT : b < T)
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (hsol : IsClassicalSolution p T u v)
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChi : MChi p ≤ M)
    (hu2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c v q))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c u q x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ q ∈ Set.Icc a b,
      coMovingPath c v q = frozenElliptic p (coMovingPath c u q))
    (hHu : 0 ≤ Hu)
    (huHolder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |coMovingPath c u s x - coMovingPath c u t x| ≤
        Hu * |s - t| ^ (1 / 2 : ℝ))
    (hBlog : 0 ≤ Blog)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hF_sq_phys : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) volume)
    (hEW : 0 ≤ EW) (hEWx : 0 ≤ EWx)
    (hHW : 0 ≤ HW) (hHWx : 0 ≤ HWx)
    (hWrep : ∀ q ∈ Set.Icc a b,
      (((W q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulation eta (coMovingPath c u) U q))
    (hXrep : ∀ q ∈ Set.Icc a b,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hWnorm : ∀ q ∈ Set.Icc a b, ‖W q‖ ≤ EW)
    (hXnorm : ∀ q ∈ Set.Icc a b, ‖X q‖ ≤ EWx)
    (hWmod : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖W s - W t‖ ≤ HW * |s - t| ^ paper5ForcingTimeExponent p)
    (hXmod : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖X s - X t‖ ≤ HWx * |s - t| ^ paper5ForcingTimeExponent p) :
    ∃ H : ℝ, 0 ≤ H ∧
      (∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab s -
            paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab t‖ ≤
          H * |s - t| ^ paper5ForcingTimeExponent p) ∧
      Continuous
        (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
          p eta c u v U V hab) ∧
      ∀ q ∈ Set.Icc a b,
        (((paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V q) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMChiPos : 0 < MChi p :=
    lt_of_lt_of_le (hbound.pos 0) (hbound.le_MChi 0)
  have hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M := fun x =>
    ⟨(hTW.U_pos x).le, (hbound.le_MChi x).trans hMChi⟩
  have hUpos : ∀ x, 0 < U x := hTW.U_pos
  have hVEq : V = frozenElliptic p U :=
    IsTravelingWave.V_eq_frozenElliptic_full hTW hbound hreg
  have huC : ∀ q ∈ Set.Icc a b, IsCUnifBdd (coMovingPath c u q) := by
    intro q hq
    refine ⟨(hu2 q hq).continuous, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (huM q hq x).1]
    exact (huM q hq x).2
  have hUC : IsCUnifBdd U :=
    U_isCUnifBdd_of_continuous hbound hreg.U_cont
  have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
  have hvUpper : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c v q x ≤ M ^ p.γ := by
    intro q hq x
    rw [hvEq q hq]
    exact frozenElliptic_le_of_rpow_le p (Real.rpow_nonneg hM0 _)
      (hu2 q hq).continuous (fun y => (huM q hq y).1)
      (fun y => Real.rpow_le_rpow (huM q hq y).1 (huM q hq y).2 hgamma0) x
  have hvM : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c v q x ∈ Set.Icc (0 : ℝ) (M ^ p.γ) := by
    intro q hq x
    constructor
    · rw [hvEq q hq]
      exact frozenElliptic_nonneg p (fun y => (huM q hq y).1) x
    · exact hvUpper q hq x
  have hvDeriv : ∀ q ∈ Set.Icc a b, ∀ x,
      |deriv (coMovingPath c v q) x| ≤ M ^ p.γ := by
    intro q hq x
    have hx := hvUpper q hq x
    rw [hvEq q hq] at hx ⊢
    exact (frozenElliptic_deriv_abs_le p (huC q hq)
      (fun y => (huM q hq y).1) x).trans hx
  have hspeed := remark5SpeedCondition_of_correctedCStarStar_lt p hc
  have hbarrier := barrierSpeed_lt_of_correctedCStarStar_lt p hc
  have hcoeff : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| ≤
          paper5CommonB1 p M ∧
        |paper5B2 p (coMovingPath c u) (coMovingPath c v) U q x| ≤
          paper5CommonB2 p M ∧
        |paper5B3 p U x| ≤ paper5CommonB3 p M ∧
        |paper5B4 p U x| ≤ paper5CommonB4 p M := by
    intro q hq x
    have hx := paper5CoefficientBounds_of_barrier_speed_common_bound p
      (sigma := paper5Sigma) (t := q) (x := x)
      (by norm_num [paper5Sigma]) hchi hspeed hbarrier hTW hreg hbound
      hMChi (huM q hq x) (hvDeriv q hq x)
    simpa only [paper5CommonB1, paper5CommonB2, paper5CommonB3,
      paper5CommonB4, paper5ConcreteLu] using hx
  let K₁ : ℝ := paper5CommonB1 p M
  let K₂ : ℝ := paper5CommonB2 p M +
    (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
      |eta| * paper5CommonB1 p M
  let K₃ : ℝ := paper5CommonB3 p M
  let K₄ : ℝ := paper5CommonB4 p M + |eta| * paper5CommonB3 p M
  let KR : ℝ := 1 + (1 + p.α) * M ^ p.α
  obtain ⟨hCommon1, hCommon2, hCommon3, hCommon4, _hResolver⟩ :=
    paper5CommonBounds_nonneg p hM0 hMChiPos
  have hzeroBudget :
      0 ≤ (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) := by
    exact mul_nonneg (by linarith [p.hm, p.hγ]) (Real.rpow_nonneg hM0 _)
  have hK₁ : 0 ≤ K₁ := hCommon1
  have hK₂ : 0 ≤ K₂ := by
    dsimp only [K₂]
    positivity
  have hK₃ : 0 ≤ K₃ := hCommon3
  have hK₄ : 0 ≤ K₄ := by
    dsimp only [K₄]
    positivity
  have hKR : 0 ≤ KR := by
    dsimp only [KR]
    exact add_nonneg zero_le_one
      (mul_nonneg (by linarith [p.hα]) (Real.rpow_nonneg hM0 _))
  have hB₁_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| ≤ K₁ :=
    fun q hq x => (hcoeff q hq x).1
  have hB₂_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta
        (coMovingPath c u) (coMovingPath c v) U q x| ≤ K₂ := by
    intro q hq x
    have hz := paper5CorrectedChemZeroCoefficient_abs_le p hM0
      (huM q hq x) (hUM x) (hvM q hq x)
    dsimp only [paper5WeightedFluxPopulationCoefficient, K₂]
    calc
      |paper5B2 p (coMovingPath c u) (coMovingPath c v) U q x +
            paper5CorrectedChemZeroCoefficient p
              (coMovingPath c u) (coMovingPath c v) U q x -
          eta * paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| ≤
          |paper5B2 p (coMovingPath c u) (coMovingPath c v) U q x| +
              |paper5CorrectedChemZeroCoefficient p
                (coMovingPath c u) (coMovingPath c v) U q x| +
            |eta * paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| := by
          exact (abs_sub _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ paper5CommonB2 p M +
              (2 * p.m + p.γ) * M ^ (p.m + p.γ - 1) +
            |eta| * paper5CommonB1 p M := by
          rw [abs_mul]
          exact add_le_add
            (add_le_add (hcoeff q hq x).2.1 hz)
            (mul_le_mul_of_nonneg_left (hcoeff q hq x).1 (abs_nonneg eta))
  have hB₃_bound : ∀ x, |paper5B3 p U x| ≤ K₃ :=
    fun x => (hcoeff a ⟨le_rfl, hab⟩ x).2.2.1
  have hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K₄ := by
    intro x
    dsimp only [paper5WeightedFluxSignalCoefficient, K₄]
    calc
      |paper5B4 p U x - eta * paper5B3 p U x| ≤
          |paper5B4 p U x| + |eta * paper5B3 p U x| := abs_sub _ _
      _ ≤ paper5CommonB4 p M + |eta| * paper5CommonB3 p M := by
        rw [abs_mul]
        exact add_le_add (hcoeff a ⟨le_rfl, hab⟩ x).2.2.2
          (mul_le_mul_of_nonneg_left
            (hcoeff a ⟨le_rfl, hab⟩ x).2.2.1 (abs_nonneg eta))
  have hR_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |1 - paper5A (1 + p.α) (coMovingPath c u) U q x| ≤ KR := by
    intro q hq x
    have hA := paper5MeanCoefficient_abs_le
      (show 1 ≤ 1 + p.α by linarith [p.hα]) hM0
      (huM q hq x) (hUM x)
    have hA' :
        |paper5A (1 + p.α) (coMovingPath c u) U q x| ≤
          (1 + p.α) * M ^ p.α := by
      simpa only [paper5A, add_sub_cancel_left] using hA
    dsimp only [KR]
    calc
      |1 - paper5A (1 + p.α) (coMovingPath c u) U q x| ≤
          |(1 : ℝ)| + |paper5A (1 + p.α) (coMovingPath c u) U q x| :=
        abs_sub _ _
      _ ≤ 1 + (1 + p.α) * M ^ p.α := by
        rw [abs_one]
        linarith
  have hB₁_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5B1 p (coMovingPath c u) (coMovingPath c v) q) volume := by
    intro q hq
    unfold paper5B1
    exact ((measurable_const.mul
      ((hv2 q hq).continuous_deriv (by norm_num)).measurable).mul
        ((Real.continuous_rpow_const (sub_nonneg.mpr p.hm)).comp
          (hu2 q hq).continuous).measurable).aestronglyMeasurable
  have hB₂_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta
        (coMovingPath c u) (coMovingPath c v) U q) volume := by
    intro q hq
    have hAm1 := paper5A_measurable_of_continuous_nonneg (p.m - 1)
      (hu2 q hq).continuous hU2.continuous
      (fun x => (huM q hq x).1) (fun x => (hUM x).1)
    have hAm := paper5A_measurable_of_continuous_nonneg p.m
      (hu2 q hq).continuous hU2.continuous
      (fun x => (huM q hq x).1) (fun x => (hUM x).1)
    have hAmg := paper5A_measurable_of_continuous_nonneg (p.m + p.γ)
      (hu2 q hq).continuous hU2.continuous
      (fun x => (huM q hq x).1) (fun x => (hUM x).1)
    have hB1m : Measurable
        (paper5B1 p (coMovingPath c u) (coMovingPath c v) q) := by
      unfold paper5B1
      exact (measurable_const.mul
        ((hv2 q hq).continuous_deriv (by norm_num)).measurable).mul
          ((Real.continuous_rpow_const (sub_nonneg.mpr p.hm)).comp
            (hu2 q hq).continuous).measurable
    have hB2m : Measurable
        (paper5B2 p (coMovingPath c u) (coMovingPath c v) U q) := by
      unfold paper5B2
      exact (((measurable_const.mul
        (hU2.continuous_deriv (by norm_num)).measurable).mul
          ((hv2 q hq).continuous_deriv (by norm_num)).measurable).mul hAm1)
    unfold paper5WeightedFluxPopulationCoefficient
    unfold paper5CorrectedChemZeroCoefficient
    exact ((hB2m.add
      (((hv2 q hq).continuous.measurable.mul hAm).sub hAmg)).sub
        (measurable_const.mul hB1m)).aestronglyMeasurable
  have hB₃_meas : AEStronglyMeasurable (paper5B3 p U) volume := by
    unfold paper5B3
    exact ((measurable_const.mul
      ((Real.continuous_rpow_const (sub_nonneg.mpr p.hm)).comp
        hU2.continuous).measurable).mul
          (hU2.continuous_deriv (by norm_num)).measurable).aestronglyMeasurable
  have hB₄_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume := by
    have hB3m : Measurable (paper5B3 p U) := by
      unfold paper5B3
      exact (measurable_const.mul
        (((Real.continuous_rpow_const (sub_nonneg.mpr p.hm)).comp
          hU2.continuous).measurable)).mul
            (hU2.continuous_deriv (by norm_num)).measurable
    have hB4m : Measurable (paper5B4 p U) := by
      unfold paper5B4
      exact ((Real.continuous_rpow_const (zero_le_one.trans p.hm)).comp
        hU2.continuous).measurable
    unfold paper5WeightedFluxSignalCoefficient
    exact (hB4m.sub (measurable_const.mul hB3m)).aestronglyMeasurable
  have hR_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) (coMovingPath c u) U q x) volume := by
    intro q hq
    exact (measurable_const.sub
      (paper5A_measurable_of_continuous_nonneg (1 + p.α)
        (hu2 q hq).continuous hU2.continuous
        (fun x => (huM q hq x).1) (fun x => (hUM x).1))).aestronglyMeasurable
  exact
    exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_data_of_population_H1_trajectories_and_coefficient_data
      p hab hdiam ha hbT hM heta heta1 hsol hTW hu2 hv2 hU2 hV2
      huC hUC huM hUM hUpos hvEq hVEq hHu huHolder hBlog hlog
      hK₁ hK₂ hK₃ hK₄ hKR
      hB₁_bound hB₂_bound hB₃_bound hB₄_bound hR_bound
      hB₁_meas hB₂_meas hB₃_meas hB₄_meas hR_meas
      hF_sq_phys hEW hEWx hHW hHWx hWrep hXrep hWnorm hXnorm hWmod hXmod

#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcingCoefficientWindowData_of_classical_wave
#print axioms
  ShenWork.Paper1.exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_data_of_population_H1_trajectories_and_classical_wave

end ShenWork.Paper1
