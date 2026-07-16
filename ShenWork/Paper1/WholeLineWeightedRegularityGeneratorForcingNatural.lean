import ShenWork.Paper1.WholeLineWeightedRegularityForcingTrajectory

open Filter MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural static data for the weighted generator forcing

The classical spatial slices identify the genuine flux derivative with a
continuous physical representative.  Consequently the measurability premise
of `paper5WeightedGeneratorForcing_data_of_population_H1` is not an additional
analytic input.
-/

/-- The genuine exponentially weighted flux derivative is strongly
measurable whenever the population and signal slices are classically `C²`.
The proof uses the physical product-rule representatives supplied by the PDE
and the traveling-wave equation. -/
theorem paper5WeightedFluxDerivative_aestronglyMeasurable_of_classical_slices
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V) :
    AEStronglyMeasurable (fun x : ℝ =>
      Real.exp (eta * x) *
        (deriv
            (fun y => (coMovingPath c u t y) ^ p.m *
              deriv (coMovingPath c v t) y) x -
          deriv (fun y => (U y) ^ p.m * deriv V y) x)) volume := by
  let actual : ℝ → ℝ := fun x =>
    Real.exp (eta * x) *
      (deriv
          (fun y => (coMovingPath c u t y) ^ p.m *
            deriv (coMovingPath c v t) y) x -
        deriv (fun y => (U y) ^ p.m * deriv V y) x)
  let physical : ℝ → ℝ := fun x => Real.exp (eta * x) *
    ((p.m * (coMovingPath c u t x) ^ (p.m - 1) *
          deriv (coMovingPath c u t) x * deriv (coMovingPath c v t) x +
        (coMovingPath c u t x) ^ p.m *
          (coMovingPath c v t x - (coMovingPath c u t x) ^ p.γ)) -
      (p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
        (U x) ^ p.m * (V x - (U x) ^ p.γ)))
  have hphysical_cont : Continuous physical := by
    have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hu : Continuous (coMovingPath c u t) := hu2.continuous
    have hv : Continuous (coMovingPath c v t) := hv2.continuous
    have hU : Continuous U := hU2.continuous
    have hV : Continuous V := hV2.continuous
    have hux : Continuous (deriv (coMovingPath c u t)) :=
      hu2.continuous_deriv (by norm_num)
    have hvx : Continuous (deriv (coMovingPath c v t)) :=
      hv2.continuous_deriv (by norm_num)
    have hUx : Continuous (deriv U) := hU2.continuous_deriv (by norm_num)
    have hVx : Continuous (deriv V) := hV2.continuous_deriv (by norm_num)
    have hm0 : 0 ≤ p.m := zero_le_one.trans p.hm
    have hm10 : 0 ≤ p.m - 1 := sub_nonneg.mpr p.hm
    have hgamma0 : 0 ≤ p.γ := zero_le_one.trans p.hγ
    have hupowm : Continuous (fun x => (coMovingPath c u t x) ^ p.m) :=
      (Real.continuous_rpow_const hm0).comp hu
    have hupowm1 : Continuous
        (fun x => (coMovingPath c u t x) ^ (p.m - 1)) :=
      (Real.continuous_rpow_const hm10).comp hu
    have hupowgamma : Continuous
        (fun x => (coMovingPath c u t x) ^ p.γ) :=
      (Real.continuous_rpow_const hgamma0).comp hu
    have hUpowm : Continuous (fun x => (U x) ^ p.m) :=
      (Real.continuous_rpow_const hm0).comp hU
    have hUpowm1 : Continuous (fun x => (U x) ^ (p.m - 1)) :=
      (Real.continuous_rpow_const hm10).comp hU
    have hUpowgamma : Continuous (fun x => (U x) ^ p.γ) :=
      (Real.continuous_rpow_const hgamma0).comp hU
    have hdynamic : Continuous (fun x =>
        p.m * (coMovingPath c u t x) ^ (p.m - 1) *
            deriv (coMovingPath c u t) x * deriv (coMovingPath c v t) x +
          (coMovingPath c u t x) ^ p.m *
            (coMovingPath c v t x - (coMovingPath c u t x) ^ p.γ)) :=
      (((continuous_const.mul hupowm1).mul hux).mul hvx).add
        (hupowm.mul (hv.sub hupowgamma))
    have hwave : Continuous (fun x =>
        p.m * (U x) ^ (p.m - 1) * deriv U x * deriv V x +
          (U x) ^ p.m * (V x - (U x) ^ p.γ)) :=
      (((continuous_const.mul hUpowm1).mul hUx).mul hVx).add
        (hUpowm.mul (hV.sub hUpowgamma))
    dsimp only [physical]
    exact hexp.mul (hdynamic.sub hwave)
  have hactual_physical : ∀ x, actual x = physical x := by
    intro x
    dsimp only [actual, physical]
    rw [paper5CoMovingFluxDerivative_realization_of_classical
        p hsol ht0 htT (hu2.of_le (by norm_num)) hv2,
      paper5WaveFluxDerivative_realization p hTW
        (hU2.of_le (by norm_num)) hV2]
  exact hphysical_cont.aestronglyMeasurable.congr
    (Eventually.of_forall fun x => (hactual_physical x).symm)

/-- Classical slice regularity automatically supplies the measurability of
the full weighted generator forcing. -/
theorem paper5WeightedGeneratorForcing_aestronglyMeasurable_of_classical_slices
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V) :
    AEStronglyMeasurable
      (paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t) volume := by
  have hflux :=
    paper5WeightedFluxDerivative_aestronglyMeasurable_of_classical_slices
      p (eta := eta) hsol ht0 htT hTW hu2 hv2 hU2 hV2
  have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hru : Continuous (fun x => reactionFun p.α
      (coMovingPath c u t x)) :=
    (continuous_reactionFun (zero_le_one.trans p.hα)).comp hu2.continuous
  have hrU : Continuous (fun x => reactionFun p.α (U x)) :=
    (continuous_reactionFun (zero_le_one.trans p.hα)).comp hU2.continuous
  have hreact : AEStronglyMeasurable (fun x : ℝ =>
      Real.exp (eta * x) *
        (reactionFun p.α (coMovingPath c u t x) -
          reactionFun p.α (U x))) volume :=
    (hexp.mul (hru.sub hrU)).aestronglyMeasurable
  refine ((hflux.const_mul (-p.χ)).add hreact).congr
    (Eventually.of_forall fun x => ?_)
  change
    -p.χ * (Real.exp (eta * x) *
        (deriv
            (fun y => (coMovingPath c u t y) ^ p.m *
              deriv (coMovingPath c v t) y) x -
          deriv (fun y => (U y) ^ p.m * deriv V y) x)) +
        Real.exp (eta * x) *
          (reactionFun p.α (coMovingPath c u t x) -
            reactionFun p.α (U x)) =
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t x
  unfold paper5WeightedGeneratorForcing
  ring

/-- The explicit generator-forcing square budget is monotone in the
population `H⁰` and `H¹` numerical budgets. -/
theorem paper5WeightedGeneratorForcingH1SquareBound_mono
    (p : CMParams) {M eta EW₁ EW₂ EWx₁ EWx₂ : ℝ}
    (hM : 0 ≤ M) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hEW : EW₁ ≤ EW₂) (hEWx : EWx₁ ≤ EWx₂) :
    paper5WeightedGeneratorForcingH1SquareBound p M eta EW₁ EWx₁ ≤
      paper5WeightedGeneratorForcingH1SquareBound p M eta EW₂ EWx₂ := by
  have hetaSq : eta ^ 2 < 1 := by
    have hprod : 0 < (1 - eta) * (1 + eta) :=
      mul_pos (sub_pos.mpr heta1) (by linarith)
    nlinarith
  have hRV : 0 ≤ paper5WeightedResolverVFactor p M eta := by
    unfold paper5WeightedResolverVFactor
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg hM _))
      (sq_nonneg (1 - eta))
  have hRVx : 0 ≤ paper5WeightedResolverVxFactor p M eta := by
    unfold paper5WeightedResolverVxFactor
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ) (Real.rpow_nonneg hM _))
      (sub_nonneg.mpr hetaSq.le)
  unfold paper5WeightedGeneratorForcingH1SquareBound
    paper5WeightedFluxDerivativeH1SquareBound
  gcongr

/-- Static exact-weight `L²` data for the full generator forcing, with its
measurability derived from the classical slices rather than carried as a
hypothesis. -/
theorem paper5WeightedGeneratorForcing_data_of_population_H1_natural
    (p : CMParams) {M T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)) :
    Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) ∧
      (∫ x : ℝ,
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) ≤
        paper5WeightedGeneratorForcingH1SquareBound p M eta
          (∫ x : ℝ,
            Real.exp (2 * eta * x) *
              |coMovingPath c u t x - U x| ^ 2)
          (∫ x : ℝ,
            paper5WeightedPopulationX eta
              (coMovingPath c u) U t x ^ 2) := by
  have hforcing_meas :=
    paper5WeightedGeneratorForcing_aestronglyMeasurable_of_classical_slices
      p (eta := eta) hsol ht0 htT hTW hu2 hv2 hU2 hV2
  exact paper5WeightedGeneratorForcing_data_of_population_H1
    p hchi hc heta hetaCap hsol ht0 htT hTW hreg hbound hMChiM
      hu2 hv2 hU2 hV2 huM hvEq hclose hWx2 hforcing_meas

/-- Numerical-budget form of the natural static producer. -/
theorem paper5WeightedGeneratorForcing_data_of_population_H1_natural_of_bounds
    (p : CMParams) {M T eta c t EW EWx : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hclose_le : (∫ x : ℝ,
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2) ≤ EW)
    (hWx_le : (∫ x : ℝ,
      paper5WeightedPopulationX eta
        (coMovingPath c u) U t x ^ 2) ≤ EWx) :
    Integrable (fun x : ℝ =>
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) ∧
      (∫ x : ℝ,
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) ≤
        paper5WeightedGeneratorForcingH1SquareBound p M eta EW EWx := by
  have hdata := paper5WeightedGeneratorForcing_data_of_population_H1_natural
    p hchi hc heta hetaCap hsol ht0 htT hTW hreg hbound hMChiM
      hu2 hv2 hU2 hV2 huM hvEq hclose hWx2
  have hMChi1 : 1 ≤ MChi p := MChi_ge_one_of_travelingWave hTW hbound
  have hM0 : 0 ≤ M := zero_le_one.trans (hMChi1.trans hMChiM)
  have heta1 : eta < 1 := by
    have hcap1 : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    exact hetaCap.trans_le hcap1
  refine ⟨hdata.1, hdata.2.trans ?_⟩
  exact paper5WeightedGeneratorForcingH1SquareBound_mono
    p hM0 heta.le heta1 hclose_le hWx_le

/-- Uniform exact-weight forcing square bound on a compact positive-time
window, obtained solely from uniform numerical `H⁰` and `H¹` budgets. -/
theorem paper5WeightedGeneratorForcing_uniform_square_bound_on_Icc_of_population_H1_natural
    (p : CMParams) {M T eta c a b EW EWx : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hsol : IsClassicalSolution p T u v)
    (ha : 0 < a) (hbT : b < T)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hu2 : ∀ s ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c u s))
    (hv2 : ∀ s ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c v s))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ s ∈ Set.Icc a b, ∀ x,
      coMovingPath c u s x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : ∀ s ∈ Set.Icc a b,
      coMovingPath c v s = frozenElliptic p (coMovingPath c u s))
    (hclose : ∀ s ∈ Set.Icc a b, Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u s x - U x| ^ 2))
    (hWx2 : ∀ s ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U s x ^ 2))
    (hclose_le : ∀ s ∈ Set.Icc a b, (∫ x : ℝ,
      Real.exp (2 * eta * x) * |coMovingPath c u s x - U x| ^ 2) ≤ EW)
    (hWx_le : ∀ s ∈ Set.Icc a b, (∫ x : ℝ,
      paper5WeightedPopulationX eta
        (coMovingPath c u) U s x ^ 2) ≤ EWx) :
    ∀ s ∈ Set.Icc a b,
      Integrable (fun x : ℝ =>
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V s x ^ 2) ∧
        (∫ x : ℝ,
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V s x ^ 2) ≤
          paper5WeightedGeneratorForcingH1SquareBound p M eta EW EWx := by
  intro s hs
  exact paper5WeightedGeneratorForcing_data_of_population_H1_natural_of_bounds
    p hchi hc heta hetaCap hsol (ha.trans_le hs.1) (hs.2.trans_lt hbT)
      hTW hreg hbound hMChiM (hu2 s hs) (hv2 s hs) hU2 hV2
      (huM s hs) (hvEq s hs) (hclose s hs) (hWx2 s hs)
      (hclose_le s hs) (hWx_le s hs)

#print axioms
  ShenWork.Paper1.paper5WeightedFluxDerivative_aestronglyMeasurable_of_classical_slices
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_aestronglyMeasurable_of_classical_slices
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_data_of_population_H1_natural
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcingH1SquareBound_mono
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_data_of_population_H1_natural_of_bounds
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcing_uniform_square_bound_on_Icc_of_population_H1_natural

end ShenWork.Paper1
