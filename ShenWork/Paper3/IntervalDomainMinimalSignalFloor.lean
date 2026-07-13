import ShenWork.Paper3.IntervalDomainMinimalEventualUpper
import ShenWork.Paper3.IntervalDomainResolverMassGap
import ShenWork.Paper3.IntervalDomainPowerSourceMassGap
import ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.Paper2.IntervalConjugateKernelIBP
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # Orbit-independent signal floor for the minimal model -/

open Filter MeasureTheory Set Topology
open scoped Topology Interval

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalDomainResolverStrictPos
open ShenWork.IntervalResolverPositivity
open ShenWork.IntervalResolverGradientBridge
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.Paper2.IntervalTruncatedWeakBarrierComparisonV6
open ShenWork.IntervalPicardLimitCoeffConv
open ShenWork.IntervalDomainLogisticWeakH2Adapter

noncomputable section

private theorem intervalMeasure_one_isProbability_signalFloor :
    IsProbabilityMeasure (intervalMeasure 1) := by
  constructor
  unfold intervalMeasure intervalSet
  simp [Real.volume_Icc]

/-- The lower moment appearing in the paper's minimal persistence constant. -/
def intervalMinimalPowerMassLower
    (p : CM2Params) (uStar M : ℝ) : ℝ :=
  if p.γ ≤ 1 then uStar * M ^ (p.γ - 1) else uStar ^ p.γ

/-- A nonnegative profile of mass `uStar` and height at most `M` has the
uniform power-mass lower bound used in Lemma 3.5. -/
theorem intervalMinimalPowerMassLower_le_integral
    (p : CM2Params) {U : ℝ → ℝ} {uStar M : ℝ}
    (hU_cont : Continuous U) (hU_nonneg : ∀ y, 0 ≤ U y)
    (hU_le : ∀ y, U y ≤ M)
    (hmass : (∫ y, U y ∂(intervalMeasure 1)) = uStar) :
    intervalMinimalPowerMassLower p uStar M ≤
      ∫ y, U y ^ p.γ ∂(intervalMeasure 1) := by
  letI : IsProbabilityMeasure (intervalMeasure 1) :=
    intervalMeasure_one_isProbability_signalFloor
  have hUint : Integrable U (intervalMeasure 1) :=
    intervalMeasure_integrable_of_continuous_nonneg_le
      hU_cont hU_nonneg hU_le
  have hUpowInt : Integrable (fun y => U y ^ p.γ) (intervalMeasure 1) :=
    intervalMeasure_rpow_integrable_of_continuous_nonneg_le
      p.γ p.hγ.le hU_cont hU_nonneg hU_le
  by_cases hγ1 : p.γ ≤ 1
  · have hexp : p.γ - 1 ≤ 0 := sub_nonpos.mpr hγ1
    have hpoint : ∀ y, M ^ (p.γ - 1) * U y ≤ U y ^ p.γ := by
      intro y
      by_cases hUy : U y = 0
      · simp only [hUy, mul_zero]
        exact Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by norm_num) _
      · have hUpos : 0 < U y := lt_of_le_of_ne (hU_nonneg y) (Ne.symm hUy)
        have hpow : M ^ (p.γ - 1) ≤ U y ^ (p.γ - 1) :=
          Real.rpow_le_rpow_of_nonpos hUpos (hU_le y) hexp
        have hadd := Real.rpow_add hUpos (p.γ - 1) 1
        rw [Real.rpow_one] at hadd
        calc
          M ^ (p.γ - 1) * U y ≤ U y ^ (p.γ - 1) * U y :=
            mul_le_mul_of_nonneg_right hpow hUpos.le
          _ = U y ^ ((p.γ - 1) + 1) := hadd.symm
          _ = U y ^ p.γ := by ring_nf
    have hlinearInt : Integrable
        (fun y => M ^ (p.γ - 1) * U y) (intervalMeasure 1) :=
      hUint.const_mul _
    have hmono := integral_mono hlinearInt hUpowInt hpoint
    rw [integral_const_mul, hmass] at hmono
    simpa [intervalMinimalPowerMassLower, hγ1, mul_comm] using hmono
  · have hγge : 1 ≤ p.γ := le_of_not_ge hγ1
    have hj := (convexOn_rpow hγge).map_integral_le
      (Real.continuous_rpow_const p.hγ.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall hU_nonneg) hUint
      (by simpa [Function.comp_apply] using hUpowInt)
    simpa [intervalMinimalPowerMassLower, hγ1, Function.comp_apply, hmass]
      using hj

/-- The concrete pointwise signal floor determined by mass and an upper
bound. -/
def intervalMinimalSignalLower
    (p : CM2Params) (uStar M : ℝ) : ℝ :=
  unitIntervalResolverMassGapConstant p * p.ν *
    intervalMinimalPowerMassLower p uStar M

theorem intervalMinimalSignalLower_pos
    (p : CM2Params) {uStar M : ℝ}
    (huStar : 0 < uStar) (hM : 0 < M) :
    0 < intervalMinimalSignalLower p uStar M := by
  have hmoment : 0 < intervalMinimalPowerMassLower p uStar M := by
    unfold intervalMinimalPowerMassLower
    split_ifs
    · exact mul_pos huStar (Real.rpow_pos_of_pos hM _)
    · exact Real.rpow_pos_of_pos huStar p.γ
  exact mul_pos
    (mul_pos (unitIntervalResolverMassGapConstant_pos p) p.hν) hmoment

/-- At one positive classical slice, exact mass and a pointwise upper bound
produce the concrete closed-interval lower bound for the elliptic signal. -/
theorem intervalDomain_solution_signal_lower_of_mass_upper
    (p : CM2Params) {T t uStar M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hM : 0 < M)
    (hmass : intervalDomain.integral (u t) = uStar)
    (hupper : ∀ z : intervalDomainPoint, u t z ≤ M) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      intervalMinimalSignalLower p uStar M ≤ intervalDomainLift (v t) x := by
  let U : ℝ → ℝ := liftRepr (u t)
  have hU_cont : Continuous U := by
    apply liftRepr_continuous
    exact ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn
  have hU_eq : ∀ y ∈ Icc (0 : ℝ) 1,
      U y = intervalDomainLift (u t) y := by
    intro y hy
    exact liftRepr_eq_on_Icc hy
  have hU_nonneg : ∀ y, 0 ≤ U y := by
    intro y
    dsimp [U, liftRepr]
    rw [intervalDomainLift, dif_pos (clamp01_mem y)]
    exact (hsol.u_pos' ht.1 ht.2).le
  have hU_le : ∀ y, U y ≤ M := by
    intro y
    dsimp [U, liftRepr]
    rw [intervalDomainLift, dif_pos (clamp01_mem y)]
    exact hupper _
  have hU_mass : (∫ y, U y ∂(intervalMeasure 1)) = uStar := by
    rw [IntervalConjugateKernelIBP.intervalMeasure_one_integral_eq_intervalIntegral]
    calc
      (∫ y in (0 : ℝ)..1, U y) =
          ∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y := by
            apply intervalIntegral.integral_congr
            intro y hy
            rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
            exact hU_eq y hy
      _ = intervalDomain.integral (u t) := rfl
      _ = uStar := hmass
  have hmoment := intervalMinimalPowerMassLower_le_integral
    p hU_cont hU_nonneg hU_le hU_mass
  let source : ℝ → ℝ := fun y => p.ν * U y ^ p.γ
  have hsource_cont : Continuous source := by
    dsimp [source]
    exact continuous_const.mul
      ((Real.continuous_rpow_const p.hγ.le).comp hU_cont)
  have hsource_nonneg : ∀ y, 0 ≤ source y := by
    intro y
    exact mul_nonneg p.hν.le (Real.rpow_nonneg (hU_nonneg y) _)
  have hsource_upper : ∀ y, source y ≤ p.ν * M ^ p.γ := by
    intro y
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hU_nonneg y) (hU_le y) p.hγ.le) p.hν.le
  have hB : 0 ≤ p.ν * M ^ p.γ :=
    mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)
  have hsource_bound : ∀ y, |source y| ≤ p.ν * M ^ p.γ := by
    intro y
    rw [abs_of_nonneg (hsource_nonneg y)]
    exact hsource_upper y
  have hsource_int : Integrable source (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound
      hsource_cont.aestronglyMeasurable hsource_bound
  have hsourceMass : p.ν * intervalMinimalPowerMassLower p uStar M ≤
      ∫ y, source y ∂(intervalMeasure 1) := by
    have hsourceIntegral : (∫ y, source y ∂(intervalMeasure 1)) =
        p.ν * ∫ y, U y ^ p.γ ∂(intervalMeasure 1) := by
      dsimp [source]
      rw [integral_const_mul]
    rw [hsourceIntegral]
    exact mul_le_mul_of_nonneg_left hmoment p.hν.le
  intro x hx
  have hresolver := cosineResolver_ge_massGap_Icc p hsource_cont hB
    hsource_nonneg hsource_bound hsource_int hx
  have hmassmul : intervalMinimalSignalLower p uStar M ≤
      unitIntervalResolverMassGapConstant p *
        (∫ y, source y ∂(intervalMeasure 1)) := by
    dsimp [intervalMinimalSignalLower]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hsourceMass
        (unitIntervalResolverMassGapConstant_pos p).le)
  have hsource_coeff : ∀ k,
      cosineCoeffs source k =
        (intervalNeumannResolverSourceCoeff p (u t) k).re := by
    intro k
    calc
      cosineCoeffs source k =
          cosineCoeffs
            (fun y => p.ν * intervalDomainLift (u t) y ^ p.γ) k := by
              apply cosineCoeffs_congr_on_Icc
              intro y hy
              dsimp [source]
              rw [hU_eq y hy]
      _ = (intervalNeumannResolverSourceCoeff p (u t) k).re := by
        symm
        exact resolverSourceCoeff_re_eq_cosineCoeffs p (u t) k
  have hsource_sq : Summable (fun k : ℕ => (cosineCoeffs source k) ^ 2) :=
    cosineCoeffs_sq_summable_of_continuousOn hsource_cont.continuousOn
  have hsource_resolver :
      (∑' k, cosineCoeffs source k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k)) =
          intervalNeumannResolverR p (u t) ⟨x, hx⟩ := by
    unfold intervalNeumannResolverR
    apply tsum_congr
    intro k
    rw [hsource_coeff k, resolverCoeff_re_eq]
    have heig : unitIntervalNeumannSpectrum.eigenvalue k =
        unitIntervalCosineEigenvalue k := by
      rw [show unitIntervalNeumannSpectrum.eigenvalue k =
        (k : ℝ) ^ 2 * Real.pi ^ 2 from rfl, unitIntervalCosineEigenvalue]
      ring
    rw [heig]
    ring
  have hv :=
    IntervalChiNegH1PhysicalResolverSupProducer.solution_v_eq_resolver_pointwise_Icc
      hsol ht hx
  calc
    intervalMinimalSignalLower p uStar M ≤
        unitIntervalResolverMassGapConstant p *
          (∫ y, source y ∂(intervalMeasure 1)) := hmassmul
    _ ≤ ∑' k, cosineCoeffs source k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k) := hresolver
    _ = intervalNeumannResolverR p (u t) ⟨x, hx⟩ := hsource_resolver
    _ = intervalDomainLift (v t) x := hv

/-- The two concrete constants needed by the minimal stability thresholds are
chosen before the orbit.  Every physical-mass bounded global orbit eventually
obeys both the corresponding `u` upper bound and `v` lower bound. -/
theorem exists_minimal_eventual_upper_and_signal_lower
    (p : CM2Params) {uStar : ℝ}
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hthreshold : p.χ₀ < chiBeta p) (huStar : 0 < uStar) :
    ∃ uBar > 0, ∃ vLower > 0,
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomain p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomain u uStar →
          (∀ᶠ t : ℝ in atTop, intervalDomain.supNorm (u t) ≤ uBar) ∧
          (∀ᶠ t : ℝ in atTop,
            ∀ x : intervalDomainPoint, vLower ≤ v t x) := by
  obtain ⟨uBar, huBar, hupperAll⟩ :=
    exists_minimal_eventual_uniform_upper_bound
      p hm ha0 hb0 hbeta hchi hthreshold huStar
  let vLower : ℝ := intervalMinimalSignalLower p uStar uBar
  have hvLower : 0 < vLower := by
    simpa [vLower] using intervalMinimalSignalLower_pos p huStar huBar
  refine ⟨uBar, huBar, vLower, hvLower, ?_⟩
  intro u v huv hmass
  have hupperEv := hupperAll u v huv hmass
  refine ⟨hupperEv, ?_⟩
  filter_upwards [hupperEv, eventually_gt_atTop (0 : ℝ)] with t hupperT ht
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain p T u v :=
    huv.1.classical hT
  have htmem : t ∈ Ioo (0 : ℝ) T := ⟨ht, htT⟩
  have hpointUpper : ∀ z : intervalDomainPoint, u t z ≤ uBar := by
    intro z
    have hz :=
      IntervalChiNegH1PhysicalResolverSupProducer.intervalDomainLift_le_supNorm_of_classical
        hsol htmem z.property
    have hz' : u t z ≤ intervalDomain.supNorm (u t) := by
      simpa [intervalDomainLift, z.property] using hz
    exact hz'.trans hupperT
  have hmassT : intervalDomain.integral (u t) = uStar := by
    simpa [HasEquilibriumMassOnPositiveTimes, intervalDomain] using
      hmass t ht
  have hsignal := intervalDomain_solution_signal_lower_of_mass_upper
    p hsol htmem huBar hmassT hpointUpper
  intro x
  have hx := hsignal x.1 x.property
  simpa [vLower, intervalDomainLift, x.property] using hx

#print axioms intervalMinimalPowerMassLower_le_integral
#print axioms intervalMinimalSignalLower_pos
#print axioms intervalDomain_solution_signal_lower_of_mass_upper
#print axioms exists_minimal_eventual_upper_and_signal_lower

end

end ShenWork.Paper3
