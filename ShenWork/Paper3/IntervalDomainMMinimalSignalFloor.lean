import ShenWork.Paper3.IntervalDomainMMinimalEventualUpper
import ShenWork.Paper3.IntervalDomainMinimalSignalFloor
import ShenWork.Paper2.IntervalDomainMEllipticResolverAgreementIcc

/-!
# M-native minimal-model eventual box (upper bound + signal floor), `1 ≤ m < 2`

Mirror of `IntervalDomainMinimalSignalFloor.lean` on the faithful `u^m`-flux
domain `intervalDomainM`.  The signal equation is `m`-independent, so the
mass-lower ⇒ signal-lower mechanism transfers verbatim through the M-native
elliptic resolver identity `solution_v_eq_resolver_pointwise_IccM`; the upper
bound is the already-proved orbit-independent
`exists_intervalDomainM_minimal_eventual_uniform_upper_bound`.
-/

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
open ShenWork.IntervalPicardLimitCoeffConv
open ShenWork.IntervalDomainLogisticWeakH2Adapter

noncomputable section

/-- Pointwise supremum bound for a faithful general-`m` classical slice
(public M-native counterpart of the private `abs_lift_le_supNorm_M`). -/
theorem intervalDomainM_lift_le_supNorm_of_classical
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (u t) y ≤ intervalDomainSupNorm (u t) := by
  classical
  have hcont : ContinuousOn (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hbdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u t x|)) := by
    obtain ⟨B, hB⟩ :=
      (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
    refine ⟨B, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hBx := hB ⟨x.1, x.2, rfl⟩
    have hlift : intervalDomainLift (u t) x.1 = u t x := by
      simp [intervalDomainLift, x.2]
    simpa only [hlift] using hBx
  have hle : |u t ⟨y, hy⟩| ≤ intervalDomainSupNorm (u t) :=
    le_csSup hbdd ⟨⟨y, hy⟩, rfl⟩
  have hlift : intervalDomainLift (u t) y = u t ⟨y, hy⟩ := by
    simp [intervalDomainLift, hy]
  rw [hlift]
  exact (le_abs_self _).trans hle

theorem intervalDomainM_solution_signal_lower_of_mass_upper
    (p : CM2Params) {T t uStar M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
    ShenWork.Paper2.IntervalDomainM.solution_v_eq_resolver_pointwise_IccM
      hsol ht hx
  calc
    intervalMinimalSignalLower p uStar M ≤
        unitIntervalResolverMassGapConstant p *
          (∫ y, source y ∂(intervalMeasure 1)) := hmassmul
    _ ≤ ∑' k, cosineCoeffs source k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k) := hresolver
    _ = intervalNeumannResolverR p (u t) ⟨x, hx⟩ := hsource_resolver
    _ = intervalDomainLift (v t) x := hv


/-- **M-native minimal eventual box producer.**  Every physical-mass bounded
global faithful orbit eventually obeys one orbit-independent upper bound and the
matching signal floor, both chosen before the orbit is quantified. -/
theorem exists_intervalDomainM_minimal_eventual_upper_and_signal_lower
    (p : CM2Params) {uStar : ℝ}
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀) (huStar : 0 < uStar) :
    ∃ uBar > 0, ∃ vLower > 0,
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomainM p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
          (∀ᶠ t : ℝ in atTop, intervalDomainM.supNorm (u t) ≤ uBar) ∧
          (∀ᶠ t : ℝ in atTop,
            ∀ x : intervalDomainPoint, vLower ≤ v t x) := by
  obtain ⟨uBar, huBar, hupperAll⟩ :=
    exists_intervalDomainM_minimal_eventual_uniform_upper_bound
      p hm ha0 hb0 hbeta hchi huStar
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
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    huv.1.classical hT
  have htmem : t ∈ Ioo (0 : ℝ) T := ⟨ht, htT⟩
  have hpointUpper : ∀ z : intervalDomainPoint, u t z ≤ uBar := by
    intro z
    have hz := intervalDomainM_lift_le_supNorm_of_classical hsol htmem z.property
    have hz' : u t z ≤ intervalDomainSupNorm (u t) := by
      simpa [intervalDomainLift, z.property] using hz
    exact hz'.trans hupperT
  have hmassT : intervalDomain.integral (u t) = uStar := by
    simpa [HasEquilibriumMassOnPositiveTimes, intervalDomainM] using
      hmass t ht
  have hsignal := intervalDomainM_solution_signal_lower_of_mass_upper
    p hsol htmem huBar hmassT hpointUpper
  intro x
  have hx := hsignal x.1 x.property
  simpa [vLower, intervalDomainLift, x.property] using hx

/-- The orbit-independent upper/floor pair required by the M-native minimal1
threshold, as a proposition with a proved producer. -/
def IntervalDomainMMinimalEventualBox
    (p : CM2Params) (uStar uBar vLower : ℝ) : Prop :=
  0 < uBar ∧ 0 < vLower ∧
    ∀ (u v : ℝ → intervalDomainPoint → ℝ),
      PositiveGlobalBoundedSolution intervalDomainM p u v →
      HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
        (∀ᶠ t : ℝ in atTop, intervalDomainM.supNorm (u t) ≤ uBar) ∧
        (∀ᶠ t : ℝ in atTop,
          ∀ x : intervalDomainPoint, vLower ≤ v t x)

/-- Canonical concrete M-native constants: the proved eventual box when one
exists, a harmless default otherwise. -/
noncomputable def intervalDomainMMinimalEventualBoxConstants
    (p : CM2Params) (uStar : ℝ) : ℝ × ℝ := by
  classical
  exact
    if h : ∃ c : ℝ × ℝ,
        IntervalDomainMMinimalEventualBox p uStar c.1 c.2 then
      Classical.choose h
    else
      (1, 1)

/-- In the subcritical `1 ≤ m < 2` minimal regime, the canonical M-native
constants are the output of the genuine upper/floor producer. -/
theorem intervalDomainMMinimalEventualBoxConstants_spec
    (p : CM2Params) {uStar : ℝ}
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀) (huStar : 0 < uStar) :
    IntervalDomainMMinimalEventualBox p uStar
      (intervalDomainMMinimalEventualBoxConstants p uStar).1
      (intervalDomainMMinimalEventualBoxConstants p uStar).2 := by
  have hex : ∃ c : ℝ × ℝ,
      IntervalDomainMMinimalEventualBox p uStar c.1 c.2 := by
    obtain ⟨uBar, huBar, vLower, hvLower, hbox⟩ :=
      exists_intervalDomainM_minimal_eventual_upper_and_signal_lower
        p hm ha0 hb0 hbeta hchi huStar
    exact ⟨(uBar, vLower), huBar, hvLower, hbox⟩
  rw [intervalDomainMMinimalEventualBoxConstants]
  simp only [dif_pos hex]
  exact Classical.choose_spec hex

#print axioms intervalDomainM_solution_signal_lower_of_mass_upper
#print axioms exists_intervalDomainM_minimal_eventual_upper_and_signal_lower
#print axioms intervalDomainMMinimalEventualBoxConstants_spec

end

end ShenWork.Paper3
