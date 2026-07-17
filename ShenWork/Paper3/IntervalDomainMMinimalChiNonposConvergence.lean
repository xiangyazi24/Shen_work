import ShenWork.Paper3.IntervalDomainSolutionPowerResolverGap
import ShenWork.Paper3.IntervalDomainStrictMaxDissipation
import ShenWork.Paper3.IntervalDomainMinimalMaxConvergence
import ShenWork.Paper3.IntervalDomainMinimalChiZeroHeat
import ShenWork.Paper3.IntervalDomainMNegativeSensitivity
import ShenWork.Paper2.IntervalDomainMEllipticResolverAgreementIcc
import ShenWork.Paper2.IntervalDomainMChiNonposMax

/-!
# General-`m` minimal convergence for χ₀ ≤ 0

This file proves uniform convergence of the population to its physical mean
in the minimal model (a = b = 0) with nonpositive sensitivity (χ₀ ≤ 0) on
the faithful general-`m` domain `intervalDomainM`.

The proof splits into two cases:
- **χ₀ < 0**: the signal gap at the spatial maximum provides a quantitative
  strict decay rate, converted to eventual entry below every threshold via
  Gronwall, then combined with static closeness.
- **χ₀ = 0**: the PDE reduces to the heat equation `u_t = u_xx` regardless
  of `m` (since both logistic and chemotaxis terms vanish), so we use the
  general-`m` Duhamel restart identity to reduce to the heat semigroup.
-/

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMMinPersistence
open ShenWork.Paper2.IntervalDomainMChiNonpos
open ShenWork.MaxPrincipleAtoms ShenWork.MinPersistenceAtoms
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs
  intervalNeumannFullKernel intervalNeumannFullKernel_integrable
  intervalFullSemigroupOperator_const)
open ShenWork.PDE (intervalNeumannResolverR)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (intervalConjugateDuhamelMapM)

noncomputable section

-- ============================================================
-- Signal gap for intervalDomainM (general-m)
-- ============================================================

/-- The quantitative signal gap on `intervalDomainM`. The proof is identical
to `intervalDomain_solution_signalGapConstant_le` but uses
`solution_v_eq_resolver_pointwise_IccM` for the elliptic identification. -/
theorem intervalDomainM_solution_signalGapConstant_le
    (p : CM2Params) {T t uStar M d : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : intervalDomainM.integral (u t) = uStar)
    (hupper : ∀ z : intervalDomainPoint, u t z ≤ M)
    (hMgap : uStar + d ≤ M) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainSignalGapConstant p uStar d ≤
        p.ν * M ^ p.γ / p.μ - intervalDomainLift (v t) x := by
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
      _ = intervalDomainM.integral (u t) := rfl
      _ = uStar := hmass
  have hqSource_le := intervalPowerSourceGapConstant_le_integral
    p huStar hd hU_cont hU_nonneg hU_le hU_mass hMgap
  let source : ℝ → ℝ := fun y => p.ν * (M ^ p.γ - U y ^ p.γ)
  have hM : 0 < M := lt_of_lt_of_le (by linarith) hMgap
  have hsource_cont : Continuous source := by
    dsimp [source]
    exact continuous_const.mul
      (continuous_const.sub
        ((Real.continuous_rpow_const p.hγ.le).comp hU_cont))
  have hsource_nonneg : ∀ y, 0 ≤ source y := by
    intro y
    dsimp [source]
    exact mul_nonneg p.hν.le (sub_nonneg.mpr
      (Real.rpow_le_rpow (hU_nonneg y) (hU_le y) p.hγ.le))
  have hsource_upper : ∀ y, source y ≤ p.ν * M ^ p.γ := by
    intro y
    dsimp [source]
    have hpow : 0 ≤ U y ^ p.γ := Real.rpow_nonneg (hU_nonneg y) _
    nlinarith [p.hν.le]
  have hB : 0 ≤ p.ν * M ^ p.γ :=
    mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)
  have hsource_bound : ∀ y, |source y| ≤ p.ν * M ^ p.γ := by
    intro y
    rw [abs_of_nonneg (hsource_nonneg y)]
    exact hsource_upper y
  have hsource_int : Integrable source (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound
      hsource_cont.aestronglyMeasurable hsource_bound
  intro x hx
  have hresolver := cosineResolver_ge_massGap_Icc p hsource_cont hB
    hsource_nonneg hsource_bound hsource_int hx
  have hmassmul : intervalDomainSignalGapConstant p uStar d ≤
      unitIntervalResolverMassGapConstant p *
      (∫ y, source y ∂(intervalMeasure 1)) := by
    dsimp [intervalDomainSignalGapConstant]
    exact mul_le_mul_of_nonneg_left hqSource_le
      (unitIntervalResolverMassGapConstant_pos p).le
  have halgebra := cosinePowerSourceDeficit_resolver_eq_const_sub
    p hU_cont hU_eq hx (M := M)
  have hv :=
    IntervalDomainM.solution_v_eq_resolver_pointwise_IccM
      hsol ht hx
  calc
    intervalDomainSignalGapConstant p uStar d ≤
        unitIntervalResolverMassGapConstant p *
        (∫ y, source y ∂(intervalMeasure 1)) := hmassmul
    _ ≤ ∑' k, cosineCoeffs source k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k) := hresolver
    _ = p.ν * M ^ p.γ / p.μ -
        intervalNeumannResolverR p (u t) ⟨x, hx⟩ := by
          simpa [source] using halgebra
    _ = p.ν * M ^ p.γ / p.μ - intervalDomainLift (v t) x := by
      rw [hv]

-- ============================================================
-- Strict max slope for intervalDomainM (χ₀ < 0)
-- ============================================================

/-- General-`m` dissipation constant at the spatial maximum of a
mass-constrained orbit. Uses `u^m` instead of `u` in front of
the signal gap term. -/
def intervalDomainMMinimalMaxDissipationConstant
    (p : CM2Params) (uStar d B : ℝ) : ℝ :=
  (-p.χ₀) *
    ((uStar + d) ^ p.m *
      (1 + p.ν * B ^ p.γ / p.μ) ^ (-p.β) *
      (p.μ * intervalDomainSignalGapConstant p uStar d))

theorem intervalDomainMMinimalMaxDissipationConstant_pos
    (p : CM2Params) {uStar d B : ℝ}
    (hχ : p.χ₀ < 0) (huStar : 0 < uStar) (hd : 0 < d)
    (hB : uStar + d ≤ B) :
    0 < intervalDomainMMinimalMaxDissipationConstant p uStar d B := by
  have hbase : 0 < 1 + p.ν * B ^ p.γ / p.μ := by
    have hB0 : 0 ≤ B := le_trans (by linarith) hB
    have : 0 ≤ p.ν * B ^ p.γ / p.μ :=
      div_nonneg (mul_nonneg p.hν.le (Real.rpow_nonneg hB0 _)) p.hμ.le
    linarith
  unfold intervalDomainMMinimalMaxDissipationConstant
  exact mul_pos (neg_pos.mpr hχ)
    (mul_pos
      (mul_pos
        (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_pos_of_pos hbase _))
      (mul_pos p.hμ (intervalDomainSignalGapConstant_pos p huStar hd)))

-- ============================================================
-- Boundary lift non-differentiability
-- ============================================================

/-- At the left boundary, `intervalDomainLift (u t)` is not differentiable
because it equals `u(t,0) > 0` at `x = 0` but vanishes for `x < 0`. -/
private theorem lift_not_differentiableAt_left
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ¬DifferentiableAt ℝ (intervalDomainLift (u t)) 0 := by
  intro hdiff
  have hU0pos : 0 < intervalDomainLift (u t) 0 := by
    rw [intervalDomainLift, dif_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
      ⟨le_rfl, zero_le_one⟩)]
    exact hsol.u_pos' ht0 htT
  have hzero : ∀ᶠ x in nhdsWithin (0 : ℝ) (Iio 0),
      intervalDomainLift (u t) x = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
    rw [intervalDomainLift, dif_neg (fun h : x ∈ Icc (0 : ℝ) 1 =>
      absurd h.1 (not_le.mpr hx))]
  have hleft : Tendsto (intervalDomainLift (u t))
      (nhdsWithin (0 : ℝ) (Iio 0)) (nhds 0) :=
    tendsto_const_nhds.congr' (hzero.mono (fun _ h => h.symm))
  haveI : (nhdsWithin (0 : ℝ) (Iio 0)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Iio (a := (0 : ℝ))]; exact le_refl (0 : ℝ))
  linarith [tendsto_nhds_unique hleft
    (hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)]

/-- At the right boundary, `intervalDomainLift (u t)` is not differentiable
because it equals `u(t,1) > 0` at `x = 1` but vanishes for `x > 1`. -/
private theorem lift_not_differentiableAt_right
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ¬DifferentiableAt ℝ (intervalDomainLift (u t)) 1 := by
  intro hdiff
  have hU1pos : 0 < intervalDomainLift (u t) 1 := by
    rw [intervalDomainLift, dif_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from
      ⟨zero_le_one, le_rfl⟩)]
    exact hsol.u_pos' ht0 htT
  have hzero : ∀ᶠ x in nhdsWithin (1 : ℝ) (Ioi 1),
      intervalDomainLift (u t) x = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    rw [intervalDomainLift, dif_neg (fun h : x ∈ Icc (0 : ℝ) 1 =>
      absurd h.2 (not_le.mpr hx))]
  have hright : Tendsto (intervalDomainLift (u t))
      (nhdsWithin (1 : ℝ) (Ioi 1)) (nhds 0) :=
    tendsto_const_nhds.congr' (hzero.mono (fun _ h => h.symm))
  haveI : (nhdsWithin (1 : ℝ) (Ioi 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioi (a := (1 : ℝ))]; exact le_refl (1 : ℝ))
  linarith [tendsto_nhds_unique hright
    (hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)]

private theorem lift_deriv_zero_at_left
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    deriv (intervalDomainLift (u t)) 0 = 0 :=
  deriv_zero_of_not_differentiableAt
    (lift_not_differentiableAt_left hsol ht0 htT)

private theorem lift_deriv_zero_at_right
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    deriv (intervalDomainLift (u t)) 1 = 0 :=
  deriv_zero_of_not_differentiableAt
    (lift_not_differentiableAt_right hsol ht0 htT)

-- ============================================================
-- PhysRep quantitative signal-gap bound
-- ============================================================

/-- When `deriv U e = 0`, the physical representative of the chemotaxis
divergence is bounded above by the negative of the signal-gap product.
This quantitative version of `physicalRep_nonpos_at_neumann_argmax`
retains the signal gap instead of just proving `≤ 0`. -/
private theorem physRep_le_neg_signal_of_deriv_zero
    {p : CM2Params} {T t : ℝ} {e q : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (he : e ∈ Icc (0 : ℝ) 1)
    (hdu : deriv (intervalDomainLift (u t)) e = 0)
    (hq : 0 < q)
    (hsignal : q ≤ p.ν * intervalDomainLift (u t) e ^ p.γ / p.μ -
        intervalDomainLift (v t) e) :
    classicalChemDivMPhysicalRep p u v t e ≤
      -(intervalDomainLift (u t) e ^ p.m *
        (1 + intervalDomainLift (v t) e) ^ (-p.β) *
        (p.μ * q)) := by
  have hUe_nonneg : 0 ≤ intervalDomainLift (u t) e := by
    simp only [intervalDomainLift, dif_pos he]
    exact (hsol.u_pos' ht0 htT).le
  have hVnn : 0 ≤ intervalDomainLift (v t) e := by
    simp only [intervalDomainLift, dif_pos he]
    exact hsol.v_nonneg ht0 htT
  have hbase : 0 < 1 + intervalDomainLift (v t) e := by linarith
  have hrep : classicalChemDivMPhysicalRep p u v t e =
      intervalDomainLift (u t) e ^ p.m *
        (-p.β * (1 + intervalDomainLift (v t) e) ^ (-p.β - 1) *
            deriv (intervalDomainLift (v t)) e ^ 2 +
          (1 + intervalDomainLift (v t) e) ^ (-p.β) *
            (p.μ * intervalDomainLift (v t) e -
              p.ν * intervalDomainLift (u t) e ^ p.γ)) := by
    simp only [classicalChemDivMPhysicalRep]
    rw [hdu]
    ring
  have hA : -p.β * (1 + intervalDomainLift (v t) e) ^ (-p.β - 1) *
      deriv (intervalDomainLift (v t)) e ^ 2 ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonpos_of_nonneg
      · exact neg_nonpos.mpr p.hβ
      · exact Real.rpow_nonneg hbase.le _
    · exact sq_nonneg _
  have hsignal_neg : p.μ * intervalDomainLift (v t) e -
      p.ν * intervalDomainLift (u t) e ^ p.γ ≤ -(p.μ * q) := by
    have h1 : p.μ * q ≤ p.ν * intervalDomainLift (u t) e ^ p.γ -
        p.μ * intervalDomainLift (v t) e := by
      have := mul_le_mul_of_nonneg_left hsignal p.hμ.le
      rw [mul_sub, mul_div_cancel₀ _ p.hμ.ne'] at this
      exact this
    linarith
  have hbase_rpow : 0 < (1 + intervalDomainLift (v t) e) ^ (-p.β) :=
    Real.rpow_pos_of_pos hbase _
  have hB : (1 + intervalDomainLift (v t) e) ^ (-p.β) *
      (p.μ * intervalDomainLift (v t) e -
        p.ν * intervalDomainLift (u t) e ^ p.γ) ≤
      (1 + intervalDomainLift (v t) e) ^ (-p.β) * (-(p.μ * q)) :=
    mul_le_mul_of_nonneg_left hsignal_neg hbase_rpow.le
  have hsum : -p.β * (1 + intervalDomainLift (v t) e) ^ (-p.β - 1) *
      deriv (intervalDomainLift (v t)) e ^ 2 +
    (1 + intervalDomainLift (v t) e) ^ (-p.β) *
      (p.μ * intervalDomainLift (v t) e -
        p.ν * intervalDomainLift (u t) e ^ p.γ) ≤
    (1 + intervalDomainLift (v t) e) ^ (-p.β) * (-(p.μ * q)) := by
    linarith [hA, hB]
  rw [hrep]
  have := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hUe_nonneg p.m)
  calc intervalDomainLift (u t) e ^ p.m *
      (-p.β * (1 + intervalDomainLift (v t) e) ^ (-p.β - 1) *
          deriv (intervalDomainLift (v t)) e ^ 2 +
        (1 + intervalDomainLift (v t) e) ^ (-p.β) *
          (p.μ * intervalDomainLift (v t) e -
            p.ν * intervalDomainLift (u t) e ^ p.γ))
    ≤ intervalDomainLift (u t) e ^ p.m *
      ((1 + intervalDomainLift (v t) e) ^ (-p.β) * (-(p.μ * q))) := this
    _ = -(intervalDomainLift (u t) e ^ p.m *
      (1 + intervalDomainLift (v t) e) ^ (-p.β) * (p.μ * q)) := by ring

-- ============================================================
-- Three-way strict slope dispatcher
-- ============================================================

/-- At every spatial argmax of a mass-constrained `intervalDomainM` solution
with strictly negative sensitivity, the excess above the mean forces a
uniform negative time slope. This is the general-`m` analogue of
`intervalDomain_minimal_argmax_uniform_strict_slope`. -/
theorem intervalDomainM_minimal_argmax_uniform_strict_slope
    {p : CM2Params} {T t uStar d B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ < 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : intervalDomainM.integral (u t) = uStar)
    (hmax : ∀ y, u t y ≤ u t x)
    (hMgap : uStar + d ≤ intervalDomainLift (u t) x.1)
    (hMB : intervalDomainLift (u t) x.1 ≤ B) :
    intervalDomain.timeDeriv u t x ≤
      -intervalDomainMMinimalMaxDissipationConstant p uStar d B := by
  let M : ℝ := intervalDomainLift (u t) x.1
  have hliftx : intervalDomainLift (u t) x.1 = u t x := by
    simp only [intervalDomainLift]
    exact (dif_pos x.2).trans
      (congrArg (u t) (Subtype.coe_eta x x.2))
  have hupper : ∀ z : intervalDomainPoint, u t z ≤ M := by
    intro z
    dsimp [M]
    rw [hliftx]
    exact hmax z
  have hsignalAll := intervalDomainM_solution_signalGapConstant_le
    p hsol ⟨ht0, htT⟩ huStar hd hmass hupper hMgap
  have hsignal := hsignalAll x.1 x.2
  have hqpos := intervalDomainSignalGapConstant_pos p huStar hd
  have hMpos : 0 < M := lt_of_lt_of_le (by linarith) hMgap
  have hBnonneg : 0 ≤ B := le_trans hMpos.le hMB
  have hMpow : M ^ p.γ ≤ B ^ p.γ :=
    Real.rpow_le_rpow hMpos.le hMB p.hγ.le
  have hvliftx : intervalDomainLift (v t) x.1 = v t x := by
    simp only [intervalDomainLift]
    exact (dif_pos x.2).trans
      (congrArg (v t) (Subtype.coe_eta x x.2))
  have hv_nonneg : 0 ≤ intervalDomainLift (v t) x.1 := by
    rw [hvliftx]
    exact hsol.v_nonneg ht0 htT
  have hv_upper : intervalDomainLift (v t) x.1 ≤
      p.ν * B ^ p.γ / p.μ := by
    have hsignal0 : 0 ≤ p.ν * M ^ p.γ / p.μ -
        intervalDomainLift (v t) x.1 := le_trans hqpos.le hsignal
    have hmul : p.ν * M ^ p.γ ≤ p.ν * B ^ p.γ :=
      mul_le_mul_of_nonneg_left hMpow p.hν.le
    have hdiv : p.ν * M ^ p.γ / p.μ ≤
        p.ν * B ^ p.γ / p.μ :=
      div_le_div_of_nonneg_right hmul p.hμ.le
    linarith
  have hbaseV : 0 < 1 + intervalDomainLift (v t) x.1 := by linarith
  have hbase_le : 1 + intervalDomainLift (v t) x.1 ≤
      1 + p.ν * B ^ p.γ / p.μ := by linarith
  have hrpow :
      (1 + p.ν * B ^ p.γ / p.μ) ^ (-p.β) ≤
        (1 + intervalDomainLift (v t) x.1) ^ (-p.β) :=
    Real.rpow_le_rpow_of_nonpos hbaseV hbase_le (neg_nonpos.mpr p.hβ)
  have hMm_pow : (uStar + d) ^ p.m ≤ M ^ p.m :=
    Real.rpow_le_rpow (by linarith) hMgap p.hm.le
  have hfactor :
      (uStar + d) ^ p.m * (1 + p.ν * B ^ p.γ / p.μ) ^ (-p.β) ≤
        M ^ p.m * (1 + intervalDomainLift (v t) x.1) ^ (-p.β) := by
    exact mul_le_mul hMm_pow hrpow
      (Real.rpow_pos_of_pos (lt_of_lt_of_le hbaseV hbase_le) _).le
      (Real.rpow_nonneg hMpos.le _)
  have hμq : 0 ≤ p.μ * intervalDomainSignalGapConstant p uStar d :=
    (mul_pos p.hμ hqpos).le
  have hactual :
      (uStar + d) ^ p.m * (1 + p.ν * B ^ p.γ / p.μ) ^ (-p.β) *
          (p.μ * intervalDomainSignalGapConstant p uStar d) ≤
        M ^ p.m * (1 + intervalDomainLift (v t) x.1) ^ (-p.β) *
          (p.μ * intervalDomainSignalGapConstant p uStar d) :=
    mul_le_mul_of_nonneg_right hfactor hμq
  -- deriv U x = 0 at argmax (interior or boundary)
  have hdu : deriv (intervalDomainLift (u t)) x.1 = 0 := by
    rcases lt_or_eq_of_le x.2.1 with h0 | h0
    · rcases lt_or_eq_of_le x.2.2 with h1 | h1
      · exact (interior_argmax_deriv_zero hmax ⟨h0, h1⟩
          ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo
            ((hsol.regularity.1 t ⟨ht0, htT⟩).1) ⟨h0, h1⟩).1.differentiableAt)).deriv
      · rw [h1]; exact lift_deriv_zero_at_right hsol ht0 htT
    · rw [← h0]; exact lift_deriv_zero_at_left hsol ht0 htT
  -- physRep ≤ -(M^m * (1+V)^(-β) * μq)
  have hphysRep := physRep_le_neg_signal_of_deriv_zero
    hsol ht0 htT x.2 hdu hqpos hsignal
  -- Three-way dispatch: timeDeriv ≤ R - χ₀ * physRep
  have hmaxlift : ∀ y, intervalDomainLift (u t) y ≤
      intervalDomainLift (u t) x.1 := by
    intro y
    rw [hliftx]
    unfold intervalDomainLift
    split_ifs with hy
    · exact hmax ⟨y, hy⟩
    · exact (hsol.u_pos' ht0 htT).le
  have hstrict : intervalDomain.timeDeriv u t x ≤
      intervalDomainLift (u t) x.1 *
        (p.a - p.b * intervalDomainLift (u t) x.1 ^ p.α) -
      p.χ₀ * classicalChemDivMPhysicalRep p u v t x.1 := by
    rcases lt_or_eq_of_le x.2.1 with h0 | h0
    · rcases lt_or_eq_of_le x.2.2 with h1 | h1
      · -- interior
        have htmem : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
        obtain ⟨hC2, _, _, _, _, _, _⟩ := hsol.regularity
        have hu_c2 := (hC2 t htmem).1
        have huxx := interior_argmax_deriv2_nonpos hmax ⟨h0, h1⟩ hu_c2
        have hcd_eq : intervalDomainChemotaxisDivM p (u t) (v t) x =
            classicalChemDivMPhysicalRep p u v t x.1 :=
          intervalDomainMChemotaxisDiv_eq_physicalRep_interior
            hsol ht0 htT ⟨h0, h1⟩
        have hpde' : intervalDomain.timeDeriv u t x =
            deriv (deriv (intervalDomainLift (u t))) x.1 -
              p.χ₀ * intervalDomainChemotaxisDivM p (u t) (v t) x +
                intervalDomainLift (u t) x.1 *
                  (p.a - p.b * intervalDomainLift (u t) x.1 ^ p.α) := by
          rw [hliftx]
          exact hsol.pde_u ht0 htT
            (show x ∈ intervalDomainM.inside from by
              show x.1 ∈ Ioo (0 : ℝ) 1; exact ⟨h0, h1⟩)
        rw [hcd_eq] at hpde'
        linarith [hpde', huxx]
      · -- right boundary
        have hx11 : x.1 = 1 := h1
        have htd : intervalDomain.timeDeriv u t x =
            deriv (fun r => intervalDomainLift (u r) 1) t := by
          show deriv (fun s => u s x) t =
            deriv (fun r => intervalDomainLift (u r) 1) t
          congr 1; funext r
          rw [intervalDomainLift, dif_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from
            ⟨zero_le_one, le_rfl⟩)]
          exact (congrArg (u r) (Subtype.ext hx11.symm)).symm
        have hmaxlift1 : ∀ y, intervalDomainLift (u t) y ≤
            intervalDomainLift (u t) 1 := by
          intro y; rw [← hx11]; exact hmaxlift y
        have hb := boundary_max_point_right_M_strict hχ.le hsol ht0 htT hmaxlift1
        rw [htd, hx11]
        exact hb
    · -- left boundary
      have hx10 : x.1 = 0 := h0.symm
      have htd : intervalDomain.timeDeriv u t x =
          deriv (fun r => intervalDomainLift (u r) 0) t := by
        show deriv (fun s => u s x) t =
          deriv (fun r => intervalDomainLift (u r) 0) t
        congr 1; funext r
        rw [intervalDomainLift, dif_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
          ⟨le_rfl, zero_le_one⟩)]
        exact (congrArg (u r) (Subtype.ext hx10.symm)).symm
      have hmaxlift0 : ∀ y, intervalDomainLift (u t) y ≤
          intervalDomainLift (u t) 0 := by
        intro y; rw [← hx10]; exact hmaxlift y
      have hb := boundary_max_point_left_M_strict hχ.le hsol ht0 htT hmaxlift0
      rw [htd, hx10]
      exact hb
  -- Combine: timeDeriv ≤ R - χ₀ * physRep ≤ R + χ₀ * K
  rw [ha, hb] at hstrict
  simp only [zero_mul, sub_zero, mul_zero] at hstrict
  -- hstrict : timeDeriv ≤ -χ₀ * physRep
  -- hphysRep : physRep ≤ -(M^m * (1+V)^(-β) * μq)
  -- Need: -χ₀ * physRep ≤ χ₀ * (M^m * (1+V)^(-β) * μq)
  have hnχ : 0 ≤ -p.χ₀ := neg_nonneg.mpr hχ.le
  have hbound : -p.χ₀ * classicalChemDivMPhysicalRep p u v t x.1 ≤
      -p.χ₀ * (-(M ^ p.m *
        (1 + intervalDomainLift (v t) x.1) ^ (-p.β) *
        (p.μ * intervalDomainSignalGapConstant p uStar d))) :=
    mul_le_mul_of_nonneg_left hphysRep hnχ
  have hχmul := mul_le_mul_of_nonpos_left hactual hχ.le
  unfold intervalDomainMMinimalMaxDissipationConstant
  nlinarith

-- ============================================================
-- SupNorm antitone on positive times (general-m minimal)
-- ============================================================

theorem intervalDomainM_minimal_supNorm_antitone_positiveTimes
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ ≤ 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    intervalDomainM.supNorm (u t) ≤ intervalDomainM.supNorm (u s) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hH : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) hH
  have hmono := lemma31_zero_M p hχ ha hH hsol
  exact hmono s ⟨hs, by linarith⟩ t ⟨ht, by linarith⟩ hst

-- ============================================================
-- Gronwall decay for χ₀ < 0 (general-m minimal)
-- ============================================================

theorem intervalDomainM_minimal_chiNeg_supNorm_decay_if_above_mass_add
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ < 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {uStar d t : ℝ} (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (ht : 1 ≤ t)
    (habove : uStar + d < intervalDomainM.supNorm (u t)) :
    intervalDomainM.supNorm (u t) ≤
      intervalDomainM.supNorm (u 1) *
        Real.exp
          ((-intervalDomainMMinimalMaxDissipationConstant p uStar d
              (intervalDomainM.supNorm (u 1)) /
                intervalDomainM.supNorm (u 1)) * (t - 1)) := by
  let B : ℝ := intervalDomainM.supNorm (u 1)
  let C : ℝ := intervalDomainMMinimalMaxDissipationConstant p uStar d B
  let K : ℝ := -C / B
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hterminalB : intervalDomainM.supNorm (u t) ≤ B := by
    dsimp [B]
    exact intervalDomainM_minimal_supNorm_antitone_positiveTimes
      p ha hb hχ.le huv (by norm_num) ht
  have hBlevel : uStar + d ≤ B :=
    habove.le.trans hterminalB
  have hBpos : 0 < B := lt_of_lt_of_le (by linarith) hBlevel
  have hCpos : 0 < C := by
    dsimp [C]
    exact intervalDomainMMinimalMaxDissipationConstant_pos
      p hχ huStar hd hBlevel
  have hKneg : K < 0 := by
    dsimp [K]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hCpos) hBpos
  let H : ℝ := t + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have htH : t < H := by dsimp [H]; linarith
  have hsol := huv.classical H hH
  have hwindow : Icc (1 : ℝ) t ⊆ Ioo (0 : ℝ) H := by
    intro s hs
    exact ⟨lt_of_lt_of_le (by norm_num) hs.1,
      lt_of_le_of_lt hs.2 htH⟩
  have hmaxSlope : ∀ s ∈ Icc (1 : ℝ) t,
      ∀ xs ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u s) xs =
          sSup (intervalDomainLift (u s) '' Icc (0 : ℝ) 1) →
      deriv (fun r => intervalDomainLift (u r) xs) s ≤
        K * sSup (intervalDomainLift (u s) '' Icc (0 : ℝ) 1) := by
    intro s hs xs hxs hargmax
    have hsmem : s ∈ Ioo (0 : ℝ) H := hwindow hs
    have hcontU : ContinuousOn (intervalDomainLift (u s))
        (Icc (0 : ℝ) 1) :=
      ((hsol.regularity.2.2.2.2.1 s hsmem).1.1).continuousOn
    have hbdd : BddAbove
        (intervalDomainLift (u s) '' Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn hcontU).bddAbove
    have hmax : ∀ y, u s y ≤ u s ⟨xs, hxs⟩ := by
      intro y
      have huy : u s y = intervalDomainLift (u s) y.1 := by
        rw [intervalDomainLift,
          dif_pos (show (y.1 : ℝ) ∈ Icc (0 : ℝ) 1 from y.2),
          Subtype.coe_eta]
      have huxs : u s ⟨xs, hxs⟩ = intervalDomainLift (u s) xs := by
        rw [intervalDomainLift, dif_pos hxs]
      rw [huy, huxs, hargmax]
      exact le_csSup hbdd (mem_image_of_mem _ y.2)
    have hsupeq : intervalDomainM.supNorm (u s) =
        sSup (intervalDomainLift (u s) '' Icc (0 : ℝ) 1) :=
      supNorm_eq_sSup_lift_image
        (fun q => (hsol.u_pos' hsmem.1 hsmem.2).le)
    have hterminal : intervalDomainM.supNorm (u t) ≤
        intervalDomainM.supNorm (u s) :=
      intervalDomainM_minimal_supNorm_antitone_positiveTimes
        p ha hb hχ.le huv hsmem.1 hs.2
    have hlevel : uStar + d ≤ intervalDomainLift (u s) xs := by
      rw [hargmax, ← hsupeq]
      exact habove.le.trans hterminal
    have hsB : intervalDomainM.supNorm (u s) ≤ B := by
      dsimp [B]
      exact intervalDomainM_minimal_supNorm_antitone_positiveTimes
        p ha hb hχ.le huv (by norm_num) hs.1
    have hpointB : intervalDomainLift (u s) xs ≤ B := by
      rw [hargmax, ← hsupeq]
      exact hsB
    have hslope := intervalDomainM_minimal_argmax_uniform_strict_slope
      ha hb hχ hsol hsmem.1 hsmem.2 huStar hd
      (by simpa [intervalDomainM] using hmass s hsmem.1)
      hmax hlevel hpointB
    have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩ =
        deriv (fun r => intervalDomainLift (u r) xs) s := by
      show deriv (fun r => u r ⟨xs, hxs⟩) s =
        deriv (fun r => intervalDomainLift (u r) xs) s
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos hxs]
    rw [htd] at hslope
    have hKB : K * B = -C := by
      dsimp [K]
      exact div_mul_cancel₀ (-C) hBpos.ne'
    have hmul := mul_le_mul_of_nonpos_left hsB hKneg.le
    rw [hKB, hsupeq] at hmul
    exact hslope.trans hmul
  have hgron := intervalDomainM_supNorm_gronwall_on_window
    hsol hwindow hmaxSlope (t₁ := (1 : ℝ)) (t₂ := t)
      ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simpa [B, C, K] using hgron

-- ============================================================
-- Eventual entry for χ₀ < 0 (general-m minimal)
-- ============================================================

theorem intervalDomainM_minimal_chiNeg_eventually_supNorm_le_mass_add
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ < 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {uStar d : ℝ} (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar) :
    ∀ᶠ t in atTop,
      intervalDomainM.supNorm (u t) ≤ uStar + d := by
  let B : ℝ := intervalDomainM.supNorm (u 1)
  have hH2 : 0 < (2 : ℝ) := by norm_num
  have hsol2 := huv.classical 2 hH2
  have hmass1 : intervalDomainM.integral (u 1) = uStar := by
    simpa [intervalDomainM] using hmass 1 (by norm_num)
  have hmass_le := intervalDomainM_classicalSolution_mass_le_supNorm hsol2
    (⟨by norm_num, by norm_num⟩ : (1 : ℝ) ∈ Ioo 0 2)
  have hBmass : uStar ≤ B := by simpa [B, hmass1] using hmass_le
  have hBpos : 0 < B := lt_of_lt_of_le huStar hBmass
  have hBlevel : uStar + d ≤ max B (uStar + d) := le_max_right _ _
  let C₀ : ℝ := intervalDomainMMinimalMaxDissipationConstant
    p uStar d (max B (uStar + d))
  let K₀ : ℝ := -C₀ / max B (uStar + d)
  have hB₀pos : 0 < max B (uStar + d) :=
    lt_of_lt_of_le hBpos (le_max_left _ _)
  have hC₀pos : 0 < C₀ := by
    dsimp [C₀]
    exact intervalDomainMMinimalMaxDissipationConstant_pos
      p hχ huStar hd hBlevel
  have hK₀neg : K₀ < 0 := by
    dsimp [K₀]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hC₀pos) hB₀pos
  have hlin : Tendsto (fun t : ℝ => K₀ * (t - 1)) atTop atBot := by
    have hbase : Tendsto (fun t : ℝ => K₀ * t + (-K₀)) atTop atBot :=
      tendsto_atBot_add_const_right _ (-K₀)
        (tendsto_id.const_mul_atTop_of_neg hK₀neg)
    convert hbase using 1
    funext t
    ring
  have hexp : Tendsto (fun t : ℝ => Real.exp (K₀ * (t - 1)))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hlin
  have hdecay : Tendsto
      (fun t : ℝ => B * Real.exp (K₀ * (t - 1))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  have hthreshold : 0 < uStar + d := by linarith
  have hevlt : ∀ᶠ t in atTop,
      B * Real.exp (K₀ * (t - 1)) < uStar + d :=
    (tendsto_order.1 hdecay).2 _ hthreshold
  filter_upwards [hevlt, eventually_ge_atTop (1 : ℝ)] with t hright ht
  by_contra hnot
  have habove : uStar + d < intervalDomainM.supNorm (u t) :=
    lt_of_not_ge hnot
  have hBt : intervalDomainM.supNorm (u t) ≤ B := by
    dsimp [B]
    exact intervalDomainM_minimal_supNorm_antitone_positiveTimes
      p ha hb hχ.le huv (by norm_num) ht
  have hBeq : max B (uStar + d) = B := max_eq_left (habove.le.trans hBt)
  have hbound := intervalDomainM_minimal_chiNeg_supNorm_decay_if_above_mass_add
    p ha hb hχ huv huStar hd hmass ht habove
  have : intervalDomainM.supNorm (u t) ≤
      B * Real.exp (K₀ * (t - 1)) := by
    simpa [B, C₀, K₀, hBeq] using hbound
  linarith

-- ============================================================
-- χ₀ = 0 heat bridge (general-m)
-- ============================================================

/-- On every positive-time restart with χ₀ = 0 and a = b = 0,
the solution equals the heat semigroup applied to the initial slice.
This holds for all `m` because the `m`-dependent chemotaxis flux is
multiplied by χ₀ = 0 and the logistic source vanishes. -/
private theorem intervalDomainM_minimal_chiZero_restart_heat
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ = 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {a : ℝ} (ha0 : 0 < a) (x : intervalDomainPoint) :
    u (a + 1) x =
      intervalFullSemigroupOperator 1 (intervalDomainLift (u a)) x.1 := by
  have hH : 0 < a + 2 := by linarith
  have hsol := huv.classical (a + 2) hH
  have hr := IntervalDomainM.intervalDomainM_classical_bform_restart_pointwise
    hsol ha0 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
      (by norm_num : (0 : ℝ) < 1) (le_rfl : (1 : ℝ) ≤ 1) x
  have hlogzero : ∀ w : intervalDomainPoint → ℝ,
      logisticLifted p w = fun _ => 0 := by
    intro w
    funext y
    unfold logisticLifted
    unfold intervalLogisticSource
    rw [ha, hb]
    simp [intervalDomainLift]
  have hintzero :
      (∫ s in (0 : ℝ)..1,
        intervalFullSemigroupOperator (1 - s)
          (logisticLifted p
            (IntervalDomainM.classicalRestartTrajectoryM a 1 u s)) x.1) = 0 := by
    have hfun : (fun s : ℝ =>
        intervalFullSemigroupOperator (1 - s)
          (logisticLifted p
            (IntervalDomainM.classicalRestartTrajectoryM a 1 u s)) x.1) =
        fun _ => 0 := by
      funext s
      rw [hlogzero]
      unfold intervalFullSemigroupOperator
      simp
    rw [hfun]
    simp
  rw [intervalConjugateDuhamelMapM, hχ, hintzero] at hr
  simpa using hr

/-- One unit of heat evolution lowers the maximum by a fixed fraction
of the gap above the physical mean. General-m version. -/
private theorem intervalDomainM_minimal_chiZero_supNorm_unit_drop
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ = 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {a uStar d : ℝ} (ha0 : 0 < a)
    (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hgap : uStar + d ≤ intervalDomainM.supNorm (u a)) :
    intervalDomainM.supNorm (u (a + 1)) ≤
      intervalDomainM.supNorm (u a) - unitWindowHeatKernelFloor * d := by
  let M : ℝ := intervalDomainM.supNorm (u a)
  have hMpos : 0 < M := lt_of_lt_of_le (by linarith) hgap
  have hH : 0 < a + 2 := by linarith
  have hsol := huv.classical (a + 2) hH
  have hat : a ∈ Ioo (0 : ℝ) (a + 2) := ⟨ha0, by linarith⟩
  let U : ℝ → ℝ := liftRepr (u a)
  have hU_cont : Continuous U := by
    apply liftRepr_continuous
    exact ((hsol.regularity.2.2.2.2.1 a hat).1.1).continuousOn
  have hU_eq : ∀ y ∈ Icc (0 : ℝ) 1,
      U y = intervalDomainLift (u a) y := by
    intro y hy
    exact liftRepr_eq_on_Icc hy
  have hU_nonneg : ∀ y, 0 ≤ U y := by
    intro y
    dsimp [U, liftRepr]
    rw [intervalDomainLift, dif_pos (clamp01_mem y)]
    exact (hsol.u_pos' hat.1 hat.2).le
  have hU_le : ∀ y, U y ≤ M := by
    intro y
    dsimp [U, liftRepr]
    exact le_trans (le_abs_self _) (abs_lift_le_supNorm_M hsol hat
      (clamp01_mem y))
  have hU_mass : (∫ y in (0 : ℝ)..1, U y) = uStar := by
    calc ∫ y in (0 : ℝ)..1, U y
        = ∫ y in (0 : ℝ)..1, intervalDomainLift (u a) y := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
          exact hU_eq y hy
      _ = intervalDomainM.integral (u a) := rfl
      _ = uStar := by simpa [intervalDomainM] using hmass a ha0
  have hU_abs : ∀ y, |U y| ≤ M := by
    intro y
    rw [abs_of_nonneg (hU_nonneg y)]
    exact hU_le y
  let f : ℝ → ℝ := fun y => M - U y
  have hf_cont : Continuous f := continuous_const.sub hU_cont
  have hf_nonneg : ∀ y, 0 ≤ f y := fun y => sub_nonneg.mpr (hU_le y)
  have hf_bound : ∀ y, |f y| ≤ M := by
    intro y
    rw [abs_of_nonneg (hf_nonneg y)]
    dsimp [f]
    linarith [hU_nonneg y]
  have hU_int : Integrable U (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound
      hU_cont.aestronglyMeasurable hU_abs
  have hf_int : Integrable f (intervalMeasure 1) :=
    (integrable_const M).sub hU_int
  have hUint : (∫ y, U y ∂(intervalMeasure 1)) = uStar := by
    rw [IntervalConjugateKernelIBP.intervalMeasure_one_integral_eq_intervalIntegral]
    calc
      (∫ y in (0 : ℝ)..1, U y) =
          ∫ y in (0 : ℝ)..1, intervalDomainLift (u a) y := by
            apply intervalIntegral.integral_congr
            intro y hy
            rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
            exact hU_eq y hy
      _ = intervalDomainM.integral (u a) := rfl
      _ = uStar := by simpa [intervalDomainM] using hmass a ha0
  have hf_mass : (∫ y, f y ∂(intervalMeasure 1)) = M - uStar := by
    dsimp [f]
    rw [integral_sub (integrable_const M) hU_int,
      intervalMeasure_integral_const (L := (1 : ℝ)) (c := M) (by norm_num),
      hUint]
    ring
  have hpoint : ∀ x : intervalDomainPoint,
      u (a + 1) x ≤ M - unitWindowHeatKernelFloor * d := by
    intro x
    have hfloor := unitWindowHeatKernelFloor_mul_integral_le_semigroup
      (t := (1 : ℝ)) (x := x.1)
      ⟨le_rfl, by norm_num⟩ x.2 hf_int hf_cont.aestronglyMeasurable
      (fun y _hy => hf_nonneg y) hf_bound
    rw [hf_mass] at hfloor
    have hK := intervalNeumannFullKernel_integrable
      (by norm_num : (0 : ℝ) < 1) x.1
    have hKM : Integrable
        (fun y => intervalNeumannFullKernel 1 x.1 y * M)
        (intervalMeasure 1) := hK.mul_const M
    have hKU : Integrable
        (fun y => intervalNeumannFullKernel 1 x.1 y * U y)
        (intervalMeasure 1) := by
      have hmul := hK.bdd_mul hU_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact hU_abs y)
      simpa [mul_comm] using hmul
    have hlin :=
      ShenWork.IntervalGradDuhamelBound.intervalFullSemigroupOperator_sub
        hKM hKU
    have hSU : intervalFullSemigroupOperator 1 U x.1 = u (a + 1) x := by
      calc
        intervalFullSemigroupOperator 1 U x.1 =
            intervalFullSemigroupOperator 1 (intervalDomainLift (u a)) x.1 :=
          ShenWork.IntervalSemigroupC1ApproxIdentity.intervalFullSemigroupOperator_congr_on_Icc
            hU_eq 1 x.1
        _ = u (a + 1) x :=
          (intervalDomainM_minimal_chiZero_restart_heat
            p ha hb hχ huv ha0 x).symm
    have hSf : intervalFullSemigroupOperator 1 f x.1 =
        M - u (a + 1) x := by
      dsimp [f]
      rw [hlin, intervalFullSemigroupOperator_const (by norm_num) M, hSU]
    rw [hSf] at hfloor
    have hgap' : d ≤ M - uStar := by
      dsimp [M]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hgap'
      unitWindowHeatKernelFloor_pos.le
    nlinarith
  apply intervalDomain_supNorm_le_of_pointwise_abs_le
  intro x
  rw [abs_of_nonneg ((hsol.u_pos' (by linarith) (by linarith)).le)]
  exact hpoint x

-- ============================================================
-- Eventual entry for χ₀ = 0 (general-m minimal)
-- ============================================================

private theorem intervalDomainM_minimal_chiZero_eventually_supNorm_le_mass_add
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ = 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {uStar d : ℝ} (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar) :
    ∀ᶠ t in atTop,
      intervalDomainM.supNorm (u t) ≤ uStar + d := by
  let B : ℝ := intervalDomainM.supNorm (u 1)
  let ρ : ℝ := unitWindowHeatKernelFloor
  have hρ : 0 < ρ := unitWindowHeatKernelFloor_pos
  have hρd : 0 < ρ * d := mul_pos hρ hd
  have hmassLower : ∀ t, 0 < t → uStar ≤ intervalDomainM.supNorm (u t) := by
    intro t ht
    have hH : 0 < t + 1 := by linarith
    have hsol := huv.classical (t + 1) hH
    have hle := intervalDomainM_classicalSolution_mass_le_supNorm hsol
      (⟨ht, by linarith⟩ : t ∈ Ioo (0 : ℝ) (t + 1))
    have hm_t : intervalDomainM.integral (u t) = uStar := by
      simpa [intervalDomainM] using hmass t ht
    simpa [hm_t] using hle
  have hentry : ∃ n : ℕ,
      intervalDomainM.supNorm (u (1 + (n : ℝ))) ≤ uStar + d := by
    by_contra hnone
    have hnone' : ∀ n : ℕ, uStar + d <
        intervalDomainM.supNorm (u (1 + (n : ℝ))) := by
      intro n
      exact lt_of_not_ge (fun hle => hnone ⟨n, hle⟩)
    have hind : ∀ n : ℕ,
        intervalDomainM.supNorm (u (1 + (n : ℝ))) ≤
          B - (n : ℝ) * ρ * d := by
      intro n
      induction n with
      | zero => simp [B]
      | succ n ih =>
          have hgap : uStar + d ≤
              intervalDomainM.supNorm (u (1 + (n : ℝ))) :=
            (hnone' n).le
          have hdrop := intervalDomainM_minimal_chiZero_supNorm_unit_drop
            p ha hb hχ huv (a := 1 + (n : ℝ))
              (by positivity) huStar hd hmass hgap
          have hdrop' :
              intervalDomainM.supNorm (u (1 + ((n + 1 : ℕ) : ℝ))) ≤
                intervalDomainM.supNorm (u (1 + (n : ℝ))) - ρ * d := by
            simpa [ρ, Nat.cast_add, Nat.cast_one, add_assoc] using hdrop
          calc
            intervalDomainM.supNorm (u (1 + ((n + 1 : ℕ) : ℝ))) ≤
                intervalDomainM.supNorm (u (1 + (n : ℝ))) - ρ * d := hdrop'
            _ ≤ (B - (n : ℝ) * ρ * d) - ρ * d :=
              sub_le_sub_right ih _
            _ = B - ((n + 1 : ℕ) : ℝ) * ρ * d := by
              norm_num [Nat.cast_add, Nat.cast_one]
              ring
    obtain ⟨n, hn⟩ := exists_nat_gt ((B - uStar) / (ρ * d))
    have hn' : B - uStar < (n : ℝ) * (ρ * d) :=
      (div_lt_iff₀ hρd).mp hn
    have hlower := hmassLower (1 + (n : ℝ)) (by positivity)
    have hupper := hind n
    nlinarith
  obtain ⟨n, hn⟩ := hentry
  refine eventually_atTop.2 ⟨1 + (n : ℝ), ?_⟩
  intro t ht
  exact (intervalDomainM_minimal_supNorm_antitone_positiveTimes
    p ha hb hχ.le huv (by positivity) ht).trans hn

-- ============================================================
-- Uniform convergence from eventual max (general-m)
-- ============================================================

/-- Static tail rigidity upgrades convergence of the spatial maximum to
uniform convergence whenever the physical mass is fixed. Uses Hölder-1/2
regularity for general `m` (no `hm : p.m = 1` needed). -/
private theorem intervalDomainM_minimal_uniform_u_converges_of_eventual_max
    (p : CM2Params)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar)
    (hmax : ∀ d, 0 < d → ∀ᶠ t in atTop,
      intervalDomainM.supNorm (u t) ≤ uStar + d) :
    UniformConvergesInSup intervalDomainM u uStar := by
  obtain ⟨Thol, _Mhol, G, hThol, _hMhol, hG, _hsupHol, hhol⟩ :=
    intervalDomainM_globalBounded_eventual_holder p huv
  unfold UniformConvergesInSup
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hstatic⟩ :=
    intervalDomainM_uniform_close_of_mass_and_upper_of_holder
      huStar hG (by linarith : 0 < ε / 2)
  have hmaxδ := hmax δ hδ
  apply eventually_atTop.1
  filter_upwards [hmaxδ,
    eventually_ge_atTop (max Thol (1 : ℝ))] with t hmax_t ht
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one
    ((le_max_right Thol (1 : ℝ)).trans ht)
  have hH : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) hH
  have htMem : t ∈ Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
  let ft : C(intervalDomainPoint, ℝ) :=
    ⟨u t, IntervalDomainM.solutionSlice_continuous hsol htMem⟩
  have hft_nonneg : ∀ x, 0 ≤ ft x := fun _x =>
    (hsol.u_pos' htMem.1 htMem.2).le
  have hft_upper : ∀ x, ft x ≤ uStar + δ := by
    intro x
    have habs := abs_lift_le_supNorm_M hsol htMem x.2
    have hpoint : ft x ≤ intervalDomainM.supNorm (u t) :=
      le_trans (le_abs_self (ft x)) (by
        simpa [ft, intervalDomainLift, x.2] using habs)
    exact hpoint.trans hmax_t
  have hft_mass : uStar - δ ≤ intervalDomain.integral ft := by
    have hm_t : intervalDomainM.integral (u t) = uStar := by
      simpa [intervalDomainM] using hmass t htPos
    have : intervalDomain.integral ft = uStar := hm_t
    linarith [hδ.le]
  have hft_hol : ∀ x y, |ft x - ft y| ≤ G * |x.1 - y.1| ^ ((1 : ℝ) / 2) := by
    intro x y
    exact hhol t ((le_max_left Thol (1 : ℝ)).trans ht) x y
  have hpointClose : ∀ x, |ft x - uStar| < ε / 2 :=
    hstatic ft hft_nonneg hft_upper hft_mass hft_hol
  have hsup_le : intervalDomainM.supNorm (fun x => u t x - uStar) ≤ ε / 2 := by
    show intervalDomain.supNorm (fun x => u t x - uStar) ≤ ε / 2
    exact intervalDomain_supNorm_le_of_pointwise_abs_le
      (fun x => (hpointClose x).le)
  have hsup_nonneg : 0 ≤
      intervalDomainM.supNorm (fun x => u t x - uStar) := by
    show 0 ≤ intervalDomain.supNorm (fun x => u t x - uStar)
    exact intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded
      (fun x => (hpointClose x).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nonneg]
  linarith

-- ============================================================
-- Combined convergence: χ₀ ≤ 0 (general-m)
-- ============================================================

/-- Uniform convergence of the population to its physical mass
for the faithful general-`m` minimal model with χ₀ ≤ 0. -/
theorem intervalDomainM_minimal_chiNonpos_uniform_u_converges
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ ≤ 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomainM p u v)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar) :
    UniformConvergesInSup intervalDomainM u uStar := by
  have heventualMax : ∀ d, 0 < d → ∀ᶠ t in atTop,
      intervalDomainM.supNorm (u t) ≤ uStar + d := by
    intro d hd
    rcases lt_or_eq_of_le hχ with hneg | hzero
    · exact intervalDomainM_minimal_chiNeg_eventually_supNorm_le_mass_add
        p ha hb hneg huv huStar hd hmass
    · exact intervalDomainM_minimal_chiZero_eventually_supNorm_le_mass_add
        p ha hb hzero huv huStar hd hmass
  exact intervalDomainM_minimal_uniform_u_converges_of_eventual_max
    p huv huStar hmass heventualMax

#print axioms intervalDomainM_solution_signalGapConstant_le
#print axioms intervalDomainMMinimalMaxDissipationConstant_pos
#print axioms intervalDomainM_minimal_argmax_uniform_strict_slope
#print axioms intervalDomainM_minimal_supNorm_antitone_positiveTimes
#print axioms intervalDomainM_minimal_chiNeg_supNorm_decay_if_above_mass_add
#print axioms intervalDomainM_minimal_chiNeg_eventually_supNorm_le_mass_add
#print axioms intervalDomainM_minimal_chiNonpos_uniform_u_converges

end

end ShenWork.Paper3
