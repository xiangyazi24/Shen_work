import ShenWork.Paper3.IntervalDomainPowerSourceMassGap
import ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
import ShenWork.Paper2.IntervalDomainLogisticWeakH2Adapter
import ShenWork.Paper2.IntervalConjugateKernelIBP

/-!
# Quantitative elliptic gap at a spatial maximum

For a positive classical slice of fixed mass `uStar`, if an upper bound `M`
lies at least `d` above `uStar`, then the elliptic signal satisfies

`nu * M^gamma / mu - v(x) >= q(d) > 0`

uniformly on the closed interval.  This is the strict term retained by the
repulsive (`chi < 0`) maximum principle.  The proof is coefficient-level:
the source is `nu * (M^gamma - u^gamma)`, the preceding mass-gap theorem
gives it positive integral, and the quantitative resolver theorem turns that
mass into a pointwise gap.
-/

open Filter MeasureTheory Set Topology

noncomputable section

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

/-- Resolving the power-source deficit is exactly the constant resolver minus
the physical resolver. -/
theorem cosinePowerSourceDeficit_resolver_eq_const_sub
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {U : ℝ → ℝ} {M x : ℝ}
    (hU_cont : Continuous U)
    (hU_eq : ∀ y ∈ Icc (0 : ℝ) 1, U y = intervalDomainLift w y)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (∑' k, cosineCoeffs (fun y => p.ν * (M ^ p.γ - U y ^ p.γ)) k *
        unitIntervalCosineMode k x /
          (p.μ + unitIntervalCosineEigenvalue k)) =
      p.ν * M ^ p.γ / p.μ -
        intervalNeumannResolverR p w ⟨x, hx⟩ := by
  let source : ℝ → ℝ := fun y => p.ν * U y ^ p.γ
  let constSource : ℝ → ℝ := fun _y => p.ν * M ^ p.γ
  have hsource_cont : Continuous source := by
    dsimp [source]
    exact continuous_const.mul
      ((Real.continuous_rpow_const p.hγ.le).comp hU_cont)
  have hsource_coeff : ∀ k,
      cosineCoeffs source k =
        (intervalNeumannResolverSourceCoeff p w k).re := by
    intro k
    calc
      cosineCoeffs source k =
          cosineCoeffs
            (fun y => p.ν * intervalDomainLift w y ^ p.γ) k := by
              apply cosineCoeffs_congr_on_Icc
              intro y hy
              simp only [source]
              rw [hU_eq y hy]
      _ = (intervalNeumannResolverSourceCoeff p w k).re := by
        symm
        exact resolverSourceCoeff_re_eq_cosineCoeffs p w k
  have hdef_coeff : ∀ k,
      cosineCoeffs (fun y => p.ν * (M ^ p.γ - U y ^ p.γ)) k =
        cosineCoeffs constSource k - cosineCoeffs source k := by
    intro k
    calc
      cosineCoeffs (fun y => p.ν * (M ^ p.γ - U y ^ p.γ)) k =
          cosineCoeffs (fun y => constSource y - source y) k := by
            apply cosineCoeffs_congr_on_Icc
            intro y _hy
            dsimp [constSource, source]
            ring
      _ = cosineCoeffs constSource k - cosineCoeffs source k :=
        cosineCoeffs_sub_eq continuousOn_const hsource_cont.continuousOn k
  have hsource_sq : Summable (fun k : ℕ => (cosineCoeffs source k) ^ 2) :=
    cosineCoeffs_sq_summable_of_continuousOn hsource_cont.continuousOn
  have hconst_sq : Summable
      (fun k : ℕ => (cosineCoeffs constSource k) ^ 2) :=
    cosineCoeffs_sq_summable_of_continuousOn continuousOn_const
  have hsource_sum : Summable (fun k =>
      cosineCoeffs source k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k)) :=
    summable_resolverTarget (p := p) hsource_sq x
  have hconst_sum : Summable (fun k =>
      cosineCoeffs constSource k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k)) :=
    summable_resolverTarget (p := p) hconst_sq x
  have hsource_resolver :
      (∑' k, cosineCoeffs source k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k)) =
          intervalNeumannResolverR p w ⟨x, hx⟩ := by
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
  have hconst_resolver :
      (∑' k, cosineCoeffs constSource k * unitIntervalCosineMode k x /
        (p.μ + unitIntervalCosineEigenvalue k)) =
          p.ν * M ^ p.γ / p.μ := by
    simpa [constSource] using
      const_reconstruction p (p.ν * M ^ p.γ) x
  calc
    (∑' k, cosineCoeffs (fun y => p.ν * (M ^ p.γ - U y ^ p.γ)) k *
        unitIntervalCosineMode k x /
          (p.μ + unitIntervalCosineEigenvalue k)) =
        ∑' k, (cosineCoeffs constSource k * unitIntervalCosineMode k x /
            (p.μ + unitIntervalCosineEigenvalue k) -
          cosineCoeffs source k * unitIntervalCosineMode k x /
            (p.μ + unitIntervalCosineEigenvalue k)) := by
              apply tsum_congr
              intro k
              rw [hdef_coeff]
              ring
    _ = (∑' k, cosineCoeffs constSource k * unitIntervalCosineMode k x /
          (p.μ + unitIntervalCosineEigenvalue k)) -
        ∑' k, cosineCoeffs source k * unitIntervalCosineMode k x /
          (p.μ + unitIntervalCosineEigenvalue k) :=
      hconst_sum.tsum_sub hsource_sum
    _ = p.ν * M ^ p.γ / p.μ -
        intervalNeumannResolverR p w ⟨x, hx⟩ := by
      rw [hconst_resolver, hsource_resolver]

/-- Uniform pointwise signal-gap constant obtained from the power-source mass
gap and the positive Neumann resolver kernel. -/
def intervalDomainSignalGapConstant
    (p : CM2Params) (uStar d : ℝ) : ℝ :=
  unitIntervalResolverMassGapConstant p *
    intervalPowerSourceGapConstant p uStar d

theorem intervalDomainSignalGapConstant_pos
    (p : CM2Params) {uStar d : ℝ}
    (huStar : 0 < uStar) (hd : 0 < d) :
    0 < intervalDomainSignalGapConstant p uStar d := by
  exact mul_pos (unitIntervalResolverMassGapConstant_pos p)
    (intervalPowerSourceGapConstant_pos p huStar hd)

/-- Quantitative closed-interval signal gap for a positive classical slice,
with a constant independent of the actual maximum `M`. -/
theorem intervalDomain_solution_signalGapConstant_le
    (p : CM2Params) {T t uStar M d : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : intervalDomain.integral (u t) = uStar)
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
      _ = intervalDomain.integral (u t) := rfl
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
    IntervalChiNegH1PhysicalResolverSupProducer.solution_v_eq_resolver_pointwise_Icc
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

/-- Existential form of the same quantitative signal gap. -/
theorem intervalDomain_solution_signal_gap_of_mass_and_upper_gap
    (p : CM2Params) {T t uStar M d : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : intervalDomain.integral (u t) = uStar)
    (hupper : ∀ z : intervalDomainPoint, u t z ≤ M)
    (hMgap : uStar + d ≤ M) :
    ∃ q > 0, ∀ x ∈ Icc (0 : ℝ) 1,
      q ≤ p.ν * M ^ p.γ / p.μ - intervalDomainLift (v t) x := by
  exact ⟨intervalDomainSignalGapConstant p uStar d,
    intervalDomainSignalGapConstant_pos p huStar hd,
    intervalDomain_solution_signalGapConstant_le
      p hsol ht huStar hd hmass hupper hMgap⟩

#print axioms cosinePowerSourceDeficit_resolver_eq_const_sub
#print axioms intervalDomainSignalGapConstant_pos
#print axioms intervalDomain_solution_signalGapConstant_le
#print axioms intervalDomain_solution_signal_gap_of_mass_and_upper_gap

end ShenWork.Paper3
