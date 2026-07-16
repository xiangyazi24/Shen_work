import ShenWork.Paper3.IntervalDomainResolverOscillation
import ShenWork.Paper2.IntervalDomainResolverStrictPos
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
import ShenWork.Paper2.IntervalDomainMRestartSources
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms
import ShenWork.Paper2.IntervalDomainMEllipticResolverAgreementIcc
import ShenWork.Paper2.IntervalDomainMEllipticResolverAgreement

/-!
# Concrete signal bounds for the faithful general-`m` interval rectangle argument

This is the `intervalDomainM` counterpart of `IntervalDomainRectangleSignalBounds`.
The elliptic signal equation `-v'' + μ v = ν u^γ` with Neumann boundary is
identical for both interval models — only the parabolic `u`-flux differs — so
the proof is the legacy one with the solution predicate retyped to
`intervalDomainM` and the two resolver-agreement facts replaced by their
faithful `…M` versions.  No `p.m = 1` hypothesis appears.
-/

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.PDE ShenWork.Paper2
open ShenWork.IntervalResolverPositivity
open ShenWork.IntervalDomainResolverStrictPos
open ShenWork.IntervalResolverWeakBounds
open ShenWork.MinPersistenceAtoms
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalDomainLogisticWeakH2Adapter
open ShenWork.IntervalPicardLimitCoeffConv (cosineCoeffs_sub_eq)

namespace ShenWork.Paper3

noncomputable section

/-- A positive classical slice of the faithful general-`m` equation in the
population box `[uMin,uMax]` has the corresponding exact elliptic order bounds
and the concrete power-oscillation gradient bound. -/
theorem intervalDomainM_solution_signal_bounds_of_population_box
    (p : CM2Params) {T t uMin uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1, uMin ≤ intervalDomainLift (u t) y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1, intervalDomainLift (u t) y ≤ uMax) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      p.ν * uMin ^ p.γ / p.μ ≤ intervalDomainLift (v t) x ∧
      intervalDomainLift (v t) x ≤ p.ν * uMax ^ p.γ / p.μ ∧
      |deriv (intervalDomainLift (v t)) x| ≤
        unitIntervalResolverGradientOscillationConstant p *
          (p.ν * (uMax ^ p.γ - uMin ^ p.γ)) := by
  obtain ⟨hC2, _, _, hNeu, hClosed, _, _⟩ := hsol.regularity
  have hUcont : ContinuousOn (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    (hClosed t ht).1.1.continuousOn
  have hVcont : ContinuousOn (intervalDomainLift (v t)) (Icc (0 : ℝ) 1) :=
    (hClosed t ht).2.1.continuousOn
  have hVc2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Ioo (0 : ℝ) 1) :=
    (hC2 t ht).2
  have huMax : 0 ≤ uMax := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    exact huMin.trans ((hlo 0 h0).trans (hhi 0 h0))
  -- A globally continuous clamped representative is used only to invoke the
  -- already proved positivity of the Neumann resolvent.
  let U : ℝ → ℝ := fun y => intervalDomainLift (u t) (clamp01 y)
  let f : ℝ → ℝ := fun y => p.ν * U y ^ p.γ
  let c0 : ℝ := p.ν * uMin ^ p.γ
  have hUcont_global : Continuous U := by
    refine continuousOn_univ.mp ?_
    exact hUcont.comp clamp01_continuous.continuousOn
      (fun y _ => clamp01_mem y)
  have hf_cont : Continuous f := by
    exact continuous_const.mul
      ((Real.continuous_rpow_const p.hγ.le).comp hUcont_global)
  have hf_ge : ∀ y, c0 ≤ f y := by
    intro y
    have hy := clamp01_mem y
    have hUy : 0 ≤ U y := huMin.trans (hlo (clamp01 y) hy)
    have hp := Real.rpow_le_rpow huMin (hlo (clamp01 y) hy) p.hγ.le
    exact mul_le_mul_of_nonneg_left hp p.hν.le
  have hf_coeff : ∀ k,
      cosineCoeffs f k =
        (intervalNeumannResolverSourceCoeff p (u t) k).re := by
    intro k
    calc
      cosineCoeffs f k =
          cosineCoeffs
            (fun y => p.ν * intervalDomainLift (u t) y ^ p.γ) k := by
              apply cosineCoeffs_congr_on_Icc
              intro y hy
              simp only [f, U, clamp01_eq_self hy]
      _ = (intervalNeumannResolverSourceCoeff p (u t) k).re := by
        symm
        exact resolverSourceCoeff_re_eq_cosineCoeffs p (u t) k
  have hf_sq : Summable (fun k : ℕ => (cosineCoeffs f k) ^ 2) := by
    have hbase : Summable (fun k : ℕ =>
        ((intervalNeumannResolverSourceCoeff p (u t) k).re) ^ 2) := by
      simpa [intervalNeumannResolverSourceCoeff_zero, sub_zero] using
        resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
    exact hbase.congr (fun k => by rw [hf_coeff k])
  let u0 : intervalDomainPoint → ℝ := fun _ => uMin
  have hU0cont : ContinuousOn (intervalDomainLift u0) (Icc (0 : ℝ) 1) := by
    refine (continuousOn_const : ContinuousOn (fun _ : ℝ => uMin)
      (Icc (0 : ℝ) 1)).congr ?_
    intro y hy
    simp [u0, intervalDomainLift, hy]
  have hc0_coeff : ∀ k,
      cosineCoeffs (fun _ : ℝ => c0) k =
        (intervalNeumannResolverSourceCoeff p u0 k).re := by
    intro k
    calc
      cosineCoeffs (fun _ : ℝ => c0) k =
          cosineCoeffs
            (fun y => p.ν * intervalDomainLift u0 y ^ p.γ) k := by
              apply cosineCoeffs_congr_on_Icc
              intro y hy
              simp [c0, u0, intervalDomainLift, hy]
      _ = (intervalNeumannResolverSourceCoeff p u0 k).re := by
        symm
        exact resolverSourceCoeff_re_eq_cosineCoeffs p u0 k
  have hf_sub_coeff : ∀ k,
      cosineCoeffs (fun y => f y - c0) k =
        (intervalNeumannResolverSourceCoeff p (u t) k).re -
          (intervalNeumannResolverSourceCoeff p u0 k).re := by
    intro k
    rw [cosineCoeffs_sub_eq hf_cont.continuousOn continuousOn_const,
      hf_coeff k, hc0_coeff k]
  have hf_sub_sq : Summable
      (fun k : ℕ => (cosineCoeffs (fun y => f y - c0) k) ^ 2) := by
    have h := resolverSourceCoeff_diff_re_sq_summable_of_continuousOn
      p hUcont hU0cont
    exact h.congr (fun k => by rw [hf_sub_coeff k]; simp)
  have hRlower : ∀ xp : intervalDomainPoint,
      c0 / p.μ ≤ intervalNeumannResolverR p (u t) xp := by
    intro xp
    exact intervalNeumannResolverR_ge_of_source_ge
      hf_cont hf_ge hf_coeff hf_sq hf_sub_sq xp
  -- The upper order bound follows directly from the closed-interval elliptic
  -- maximum principle applied to the physical signal.
  let B : ℝ := p.ν * uMax ^ p.γ
  have hB : 0 ≤ B := mul_nonneg p.hν.le (Real.rpow_nonneg huMax _)
  have hVd1 : ∀ y ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (intervalDomainLift (v t)) y := by
    intro y hy
    exact (hVc2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hy)
  have hVd2 : ∀ y ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (deriv (intervalDomainLift (v t))) y := by
    intro y hy
    exact ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hVc2 hy).2).differentiableAt
  have hVPDE : ∀ y ∈ Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) y =
        p.μ * intervalDomainLift (v t) y -
          p.ν * intervalDomainLift (u t) y ^ p.γ := by
    intro y hy
    let yp : intervalDomainPoint := ⟨y, Ioo_subset_Icc_self hy⟩
    have hpde := hsol.pde_v ht.1 ht.2 (x := yp) hy
    have hu : intervalDomainLift (u t) y = u t yp := by
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hy)]
    have hv : intervalDomainLift (v t) y = v t yp := by
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hy)]
    have hlap : intervalDomainM.laplacian (v t) yp =
        deriv (deriv (intervalDomainLift (v t))) y := rfl
    rw [hlap, ← hu, ← hv] at hpde
    linarith
  have hVSrc : ∀ y ∈ Ioo (0 : ℝ) 1,
      |p.ν * intervalDomainLift (u t) y ^ p.γ| ≤ B := by
    intro y hy
    have hyc := Ioo_subset_Icc_self hy
    have hUy : 0 ≤ intervalDomainLift (u t) y := huMin.trans (hlo y hyc)
    have hp := Real.rpow_le_rpow hUy (hhi y hyc) p.hγ.le
    have hnn : 0 ≤ p.ν * intervalDomainLift (u t) y ^ p.γ :=
      mul_nonneg p.hν.le (Real.rpow_nonneg hUy _)
    rw [abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left hp p.hν.le
  have hVupper := elliptic_sup_bound (w := intervalDomainLift (v t))
    (Src := fun y => p.ν * intervalDomainLift (u t) y ^ p.γ)
    (μ := p.μ) (B := B) p.hμ hVcont hVd1 hVd2 hVPDE hVSrc
    (hNeu t ht).2.1 (hNeu t ht).2.2
  intro x hx
  have hvR :=
    ShenWork.Paper2.IntervalDomainM.solution_v_eq_resolver_pointwise_IccM
      hsol ht hx
  have hlower : p.ν * uMin ^ p.γ / p.μ ≤
      intervalDomainLift (v t) x := by
    change c0 / p.μ ≤ intervalDomainLift (v t) x
    rw [← hvR]
    exact hRlower ⟨x, hx⟩
  have hupper : intervalDomainLift (v t) x ≤
      p.ν * uMax ^ p.γ / p.μ := by
    change intervalDomainLift (v t) x ≤ B / p.μ
    exact hVupper x hx
  have hgradR := intervalDomain_resolverGradient_abs_le_power_oscillation
    p huMin hUcont hlo hhi hx
  have hgradEq :=
    ShenWork.Paper2.IntervalDomainM.solution_lift_v_deriv_eq_resolverGrad_IccM
      hsol ht hx
  rw [hgradEq]
  exact ⟨hlower, hupper, hgradR⟩

#print axioms intervalDomainM_solution_signal_bounds_of_population_box

end

end ShenWork.Paper3
