import ShenWork.Paper2.IntervalDomainMEllipticResolverAgreement
import ShenWork.PDE.IntervalProfileBoundaryRegularity

/-!
# Closed-interval elliptic resolver agreement for the faithful domain

The faithful general-`m` elliptic identification is first obtained on the open
spatial interval.  Both the resolver cosine series and the classical chemical
slice are continuous on the closed unit interval, so density of `(0,1)` in
`[0,1]` supplies the two endpoint values.
-/

open Set Topology
open scoped Topology
open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.IntervalResolverWeakBounds

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

/-- The faithful chemical slice agrees with its Neumann resolver on the closed
unit interval. -/
theorem solution_v_eq_resolver_pointwise_IccM
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t x : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalNeumannResolverR p (u t) ⟨x, hx⟩ =
      intervalDomainLift (v t) x := by
  classical
  let R : ℝ → ℝ := fun z =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p (u t) k).re *
      unitIntervalCosineMode k z
  have hUcont : ContinuousOn (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hRcont : Continuous R := by
    have hsrcL2 : Summable fun k : ℕ =>
        ((intervalNeumannResolverSourceCoeff p (u t) k).re) ^ 2 := by
      simpa [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero] using
        resolverSourceCoeff_re_sq_summable_of_continuousOn p hUcont
    have hseries0 := resolver_cosineSeries_summable_of_sourceL2 p hsrcL2 0
    have habs : Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (u t) k).re| := by
      simpa [unitIntervalCosineMode, Real.norm_eq_abs] using hseries0.norm
    refine continuous_tsum (fun k => ?_) habs (fun k z => ?_)
    · exact continuous_const.mul
        (Real.continuous_cos.comp (by fun_prop))
    · rw [Real.norm_eq_abs, abs_mul]
      have hcos : |unitIntervalCosineMode k z| ≤ 1 :=
        Real.abs_cos_le_one _
      exact (mul_le_mul_of_nonneg_left hcos (abs_nonneg _)).trans_eq
        (mul_one _)
  have hVcont : ContinuousOn (intervalDomainLift (v t)) (Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hIoo : EqOn R (intervalDomainLift (v t)) (Ioo (0 : ℝ) 1) := by
    intro y hy
    have hagree := solution_v_eq_resolver_pointwiseM hsol ht hy
    simpa [R, intervalNeumannResolverR] using hagree
  have hIcc : EqOn R (intervalDomainLift (v t)) (Icc (0 : ℝ) 1) :=
    ShenWork.IntervalFullKernelRegularity.eqOn_Icc_of_eqOn_Ioo_of_continuousOn
      hRcont.continuousOn hVcont hIoo
  simpa [R, intervalNeumannResolverR] using hIcc hx

#print axioms solution_v_eq_resolver_pointwise_IccM

end ShenWork.Paper2.IntervalDomainM
