/- Exact action of the interval elliptic resolver on a constant source. -/
import ShenWork.Paper3.IntervalDomainSignalDecomposition
import ShenWork.Paper2.IntervalDomainResolverStrictPos

namespace ShenWork.Paper3

open ShenWork.PDE
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalDomainResolverStrictPos

noncomputable section

lemma intervalNeumannResolverSourceCoeff_const_re
    (p : CM2Params) (uStar : ℝ) (k : ℕ) :
    (intervalNeumannResolverSourceCoeff p (fun _ => uStar) k).re =
      cosineCoeffs (fun _ : ℝ => p.ν * uStar ^ p.γ) k := by
  change cosineCoeffs
      (fun x => p.ν * intervalDomainLift
        (fun _ : intervalDomainPoint => uStar) x ^ p.γ) k = _
  exact paper3_cosineCoeffs_congr_on_Icc
    (fun x hx => by simp [intervalDomainLift, hx]) k

/-- The Neumann resolver of the constant density `uStar` is the constant
`nu*uStar^gamma/mu`. -/
theorem intervalNeumannResolverR_const
    (p : CM2Params) (uStar : ℝ) (x : intervalDomainPoint) :
    intervalNeumannResolverR p (fun _ => uStar) x =
      p.ν * uStar ^ p.γ / p.μ := by
  rw [resolverR_apply_eq]
  have hterm : ∀ k : ℕ,
      (intervalNeumannResolverCoeff p (fun _ => uStar) k).re *
          Real.cos ((k : ℝ) * Real.pi * x.1) =
        cosineCoeffs (fun _ : ℝ => p.ν * uStar ^ p.γ) k *
          unitIntervalCosineMode k x.1 /
            (p.μ + unitIntervalCosineEigenvalue k) := by
    intro k
    rw [resolverCoeff_re_eq,
      intervalNeumannResolverSourceCoeff_const_re]
    simp only [unitIntervalCosineMode, unitIntervalCosineEigenvalue,
      unitIntervalNeumannSpectrum]
    ring
  rw [tsum_congr hterm]
  exact const_reconstruction p (p.ν * uStar ^ p.γ) x.1

/-- The equilibrium elliptic relation identifies the constant resolver with
the prescribed chemical equilibrium. -/
theorem intervalNeumannResolverR_const_eq_vStar
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (x : intervalDomainPoint) :
    intervalNeumannResolverR p (fun _ => uStar) x = vStar := by
  rw [intervalNeumannResolverR_const]
  rw [div_eq_iff p.hμ.ne']
  simpa [mul_comm] using heq.elliptic_relation.symm

/-- The gradient reconstruction of a constant source is identically zero. -/
theorem intervalNeumannResolverRGrad_const
    (p : CM2Params) (uStar : ℝ) (x : intervalDomainPoint) :
    intervalNeumannResolverRGrad p (fun _ => uStar) x = 0 := by
  rw [resolverRGrad_apply_eq]
  have hzero :
      (fun k : ℕ =>
        (intervalNeumannResolverCoeff p (fun _ => uStar) k).re *
          (-((k : ℝ) * Real.pi) *
            Real.sin ((k : ℝ) * Real.pi * x.1))) = fun _ => 0 := by
    funext k
    rw [resolverCoeff_re_eq,
      intervalNeumannResolverSourceCoeff_const_re,
      cosineCoeffs_const]
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  rw [hzero, tsum_zero]

#print axioms intervalNeumannResolverR_const
#print axioms intervalNeumannResolverR_const_eq_vStar
#print axioms intervalNeumannResolverRGrad_const

end

end ShenWork.Paper3
