/-
  ShenWork/Paper2/IntervalDomainSemigroupIBP.lean

  **T5 ⋈ T4 — the spatial Neumann IBP, with its regularity package discharged
  from the full-kernel semigroup representation.**

  Combines:
  * T4-a `intervalDomain_spatial_integrationByParts_identity` — the genuine spatial
    integration-by-parts identity, conditional on a `C²`-up-to-boundary regularity
    package; and
  * T5-a..d (`IntervalFullKernelBoundaryRegularity`) — that package, *proved* for a
    full-Neumann-kernel semigroup profile slice `lift w = S_t f` on `[0,1]`.

  The result `intervalDomain_spatial_IBP_of_semigroup` discharges the `hIBP`
  frontier of the energy chain for any slice that is a semigroup profile, taking
  only the spectral data (`Continuous f`, bounded cosine coefficients, the Poisson
  kernel identity) and the genuine one-sided Neumann condition (T3) — **no
  regularity hypotheses**.  The `C^{2,1}`-up-to-boundary regularity is now genuine
  analytic content, not an assumption.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity
import ShenWork.Paper2.IntervalDomainNeumannIBP

open MeasureTheory Set
open scoped Topology

namespace ShenWork.Paper2.IntervalDomainEnergyStep

open ShenWork.IntervalDomain ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelRegularity

/-- **Spatial Neumann integration by parts for a semigroup-profile slice.**
If `w`'s lift agrees on `[0,1]` with the full-kernel Neumann semigroup `S_t f` of a
continuous bounded-coefficient source `f`, and `w` satisfies the genuine one-sided
Neumann condition at both endpoints (T3), then the spatial IBP identity holds:

  `∫₀¹ w·Δw = intervalDomainNeumannBoundaryTerm w w − ∫₀¹ w'·w'`.

This discharges the `hIBP` frontier (here for `test = f = w`) with the
`C²`-up-to-boundary regularity package *proved* from the semigroup representation
(T5-a..d), not assumed. -/
theorem intervalDomain_spatial_IBP_of_semigroup
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {w : intervalDomainPoint → ℝ}
    (hw : Set.EqOn (intervalDomainLift w)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)))
    (hNeuR : intervalDomain.normalDeriv w intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv w intervalDomainLeftEndpoint = 0) :
    intervalDomain.integral (fun x => w x * intervalDomain.laplacian w x) =
      intervalDomainNeumannBoundaryTerm w w -
        intervalDomainDerivativePairIntegral w w := by
  refine intervalDomain_spatial_integrationByParts_identity w w
    (intervalDomainLift_continuousOn_Icc_of_semigroup ht hf hM hw hkernel)
    (deriv_intervalDomainLift_continuousOn_Icc_of_semigroup ht hf hM hw hkernel)
    (fun x hx => intervalDomainLift_hasDerivWithinAt_Ioi_of_semigroup ht hf hM hw hkernel hx)
    (fun x hx => deriv_intervalDomainLift_hasDerivWithinAt_Ioi_of_semigroup ht hf hM hw hkernel hx)
    (intervalIntegrable_deriv_intervalDomainLift_of_semigroup ht hf hM hw hkernel)
    (intervalIntegrable_deriv2_intervalDomainLift_of_semigroup ht hf hM hw hkernel)
    ?_ ?_
  · rw [deriv_intervalDomainLift_eq_zero_at_one, hNeuR]
  · rw [deriv_intervalDomainLift_eq_zero_at_zero, hNeuL]

end ShenWork.Paper2.IntervalDomainEnergyStep
