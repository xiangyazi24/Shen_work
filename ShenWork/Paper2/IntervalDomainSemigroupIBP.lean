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

/-- **L2 energy differential inequality for a semigroup-profile solution.**
When the slice `u t` is a full-kernel semigroup profile, the `hIBP` frontier is
supplied by `intervalDomain_spatial_IBP_of_semigroup` (T5-e, regularity derived,
not assumed) and the Neumann frontier `hNeuR`/`hNeuL` by the genuine solution's
`hsol.neumann` (T3).  The energy inequality

  `E'(t) + dissipation ≤ χ·(ε·gradDiss + C·∫u^{2+ρ}) + logistic`

then holds conditional only on the chain-rule `hL2Time`, the PDE substitution
`hPDEIntegral`, and the cross-diffusion controls — the spatial Neumann IBP and the
`C^{2,1}`-up-to-boundary regularity it needs are now genuine analytic content. -/
theorem intervalDomain_l2_half_energy_inequality_of_semigroup
    {params : CM2Params} {T rho eps chiBound t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (heps : 0 < eps) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hL2Time :
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
        intervalDomain.integral (intervalDomainL2TimeTerm u t))
    (hPDEIntegral :
      intervalDomain.integral (intervalDomainL2TimeTerm u t) =
        intervalDomainL2DiffusionIntegral u t -
          params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
          intervalDomainL2LogisticIntegral params u t)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    (hw : Set.EqOn (intervalDomainLift (u t))
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)))
    (hCrossControl :
      -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t)) :
    ∃ Ceps,
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
          intervalDomainL2DiffusionDissipation u t ≤
        chiBound *
            (eps * intervalDomainLpWeightedGradientDissipation 2 u t +
              Ceps *
                intervalDomain.integral (fun x => (u t x) ^ (2 + rho))) +
          intervalDomainL2LogisticIntegral params u t := by
  have hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_rightEndpoint_mem_boundary).1
  have hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_leftEndpoint_mem_boundary).1
  -- The spatial Neumann IBP for the semigroup slice IS the L2 `hIBP` frontier.
  have hIBP :
      intervalDomainL2DiffusionIntegral u t =
        intervalDomainNeumannBoundaryTerm (u t) (u t) -
          intervalDomainL2DiffusionDissipation u t :=
    intervalDomain_spatial_IBP_of_semigroup ht0 hf hM hw hkernel hNeuR hNeuL
  exact intervalDomain_l2_half_energy_cross_bootstrap_inequality_of_frontiers
    heps hchiBound ht0 htT hcross hL2Time hPDEIntegral hIBP hNeuR hNeuL hCrossControl

end ShenWork.Paper2.IntervalDomainEnergyStep
