/-
  ShenWork/Paper2/IntervalDomainProfileIBP.lean

  **T5 ⋈ T4 — spatial Neumann IBP for any `C²` Neumann profile, and the cosine
  heat-value instance (covers the Duhamel term and the full solution).**

  `intervalDomain_spatial_IBP_of_profile` discharges the `hIBP` frontier for any
  slice `w` whose lift agrees on `[0,1]` with a profile `S` that is `ContDiff ℝ 2`
  with `deriv S 0 = deriv S 1 = 0` (Neumann), using the abstract regularity package
  (`IntervalProfileBoundaryRegularity`) + the genuine IBP (T4-a).

  `intervalDomain_spatial_IBP_of_cosineProfile` specialises `S` to a bounded-coeff
  cosine heat value `Σ bₙ cos(nπ·)`.  Since the homogeneous semigroup, the Duhamel
  term (`IntervalDuhamelRegularity.DuhamelHeatValueRepresentation`), and hence the
  **full** full-kernel solution `u t = S_t u₀ + D_t` are all bounded-coeff cosine
  heat values on `[0,1]`, this discharges `hIBP` for the full solution from a single
  closed-boundary heat-value representation.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalProfileBoundaryRegularity
import ShenWork.Paper2.IntervalDomainNeumannIBP

open MeasureTheory Set
open scoped Topology

namespace ShenWork.Paper2.IntervalDomainEnergyStep

open ShenWork.IntervalDomain
open ShenWork.IntervalFullKernelRegularity
open ShenWork.IntervalDomainRegularityBootstrap

/-- **Spatial Neumann IBP for any `C²` Neumann profile slice.**  If `w`'s lift
agrees on `[0,1]` with a profile `S` that is `ContDiff ℝ 2` with `deriv S` vanishing
at both endpoints, and `w` satisfies the genuine one-sided Neumann condition (T3),
then the spatial IBP identity holds.  No regularity hypotheses on `w` itself —
the `C^{2,1}`-up-to-boundary package is proved from `S`. -/
theorem intervalDomain_spatial_IBP_of_profile
    {S : ℝ → ℝ} (hS : ContDiff ℝ 2 S) (hS_d0 : deriv S 0 = 0) (hS_d1 : deriv S 1 = 0)
    {w : intervalDomainPoint → ℝ}
    (hw : Set.EqOn (intervalDomainLift w) S (Set.Icc (0 : ℝ) 1))
    (hNeuR : intervalDomain.normalDeriv w intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv w intervalDomainLeftEndpoint = 0) :
    intervalDomain.integral (fun x => w x * intervalDomain.laplacian w x) =
      intervalDomainNeumannBoundaryTerm w w -
        intervalDomainDerivativePairIntegral w w := by
  refine intervalDomain_spatial_integrationByParts_identity w w
    (intervalDomainLift_profile_continuousOn_Icc hS hw)
    (deriv_intervalDomainLift_profile_continuousOn_Icc hS hS_d0 hS_d1 hw)
    (fun x hx => intervalDomainLift_profile_hasDerivWithinAt_Ioi hS hw hx)
    (fun x hx => deriv_intervalDomainLift_profile_hasDerivWithinAt_Ioi hS hw hx)
    (intervalIntegrable_deriv_intervalDomainLift_profile hS hS_d0 hS_d1 hw)
    (intervalIntegrable_deriv2_intervalDomainLift_profile hS hw)
    ?_ ?_
  · rw [deriv_intervalDomainLift_eq_zero_at_one, hNeuR]
  · rw [deriv_intervalDomainLift_eq_zero_at_zero, hNeuL]

/-- **Spatial Neumann IBP for a cosine heat-value profile slice.**  Specialises
`intervalDomain_spatial_IBP_of_profile` to `S = Σ bₙ cos(nπ·)` (a bounded-coeff
cosine heat value), the common spatial form of the homogeneous semigroup, the
Duhamel term, and the full full-kernel solution on `[0,1]`. -/
theorem intervalDomain_spatial_IBP_of_cosineProfile
    {τ : ℝ} (hτ : 0 < τ) {b : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |b n| ≤ M)
    {w : intervalDomainPoint → ℝ}
    (hw : Set.EqOn (intervalDomainLift w)
      (fun x => unitIntervalCosineHeatValue τ b x) (Set.Icc (0 : ℝ) 1))
    (hNeuR : intervalDomain.normalDeriv w intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv w intervalDomainLeftEndpoint = 0) :
    intervalDomain.integral (fun x => w x * intervalDomain.laplacian w x) =
      intervalDomainNeumannBoundaryTerm w w -
        intervalDomainDerivativePairIntegral w w :=
  intervalDomain_spatial_IBP_of_profile
    (unitIntervalCosineHeatValue_contDiff_two hτ hM)
    (unitIntervalCosineHeatValue_deriv_zero_at_endpoint hτ hM (Or.inl rfl))
    (unitIntervalCosineHeatValue_deriv_zero_at_endpoint hτ hM (Or.inr rfl))
    hw hNeuR hNeuL

end ShenWork.Paper2.IntervalDomainEnergyStep
