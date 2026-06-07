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

/-- **Spatial Neumann IBP from an OPEN-interior profile agreement.**  Variant of
`intervalDomain_spatial_IBP_of_profile` that consumes the agreement
`lift w = S` on the *open* interior `(0,1)` together with closed-`[0,1]`
`C²` regularity of the lift (conjunct (7)'s `ContDiffOn ℝ 2 _ (Icc 0 1)`).  The
closed-`Icc` agreement is recovered by the density bridge
`eqOn_Icc_of_eqOn_Ioo_of_continuousOn` (`S` is `ContDiff ℝ 2`, hence continuous,
and `lift w` is continuous on `[0,1]` by `hreg`).  This removes the artificial
`Ioo → Icc` gap: the heat-value representation is naturally produced on the open
interior (the Fubini/`∑'` interchange), and the endpoint values follow from
continuity rather than being assumed separately. -/
theorem intervalDomain_spatial_IBP_of_profile_interior
    {S : ℝ → ℝ} (hS : ContDiff ℝ 2 S) (hS_d0 : deriv S 0 = 0) (hS_d1 : deriv S 1 = 0)
    {w : intervalDomainPoint → ℝ}
    (hreg : ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1))
    (hw : Set.EqOn (intervalDomainLift w) S (Set.Ioo (0 : ℝ) 1))
    (hNeuR : intervalDomain.normalDeriv w intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv w intervalDomainLeftEndpoint = 0) :
    intervalDomain.integral (fun x => w x * intervalDomain.laplacian w x) =
      intervalDomainNeumannBoundaryTerm w w -
        intervalDomainDerivativePairIntegral w w :=
  intervalDomain_spatial_IBP_of_profile hS hS_d0 hS_d1
    (eqOn_Icc_of_eqOn_Ioo_of_continuousOn hreg.continuousOn hS.continuous.continuousOn hw)
    hNeuR hNeuL

/-- **Spatial Neumann IBP from an OPEN-interior cosine-heat-value agreement.**
Cosine instance of `intervalDomain_spatial_IBP_of_profile_interior`: the slice
agrees with `Σ bₙ cos(nπ·)` only on the *open* `(0,1)` (the form delivered by the
Fubini/parabolic-gain representation), and closed-`[0,1]` continuity is supplied
by the closed-`C²` regularity `hreg`. -/
theorem intervalDomain_spatial_IBP_of_cosineProfile_interior
    {τ : ℝ} (hτ : 0 < τ) {b : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |b n| ≤ M)
    {w : intervalDomainPoint → ℝ}
    (hreg : ContDiffOn ℝ 2 (intervalDomainLift w) (Set.Icc (0 : ℝ) 1))
    (hw : Set.EqOn (intervalDomainLift w)
      (fun x => unitIntervalCosineHeatValue τ b x) (Set.Ioo (0 : ℝ) 1))
    (hNeuR : intervalDomain.normalDeriv w intervalDomainRightEndpoint = 0)
    (hNeuL : intervalDomain.normalDeriv w intervalDomainLeftEndpoint = 0) :
    intervalDomain.integral (fun x => w x * intervalDomain.laplacian w x) =
      intervalDomainNeumannBoundaryTerm w w -
        intervalDomainDerivativePairIntegral w w :=
  intervalDomain_spatial_IBP_of_profile_interior
    (unitIntervalCosineHeatValue_contDiff_two hτ hM)
    (unitIntervalCosineHeatValue_deriv_zero_at_endpoint hτ hM (Or.inl rfl))
    (unitIntervalCosineHeatValue_deriv_zero_at_endpoint hτ hM (Or.inr rfl))
    hreg hw hNeuR hNeuL

/-- **L2 energy differential inequality for a cosine-heat-value solution slice.**
When `u t` is represented on `[0,1]` by a bounded-coefficient cosine heat value
(the common spatial form of the full full-kernel solution `S_t u₀ + D_t`), the
`hIBP` frontier is supplied by `intervalDomain_spatial_IBP_of_cosineProfile` (the
`C^{2,1}`-up-to-boundary regularity proved from the spectral representation) and the
Neumann frontier by `hsol.neumann` (T3).  The energy inequality

  `E'(t) + dissipation ≤ χ·(ε·gradDiss + C·∫u^{2+ρ}) + logistic`

then holds conditional only on the chain rule `hL2Time`, the PDE substitution
`hPDEIntegral`, and the cross-diffusion controls.  The single deep analytic input
is now exactly the closed-boundary heat-value representation `hrep` (the
Fubini/parabolic-gain step). -/
theorem intervalDomain_l2_half_energy_inequality_of_cosineProfile
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
    {τ : ℝ} (hτ : 0 < τ) {b : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |b n| ≤ M)
    (hrep : Set.EqOn (intervalDomainLift (u t))
      (fun x => unitIntervalCosineHeatValue τ b x) (Set.Icc (0 : ℝ) 1))
    (hCrossControl :
      -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t)) :
    ∃ Ceps,
      deriv (fun τ' => intervalDomainL2HalfEnergy u τ') t +
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
  have hIBP :
      intervalDomainL2DiffusionIntegral u t =
        intervalDomainNeumannBoundaryTerm (u t) (u t) -
          intervalDomainL2DiffusionDissipation u t :=
    intervalDomain_spatial_IBP_of_cosineProfile hτ hM hrep hNeuR hNeuL
  exact intervalDomain_l2_half_energy_cross_bootstrap_inequality_of_frontiers
    heps hchiBound ht0 htT hcross hL2Time hPDEIntegral hIBP hNeuR hNeuL hCrossControl

/-- **L2 energy inequality from an OPEN-interior cosine representation.**  Variant
of `intervalDomain_l2_half_energy_inequality_of_cosineProfile` whose deepest
analytic input is the cosine heat-value representation on the *open* interior
`(0,1)` — exactly the form delivered by
`ShenWork.IntervalDuhamelRegularity.DuhamelHeatValueRepresentation` (the
Fubini/parabolic-gain step).  The closed-`[0,1]` agreement is recovered for free
from conjunct (7) of the solution's regularity (closed-`C²` of the lift) via the
density bridge `eqOn_Icc_of_eqOn_Ioo_of_continuousOn`.  This closes the artificial
`Ioo → Icc` gap (T5 tail R3): the representation no longer has to be assumed up to
the endpoints, only on the open interior where the spectral interchange lives. -/
theorem intervalDomain_l2_half_energy_inequality_of_cosineProfile_interior
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
    {τ : ℝ} (hτ : 0 < τ) {b : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |b n| ≤ M)
    (hrepIoo : Set.EqOn (intervalDomainLift (u t))
      (fun x => unitIntervalCosineHeatValue τ b x) (Set.Ioo (0 : ℝ) 1))
    (hCrossControl :
      -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t)) :
    ∃ Ceps,
      deriv (fun τ' => intervalDomainL2HalfEnergy u τ') t +
          intervalDomainL2DiffusionDissipation u t ≤
        chiBound *
            (eps * intervalDomainLpWeightedGradientDissipation 2 u t +
              Ceps *
                intervalDomain.integral (fun x => (u t x) ^ (2 + rho))) +
          intervalDomainL2LogisticIntegral params u t := by
  -- Conjunct (7): closed-`[0,1]` `C²` of the `u`-lift at the interior time `t`.
  have hreg7 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  -- Density bridge: open-interior cosine agreement ⇒ closed-`Icc` agreement.
  have hrep : Set.EqOn (intervalDomainLift (u t))
      (fun x => unitIntervalCosineHeatValue τ b x) (Set.Icc (0 : ℝ) 1) :=
    eqOn_Icc_of_eqOn_Ioo_of_continuousOn hreg7.continuousOn
      ((unitIntervalCosineHeatValue_contDiff_two hτ hM).continuous.continuousOn) hrepIoo
  exact intervalDomain_l2_half_energy_inequality_of_cosineProfile
    heps hchiBound ht0 htT hsol hcross hL2Time hPDEIntegral hτ hM hrep hCrossControl

end ShenWork.Paper2.IntervalDomainEnergyStep
