import ShenWork.PDE.IntervalDomainAPrioriGlobal
import ShenWork.PDE.P3MoserActualWiring
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.PDE.P3MoserRegularityProducer
import ShenWork.Paper2.IntervalDomainVSliceBounds

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.MinPersistenceAtoms
open Filter

noncomputable section

namespace ShenWork.IntervalDomainExistence

private theorem intervalDomain_lift_eq_interior
    (f : intervalDomain.Point → ℝ) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- A finite-horizon `L∞` bound on `u` gives the chemotactic drift bound for
the elliptic `v` slice.  The derivative estimate is the existing
`v_slice_coeff_bounds`; the denominator is harmless because `v >= 0` and
`β >= 0`, so `(1 + v)^β >= 1`. -/
theorem IntervalDomainChemotacticDriftBound_of_LinfBound
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hpoint : PointwiseBoundedBefore T u) :
    IntervalDomainChemotacticDriftBound p T v := by
  rcases hpoint with ⟨M, hM⟩
  let M' : ℝ := max M 0
  let W : ℝ := 2 * (p.ν * M' ^ p.γ)
  have hM' : 0 ≤ M' := le_max_right M 0
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM' _))
  refine ⟨W, hW_nonneg, ?_⟩
  intro t y ht0 htT hyIcc
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨h3, _, _, h6, h7, _, _⟩ := hsol.regularity
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0 : ℝ) 1) :=
    (h3 t htmem).2
  have hv_cont : ContinuousOn (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) :=
    (h7 t htmem).2.1.continuousOn
  have hNeu0 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (h6 t htmem).2.1
  have hNeu1 : Tendsto (deriv (intervalDomainLift (v t)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) :=
    (h6 t htmem).2.2
  have hv_nonneg : ∀ z, 0 ≤ intervalDomainLift (v t) z := by
    intro z
    unfold intervalDomainLift
    split_ifs with hz
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hu_nonneg_int :
      ∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ intervalDomainLift (u t) z := by
    intro z hz
    rw [intervalDomain_lift_eq_interior (u t) hz]
    exact (hsol.u_pos' ht0 htT).le
  have hu_le_int :
      ∀ z ∈ Set.Ioo (0 : ℝ) 1, intervalDomainLift (u t) z ≤ M' := by
    intro z hz
    rw [intervalDomain_lift_eq_interior (u t) hz]
    exact le_trans
      (hM t ⟨z, Set.Ioo_subset_Icc_self hz⟩ ht0 htT hz)
      (le_max_left M 0)
  have hPDE_v : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv (intervalDomainLift (v t))) z =
        p.μ * intervalDomainLift (v t) z -
          p.ν * (intervalDomainLift (u t) z) ^ p.γ := by
    intro z hz
    have hx : (⟨z, Set.Ioo_subset_Icc_self hz⟩ : intervalDomain.Point) ∈
        intervalDomain.inside := hz
    have hpv := hsol.pde_v ht0 htT hx
    rw [intervalDomain_lift_eq_interior (v t) hz,
      intervalDomain_lift_eq_interior (u t) hz]
    have hlap : intervalDomain.laplacian (v t)
        (⟨z, Set.Ioo_subset_Icc_self hz⟩ : intervalDomain.Point) =
        deriv (deriv (intervalDomainLift (v t))) z := rfl
    rw [hlap] at hpv
    linarith [hpv]
  have hvb := v_slice_coeff_bounds (p := p) (u := u t) (v := v t) (M' := M')
    hM' hv_c2 hv_cont hv_nonneg hu_nonneg_int hu_le_int hPDE_v hNeu0 hNeu1
  by_cases hy0 : y = 0
  · subst y
    have hderiv0 : deriv (intervalDomainLift (v t)) 0 = 0 :=
      (h7 t htmem).2.2.1
    simp [intervalDomainChemotacticDrift, hderiv0, hW_nonneg]
  by_cases hy1 : y = 1
  · subst y
    have hderiv1 : deriv (intervalDomainLift (v t)) 1 = 0 :=
      (h7 t htmem).2.2.2
    simp [intervalDomainChemotacticDrift, hderiv1, hW_nonneg]
  · have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hy0), lt_of_le_of_ne hyIcc.2 hy1⟩
    have hbase : 1 ≤ 1 + intervalDomainLift (v t) y := by
      linarith [hv_nonneg y]
    have hden_ge : 1 ≤ (1 + intervalDomainLift (v t) y) ^ p.β :=
      Real.one_le_rpow hbase p.hβ
    have hden_pos : 0 < (1 + intervalDomainLift (v t) y) ^ p.β :=
      lt_of_lt_of_le zero_lt_one hden_ge
    rw [intervalDomainChemotacticDrift, abs_div, abs_of_nonneg hden_pos.le]
    exact (div_le_self (abs_nonneg _) hden_ge).trans (hvb.1 y hyIoo)

/-- Lower-level inputs that replace the old Moser-ladder route fields
`driftBoundFromMass`, `allLpBoundFromBootstrap`, and `endpointBoundFromLp`.

The remaining `l2SeedRegularity` field is kept explicit because the current
classical-solution interface does not determine the value `u 0`, while the seed
frontier asks for closed-time continuity of an energy involving `u 0`.

The Moser part now carries the actual atoms: physical-`B` dissipation,
relative interpolation, and the quantitative endpoint/root tower.  It no
longer forwards through `IntervalDomainPaper2Corollary21FrontierData` or
`Prop25MoserFrontiers`. -/
structure IntervalDomainMassLpSmoothingMoserLadderResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingMoserLadderResiduals

theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
    h.moserDissipation h.relativeMoserInterpolation

theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    h.moserDissipation h.relativeMoserInterpolation h.quantitativeEndpoint

/-- Build the old residual package.  The old drift field is reconstructed from
the `L∞` bound obtained by the L² seed, Corollary 2.1, and the quantitative
Moser endpoint. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  driftBoundFromMass := by
    intro u₀ hu₀ T hT u v hsol htrace hmass
    have hCor21 : Corollary_2_1 intervalDomain p := h.corollary21
    have hProp25 : Proposition_2_5 intervalDomain p := h.proposition25
    have hspatial :
        IntervalDomainL2SpatialAbsorptionEstimate p T u v hsol hmass :=
      intervalDomainL2SpatialAbsorptionEstimate_of_classical
        h.boundednessHyp hsol hmass
    have huniform :
        IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequalityUniformCeps_of_classicalSolution
        hsol
    have hhalf :
        IntervalDomainL2HalfEnergyDifferentialInequality p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequality_of_classicalSolution hsol
    have habsorbing :
        IntervalDomainL2AbsorbingDifferentialInequalityResult p T u :=
      IntervalDomainL2AbsorbingDifferentialInequality
        h.boundednessHyp.1 hsol hmass hspatial huniform
    have hregularity : IntervalDomainL2SeedRegularityFrontier T u :=
      h.l2SeedRegularity u₀ hu₀ T hT u v hsol htrace
    have hintegrated :
        IntervalDomainL2AbsorbingIntegratedInequalityResult p T u :=
      IntervalDomainL2AbsorbingIntegratedInequality
        h.boundednessHyp.2.1 hsol habsorbing hregularity
    have hL2 :
        LpPowerBoundedBefore intervalDomain 2 T u :=
      intervalDomainL2PowerBoundedBefore_of_absorbingIntegratedInequality
        hsol hintegrated hregularity
    have hbootstrap :
        ∃ rho > 0,
          CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
            ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
              LpPowerBoundedBefore intervalDomain p0 T u :=
      intervalDomainL2BootstrapSeed_of_L2PowerBoundedBefore
        h.boundednessHyp hu₀ hT hsol htrace hhalf hL2
    have hbounded :
        IsPaper2BoundedBefore intervalDomain T u :=
      intervalDomainBoundedBefore_of_corollary21_and_proposition25
        hCor21 hProp25 hu₀ hT hsol htrace hbootstrap
    have hpoint : PointwiseBoundedBefore T u :=
      pointwiseBoundedBefore_of_boundedBefore_and_supNormControls hbounded
        (supNormControlsPointwiseBefore_of_classicalSolution hsol)
    exact IntervalDomainChemotacticDriftBound_of_LinfBound hsol hpoint
  l2SeedRegularity := h.l2SeedRegularity
  allLpBoundFromBootstrap := h.corollary21
  endpointBoundFromLp := h.proposition25

/-- A-priori bound from the reduced Moser-ladder residuals. -/
def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserLadderResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_routeResiduals.aprioriBound

end IntervalDomainMassLpSmoothingMoserLadderResiduals

/-- Lower-level inputs that replace the old pointwise Moser-ladder route
fields by a supplied integrated first-crossing step.

This package is intentionally route-level: it consumes
`IntegratedMoserFirstCrossingStep` directly via `P3MoserActualWiring` and does
not derive old pointwise Moser atoms such as
`MoserDissipationDropBeforeNonnegB` or `RelativeMoserInterpolationBefore`. -/
structure IntervalDomainMassLpSmoothingIntegratedStepResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  integratedStep :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingIntegratedStepResiduals

/-- Corollary 2.1 from the supplied integrated first-crossing step. -/
theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    Corollary_2_1 intervalDomain p :=
  intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
    h.integratedStep

/-- Proposition 2.5 from the supplied integrated first-crossing step and the
quantitative Moser endpoint/root tower. -/
theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
    h.integratedStep h.quantitativeEndpoint

/-- Build the old mass/Lp/smoothing residual package from the integrated-step
route.

The drift field is reconstructed from the `L∞` bound obtained by the L² seed,
Corollary 2.1, and Proposition 2.5, exactly as in
`IntervalDomainMassLpSmoothingMoserLadderResiduals.to_routeResiduals`. -/
def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  driftBoundFromMass := by
    intro u₀ hu₀ T hT u v hsol htrace hmass
    have hCor21 : Corollary_2_1 intervalDomain p := h.corollary21
    have hProp25 : Proposition_2_5 intervalDomain p := h.proposition25
    have hspatial :
        IntervalDomainL2SpatialAbsorptionEstimate p T u v hsol hmass :=
      intervalDomainL2SpatialAbsorptionEstimate_of_classical
        h.boundednessHyp hsol hmass
    have huniform :
        IntervalDomainL2HalfEnergyDifferentialInequalityUniformCeps p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequalityUniformCeps_of_classicalSolution
        hsol
    have hhalf :
        IntervalDomainL2HalfEnergyDifferentialInequality p T u v :=
      intervalDomainL2HalfEnergyDifferentialInequality_of_classicalSolution hsol
    have habsorbing :
        IntervalDomainL2AbsorbingDifferentialInequalityResult p T u :=
      IntervalDomainL2AbsorbingDifferentialInequality
        h.boundednessHyp.1 hsol hmass hspatial huniform
    have hregularity : IntervalDomainL2SeedRegularityFrontier T u :=
      h.l2SeedRegularity u₀ hu₀ T hT u v hsol htrace
    have hintegrated :
        IntervalDomainL2AbsorbingIntegratedInequalityResult p T u :=
      IntervalDomainL2AbsorbingIntegratedInequality
        h.boundednessHyp.2.1 hsol habsorbing hregularity
    have hL2 :
        LpPowerBoundedBefore intervalDomain 2 T u :=
      intervalDomainL2PowerBoundedBefore_of_absorbingIntegratedInequality
        hsol hintegrated hregularity
    have hbootstrap :
        ∃ rho > 0,
          CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
            ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
              LpPowerBoundedBefore intervalDomain p0 T u :=
      intervalDomainL2BootstrapSeed_of_L2PowerBoundedBefore
        h.boundednessHyp hu₀ hT hsol htrace hhalf hL2
    have hbounded :
        IsPaper2BoundedBefore intervalDomain T u :=
      intervalDomainBoundedBefore_of_corollary21_and_proposition25
        hCor21 hProp25 hu₀ hT hsol htrace hbootstrap
    have hpoint : PointwiseBoundedBefore T u :=
      pointwiseBoundedBefore_of_boundedBefore_and_supNormControls hbounded
        (supNormControlsPointwiseBefore_of_classicalSolution hsol)
    exact IntervalDomainChemotacticDriftBound_of_LinfBound hsol hpoint
  l2SeedRegularity := h.l2SeedRegularity
  allLpBoundFromBootstrap := h.corollary21
  endpointBoundFromLp := h.proposition25

/-- A-priori bound from the integrated-step residual package. -/
def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedStepResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_routeResiduals.aprioriBound

end IntervalDomainMassLpSmoothingIntegratedStepResiduals

/-- Lower-level inputs that produce the integrated first-crossing step from the
regularity-aware integrated Moser data, without exposing the older lower-average
/ upper-gap split as residual fields. -/
structure IntervalDomainMassLpSmoothingIntegratedMoserResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingIntegratedMoserResiduals

def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedMoserResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
      (h.classicalRegularity hsol hcross hboot)
      hsol
      (h.integratedDissipation hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedMoserResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_integratedStepResiduals.to_routeResiduals

def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingIntegratedMoserResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_integratedStepResiduals.aprioriBound

end IntervalDomainMassLpSmoothingIntegratedMoserResiduals

/-- Lower-level inputs that produce the integrated first-crossing step from the
regular-energy coefficient-gap route, without carrying a pre-built integrated
dissipation field. -/
structure IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTC :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyWindowFTC intervalDomain u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals

def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
      hsol hcross hboot
      (h.classicalRegularity hsol hcross hboot)
      (h.energyWindowFTC hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (h.coeffGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

/-- Corollary 2.1 from the regular-energy coefficient-gap residual package. -/
theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    Corollary_2_1 intervalDomain p :=
  h.to_integratedStepResiduals.corollary21

/-- Proposition 2.5 from the regular-energy coefficient-gap residual package. -/
theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    Proposition_2_5 intervalDomain p :=
  h.to_integratedStepResiduals.proposition25

def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_integratedStepResiduals.to_routeResiduals

def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_integratedStepResiduals.aprioriBound

end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals

/-- Regular-energy coefficient-gap residuals with the window-FTC field reduced
to local FTC data: closed endpoint power-energy continuity plus
derivative-window integrability. -/
structure IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTCData :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserEnergyWindowFTCLocalData u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals

def to_regularEnergyCoeffGapResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  classicalRegularity := h.classicalRegularity
  energyWindowFTC := fun hsol hcross hboot =>
    intervalDomain_integratedMoserEnergyWindowFTC_of_localData
      hsol (h.energyWindowFTCData hsol hcross hboot)
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint

def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p :=
  h.to_regularEnergyCoeffGapResiduals.to_integratedStepResiduals

/-- Corollary 2.1 from the local-FTC-data regular-energy coefficient-gap route. -/
theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    Corollary_2_1 intervalDomain p :=
  h.to_regularEnergyCoeffGapResiduals.corollary21

/-- Proposition 2.5 from the local-FTC-data regular-energy coefficient-gap route. -/
theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    Proposition_2_5 intervalDomain p :=
  h.to_regularEnergyCoeffGapResiduals.proposition25

def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_regularEnergyCoeffGapResiduals.to_routeResiduals

def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_regularEnergyCoeffGapResiduals.aprioriBound

end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals

/-- Regular-energy coefficient-gap residuals with the window-FTC field reduced
to only derivative-window integrability.  The endpoint continuity needed for
the energy-window FTC is inherited from `classicalRegularity`. -/
structure IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  derivativeWindowIntegrability :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coeffGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals

def to_FTCLocalDataResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals
      p) :
    IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals
      p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  classicalRegularity := h.classicalRegularity
  energyWindowFTCData := fun hsol hcross hboot =>
    let hreg := h.classicalRegularity hsol hcross hboot
    { endpointEnergy := hreg.endpointEnergy
      derivativeWindowIntegrability :=
        h.derivativeWindowIntegrability hsol hcross hboot }
  relativeMoserInterpolation := h.relativeMoserInterpolation
  coeffGap := h.coeffGap
  quantitativeEndpoint := h.quantitativeEndpoint

def to_regularEnergyCoeffGapResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals
      p) :
    IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p :=
  h.to_FTCLocalDataResiduals.to_regularEnergyCoeffGapResiduals

def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals
      p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p :=
  h.to_FTCLocalDataResiduals.to_integratedStepResiduals

/-- Corollary 2.1 from the derivative-window regular-energy coefficient-gap
route. -/
theorem corollary21
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals
      p) :
    Corollary_2_1 intervalDomain p :=
  h.to_FTCLocalDataResiduals.corollary21

/-- Proposition 2.5 from the derivative-window regular-energy coefficient-gap
route. -/
theorem proposition25
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals
      p) :
    Proposition_2_5 intervalDomain p :=
  h.to_FTCLocalDataResiduals.proposition25

def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals
      p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_FTCLocalDataResiduals.to_routeResiduals

def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals
      p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_FTCLocalDataResiduals.aprioriBound

end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals

/-- Lower-level inputs that refine `IntegratedStepResiduals` by replacing
the opaque `integratedStep` field with an explicit high-excursion
contradiction-window frontier supplier.

The conversion to `IntegratedStepResiduals` uses
`integratedMoserFirstCrossingStep_of_windowFrontier` from
`P3MoserIntegratedClosure`. -/
structure IntervalDomainMassLpSmoothingWindowFrontierResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  windowFrontier :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingFromWindowFrontier
          intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingWindowFrontierResiduals

def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingWindowFrontierResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  integratedStep := fun hsol hcross hboot =>
    integratedMoserFirstCrossingStep_of_windowFrontier
      (h.windowFrontier hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingWindowFrontierResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_integratedStepResiduals.to_routeResiduals

def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingWindowFrontierResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_integratedStepResiduals.aprioriBound

end IntervalDomainMassLpSmoothingWindowFrontierResiduals

/-- Lower-level inputs that refine `WindowFrontierResiduals` by splitting the
high-excursion frontier into its lower-average and upper-gap suppliers. -/
structure IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainL2SeedRegularityFrontier T u
  lowerUpperFrontiers :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingLowerUpperFrontiers
          intervalDomain u T rho p0
  quantitativeEndpoint :
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals

def to_windowFrontierResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals p) :
    IntervalDomainMassLpSmoothingWindowFrontierResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  windowFrontier := fun hsol hcross hboot =>
    integratedMoserFirstCrossingFromWindowFrontier_of_lowerUpperFrontiers
      (h.lowerUpperFrontiers hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p :=
  h.to_windowFrontierResiduals.to_integratedStepResiduals

def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals p) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  h.to_integratedStepResiduals.to_routeResiduals

def aprioriBound
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals p) :
    IntervalDomainMassLpSmoothingAprioriBound p :=
  h.to_integratedStepResiduals.aprioriBound

end IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals

#print axioms IntervalDomainMassLpSmoothingIntegratedStepResiduals.corollary21
#print axioms IntervalDomainMassLpSmoothingIntegratedStepResiduals.proposition25
#print axioms IntervalDomainMassLpSmoothingIntegratedStepResiduals.to_routeResiduals
#print axioms IntervalDomainMassLpSmoothingIntegratedStepResiduals.aprioriBound
#print axioms
  IntervalDomainMassLpSmoothingIntegratedMoserResiduals.to_integratedStepResiduals
#print axioms
  IntervalDomainMassLpSmoothingIntegratedMoserResiduals.to_routeResiduals
#print axioms IntervalDomainMassLpSmoothingIntegratedMoserResiduals.aprioriBound
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.to_integratedStepResiduals
#print axioms IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.corollary21
#print axioms IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.proposition25
#print axioms
  IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.to_routeResiduals
#print axioms IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals.aprioriBound

namespace IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals

#print axioms to_regularEnergyCoeffGapResiduals
#print axioms to_integratedStepResiduals
#print axioms corollary21
#print axioms proposition25
#print axioms to_routeResiduals
#print axioms aprioriBound

end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapFTCLocalDataResiduals

namespace IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals

#print axioms to_FTCLocalDataResiduals
#print axioms to_regularEnergyCoeffGapResiduals
#print axioms to_integratedStepResiduals
#print axioms corollary21
#print axioms proposition25
#print axioms to_routeResiduals
#print axioms aprioriBound

end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapDerivativeWindowResiduals

#print axioms IntervalDomainMassLpSmoothingWindowFrontierResiduals.to_integratedStepResiduals
#print axioms IntervalDomainMassLpSmoothingWindowFrontierResiduals.to_routeResiduals
#print axioms IntervalDomainMassLpSmoothingWindowFrontierResiduals.aprioriBound
#print axioms IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.to_windowFrontierResiduals
#print axioms IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.to_integratedStepResiduals
#print axioms IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.to_routeResiduals
#print axioms IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals.aprioriBound

end ShenWork.IntervalDomainExistence

end
