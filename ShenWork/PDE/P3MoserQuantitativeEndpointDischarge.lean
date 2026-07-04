import ShenWork.PDE.IntervalDomainMoserActualAtoms
import ShenWork.Paper3.IntervalDomainIntegratedMoserAssembly
import ShenWork.Paper2.IntervalDomainMCL

/-!
Quantitative endpoint wiring for the integrated Moser route.

The scalar dyadic root tower is already proved in
`IntervalDomainMoserActualAtoms`.  This file only connects a PDE-produced
dyadic recurrence and a terminal pointwise power-control estimate to the
existing `IntervalDomainMoserQuantitativeEndpoint` field.
-/

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMCL
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserLemmaDischarge

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserQuantitativeEndpointDischarge

/-- Data from the PDE-level dyadic Moser endpoint recurrence.

The recurrence is indexed from `1`, matching the already-proved scalar tower
`dyadic_root_tower_bound`.  The terminal index is stored as `terminalIndex + 1`
so that the scalar theorem applies directly. -/
def DyadicMoserEndpointRecurrence
    (u : ℝ → intervalDomain.Point → ℝ) (T : ℝ)
    (pSeq rootBound : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ terminalIndex : ℕ,
    1 ≤ C ∧
      0 ≤ rootBound 1 ∧
      (∀ k, 1 ≤ k →
        rootBound (k + 1) ≤ dyadicMoserFactor C k * rootBound k) ∧
      0 < pSeq (terminalIndex + 1) ∧
      0 ≤ rootBound (terminalIndex + 1) ∧
      IntervalDomainMoserPointwisePowerControlBefore
        u T (pSeq (terminalIndex + 1)) (rootBound (terminalIndex + 1))

/-- Wire a PDE-level dyadic root recurrence into the existing quantitative
endpoint interface, using the already-proved scalar root tower bound. -/
theorem intervalDomain_moserQuantitativeEndpoint_of_dyadic_recurrence
    {u : ℝ → intervalDomain.Point → ℝ} {T : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hrec : DyadicMoserEndpointRecurrence u T pSeq rootBound) :
    IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound := by
  rcases hrec with
    ⟨C, terminalIndex, hC_ge_one, hroot_one_nonneg, hrecurrence,
      hterminal_p_pos, hterminal_root_nonneg, hterminal_pointwise⟩
  refine
    ⟨4 * C * rootBound 1, ?_, terminalIndex + 1,
      hterminal_p_pos, hterminal_root_nonneg, ?_,
      hterminal_pointwise⟩
  · have hC_nonneg : 0 ≤ C := le_trans zero_le_one hC_ge_one
    exact mul_nonneg (mul_nonneg (by norm_num) hC_nonneg)
      hroot_one_nonneg
  · exact
      dyadic_root_tower_bound
        (C := C) (M := rootBound)
        hC_ge_one hroot_one_nonneg hrecurrence
        terminalIndex

/-- Conditional endpoint producer from integrated dissipation.

The integrated PDE estimate is consumed only through the supplied extraction
of the dyadic recurrence data.  This theorem does not re-prove the scalar tower
and does not pretend that a bare time-integrated estimate alone gives
pointwise control. -/
theorem intervalDomain_moserQuantitativeEndpoint_of_integrated_dissipation
    {u : ℝ → intervalDomain.Point → ℝ} {T rho p0 : ℝ}
    {pSeq rootBound : ℕ → ℝ}
    (hdiss :
      IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (hfromDiss :
      IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 →
        DyadicMoserEndpointRecurrence u T pSeq rootBound) :
    IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound :=
  intervalDomain_moserQuantitativeEndpoint_of_dyadic_recurrence
    (hfromDiss hdiss)

#print axioms intervalDomain_moserQuantitativeEndpoint_of_dyadic_recurrence
#print axioms intervalDomain_moserQuantitativeEndpoint_of_integrated_dissipation

end ShenWork.IntervalDomainExistence.P3MoserQuantitativeEndpointDischarge

namespace ShenWork.Paper3

open ShenWork.IntervalDomainExistence.P3MoserQuantitativeEndpointDischarge

/-- Integrated-drop residuals where the quantitative endpoint field is supplied
as dyadic endpoint data extracted from the integrated dissipation estimate.

This is a wiring layer for
`IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals`: the existing
closed-energy, integrated-dissipation, and mass-gradient fields are forwarded,
while `dyadicEndpoint` is converted to the older `quantitativeEndpoint` field. -/
structure IntervalDomainMassLpSmoothingMoserIntegratedDropDyadicEndpointResiduals
    (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  closedEnergyTrace :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        Nonempty
          (ClosedEnergyIdentityTraceData T u₀ u)
  integratedMoserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
  relativeMassGradient :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        ∃ cGrad : ℝ → ℝ,
          (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
          (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
            LpMassGradientInterpolationEstimate intervalDomain
              (pExp + rho) eta Ceta T u) ∧
          (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
            intervalDomain.integral (fun x =>
              (u t x) ^ (pExp + rho - 2) *
                (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad pExp * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
          MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0
  dyadicEndpoint :
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
            IntegratedMoserDissipationDropBefore
              intervalDomain u T (2 * p.γ) pExp →
              DyadicMoserEndpointRecurrence u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingMoserIntegratedDropDyadicEndpointResiduals

/-- Convert dyadic endpoint data to the integrated-drop assembly residuals by
filling the existing `quantitativeEndpoint` field. -/
def to_integratedDropResiduals
    {p : CM2Params}
    (h :
      IntervalDomainMassLpSmoothingMoserIntegratedDropDyadicEndpointResiduals
        p) :
    IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p where
  boundednessHyp := h.boundednessHyp
  closedEnergyTrace := h.closedEnergyTrace
  integratedMoserDissipation := h.integratedMoserDissipation
  relativeMassGradient := h.relativeMassGradient
  quantitativeEndpoint := by
    intro u₀ hu₀ T hT u v hsol htrace pExp hpExp hLp
    have hcross :
        CrossDiffusionBootstrapEstimate intervalDomain p T
          (2 * p.γ) u v :=
      intervalDomain_crossDiffusionBootstrapEstimate_of_classical hsol
    have hboot :
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T (2 * p.γ) pExp :=
      abstract_prop25_bootstrap_two_gamma hT hpExp hLp
    have hdiss :
        IntegratedMoserDissipationDropBefore
          intervalDomain u T (2 * p.γ) pExp :=
      h.integratedMoserDissipation hsol hcross hboot
    rcases h.dyadicEndpoint hu₀ hT hsol htrace pExp hpExp hLp with
      ⟨pSeq, rootBound, hendpoint⟩
    refine ⟨pSeq, rootBound, ?_⟩
    intro hAll
    exact
      intervalDomain_moserQuantitativeEndpoint_of_integrated_dissipation
        hdiss (hendpoint hAll)

#print axioms to_integratedDropResiduals

end IntervalDomainMassLpSmoothingMoserIntegratedDropDyadicEndpointResiduals

end ShenWork.Paper3

end
