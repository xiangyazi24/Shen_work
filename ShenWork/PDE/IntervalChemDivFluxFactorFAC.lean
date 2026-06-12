import ShenWork.PDE.IntervalChemDivFluxJointC2Producer
import ShenWork.PDE.IntervalResolverPositivity

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverPositivity
open ShenWork.PDE
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Non-circular local inputs for the FAC lane.

The resolver/Picard joint `C²` fields and the time-partial bridge remain explicit
analytic hypotheses.  The positivity floor is deliberately absent: it is proved
below from the committed Neumann resolver positivity theorem. -/
structure CoupledChemDivFluxFactorFACInputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_spectral_agreement :
    ∃ U : ℝ,
      ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement U
        (coupledChemicalConcentration p u)
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ s : ℝ, Continuous (u s)) ∧
    (∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
            q.2)
        (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

/-- The concrete resolver floor: `1 + v` is strictly positive because the
committed elliptic resolver is nonnegative for every nonnegative continuous
Picard slice. -/
theorem coupledChemical_floor_pos_of_nonneg_continuous
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (s x : ℝ) :
    0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have hnonneg :
        0 ≤ intervalNeumannResolverR p (u s) ⟨x, hx⟩ := by
      simpa [coupledChemicalConcentration] using
        coupledChemical_nonneg (p := p) (T := 1) (u := fun _ => u s)
          (fun _ _ _ => hu_nonneg s) (fun _ _ _ => hu_cont s)
          (by norm_num : 0 < (1 / 2 : ℝ))
          (by norm_num : (1 / 2 : ℝ) < 1) ⟨x, hx⟩
    simpa [coupledChemicalConcentration, intervalDomainLift, hx] using
      add_pos_of_pos_of_nonneg zero_lt_one hnonneg
  · simp [intervalDomainLift, hx]

/-- FAC producer for the factor package.  It discharges exactly the resolver
floor field and leaves the currently uncommitted joint `C²`/time-bridge analytic
facts as explicit, satisfiable hypotheses. -/
theorem coupledChemDivFluxFactorJointC2Inputs_of_FACInputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputs p u) :
    CoupledChemDivFluxFactorJointC2Inputs p u := by
  refine ⟨fun τ => ?_⟩
  rcases H.exists_local_slab τ with
    ⟨δ, hδ, hsource, hu_cont, hu_nonneg, hu_c2, hv_c2, hgradv_c2,
    htime_bridge, htime_cont⟩
  refine ⟨δ, hδ, hsource, hu_c2, hv_c2, hgradv_c2, ?_,
    htime_bridge, htime_cont⟩
  intro x _ s _
  exact coupledChemical_floor_pos_of_nonneg_continuous hu_cont hu_nonneg s x

/-- Spectral agreement still feeds the committed resolver joint continuity. -/
theorem FAC_resolver_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorFACInputs p u) :
    ∃ U : ℝ, ContinuousOn
      (Function.uncurry
        (fun t x => intervalDomainLift (coupledChemicalConcentration p u t) x))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1) := by
  rcases H.resolver_spectral_agreement with ⟨U, HR⟩
  exact ⟨U, ShenWork.IntervalResolverTimeRegularity.resolver_jointContinuousOn_closed HR⟩

end ShenWork.IntervalCoupledRegularityBootstrap
