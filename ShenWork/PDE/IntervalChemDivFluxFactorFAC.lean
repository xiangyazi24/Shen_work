import ShenWork.PDE.IntervalChemDivFluxJointC2Producer
import ShenWork.PDE.IntervalCoupledResolverJointC2
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.PDE.IntervalResolverSpectralJointC2Concrete

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverPositivity
open ShenWork.IntervalResolverSpectralJointC2Concrete
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Non-resolver local FAC inputs on a slab already contained in the spectral
agreement time window. -/
def FACLocalSlabInputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (U τ δ : ℝ) : Prop :=
  0 < δ ∧
    (∀ s : ℝ, s ∈ Metric.ball τ δ → 0 < s ∧ s < U) ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ s : ℝ, Continuous (u s)) ∧
    (∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

/-- Non-circular local inputs for the FAC lane.

The Picard joint `C²` field and the time-partial bridge remain explicit
analytic hypotheses.  The resolver value
and gradient `C²` fields are derived from spectral agreement and the concrete
compact-support restart theorem below.  The positivity floor is deliberately
absent: it is proved from the committed Neumann resolver positivity theorem. -/
structure CoupledChemDivFluxFactorFACInputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_package :
    ∃ U : ℝ,
      ShenWork.IntervalResolverJointC2.ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u) ∧
      ∀ τ : ℝ, ∃ δ : ℝ, FACLocalSlabInputs p u U τ δ

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
  rcases H.resolver_package with ⟨U, HRc2, hslabs⟩
  refine ⟨fun τ => ?_⟩
  rcases hslabs τ with
    ⟨δ, hδ, htime_window, hsource, hu_cont, hu_nonneg, hu_c2,
      htime_bridge, htime_cont⟩
  have hresolver_c2 :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
          (s, x) ∧
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
              q.2)
          (s, x) := by
    intro x hx s hs
    rcases htime_window s hs with ⟨hs0, hsU⟩
    exact coupledChemicalConcentration_resolver_jointC2At_c2Data
      (p := p) (u := u) (U := U) (s := s) (x := x)
      HRc2 hs0 hsU hx
      (by
        intro a₀ M _hM ha₀ a src offset hτ _hagree
        exact resolverSpectralJointC2At_of_restartSmoothCutoff
          (a₀ := a₀) (M := M) (a := a)
          (offset := offset) (s := s) (x := x) hτ ha₀ src)
  have hv_c2 :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
          (s, x) :=
    fun x hx s hs => (hresolver_c2 x hx s hs).1
  have hgradv_c2 :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
              q.2)
          (s, x) :=
    fun x hx s hs => (hresolver_c2 x hx s hs).2
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
  rcases H.resolver_package with ⟨U, HRc2, _hslabs⟩
  exact
    ⟨U,
      ShenWork.IntervalResolverTimeRegularity.resolver_jointContinuousOn_closed
        HRc2.toSpectralAgreement⟩

end ShenWork.IntervalCoupledRegularityBootstrap
