import ShenWork.PDE.IntervalChemDivTimeDerivative

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverTimeRegularity
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Local analytic atoms for the pointwise chem-div time chain rule.

These are intentionally pointwise-in-space facts about the explicit lifted
source field, not coefficient differentiability and not `DuhamelSourceTimeC1`.
The downstream wrapper below turns them into the `CoupledChemDivLocalChainRule`
package consumed by `CoupledChemDivTimeC1Fields`. -/
structure CoupledChemDivPointwiseChainAtoms
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      MeasureTheory.IntervalIntegrable (coupledChemDivSourceLift p u s)
        MeasureTheory.volume (0 : ℝ) 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => coupledChemDivSourceLift p u r x)
        (coupledChemDivTimeDerivativeLift p u s x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

/-- Producer for the local chem-div chain-rule package from pointwise analytic
atoms.  This is the only wrapper needed by the coefficient-time-C¹ consumer; the
atoms are kept separate so each unresolved calculus step has a named target. -/
theorem coupledChemDivLocalChainRule_of_pointwiseChainAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (A : CoupledChemDivPointwiseChainAtoms p u) :
    CoupledChemDivLocalChainRule p u where
  exists_local_slab := A.exists_local_slab

/-- The committed resolver lemma feeding the `∂ₜv` continuity factor. -/
theorem chemDiv_vt_jointContinuous_factor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1) := by
  exact coupledChemicalTimeDerivative_jointContinuousOn_closed H

/-- The committed resolver endpoint restriction feeding fixed-space `∂ₜv`
continuity on positive compact time windows. -/
theorem chemDiv_vt_continuousOn_factor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U T c x : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => coupledChemicalTimeDerivativeLift p u s x)
      (Icc c T) := by
  exact
    coupledChemicalTimeDerivative_continuousOn_Icc_of_lt_horizon
      H hc hTU hx

/-- The K1 datum feeding the `∂ₜu` factor in
`coupledChemDivTimeDerivativeLift`. -/
theorem chemDiv_ut_factor
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) :
    ShenWork.Paper2.PicardLimitK1.slopeSlice u s x =
      deriv (fun r => intervalDomainLift (u r) x) s := by
  rfl

/-- The committed resolver differentiability theorem feeding the `∂ₜv`
pointwise factor on positive horizon times. -/
theorem chemDiv_v_hasDerivAt_factor
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U s y : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hs0 : 0 < s) (hsU : s < U) (hy : y ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r => intervalDomainLift (coupledChemicalConcentration p u r) y)
      (coupledChemicalTimeDerivativeLift p u s y) s := by
  let yy : intervalDomainPoint := ⟨y, hy⟩
  have hhas := (resolver_differentiableAt_time H hs0 hsU yy).hasDerivAt
  have hfun :
      (fun r => intervalDomainLift (coupledChemicalConcentration p u r) y) =
        fun r => coupledChemicalConcentration p u r yy := by
    funext r
    simp [yy, intervalDomainLift, hy]
  have hder :
      deriv (fun r => coupledChemicalConcentration p u r yy) s =
        coupledChemicalTimeDerivativeLift p u s y := by
    unfold coupledChemicalTimeDerivativeLift
    rw [hfun]
  rw [hfun, ← hder]
  exact hhas

end ShenWork.IntervalCoupledRegularityBootstrap
