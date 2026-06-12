import ShenWork.PDE.IntervalChemDivFluxChain

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.IntervalMildSourceDecayHelper
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Interior source is the spatial derivative of the lifted chemotactic flux. -/
theorem coupledChemDivSourceLift_eq_deriv_fluxLift_interior
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    coupledChemDivSourceLift p u s x =
      deriv (coupledChemDivFluxLift p u s) x := by
  have hxIcc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  unfold coupledChemDivSourceLift intervalDomainChemotaxisDiv
    coupledChemDivFluxLift
  simp only [intervalDomainLift, hxIcc, dif_pos]

/-- The explicit chem-div time derivative is the spatial derivative of the
inner flux time derivative. -/
theorem coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ} :
    coupledChemDivTimeDerivativeLift p u s x =
      deriv (coupledChemDivFluxTimeDerivativeLift p u s) x := by
  rfl

/-- Local atoms for the remaining outer `∂ₜ∂ₓ = ∂ₓ∂ₜ` commute step. -/
structure CoupledChemDivOuterCommuteAtoms
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => deriv (coupledChemDivFluxLift p u r) x)
        (deriv (coupledChemDivFluxTimeDerivativeLift p u s) x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

/-- Producer for `CoupledChemDivLocalChainRule` from the explicit outer commute
atoms.  No coefficient derivative or `DuhamelSourceTimeC1` is assumed. -/
theorem coupledChemDivLocalChainRule_of_outerCommuteAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (A : CoupledChemDivOuterCommuteAtoms p u) :
    CoupledChemDivLocalChainRule p u := by
  refine coupledChemDivLocalChainRule_of_pointwiseChainAtoms ?_
  refine ⟨fun τ => ?_⟩
  rcases A.exists_local_slab τ with ⟨δ, hδ, hsrc, hcomm, hcont⟩
  refine ⟨δ, hδ, hsrc, ?_, hcont⟩
  intro x hx s hs
  have hsource :
      (fun r => coupledChemDivSourceLift p u r x) =
        fun r => deriv (coupledChemDivFluxLift p u r) x := by
    funext r
    exact coupledChemDivSourceLift_eq_deriv_fluxLift_interior hx
  have htime :
      coupledChemDivTimeDerivativeLift p u s x =
        deriv (coupledChemDivFluxTimeDerivativeLift p u s) x :=
    coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative
  rw [hsource, htime]
  exact hcomm x hx s hs

/-- Direct source-time-C¹ wiring with the local chain rule supplied by the
outer commute producer. -/
noncomputable def coupledChemDivSource_timeC1_of_outerCommuteAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (Cchem : ℝ) (hCchem : 0 ≤ Cchem)
    (hH2 : ∀ s, 0 ≤ s →
      IntervalWeakH2Neumann (coupledChemDivSourceLift p u s))
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (coupledChemDivSourceLift p u s) k|
        ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2)
    (hzero : ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem)
    (A : CoupledChemDivOuterCommuteAtoms p u)
    (hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n))
    (MchemDot : ℝ)
    (hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) :=
  coupledChemDivSource_timeC1_of_fields
    { Cchem := Cchem
      hCchem := hCchem
      hH2 := hH2
      hdecay := hdecay
      hzero := hzero
      hchain := coupledChemDivLocalChainRule_of_outerCommuteAtoms A
      hadotcont := hadotcont
      MchemDot := MchemDot
      hMdot := hMdot }

end ShenWork.IntervalCoupledRegularityBootstrap
