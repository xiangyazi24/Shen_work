import ShenWork.PDE.IntervalChemDivFluxJointC2Producer

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.IntervalMildSourceDecayHelper
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Time mirror of `real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt`:
a joint Fréchet derivative identifies the *time* derivative of a fixed-space
slice with the `(1, 0)` directional derivative. -/
theorem real_twoVar_time_deriv_eq_fderiv_of_differentiableAt
    {F : ℝ × ℝ → ℝ} {s x : ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun r : ℝ => F (r, x)) s =
      fderiv ℝ F (s, x) (1, 0) := by
  have hpath : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) s := by
    simpa using
      (HasDerivAt.prodMk (hasDerivAt_id s) (hasDerivAt_const s x))
  have hcomp : HasDerivAt (fun r : ℝ => F (r, x))
      (fderiv ℝ F (s, x) (1, 0)) s := by
    simpa [Function.comp_def] using hF.hasFDerivAt.comp_hasDerivAt s hpath
  exact hcomp.deriv

/-- Extract the inner-`u` time slope from joint `C²` of the lifted `u`: the
canonical time derivative of the fixed-space slice is `slopeSlice`, by the very
definition of `slopeSlice`. -/
theorem slopeSlice_hasDerivAt_of_jointC2
    {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) :
    HasDerivAt (fun r => intervalDomainLift (u r) x)
      (ShenWork.Paper2.PicardLimitK1.slopeSlice u s x) s := by
  have hpath : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) s := by
    simpa using
      (HasDerivAt.prodMk (hasDerivAt_id s) (hasDerivAt_const s x))
  have hdiff : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x) :=
    (hu.differentiableAt (by norm_num))
  have hslice : DifferentiableAt ℝ
      (fun r : ℝ => intervalDomainLift (u r) x) s := by
    simpa [Function.comp_def] using hdiff.comp s hpath.differentiableAt
  simpa [ShenWork.Paper2.PicardLimitK1.slopeSlice] using hslice.hasDerivAt

/-- Extract the inner-`v` time derivative from joint `C²` of the lifted resolver
value: the canonical time derivative of the fixed-space slice is
`coupledChemicalTimeDerivativeLift`, by its definition. -/
theorem coupledChemicalTimeDeriv_hasDerivAt_of_jointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x)) :
    HasDerivAt
      (fun r => intervalDomainLift (coupledChemicalConcentration p u r) x)
      (coupledChemicalTimeDerivativeLift p u s x) s := by
  have hpath : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) s := by
    simpa using
      (HasDerivAt.prodMk (hasDerivAt_id s) (hasDerivAt_const s x))
  have hdiff : DifferentiableAt ℝ
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x) := hv.differentiableAt (by norm_num)
  have hslice : DifferentiableAt ℝ
      (fun r : ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u r) x) s := by
    simpa [Function.comp_def] using hdiff.comp s hpath.differentiableAt
  simpa [coupledChemicalTimeDerivativeLift] using hslice.hasDerivAt

/-- **Time-bridge producer.**  From joint `C²` of `u` and `v` near `x` (which
yields the inner `u`- and `v`-time `HasDerivAt`s for free), the floor, and the
single residual inner-commute datum `hgv` (the `∂ₜ∂ₓv` time derivative of the
gradient slice — the iterate time-`C²` leg), the explicit chem-div flux time
derivative equals the `(1, 0)` Fréchet partial of the flux, eventually near `x`.

This is the mirror of the committed spatial bridge in the time direction. -/
theorem coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, y))
    (hv : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, y))
    (hgradv : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
          q.2)
      (s, y))
    (hbase : ∀ᶠ y in 𝓝 x,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) y)
    (hgv : ∀ᶠ y in 𝓝 x, HasDerivAt
      (fun r => deriv
        (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s) :
    (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y : ℝ =>
        fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
          (s, y) (1, 0)) := by
  filter_upwards [hu, hv, hgradv, hbase, hgv]
    with y hu_y hv_y hgradv_y hbase_y hgv_y
  have hslopeU : HasDerivAt (fun r => intervalDomainLift (u r) y)
      (ShenWork.Paper2.PicardLimitK1.slopeSlice u s y) s :=
    slopeSlice_hasDerivAt_of_jointC2 hu_y
  have hvU : HasDerivAt
      (fun r => intervalDomainLift (coupledChemicalConcentration p u r) y)
      (coupledChemicalTimeDerivativeLift p u s y) s :=
    coupledChemicalTimeDeriv_hasDerivAt_of_jointC2 hv_y
  have hderiv : HasDerivAt (fun r => coupledChemDivFluxLift p u r y)
      (coupledChemDivFluxTimeDerivativeLift p u s y) s :=
    coupledChemDivFlux_hasDerivAt_time hslopeU hgv_y hvU hbase_y
  have hflux_c2 : ContDiffAt ℝ 2
      (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) :=
    coupledChemDivFlux_contDiffAt_of_factorJointC2 hu_y hv_y hgradv_y hbase_y
  have hdiff : DifferentiableAt ℝ
      (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) :=
    hflux_c2.differentiableAt (by norm_num)
  have hbridge :
      deriv (fun r : ℝ => coupledChemDivFluxLift p u r y) s =
        fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
          (s, y) (1, 0) := by
    simpa [Function.uncurry] using
      real_twoVar_time_deriv_eq_fderiv_of_differentiableAt hdiff
  rw [← hbridge, hderiv.deriv]

end ShenWork.IntervalCoupledRegularityBootstrap
