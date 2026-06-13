import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalChemDivFluxTimeBridge
import ShenWork.PDE.IntervalChemDivOuterCommuteProducer
import ShenWork.PDE.IntervalChemDivOuterCommute

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- **Resolver inner commute `hgv` from the physical resolver joint `C²`.**

The residual `∂ₜ∂ₓv = ∂ₓ∂ₜv` commute datum for the resolver value
`v = coupledChemicalConcentration` is produced by applying the committed Clairaut
bridge `real_twoVar_clairaut_hasDerivAt_of_fderiv_partials` to the resolver's
physical joint `C²` (value `+` gradient), exactly mirroring the chem-div flux
outer commute.  No eigen-cube ladder, no `DuhamelSourceTimeC2Coeff`. -/
theorem coupledChemical_innerCommute_of_physicalJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s := by
  set F : ℝ → ℝ → ℝ :=
    fun r => intervalDomainLift (coupledChemicalConcentration p u r) with hF
  have hFC2 : ContDiffAt ℝ 2 (Function.uncurry F) (s, y) :=
    coupledChemical_jointContDiffAt_two H hy
  -- spatial bridge:  `∂ₓ (F r) = D(F)(r, y)(0,1)`, eventually in `r`.
  have hspatial :
      (fun r : ℝ => deriv (F r) y) =ᶠ[𝓝 s]
        (fun r : ℝ => fderiv ℝ (Function.uncurry F) (r, y) (0, 1)) := by
    have hmem : {r : ℝ | True} ∈ 𝓝 s := univ_mem' (fun _ => trivial)
    filter_upwards [hmem] with r _
    have hgr : ContDiffAt ℝ 2 (Function.uncurry F) (r, y) :=
      coupledChemical_jointContDiffAt_two H hy
    have hdiff : DifferentiableAt ℝ (Function.uncurry F) (r, y) :=
      hgr.differentiableAt (by norm_num)
    simpa [F, Function.uncurry] using
      real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt hdiff
  -- time bridge:  `∂ₜv = D(F)(s, y)(1,0)`, eventually in `y`, with
  -- `coupledChemicalTimeDerivativeLift` definitionally the time `deriv` slice.
  have htime :
      (fun z : ℝ => coupledChemicalTimeDerivativeLift p u s z) =ᶠ[𝓝 y]
        (fun z : ℝ => fderiv ℝ (Function.uncurry F) (s, z) (1, 0)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    have hgr : ContDiffAt ℝ 2 (Function.uncurry F) (s, z) :=
      coupledChemical_jointContDiffAt_two H hz
    have hdiff : DifferentiableAt ℝ (Function.uncurry F) (s, z) :=
      hgr.differentiableAt (by norm_num)
    have := real_twoVar_time_deriv_eq_fderiv_of_differentiableAt hdiff
    simpa [coupledChemicalTimeDerivativeLift, F, Function.uncurry] using this
  simpa [F] using
    real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
      (F := F) (Ft := coupledChemicalTimeDerivativeLift p u)
      hFC2 hspatial htime

/-- **Flux time-partial bridge `=ᶠ` field, discharged physically.**

Feeding the resolver physical joint `C²` (value `+` gradient) and the iterate
Picard joint `C²` (`hu_c2`) and floor into the committed time-bridge producer
`coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt`, with the residual inner
commute `hgv` supplied by `coupledChemical_innerCommute_of_physicalJointC2`
(Clairaut), discharges the `coupledChemDivFluxTimeDerivativeLift =ᶠ ∂ₜ flux`
field of the FAC slab — no hypothesis on the bridge or the resolver `C²`. -/
theorem coupledChemDivFlux_timeBridge_of_physicalJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_c2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hbase : ∀ s : ℝ, ∀ x : ℝ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x)
    {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y : ℝ =>
        fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0)) := by
  have hopen : Ioo (0 : ℝ) 1 ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  refine coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
    (hu := ?_) (hv := ?_) (hgradv := ?_) (hbase := ?_) (hgv := ?_)
  · filter_upwards [hopen] with y hy using hu_c2 y hy s
  · filter_upwards [hopen] with y hy using coupledChemical_jointContDiffAt_two H hy
  · filter_upwards [hopen] with y hy using coupledChemical_grad_jointContDiffAt_two H hy
  · filter_upwards [hopen] with y _ using hbase s y
  · filter_upwards [hopen] with y hy using
      coupledChemical_innerCommute_of_physicalJointC2 H hy

/-- **Physical FAC inputs with the time-partial bridge field discharged.**

Same as `coupledChemDivFluxFactorJointC2Inputs_of_physical`, but the
`coupledChemDivFluxTimeDerivativeLift =ᶠ ∂ₜ flux` field is no longer a slab
hypothesis: it is produced internally from the resolver physical joint `C²`
via the Clairaut inner commute.  The remaining `other'` fields are exactly the
genuine upstream data — source continuity, the iterate Picard joint `C²`
(`hu_c2`), the global positivity floor inputs, and the still-open closed-slab
continuity `htime_cont` of the flux mixed time-derivative lift. -/
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
        ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      ContinuousOn
        (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)) :
    CoupledChemDivFluxFactorJointC2Inputs p u := by
  have hbase : ∀ s x : ℝ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x :=
    fun s x => coupledChemical_floor_pos_of_nonneg_continuous hu_cont hu_nonneg s x
  refine coupledChemDivFluxFactorJointC2Inputs_of_physical H (fun τ => ?_)
  rcases other τ with ⟨δ, hδ, hsrc, hu_c2, htime_cont⟩
  refine ⟨δ, hδ, hsrc, (fun x hx s _ => hu_c2 x hx s),
    (fun x _ s _ => hbase s x), (fun x hx s _ => ?_), htime_cont⟩
  exact coupledChemDivFlux_timeBridge_of_physicalJointC2 H hu_c2 hbase hx

end ShenWork.IntervalCoupledRegularityBootstrap
