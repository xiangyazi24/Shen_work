import ShenWork.PDE.IntervalChemDivOuterCommuteProducer

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.IntervalMildSourceDecayHelper
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Product/quotient/rpow calculus for the lifted chem-div flux.

This is the formal algebraic step in the route: once the three factors
`u`, `v`, and `∂ₓv` are jointly regular at `(s, x)`, positivity of `1 + v`
keeps the rpow denominator away from zero, and `ContDiffAt.mul`/
`ContDiffAt.div`/`ContDiffAt.rpow_const_of_ne` produce joint `C²` of the
uncurried flux. -/
theorem coupledChemDivFlux_contDiffAt_of_factorJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x))
    (hgradv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
          q.2)
      (s, x))
    (hbase : 0 <
      1 + intervalDomainLift (coupledChemicalConcentration p u s) x) :
    ContDiffAt ℝ 2
      (Function.uncurry (coupledChemDivFluxLift p u)) (s, x) := by
  have hbase_fun : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        1 + intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x) := by
    simpa using (contDiffAt_const (c := (1 : ℝ))).add hv
  have hden : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        (1 + intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
          ^ p.β)
      (s, x) :=
    hbase_fun.rpow_const_of_ne (ne_of_gt hbase)
  have hden_ne :
      (1 + intervalDomainLift (coupledChemicalConcentration p u s) x) ^
          p.β ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hbase p.β)
  have hquot := (hu.mul hgradv).div hden hden_ne
  simpa [coupledChemDivFluxLift, Function.uncurry] using hquot

/-- A joint Fréchet derivative identifies the spatial derivative of a fixed-time
slice with the `(0, 1)` directional derivative. -/
theorem real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
    {F : ℝ × ℝ → ℝ} {s x : ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun y : ℝ => F (s, y)) x =
      fderiv ℝ F (s, x) (0, 1) := by
  have hpath : HasDerivAt (fun y : ℝ => (s, y)) (0, 1) x := by
    simpa using
      (HasDerivAt.prodMk (hasDerivAt_const x s) (hasDerivAt_id x))
  have hcomp : HasDerivAt (fun y : ℝ => F (s, y))
      (fderiv ℝ F (s, x) (0, 1)) x := by
    simpa [Function.comp_def] using hF.hasFDerivAt.comp_hasDerivAt x hpath
  exact hcomp.deriv

/-- Factor-level, non-circular inputs for the lifted chem-div flux joint `C²`
producer.

The factor fields are the exact remaining analytic targets: joint `C²` of the
lifted `u`, joint `C²` of the resolver value `v`, joint `C²` of the gradient
factor `∂ₓv`, and positivity of `1 + v`.  The currently committed resolver API
only exposes joint continuity of `v` and `∂ₜv`, plus fixed-time spatial `C²`, so
this package records the satisfiable factor targets without assuming the outer
commute atom, the source coefficient derivative, or `DuhamelSourceTimeC1`. -/
structure CoupledChemDivFluxFactorJointC2Inputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      MeasureTheory.IntervalIntegrable (coupledChemDivSourceLift p u s)
        MeasureTheory.volume (0 : ℝ) 1) ∧
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
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

/-- Produce the primitive joint-`C²` flux package from the factor-level local
slab inputs.

The named intermediate facts mirror the intended proof once the resolver-side
joint `ContDiffAt` theorem is committed: product, quotient, and rpow calculus
feed `hflux_joint_c2_from_product_quotient_rpow`, while the two partial bridges
are passed to the existing Clairaut bridge in
`coupledChemDivOuterCommuteAtoms_of_fluxJointC2`. -/
theorem coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorJointC2Inputs p u) :
    CoupledChemDivFluxJointC2Hyp p u := by
  refine ⟨fun τ => ?_⟩
  rcases H.exists_local_slab τ with
    ⟨δ, hδ, hsource_cont, hu_c2, hv_c2, hgradv_c2, hbase,
      htime, htime_cont⟩
  have hsource_cont_slab :
      ∀ᶠ s in 𝓝 τ,
        MeasureTheory.IntervalIntegrable (coupledChemDivSourceLift p u s)
          MeasureTheory.volume (0 : ℝ) 1 :=
    hsource_cont
  have hflux_joint_c2_from_product_quotient_rpow :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        ContDiffAt ℝ 2
          (Function.uncurry (coupledChemDivFluxLift p u)) (s, x) :=
    fun x hx s hs =>
      coupledChemDivFlux_contDiffAt_of_factorJointC2
        (hu_c2 x hx s hs) (hv_c2 x hx s hs) (hgradv_c2 x hx s hs)
        (hbase x hx s hs)
  have hspatial_deriv_fderiv_bridge :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        (fun r : ℝ => deriv (coupledChemDivFluxLift p u r) x) =ᶠ[𝓝 s]
          (fun r : ℝ =>
            fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
              (r, x) (0, 1)) :=
    fun x hx s hs => by
      have hball_nhds : Metric.ball τ δ ∈ 𝓝 s :=
        Metric.isOpen_ball.mem_nhds hs
      filter_upwards [hball_nhds] with r hr
      have hflux_r : ContDiffAt ℝ 2
          (Function.uncurry (coupledChemDivFluxLift p u)) (r, x) :=
        coupledChemDivFlux_contDiffAt_of_factorJointC2
          (hu_c2 x hx r hr) (hv_c2 x hx r hr) (hgradv_c2 x hx r hr)
          (hbase x hx r hr)
      have hdiff_r :
          DifferentiableAt ℝ
            (Function.uncurry (coupledChemDivFluxLift p u)) (r, x) :=
        hflux_r.differentiableAt (by norm_num)
      simpa [Function.uncurry] using
        real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt hdiff_r
  have htime_deriv_fderiv_bridge :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
          (fun y : ℝ =>
            fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
              (s, y) (1, 0)) :=
    htime
  have htime_derivative_continuous :
      ContinuousOn
        (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    htime_cont
  exact
    ⟨δ, hδ, hsource_cont_slab,
      hflux_joint_c2_from_product_quotient_rpow,
      hspatial_deriv_fderiv_bridge,
      htime_deriv_fderiv_bridge,
      htime_derivative_continuous⟩

/-- Direct outer-commute atoms from the factor-level joint flux inputs. -/
theorem coupledChemDivOuterCommuteAtoms_of_factorJointC2Inputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxFactorJointC2Inputs p u) :
    CoupledChemDivOuterCommuteAtoms p u :=
  coupledChemDivOuterCommuteAtoms_of_fluxJointC2
    (coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs H)

/-- Direct source-time-`C¹` wiring from the factor-level joint flux inputs. -/
noncomputable def coupledChemDivSource_timeC1_of_factorJointC2Inputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (Cchem : ℝ) (hCchem : 0 ≤ Cchem)
    (hH2 : ∀ s, 0 ≤ s →
      IntervalWeakH2Neumann (coupledChemDivSourceLift p u s))
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (coupledChemDivSourceLift p u s) k|
        ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2)
    (hzero : ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem)
    (H : CoupledChemDivFluxFactorJointC2Inputs p u)
    (hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n))
    (MchemDot : ℝ)
    (hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) :=
  coupledChemDivSource_timeC1_of_fluxJointC2
    Cchem hCchem hH2 hdecay hzero
    (coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs H)
    hadotcont MchemDot hMdot

end ShenWork.IntervalCoupledRegularityBootstrap
