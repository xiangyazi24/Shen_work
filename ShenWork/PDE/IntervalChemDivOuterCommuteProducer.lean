import ShenWork.PDE.IntervalChemDivOuterCommute
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.IntervalMildSourceDecayHelper
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Time derivative of the spatial Fréchet partial for a real two-variable
function, extracted from pointwise joint `C²`. -/
theorem real_twoVar_hasDerivAt_time_fderiv_spatial_of_contDiffAt
    (F : ℝ × ℝ → ℝ) (s x : ℝ)
    (hf : ContDiffAt ℝ 2 F (s, x)) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ F (r, x) (0, 1))
      ((fderiv ℝ (fderiv ℝ F) (s, x) (1, 0)) (0, 1)) s := by
  have hFderivDiff : DifferentiableAt ℝ (fderiv ℝ F) (s, x) := by
    exact
      (hf.fderiv_right (m := 1) (n := 2) (by norm_num)).differentiableAt
        (by norm_num)
  have hFderiv : HasFDerivAt (fderiv ℝ F)
      (fderiv ℝ (fderiv ℝ F) (s, x)) (s, x) :=
    hFderivDiff.hasFDerivAt
  have hpath : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) s := by
    simpa using
      (HasDerivAt.prodMk (hasDerivAt_id s) (hasDerivAt_const s x))
  have hcomp : HasDerivAt (fun r : ℝ => fderiv ℝ F (r, x))
      (fderiv ℝ (fderiv ℝ F) (s, x) (1, 0)) s := by
    simpa [Function.comp_def] using hFderiv.comp_hasDerivAt s hpath
  let ex : ℝ × ℝ := (0, 1)
  let evalEx : (ℝ × ℝ →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ) ex
  have heval : HasFDerivAt (fun L : ℝ × ℝ →L[ℝ] ℝ => L ex) evalEx
      (fderiv ℝ F (s, x)) := by
    simpa [evalEx] using evalEx.hasFDerivAt
  have hout : HasDerivAt
      ((fun L : ℝ × ℝ →L[ℝ] ℝ => L ex) ∘
        fun r : ℝ => fderiv ℝ F (r, x))
      (evalEx (fderiv ℝ (fderiv ℝ F) (s, x) (1, 0))) s :=
    heval.comp_hasDerivAt s hcomp
  simpa [Function.comp_def, ex, evalEx] using hout

/-- Spatial derivative of the time Fréchet partial for a real two-variable
function, extracted from pointwise joint `C²`. -/
theorem real_twoVar_hasDerivAt_space_fderiv_time_of_contDiffAt
    (F : ℝ × ℝ → ℝ) (s x : ℝ)
    (hf : ContDiffAt ℝ 2 F (s, x)) :
    HasDerivAt
      (fun y : ℝ => fderiv ℝ F (s, y) (1, 0))
      ((fderiv ℝ (fderiv ℝ F) (s, x) (0, 1)) (1, 0)) x := by
  have hFderivDiff : DifferentiableAt ℝ (fderiv ℝ F) (s, x) := by
    exact
      (hf.fderiv_right (m := 1) (n := 2) (by norm_num)).differentiableAt
        (by norm_num)
  have hFderiv : HasFDerivAt (fderiv ℝ F)
      (fderiv ℝ (fderiv ℝ F) (s, x)) (s, x) :=
    hFderivDiff.hasFDerivAt
  have hpath : HasDerivAt (fun y : ℝ => (s, y)) (0, 1) x := by
    simpa using
      (HasDerivAt.prodMk (hasDerivAt_const x s) (hasDerivAt_id x))
  have hcomp : HasDerivAt (fun y : ℝ => fderiv ℝ F (s, y))
      (fderiv ℝ (fderiv ℝ F) (s, x) (0, 1)) x := by
    simpa [Function.comp_def] using hFderiv.comp_hasDerivAt x hpath
  let et : ℝ × ℝ := (1, 0)
  let evalEt : (ℝ × ℝ →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ) et
  have heval : HasFDerivAt (fun L : ℝ × ℝ →L[ℝ] ℝ => L et) evalEt
      (fderiv ℝ F (s, x)) := by
    simpa [evalEt] using evalEt.hasFDerivAt
  have hout : HasDerivAt
      ((fun L : ℝ × ℝ →L[ℝ] ℝ => L et) ∘
        fun y : ℝ => fderiv ℝ F (s, y))
      (evalEt (fderiv ℝ (fderiv ℝ F) (s, x) (0, 1))) x :=
    heval.comp_hasDerivAt x hcomp
  simpa [Function.comp_def, et, evalEt] using hout

/-- Clairaut bridge from joint `C²` and one-fold partial identifications to the
iterated `deriv` shape used by the chem-div outer-commute atom. -/
theorem real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
    {F Ft : ℝ → ℝ → ℝ} {s x : ℝ}
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (s, x))
    (hspatial :
      (fun r : ℝ => deriv (F r) x) =ᶠ[𝓝 s]
        (fun r : ℝ => fderiv ℝ (Function.uncurry F) (r, x) (0, 1)))
    (htime :
      (fun y : ℝ => Ft s y) =ᶠ[𝓝 x]
        (fun y : ℝ => fderiv ℝ (Function.uncurry F) (s, y) (1, 0))) :
    HasDerivAt (fun r : ℝ => deriv (F r) x) (deriv (Ft s) x) s := by
  let Fu : ℝ × ℝ → ℝ := Function.uncurry F
  let A : ℝ := (fderiv ℝ (fderiv ℝ Fu) (s, x) (1, 0)) (0, 1)
  let B : ℝ := (fderiv ℝ (fderiv ℝ Fu) (s, x) (0, 1)) (1, 0)
  have hbase : HasDerivAt
      (fun r : ℝ => fderiv ℝ Fu (r, x) (0, 1)) A s := by
    simpa [Fu, A] using
      real_twoVar_hasDerivAt_time_fderiv_spatial_of_contDiffAt
        Fu s x (by simpa [Fu] using hF)
  have hspace_time : HasDerivAt
      (fun y : ℝ => fderiv ℝ Fu (s, y) (1, 0)) B x := by
    simpa [Fu, B] using
      real_twoVar_hasDerivAt_space_fderiv_time_of_contDiffAt
        Fu s x (by simpa [Fu] using hF)
  have hsymm : A = B := by
    simpa [Fu, A, B] using
      (hF.isSymmSndFDerivAt (by norm_num)).eq (1, 0) (0, 1)
  have hFt : HasDerivAt (Ft s) B x := by
    exact hspace_time.congr_of_eventuallyEq (by simpa [Fu] using htime)
  have hderivFt : deriv (Ft s) x = B := hFt.deriv
  have hout : HasDerivAt (fun r : ℝ => deriv (F r) x) A s := by
    exact hbase.congr_of_eventuallyEq (by simpa [Fu] using hspatial)
  rw [hderivFt, ← hsymm]
  exact hout

/-- Primitive, non-circular regularity package for the outer chem-div commute.

The intended producer is the joint `C²` regularity of the lifted flux
`(t, x) ↦ coupledChemDivFluxLift p u t x`, together with the already-wired
identification of its time derivative with
`coupledChemDivFluxTimeDerivativeLift p u`.  This package deliberately does not
assume `CoupledChemDivOuterCommuteAtoms`, `CoupledChemDivLocalChainRule`, any
source `HasDerivAt`, or `DuhamelSourceTimeC1`. -/
structure CoupledChemDivFluxJointC2Hyp
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      IntervalIntegrable (coupledChemDivSourceLift p u s)
        MeasureTheory.volume (0 : ℝ) 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun r : ℝ => deriv (coupledChemDivFluxLift p u r) x) =ᶠ[𝓝 s]
        (fun r : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (r, x) (0, 1))) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

/-- Discharge the outer-commute atom package from the primitive joint-regularity
bridge for the lifted flux. -/
theorem coupledChemDivOuterCommuteAtoms_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivOuterCommuteAtoms p u := by
  refine ⟨fun τ => ?_⟩
  rcases H.exists_local_slab τ with
    ⟨δ, hδ, hsource_cont, hflux_c2, hspatial, htime, htime_cont⟩
  have hsource_cont_slab :
      ∀ᶠ s in 𝓝 τ,
        IntervalIntegrable (coupledChemDivSourceLift p u s)
          MeasureTheory.volume (0 : ℝ) 1 :=
    hsource_cont
  have houter_commute :
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
        HasDerivAt
          (fun r => deriv (coupledChemDivFluxLift p u r) x)
          (deriv (coupledChemDivFluxTimeDerivativeLift p u s) x) s :=
    fun x hx s hs =>
      real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
        (F := coupledChemDivFluxLift p u)
        (Ft := coupledChemDivFluxTimeDerivativeLift p u)
        (hflux_c2 x hx s hs) (hspatial x hx s hs) (htime x hx s hs)
  have htime_deriv_cont :
      ContinuousOn
        (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
        (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    htime_cont
  exact ⟨δ, hδ, hsource_cont_slab, houter_commute, htime_deriv_cont⟩

/-- Local chain-rule package obtained directly from the primitive joint-`C²`
flux regularity package. -/
theorem coupledChemDivLocalChainRule_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivLocalChainRule p u :=
  coupledChemDivLocalChainRule_of_outerCommuteAtoms
    (coupledChemDivOuterCommuteAtoms_of_fluxJointC2 H)

/-- Direct source-time-C¹ wiring from the primitive joint-`C²` flux package. -/
noncomputable def coupledChemDivSource_timeC1_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (Cchem : ℝ) (hCchem : 0 ≤ Cchem)
    (hH2 : ∀ s, 0 ≤ s →
      IntervalWeakH2Neumann (coupledChemDivSourceLift p u s))
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (coupledChemDivSourceLift p u s) k|
        ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2)
    (hzero : ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem)
    (H : CoupledChemDivFluxJointC2Hyp p u)
    (hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n))
    (MchemDot : ℝ)
    (hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) :=
  coupledChemDivSource_timeC1_of_outerCommuteAtoms
    Cchem hCchem hH2 hdecay hzero
    (coupledChemDivOuterCommuteAtoms_of_fluxJointC2 H)
    hadotcont MchemDot hMdot

end ShenWork.IntervalCoupledRegularityBootstrap
