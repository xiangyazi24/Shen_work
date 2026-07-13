/- Positive-time integrability of the differentiated nonlinear flux remainder. -/
import ShenWork.Paper3.IntervalDomainPhysicalFluxDerivativeRouteA
import ShenWork.Paper3.IntervalDomainL2ProductBounds

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

private theorem intervalIntegrable_congr_Ioo
    {f g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1)
    (heq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x = g x) :
    IntervalIntegrable f volume 0 1 := by
  refine hg.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hrestrict : volume.restrict (Set.Ioc (0 : ℝ) 1) =
      volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hrestrict]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (heq x hx).symm

/-- Once the linear signal laplacian is in `L²`, the exact physical flux
remainder has an interval-integrable derivative.  This closes the qualitative
integrability premise used by the modal route-(a) identification. -/
theorem paper3ChemFluxRemainder_deriv_intervalIntegrable
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hm : p.m = 1)
    (Hlin : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u t)))
    (hz1xx : MemLp (paper3LinearSignalLaplacian p uStar (u t)) 2
      (intervalMeasure 1)) :
    IntervalIntegrable
      (deriv (paper3ChemFluxRemainderProfileM
        p uStar vStar (u t) (v t))) volume 0 1 := by
  let z1xx : ℝ → ℝ := paper3LinearSignalLaplacian p uStar (u t)
  let c : ℝ := uStar * paper3SensitivityFactor p.β vStar
  let linFlux : ℝ → ℝ := paper3LinearChemFluxProfile p uStar vStar (u t)
  let fullFlux : ℝ → ℝ :=
    ShenWork.Paper2.IntervalDomainM.intervalFluxM p (u t) (v t)
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  have hfullInt : IntervalIntegrable (deriv fullFlux) volume 0 1 := by
    simpa [fullFlux] using
      ShenWork.Paper2.IntervalDomainM.deriv_fluxM_intervalIntegrable
        hsolM ht.1 ht.2
  have hz1Int : IntervalIntegrable z1xx volume 0 1 := by
    simpa [z1xx] using
      ShenWork.Paper3.MemLp.intervalIntegrable_two_unit hz1xx
  have hlinModelInt : IntervalIntegrable (fun x => c * z1xx x) volume 0 1 :=
    hz1Int.const_mul c
  have hlinHas : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt linFlux (c * z1xx x) x := by
    intro x hx
    have hz := paper3LinearSignalGradient_hasDerivAt_laplacian
      p uStar (u t) Hlin hx
    have hscaled := hz.const_mul c
    change HasDerivAt
      (fun y => uStar ^ p.m * paper3SensitivityFactor p.β vStar *
        paper3LinearSignalGradient p uStar (u t) y)
      (c * z1xx x) x
    rw [hm, Real.rpow_one]
    simpa [c, z1xx] using hscaled
  have hlinInt : IntervalIntegrable (deriv linFlux) volume 0 1 :=
    intervalIntegrable_congr_Ioo hlinModelInt
      (fun x hx => (hlinHas x hx).deriv)
  have hmodelInt : IntervalIntegrable
      (fun x => deriv fullFlux x - deriv linFlux x) volume 0 1 :=
    hfullInt.sub hlinInt
  apply intervalIntegrable_congr_Ioo hmodelInt
  intro x hx
  have hfullDiff : DifferentiableAt ℝ fullFlux x := by
    have hC1 := ShenWork.Paper2.IntervalDomainM.fluxM_contDiffOn_Icc
      hsolM ht.1 ht.2
    exact (hC1.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx)
        Set.Ioo_subset_Icc_self)
  have hrem := hfullDiff.hasDerivAt.sub (hlinHas x hx)
  have hlinDeriv := (hlinHas x hx).deriv
  rw [hlinDeriv]
  simpa [paper3ChemFluxRemainderProfileM, fullFlux, linFlux] using hrem.deriv

#print axioms paper3ChemFluxRemainder_deriv_intervalIntegrable

end

end ShenWork.Paper3
