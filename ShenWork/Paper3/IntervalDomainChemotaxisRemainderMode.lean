/- Exact modal form of the quadratic-and-higher chemotaxis remainder. -/
import ShenWork.Paper3.IntervalDomainLinearChemMode

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalDomain
open ShenWork.IntervalConjugateCosineSeries

noncomputable section

def paper3LinearChemFluxProfile
    (p : CM2Params) (uStar vStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  uStar ^ p.m * paper3SensitivityFactor p.β vStar *
    paper3LinearSignalGradient p uStar u x

def paper3ChemFluxRemainderProfileM
    (p : CM2Params) (uStar vStar : ℝ)
    (u v : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  intervalFluxM p u v x -
    paper3LinearChemFluxProfile p uStar vStar u x

lemma intervalSineInner_sub_p3
    {f g : ℝ → ℝ} (k : ℕ)
    (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    intervalSineInner (fun x => f x - g x) k =
      intervalSineInner f k - intervalSineInner g k := by
  unfold intervalSineInner
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk, if_neg hk, if_neg hk]
    have hsin : ContinuousOn
        (fun x : ℝ => Real.sin ((k : ℝ) * Real.pi * x))
        (Set.uIcc (0 : ℝ) 1) := by fun_prop
    have hfi : IntervalIntegrable
        (fun x => Real.sin ((k : ℝ) * Real.pi * x) * f x)
        volume 0 1 := hf.continuousOn_mul hsin
    have hgi : IntervalIntegrable
        (fun x => Real.sin ((k : ℝ) * Real.pi * x) * g x)
        volume 0 1 := hg.continuousOn_mul hsin
    rw [show (∫ x in (0 : ℝ)..1,
        Real.sin ((k : ℝ) * Real.pi * x) * (f x - g x)) =
      (∫ x in (0 : ℝ)..1,
        Real.sin ((k : ℝ) * Real.pi * x) * f x) -
      (∫ x in (0 : ℝ)..1,
        Real.sin ((k : ℝ) * Real.pi * x) * g x) by
      rw [← intervalIntegral.integral_sub hfi hgi]
      apply intervalIntegral.integral_congr
      intro x _
      ring]
    ring

/-- After removal of the complete diagonal linear multiplier, the chemotaxis
modal remainder is exactly the divergence coefficient of the nonlinear flux
remainder. -/
theorem paper3ChemotaxisRemainderCoeffM_eq_fluxRemainder
    (p : CM2Params) (hm : p.m = 1)
    {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (u v : ℝ → intervalDomainPoint → ℝ) (t : ℝ) (k : ℕ)
    (hUcont : ContinuousOn (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1))
    (hsource_lin : Summable fun n : ℕ =>
      (paper3LinearEllipticSourceCoeffReal p uStar (u t) n) ^ 2)
    (hflux : IntervalIntegrable (intervalFluxM p (u t) (v t)) volume 0 1)
    (hlinear : IntervalIntegrable
      (paper3LinearChemFluxProfile p uStar vStar (u t)) volume 0 1) :
    paper3ChemotaxisRemainderCoeffM
        p uStar vStar u v t k =
      -p.χ₀ * (((k : ℝ) * Real.pi) *
        intervalSineInner
          (paper3ChemFluxRemainderProfileM
            p uStar vStar (u t) (v t)) k) := by
  have hlinMode := paper3LinearChemFlux_mode_eq_growthCorrection
    p hm heq u t k hUcont hsource_lin
  unfold paper3ChemotaxisRemainderCoeffM
  rw [← hlinMode]
  unfold paper3ChemFluxRemainderProfileM
  rw [intervalSineInner_sub_p3 k hflux hlinear]
  unfold paper3LinearChemFluxProfile
  ring

#print axioms intervalSineInner_sub_p3
#print axioms paper3ChemotaxisRemainderCoeffM_eq_fluxRemainder

end

end ShenWork.Paper3
