/- General-`m` exact modal form of the chemotaxis flux remainder. -/
import ShenWork.Paper3.IntervalDomainLinearChemModeGeneralM
import ShenWork.Paper3.IntervalDomainChemotaxisRemainderMode

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator
open ShenWork.Paper2.IntervalDomainM
open ShenWork.IntervalDomain
open ShenWork.IntervalConjugateCosineSeries

noncomputable section

/-- After subtracting the paper-faithful general-`m` linear multiplier, the
chemotaxis modal remainder is exactly the divergence coefficient of the
physical general-`m` flux remainder. -/
theorem paper3ChemotaxisRemainderCoeffM_eq_fluxRemainder_generalM
    (p : CM2Params)
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
  have hlinMode := paper3LinearChemFlux_mode_eq_growthCorrection_generalM
    p heq u t k hUcont hsource_lin
  unfold paper3ChemotaxisRemainderCoeffM
  rw [← hlinMode]
  unfold paper3ChemFluxRemainderProfileM
  rw [intervalSineInner_sub_p3 k hflux hlinear]
  unfold paper3LinearChemFluxProfile
  ring

#print axioms paper3ChemotaxisRemainderCoeffM_eq_fluxRemainder_generalM

end


end ShenWork.Paper3
