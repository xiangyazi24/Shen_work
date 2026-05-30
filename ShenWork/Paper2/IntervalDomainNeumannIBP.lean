/-
  ShenWork/Paper2/IntervalDomainNeumannIBP.lean

  **T4 — genuine spatial Neumann integration by parts on `[0,1]`.**

  Discharges the `hIBP` frontier of the Paper-2 energy chain
  (`IntervalDomainEnergyStep`): the spatial integration-by-parts identity

    `∫₀¹ test·Δf  =  boundaryTerm(test,f) − ∫₀¹ test'·f'`

  for the lifted interval functions, where `Δf = (lift f)''` and the boundary
  term is `intervalDomainNeumannBoundaryTerm` built from the **genuine one-sided**
  `intervalDomainNormalDeriv` (T3).  This is the honest analytic IBP, proved from
  Mathlib's `integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right` (right-derivative
  form, which handles the lift's endpoint kink cleanly) plus the product-lift and
  derivative-pair bridges.

  The hypotheses package the `C²`-up-to-boundary regularity of the lift (the T5
  frontier) and the boundary identification `deriv (lift f) {0,1} = normalDeriv f
  {left,right}` (continuity of the first derivative up to the boundary).  No
  Neumann assumption is used here — this is the *pure* IBP identity, exactly the
  `hIBP` frontier shape; the boundary term is separately killed by T3's genuine
  Neumann condition in the energy chain.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainEnergyStep
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Set
open scoped Topology Interval

namespace ShenWork.Paper2.IntervalDomainEnergyStep

open ShenWork.IntervalDomain

/-- **Genuine spatial Neumann integration by parts** discharging the `hIBP`
frontier.  Given the `C²`-up-to-boundary regularity of the lifted interval
functions (right-derivatives in the interior, continuity of `lift test` and of
`deriv (lift f)` on `[0,1]`, interval-integrable derivatives) and the boundary
identification of `deriv (lift f)` at the endpoints with the genuine one-sided
`intervalDomainNormalDeriv`, the spatial integration-by-parts identity holds:

  `∫₀¹ test·Δf = intervalDomainNeumannBoundaryTerm test f − ∫₀¹ test'·f'`. -/
theorem intervalDomain_spatial_integrationByParts_identity
    (test f : intervalDomain.Point → ℝ)
    (htest_cont : ContinuousOn (intervalDomainLift test) (Set.Icc 0 1))
    (hf1_cont : ContinuousOn (deriv (intervalDomainLift f)) (Set.Icc 0 1))
    (htest_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (intervalDomainLift test)
        (deriv (intervalDomainLift test) x) (Set.Ioi x) x)
    (hf_deriv2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (deriv (intervalDomainLift f))
        (deriv (deriv (intervalDomainLift f)) x) (Set.Ioi x) x)
    (htest1_int :
      IntervalIntegrable (deriv (intervalDomainLift test)) volume 0 1)
    (hf2_int :
      IntervalIntegrable (deriv (deriv (intervalDomainLift f))) volume 0 1)
    (hbdryR :
      deriv (intervalDomainLift f) 1 =
        intervalDomain.normalDeriv f intervalDomainRightEndpoint)
    (hbdryL :
      deriv (intervalDomainLift f) 0 =
        intervalDomain.normalDeriv f intervalDomainLeftEndpoint) :
    intervalDomain.integral (fun x => test x * intervalDomain.laplacian f x) =
      intervalDomainNeumannBoundaryTerm test f -
        intervalDomainDerivativePairIntegral test f := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le h01
  -- Mathlib integration by parts (right-derivative form).
  have hIBP :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
      (u := intervalDomainLift test) (v := deriv (intervalDomainLift f))
      (u' := deriv (intervalDomainLift test))
      (v' := deriv (deriv (intervalDomainLift f)))
      (a := 0) (b := 1)
      (by rw [huIcc]; exact htest_cont)
      (by rw [huIcc]; exact hf1_cont)
      (by rw [min_eq_left h01, max_eq_right h01]; exact htest_deriv)
      (by rw [min_eq_left h01, max_eq_right h01]; exact hf_deriv2)
      htest1_int hf2_int
  -- LHS bridge: the domain integral of `test·Δf` is the parametric integral.
  have hLHS :
      intervalDomain.integral (fun x => test x * intervalDomain.laplacian f x) =
        ∫ y in (0 : ℝ)..1,
          intervalDomainLift test y * deriv (deriv (intervalDomainLift f)) y := by
    show intervalDomainIntegral (fun x => test x * intervalDomainLaplacian f x) = _
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr ?_
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := huIcc ▸ hy
    simp only [intervalDomainLift, intervalDomainLaplacian, dif_pos hy']
  -- Boundary bridge: the IBP boundary term is `intervalDomainNeumannBoundaryTerm`.
  have e1 : intervalDomainLift test 1 = test intervalDomainRightEndpoint := by
    simp only [intervalDomainLift,
      dif_pos (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]
    rfl
  have e0 : intervalDomainLift test 0 = test intervalDomainLeftEndpoint := by
    simp only [intervalDomainLift,
      dif_pos (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)]
    rfl
  have hbdry :
      intervalDomainLift test 1 * deriv (intervalDomainLift f) 1 -
          intervalDomainLift test 0 * deriv (intervalDomainLift f) 0 =
        intervalDomainNeumannBoundaryTerm test f := by
    unfold intervalDomainNeumannBoundaryTerm
    rw [hbdryR, hbdryL, e1, e0]
  -- Pair bridge: the remaining integral is the derivative-pair dissipation.
  have hPair :
      (∫ x in (0 : ℝ)..1,
          deriv (intervalDomainLift test) x * deriv (intervalDomainLift f) x) =
        intervalDomainDerivativePairIntegral test f := rfl
  rw [hLHS, hIBP, hbdry, hPair]

end ShenWork.Paper2.IntervalDomainEnergyStep
