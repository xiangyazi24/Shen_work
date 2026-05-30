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

/-- **L2 energy differential inequality with the Neumann IBP genuinely
discharged.**  Specialising the `_of_frontiers` chain top to `f = test = u t`,
the spatial integration-by-parts frontier `hIBP` is supplied by
`intervalDomain_spatial_integrationByParts_identity` (T4-a) and the Neumann
boundary frontier `hNeuR`/`hNeuL` by the genuine solution's `hsol.neumann` (T3).

What remains conditional is exactly the honest analytic frontier set: the
`C²`-up-to-boundary regularity of `u t` (= T5), the time-derivative chain rule
`hL2Time`, the PDE substitution under the integral `hPDEIntegral`, and the
cross-diffusion controls.  The energy inequality
`E'(t) + dissipation ≤ χ·(ε·gradDiss + C·∫u^{2+ρ}) + logistic` then holds. -/
theorem intervalDomain_l2_half_energy_inequality_of_regularity
    {params : CM2Params} {T rho eps chiBound t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (heps : 0 < eps) (hchiBound : 0 ≤ chiBound)
    (ht0 : 0 < t) (htT : t < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hL2Time :
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t =
        intervalDomain.integral (intervalDomainL2TimeTerm u t))
    (hPDEIntegral :
      intervalDomain.integral (intervalDomainL2TimeTerm u t) =
        intervalDomainL2DiffusionIntegral u t -
          params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
          intervalDomainL2LogisticIntegral params u t)
    -- C²-up-to-boundary regularity of `u t` (the T5 frontier):
    (hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc 0 1))
    (hf1_cont : ContinuousOn (deriv (intervalDomainLift (u t))) (Set.Icc 0 1))
    (hf_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (intervalDomainLift (u t))
        (deriv (intervalDomainLift (u t)) x) (Set.Ioi x) x)
    (hf_deriv2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (deriv (intervalDomainLift (u t)))
        (deriv (deriv (intervalDomainLift (u t))) x) (Set.Ioi x) x)
    (hf1_int :
      IntervalIntegrable (deriv (intervalDomainLift (u t))) volume 0 1)
    (hf2_int :
      IntervalIntegrable (deriv (deriv (intervalDomainLift (u t)))) volume 0 1)
    (hbdryR :
      deriv (intervalDomainLift (u t)) 1 =
        intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint)
    (hbdryL :
      deriv (intervalDomainLift (u t)) 0 =
        intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint)
    (hCrossControl :
      -params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t ≤
        chiBound *
          intervalDomain.crossDiffusionEnergyTerm params 2 (u t) (v t)) :
    ∃ Ceps,
      deriv (fun τ => intervalDomainL2HalfEnergy u τ) t +
          intervalDomainL2DiffusionDissipation u t ≤
        chiBound *
            (eps * intervalDomainLpWeightedGradientDissipation 2 u t +
              Ceps *
                intervalDomain.integral (fun x => (u t x) ^ (2 + rho))) +
          intervalDomainL2LogisticIntegral params u t := by
  -- Neumann BC from the genuine classical solution (T3).
  have hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_rightEndpoint_mem_boundary).1
  have hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_leftEndpoint_mem_boundary).1
  -- Spatial Neumann IBP from T4-a, specialised to `test = f = u t`.  The result
  -- is definitionally the `hIBP` frontier shape for the L2 diffusion integral.
  have hIBP :
      intervalDomainL2DiffusionIntegral u t =
        intervalDomainNeumannBoundaryTerm (u t) (u t) -
          intervalDomainL2DiffusionDissipation u t :=
    intervalDomain_spatial_integrationByParts_identity (u t) (u t)
      hcont hf1_cont hf_deriv hf_deriv2 hf1_int hf2_int hbdryR hbdryL
  exact intervalDomain_l2_half_energy_cross_bootstrap_inequality_of_frontiers
    heps hchiBound ht0 htT hcross hL2Time hPDEIntegral hIBP hNeuR hNeuL hCrossControl

end ShenWork.Paper2.IntervalDomainEnergyStep
