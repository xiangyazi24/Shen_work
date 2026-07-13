import ShenWork.Paper3.IntervalDomainEntropyTimeDerivative
import ShenWork.Paper3.IntervalDomainModelLinearizationAudit

/-!
# Exact entropy-production identity for the faithful interval equation

At `m = 1`, the entropy test `1 - uStar/u` is the difference of the
standard weighted `L^p` tests at exponents `p = 1` and `p = 0`.  This file
uses the already-proved faithful weighted-PDE identities at those two
exponents.  Thus no spatial integration-by-parts argument is duplicated.
-/

open ShenWork.IntervalDomain MeasureTheory Set
open scoped Topology Interval

namespace ShenWork.Paper3

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep

theorem entropyLpTest_one {U : ℝ} (hU : 0 < U) :
    |U| ^ ((1 : ℝ) - 2) * U = 1 := by
  rw [abs_of_pos hU]
  norm_num [Real.rpow_neg_one]
  exact inv_mul_cancel₀ hU.ne'

theorem entropyLpTest_zero {U : ℝ} (hU : 0 < U) :
    |U| ^ ((0 : ℝ) - 2) * U = 1 / U := by
  rw [abs_of_pos hU]
  norm_num
  field_simp [hU.ne']

/-- The entropy weighted-time term is the difference of the `p=1` and
`p=0` weighted `L^p` time terms. -/
theorem intervalDomain_entropyTimeTerm_eq_lp_one_sub_zero
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) =
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm 1 u t) -
        uStar * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm 0 u t) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let Ut : ℝ → ℝ :=
    ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u t
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using
      (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hUtJoint : ContinuousOn
      (Function.uncurry
        (ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.1.1
  have hUtcont : ContinuousOn Ut (Set.Icc (0 : ℝ) 1) := by
    simpa [Ut] using
      ShenWork.Paper2.intervalDomain_continuousOn_timeSlice hUtJoint ht
  have hUpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < U y := by
    intro y hy
    simpa [U, intervalDomainLift, hy] using
      hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomain.Point)) ht0 htT
  have hUt_eq (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      Ut y = intervalDomain.timeDeriv u t ⟨y, hy⟩ := by
    dsimp [Ut]
    unfold ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand
    have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r ⟨y, hy⟩ := by
      intro r
      simp [intervalDomainLift, hy]
    rw [show (fun r : ℝ => intervalDomainLift (u r) y) =
      fun r => u r ⟨y, hy⟩ from funext hlift]
    rfl
  have htestCont (q : ℝ) : ContinuousOn
      (fun y => U y ^ (q - 2) * U y * Ut y) (Set.Icc (0 : ℝ) 1) :=
    (((hUcont.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))).mul hUcont).mul hUtcont)
  have hleftCont : ContinuousOn
      (fun y => (1 - uStar / U y) * Ut y) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_const.sub
      (continuousOn_const.div hUcont
        (fun y hy => ne_of_gt (hUpos y hy)))).mul hUtcont
  have hleftLiftCont : ContinuousOn
      (intervalDomainLift (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x))
      (Set.Icc (0 : ℝ) 1) := by
    refine hleftCont.congr ?_
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    rw [hUt_eq y hy]
    simp [U, intervalDomainLift, hy]
  have hlpLiftCont (q : ℝ) : ContinuousOn
      (intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm q u t))
      (Set.Icc (0 : ℝ) 1) := by
    refine (htestCont q).congr ?_
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos,
      intervalDomainLpEnergyWeightedTimeTerm]
    rw [hUt_eq y hy]
    have huPos : 0 < u t ⟨y, hy⟩ := by
      simpa [U, intervalDomainLift, hy] using hUpos y hy
    simp [U, intervalDomainLift, hy, abs_of_pos huPos]
  have hleftInt : IntervalIntegrable
      (intervalDomainLift (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hleftLiftCont
  have hOneInt : IntervalIntegrable
      (intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm 1 u t))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hlpLiftCont 1
  have hZeroInt : IntervalIntegrable
      (intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm 0 u t))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hlpLiftCont 0
  change (∫ y in (0 : ℝ)..1,
      intervalDomainLift (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) y) =
    (∫ y in (0 : ℝ)..1,
      intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm 1 u t) y) -
      uStar * (∫ y in (0 : ℝ)..1,
        intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm 0 u t) y)
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub hOneInt (hZeroInt.const_mul uStar)]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp only [intervalDomainLift, hy, dif_pos,
    intervalDomainLpEnergyWeightedTimeTerm]
  have huPos : 0 < u t ⟨y, hy⟩ := by
    simpa [U, intervalDomainLift, hy] using hUpos y hy
  rw [show |u t ⟨y, hy⟩| ^ ((1 : ℝ) - 2) * u t ⟨y, hy⟩ = 1 from
      entropyLpTest_one huPos,
    show |u t ⟨y, hy⟩| ^ ((0 : ℝ) - 2) * u t ⟨y, hy⟩ =
        1 / u t ⟨y, hy⟩ from entropyLpTest_zero huPos]
  ring

/-- The two logistic tests combine to the exact theta dissipation when the
reference constant is a positive equilibrium. -/
theorem intervalDomain_entropyLogistic_one_sub_zero
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution
      intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    intervalDomainLpLogisticIntegral p 1 u t -
        uStar * intervalDomainLpLogisticIntegral p 0 u t =
      -p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  have haeq : p.a = p.b * uStar ^ p.α := by
    have := heq.reaction_eq_zero
    rcases mul_eq_zero.mp this with hzero | hzero
    · exact False.elim (heq.u_pos.ne' hzero)
    · exact sub_eq_zero.mp hzero
  have hOneInt :=
    ShenWork.Paper2.IntervalDomainM.lift_lp_logistic_intervalIntegrable
      (pExp := (1 : ℝ)) hsol ht0 htT
  have hZeroInt :=
    ShenWork.Paper2.IntervalDomainM.lift_lp_logistic_intervalIntegrable
      (pExp := (0 : ℝ)) hsol ht0 htT
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol ht
  have hUpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < U y := by
    intro y hy
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_pos_Icc hsol ht y hy
  have hthetaCont : ContinuousOn
      (fun y => (U y - uStar) * (U y ^ p.α - uStar ^ p.α))
      (Set.Icc (0 : ℝ) 1) :=
    (hUcont.sub continuousOn_const).mul
      ((hUcont.rpow_const
        (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))).sub continuousOn_const)
  have hthetaInt : IntervalIntegrable
      (fun y => (U y - uStar) * (U y ^ p.α - uStar ^ p.α))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hthetaCont
  unfold intervalDomainLpLogisticIntegral chemotaxisThetaDissipation
  change (∫ y in (0 : ℝ)..1,
      intervalDomainLift (fun x =>
        intervalDomainLpDiffusionTest 1 u t x *
          (u t x * (p.a - p.b * u t x ^ p.α))) y) -
      uStar * (∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x =>
          intervalDomainLpDiffusionTest 0 u t x *
            (u t x * (p.a - p.b * u t x ^ p.α))) y) =
    -p.b * (∫ y in (0 : ℝ)..1,
      intervalDomainLift (fun x =>
        (u t x - uStar) * (u t x ^ p.α - uStar ^ p.α)) y)
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub hOneInt (hZeroInt.const_mul uStar)]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp only [intervalDomainLift, hy, dif_pos, intervalDomainLpDiffusionTest]
  have huPos : 0 < u t ⟨y, hy⟩ :=
    ShenWork.Paper2.IntervalDomainM.u_pos hsol ht0 htT ⟨y, hy⟩
  rw [entropyLpTest_one huPos, entropyLpTest_zero huPos, haeq]
  field_simp [huPos.ne']
  ring

/-- Exact entropy-production identity on one positive classical slice. -/
theorem intervalDomain_entropySlope_identity
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : p.m = 1)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) =
      -uStar * intervalDomainLpWeightedGradientDissipation 0 u t +
        p.χ₀ * uStar *
          ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM p 0 u v t -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  have htime := intervalDomain_entropyTimeTerm_eq_lp_one_sub_zero
    hsol ht0 htT (uStar := uStar)
  have hpde1 := ShenWork.Paper2.IntervalDomainM.pdeIntegral
    (pExp := (1 : ℝ)) hsolM ht0 htT
  have hpde0 := ShenWork.Paper2.IntervalDomainM.pdeIntegral
    (pExp := (0 : ℝ)) hsolM ht0 htT
  have hdiff1 := ShenWork.Paper2.IntervalDomainM.diffusion_ibp
    (pExp := (1 : ℝ)) hsolM ht0 htT
  have hdiff0 := ShenWork.Paper2.IntervalDomainM.diffusion_ibp
    (pExp := (0 : ℝ)) hsolM ht0 htT
  have hdiss1 := ShenWork.Paper2.IntervalDomainM.diffusion_dissipation_eq
    (pExp := (1 : ℝ)) hsolM ht0 htT
  have hdiss0 := ShenWork.Paper2.IntervalDomainM.diffusion_dissipation_eq
    (pExp := (0 : ℝ)) hsolM ht0 htT
  have hchem1 := ShenWork.Paper2.IntervalDomainM.chemotaxis_ibp
    (pExp := (1 : ℝ)) hsolM ht0 htT
  have hchem0 := ShenWork.Paper2.IntervalDomainM.chemotaxis_ibp
    (pExp := (0 : ℝ)) hsolM ht0 htT
  have hneuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0 :=
    (hsolM.2.2.2.2.2.2 t intervalDomainRightEndpoint ht0 htT
      ShenWork.Paper2.IntervalDomainM.rightEndpoint_mem_boundaryM).1
  have hneuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0 :=
    (hsolM.2.2.2.2.2.2 t intervalDomainLeftEndpoint ht0 htT
      ShenWork.Paper2.IntervalDomainM.leftEndpoint_mem_boundaryM).1
  have hboundary (q : ℝ) : intervalDomainNeumannBoundaryTerm
      (intervalDomainLpDiffusionTest q u t) (u t) = 0 :=
    intervalDomain_neumannBoundaryTerm_eq_zero _ _ hneuR hneuL
  have hlog := intervalDomain_entropyLogistic_one_sub_zero
    hsolM ht0 htT heq
  rw [htime, hpde1, hpde0, hdiff1, hdiff0,
    hboundary 1, hboundary 0, zero_sub, hdiss1, hdiss0]
  have hchem1' :
      -p.χ₀ * ShenWork.Paper2.IntervalDomainM.lpChemotaxisIntegralM
          p 1 u v t = 0 := by
    simpa using hchem1
  have hchem0' :
      -p.χ₀ * ShenWork.Paper2.IntervalDomainM.lpChemotaxisIntegralM
          p 0 u v t =
        -p.χ₀ * ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
          p 0 u v t := by
    simpa using hchem0
  let C1 := ShenWork.Paper2.IntervalDomainM.lpChemotaxisIntegralM p 1 u v t
  let C0 := ShenWork.Paper2.IntervalDomainM.lpChemotaxisIntegralM p 0 u v t
  let X0 := ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM p 0 u v t
  let L1 := intervalDomainLpLogisticIntegral p 1 u t
  let L0 := intervalDomainLpLogisticIntegral p 0 u t
  let G1 := intervalDomainLpWeightedGradientDissipation 1 u t
  let G0 := intervalDomainLpWeightedGradientDissipation 0 u t
  change
    -((1 - 1) * G1) - p.χ₀ * C1 + L1 -
        uStar * (0 - (0 - 1) * G0 - p.χ₀ * C0 + L0) =
      -uStar * G0 + p.χ₀ * uStar * X0 -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t)
  have hc1 : -p.χ₀ * C1 = 0 := by simpa [C1] using hchem1'
  have hc0 : -p.χ₀ * C0 = -p.χ₀ * X0 := by
    simpa [C0, X0] using hchem0'
  have hlog' : L1 - uStar * L0 =
      -p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
    simpa [L1, L0] using hlog
  calc
    -((1 - 1) * G1) - p.χ₀ * C1 + L1 -
          uStar * (0 - (0 - 1) * G0 - p.χ₀ * C0 + L0) =
        (-p.χ₀ * C1) + (L1 - uStar * L0) - uStar * G0 -
          uStar * (-p.χ₀ * C0) := by ring
    _ = -uStar * G0 + p.χ₀ * uStar * X0 -
          p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      rw [hc1, hc0, hlog']
      ring

#print axioms entropyLpTest_one
#print axioms entropyLpTest_zero
#print axioms intervalDomain_entropyTimeTerm_eq_lp_one_sub_zero
#print axioms intervalDomain_entropyLogistic_one_sub_zero
#print axioms intervalDomain_entropySlope_identity

end

end ShenWork.Paper3
