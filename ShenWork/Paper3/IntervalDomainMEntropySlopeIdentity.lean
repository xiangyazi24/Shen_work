import ShenWork.Paper3.IntervalDomainMEntropyTimeDerivative
import ShenWork.Paper3.EventualExponentialStability
import ShenWork.Paper2.IntervalDomainMLpEnergy
import ShenWork.Paper2.IntervalDomainMMass

/-!
# Exact entropy-production inequality for the faithful general-`m` equation

The general-`m` entropy test `h_m'(u) = 1 - (uStar/u)^(2m-1)` is the
difference of the standard weighted `L^p` tests at the exponents `p = 1` and
`p = 2 - 2m`:

`h_m'(U) = |U|^(1-2) U - uStar^(2m-1) · |U|^((2-2m)-2) U`  (for `U > 0`).

This file reuses the already-proved faithful weighted-PDE identities at those
two exponents (`ShenWork.Paper2.IntervalDomainM.pdeIntegral` etc., which are
exponent-generic), so no spatial integration by parts is duplicated.  The
logistic block is handled by a pointwise power inequality valid for `m ≥ 1`,
giving the paper's `-b · θ`-dissipation bound (7.2)–(7.4) of Section 7.
-/

open ShenWork.IntervalDomain MeasureTheory Set
open scoped Topology Interval

namespace ShenWork.Paper3

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep

/-- The general-`m` entropy test as a difference of two `L^p` diffusion
tests. -/
theorem chemotaxisEntropyIntegrand_eq_lp_split
    {m uStar U : ℝ} (huStar : 0 < uStar) (hU : 0 < U) :
    chemotaxisEntropyIntegrand m uStar U =
      |U| ^ ((1 : ℝ) - 2) * U -
        uStar ^ (2 * m - 1) * (|U| ^ ((2 - 2 * m) - 2) * U) := by
  rw [abs_of_pos hU]
  unfold chemotaxisEntropyIntegrand
  have h1 : U ^ ((1 : ℝ) - 2) * U = 1 := by
    rw [show ((1 : ℝ) - 2) = -1 by norm_num, Real.rpow_neg_one]
    exact inv_mul_cancel₀ hU.ne'
  have h2 : U ^ ((2 - 2 * m) - 2) * U = U ^ (1 - 2 * m) := by
    calc
      U ^ ((2 - 2 * m) - 2) * U =
          U ^ ((2 - 2 * m) - 2) * U ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = U ^ (((2 - 2 * m) - 2) + 1) := by rw [← Real.rpow_add hU]
      _ = U ^ (1 - 2 * m) := by
          congr 1
          ring
  have hdiv : (uStar / U) ^ (2 * m - 1) =
      uStar ^ (2 * m - 1) * U ^ (1 - 2 * m) := by
    rw [Real.div_rpow huStar.le hU.le, div_eq_mul_inv, ← Real.rpow_neg hU.le]
    congr 1
    ring
  rw [h1, h2, hdiv]

/-- Pointwise general-`m` logistic comparison (paper Section 7, logistic
block): for `m ≥ 1` the entropy-tested logistic term is dominated by the
`θ = α` dissipation integrand. -/
theorem entropyLogisticPointwise_le
    {m uStar alpha U b : ℝ}
    (hm : 1 ≤ m) (huStar : 0 < uStar) (hU : 0 < U)
    (halpha : 0 ≤ alpha) (hb : 0 ≤ b) :
    chemotaxisEntropyIntegrand m uStar U *
        (U * (b * uStar ^ alpha - b * U ^ alpha)) ≤
      -b * ((U - uStar) * (U ^ alpha - uStar ^ alpha)) := by
  have hrpos : 0 < uStar / U := div_pos huStar hU
  have hq : 0 ≤ 2 * m - 2 := by linarith
  have hrU : uStar / U * U = uStar := div_mul_cancel₀ uStar hU.ne'
  have hEU : chemotaxisEntropyIntegrand m uStar U * U - (U - uStar) =
      uStar * (1 - (uStar / U) ^ (2 * m - 2)) := by
    unfold chemotaxisEntropyIntegrand
    rw [show (2 * m - 1 : ℝ) = (2 * m - 2) + 1 by ring,
      Real.rpow_add_one (ne_of_gt hrpos)]
    linear_combination (-((uStar / U) ^ (2 * m - 2))) * hrU
  have hkey' : 0 ≤
      (chemotaxisEntropyIntegrand m uStar U * U - (U - uStar)) *
        (U ^ alpha - uStar ^ alpha) := by
    rw [hEU]
    rcases le_total uStar U with hle | hle
    · have hr1 : uStar / U ≤ 1 := (div_le_one hU).mpr hle
      have hpow : (uStar / U) ^ (2 * m - 2) ≤ 1 :=
        Real.rpow_le_one hrpos.le hr1 hq
      have hS : 0 ≤ U ^ alpha - uStar ^ alpha :=
        sub_nonneg.mpr (Real.rpow_le_rpow huStar.le hle halpha)
      have hfac : 0 ≤ 1 - (uStar / U) ^ (2 * m - 2) := by linarith
      exact mul_nonneg (mul_nonneg huStar.le hfac) hS
    · have hr1 : 1 ≤ uStar / U := (one_le_div hU).mpr hle
      have hpow : 1 ≤ (uStar / U) ^ (2 * m - 2) := by
        calc (1 : ℝ) = (1 : ℝ) ^ (2 * m - 2) := (Real.one_rpow _).symm
          _ ≤ (uStar / U) ^ (2 * m - 2) :=
            Real.rpow_le_rpow (by norm_num) hr1 hq
      have hS : U ^ alpha - uStar ^ alpha ≤ 0 :=
        sub_nonpos.mpr (Real.rpow_le_rpow hU.le hle halpha)
      have hfac : 1 - (uStar / U) ^ (2 * m - 2) ≤ 0 := by linarith
      have h1 : uStar * (1 - (uStar / U) ^ (2 * m - 2)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos huStar.le hfac
      exact mul_nonneg_of_nonpos_of_nonpos h1 hS
  have hgap : (U - uStar) * (U ^ alpha - uStar ^ alpha) ≤
      chemotaxisEntropyIntegrand m uStar U * U *
        (U ^ alpha - uStar ^ alpha) := by
    nlinarith [hkey']
  have hmul := mul_le_mul_of_nonneg_left hgap hb
  calc
    chemotaxisEntropyIntegrand m uStar U *
        (U * (b * uStar ^ alpha - b * U ^ alpha)) =
      -(b * (chemotaxisEntropyIntegrand m uStar U * U *
        (U ^ alpha - uStar ^ alpha))) := by ring
    _ ≤ -(b * ((U - uStar) * (U ^ alpha - uStar ^ alpha))) := by linarith
    _ = -b * ((U - uStar) * (U ^ alpha - uStar ^ alpha)) := by ring

/-- The entropy weighted-time term is the difference of the `p = 1` and
`p = 2 - 2m` weighted `L^p` time terms. -/
theorem intervalDomainM_entropyTimeTerm_eq_lp_split
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (huStar : 0 < uStar) :
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) =
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm 1 u t) -
        uStar ^ (2 * p.m - 1) * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm (2 - 2 * p.m) u t) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let Ut : ℝ → ℝ :=
    ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u t
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hreg : intervalDomainClassicalRegularity T u v := hsol.regularity
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hreg.2.2.2.2.1 t ht).1.1.continuousOn
  have hUtJoint : ContinuousOn
      (Function.uncurry
        (ShenWork.Paper2.intervalDomainMassTimeDerivIntegrand u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hreg.2.2.2.2.2.1.1
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
  have hEcont : ContinuousOn
      (fun y => chemotaxisEntropyIntegrand p.m uStar (U y))
      (Set.Icc (0 : ℝ) 1) := by
    have hInt : ContinuousOn
        (chemotaxisEntropyIntegrand p.m uStar) ({0}ᶜ : Set ℝ) := by
      intro z hz
      exact (chemotaxisEntropyIntegrand_continuousAt_of_ne
        (m := p.m) (uStar := uStar) huStar.ne'
          (by simpa using hz)).continuousWithinAt
    exact ContinuousOn.comp (g := chemotaxisEntropyIntegrand p.m uStar)
      hInt hUcont (fun y hy => ne_of_gt (hUpos y hy))
  have hleftCont : ContinuousOn
      (fun y => chemotaxisEntropyIntegrand p.m uStar (U y) * Ut y)
      (Set.Icc (0 : ℝ) 1) :=
    hEcont.mul hUtcont
  have hleftLiftCont : ContinuousOn
      (intervalDomainLift (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x))
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
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hleftLiftCont
  have hOneInt : IntervalIntegrable
      (intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm 1 u t))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hlpLiftCont 1
  have hSplitInt : IntervalIntegrable
      (intervalDomainLift
        (intervalDomainLpEnergyWeightedTimeTerm (2 - 2 * p.m) u t))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hlpLiftCont (2 - 2 * p.m)
  change (∫ y in (0 : ℝ)..1,
      intervalDomainLift (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) y) =
    (∫ y in (0 : ℝ)..1,
      intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm 1 u t) y) -
      uStar ^ (2 * p.m - 1) * (∫ y in (0 : ℝ)..1,
        intervalDomainLift
          (intervalDomainLpEnergyWeightedTimeTerm (2 - 2 * p.m) u t) y)
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub hOneInt
    (hSplitInt.const_mul (uStar ^ (2 * p.m - 1)))]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp only [intervalDomainLift, hy, dif_pos,
    intervalDomainLpEnergyWeightedTimeTerm]
  have huPos : 0 < u t ⟨y, hy⟩ := by
    simpa [U, intervalDomainLift, hy] using hUpos y hy
  rw [chemotaxisEntropyIntegrand_eq_lp_split huStar huPos]
  ring

/-- The two logistic tests are dominated by the exact theta dissipation when
the reference constant is a positive equilibrium and `m ≥ 1`. -/
theorem intervalDomainM_entropyLogistic_le
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    intervalDomainLpLogisticIntegral p 1 u t -
        uStar ^ (2 * p.m - 1) *
          intervalDomainLpLogisticIntegral p (2 - 2 * p.m) u t ≤
      -p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  have haeq : p.a = p.b * uStar ^ p.α := by
    have := heq.reaction_eq_zero
    rcases mul_eq_zero.mp this with hzero | hzero
    · exact False.elim (heq.u_pos.ne' hzero)
    · exact sub_eq_zero.mp hzero
  have hOneInt :=
    ShenWork.Paper2.IntervalDomainM.lift_lp_logistic_intervalIntegrable
      (pExp := (1 : ℝ)) hsol ht0 htT
  have hSplitInt :=
    ShenWork.Paper2.IntervalDomainM.lift_lp_logistic_intervalIntegrable
      (pExp := 2 - 2 * p.m) hsol ht0 htT
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
      uStar ^ (2 * p.m - 1) * (∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x =>
          intervalDomainLpDiffusionTest (2 - 2 * p.m) u t x *
            (u t x * (p.a - p.b * u t x ^ p.α))) y) ≤
    -p.b * (∫ y in (0 : ℝ)..1,
      intervalDomainLift (fun x =>
        (u t x - uStar) * (u t x ^ p.α - uStar ^ p.α)) y)
  have hthetaLiftCont : ContinuousOn
      (intervalDomainLift (fun x =>
        (u t x - uStar) * (u t x ^ p.α - uStar ^ p.α)))
      (Set.Icc (0 : ℝ) 1) := by
    refine hthetaCont.congr ?_
    intro y hy
    simp [intervalDomainLift, hy, U]
  have hthetaLiftInt : IntervalIntegrable
      (intervalDomainLift (fun x =>
        (u t x - uStar) * (u t x ^ p.α - uStar ^ p.α))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hthetaLiftCont
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub hOneInt
    (hSplitInt.const_mul (uStar ^ (2 * p.m - 1)))]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num)
    (hOneInt.sub (hSplitInt.const_mul (uStar ^ (2 * p.m - 1))))
    (hthetaLiftInt.const_mul (-p.b)) ?_
  intro y hy
  simp only [intervalDomainLift, hy, dif_pos, intervalDomainLpDiffusionTest]
  have huPos : 0 < u t ⟨y, hy⟩ :=
    ShenWork.Paper2.IntervalDomainM.u_pos hsol ht0 htT ⟨y, hy⟩
  have hfactor :
      |u t ⟨y, hy⟩| ^ ((1 : ℝ) - 2) * u t ⟨y, hy⟩ *
          (u t ⟨y, hy⟩ * (p.a - p.b * u t ⟨y, hy⟩ ^ p.α)) -
        uStar ^ (2 * p.m - 1) *
          (|u t ⟨y, hy⟩| ^ ((2 - 2 * p.m) - 2) * u t ⟨y, hy⟩ *
            (u t ⟨y, hy⟩ * (p.a - p.b * u t ⟨y, hy⟩ ^ p.α))) =
      chemotaxisEntropyIntegrand p.m uStar (u t ⟨y, hy⟩) *
        (u t ⟨y, hy⟩ * (p.a - p.b * u t ⟨y, hy⟩ ^ p.α)) := by
    rw [chemotaxisEntropyIntegrand_eq_lp_split heq.u_pos huPos]
    ring
  rw [hfactor, haeq]
  exact entropyLogisticPointwise_le hm heq.u_pos huPos p.hα.le p.hb

/-- Exact general-`m` entropy-production inequality on one positive classical
slice of the faithful equation: the paper's (7.2)–(7.4) with the logistic
block already reduced to `θ = α` dissipation. -/
theorem intervalDomainM_entropySlope_le_of_classical
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) ≤
      -((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) *
          intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t +
        p.χ₀ * ((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) *
          ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
            p (2 - 2 * p.m) u v t -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  have htime := intervalDomainM_entropyTimeTerm_eq_lp_split
    hsol ht0 htT heq.u_pos
  have hneuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0 :=
    (hsol.2.2.2.2.2.2 t intervalDomainRightEndpoint ht0 htT
      ShenWork.Paper2.IntervalDomainM.rightEndpoint_mem_boundaryM).1
  have hneuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0 :=
    (hsol.2.2.2.2.2.2 t intervalDomainLeftEndpoint ht0 htT
      ShenWork.Paper2.IntervalDomainM.leftEndpoint_mem_boundaryM).1
  have hq_eq : ∀ q : ℝ,
      intervalDomain.integral (intervalDomainLpEnergyWeightedTimeTerm q u t) =
        -((q - 1) * intervalDomainLpWeightedGradientDissipation q u t) +
          p.χ₀ * (q - 1) *
            ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM p q u v t +
          intervalDomainLpLogisticIntegral p q u t := by
    intro q
    have hpde := ShenWork.Paper2.IntervalDomainM.pdeIntegral
      (pExp := q) hsol ht0 htT
    have hdiff := ShenWork.Paper2.IntervalDomainM.diffusion_ibp
      (pExp := q) hsol ht0 htT
    have hdiss := ShenWork.Paper2.IntervalDomainM.diffusion_dissipation_eq
      (pExp := q) hsol ht0 htT
    have hchem := ShenWork.Paper2.IntervalDomainM.chemotaxis_ibp
      (pExp := q) hsol ht0 htT
    have hbdry : intervalDomainNeumannBoundaryTerm
        (intervalDomainLpDiffusionTest q u t) (u t) = 0 :=
      intervalDomain_neumannBoundaryTerm_eq_zero _ _ hneuR hneuL
    rw [hpde, hdiff, hbdry, hdiss]
    linear_combination hchem
  have h1 := hq_eq 1
  have hS := hq_eq (2 - 2 * p.m)
  have hlog := intervalDomainM_entropyLogistic_le hm hsol ht0 htT heq
  calc
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) =
        intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm 1 u t) -
          uStar ^ (2 * p.m - 1) * intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm (2 - 2 * p.m) u t) := htime
    _ = -((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) *
            intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t +
          p.χ₀ * ((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) *
            ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
              p (2 - 2 * p.m) u v t +
          (intervalDomainLpLogisticIntegral p 1 u t -
            uStar ^ (2 * p.m - 1) *
              intervalDomainLpLogisticIntegral p (2 - 2 * p.m) u t) := by
        rw [h1, hS]
        ring
    _ ≤ -((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) *
            intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t +
          p.χ₀ * ((2 * p.m - 1) * uStar ^ (2 * p.m - 1)) *
            ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
              p (2 - 2 * p.m) u v t -
          p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
        linarith

#print axioms chemotaxisEntropyIntegrand_eq_lp_split
#print axioms entropyLogisticPointwise_le
#print axioms intervalDomainM_entropyTimeTerm_eq_lp_split
#print axioms intervalDomainM_entropyLogistic_le
#print axioms intervalDomainM_entropySlope_le_of_classical

end

end ShenWork.Paper3
