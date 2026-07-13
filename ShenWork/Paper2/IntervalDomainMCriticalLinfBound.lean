import ShenWork.Paper2.IntervalDomainMCriticalLpBootstrap
import ShenWork.Paper2.IntervalDomainMSlowLinfBound
import ShenWork.Paper2.IntervalConjugateKernelL1FarBound
import ShenWork.Paper2.IntervalConjugateDuhamelSupLocalized

/-!
# Uniform sup bound for the faithful critical interval equation

For `m = 1`, the one-scale restart estimate is linear in the slab maximum and
cannot be absorbed.  The chemotactic Duhamel leg is therefore split into a
far interval and a short terminal interval.  The far part uses the positive-
lag `L¹ → L∞` conjugate-kernel estimate, with an `L¹` flux bound supplied by
the finite-power bootstrap.  The near part uses the integrable
`L∞ → L∞` square-root estimate.  Choosing the terminal width as a negative
power of the slab maximum makes both contributions sublinear.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.Paper2.IntervalConjugateKernelL1FarBound
  (intervalConjugateKernelOperator_abs_le_L1_far)

/-- Terminal width used in the critical two-scale split. -/
def criticalTerminalWidth (a M : ℝ) : ℝ :=
  a * (M + 1) ^ (-(2 / 5 : ℝ))

lemma criticalTerminalWidth_pos {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    0 < criticalTerminalWidth a M := by
  unfold criticalTerminalWidth
  exact mul_pos ha (Real.rpow_pos_of_pos (by linarith) _)

lemma criticalTerminalWidth_le {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    criticalTerminalWidth a M ≤ a := by
  unfold criticalTerminalWidth
  have hdecay : (M + 1) ^ (-(2 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ M + 1) (-(2 / 5 : ℝ))]

lemma criticalTerminalWidth_inv_sq
    {a M A : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    A / (criticalTerminalWidth a M) ^ 2 =
      (A / a ^ 2) * (M + 1) ^ (4 / 5 : ℝ) := by
  have hX : 0 < M + 1 := by linarith
  have hpow : ((M + 1) ^ (-(2 / 5 : ℝ))) ^ 2 =
      (M + 1) ^ (-(4 / 5 : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hX.le]
    congr 1
    norm_num
  unfold criticalTerminalWidth
  rw [mul_pow, hpow, Real.rpow_neg hX.le]
  field_simp [ne_of_gt ha, ne_of_gt (Real.rpow_pos_of_pos hX (4 / 5 : ℝ))]

lemma criticalTerminalWidth_near
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    M * Real.sqrt (criticalTerminalWidth a M) ≤
      Real.sqrt a * (M + 1) ^ (4 / 5 : ℝ) := by
  have hX : 0 < M + 1 := by linarith
  have hsqrt : Real.sqrt (criticalTerminalWidth a M) =
      Real.sqrt a * (M + 1) ^ (-(1 / 5 : ℝ)) := by
    unfold criticalTerminalWidth
    rw [Real.sqrt_mul ha.le]
    rw [Real.sqrt_eq_rpow ((M + 1) ^ (-(2 / 5 : ℝ))),
      ← Real.rpow_mul hX.le]
    congr 2
    norm_num
  rw [hsqrt]
  have hdecay : 0 ≤ (M + 1) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_nonneg hX.le _
  have hprod : (M + 1) * (M + 1) ^ (-(1 / 5 : ℝ)) =
      (M + 1) ^ (4 / 5 : ℝ) := by
    calc
      (M + 1) * (M + 1) ^ (-(1 / 5 : ℝ)) =
          (M + 1) ^ (1 : ℝ) * (M + 1) ^ (-(1 / 5 : ℝ)) := by
            rw [Real.rpow_one]
      _ = (M + 1) ^ ((1 : ℝ) + (-(1 / 5 : ℝ))) :=
        (Real.rpow_add hX _ _).symm
      _ = (M + 1) ^ (4 / 5 : ℝ) := by norm_num
  calc
    M * (Real.sqrt a * (M + 1) ^ (-(1 / 5 : ℝ))) ≤
        (M + 1) * (Real.sqrt a * (M + 1) ^ (-(1 / 5 : ℝ))) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (Real.sqrt_nonneg a) hdecay)
    _ = Real.sqrt a * (M + 1) ^ (4 / 5 : ℝ) := by
      rw [show (M + 1) *
          (Real.sqrt a * (M + 1) ^ (-(1 / 5 : ℝ))) =
          Real.sqrt a *
            ((M + 1) * (M + 1) ^ (-(1 / 5 : ℝ))) by ring,
        hprod]

/-- The width choice converts the far inverse-square loss and the near
square-root loss into the same sublinear power `4/5`. -/
theorem critical_two_scale_terms_le
    {a r T M A D : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (har : a ≤ r) (hrT : r ≤ T) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    let ε := criticalTerminalWidth a M
    (r - ε) * (A / ε ^ 2) + D * (M * Real.sqrt ε) ≤
      (T * (A / a ^ 2) + D * Real.sqrt a) *
        (M + 1) ^ (4 / 5 : ℝ) := by
  dsimp only
  let ε : ℝ := criticalTerminalWidth a M
  have hε : 0 < ε := criticalTerminalWidth_pos ha hM
  have hεa : ε ≤ a := criticalTerminalWidth_le ha hM
  have hεr : ε ≤ r := hεa.trans har
  have hfarFactor : 0 ≤ A / ε ^ 2 :=
    div_nonneg hA (sq_nonneg ε)
  have hfar : (r - ε) * (A / ε ^ 2) ≤
      T * ((A / a ^ 2) * (M + 1) ^ (4 / 5 : ℝ)) := by
    calc
      (r - ε) * (A / ε ^ 2) ≤ T * (A / ε ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hfarFactor
      _ = T * ((A / a ^ 2) * (M + 1) ^ (4 / 5 : ℝ)) := by
        rw [show A / ε ^ 2 =
          (A / a ^ 2) * (M + 1) ^ (4 / 5 : ℝ) by
            simpa [ε] using criticalTerminalWidth_inv_sq
              (a := a) (M := M) (A := A) ha hM]
  have hnear : D * (M * Real.sqrt ε) ≤
      D * (Real.sqrt a * (M + 1) ^ (4 / 5 : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (by simpa [ε] using criticalTerminalWidth_near ha hM) hD
  calc
    (r - ε) * (A / ε ^ 2) + D * (M * Real.sqrt ε) ≤
        T * ((A / a ^ 2) * (M + 1) ^ (4 / 5 : ℝ)) +
          D * (Real.sqrt a * (M + 1) ^ (4 / 5 : ℝ)) :=
      add_le_add hfar hnear
    _ = (T * (A / a ^ 2) + D * Real.sqrt a) *
        (M + 1) ^ (4 / 5 : ℝ) := by ring

/-- Every finite-power bound above one controls the spatial mass of the
positive solution slice. -/
theorem solution_one_integral_le_of_lp
    {p : CM2Params} {T t pExp C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hp : 1 ≤ pExp)
    (hpower : intervalDomainM.integral (fun z => (u t z) ^ pExp) ≤ C) :
    (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y) ≤ C + 1 := by
  have hu_int : IntervalIntegrable
      (fun y => intervalDomainLift (u t) y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact solution_lift_continuousOn_Icc hsol ⟨ht0, htT⟩
  have hp_int : IntervalIntegrable
      (fun y => intervalDomainLift (u t) y ^ pExp) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact power_continuousOn_timeSlice (q := pExp) hsol ⟨ht0, htT⟩
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤
        intervalDomainLift (u t) y ^ pExp + 1 := by
    intro y hy
    have h :=
      ShenWork.Paper2.IntervalDomainLpMonotonicity.rpow_le_one_add_rpow_of_nonneg_of_le
        (solution_lift_pos_Icc hsol ⟨ht0, htT⟩ y hy).le
        (by norm_num : (0 : ℝ) ≤ 1) hp
    simpa using h
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1) hu_int
    (hp_int.add intervalIntegrable_const) hpoint
  have hsplit :
      (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp + 1) =
        (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp) + 1 := by
    rw [intervalIntegral.integral_add hp_int intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  rw [hsplit] at hmono
  have hp_eq :
      (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp) =
        intervalDomainM.integral (fun z => (u t z) ^ pExp) := by
    change (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y ^ pExp) =
      intervalDomain.integral (fun z => (u t z) ^ pExp)
    exact
      (ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation.intervalDomain_integral_rpow_eq_lift_integral).symm
  rw [hp_eq] at hmono
  linarith

/-- At the critical diffusion exponent, the restart flux has an `L¹` bound
independent of the slab maximum. -/
theorem restartFluxM_integral_abs_le_of_lp
    {p : CM2Params} {T a h pExp C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hm : p.m = 1) (hp : 1 ≤ pExp) (hγp : p.γ ≤ pExp)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ pExp) ≤ C) (r : ℝ) :
    (∫ y in (0 : ℝ)..1, |restartFluxM p a h u v r y|) ≤
      (C + 1) * (2 * p.ν * (C + 1)) := by
  let r₀ : ℝ := restartTimeClamp h r
  let τ : ℝ := a + r₀
  have hr₀ : r₀ ∈ Icc (0 : ℝ) h := restartTimeClamp_mem hh r
  have hτ0 : 0 < τ := by
    dsimp [τ]
    exact add_pos_of_pos_of_nonneg ha hr₀.1
  have hτT : τ < T := by
    dsimp [τ]
    exact lt_of_le_of_lt
      (by simpa [add_comm] using add_le_add_left hr₀.2 a) hahT
  have hmass :
      (∫ y in (0 : ℝ)..1, intervalDomainLift (u τ) y) ≤ C + 1 :=
    solution_one_integral_le_of_lp hsol hτ0 hτT hp (hpower τ hτ0 hτT)
  let G : ℝ := 2 * p.ν * (C + 1)
  have hG : 0 ≤ G := by
    have hgrad := chemical_gradient_abs_le_of_lp hsol hτ0 hτT
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) hγp (hpower τ hτ0 hτT)
    exact (abs_nonneg (deriv (intervalDomainLift (v τ)) 0)).trans hgrad
  have hflux_cont : Continuous (restartFluxM p a h u v r) :=
    (restartFluxM_continuous hsol ha hh hahT).uncurry_left r
  have hu_cont : ContinuousOn (intervalDomainLift (u τ)) (Icc (0 : ℝ) 1) :=
    solution_lift_continuousOn_Icc hsol ⟨hτ0, hτT⟩
  have hflux_int : IntervalIntegrable
      (fun y => |restartFluxM p a h u v r y|) volume 0 1 :=
    hflux_cont.abs.intervalIntegrable 0 1
  have huG_int : IntervalIntegrable
      (fun y => intervalDomainLift (u τ) y * G) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hu_cont.mul continuousOn_const
  have hpoint : ∀ y ∈ Icc (0 : ℝ) 1,
      |restartFluxM p a h u v r y| ≤
        intervalDomainLift (u τ) y * G := by
    intro y hy
    have hu_pos : 0 < restartField a h u r y :=
      restartField_u_pos hsol ha hh hahT r y
    have hv_nonneg : 0 ≤ restartField a h v r y :=
      restartField_v_nonneg hsol ha hh hahT r y
    have hden : 1 ≤ (1 + restartField a h v r y) ^ p.β :=
      Real.one_le_rpow (by linarith) p.hβ
    have hgrad : |restartChemGrad p a h u v r y| ≤ G := by
      rw [restartChemGrad_clamp p hh u v r y]
      rw [clamp01_eq_self hy]
      change |restartChemGrad p a h u v r₀ y| ≤ G
      have hphys := restartChemGrad_eq_deriv hsol ha hh hahT hr₀ hy
      rw [hphys]
      simpa [G, τ] using
        chemical_gradient_abs_le_of_lp hsol hτ0 hτT hy hγp
          (hpower τ hτ0 hτT)
    have hfield : restartField a h u r y = intervalDomainLift (u τ) y := by
      rw [restartField_timeClamp hh u r y]
      exact restartField_eq_physical hr₀ hy
    unfold restartFluxM
    rw [abs_div, abs_mul, hm, Real.rpow_one,
      abs_of_pos hu_pos,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) p.β)]
    rw [hfield]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).2
    have hu_nonneg : 0 ≤ intervalDomainLift (u τ) y := by
      rw [← hfield]
      exact hu_pos.le
    have hnum : intervalDomainLift (u τ) y *
        |restartChemGrad p a h u v r y| ≤
          intervalDomainLift (u τ) y * G :=
      mul_le_mul_of_nonneg_left hgrad hu_nonneg
    exact hnum.trans (le_mul_of_one_le_right
      (mul_nonneg hu_nonneg hG) hden)
  calc
    (∫ y in (0 : ℝ)..1, |restartFluxM p a h u v r y|) ≤
        ∫ y in (0 : ℝ)..1, intervalDomainLift (u τ) y * G :=
      intervalIntegral.integral_mono_on (by norm_num) hflux_int huG_int hpoint
    _ = (∫ y in (0 : ℝ)..1, intervalDomainLift (u τ) y) * G := by
      rw [intervalIntegral.integral_mul_const]
    _ ≤ (C + 1) * G := mul_le_mul_of_nonneg_right hmass hG
    _ = (C + 1) * (2 * p.ν * (C + 1)) := rfl

/-- The part of the conjugate Duhamel integral separated from the terminal
diagonal is bounded using only the critical flux `L¹` mass. -/
theorem restartChemDuhamelM_far_abs_le_of_lp
    {p : CM2Params} {T a h r ε pExp C : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hm : p.m = 1) (hp : 1 ≤ pExp) (hγp : p.γ ≤ pExp)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ pExp) ≤ C)
    (hε : 0 < ε) (hεr : ε ≤ r) (x : ℝ) :
    |∫ s in (0 : ℝ)..(r - ε),
        intervalConjugateKernelOperator (r - s)
          (restartFluxM p a h u v s) x| ≤
      (r - ε) *
        ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant /
            ε ^ 2) * ((C + 1) * (2 * p.ν * (C + 1)))) := by
  let q : ℝ → ℝ → ℝ := restartFluxM p a h u v
  let Q₁ : ℝ := (C + 1) * (2 * p.ν * (C + 1))
  let Cspec : ℝ :=
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant
  have hr : 0 < r := hε.trans_le hεr
  have hrε : 0 ≤ r - ε := sub_nonneg.mpr hεr
  have hqcont : Continuous (Function.uncurry q) := by
    simpa [q] using restartFluxM_continuous hsol ha hh hahT
  obtain ⟨Cq, hCq, hqbound⟩ :=
    exists_restartFluxM_bound hsol ha hh hahT
  have hqint : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s
    exact intervalMeasure_integrable_of_abs_bound
      (hqcont.uncurry_left s).measurable.aestronglyMeasurable
      (by simpa [q] using hqbound s)
  have hwhole : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (r - s) (q s) x)
      volume 0 r :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      hr hCq hqcont.measurable hqint (by simpa [q] using hqbound)
  have hfar : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (r - s) (q s) x)
      volume 0 (r - ε) := by
    apply hwhole.mono_set
    rw [Set.uIcc_of_le hrε, Set.uIcc_of_le hr.le]
    intro s hs
    exact ⟨hs.1, hs.2.trans (sub_le_self r hε.le)⟩
  have hQ₁ : 0 ≤ Q₁ := by
    have hnonneg : 0 ≤ ∫ y in (0 : ℝ)..1, |q 0 y| :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun y _ => abs_nonneg (q 0 y))
    have hb := restartFluxM_integral_abs_le_of_lp
      hsol ha hh hahT hm hp hγp hpower 0
    simpa [q, Q₁] using hnonneg.trans hb
  have hCspec : 0 ≤ Cspec := by
    dsimp [Cspec]
    exact
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant_nonneg
  have hK : 0 ≤ (Cspec / ε ^ 2) * Q₁ :=
    mul_nonneg (div_nonneg hCspec (sq_nonneg ε)) hQ₁
  have hpoint : ∀ s ∈ Icc (0 : ℝ) (r - ε),
      |intervalConjugateKernelOperator (r - s) (q s) x| ≤
        (Cspec / ε ^ 2) * Q₁ := by
    intro s hs
    have hlagε : ε ≤ r - s := by linarith [hs.2]
    have hlag : 0 < r - s := hε.trans_le hlagε
    have hop := intervalConjugateKernelOperator_abs_le_L1_far
      hlag (hqcont.uncurry_left s) x
    have hmass := restartFluxM_integral_abs_le_of_lp
      hsol ha hh hahT hm hp hγp hpower s
    have hsq : ε ^ 2 ≤ (r - s) ^ 2 := by
      nlinarith
    have hfactor : Cspec / (r - s) ^ 2 ≤ Cspec / ε ^ 2 :=
      div_le_div_of_nonneg_left hCspec (sq_pos_of_pos hε) hsq
    calc
      |intervalConjugateKernelOperator (r - s) (q s) x| ≤
          (Cspec / (r - s) ^ 2) *
            ∫ y in (0 : ℝ)..1, |q s y| := by
              simpa [q, Cspec] using hop
      _ ≤ (Cspec / ε ^ 2) * Q₁ :=
        mul_le_mul hfactor (by simpa [q, Q₁] using hmass)
          (intervalIntegral.integral_nonneg (by norm_num)
            (fun y _ => abs_nonneg (q s y)))
          (div_nonneg hCspec (sq_nonneg ε))
  calc
    |∫ s in (0 : ℝ)..(r - ε),
        intervalConjugateKernelOperator (r - s) (q s) x| ≤
        ∫ s in (0 : ℝ)..(r - ε),
          |intervalConjugateKernelOperator (r - s) (q s) x| :=
      intervalIntegral.abs_integral_le_integral_abs hrε
    _ ≤ ∫ _s in (0 : ℝ)..(r - ε), (Cspec / ε ^ 2) * Q₁ :=
      intervalIntegral.integral_mono_on hrε hfar.abs intervalIntegrable_const hpoint
    _ = (r - ε) * ((Cspec / ε ^ 2) * Q₁) := by
      rw [intervalIntegral.integral_const]
      norm_num [smul_eq_mul]
    _ = (r - ε) *
        ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant /
          ε ^ 2) * ((C + 1) * (2 * p.ν * (C + 1)))) := rfl

/-- The short terminal part of the conjugate Duhamel integral retains the
integrable square-root estimate. -/
theorem restartChemDuhamelM_near_abs_le_of_slab
    {p : CM2Params} {T a h r ε pExp C M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hm : p.m = 1) (hγp : p.γ ≤ pExp)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ pExp) ≤ C)
    (hM : 0 ≤ M)
    (hslab : ∀ τ ∈ Icc a (a + h), ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u τ) y ≤ M)
    (hε : 0 < ε) (x : ℝ) :
    |∫ s in (r - ε)..r,
        intervalConjugateKernelOperator (r - s)
          (restartFluxM p a h u v s) x| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt ε) * (M * (2 * p.ν * (C + 1))) := by
  let q : ℝ → ℝ → ℝ := restartFluxM p a h u v
  let qNear : ℝ → ℝ → ℝ := fun σ y => q (r - ε + σ) y
  let G : ℝ := 2 * p.ν * (C + 1)
  let Cq : ℝ := M * G
  have hqcont : Continuous (Function.uncurry q) := by
    simpa [q] using restartFluxM_continuous hsol ha hh hahT
  have hqNearCont : Continuous (Function.uncurry qNear) := by
    have hmap : Continuous (fun z : ℝ × ℝ =>
        ((r - ε + z.1, z.2) : ℝ × ℝ)) := by fun_prop
    simpa [qNear, Function.uncurry] using hqcont.comp hmap
  have hG : 0 ≤ G := by
    have haT : a < T := lt_of_le_of_lt (by linarith [hh] : a ≤ a + h) hahT
    have hγ := solution_gamma_integral_le_of_lp hsol ha haT hγp
      (hpower a ha haT)
    have hγnonneg : 0 ≤ ∫ y in (0 : ℝ)..1,
        intervalDomainLift (u a) y ^ p.γ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y hy =>
        Real.rpow_nonneg
          (solution_lift_pos_Icc hsol ⟨ha, haT⟩ y (by
            simpa [Set.uIcc_of_le zero_le_one] using hy)).le _)
    dsimp [G]
    exact mul_nonneg (mul_nonneg (by norm_num) p.hν.le)
      (by linarith)
  have hCq : 0 ≤ Cq := mul_nonneg hM hG
  have hqBound : ∀ σ y, |qNear σ y| ≤ Cq := by
    intro σ y
    have hb := restartFluxM_abs_le_of_lp_and_slab
      hsol ha hh hahT hγp hpower hM hslab (r - ε + σ) y
    simpa [qNear, q, Cq, G, hm, Real.rpow_one] using hb
  have hqInt : ∀ σ, Integrable (qNear σ) (intervalMeasure 1) := by
    intro σ
    exact intervalMeasure_integrable_of_abs_bound
      (hqNearCont.uncurry_left σ).measurable.aestronglyMeasurable
      (hqBound σ)
  have hBint : IntervalIntegrable
      (fun σ => intervalConjugateKernelOperator (ε - σ) (qNear σ) x)
      volume 0 ε :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      hε hCq hqNearCont.measurable hqInt hqBound
  have hbound :=
    ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound_localized
      hε le_rfl (fun σ _ => hqInt σ) hCq
        (fun σ _ => hqBound σ) x hBint
  have hshift := intervalIntegral.integral_comp_add_left
    (fun s => intervalConjugateKernelOperator (r - s) (q s) x)
    (r - ε) (a := (0 : ℝ)) (b := ε)
  have heq :
      (∫ s in (r - ε)..r,
          intervalConjugateKernelOperator (r - s) (q s) x) =
        ∫ σ in (0 : ℝ)..ε,
          intervalConjugateKernelOperator (ε - σ) (qNear σ) x := by
    calc
      (∫ s in (r - ε)..r,
          intervalConjugateKernelOperator (r - s) (q s) x) =
          ∫ s in ((r - ε) + 0)..((r - ε) + ε),
            intervalConjugateKernelOperator (r - s) (q s) x := by
              congr 2 <;> ring
      _ = ∫ σ in (0 : ℝ)..ε,
          intervalConjugateKernelOperator
            (r - ((r - ε) + σ)) (q ((r - ε) + σ)) x := hshift.symm
      _ = ∫ σ in (0 : ℝ)..ε,
          intervalConjugateKernelOperator (ε - σ) (qNear σ) x := by
            refine intervalIntegral.integral_congr (fun σ _ => ?_)
            simp only [qNear]
            rw [show r - (r - ε + σ) = ε - σ by ring]
  rw [heq]
  simpa [Cq, G] using hbound

/-- Two-scale estimate for the full critical chemotactic Duhamel leg. -/
theorem restartChemDuhamelM_two_scale_abs_le
    {p : CM2Params} {T a h r ε pExp C M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hm : p.m = 1) (hp : 1 ≤ pExp) (hγp : p.γ ≤ pExp)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ pExp) ≤ C)
    (hM : 0 ≤ M)
    (hslab : ∀ τ ∈ Icc a (a + h), ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u τ) y ≤ M)
    (hε : 0 < ε) (hεr : ε ≤ r) (x : ℝ) :
    |restartChemDuhamelM p a h u v r x| ≤
      (r - ε) *
          ((ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant /
              ε ^ 2) * ((C + 1) * (2 * p.ν * (C + 1)))) +
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt ε) * (M * (2 * p.ν * (C + 1))) := by
  let q : ℝ → ℝ → ℝ := restartFluxM p a h u v
  have hr : 0 < r := hε.trans_le hεr
  have hrε : 0 ≤ r - ε := sub_nonneg.mpr hεr
  have hqcont : Continuous (Function.uncurry q) := by
    simpa [q] using restartFluxM_continuous hsol ha hh hahT
  obtain ⟨Cq, hCq, hqbound⟩ :=
    exists_restartFluxM_bound hsol ha hh hahT
  have hqint : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s
    exact intervalMeasure_integrable_of_abs_bound
      (hqcont.uncurry_left s).measurable.aestronglyMeasurable
      (by simpa [q] using hqbound s)
  have hwhole : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (r - s) (q s) x)
      volume 0 r :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      hr hCq hqcont.measurable hqint (by simpa [q] using hqbound)
  have hfar : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (r - s) (q s) x)
      volume 0 (r - ε) := by
    apply hwhole.mono_set
    rw [Set.uIcc_of_le hrε, Set.uIcc_of_le hr.le]
    intro s hs
    exact ⟨hs.1, hs.2.trans (sub_le_self r hε.le)⟩
  have hnear : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (r - s) (q s) x)
      volume (r - ε) r := by
    apply hwhole.mono_set
    rw [Set.uIcc_of_le (by linarith : r - ε ≤ r), Set.uIcc_of_le hr.le]
    intro s hs
    exact ⟨hrε.trans hs.1, hs.2⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hfar hnear
  have hfarBound := restartChemDuhamelM_far_abs_le_of_lp
    hsol ha hh hahT hm hp hγp hpower hε hεr x
  have hnearBound := restartChemDuhamelM_near_abs_le_of_slab
    (r := r) hsol ha hh hahT hm hγp hpower hM hslab hε x
  unfold restartChemDuhamelM
  rw [← hsplit]
  exact (abs_add_le _ _).trans (add_le_add hfarBound hnearBound)

/-- Fixed coefficient multiplying the sublinear slab power in the critical
restart estimate. -/
def criticalChemCoefficient (p : CM2Params) (T a C : ℝ) : ℝ :=
  let G := 2 * p.ν * (C + 1)
  let Q₁ := (C + 1) * G
  let A :=
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant * Q₁
  let D :=
    2 * ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant * G
  T * (A / a ^ 2) + D * Real.sqrt a

/-- Quantitative upper bound for a critical physical slice at a restart lag
bounded below by the fixed restart time. -/
theorem solutionSlice_le_of_restart_critical_lp_slab_guard
    {p : CM2Params} {T a h r pExp C M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (har : a ≤ r) (hrh : r ≤ h)
    (hm : p.m = 1) (hp : 1 < pExp) (hγp : p.γ ≤ pExp)
    (hpower : ∀ τ, 0 < τ → τ < T →
      intervalDomainM.integral (fun z => (u τ z) ^ pExp) ≤ C)
    (hM : 0 ≤ M)
    (hslab : ∀ τ ∈ Icc a (a + h), ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u τ) y ≤ M)
    (hL : 0 ≤ L)
    (hsource : ∀ z ≥ 0, z * (p.a - p.b * z ^ p.α) ≤ L) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u (a + r)) x ≤
        fixedHeatKernelBound a * (C + 1) +
          |p.χ₀| *
            (criticalChemCoefficient p T a C *
              (M + 1) ^ (4 / 5 : ℝ)) + h * L := by
  have hr : 0 < r := ha.trans_le har
  have haT : a < T := lt_of_lt_of_le (by linarith : a < a + r)
    (lt_of_le_of_lt (by linarith) hahT).le
  have hC1 : 0 ≤ C + 1 := by
    have hγ := solution_gamma_integral_le_of_lp hsol ha haT hγp
      (hpower a ha haT)
    have hγnonneg : 0 ≤ ∫ y in (0 : ℝ)..1,
        intervalDomainLift (u a) y ^ p.γ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y hy =>
        Real.rpow_nonneg
          (solution_lift_pos_Icc hsol ⟨ha, haT⟩ y (by
            simpa [Set.uIcc_of_le zero_le_one] using hy)).le _)
    linarith
  let G : ℝ := 2 * p.ν * (C + 1)
  let Q₁ : ℝ := (C + 1) * G
  let Cspec : ℝ :=
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant
  let Cg : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  let Achem : ℝ := Cspec * Q₁
  let Dchem : ℝ := 2 * Cg * G
  let ε : ℝ := criticalTerminalWidth a M
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (mul_nonneg (by norm_num) p.hν.le) hC1
  have hQ₁ : 0 ≤ Q₁ := mul_nonneg hC1 hG
  have hCspec : 0 ≤ Cspec := by
    dsimp [Cspec]
    exact
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant_nonneg
  have hCg : 0 ≤ Cg := by
    dsimp [Cg]
    exact
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hAchem : 0 ≤ Achem := mul_nonneg hCspec hQ₁
  have hDchem : 0 ≤ Dchem := by
    dsimp [Dchem]
    positivity
  have hε : 0 < ε := by
    simpa [ε] using criticalTerminalWidth_pos ha hM
  have hεr : ε ≤ r := by
    have hεa : ε ≤ a := by
      simpa [ε] using criticalTerminalWidth_le ha hM
    exact hεa.trans har
  have hrT : r ≤ T := by linarith
  have hhom : ∀ x,
      |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator r
          (intervalDomainLift (u a)) x| ≤
        fixedHeatKernelBound a * (C + 1) := by
    intro x
    have hb := restartHomM_abs_le_of_lp hsol ha haT hr hp
      (hpower a ha haT) x
    exact hb.trans <| mul_le_mul_of_nonneg_right
      (fixedHeatKernelBound_anti ha har) hC1
  have hchem : ∀ x, |restartChemDuhamelM p a h u v r x| ≤
      criticalChemCoefficient p T a C *
        (M + 1) ^ (4 / 5 : ℝ) := by
    intro x
    have hb := restartChemDuhamelM_two_scale_abs_le
      hsol ha hh hahT hm hp.le hγp hpower hM hslab hε hεr x
    have hs := critical_two_scale_terms_le ha hM har hrT hAchem hDchem
    calc
      |restartChemDuhamelM p a h u v r x| ≤
          (r - ε) * ((Cspec / ε ^ 2) * Q₁) +
            Cg * (2 * Real.sqrt ε) * (M * G) := by
              simpa [Cspec, Q₁, Cg, G] using hb
      _ = (r - ε) * (Achem / ε ^ 2) +
          Dchem * (M * Real.sqrt ε) := by
            dsimp [Achem, Dchem]
            field_simp [ne_of_gt hε]
      _ ≤ (T * (Achem / a ^ 2) + Dchem * Real.sqrt a) *
          (M + 1) ^ (4 / 5 : ℝ) := by
            simpa [ε] using hs
      _ = criticalChemCoefficient p T a C *
          (M + 1) ^ (4 / 5 : ℝ) := by
            simp only [criticalChemCoefficient]
            dsimp [G, Q₁, Achem, Dchem, Cspec, Cg]
  have hlog : ∀ x, restartLogisticDuhamelM p a h u r x ≤ h * L := by
    intro x
    have hb := restartLogisticDuhamelM_le_of_guard hsol ha hh hahT hr hsource x
    exact hb.trans (mul_le_mul_of_nonneg_right hrh hL)
  let R : ℝ := fixedHeatKernelBound a * (C + 1) +
    |p.χ₀| *
      (criticalChemCoefficient p T a C *
        (M + 1) ^ (4 / 5 : ℝ)) + h * L
  have hcand : ∀ x, faithfulRestartDuhamelM p a h u v r x ≤ R := by
    intro x
    unfold faithfulRestartDuhamelM
    dsimp [R]
    have hh₀ := hhom x
    have hc₀ := hchem x
    have hl₀ := hlog x
    have hχ : 0 ≤ |p.χ₀| := abs_nonneg _
    have hchemMul :
        -p.χ₀ * restartChemDuhamelM p a h u v r x ≤
          |p.χ₀| * |restartChemDuhamelM p a h u v r x| := by
      calc
        -p.χ₀ * restartChemDuhamelM p a h u v r x ≤
            |-p.χ₀ * restartChemDuhamelM p a h u v r x| := le_abs_self _
        _ = |p.χ₀| * |restartChemDuhamelM p a h u v r x| := by
          rw [abs_mul, abs_neg]
    nlinarith [le_abs_self
      (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator r
        (intervalDomainLift (u a)) x),
      mul_le_mul_of_nonneg_left hc₀ hχ]
  have haeEq := faithfulRestartDuhamelM_ae_eq_solution
    hsol ha hh hahT hr hrh
  have haeLe : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      intervalDomainLift (u (a + r)) x ≤ R := by
    filter_upwards [haeEq] with x hx
    rw [← hx]
    exact hcand x
  have har0 : 0 < a + r := by linarith
  have harT : a + r < T :=
    lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hrh a) hahT
  have hcont := solution_lift_continuousOn_Icc hsol ⟨har0, harT⟩
  simpa [R] using continuousOn_le_of_ae_le_Ioc hcont haeLe

/-- Complete finite-horizon boundedness in the positive-sensitivity critical
branch of the faithful equation. -/
theorem critical_bounded_before_positive
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  obtain ⟨pExp, hpExp, hLp⟩ := exists_critical_lp_above_gamma
    hguard hu₀ hsol htrace hbeta hm hchi hthreshold
  have hp : 1 < pExp := lt_of_le_of_lt (le_max_left _ _) hpExp
  have hγp : p.γ ≤ pExp :=
    (le_max_right (1 : ℝ) p.γ).trans hpExp.le
  obtain ⟨C, hpower⟩ := hLp
  obtain ⟨δ, hδ, E, hE, hearly⟩ :=
    exists_initial_trace_pointwise_upper hu₀ hsol htrace
  obtain ⟨L, hL, hsource⟩ := exists_logistic_source_upper_of_guard p hguard
  let a : ℝ := min (δ / 4) (T / 4)
  have ha : 0 < a := lt_min
    (div_pos hδ (by norm_num)) (div_pos hsol.1 (by norm_num))
  have h2aδ : 2 * a < δ := by
    have haδ : a ≤ δ / 4 := min_le_left _ _
    linarith
  have h2aT : 2 * a < T := by
    have haT : a ≤ T / 4 := min_le_right _ _
    linarith [hsol.1]
  have haT : a < T := lt_trans (by linarith : a < 2 * a) h2aT
  have hC1 : 0 ≤ C + 1 := by
    have hγ := solution_gamma_integral_le_of_lp hsol ha haT hγp
      (hpower a ha haT)
    have hγnonneg : 0 ≤ ∫ y in (0 : ℝ)..1,
        intervalDomainLift (u a) y ^ p.γ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun y hy =>
        Real.rpow_nonneg
          (solution_lift_pos_Icc hsol ⟨ha, haT⟩ y (by
            simpa [Set.uIcc_of_le zero_le_one] using hy)).le _)
    linarith
  have hKchem : 0 ≤ criticalChemCoefficient p T a C := by
    let G : ℝ := 2 * p.ν * (C + 1)
    let Q₁ : ℝ := (C + 1) * G
    let Achem : ℝ :=
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant * Q₁
    let Dchem : ℝ :=
      2 * ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant * G
    have hG : 0 ≤ G := by
      dsimp [G]
      exact mul_nonneg (mul_nonneg (by norm_num) p.hν.le) hC1
    have hQ₁ : 0 ≤ Q₁ := mul_nonneg hC1 hG
    have hAchem : 0 ≤ Achem := by
      dsimp [Achem]
      exact mul_nonneg
        ShenWork.HeatKernelGradientEstimates.unitIntervalCosineGradientL1LinftyConstant_nonneg
        hQ₁
    have hDchem : 0 ≤ Dchem := by
      dsimp [Dchem]
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg)
        hG
    simp only [criticalChemCoefficient]
    exact add_nonneg
      (mul_nonneg hsol.1.le (div_nonneg hAchem (sq_nonneg a)))
      (mul_nonneg hDchem (Real.sqrt_nonneg a))
  let A : ℝ := fixedHeatKernelBound a * (C + 1) + T * L
  let B : ℝ := |p.χ₀| * criticalChemCoefficient p T a C
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg (fixedHeatKernelBound_nonneg a) hC1)
      (mul_nonneg hsol.1.le hL)
  have hB : 0 ≤ B :=
    mul_nonneg (abs_nonneg _) hKchem
  obtain ⟨R, hR, hscalar⟩ :=
    exists_uniform_bound_of_sublinear_inequality
      (m := (4 / 5 : ℝ)) (A := A + 1) (B := B)
      (by norm_num) (by norm_num) (by linarith) hB
  refine ⟨max E R, ?_⟩
  intro t ht0 htT
  change intervalDomainSupNorm (u t) ≤ max E R
  unfold intervalDomainSupNorm
  apply csSup_le
  · let x₀ : intervalDomainPoint := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    exact ⟨|u t x₀|, ⟨x₀, rfl⟩⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  change |u t x| ≤ max E R
  rw [abs_of_pos (u_pos hsol ht0 htT x)]
  by_cases htEarly : t < 2 * a
  · exact (hearly t ht0 (htEarly.trans h2aδ) x).trans (le_max_left _ _)
  · have h2at : 2 * a ≤ t := le_of_not_gt htEarly
    let h : ℝ := t - a
    have hh : 0 ≤ h := by dsimp [h]; linarith
    have hha : a ≤ h := by dsimp [h]; linarith
    have haht : a + h = t := by dsimp [h]; ring
    have hahT : a + h < T := by simpa [haht] using htT
    let Kset : Set (ℝ × ℝ) := Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) 1
    let F : ℝ × ℝ → ℝ := fun z => restartField a h u z.1 z.2
    have hKcompact : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
    have hKne : Kset.Nonempty := by
      exact ⟨(0, 0), ⟨⟨le_rfl, hh⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
    have hFcont : ContinuousOn F Kset :=
      (restartField_continuous hsol ha hh hahT u (Or.inl rfl)).continuousOn
    obtain ⟨z, hz, hzmax⟩ := hKcompact.exists_isMaxOn hKne hFcont
    let M : ℝ := F z
    have hztime0 : 0 < a + z.1 := by linarith [hz.1.1]
    have hztimeT : a + z.1 < T := by
      have hzle : a + z.1 ≤ a + h := by
        simpa [add_comm] using add_le_add_left hz.1.2 a
      exact hzle.trans_lt hahT
    have hM : 0 ≤ M := by
      have hpos := u_pos hsol hztime0 hztimeT
        (⟨z.2, hz.2⟩ : intervalDomainPoint)
      have heq := restartField_eq_physical
        (a := a) (h := h) (w := u) hz.1 hz.2
      dsimp [M, F]
      rw [heq]
      simpa [intervalDomainLift, hz.2] using hpos.le
    have hslab : ∀ τ ∈ Icc a (a + h), ∀ q ∈ Icc (0 : ℝ) 1,
        intervalDomainLift (u τ) q ≤ M := by
      intro τ hτ q hq
      have hrange : τ - a ∈ Icc (0 : ℝ) h := by
        constructor <;> linarith [hτ.1, hτ.2]
      have hmz := hzmax (show (τ - a, q) ∈ Kset from ⟨hrange, hq⟩)
      have heq := restartField_eq_physical (a := a) (h := h) (w := u) hrange hq
      dsimp [M, F] at hmz
      rw [heq, show a + (τ - a) = τ by ring] at hmz
      exact hmz
    have hutM : u t x ≤ M := by
      have hmz := hzmax (show (h, x.1) ∈ Kset from
        ⟨Set.right_mem_Icc.mpr hh, x.property⟩)
      have heq := restartField_eq_physical
        (a := a) (h := h) (w := u) (Set.right_mem_Icc.mpr hh) x.property
      dsimp [M, F] at hmz
      rw [heq, haht] at hmz
      simpa [intervalDomainLift, x.property] using hmz
    have hMbound : M ≤ max E R := by
      by_cases hzEarly : z.1 < a
      · have htimeEarly : a + z.1 < 2 * a := by linarith
        have hME := hearly (a + z.1) hztime0
          (htimeEarly.trans h2aδ) (⟨z.2, hz.2⟩ : intervalDomainPoint)
        have heq := restartField_eq_physical (a := a) (h := h) (w := u) hz.1 hz.2
        have hME' : M ≤ E := by
          dsimp [M, F]
          rw [heq]
          simpa [intervalDomainLift, hz.2] using hME
        exact hME'.trans (le_max_left _ _)
      · have haz : a ≤ z.1 := le_of_not_gt hzEarly
        have hslice := solutionSlice_le_of_restart_critical_lp_slab_guard
          hsol ha hh hahT haz hz.1.2 hm hp hγp hpower hM hslab hL hsource
          z.2 hz.2
        have heq := restartField_eq_physical (a := a) (h := h) (w := u) hz.1 hz.2
        have hraw : M ≤ fixedHeatKernelBound a * (C + 1) +
            |p.χ₀| * (criticalChemCoefficient p T a C *
              (M + 1) ^ (4 / 5 : ℝ)) + h * L := by
          have hMeq : M = intervalDomainLift (u (a + z.1)) z.2 := by
            dsimp [M, F]
            exact heq
          calc
            M = intervalDomainLift (u (a + z.1)) z.2 := hMeq
            _ ≤ _ := hslice
        have hhT : h ≤ T := by dsimp [h]; linarith
        have hlogLe : h * L ≤ T * L :=
          mul_le_mul_of_nonneg_right hhT hL
        have hchemRewrite : |p.χ₀| *
            (criticalChemCoefficient p T a C *
              (M + 1) ^ (4 / 5 : ℝ)) =
              B * (M + 1) ^ (4 / 5 : ℝ) := by
          dsimp [B]
          ring
        rw [hchemRewrite] at hraw
        have hineq : M + 1 ≤
            (A + 1) + B * (M + 1) ^ (4 / 5 : ℝ) := by
          dsimp [A]
          linarith
        have hX : 0 ≤ M + 1 := by linarith
        have hXR : M + 1 ≤ R := hscalar (M + 1) hX hineq
        have hMR : M ≤ R := by linarith
        exact hMR.trans (le_max_right _ _)
    exact hutM.trans hMbound

/-- At `m = 1`, a legacy interval-domain classical solution is also a
classical solution for the faithful linear-flux domain. -/
theorem classicalSolution_intervalDomainM_of_m_eq_one
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : p.m = 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v) :
    IsPaper2ClassicalSolution intervalDomainM p T u v := by
  simpa [IsPaper2ClassicalSolution, intervalDomainM, intervalDomain,
    intervalDomainChemotaxisDivM, intervalDomainChemotaxisDiv, hm] using hsol

/-- Positive-sensitivity realization of the exact finite-horizon
`hcriticalBootstrap` frontier in the legacy Theorem 1.2 assembly.

The two elliptic mechanisms remain separate upstream: Proposition 2.2 gives
the all-exponent cross-diffusion estimate with `rho = gamma`, while the
`(1 + v) ^ (-(2 * beta - 1))` test gives the admissible finite seed. -/
theorem criticalBootstrapFrontier_positive_intervalDomain
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b) (hchiPos : 0 < p.χ₀) :
    0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
    p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        ∃ rho > 0,
          CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
            ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
              LpPowerBoundedBefore intervalDomain p0 T u := by
  intro _ha _hb hbeta hm hthreshold u₀ hu₀ T _hT u v hsol htrace
  have hu₀M : PositiveInitialDatum intervalDomainM u₀ := by
    simpa [intervalDomainM, intervalDomain] using hu₀
  have htraceM : InitialTrace intervalDomainM u₀ u := by
    simpa [intervalDomainM, intervalDomain] using htrace
  obtain ⟨p0, hp0, hLpM⟩ :=
    exists_high_critical_lp_power_bounded_before hguard hu₀M
      (classicalSolution_intervalDomainM_of_m_eq_one hm hsol) htraceM
      hbeta hm hchiPos hthreshold
  have hLp : LpPowerBoundedBefore intervalDomain p0 T u := by
    simpa [intervalDomainM, intervalDomain] using hLpM
  exact ⟨p.γ, p.hγ,
    intervalDomain_crossDiffusionBootstrapEstimate_sharp hsol hbeta,
    p0, hp0, hLp⟩

/-- Legacy-domain form of the finite-horizon positive critical bound.  Its
proof uses the signal-weighted critical seed and stops after one finite
exponent above `max 1 gamma`. -/
theorem critical_bounded_before_positive_intervalDomain
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hu₀M : PositiveInitialDatum intervalDomainM u₀ := by
    simpa [intervalDomainM, intervalDomain] using hu₀
  have htraceM : InitialTrace intervalDomainM u₀ u := by
    simpa [intervalDomainM, intervalDomain] using htrace
  have hboundedM : IsPaper2BoundedBefore intervalDomainM T u :=
    critical_bounded_before_positive hguard hu₀M
      (classicalSolution_intervalDomainM_of_m_eq_one hm hsol)
      htraceM hbeta hm hchi hthreshold
  simpa [IsPaper2BoundedBefore, intervalDomainM, intervalDomain] using hboundedM

#print axioms solution_one_integral_le_of_lp
#print axioms restartFluxM_integral_abs_le_of_lp
#print axioms restartChemDuhamelM_far_abs_le_of_lp
#print axioms restartChemDuhamelM_near_abs_le_of_slab
#print axioms restartChemDuhamelM_two_scale_abs_le
#print axioms critical_two_scale_terms_le
#print axioms solutionSlice_le_of_restart_critical_lp_slab_guard
#print axioms criticalBootstrapFrontier_positive_intervalDomain
#print axioms critical_bounded_before_positive
#print axioms critical_bounded_before_positive_intervalDomain

end ShenWork.Paper2.IntervalDomainM

end
