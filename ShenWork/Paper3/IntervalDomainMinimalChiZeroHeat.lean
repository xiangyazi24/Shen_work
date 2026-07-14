import ShenWork.Paper3.IntervalDomainMinimalUniformConvergence
import ShenWork.Paper3.IntervalDomainUniformHeatKernelFloor
import ShenWork.Paper3.IntervalDomainClassicalRestartPointwise
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta
import ShenWork.PDE.IntervalSemigroupC1ApproxIdentity
import ShenWork.Paper2.IntervalConjugateKernelIBP

/-!
# The zero-sensitivity minimal branch is the Neumann heat flow

At `chi = a = b = 0`, the faithful restarted B-form identity has no Duhamel
source.  A one-time-unit heat-kernel floor gives a quantitative decrease of
any maximum lying above the conserved physical mean.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalDomainExistence

noncomputable section

local instance intervalDomainMinimalChiZeroHeatMetricSpace : MetricSpace intervalDomainPoint :=
  inferInstanceAs (MetricSpace (Subtype (Set.Icc (0 : ℝ) 1)))

/-- On every positive-time restart, the `chi = a = b = 0` equation is exactly
the homogeneous Neumann heat semigroup. -/
theorem intervalDomain_minimal_chiZero_restart_heat
    (p : CM2Params) (hm : p.m = 1)
    (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ = 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {a : ℝ} (ha0 : 0 < a) (x : intervalDomainPoint) :
    u (a + 1) x =
      intervalFullSemigroupOperator 1 (intervalDomainLift (u a)) x.1 := by
  have hH : 0 < a + 2 := by linarith
  have hsol := huv.classical (a + 2) hH
  have hr := intervalDomain_classical_bform_restart_pointwise
    hsol hm ha0 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
      (by norm_num : (0 : ℝ) < 1) (le_rfl : (1 : ℝ) ≤ 1) x
  have hlogzero : ∀ w : intervalDomainPoint → ℝ,
      logisticLifted p w = fun _ => 0 := by
    intro w
    funext y
    unfold logisticLifted
    unfold ShenWork.IntervalDomainExistence.intervalLogisticSource
    rw [ha, hb]
    simp [intervalDomainLift]
  have hintzero :
      (∫ s in (0 : ℝ)..1,
        intervalFullSemigroupOperator (1 - s)
          (logisticLifted p (intervalDomainRestartTrajectory a 1 u s)) x.1) = 0 := by
    have hfun : (fun s : ℝ =>
        intervalFullSemigroupOperator (1 - s)
          (logisticLifted p (intervalDomainRestartTrajectory a 1 u s)) x.1) =
        fun _ => 0 := by
      funext s
      rw [hlogzero]
      unfold intervalFullSemigroupOperator
      simp
    rw [hfun]
    simp
  rw [intervalConjugateDuhamelMap, hχ, hintzero] at hr
  simpa using hr

/-- If the maximum at a positive restart lies at least `d` above the physical
mean, one unit of heat evolution lowers it by the fixed amount
`unitWindowHeatKernelFloor * d`. -/
theorem intervalDomain_minimal_chiZero_supNorm_unit_drop
    (p : CM2Params) (hm : p.m = 1)
    (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ = 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {a uStar d : ℝ} (ha0 : 0 < a)
    (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hgap : uStar + d ≤ intervalDomain.supNorm (u a)) :
    intervalDomain.supNorm (u (a + 1)) ≤
      intervalDomain.supNorm (u a) - unitWindowHeatKernelFloor * d := by
  let M : ℝ := intervalDomain.supNorm (u a)
  have hMpos : 0 < M := lt_of_lt_of_le (by linarith) hgap
  have hH : 0 < a + 2 := by linarith
  have hsol := huv.classical (a + 2) hH
  have hat : a ∈ Set.Ioo (0 : ℝ) (a + 2) := ⟨ha0, by linarith⟩
  let U : ℝ → ℝ := liftRepr (u a)
  have hU_cont : Continuous U := by
    apply liftRepr_continuous
    exact ((hsol.regularity.2.2.2.2.1 a hat).1.1).continuousOn
  have hU_eq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      U y = intervalDomainLift (u a) y := by
    intro y hy
    exact liftRepr_eq_on_Icc hy
  have hU_nonneg : ∀ y, 0 ≤ U y := by
    intro y
    dsimp [U, liftRepr]
    rw [intervalDomainLift, dif_pos (clamp01_mem y)]
    exact (hsol.u_pos' ha0 hat.2).le
  have hU_abs : ∀ y, |U y| ≤ M := by
    intro y
    dsimp [U, liftRepr, M]
    exact abs_lift_le_supNorm hsol hat (clamp01_mem y)
  have hU_le : ∀ y, U y ≤ M := fun y =>
    (le_abs_self (U y)).trans (hU_abs y)
  let f : ℝ → ℝ := fun y => M - U y
  have hf_cont : Continuous f := continuous_const.sub hU_cont
  have hf_nonneg : ∀ y, 0 ≤ f y := fun y => sub_nonneg.mpr (hU_le y)
  have hf_bound : ∀ y, |f y| ≤ M := by
    intro y
    rw [abs_of_nonneg (hf_nonneg y)]
    dsimp [f]
    linarith [hU_nonneg y]
  have hU_int : Integrable U (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound
      hU_cont.aestronglyMeasurable hU_abs
  have hf_int : Integrable f (intervalMeasure 1) :=
    (integrable_const M).sub hU_int
  have hUint : (∫ y, U y ∂(intervalMeasure 1)) = uStar := by
    rw [ShenWork.Paper2.IntervalConjugateKernelIBP.intervalMeasure_one_integral_eq_intervalIntegral]
    calc
      (∫ y in (0 : ℝ)..1, U y) =
          ∫ y in (0 : ℝ)..1, intervalDomainLift (u a) y := by
            apply intervalIntegral.integral_congr
            intro y hy
            rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
            exact hU_eq y hy
      _ = intervalDomain.integral (u a) := rfl
      _ = uStar := by simpa [intervalDomain] using hmass a ha0
  have hf_mass : (∫ y, f y ∂(intervalMeasure 1)) = M - uStar := by
    dsimp [f]
    rw [integral_sub (integrable_const M) hU_int,
      intervalMeasure_integral_const (L := (1 : ℝ)) (c := M) (by norm_num),
      hUint]
    ring
  have hpoint : ∀ x : intervalDomainPoint,
      u (a + 1) x ≤ M - unitWindowHeatKernelFloor * d := by
    intro x
    have hfloor := unitWindowHeatKernelFloor_mul_integral_le_semigroup
      (t := (1 : ℝ)) (x := x.1)
      ⟨le_rfl, by norm_num⟩ x.2 hf_int hf_cont.aestronglyMeasurable
      (fun y _hy => hf_nonneg y) hf_bound
    rw [hf_mass] at hfloor
    have hK := intervalNeumannFullKernel_integrable
      (by norm_num : (0 : ℝ) < 1) x.1
    have hKM : Integrable
        (fun y => intervalNeumannFullKernel 1 x.1 y * M)
        (intervalMeasure 1) := hK.mul_const M
    have hKU : Integrable
        (fun y => intervalNeumannFullKernel 1 x.1 y * U y)
        (intervalMeasure 1) := by
      have hmul := hK.bdd_mul hU_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact hU_abs y)
      simpa [mul_comm] using hmul
    have hlin :=
      ShenWork.IntervalGradDuhamelBound.intervalFullSemigroupOperator_sub
        hKM hKU
    have hSU : intervalFullSemigroupOperator 1 U x.1 = u (a + 1) x := by
      calc
        intervalFullSemigroupOperator 1 U x.1 =
            intervalFullSemigroupOperator 1 (intervalDomainLift (u a)) x.1 :=
          ShenWork.IntervalSemigroupC1ApproxIdentity.intervalFullSemigroupOperator_congr_on_Icc
            hU_eq 1 x.1
        _ = u (a + 1) x :=
          (intervalDomain_minimal_chiZero_restart_heat
            p hm ha hb hχ huv ha0 x).symm
    have hSf : intervalFullSemigroupOperator 1 f x.1 =
        M - u (a + 1) x := by
      dsimp [f]
      rw [hlin, intervalFullSemigroupOperator_const (by norm_num) M, hSU]
    rw [hSf] at hfloor
    have hgap' : d ≤ M - uStar := by
      dsimp [M]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hgap'
      unitWindowHeatKernelFloor_pos.le
    nlinarith
  apply intervalDomain_supNorm_le_of_pointwise_abs_le
  intro x
  rw [abs_of_nonneg ((hsol.u_pos' (by linarith) (by linarith)).le)]
  exact hpoint x

/-- The zero-sensitivity heat branch eventually enters every upper
neighbourhood of the conserved physical mean. -/
theorem intervalDomain_minimal_chiZero_eventually_supNorm_le_mass_add
    (p : CM2Params) (hm : p.m = 1)
    (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ = 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {uStar d : ℝ} (huStar : 0 < uStar) (hd : 0 < d)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
    ∀ᶠ t in atTop,
      intervalDomain.supNorm (u t) ≤ uStar + d := by
  let B : ℝ := intervalDomain.supNorm (u 1)
  let ρ : ℝ := unitWindowHeatKernelFloor
  have hρ : 0 < ρ := unitWindowHeatKernelFloor_pos
  have hρd : 0 < ρ * d := mul_pos hρ hd
  have hmassLower : ∀ t, 0 < t → uStar ≤ intervalDomain.supNorm (u t) := by
    intro t ht
    have hH : 0 < t + 1 := by linarith
    have hsol := huv.classical (t + 1) hH
    have hle := intervalDomain_classicalSolution_mass_le_supNorm hsol
      (⟨ht, by linarith⟩ : t ∈ Set.Ioo (0 : ℝ) (t + 1))
    have hm_t : intervalDomain.integral (u t) = uStar := by
      simpa [intervalDomain] using hmass t ht
    simpa [hm_t] using hle
  have hentry : ∃ n : ℕ,
      intervalDomain.supNorm (u (1 + (n : ℝ))) ≤ uStar + d := by
    by_contra hnone
    have hnone' : ∀ n : ℕ, uStar + d <
        intervalDomain.supNorm (u (1 + (n : ℝ))) := by
      intro n
      exact lt_of_not_ge (fun hle => hnone ⟨n, hle⟩)
    have hind : ∀ n : ℕ,
        intervalDomain.supNorm (u (1 + (n : ℝ))) ≤
          B - (n : ℝ) * ρ * d := by
      intro n
      induction n with
      | zero => simp [B]
      | succ n ih =>
          have hgap : uStar + d ≤
              intervalDomain.supNorm (u (1 + (n : ℝ))) :=
            (hnone' n).le
          have hdrop := intervalDomain_minimal_chiZero_supNorm_unit_drop
            p hm ha hb hχ huv (a := 1 + (n : ℝ))
              (by positivity) huStar hd hmass hgap
          have hdrop' :
              intervalDomain.supNorm (u (1 + ((n + 1 : ℕ) : ℝ))) ≤
                intervalDomain.supNorm (u (1 + (n : ℝ))) - ρ * d := by
            simpa [ρ, Nat.cast_add, Nat.cast_one, add_assoc] using hdrop
          calc
            intervalDomain.supNorm (u (1 + ((n + 1 : ℕ) : ℝ))) ≤
                intervalDomain.supNorm (u (1 + (n : ℝ))) - ρ * d := hdrop'
            _ ≤ (B - (n : ℝ) * ρ * d) - ρ * d :=
              sub_le_sub_right ih _
            _ = B - ((n + 1 : ℕ) : ℝ) * ρ * d := by
              norm_num [Nat.cast_add, Nat.cast_one]
              ring
    obtain ⟨n, hn⟩ := exists_nat_gt ((B - uStar) / (ρ * d))
    have hn' : B - uStar < (n : ℝ) * (ρ * d) :=
      (div_lt_iff₀ hρd).mp hn
    have hlower := hmassLower (1 + (n : ℝ)) (by positivity)
    have hupper := hind n
    nlinarith
  obtain ⟨n, hn⟩ := hentry
  refine eventually_atTop.2 ⟨1 + (n : ℝ), ?_⟩
  intro t ht
  exact (intervalDomain_minimal_supNorm_antitone_positiveTimes
    p ha hb hχ.le huv (by positivity) ht).trans hn

/-- Static tail rigidity upgrades convergence of the spatial maximum to
uniform convergence whenever the physical mass is fixed. -/
theorem intervalDomain_minimal_uniform_u_converges_of_eventual_max
    (p : CM2Params) (hm : p.m = 1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hmax : ∀ d, 0 < d → ∀ᶠ t in atTop,
      intervalDomain.supNorm (u t) ≤ uStar + d) :
    UniformConvergesInSup intervalDomain u uStar := by
  obtain ⟨Tlip, G, hG, hlip⟩ :=
    intervalDomain_globalBounded_eventual_lipschitz p hm huv
  unfold UniformConvergesInSup
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hstatic⟩ :=
    intervalDomain_uniform_close_of_mass_and_upper_of_lipschitz
      huStar hG (by linarith : 0 < ε / 2)
  have hmaxδ := hmax δ hδ
  apply eventually_atTop.1
  filter_upwards [hmaxδ,
    eventually_ge_atTop (max Tlip (1 : ℝ))] with t hmax_t ht
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one
    ((le_max_right Tlip (1 : ℝ)).trans ht)
  have hH : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) hH
  have htMem : t ∈ Set.Ioo (0 : ℝ) (t + 1) := ⟨htPos, by linarith⟩
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  let ft : C(intervalDomainPoint, ℝ) :=
    ⟨u t, ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous
      hsolM htMem⟩
  have hft_nonneg : ∀ x, 0 ≤ ft x := fun _x =>
    (hsol.u_pos' htMem.1 htMem.2).le
  have hft_upper : ∀ x, ft x ≤ uStar + δ := by
    intro x
    have habs := abs_lift_le_supNorm hsol htMem x.2
    have hpoint : ft x ≤ intervalDomain.supNorm (u t) :=
      le_trans (le_abs_self (ft x)) (by
        simpa [ft, intervalDomainLift, x.2] using habs)
    exact hpoint.trans hmax_t
  have hft_mass : uStar - δ ≤ intervalDomain.integral ft := by
    have hm_t : intervalDomain.integral (u t) = uStar := by
      simpa [intervalDomain] using hmass t htPos
    simpa [ft, hm_t] using (sub_le_self uStar hδ.le)
  have hft_lip : LipschitzWith ⟨G, hG⟩ ft := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxy := hlip t ((le_max_left Tlip (1 : ℝ)).trans ht)
      x.1 x.2 y.1 y.2
    simpa [ft, intervalDomainLift, x.2, y.2, Real.dist_eq] using hxy
  have hpointClose : ∀ x, |ft x - uStar| < ε / 2 :=
    hstatic ft hft_nonneg hft_upper hft_mass hft_lip
  have hsup_le : intervalDomain.supNorm (fun x => u t x - uStar) ≤ ε / 2 :=
    intervalDomain_supNorm_le_of_pointwise_abs_le
      (fun x => (hpointClose x).le)
  have hsup_nonneg : 0 ≤
      intervalDomain.supNorm (fun x => u t x - uStar) :=
    intervalDomain_supNorm_nonneg_of_pointwise_abs_bounded
      (fun x => (hpointClose x).le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nonneg]
  linarith

/-- Uniform convergence in the zero-sensitivity minimal branch. -/
theorem intervalDomain_minimal_chiZero_uniform_u_converges
    (p : CM2Params) (hm : p.m = 1)
    (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ = 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
    UniformConvergesInSup intervalDomain u uStar := by
  exact intervalDomain_minimal_uniform_u_converges_of_eventual_max
    p hm huv huStar hmass
      (fun d hd =>
        intervalDomain_minimal_chiZero_eventually_supNorm_le_mass_add
          p hm ha hb hχ huv huStar hd hmass)

/-- Uniform convergence for the full nonpositive-sensitivity minimal branch,
with the neutral mode fixed by physical mass. -/
theorem intervalDomain_minimal_chiNonpos_uniform_u_converges
    (p : CM2Params) (hm : p.m = 1)
    (ha : p.a = 0) (hb : p.b = 0) (hχ : p.χ₀ ≤ 0)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
    UniformConvergesInSup intervalDomain u uStar := by
  rcases lt_or_eq_of_le hχ with hneg | hzero
  · exact intervalDomain_minimal_chiNeg_uniform_u_converges
      p hm ha hb hneg huv huStar hmass
  · exact intervalDomain_minimal_chiZero_uniform_u_converges
      p hm ha hb hzero huv huStar hmass

#print axioms intervalDomain_minimal_chiZero_restart_heat
#print axioms intervalDomain_minimal_chiZero_supNorm_unit_drop
#print axioms intervalDomain_minimal_chiZero_eventually_supNorm_le_mass_add
#print axioms intervalDomain_minimal_uniform_u_converges_of_eventual_max
#print axioms intervalDomain_minimal_chiZero_uniform_u_converges
#print axioms intervalDomain_minimal_chiNonpos_uniform_u_converges

end

end ShenWork.Paper3
