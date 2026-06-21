import ShenWork.Paper2.IntervalDomainMCL

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainGNYObstruction

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMCL

lemma ae_ne_singleton (a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x ≠ a := by
  rw [MeasureTheory.ae_iff]
  simp

lemma intervalDomainLift_const_continuousOn (A : ℝ) :
    ContinuousOn (intervalDomainLift (fun _ : intervalDomain.Point => A))
      (Set.Icc (0 : ℝ) 1) := by
  refine
    (continuousOn_const :
      ContinuousOn (fun _ : ℝ => A) (Set.Icc (0 : ℝ) 1)).congr ?_
  intro x hx
  simp [intervalDomainLift, hx]

lemma intervalDomain_integral_const (A : ℝ) :
    intervalDomain.integral (fun _ : intervalDomain.Point => A) = A := by
  change intervalDomainIntegral (fun _ : intervalDomainPoint => A) = A
  unfold intervalDomainIntegral
  have hcongr :
      (∫ x in (0 : ℝ)..1,
          intervalDomainLift (fun _ : intervalDomainPoint => A) x) =
        ∫ _x in (0 : ℝ)..1, A := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    simp [intervalDomainLift, hxIcc]
  rw [hcongr]
  rw [intervalIntegral.integral_const]
  norm_num [smul_eq_mul]

lemma intervalDomain_grad_const_integral_zero (B : ℝ) :
    intervalDomain.integral (fun x : intervalDomain.Point =>
      (intervalDomain.gradNorm (fun _ : intervalDomain.Point => B) x) ^ 2) = 0 := by
  change ∫ x in (0 : ℝ)..1,
      intervalDomainLift (fun x : intervalDomainPoint =>
        (intervalDomain.gradNorm (fun _ : intervalDomain.Point => B) x) ^ 2) x = 0
  apply intervalIntegral.integral_zero_ae
  filter_upwards [ae_ne_singleton (1 : ℝ)] with x hx_ne_one hx_interval
  have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx_interval
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hxIoc.1.le, hxIoc.2⟩
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx_ne_one⟩
  have hloc :
      intervalDomainLift (fun _ : intervalDomain.Point => B) =ᶠ[𝓝 x]
        fun _ : ℝ => B := by
    filter_upwards [Icc_mem_nhds hxIoo.1 hxIoo.2] with y hy
    simp [intervalDomainLift, hy]
  have hderiv :
      deriv (intervalDomainLift (fun _ : intervalDomain.Point => B)) x = 0 := by
    rw [hloc.deriv_eq]
    simp
  simpa [intervalDomainLift, intervalDomain, intervalDomainGradNorm, hxIcc] using
    hderiv

theorem not_oldUnitIntervalPowerGNYoungForMoser :
    ¬ OldUnitIntervalPowerGNYoungForMoser := by
  intro hGN
  unfold OldUnitIntervalPowerGNYoungForMoser at hGN
  rcases hGN 1 1 1 (by norm_num) (by norm_num) (by norm_num) with
    ⟨Ceps, hCeps, hineq⟩
  let A : ℝ := Ceps + 1
  have hApos : 0 < A := by dsimp [A]; linarith
  have hcont := intervalDomainLift_const_continuousOn A
  have hnonneg : ∀ x : intervalDomain.Point, 0 ≤ (fun _ => A) x :=
    fun _ => hApos.le
  have hraw := hineq (fun _ : intervalDomain.Point => A) hcont hnonneg
  have hleft :
      intervalDomain.integral (fun _ : intervalDomain.Point => A ^ ((1 : ℝ) + 1)) =
        A ^ (2 : ℝ) := by
    rw [intervalDomain_integral_const]
    norm_num
  have hmass :
      intervalDomain.integral (fun _ : intervalDomain.Point => A ^ (1 : ℝ)) = A := by
    simpa [Real.rpow_one] using intervalDomain_integral_const (A ^ (1 : ℝ))
  have hgrad :
      intervalDomain.integral (fun x : intervalDomain.Point =>
        (intervalDomain.gradNorm
          (fun _ : intervalDomain.Point => A ^ ((1 : ℝ) / 2)) x) ^ 2) = 0 :=
    intervalDomain_grad_const_integral_zero (A ^ ((1 : ℝ) / 2))
  have hgrad' :
      intervalDomain.integral (fun x : intervalDomain.Point =>
        (intervalDomain.gradNorm
          (fun y : intervalDomain.Point =>
            (fun _ : intervalDomain.Point => A) y ^ ((1 : ℝ) / 2)) x) ^ 2) = 0 := by
    simpa using hgrad
  have hgrad'' :
      intervalDomain.integral (fun x : intervalDomain.Point =>
        (intervalDomain.gradNorm
          (fun _ : intervalDomain.Point => A ^ (2 : ℝ)⁻¹) x) ^ 2) = 0 := by
    simpa [one_div] using hgrad
  have hleft' :
      intervalDomain.integral (fun x : intervalDomain.Point =>
        (fun _ : intervalDomain.Point => A) x ^ ((1 : ℝ) + 1)) =
        A ^ (2 : ℝ) := by
    simpa using hleft
  have hmass' :
      intervalDomain.integral (fun x : intervalDomain.Point =>
        (fun _ : intervalDomain.Point => A) x ^ (1 : ℝ)) = A := by
    simpa using hmass
  have hconstMass :
      intervalDomain.integral (fun _ : intervalDomain.Point => A) = A :=
    intervalDomain_integral_const A
  have hAineq : A ^ (2 : ℝ) ≤ Ceps * A := by
    simpa [hleft', hmass', hconstMass, hgrad', hgrad''] using hraw
  have hstrict : Ceps * A < A ^ (2 : ℝ) := by
    rw [Real.rpow_two, pow_two]
    exact mul_lt_mul_of_pos_right
      (by dsimp [A]; exact lt_add_of_pos_right Ceps zero_lt_one) hApos
  exact not_lt_of_ge hAineq hstrict

#print axioms not_oldUnitIntervalPowerGNYoungForMoser

end ShenWork.Paper2.IntervalDomainGNYObstruction

end