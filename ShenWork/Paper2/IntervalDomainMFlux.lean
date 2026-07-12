import ShenWork.Paper2.IntervalDomainMLpTimeLeibniz
import ShenWork.Paper2.IntervalDomainLpEnergyFrontiers

/-!
# General-m chemotaxis flux on the unit interval

This is the closed-interval regularity and integration-by-parts package for
the published flux `u^m vₓ / (1+v)^β`.  It deliberately does not use the
legacy linear-flux resolver wrappers.
-/

open ShenWork.IntervalDomain MeasureTheory Set
open scoped Topology

namespace ShenWork.Paper2.IntervalDomainM

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalFullKernelRegularity
open ShenWork.IntervalEllipticCharacterization

/-- The paper-faithful chemotaxis flux as a real function. -/
def intervalFluxM (p : CM2Params)
    (u v : intervalDomainPoint → ℝ) (y : ℝ) : ℝ :=
  (intervalDomainLift u y) ^ p.m * deriv (intervalDomainLift v) y /
    (1 + intervalDomainLift v y) ^ p.β

theorem leftEndpoint_mem_boundaryM :
    intervalDomainLeftEndpoint ∈ intervalDomainM.boundary := by
  exact Or.inl rfl

theorem rightEndpoint_mem_boundaryM :
    intervalDomainRightEndpoint ∈ intervalDomainM.boundary := by
  exact Or.inr rfl

theorem lift_u_pos_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) y := by
  intro y hy
  simpa [intervalDomainLift, hy] using u_pos hsol ht0 htT ⟨y, hy⟩

theorem lift_v_nonneg_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift (v t) y := by
  intro y hy
  simp only [intervalDomainLift, hy, dif_pos]
  exact hsol.2.2.2.1 t ⟨y, hy⟩ ht0 htT

theorem derivWithin_left_zero
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (f : ℝ → intervalDomain.Point → ℝ)
    (hf : f = u ∨ f = v) :
    derivWithin (intervalDomainLift (f t)) (Set.Icc (0 : ℝ) 1) 0 = 0 := by
  have hset : (Set.Ici (0 : ℝ)) =ᶠ[𝓝 (0 : ℝ)] Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    simp only [eq_iff_iff]
    exact ⟨fun h0 => ⟨h0, le_of_lt hx⟩, fun h => h.1⟩
  have hNpair := hsol.2.2.2.2.2.2 t intervalDomainLeftEndpoint
    ht0 htT leftEndpoint_mem_boundaryM
  have hN : intervalDomainM.normalDeriv (f t) intervalDomainLeftEndpoint = 0 := by
    rcases hf with rfl | rfl
    · exact hNpair.1
    · exact hNpair.2
  have hNeq :
      intervalDomainM.normalDeriv (f t) intervalDomainLeftEndpoint =
        derivWithin (intervalDomainLift (f t)) (Set.Ici (0 : ℝ)) 0 := by
    change intervalDomainNormalDeriv (f t) intervalDomainLeftEndpoint = _
    unfold intervalDomainNormalDeriv
    rw [if_pos (show (intervalDomainLeftEndpoint : intervalDomainPoint).1 = 0
      from rfl)]
  rw [hNeq, derivWithin_congr_set hset] at hN
  exact hN

theorem derivWithin_right_zero
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (f : ℝ → intervalDomain.Point → ℝ)
    (hf : f = u ∨ f = v) :
    derivWithin (intervalDomainLift (f t)) (Set.Icc (0 : ℝ) 1) 1 = 0 := by
  have hset : (Set.Iic (1 : ℝ)) =ᶠ[𝓝 (1 : ℝ)] Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    simp only [eq_iff_iff]
    exact ⟨fun h1 => ⟨le_of_lt hx, h1⟩, fun h => h.2⟩
  have hNpair := hsol.2.2.2.2.2.2 t intervalDomainRightEndpoint
    ht0 htT rightEndpoint_mem_boundaryM
  have hN : intervalDomainM.normalDeriv (f t) intervalDomainRightEndpoint = 0 := by
    rcases hf with rfl | rfl
    · exact hNpair.1
    · exact hNpair.2
  have hNeq :
      intervalDomainM.normalDeriv (f t) intervalDomainRightEndpoint =
        derivWithin (intervalDomainLift (f t)) (Set.Iic (1 : ℝ)) 1 := by
    change intervalDomainNormalDeriv (f t) intervalDomainRightEndpoint = _
    unfold intervalDomainNormalDeriv
    rw [if_neg (show ¬ (intervalDomainRightEndpoint : intervalDomainPoint).1 = 0
        by norm_num [intervalDomainRightEndpoint]),
      if_pos (show (intervalDomainRightEndpoint : intervalDomainPoint).1 = 1
        from rfl)]
  rw [hNeq, derivWithin_congr_set hset] at hN
  exact hN

theorem deriv_lift_contDiffOn_one_Icc
    {f : intervalDomain.Point → ℝ}
    (hf : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    (hd0 : derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) 0 = 0)
    (hd1 : derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) 1 = 0) :
    ContDiffOn ℝ 1 (deriv (intervalDomainLift f)) (Set.Icc (0 : ℝ) 1) := by
  have hwithin : ContDiffOn ℝ 1
      (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
      (Set.Icc (0 : ℝ) 1) :=
    hf.derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
  refine hwithin.congr (fun x hx => ?_)
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · rw [← hx0, deriv_intervalDomainLift_eq_zero_at_zero, hd0]
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · rw [hx1, deriv_intervalDomainLift_eq_zero_at_one, hd1]
  exact deriv_eq_derivWithin_interior ⟨hx0, hx1⟩

theorem fluxM_contDiffOn_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContDiffOn ℝ 1 (intervalFluxM p (u t) (v t))
      (Set.Icc (0 : ℝ) 1) := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hCu : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc 0 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hCv : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Icc 0 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hu_ne : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x ≠ 0 :=
    fun x hx => ne_of_gt (lift_u_pos_Icc hsol ht0 htT x hx)
  have hv_nonneg := lift_v_nonneg_Icc hsol ht0 htT
  have hu_pow : ContDiffOn ℝ 1
      (fun x => (intervalDomainLift (u t) x) ^ p.m) (Set.Icc 0 1) :=
    (hCu.of_le (by norm_num)).rpow_const_of_ne hu_ne
  have hdv : ContDiffOn ℝ 1 (deriv (intervalDomainLift (v t))) (Set.Icc 0 1) :=
    deriv_lift_contDiffOn_one_Icc hCv
      (derivWithin_left_zero hsol ht0 htT v (Or.inr rfl))
      (derivWithin_right_zero hsol ht0 htT v (Or.inr rfl))
  have hbase : ContDiffOn ℝ 1 (fun x => 1 + intervalDomainLift (v t) x)
      (Set.Icc 0 1) := contDiffOn_const.add (hCv.of_le (by norm_num))
  have hbase_ne : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      1 + intervalDomainLift (v t) x ≠ 0 := by
    intro x hx
    have := hv_nonneg x hx
    linarith
  have hden : ContDiffOn ℝ 1
      (fun x => (1 + intervalDomainLift (v t) x) ^ p.β) (Set.Icc 0 1) :=
    hbase.rpow_const_of_ne hbase_ne
  exact (hu_pow.mul hdv).div hden
    (fun x hx => ne_of_gt (Real.rpow_pos_of_pos (by
      have := hv_nonneg x hx
      linarith) _))

theorem fluxM_contDiffOn_Ioo
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContDiffOn ℝ 1 (intervalFluxM p (u t) (v t))
      (Set.Ioo (0 : ℝ) 1) :=
  (fluxM_contDiffOn_Icc hsol ht0 htT).mono Set.Ioo_subset_Icc_self

theorem fluxM_endpoint_zero
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalFluxM p (u t) (v t) 0 = 0 ∧
      intervalFluxM p (u t) (v t) 1 = 0 := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hclosed := (hsol.regularity.2.2.2.2.1 t ht).2
  unfold intervalFluxM
  rw [hclosed.2.1, hclosed.2.2]
  simp

theorem deriv_fluxM_intervalIntegrable
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable (deriv (intervalFluxM p (u t) (v t))) volume 0 1 := by
  classical
  set f : ℝ → ℝ := intervalFluxM p (u t) (v t) with hf
  have hC1c : ContDiffOn ℝ 1 f (Set.Icc (0 : ℝ) 1) :=
    fluxM_contDiffOn_Icc hsol ht0 htT
  have hC1o : ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) 1) :=
    hC1c.mono Set.Ioo_subset_Icc_self
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) :=
    uniqueDiffOn_Icc (by norm_num)
  have hdWcont : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) 1))
      (Set.Icc (0 : ℝ) 1) :=
    hC1c.continuousOn_derivWithin huniq (by norm_num)
  have hdWint : IntervalIntegrable
      (derivWithin f (Set.Icc (0 : ℝ) 1)) volume 0 1 := by
    have hc : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) 1))
        (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hdWcont
    exact hc.intervalIntegrable
  have heq : Set.EqOn (deriv f) (derivWithin f (Set.Icc (0 : ℝ) 1))
      (Set.Ioo (0 : ℝ) 1) := by
    intro z hz
    have hd : DifferentiableAt ℝ f z :=
      (hC1o.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hz)
    rw [hd.derivWithin (huniq.uniqueDiffWithinAt (Set.Ioo_subset_Icc_self hz))]
  refine hdWint.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push Not at hy
  obtain ⟨hyIoc, hne⟩ := hy
  simp only [Set.mem_singleton_iff]
  by_contra hy1
  exact hne ((heq ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩).symm)

end

end ShenWork.Paper2.IntervalDomainM
