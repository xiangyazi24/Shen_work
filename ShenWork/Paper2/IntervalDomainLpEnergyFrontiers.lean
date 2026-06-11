import ShenWork.Paper2.IntervalDomainLpTimeLeibniz
import ShenWork.Paper2.IntervalDomainL2PDEIntegral
import ShenWork.Paper2.IntervalDomainL2CrossControl
import ShenWork.Paper2.IntervalDomainNeumannIBP
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity

open ShenWork.IntervalDomain MeasureTheory Set
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalFullKernelRegularity

theorem intervalDomain_solution_lift_u_pos
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 < intervalDomainLift (u t) y := by
  have hval :
      intervalDomainLift (u t) y = u t ⟨y, hy⟩ := by
    simp [intervalDomainLift, hy]
  rw [hval]
  exact hsol.u_pos' ht0 htT

theorem intervalDomainLpDiffusionTest_lift_eq_on_Icc
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    Set.EqOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (fun y =>
        (intervalDomainLift (u t) y) ^ (pExp - 2) *
          intervalDomainLift (u t) y)
      (Set.Icc (0 : ℝ) 1) := by
  intro y hy
  have hpos : 0 < u t (⟨y, hy⟩ : intervalDomain.Point) :=
    hsol.u_pos' (x := (⟨y, hy⟩ : intervalDomain.Point)) ht0 htT
  simp [intervalDomainLift, intervalDomainLpDiffusionTest, hy, abs_of_pos hpos]

theorem intervalDomainLpDiffusionTest_contDiffOn_two_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContDiffOn ℝ 2
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.Icc (0 : ℝ) 1) := by
  have hCu : ContDiffOn ℝ 2
      (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hne :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u t) y ≠ 0 := by
    intro y hy
    exact ne_of_gt (intervalDomain_solution_lift_u_pos hsol ht0 htT hy)
  have hpow : ContDiffOn ℝ 2
      (fun y => (intervalDomainLift (u t) y) ^ (pExp - 2))
      (Set.Icc (0 : ℝ) 1) :=
    hCu.rpow_const_of_ne hne
  have hprod : ContDiffOn ℝ 2
      (fun y =>
        (intervalDomainLift (u t) y) ^ (pExp - 2) *
          intervalDomainLift (u t) y)
      (Set.Icc (0 : ℝ) 1) :=
    hpow.mul hCu
  exact hprod.congr
    (intervalDomainLpDiffusionTest_lift_eq_on_Icc hsol ht0 htT)

theorem intervalDomainLift_laplacian_intervalIntegrable_of_contDiffOn
    {f : intervalDomain.Point → ℝ}
    (hf : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (intervalDomainLift (fun x => intervalDomain.laplacian f x))
      volume 0 1 := by
  have hderiv2 :
      IntervalIntegrable (deriv (deriv (intervalDomainLift f))) volume 0 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hf
  refine hderiv2.congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  have hne1 : ∀ᵐ y ∂volume, y ≠ (1 : ℝ) := by
    have heq : {y : ℝ | ¬ y ≠ 1} = {(1 : ℝ)} := by
      ext y
      simp
    rw [ae_iff, heq]
    exact Real.volume_singleton
  filter_upwards [hne1] with y hyne hymem
  rw [Set.uIoc_of_le zero_le_one] at hymem
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hymem.1, lt_of_le_of_ne hymem.2 hyne⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
  simp only [intervalDomainLift, hyIcc, dif_pos]
  change deriv (fun y => deriv (intervalDomainLift f) y) y =
    intervalDomainLaplacian f ⟨y, hyIcc⟩
  rfl

theorem intervalDomainLift_lp_diffusion_intervalIntegrable_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift
        (fun x =>
          intervalDomainLpDiffusionTest pExp u t x *
            intervalDomain.laplacian (u t) x))
      volume 0 1 := by
  have hCu : ContDiffOn ℝ 2
      (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have htest_cont : ContinuousOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact
      (intervalDomainLpDiffusionTest_contDiffOn_two_of_regularity
        hsol ht0 htT).continuousOn
  have hlap :
      IntervalIntegrable
        (intervalDomainLift (fun x => intervalDomain.laplacian (u t) x))
        volume 0 1 :=
    intervalDomainLift_laplacian_intervalIntegrable_of_contDiffOn hCu
  have hfun :
      intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              intervalDomain.laplacian (u t) x) =
        fun y =>
          intervalDomainLift (intervalDomainLpDiffusionTest pExp u t) y *
            intervalDomainLift
              (fun x => intervalDomain.laplacian (u t) x) y := by
    funext y
    exact intervalDomainLift_mul _ _ y
  rw [hfun]
  exact hlap.continuousOn_mul htest_cont

theorem intervalDomainLift_lp_chemotaxis_intervalIntegrable_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift
        (fun x =>
          intervalDomainLpDiffusionTest pExp u t x *
            intervalDomain.chemotaxisDiv params (u t) (v t) x))
      volume 0 1 := by
  have htest_cont : ContinuousOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact
      (intervalDomainLpDiffusionTest_contDiffOn_two_of_regularity
        hsol ht0 htT).continuousOn
  have hchem :
      IntervalIntegrable
        (intervalDomainLift
          (intervalDomain.chemotaxisDiv params (u t) (v t)))
        volume 0 1 :=
    intervalDomainLift_chemDiv_intervalIntegrable_of_regularity
      hsol ht0 htT
  have hfun :
      intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              intervalDomain.chemotaxisDiv params (u t) (v t) x) =
        fun y =>
          intervalDomainLift (intervalDomainLpDiffusionTest pExp u t) y *
            intervalDomainLift
              (intervalDomain.chemotaxisDiv params (u t) (v t)) y := by
    funext y
    exact intervalDomainLift_mul _ _ y
  rw [hfun]
  exact hchem.continuousOn_mul htest_cont

theorem intervalDomainLift_reaction_continuousOn_of_regularity
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContinuousOn
      (intervalDomainLift
        (fun x =>
          u t x * (params.a - params.b * (u t x) ^ params.α)))
      (Set.uIcc (0 : ℝ) 1) := by
  rw [Set.uIcc_of_le zero_le_one]
  have hCu : ContDiffOn ℝ 2
      (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hU : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    hCu.continuousOn
  have hne :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u t) y ≠ 0 := by
    intro y hy
    exact ne_of_gt (intervalDomain_solution_lift_u_pos hsol ht0 htT hy)
  have hpow : ContinuousOn
      (fun y => (intervalDomainLift (u t) y) ^ params.α)
      (Set.Icc (0 : ℝ) 1) :=
    hU.rpow_const (fun y hy => Or.inl (hne y hy))
  have hcomp : ContinuousOn
      (fun y =>
        intervalDomainLift (u t) y *
          (params.a - params.b * (intervalDomainLift (u t) y) ^ params.α))
      (Set.Icc (0 : ℝ) 1) :=
    hU.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
  refine hcomp.congr ?_
  intro y hy
  simp [intervalDomainLift, hy]

theorem intervalDomainLift_lp_logistic_intervalIntegrable_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift
        (fun x =>
          intervalDomainLpDiffusionTest pExp u t x *
            (u t x * (params.a - params.b * (u t x) ^ params.α))))
      volume 0 1 := by
  have htest_cont : ContinuousOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact
      (intervalDomainLpDiffusionTest_contDiffOn_two_of_regularity
        hsol ht0 htT).continuousOn
  have hreact_cont :=
    intervalDomainLift_reaction_continuousOn_of_regularity
      hsol ht0 htT
  have hreact_int :
      IntervalIntegrable
        (intervalDomainLift
          (fun x =>
            u t x * (params.a - params.b * (u t x) ^ params.α)))
        volume 0 1 :=
    hreact_cont.intervalIntegrable
  have hfun :
      intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              (u t x * (params.a - params.b * (u t x) ^ params.α))) =
        fun y =>
          intervalDomainLift (intervalDomainLpDiffusionTest pExp u t) y *
            intervalDomainLift
              (fun x =>
                u t x * (params.a - params.b * (u t x) ^ params.α)) y := by
    funext y
    exact intervalDomainLift_mul _ _ y
  rw [hfun]
  exact hreact_int.continuousOn_mul htest_cont

theorem intervalDomain_lp_energy_hPDEIntegral_of_integrable
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hA : IntervalIntegrable
        (intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              intervalDomain.laplacian (u t) x))
        volume 0 1)
    (hB : IntervalIntegrable
        (intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              intervalDomain.chemotaxisDiv params (u t) (v t) x))
        volume 0 1)
    (hC : IntervalIntegrable
        (intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              (u t x * (params.a - params.b * (u t x) ^ params.α))))
        volume 0 1) :
    intervalDomain.integral (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
      intervalDomainLpDiffusionIntegral pExp u t -
        params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
        intervalDomainLpLogisticIntegral params pExp u t := by
  classical
  have hAB : IntervalIntegrable
      (fun y =>
        intervalDomainLift
            (fun x =>
              intervalDomainLpDiffusionTest pExp u t x *
                intervalDomain.laplacian (u t) x) y -
          params.χ₀ * intervalDomainLift
            (fun x =>
              intervalDomainLpDiffusionTest pExp u t x *
                intervalDomain.chemotaxisDiv params (u t) (v t) x) y)
      volume 0 1 := hA.sub (hB.const_mul params.χ₀)
  have hcomb :
      (∫ y in (0 : ℝ)..1,
          (intervalDomainLift
              (fun x =>
                intervalDomainLpDiffusionTest pExp u t x *
                  intervalDomain.laplacian (u t) x) y -
            params.χ₀ * intervalDomainLift
              (fun x =>
                intervalDomainLpDiffusionTest pExp u t x *
                  intervalDomain.chemotaxisDiv params (u t) (v t) x) y +
            intervalDomainLift
              (fun x =>
                intervalDomainLpDiffusionTest pExp u t x *
                  (u t x *
                    (params.a - params.b * (u t x) ^ params.α))) y))
        = intervalDomainLpDiffusionIntegral pExp u t -
            params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
            intervalDomainLpLogisticIntegral params pExp u t := by
    rw [intervalIntegral.integral_add hAB hC,
      intervalIntegral.integral_sub hA (hB.const_mul params.χ₀),
      intervalIntegral.integral_const_mul]
    rfl
  rw [← hcomb]
  change intervalDomainIntegral (intervalDomainLpEnergyWeightedTimeTerm pExp u t)
    = _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr_ae ?_
  have hne1 : ∀ᵐ y ∂volume, y ≠ (1 : ℝ) := by
    have heq : {y : ℝ | ¬ y ≠ 1} = {(1 : ℝ)} := by
      ext y
      simp
    rw [ae_iff, heq]
    exact Real.volume_singleton
  filter_upwards [hne1] with y hyne hymem
  rw [Set.uIoc_of_le zero_le_one] at hymem
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hymem.1, lt_of_le_of_ne hymem.2 hyne⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
  have hxin : (⟨y, hyIcc⟩ : intervalDomain.Point) ∈ intervalDomain.inside :=
    hyIoo
  have hpde :=
    intervalDomain_solution_lp_weighted_timeDeriv_eq_pde
      (pExp := pExp) hsol ht0 htT hxin
  have hlift : ∀ f : intervalDomain.Point → ℝ,
      intervalDomainLift f y = f ⟨y, hyIcc⟩ := by
    intro f
    simp [intervalDomainLift, hyIcc]
  simp only [hlift]
  rw [hpde]
  simp [intervalDomainLpDiffusionTest]
  ring_nf

theorem intervalDomain_lp_energy_hPDEIntegral_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
      intervalDomainLpDiffusionIntegral pExp u t -
        params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
        intervalDomainLpLogisticIntegral params pExp u t :=
  intervalDomain_lp_energy_hPDEIntegral_of_integrable hsol ht0 htT
    (intervalDomainLift_lp_diffusion_intervalIntegrable_of_regularity
      hsol ht0 htT)
    (intervalDomainLift_lp_chemotaxis_intervalIntegrable_of_regularity
      hsol ht0 htT)
    (intervalDomainLift_lp_logistic_intervalIntegrable_of_regularity
      hsol ht0 htT)

theorem intervalDomain_lp_energy_hPDEIntegral_frontier
    {params : CM2Params} {T pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ t, 0 < t → t < T →
      intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
        intervalDomainLpDiffusionIntegral pExp u t -
          params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t := by
  intro t ht0 htT
  exact intervalDomain_lp_energy_hPDEIntegral_of_regularity hsol ht0 htT

theorem intervalDomain_solution_derivWithin_u_left_zero
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) 0 = 0 := by
  have hset : (Set.Ici (0 : ℝ)) =ᶠ[𝓝 (0 : ℝ)] Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    simp only [eq_iff_iff]
    exact ⟨fun h0 => ⟨h0, le_of_lt hx⟩, fun h => h.1⟩
  have hN := (hsol.neumann ht0 htT intervalDomain_leftEndpoint_mem_boundary).1
  have hNeq :
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint =
        derivWithin (intervalDomainLift (u t)) (Set.Ici (0 : ℝ)) 0 := by
    change intervalDomainNormalDeriv (u t) intervalDomainLeftEndpoint = _
    unfold intervalDomainNormalDeriv
    rw [if_pos (show (intervalDomainLeftEndpoint : intervalDomainPoint).1 = 0
      from rfl)]
  rw [hNeq, derivWithin_congr_set hset] at hN
  exact hN

theorem intervalDomain_solution_derivWithin_u_right_zero
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) 1 = 0 := by
  have hset : (Set.Iic (1 : ℝ)) =ᶠ[𝓝 (1 : ℝ)] Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    simp only [eq_iff_iff]
    exact ⟨fun h1 => ⟨le_of_lt hx, h1⟩, fun h => h.2⟩
  have hN := (hsol.neumann ht0 htT intervalDomain_rightEndpoint_mem_boundary).1
  have hNeq :
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint =
        derivWithin (intervalDomainLift (u t)) (Set.Iic (1 : ℝ)) 1 := by
    change intervalDomainNormalDeriv (u t) intervalDomainRightEndpoint = _
    unfold intervalDomainNormalDeriv
    rw [if_neg (show ¬ (intervalDomainRightEndpoint : intervalDomainPoint).1 = 0
        by norm_num [intervalDomainRightEndpoint]),
      if_pos (show (intervalDomainRightEndpoint : intervalDomainPoint).1 = 1
        from rfl)]
  rw [hNeq, derivWithin_congr_set hset] at hN
  exact hN

theorem intervalDomain_lp_energy_hIBP_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpDiffusionIntegral pExp u t =
      intervalDomainNeumannBoundaryTerm
          (intervalDomainLpDiffusionTest pExp u t) (u t) -
        intervalDomainLpDiffusionDissipation pExp u t := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hCu : ContDiffOn ℝ 2
      (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have htestC2 : ContDiffOn ℝ 2
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.Icc (0 : ℝ) 1) :=
    intervalDomainLpDiffusionTest_contDiffOn_two_of_regularity
      hsol ht0 htT
  have hdw0 :
      derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) 0 = 0 :=
    intervalDomain_solution_derivWithin_u_left_zero hsol ht0 htT
  have hdw1 :
      derivWithin (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) 1 = 0 :=
    intervalDomain_solution_derivWithin_u_right_zero hsol ht0 htT
  have htest_cont : ContinuousOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.Icc 0 1) :=
    htestC2.continuousOn
  have hf1_cont : ContinuousOn (deriv (intervalDomainLift (u t)))
      (Set.Icc 0 1) :=
    deriv_intervalDomainLift_continuousOn_Icc_of_regularity hCu hdw0 hdw1
  have htest_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
        (deriv
          (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t)) x)
        (Set.Ioi x) x := fun x hx =>
    (hasDerivAt_of_contDiffOn_two_interior htestC2 hx).hasDerivWithinAt
  have hf_deriv2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (deriv (intervalDomainLift (u t)))
        (deriv (deriv (intervalDomainLift (u t))) x) (Set.Ioi x) x :=
    fun x hx =>
      (hasDerivAt_deriv_of_contDiffOn_two_interior hCu hx).hasDerivWithinAt
  have htest1_int : IntervalIntegrable
      (deriv (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t)))
      volume 0 1 :=
    intervalIntegrable_deriv_of_contDiffOn_two htestC2
  have hf2_int : IntervalIntegrable
      (deriv (deriv (intervalDomainLift (u t)))) volume 0 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hCu
  have hbdryR :
      deriv (intervalDomainLift (u t)) 1 =
        intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint := by
    rw [deriv_intervalDomainLift_eq_zero_at_one,
      (hsol.neumann ht0 htT intervalDomain_rightEndpoint_mem_boundary).1]
  have hbdryL :
      deriv (intervalDomainLift (u t)) 0 =
        intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint := by
    rw [deriv_intervalDomainLift_eq_zero_at_zero,
      (hsol.neumann ht0 htT intervalDomain_leftEndpoint_mem_boundary).1]
  exact intervalDomain_spatial_integrationByParts_identity
    (intervalDomainLpDiffusionTest pExp u t) (u t)
    htest_cont hf1_cont htest_deriv hf_deriv2
    htest1_int hf2_int hbdryR hbdryL

theorem intervalDomain_lp_energy_hIBP_frontier
    {params : CM2Params} {T pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ t, 0 < t → t < T →
      intervalDomainLpDiffusionIntegral pExp u t =
        intervalDomainNeumannBoundaryTerm
            (intervalDomainLpDiffusionTest pExp u t) (u t) -
          intervalDomainLpDiffusionDissipation pExp u t := by
  intro t ht0 htT
  exact intervalDomain_lp_energy_hIBP_of_regularity hsol ht0 htT

theorem intervalDomain_lp_energy_balance_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : pExp ≠ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    (1 / pExp) *
        deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
      intervalDomainLpDiffusionDissipation pExp u t =
        -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
          intervalDomainLpLogisticIntegral params pExp u t := by
  have hNeuR :
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_rightEndpoint_mem_boundary).1
  have hNeuL :
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0 :=
    (hsol.neumann ht0 htT intervalDomain_leftEndpoint_mem_boundary).1
  exact intervalDomain_lp_energy_balance_of_frontiers
    (params := params) (T := T) (pExp := pExp) (t := t)
    (u := u) (v := v) hpExp ht0 htT
    (intervalDomain_lp_energy_hLpTime_frontier (q := pExp) hsol)
    (intervalDomain_lp_energy_hPDEIntegral_of_regularity hsol ht0 htT)
    (intervalDomain_lp_energy_hIBP_of_regularity hsol ht0 htT)
    hNeuR hNeuL

end

end ShenWork.Paper2
