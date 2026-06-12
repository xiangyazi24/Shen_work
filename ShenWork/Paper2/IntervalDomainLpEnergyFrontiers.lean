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

theorem intervalDomain_lp_diffusion_test_deriv_eq
    {params : CM2Params} {T t pExp y : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    deriv (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t)) y =
      (pExp - 1) * (intervalDomainLift (u t) y) ^ (pExp - 2) *
        deriv (intervalDomainLift (u t)) y := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hclosed := (hsol.regularity.2.2.2.2.1 t ht).1
  by_cases hy0 : y = 0
  · subst y
    rw [deriv_intervalDomainLift_eq_zero_at_zero, hclosed.2.1]
    ring
  by_cases hy1 : y = 1
  · subst y
    rw [deriv_intervalDomainLift_eq_zero_at_one, hclosed.2.2]
    ring
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨lt_of_le_of_ne hy.1 (fun h => hy0 h.symm),
      lt_of_le_of_ne hy.2 hy1⟩
  have hu_has :
      HasDerivAt (intervalDomainLift (u t))
        (deriv (intervalDomainLift (u t)) y) y :=
    hasDerivAt_of_contDiffOn_two_interior hclosed.1 hyIoo
  have hu_pos : 0 < intervalDomainLift (u t) y := by
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
    have hpos : 0 < u t (⟨y, hyIcc⟩ : intervalDomain.Point) :=
      hsol.u_pos' ht0 htT
    simpa [intervalDomainLift, hyIcc] using hpos
  have hpow0 :=
    hu_has.rpow_const (p := pExp - 1) (Or.inl (ne_of_gt hu_pos))
  have hpow :
      HasDerivAt (fun z => (intervalDomainLift (u t) z) ^ (pExp - 1))
        (deriv (intervalDomainLift (u t)) y *
          (pExp - 1) * (intervalDomainLift (u t) y) ^ (pExp - 2)) y := by
    refine hpow0.congr_deriv ?_
    ring_nf
  have htest_eq :
      intervalDomainLift (intervalDomainLpDiffusionTest pExp u t)
        =ᶠ[𝓝 y]
      fun z => (intervalDomainLift (u t) z) ^ (pExp - 1) := by
    filter_upwards [Ioo_mem_nhds hyIoo.1 hyIoo.2] with z hz
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
    have hpos : 0 < u t (⟨z, hzIcc⟩ : intervalDomain.Point) :=
      hsol.u_pos' ht0 htT
    simp [intervalDomainLift, intervalDomainLpDiffusionTest, hzIcc,
      abs_of_pos hpos]
    calc
      u t (⟨z, hzIcc⟩ : intervalDomain.Point) ^ (pExp - 2) *
          u t (⟨z, hzIcc⟩ : intervalDomain.Point) =
        u t (⟨z, hzIcc⟩ : intervalDomain.Point) ^ (pExp - 2) *
          u t (⟨z, hzIcc⟩ : intervalDomain.Point) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = u t (⟨z, hzIcc⟩ : intervalDomain.Point) ^
            ((pExp - 2) + 1) := by
          rw [Real.rpow_add hpos]
      _ = u t (⟨z, hzIcc⟩ : intervalDomain.Point) ^ (pExp - 1) := by
          congr 1
          ring
  have htest_has := hpow.congr_of_eventuallyEq htest_eq
  have hderiv_test :
      deriv (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t)) y =
        deriv (intervalDomainLift (u t)) y *
          (pExp - 1) * (intervalDomainLift (u t) y) ^ (pExp - 2) :=
    htest_has.deriv
  rw [hderiv_test]
  ring

theorem intervalDomain_lp_diffusion_test_deriv_mul_deriv_eq
    {params : CM2Params} {T t pExp y : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    deriv (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t)) y *
        deriv (intervalDomainLift (u t)) y =
      (pExp - 1) *
        ((intervalDomainLift (u t) y) ^ (pExp - 2) *
          |deriv (intervalDomainLift (u t)) y| ^ 2) := by
  rw [intervalDomain_lp_diffusion_test_deriv_eq
    (pExp := pExp) hsol ht0 htT hy]
  ring_nf
  rw [sq_abs]

theorem intervalDomain_lp_diffusion_dissipation_eq_weighted_gradient
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpDiffusionDissipation pExp u t =
      (pExp - 1) * intervalDomainLpWeightedGradientDissipation pExp u t := by
  unfold intervalDomainLpDiffusionDissipation
  unfold intervalDomainDerivativePairIntegral
  unfold intervalDomainLpWeightedGradientDissipation
  change (∫ y in (0 : ℝ)..1, _) =
    (pExp - 1) * intervalDomainIntegral _
  unfold intervalDomainIntegral
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hy
  have hpoint :=
    intervalDomain_lp_diffusion_test_deriv_mul_deriv_eq
      (pExp := pExp) hsol ht0 htT hy
  simpa [intervalDomainLift, hy, intervalDomain, intervalDomainGradNorm,
    sq_abs, mul_assoc]
    using hpoint

theorem intervalDomain_lp_weighted_gradient_dissipation_nonneg_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    0 ≤ intervalDomainLpWeightedGradientDissipation pExp u t := by
  unfold intervalDomainLpWeightedGradientDissipation
  change 0 ≤ intervalDomainIntegral _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_nonneg (by norm_num) (fun y hy => ?_)
  have hu_pos : 0 < u t (⟨y, hy⟩ : intervalDomain.Point) :=
    hsol.u_pos' ht0 htT
  simp [intervalDomainLift, hy, intervalDomain, intervalDomainGradNorm]
  exact mul_nonneg (Real.rpow_nonneg hu_pos.le _) (sq_nonneg _)

theorem intervalDomain_lp_logisticIntegral_le_a_energy_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpLogisticIntegral params pExp u t ≤
      params.a * intervalDomainLpEnergy pExp u t := by
  classical
  have hleft :
      IntervalIntegrable
        (intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              (u t x * (params.a - params.b * (u t x) ^ params.α))))
        volume 0 1 :=
    intervalDomainLift_lp_logistic_intervalIntegrable_of_regularity
      hsol ht0 htT
  have hCu : ContDiffOn ℝ 2
      (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hne :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u t) y ≠ 0 := by
    intro y hy
    exact ne_of_gt (intervalDomain_solution_lift_u_pos hsol ht0 htT hy)
  have hpow_cont : ContinuousOn
      (fun y => (intervalDomainLift (u t) y) ^ pExp)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact hCu.continuousOn.rpow_const (fun y hy => Or.inl (hne y hy))
  have hright : IntervalIntegrable
      (fun y => params.a * (intervalDomainLift (u t) y) ^ pExp)
      volume 0 1 :=
    hpow_cont.intervalIntegrable.const_mul _
  have hpoint : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              (u t x * (params.a - params.b * (u t x) ^ params.α))) y ≤
        params.a * (intervalDomainLift (u t) y) ^ pExp := by
    intro y hy
    set U : ℝ := u t (⟨y, hy⟩ : intervalDomain.Point) with hU
    have hu_pos : 0 < U := by
      rw [hU]
      exact hsol.u_pos' ht0 htT
    have hpow_two : U ^ (pExp - 2) * U * U = U ^ pExp := by
      calc
        U ^ (pExp - 2) * U * U = (U ^ (pExp - 2) * U) * U := by
          ring
        _ = U ^ (pExp - 1) * U := by
          congr 1
          calc
            U ^ (pExp - 2) * U =
                U ^ (pExp - 2) * U ^ (1 : ℝ) := by
                rw [Real.rpow_one]
            _ = U ^ ((pExp - 2) + 1) := by
                rw [Real.rpow_add hu_pos]
            _ = U ^ (pExp - 1) := by
                congr 1
                ring
        _ = U ^ (pExp - 1) * U ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = U ^ ((pExp - 1) + 1) := by
              rw [Real.rpow_add hu_pos]
        _ = U ^ pExp := by
              congr 1
              ring
    have hdrop :
        params.a - params.b * U ^ params.α ≤ params.a := by
      have hbpow : 0 ≤ params.b * U ^ params.α :=
        mul_nonneg params.hb (Real.rpow_nonneg hu_pos.le _)
      linarith
    have hpow_nonneg : 0 ≤ U ^ pExp :=
      Real.rpow_nonneg hu_pos.le _
    set R : ℝ := params.a - params.b * U ^ params.α with hR
    have hlift_eq :
        intervalDomainLift
            (fun x =>
              intervalDomainLpDiffusionTest pExp u t x *
                (u t x * (params.a - params.b * (u t x) ^ params.α))) y =
          U ^ (pExp - 2) * U * (U * R) := by
      simp only [intervalDomainLift, dif_pos hy, intervalDomainLpDiffusionTest]
      rw [← hU, abs_of_pos hu_pos, ← hR]
    calc
      intervalDomainLift
          (fun x =>
            intervalDomainLpDiffusionTest pExp u t x *
              (u t x * (params.a - params.b * (u t x) ^ params.α))) y =
          U ^ (pExp - 2) * U * (U * R) := hlift_eq
      _ = U ^ pExp * R := by
          calc
            U ^ (pExp - 2) * U * (U * R) =
                (U ^ (pExp - 2) * U * U) * R := by
                ring
            _ = U ^ pExp * R := by
                rw [hpow_two]
      _ ≤ U ^ pExp * params.a :=
          mul_le_mul_of_nonneg_left hdrop hpow_nonneg
      _ = params.a * (intervalDomainLift (u t) y) ^ pExp := by
            simp [intervalDomainLift, hy, hU]
            ring
  calc
    intervalDomainLpLogisticIntegral params pExp u t =
        ∫ y in (0 : ℝ)..1,
          intervalDomainLift
            (fun x =>
              intervalDomainLpDiffusionTest pExp u t x *
                (u t x * (params.a - params.b * (u t x) ^ params.α))) y := rfl
    _ ≤ ∫ y in (0 : ℝ)..1,
          params.a * (intervalDomainLift (u t) y) ^ pExp :=
        intervalIntegral.integral_mono_on (by norm_num) hleft hright hpoint
    _ = params.a * intervalDomainLpEnergy pExp u t := by
        rw [intervalIntegral.integral_const_mul]
        rw [intervalDomainLpEnergy_eq_powerEnergy_of_pos
          (q := pExp) (t := t) (u := u)
          (fun x => hsol.u_pos' (x := x) ht0 htT)]
        rfl

theorem intervalDomain_lp_crossControl_of_regularity
    {params : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
      (|params.χ₀| * (pExp - 1)) *
        intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) := by
  classical
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  set lu : ℝ → ℝ := intervalDomainLift (u t) with hlu
  set lv : ℝ → ℝ := intervalDomainLift (v t) with hlv
  set ltest : ℝ → ℝ :=
    intervalDomainLift (intervalDomainLpDiffusionTest pExp u t) with hltest
  set F : ℝ → ℝ := intervalFlux params (u t) (v t) with hFdef
  have hCu : ContDiffOn ℝ 2 lu (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hCv : ContDiffOn ℝ 2 lv (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).2.1
  have htestC2 : ContDiffOn ℝ 2 ltest (Set.Icc (0 : ℝ) 1) := by
    rw [hltest]
    exact intervalDomainLpDiffusionTest_contDiffOn_two_of_regularity
      hsol ht0 htT
  have htestI : ContDiffOn ℝ 2 ltest (Set.Ioo (0 : ℝ) 1) :=
    htestC2.mono Set.Ioo_subset_Icc_self
  have htest_cont : ContinuousOn ltest (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact htestC2.continuousOn
  have hF_cont : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (flux_contDiffOn_Icc hsol ht).continuousOn
  have htest_deriv_has :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt ltest (deriv ltest x) x := by
    intro x hx
    exact ((htestI.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hFderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (deriv F x) x := by
    intro x hx
    exact (((flux_contDiffOn_Ioo_of_solution hsol ht).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have htest1_int : IntervalIntegrable (deriv ltest) volume 0 1 :=
    intervalIntegrable_deriv_of_contDiffOn_two htestC2
  have hdF_int : IntervalIntegrable (deriv F) volume 0 1 :=
    solution_deriv_flux_intervalIntegrable hsol ht
  obtain ⟨hbc0, hbc1⟩ := flux_endpoint_zero hsol ht
  have hIBP : (∫ y in (0 : ℝ)..1, ltest y * deriv F y)
      = - ∫ y in (0 : ℝ)..1, deriv ltest y * F y :=
    intervalFluxByParts_open htest_cont hF_cont htest_deriv_has hFderiv
      htest1_int hdF_int hbc0 hbc1
  have hchem_eq : intervalDomainLpChemotaxisIntegral params pExp u v t
      = ∫ y in (0 : ℝ)..1, ltest y * deriv F y := by
    rw [intervalDomainLpChemotaxisIntegral]
    show intervalDomainIntegral
      (fun x =>
        intervalDomainLpDiffusionTest pExp u t x *
          intervalDomain.chemotaxisDiv params (u t) (v t) x) = _
    rw [intervalDomainIntegral]
    refine intervalIntegral.integral_congr ?_
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    rw [intervalDomainLift_mul]
    have hchem : intervalDomainLift
        (intervalDomain.chemotaxisDiv params (u t) (v t)) y = deriv F y := by
      simp only [intervalDomainLift, hy, dif_pos]
      rw [hFdef]
      rfl
    rw [hchem]
  set rhsCross : ℝ → ℝ := fun y =>
    lu y ^ (pExp - 1) * |deriv lu y| * |deriv lv y| /
      (1 + lv y) ^ params.β with hrhsCross
  set rhsCont : ℝ → ℝ := fun y =>
    lu y ^ (pExp - 1) *
      |derivWithin lu (Set.Icc (0 : ℝ) 1) y| *
        |derivWithin lv (Set.Icc (0 : ℝ) 1) y| /
      (1 + lv y) ^ params.β with hrhsCont
  have hlu_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < lu x := by
    intro x hx
    have hpos : 0 < u t (⟨x, hx⟩ : intervalDomain.Point) :=
      hsol.u_pos' ht0 htT
    simpa [hlu, intervalDomainLift, hx] using hpos
  have hvnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lv x :=
    solution_lift_v_nonneg_Icc hsol ht
  have hbase_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + lv x := by
    intro x hx
    have := hvnn x hx
    linarith
  have hrhsCont_cont : ContinuousOn rhsCont (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hlu_pow_c : ContinuousOn (fun y => lu y ^ (pExp - 1))
        (Set.Icc (0 : ℝ) 1) :=
      hCu.continuousOn.rpow_const
        (fun y hy => Or.inl (ne_of_gt (hlu_pos y hy)))
    have hdwu_c :
        ContinuousOn (fun y => |derivWithin lu (Set.Icc (0 : ℝ) 1) y|)
          (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_derivWithin_of_contDiffOn_two hCu).abs
    have hdwv_c :
        ContinuousOn (fun y => |derivWithin lv (Set.Icc (0 : ℝ) 1) y|)
          (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_derivWithin_of_contDiffOn_two hCv).abs
    have hnum_c : ContinuousOn
        (fun y =>
          lu y ^ (pExp - 1) *
            |derivWithin lu (Set.Icc (0 : ℝ) 1) y| *
              |derivWithin lv (Set.Icc (0 : ℝ) 1) y|)
        (Set.Icc (0 : ℝ) 1) :=
      (hlu_pow_c.mul hdwu_c).mul hdwv_c
    have hden_c : ContinuousOn
        (fun y => (1 + lv y) ^ params.β) (Set.Icc (0 : ℝ) 1) := by
      apply ContinuousOn.rpow_const (contDiffOn_const.add hCv).continuousOn
      intro x hx
      exact Or.inl (ne_of_gt (hbase_pos x hx))
    have hden_ne :
        ∀ x ∈ Set.Icc (0 : ℝ) 1, (1 + lv x) ^ params.β ≠ 0 :=
      fun x hx => ne_of_gt (Real.rpow_pos_of_pos (hbase_pos x hx) _)
    exact hnum_c.div hden_c hden_ne
  have hrhsCross_int : IntervalIntegrable rhsCross volume 0 1 := by
    have hcontII : IntervalIntegrable rhsCont volume 0 1 :=
      hrhsCont_cont.intervalIntegrable
    refine hcontII.congr_ae ?_
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by
      simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    push_neg at hy
    obtain ⟨hyIoc, hne⟩ := hy
    simp only [Set.mem_singleton_iff]
    by_contra hy1
    have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
    apply hne
    have hdu_eq : derivWithin lu (Set.Icc (0 : ℝ) 1) y = deriv lu y :=
      (deriv_eq_derivWithin_interior hyIoo).symm
    have hdv_eq : derivWithin lv (Set.Icc (0 : ℝ) 1) y = deriv lv y :=
      (deriv_eq_derivWithin_interior hyIoo).symm
    simp only [hrhsCont, hrhsCross, hdu_eq, hdv_eq]
  have hlhs_int : IntervalIntegrable
      (fun y => params.χ₀ * (deriv ltest y * F y)) volume 0 1 :=
    (htest1_int.mul_continuousOn hF_cont).const_mul params.χ₀
  have hrhs_int : IntervalIntegrable
      (fun y => (|params.χ₀| * (pExp - 1)) * rhsCross y) volume 0 1 :=
    hrhsCross_int.const_mul _
  have hptw : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      params.χ₀ * (deriv ltest y * F y) ≤
        (|params.χ₀| * (pExp - 1)) * rhsCross y := by
    intro y hy
    have hluy_pos : 0 < lu y := hlu_pos y hy
    have hDpos : 0 < (1 + lv y) ^ params.β :=
      Real.rpow_pos_of_pos (hbase_pos y hy) _
    have hp_nonneg : 0 ≤ pExp - 1 := by
      linarith
    have hpow_nonneg : 0 ≤ lu y ^ (pExp - 2) :=
      Real.rpow_nonneg hluy_pos.le _
    set c : ℝ :=
      ((pExp - 1) * lu y ^ (pExp - 2) * lu y) /
        (1 + lv y) ^ params.β with hcdef
    have hc : 0 ≤ c := by
      rw [hcdef]
      exact div_nonneg
        (mul_nonneg (mul_nonneg hp_nonneg hpow_nonneg) hluy_pos.le)
        hDpos.le
    have hpow_lu : lu y ^ (pExp - 2) * lu y = lu y ^ (pExp - 1) := by
      calc
        lu y ^ (pExp - 2) * lu y =
            lu y ^ (pExp - 2) * lu y ^ (1 : ℝ) := by
            rw [Real.rpow_one]
        _ = lu y ^ ((pExp - 2) + 1) := by
            rw [Real.rpow_add hluy_pos]
        _ = lu y ^ (pExp - 1) := by
            congr 1
            ring
    have hcoef_eq :
        (pExp - 1) * lu y ^ (pExp - 2) * lu y =
          (pExp - 1) * lu y ^ (pExp - 1) := by
      calc
        (pExp - 1) * lu y ^ (pExp - 2) * lu y =
            (pExp - 1) * (lu y ^ (pExp - 2) * lu y) := by
            ring
        _ = (pExp - 1) * lu y ^ (pExp - 1) := by
            rw [hpow_lu]
    have htest_deriv :
        deriv ltest y =
          (pExp - 1) * lu y ^ (pExp - 2) * deriv lu y := by
      rw [hltest, hlu]
      exact intervalDomain_lp_diffusion_test_deriv_eq
        (pExp := pExp) hsol ht0 htT hy
    have habs : params.χ₀ * deriv lu y * deriv lv y
        ≤ |params.χ₀| * |deriv lu y| * |deriv lv y| := by
      have h := le_abs_self (params.χ₀ * deriv lu y * deriv lv y)
      rwa [abs_mul, abs_mul] at h
    have hL : params.χ₀ * (deriv ltest y * F y)
        = c * (params.χ₀ * deriv lu y * deriv lv y) := by
      rw [htest_deriv, hFdef]
      simp only [intervalFlux]
      rw [hcdef]
      ring
    have hR : (|params.χ₀| * (pExp - 1)) * rhsCross y
        = c * (|params.χ₀| * |deriv lu y| * |deriv lv y|) := by
      rw [hcdef]
      simp only [hrhsCross]
      rw [hcoef_eq]
      ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left habs hc
  calc
    -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t
        = ∫ y in (0 : ℝ)..1,
            params.χ₀ * (deriv ltest y * F y) := by
          rw [hchem_eq, hIBP, intervalIntegral.integral_const_mul]
          ring
    _ ≤ ∫ y in (0 : ℝ)..1,
          (|params.χ₀| * (pExp - 1)) * rhsCross y :=
        intervalIntegral.integral_mono_on (by norm_num) hlhs_int hrhs_int hptw
    _ =
        (|params.χ₀| * (pExp - 1)) *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1

theorem intervalDomain_lp_energy_hCrossControl_of_regularity
    {params : CM2Params} {T pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : 1 < pExp)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ t, 0 < t → t < T →
      -params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t ≤
        (|params.χ₀| * (pExp - 1)) *
          intervalDomain.crossDiffusionEnergyTerm params pExp (u t) (v t) := by
  intro t ht0 htT
  exact intervalDomain_lp_crossControl_of_regularity hpExp hsol ht0 htT

theorem intervalDomain_lp_energy_hDiffusionCoercive_of_regularity
    {params : CM2Params} {T pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    ∀ t, 0 < t → t < T →
      (pExp - 1) * intervalDomainLpWeightedGradientDissipation pExp u t ≤
        intervalDomainLpDiffusionDissipation pExp u t := by
  intro t ht0 htT
  rw [intervalDomain_lp_diffusion_dissipation_eq_weighted_gradient
    (pExp := pExp) hsol ht0 htT]

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
