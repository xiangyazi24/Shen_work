import ShenWork.Paper2.IntervalDomainMFlux

/-!
# Weighted Lp identity for the paper-faithful interval equation

For a positive classical solution of the `u^m`-flux system this file proves
the exact tested identity used in Sections 4.2 and 4.3 of the source paper.
-/

open ShenWork.IntervalDomain MeasureTheory Set
open scoped Topology

namespace ShenWork.Paper2.IntervalDomainM

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalFullKernelRegularity

/-- Chemotaxis term before moving the divergence off the flux. -/
def lpChemotaxisIntegralM
    (p : CM2Params) (pExp : ℝ)
    (u v : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral
    (fun x => intervalDomainLpDiffusionTest pExp u t x *
      intervalDomainChemotaxisDivM p (u t) (v t) x)

/-- Signed cross term after integration by parts. -/
def lpSignedCrossIntegralM
    (p : CM2Params) (pExp : ℝ)
    (u v : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    (intervalDomainLift (u t) y) ^ (pExp + p.m - 2) *
      deriv (intervalDomainLift (u t)) y *
      deriv (intervalDomainLift (v t)) y /
        (1 + intervalDomainLift (v t) y) ^ p.β

theorem diffusionTest_lift_eq_on_Icc
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    Set.EqOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (fun y => (intervalDomainLift (u t) y) ^ (pExp - 2) *
        intervalDomainLift (u t) y)
      (Set.Icc (0 : ℝ) 1) := by
  intro y hy
  have hpos : 0 < u t (⟨y, hy⟩ : intervalDomain.Point) :=
    u_pos hsol ht0 htT ⟨y, hy⟩
  simp [intervalDomainLift, intervalDomainLpDiffusionTest, hy, abs_of_pos hpos]

theorem diffusionTest_contDiffOn_two
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContDiffOn ℝ 2
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.Icc (0 : ℝ) 1) := by
  have hCu : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc 0 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hne : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≠ 0 :=
    fun y hy => ne_of_gt (lift_u_pos_Icc hsol ht0 htT y hy)
  have hpow : ContDiffOn ℝ 2
      (fun y => (intervalDomainLift (u t) y) ^ (pExp - 2)) (Set.Icc 0 1) :=
    hCu.rpow_const_of_ne hne
  exact (hpow.mul hCu).congr (diffusionTest_lift_eq_on_Icc hsol ht0 htT)

theorem lift_lp_diffusion_intervalIntegrable
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift (fun x =>
        intervalDomainLpDiffusionTest pExp u t x *
          intervalDomain.laplacian (u t) x)) volume 0 1 := by
  have hCu : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc 0 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have htest : ContinuousOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (diffusionTest_contDiffOn_two hsol ht0 htT).continuousOn
  have hlap := intervalDomainLift_laplacian_intervalIntegrable_of_contDiffOn hCu
  rw [show intervalDomainLift (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        intervalDomain.laplacian (u t) x) =
      fun y => intervalDomainLift (intervalDomainLpDiffusionTest pExp u t) y *
        intervalDomainLift (fun x => intervalDomain.laplacian (u t) x) y by
    funext y
    exact intervalDomainLift_mul _ _ y]
  exact hlap.continuousOn_mul htest

theorem lift_chemDivM_intervalIntegrable
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift (intervalDomainChemotaxisDivM p (u t) (v t)))
      volume 0 1 := by
  have hderiv := deriv_fluxM_intervalIntegrable hsol ht0 htT
  refine hderiv.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  exact Filter.Eventually.of_forall fun y hy => by
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, hy.2⟩
    simp only [intervalDomainLift, hyIcc, dif_pos]
    rfl

theorem lift_lp_chemotaxisM_intervalIntegrable
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift (fun x =>
        intervalDomainLpDiffusionTest pExp u t x *
          intervalDomainChemotaxisDivM p (u t) (v t) x)) volume 0 1 := by
  have htest : ContinuousOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (diffusionTest_contDiffOn_two hsol ht0 htT).continuousOn
  have hchem := lift_chemDivM_intervalIntegrable hsol ht0 htT
  rw [show intervalDomainLift (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        intervalDomainChemotaxisDivM p (u t) (v t) x) =
      fun y => intervalDomainLift (intervalDomainLpDiffusionTest pExp u t) y *
        intervalDomainLift (intervalDomainChemotaxisDivM p (u t) (v t)) y by
    funext y
    exact intervalDomainLift_mul _ _ y]
  exact hchem.continuousOn_mul htest

theorem lift_reaction_continuousOn
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContinuousOn
      (intervalDomainLift (fun x =>
        u t x * (p.a - p.b * (u t x) ^ p.α)))
      (Set.uIcc (0 : ℝ) 1) := by
  rw [Set.uIcc_of_le zero_le_one]
  have hCu : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc 0 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hne : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≠ 0 :=
    fun y hy => ne_of_gt (lift_u_pos_Icc hsol ht0 htT y hy)
  have hpow := hCu.continuousOn.rpow_const
    (p := p.α) (fun y hy => Or.inl (hne y hy))
  have hca : ContinuousOn (fun _ : ℝ => p.a) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const
  have hcb : ContinuousOn (fun _ : ℝ => p.b) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const
  have hcomp : ContinuousOn
      (fun y => intervalDomainLift (u t) y *
        (p.a - p.b * (intervalDomainLift (u t) y) ^ p.α))
      (Set.Icc (0 : ℝ) 1) :=
    hCu.continuousOn.mul (hca.sub (hcb.mul hpow))
  refine hcomp.congr ?_
  intro y hy
  simp [intervalDomainLift, hy]

theorem lift_lp_logistic_intervalIntegrable
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift (fun x =>
        intervalDomainLpDiffusionTest pExp u t x *
          (u t x * (p.a - p.b * (u t x) ^ p.α)))) volume 0 1 := by
  have htest : ContinuousOn
      (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (diffusionTest_contDiffOn_two hsol ht0 htT).continuousOn
  have hreact : IntervalIntegrable
      (intervalDomainLift (fun x =>
        u t x * (p.a - p.b * (u t x) ^ p.α))) volume 0 1 :=
    (lift_reaction_continuousOn hsol ht0 htT).intervalIntegrable
  rw [show intervalDomainLift (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        (u t x * (p.a - p.b * (u t x) ^ p.α))) =
      fun y => intervalDomainLift (intervalDomainLpDiffusionTest pExp u t) y *
        intervalDomainLift (fun x =>
          u t x * (p.a - p.b * (u t x) ^ p.α)) y by
    funext y
    exact intervalDomainLift_mul _ _ y]
  exact hreact.continuousOn_mul htest

theorem pdeIntegral
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
      intervalDomainLpDiffusionIntegral pExp u t -
        p.χ₀ * lpChemotaxisIntegralM p pExp u v t +
          intervalDomainLpLogisticIntegral p pExp u t := by
  classical
  have hA := lift_lp_diffusion_intervalIntegrable (pExp := pExp) hsol ht0 htT
  have hB := lift_lp_chemotaxisM_intervalIntegrable (pExp := pExp) hsol ht0 htT
  have hC := lift_lp_logistic_intervalIntegrable (pExp := pExp) hsol ht0 htT
  have hAB := hA.sub (hB.const_mul p.χ₀)
  let A : ℝ → ℝ := intervalDomainLift (fun x =>
    intervalDomainLpDiffusionTest pExp u t x * intervalDomain.laplacian (u t) x)
  let B : ℝ → ℝ := intervalDomainLift (fun x =>
    intervalDomainLpDiffusionTest pExp u t x *
      intervalDomainChemotaxisDivM p (u t) (v t) x)
  let C : ℝ → ℝ := intervalDomainLift (fun x =>
    intervalDomainLpDiffusionTest pExp u t x *
      (u t x * (p.a - p.b * (u t x) ^ p.α)))
  have hcomb : (∫ y in (0 : ℝ)..1, A y - p.χ₀ * B y + C y) =
      (∫ y in (0 : ℝ)..1, A y) - p.χ₀ * (∫ y in (0 : ℝ)..1, B y) +
        ∫ y in (0 : ℝ)..1, C y := by
    rw [intervalIntegral.integral_add hAB hC,
      intervalIntegral.integral_sub hA (hB.const_mul p.χ₀),
      intervalIntegral.integral_const_mul]
  unfold intervalDomainLpDiffusionIntegral lpChemotaxisIntegralM
    intervalDomainLpLogisticIntegral
  change (∫ y in (0 : ℝ)..1,
      intervalDomainLift (intervalDomainLpEnergyWeightedTimeTerm pExp u t) y) =
    (∫ y in (0 : ℝ)..1, A y) - p.χ₀ * (∫ y in (0 : ℝ)..1, B y) +
      ∫ y in (0 : ℝ)..1, C y
  rw [← hcomb]
  refine intervalIntegral.integral_congr_ae ?_
  have hne1 : ∀ᵐ y ∂volume, y ≠ (1 : ℝ) := by
    rw [ae_iff]
    simpa using Real.volume_singleton
  filter_upwards [hne1] with y hyne hy
  rw [Set.uIoc_of_le zero_le_one] at hy
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hy.1, lt_of_le_of_ne hy.2 hyne⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
  have hx : (⟨y, hyIcc⟩ : intervalDomain.Point) ∈ intervalDomainM.inside := hyIoo
  have hpde := hsol.2.2.2.2.1 t ⟨y, hyIcc⟩ ht0 htT hx
  have hpde' : intervalDomain.timeDeriv u t ⟨y, hyIcc⟩ =
      intervalDomain.laplacian (u t) ⟨y, hyIcc⟩ -
        p.χ₀ * intervalDomainChemotaxisDivM p (u t) (v t) ⟨y, hyIcc⟩ +
          u t ⟨y, hyIcc⟩ *
            (p.a - p.b * (u t ⟨y, hyIcc⟩) ^ p.α) := hpde
  have hlift : ∀ f : intervalDomain.Point → ℝ,
      intervalDomainLift f y = f ⟨y, hyIcc⟩ := by
    intro f
    simp [intervalDomainLift, hyIcc]
  simp only [hlift]
  unfold intervalDomainLpEnergyWeightedTimeTerm
  rw [hpde']
  have hupos : 0 < u t ⟨y, hyIcc⟩ := u_pos hsol ht0 htT ⟨y, hyIcc⟩
  simp [A, B, C, intervalDomainLift, intervalDomainLpDiffusionTest,
    hyIcc, abs_of_pos hupos]
  ring

theorem diffusion_ibp
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpDiffusionIntegral pExp u t =
      intervalDomainNeumannBoundaryTerm
          (intervalDomainLpDiffusionTest pExp u t) (u t) -
        intervalDomainLpDiffusionDissipation pExp u t := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hCu : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc 0 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have htestC2 := diffusionTest_contDiffOn_two (pExp := pExp) hsol ht0 htT
  have hd0 := derivWithin_left_zero hsol ht0 htT u (Or.inl rfl)
  have hd1 := derivWithin_right_zero hsol ht0 htT u (Or.inl rfl)
  have htest_cont := htestC2.continuousOn
  have hu1_cont := deriv_intervalDomainLift_continuousOn_Icc_of_regularity
    hCu hd0 hd1
  have htest_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (intervalDomainLift (intervalDomainLpDiffusionTest pExp u t))
        (deriv (intervalDomainLift
          (intervalDomainLpDiffusionTest pExp u t)) x) (Set.Ioi x) x :=
    fun x hx => (hasDerivAt_of_contDiffOn_two_interior htestC2 hx).hasDerivWithinAt
  have hu_deriv2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (deriv (intervalDomainLift (u t)))
        (deriv (deriv (intervalDomainLift (u t))) x) (Set.Ioi x) x :=
    fun x hx =>
      (hasDerivAt_deriv_of_contDiffOn_two_interior hCu hx).hasDerivWithinAt
  have htest1_int := intervalIntegrable_deriv_of_contDiffOn_two htestC2
  have hu2_int := intervalIntegrable_deriv_deriv_of_contDiffOn_two hCu
  have hbdryR : deriv (intervalDomainLift (u t)) 1 =
      intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint := by
    rw [deriv_intervalDomainLift_eq_zero_at_one]
    exact (hsol.2.2.2.2.2.2 t intervalDomainRightEndpoint ht0 htT
      rightEndpoint_mem_boundaryM).1.symm
  have hbdryL : deriv (intervalDomainLift (u t)) 0 =
      intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint := by
    rw [deriv_intervalDomainLift_eq_zero_at_zero]
    exact (hsol.2.2.2.2.2.2 t intervalDomainLeftEndpoint ht0 htT
      leftEndpoint_mem_boundaryM).1.symm
  exact intervalDomain_spatial_integrationByParts_identity
    (intervalDomainLpDiffusionTest pExp u t) (u t)
    htest_cont hu1_cont htest_deriv hu_deriv2 htest1_int hu2_int hbdryR hbdryL

theorem diffusion_test_deriv_eq
    {p : CM2Params} {T t pExp y : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
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
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hy.1 (fun h => hy0 h.symm), lt_of_le_of_ne hy.2 hy1⟩
  have hu_has : HasDerivAt (intervalDomainLift (u t))
      (deriv (intervalDomainLift (u t)) y) y :=
    hasDerivAt_of_contDiffOn_two_interior hclosed.1 hyIoo
  have hu_pos : 0 < intervalDomainLift (u t) y :=
    lift_u_pos_Icc hsol ht0 htT y (Set.Ioo_subset_Icc_self hyIoo)
  have hpow0 := hu_has.rpow_const (p := pExp - 1)
    (Or.inl (ne_of_gt hu_pos))
  have hpow : HasDerivAt
      (fun z => (intervalDomainLift (u t) z) ^ (pExp - 1))
      (deriv (intervalDomainLift (u t)) y * (pExp - 1) *
        (intervalDomainLift (u t) y) ^ (pExp - 2)) y := by
    refine hpow0.congr_deriv ?_
    ring
  have heq : intervalDomainLift (intervalDomainLpDiffusionTest pExp u t)
      =ᶠ[𝓝 y] fun z => (intervalDomainLift (u t) z) ^ (pExp - 1) := by
    filter_upwards [Ioo_mem_nhds hyIoo.1 hyIoo.2] with z hz
    have hzIcc := Set.Ioo_subset_Icc_self hz
    have hpos : 0 < u t (⟨z, hzIcc⟩ : intervalDomain.Point) :=
      u_pos hsol ht0 htT ⟨z, hzIcc⟩
    simp only [intervalDomainLift, hzIcc, dif_pos, intervalDomainLpDiffusionTest,
      abs_of_pos hpos]
    rw [show pExp - 1 = (pExp - 2) + 1 by ring,
      Real.rpow_add hpos, Real.rpow_one]
  have htest := hpow.congr_of_eventuallyEq heq
  rw [htest.deriv]
  ring

theorem diffusion_dissipation_eq
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpDiffusionDissipation pExp u t =
      (pExp - 1) * intervalDomainLpWeightedGradientDissipation pExp u t := by
  unfold intervalDomainLpDiffusionDissipation intervalDomainDerivativePairIntegral
  unfold intervalDomainLpWeightedGradientDissipation
  change (∫ y in (0 : ℝ)..1, _) = (pExp - 1) * intervalDomainIntegral _
  unfold intervalDomainIntegral
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hy
  rw [diffusion_test_deriv_eq (pExp := pExp) hsol ht0 htT hy]
  simp [intervalDomainLift, hy, intervalDomain, intervalDomainGradNorm, sq_abs]
  ring

theorem chemotaxis_ibp
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    -p.χ₀ * lpChemotaxisIntegralM p pExp u v t =
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t := by
  let test : ℝ → ℝ :=
    intervalDomainLift (intervalDomainLpDiffusionTest pExp u t)
  let F : ℝ → ℝ := intervalFluxM p (u t) (v t)
  have htestC2 := diffusionTest_contDiffOn_two (pExp := pExp) hsol ht0 htT
  have htest_cont : ContinuousOn test (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact htestC2.continuousOn
  have hF_cont : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact (fluxM_contDiffOn_Icc hsol ht0 htT).continuousOn
  have htest_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt test (deriv test x) x := by
    intro x hx
    exact ((htestC2.mono Set.Ioo_subset_Icc_self).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
  have hF_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F (deriv F x) x := by
    intro x hx
    exact ((fluxM_contDiffOn_Ioo hsol ht0 htT).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
  have htest_int := intervalIntegrable_deriv_of_contDiffOn_two htestC2
  have hF_int := deriv_fluxM_intervalIntegrable hsol ht0 htT
  obtain ⟨hF0, hF1⟩ := fluxM_endpoint_zero hsol ht0 htT
  have hibp : (∫ y in (0 : ℝ)..1, test y * deriv F y) =
      -∫ y in (0 : ℝ)..1, deriv test y * F y :=
    intervalFluxByParts_open htest_cont hF_cont htest_deriv hF_deriv
      htest_int hF_int hF0 hF1
  have hchem : lpChemotaxisIntegralM p pExp u v t =
      ∫ y in (0 : ℝ)..1, test y * deriv F y := by
    unfold lpChemotaxisIntegralM
    change intervalDomainIntegral _ = _
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr ?_
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    simp only [intervalDomainLift_mul]
    have hdiv : intervalDomainLift
        (intervalDomainChemotaxisDivM p (u t) (v t)) y = deriv F y := by
      simp only [intervalDomainLift, hy, dif_pos]
      change deriv (fun z =>
        (intervalDomainLift (u t) z) ^ p.m * deriv (intervalDomainLift (v t)) z /
          (1 + intervalDomainLift (v t) z) ^ p.β) y = deriv F y
      rfl
    calc
      intervalDomainLift (fun x => intervalDomainLpDiffusionTest pExp u t x *
          intervalDomainChemotaxisDivM p (u t) (v t) x) y =
        intervalDomainLift (intervalDomainLpDiffusionTest pExp u t) y *
          intervalDomainLift (intervalDomainChemotaxisDivM p (u t) (v t)) y :=
        intervalDomainLift_mul _ _ y
      _ = test y * deriv F y := by rw [hdiv]
  have hcross : (∫ y in (0 : ℝ)..1, deriv test y * F y) =
      (pExp - 1) * lpSignedCrossIntegralM p pExp u v t := by
    unfold lpSignedCrossIntegralM
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hy
    rw [show deriv test y =
        (pExp - 1) * (intervalDomainLift (u t) y) ^ (pExp - 2) *
          deriv (intervalDomainLift (u t)) y by
      dsimp [test]
      exact diffusion_test_deriv_eq (pExp := pExp) hsol ht0 htT hy]
    have hu := lift_u_pos_Icc hsol ht0 htT y hy
    have hpowers : (intervalDomainLift (u t) y) ^ (pExp - 2) *
        (intervalDomainLift (u t) y) ^ p.m =
          (intervalDomainLift (u t) y) ^ (pExp + p.m - 2) := by
      rw [← Real.rpow_add hu]
      congr 1
      ring
    dsimp [F, intervalFluxM]
    calc
      (pExp - 1) * (intervalDomainLift (u t) y) ^ (pExp - 2) *
          deriv (intervalDomainLift (u t)) y *
          ((intervalDomainLift (u t) y) ^ p.m *
            deriv (intervalDomainLift (v t)) y /
              (1 + intervalDomainLift (v t) y) ^ p.β) =
        (pExp - 1) *
          ((intervalDomainLift (u t) y) ^ (pExp - 2) *
            (intervalDomainLift (u t) y) ^ p.m) *
          deriv (intervalDomainLift (u t)) y *
          deriv (intervalDomainLift (v t)) y /
            (1 + intervalDomainLift (v t) y) ^ p.β := by ring
      _ = (pExp - 1) *
          ((intervalDomainLift (u t) y) ^ (pExp + p.m - 2) *
            deriv (intervalDomainLift (u t)) y *
            deriv (intervalDomainLift (v t)) y /
              (1 + intervalDomainLift (v t) y) ^ p.β) := by
        rw [hpowers]
        ring
  rw [hchem, hibp, hcross]
  ring

theorem logistic_exact
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpLogisticIntegral p pExp u t =
      p.a * intervalDomain.integral (fun x => (u t x) ^ pExp) -
        p.b * intervalDomain.integral (fun x => (u t x) ^ (pExp + p.α)) := by
  have hleft := lift_lp_logistic_intervalIntegrable (pExp := pExp) hsol ht0 htT
  have hpowp : IntervalIntegrable
      (fun y => (intervalDomainLift (u t) y) ^ pExp) volume 0 1 :=
    by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1.continuousOn.rpow_const
        (p := pExp)
        (fun y hy => Or.inl (ne_of_gt (lift_u_pos_Icc hsol ht0 htT y hy)))
  have hpowhigh : IntervalIntegrable
      (fun y => (intervalDomainLift (u t) y) ^ (pExp + p.α)) volume 0 1 :=
    by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1.continuousOn.rpow_const
        (p := pExp + p.α)
        (fun y hy => Or.inl (ne_of_gt (lift_u_pos_Icc hsol ht0 htT y hy)))
  have hpLift :
      (∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x => (u t x) ^ pExp) y) =
      ∫ y in (0 : ℝ)..1, (intervalDomainLift (u t) y) ^ pExp := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hy
    simp [intervalDomainLift, hy]
  have hhighLift :
      (∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x => (u t x) ^ (pExp + p.α)) y) =
      ∫ y in (0 : ℝ)..1, (intervalDomainLift (u t) y) ^ (pExp + p.α) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hy
    simp [intervalDomainLift, hy]
  unfold intervalDomainLpLogisticIntegral
  change (∫ y in (0 : ℝ)..1, intervalDomainLift (fun x =>
      intervalDomainLpDiffusionTest pExp u t x *
        (u t x * (p.a - p.b * (u t x) ^ p.α))) y) =
    p.a * (∫ y in (0 : ℝ)..1,
      intervalDomainLift (fun x => (u t x) ^ pExp) y) -
      p.b * (∫ y in (0 : ℝ)..1,
        intervalDomainLift (fun x => (u t x) ^ (pExp + p.α)) y)
  rw [hpLift, hhighLift]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hpowp.const_mul p.a)
      (hpowhigh.const_mul p.b)]
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp only [intervalDomainLift, hy, dif_pos, intervalDomainLpDiffusionTest,
    abs_of_pos (u_pos hsol ht0 htT ⟨y, hy⟩)]
  have halg (U : ℝ) (hUpos : 0 < U) :
      U ^ (pExp - 2) * U * (U * (p.a - p.b * U ^ p.α)) =
        p.a * U ^ pExp - p.b * U ^ (pExp + p.α) := by
    have hmul1 : U ^ (pExp - 2) * U = U ^ (pExp - 1) := by
      calc
        U ^ (pExp - 2) * U = U ^ (pExp - 2) * U ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = U ^ ((pExp - 2) + 1) := by rw [Real.rpow_add hUpos]
        _ = U ^ (pExp - 1) := by congr 1 <;> ring
    have h1 : U ^ (pExp - 2) * U * U = U ^ pExp := by
      calc
        U ^ (pExp - 2) * U * U = U ^ (pExp - 1) * U := by rw [hmul1]
        _ = U ^ (pExp - 1) * U ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = U ^ ((pExp - 1) + 1) := by rw [Real.rpow_add hUpos]
        _ = U ^ pExp := by congr 1 <;> ring
    have h2 : U ^ pExp * U ^ p.α = U ^ (pExp + p.α) := by
      rw [← Real.rpow_add hUpos]
    rw [show U ^ (pExp - 2) * U * (U * (p.a - p.b * U ^ p.α)) =
        (U ^ (pExp - 2) * U * U) * (p.a - p.b * U ^ p.α) by ring,
      h1]
    calc
      U ^ pExp * (p.a - p.b * U ^ p.α) =
          p.a * U ^ pExp - p.b * (U ^ pExp * U ^ p.α) := by ring
      _ = p.a * U ^ pExp - p.b * U ^ (pExp + p.α) := by rw [h2]
  exact halg _ (u_pos hsol ht0 htT _)

/-- Exact weighted Lp identity for the published general-`m` equation. -/
theorem weightedLpEnergy_identity
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hpExp : pExp ≠ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        (pExp - 1) * intervalDomainLpWeightedGradientDissipation pExp u t +
        p.b * intervalDomain.integral (fun x => (u t x) ^ (pExp + p.α)) =
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t +
        p.a * intervalDomain.integral (fun x => (u t x) ^ pExp) := by
  have htime := lp_energy_hLpTime (q := pExp) hsol ht0 htT
  have hpde := pdeIntegral (pExp := pExp) hsol ht0 htT
  have hibp := diffusion_ibp (pExp := pExp) hsol ht0 htT
  have hdiff := diffusion_dissipation_eq (pExp := pExp) hsol ht0 htT
  have hchem := chemotaxis_ibp (pExp := pExp) hsol ht0 htT
  have hlog := logistic_exact (pExp := pExp) hsol ht0 htT
  have hNeuR : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint = 0 :=
    (hsol.2.2.2.2.2.2 t intervalDomainRightEndpoint ht0 htT
      rightEndpoint_mem_boundaryM).1
  have hNeuL : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint = 0 :=
    (hsol.2.2.2.2.2.2 t intervalDomainLeftEndpoint ht0 htT
      leftEndpoint_mem_boundaryM).1
  have hboundary : intervalDomainNeumannBoundaryTerm
      (intervalDomainLpDiffusionTest pExp u t) (u t) = 0 :=
    intervalDomain_neumannBoundaryTerm_eq_zero _ _ hNeuR hNeuL
  have hscaled : (1 / pExp) *
      deriv (fun τ => intervalDomainLpEnergy pExp u τ) t =
        intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm pExp u t) := by
    rw [htime]
    field_simp [hpExp]
  rw [hscaled, hpde, hibp, hboundary, zero_sub, hdiff, hlog]
  calc
    -((pExp - 1) * intervalDomainLpWeightedGradientDissipation pExp u t) -
          p.χ₀ * lpChemotaxisIntegralM p pExp u v t +
          (p.a * intervalDomain.integral (fun x => (u t x) ^ pExp) -
            p.b * intervalDomain.integral (fun x => (u t x) ^ (pExp + p.α))) +
          (pExp - 1) * intervalDomainLpWeightedGradientDissipation pExp u t +
          p.b * intervalDomain.integral (fun x => (u t x) ^ (pExp + p.α)) =
        -p.χ₀ * lpChemotaxisIntegralM p pExp u v t +
          p.a * intervalDomain.integral (fun x => (u t x) ^ pExp) := by ring
    _ = p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t +
          p.a * intervalDomain.integral (fun x => (u t x) ^ pExp) := by
      rw [hchem]

end

end ShenWork.Paper2.IntervalDomainM
