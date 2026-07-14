import ShenWork.PDE.IntervalAgmonInterpolation
import ShenWork.Paper2.IntervalDomainH1GradientBound
import ShenWork.Paper2.IntervalDomainMass
import ShenWork.Paper3.IntervalDomainIntegratedMoserAssembly

set_option linter.style.longLine false

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Interval

namespace ShenWork.IntervalDomainExistence.P3MoserRelativeMassGradientProducer

noncomputable section

private theorem p0_gt_one_of_bootstrap
    {params : CM2Params} {T rho p0 : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    1 < p0 := by
  have hthreshold := AbstractLpBootstrapHypothesis.p0_gt_threshold hboot
  have hone_le :
      (1 : ℝ) ≤ max 1 (rho * (params.N : ℝ) / 2) :=
    le_max_left _ _
  linarith

private theorem pExp_pos_of_bootstrap
    {params : CM2Params} {T rho p0 pExp : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hpExp : p0 ≤ pExp) :
    0 < pExp := by
  have hp0 : 1 < p0 := p0_gt_one_of_bootstrap hboot
  linarith

private theorem pExp_gt_one_of_bootstrap
    {params : CM2Params} {T rho p0 pExp : ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hpExp : p0 ≤ pExp) :
    1 < pExp := by
  have hp0 : 1 < p0 := p0_gt_one_of_bootstrap hboot
  linarith

private theorem intervalDomain_abs_le_supNorm_of_bddAbove
    {f : intervalDomain.Point → ℝ}
    (hbdd : BddAbove (Set.range fun x : intervalDomain.Point => |f x|))
    (x : intervalDomain.Point) :
    |f x| ≤ intervalDomain.supNorm f := by
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

theorem intervalDomain_weightedGradient_intervalIntegrable_of_regularity
    {params : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift
        (fun x => (u t x) ^ (q - 2) *
          (intervalDomain.gradNorm (u t) x) ^ 2))
      volume 0 1 := by
  have hCu : ContDiffOn ℝ 2
      (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hdw0 :
      derivWithin (intervalDomainLift (u t))
        (Set.Icc (0 : ℝ) 1) 0 = 0 :=
    intervalDomain_solution_derivWithin_u_left_zero hsol ht0 htT
  have hdw1 :
      derivWithin (intervalDomainLift (u t))
        (Set.Icc (0 : ℝ) 1) 1 = 0 :=
    intervalDomain_solution_derivWithin_u_right_zero hsol ht0 htT
  have hdu_cont :
      ContinuousOn (deriv (intervalDomainLift (u t)))
        (Set.Icc (0 : ℝ) 1) :=
    deriv_intervalDomainLift_continuousOn_Icc_of_regularity hCu hdw0 hdw1
  have hne :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u t) y ≠ 0 :=
    fun y hy => ne_of_gt (intervalDomain_solution_lift_u_pos hsol ht0 htT hy)
  have hpow_cont : ContinuousOn
      (fun y => (intervalDomainLift (u t) y) ^ (q - 2))
      (Set.Icc (0 : ℝ) 1) :=
    (hCu.rpow_const_of_ne hne).continuousOn
  have hgrad_sq_cont : ContinuousOn
      (fun y => (deriv (intervalDomainLift (u t)) y) ^ 2)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [pow_two] using hdu_cont.mul hdu_cont
  have hprod_cont : ContinuousOn
      (fun y => (intervalDomainLift (u t) y) ^ (q - 2) *
        (deriv (intervalDomainLift (u t)) y) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    hpow_cont.mul hgrad_sq_cont
  have hlift_cont : ContinuousOn
      (intervalDomainLift
        (fun x => (u t x) ^ (q - 2) *
          (intervalDomain.gradNorm (u t) x) ^ 2))
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    refine hprod_cont.congr ?_
    intro y hy
    simp only [intervalDomainLift, dif_pos hy]
    simp [intervalDomain, intervalDomainGradNorm, sq_abs]
  exact hlift_cont.intervalIntegrable

theorem intervalDomain_mass_rpow_le_integral_rpow_of_classical
    {params : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hq : 1 ≤ q) :
    (intervalDomain.integral (u t)) ^ q ≤
      intervalDomain.integral (fun x => (u t x) ^ q) := by
  let f : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hCu : ContDiffOn ℝ 2
      (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    exact hCu.continuousOn
  have hfpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x := by
    intro x hx
    dsimp [f]
    exact intervalDomain_solution_lift_u_pos hsol ht0 htT hx
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ q) :=
    convexOn_rpow hq
  have hq_nonneg : 0 ≤ q := le_trans zero_le_one hq
  have hcontpow : ContinuousOn (fun x : ℝ => x ^ q) (Set.Ici (0 : ℝ)) :=
    (Real.continuous_rpow_const hq_nonneg).continuousOn
  have hfs : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      f x ∈ Set.Ici (0 : ℝ) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx =>
      (hfpos x ⟨le_of_lt hx.1, hx.2⟩).le
  have hfi_on : IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume :=
    hfcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpowcont_Icc : ContinuousOn (fun x => f x ^ q) (Set.Icc (0 : ℝ) 1) :=
    hfcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hfpos x hx)))
  have hgi_on : IntegrableOn ((fun x : ℝ => x ^ q) ∘ f)
      (Set.Ioc (0 : ℝ) 1) volume := by
    change IntegrableOn (fun x => f x ^ q) (Set.Ioc (0 : ℝ) 1) volume
    exact hpowcont_Icc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hJ := hconv.map_set_average_le (μ := volume) (t := Set.Ioc (0 : ℝ) 1)
    hcontpow isClosed_Ici ?h0 ?htop hfs hfi_on hgi_on
  · have hμ : volume.real (Set.Ioc (0 : ℝ) 1) = 1 := by
      rw [Measure.real, Real.volume_Ioc]
      norm_num
    have hAvg_f :
        (⨍ x in Set.Ioc (0 : ℝ) 1, f x ∂volume) =
          ∫ x in (0 : ℝ)..1, f x := by
      rw [MeasureTheory.setAverage_eq, hμ]
      simp [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    have hAvg_pow :
        (⨍ x in Set.Ioc (0 : ℝ) 1, f x ^ q ∂volume) =
          ∫ x in (0 : ℝ)..1, f x ^ q := by
      rw [MeasureTheory.setAverage_eq, hμ]
      simp [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    rw [hAvg_f, hAvg_pow] at hJ
    have hpow_int_eq :
        (∫ x in (0 : ℝ)..1, f x ^ q) =
          intervalDomainIntegral (fun x => (u t x) ^ q) := by
      unfold intervalDomainIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hx
      simp [f, intervalDomainLift, hxIcc]
    change (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x) ^ q ≤
      intervalDomainIntegral (fun x => (u t x) ^ q)
    rwa [hpow_int_eq] at hJ
  · simp [Real.volume_Ioc]
  · simp [Real.volume_Ioc]

theorem intervalDomain_mass_le_seed_plus_one_of_classical
    {params : CM2Params} {T t p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hp0 : 1 ≤ p0) :
    intervalDomain.integral (u t) ≤
      intervalDomain.integral (fun x => (u t x) ^ p0) + 1 := by
  have hu_int :
      IntervalIntegrable
        (intervalDomainLift (u t)) volume 0 1 := by
    simpa [Real.rpow_one] using
      (intervalDomain_u_rpow_intervalIntegrable_of_regularity
        (params := params) (T := T) (t := t) (q := (1 : ℝ))
        (u := u) (v := v) hsol ht0 htT)
  have hp0_int :
      IntervalIntegrable
        (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0))
        volume 0 1 :=
    intervalDomain_u_rpow_intervalIntegrable_of_regularity
      (params := params) (T := T) (t := t) (q := p0)
      (u := u) (v := v) hsol ht0 htT
  have hright_int :
      IntervalIntegrable
        (fun y : ℝ =>
          intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0) y + 1)
        volume 0 1 :=
    hp0_int.add intervalIntegrable_const
  have hmono :
      (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y) ≤
        ∫ y in (0 : ℝ)..1,
          intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0) y + 1 := by
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hu_int hright_int ?_
    intro y hy
    have hu_nonneg : 0 ≤ u t (⟨y, hy⟩ : intervalDomain.Point) :=
      (hsol.u_pos' ht0 htT).le
    have hle :=
      rpow_le_one_add_rpow_of_nonneg_of_le
        hu_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ)) hp0
    simpa [intervalDomainLift, hy, Real.rpow_one] using hle
  have hadd :
      (∫ y in (0 : ℝ)..1,
          intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0) y + 1) =
        (∫ y in (0 : ℝ)..1,
          intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0) y) + 1 := by
    rw [intervalIntegral.integral_add hp0_int intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  rw [hadd] at hmono
  change (∫ y in (0 : ℝ)..1, intervalDomainLift (u t) y) ≤
    (∫ y in (0 : ℝ)..1,
      intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0) y) + 1
  exact hmono

theorem intervalDomain_massGradientInterpolation_of_classical
    {params : CM2Params}
    {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (_hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    ∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain
        (pExp + rho) eta Ceta T u := by
  intro pExp hpExp eta heta
  have hrho : 0 < rho := AbstractLpBootstrapHypothesis.rho_pos hboot
  have hpExp_gt_one : 1 < pExp :=
    pExp_gt_one_of_bootstrap hboot hpExp
  have hq : 1 < pExp + rho := by linarith
  obtain ⟨Ceta, _hCeta_pos, hest⟩ :=
    unitIntervalPositiveAgmonInterpolation
      (pExp + rho) hq eta heta
  refine ⟨Ceta, ?_⟩
  intro t ht0 htT
  exact hest (u t)
    (fun x => hsol.u_pos' ht0 htT (x := x))
    ((hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1)

theorem intervalDomain_moserMassPowerToCurrentLpLowerOrder_of_classical
    {params : CM2Params}
    {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (_hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0 := by
  obtain ⟨C0, hC0⟩ := AbstractLpBootstrapHypothesis.initial_lp_bound hboot
  have hp0_gt_one : 1 < p0 := p0_gt_one_of_bootstrap hboot
  have hp0_one : 1 ≤ p0 := hp0_gt_one.le
  have hp0_pos : 0 < p0 := lt_trans zero_lt_one hp0_gt_one
  have hrho_pos : 0 < rho := AbstractLpBootstrapHypothesis.rho_pos hboot
  let Mmass : ℝ := max (C0 + 1) 1
  have hMmass_pos : 0 < Mmass := by
    dsimp [Mmass]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMmass_nonneg : 0 ≤ Mmass := hMmass_pos.le
  intro p hp Cmass
  let Crel : ℝ := max Cmass 0 * Mmass ^ rho
  refine ⟨Crel, ?_, ?_⟩
  · dsimp [Crel]
    exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hMmass_nonneg rho)
  · intro t ht0 htT
    have hp_gt_one : 1 < p := by linarith [hp0_gt_one, hp]
    have hp_one : 1 ≤ p := hp_gt_one.le
    have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp_one
    have hrho_nonneg : 0 ≤ rho := hrho_pos.le
    set mass : ℝ := intervalDomain.integral (u t)
    set Ip : ℝ := intervalDomain.integral (fun x => (u t x) ^ p)
    have hmass_nonneg : 0 ≤ mass := by
      dsimp [mass]
      simpa [Real.rpow_one] using
        (intervalDomain_integral_u_rpow_nonneg_of_regularity
          (params := params) (T := T) (t := t) (q := (1 : ℝ))
          (u := u) (v := v) hsol ht0 htT)
    have hIp_nonneg : 0 ≤ Ip := by
      dsimp [Ip]
      exact intervalDomain_integral_u_rpow_nonneg_of_regularity
        (params := params) (T := T) (t := t) (q := p)
        (u := u) (v := v) hsol ht0 htT
    have hmass_p_le : mass ^ p ≤ Ip := by
      dsimp [mass, Ip]
      exact intervalDomain_mass_rpow_le_integral_rpow_of_classical
        (params := params) (T := T) (t := t) (q := p)
        (u := u) (v := v) hsol ht0 htT hp_one
    have hmass_le_seed :
        mass ≤ intervalDomain.integral (fun x => (u t x) ^ p0) + 1 := by
      dsimp [mass]
      exact intervalDomain_mass_le_seed_plus_one_of_classical
        (params := params) (T := T) (t := t) (p0 := p0)
        (u := u) (v := v) hsol ht0 htT hp0_one
    have hseed_le_C0 :
        intervalDomain.integral (fun x => (u t x) ^ p0) ≤ C0 :=
      hC0 t ht0 htT
    have hmass_le_M : mass ≤ Mmass := by
      dsimp [Mmass]
      exact le_trans (le_trans hmass_le_seed (by linarith : _ ≤ C0 + 1))
        (le_max_left _ _)
    have hmass_rho_le : mass ^ rho ≤ Mmass ^ rho :=
      Real.rpow_le_rpow hmass_nonneg hmass_le_M hrho_nonneg
    have hmass_pow_le :
        mass ^ (p + rho) ≤ Mmass ^ rho * Ip := by
      calc
        mass ^ (p + rho) = mass ^ p * mass ^ rho := by
          rw [Real.rpow_add_of_nonneg hmass_nonneg hp_nonneg hrho_nonneg]
        _ ≤ Ip * Mmass ^ rho :=
          mul_le_mul hmass_p_le hmass_rho_le
            (Real.rpow_nonneg hmass_nonneg rho) hIp_nonneg
        _ = Mmass ^ rho * Ip := by ring
    have hpow_nonneg : 0 ≤ mass ^ (p + rho) :=
      Real.rpow_nonneg hmass_nonneg (p + rho)
    have hscaled₁ :
        Cmass * mass ^ (p + rho) ≤
          max Cmass 0 * mass ^ (p + rho) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpow_nonneg
    have hscaled₂ :
        max Cmass 0 * mass ^ (p + rho) ≤
          max Cmass 0 * (Mmass ^ rho * Ip) :=
      mul_le_mul_of_nonneg_left hmass_pow_le (le_max_right _ _)
    calc
      Cmass * (intervalDomain.integral (u t)) ^ (p + rho)
          = Cmass * mass ^ (p + rho) := by rfl
      _ ≤ max Cmass 0 * mass ^ (p + rho) := hscaled₁
      _ ≤ max Cmass 0 * (Mmass ^ rho * Ip) := hscaled₂
      _ = Crel * intervalDomain.integral (fun x => (u t x) ^ p) := by
        dsimp [Crel, Ip]
        ring

theorem intervalDomain_weightedGradient_rho_le_of_boundedBefore
    {params : CM2Params} {T rho : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u)
    (hrho : 0 ≤ rho) :
    ∃ M : ℝ, 0 < M ∧
      ∀ pExp, ∀ t, 0 < t → t < T →
        intervalDomainLpWeightedGradientDissipation (pExp + rho) u t ≤
          M ^ rho * intervalDomainLpWeightedGradientDissipation pExp u t := by
  rcases hbounded with ⟨Mb, hMb⟩
  let M : ℝ := max Mb 1
  have hM_pos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨M, hM_pos, ?_⟩
  intro pExp t ht0 htT
  unfold intervalDomainLpWeightedGradientDissipation
  change intervalDomainIntegral _ ≤ M ^ rho * intervalDomainIntegral _
  unfold intervalDomainIntegral
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    ?_ ?_ ?_
  · exact intervalDomain_weightedGradient_intervalIntegrable_of_regularity
      (params := params) (T := T) (t := t) (q := pExp + rho)
      (u := u) (v := v) hsol ht0 htT
  · exact
      (intervalDomain_weightedGradient_intervalIntegrable_of_regularity
        (params := params) (T := T) (t := t) (q := pExp)
        (u := u) (v := v) hsol ht0 htT).const_mul _
  · intro y hy
    simp only [intervalDomainLift, dif_pos hy]
    have hbdd_slice :
        BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) :=
      intervalDomain_solution_slice_abs_bddAbove hsol ⟨ht0, htT⟩
    have hu_pos : 0 < u t (⟨y, hy⟩ : intervalDomain.Point) :=
      hsol.u_pos' ht0 htT
    have hu_nonneg : 0 ≤ u t (⟨y, hy⟩ : intervalDomain.Point) := hu_pos.le
    have hsup_le_Mb : intervalDomain.supNorm (u t) ≤ Mb :=
      hMb t ht0 htT
    have hpoint_le_M : u t (⟨y, hy⟩ : intervalDomain.Point) ≤ M := by
      have habs_le :
          |u t (⟨y, hy⟩ : intervalDomain.Point)| ≤ intervalDomain.supNorm (u t) :=
        intervalDomain_abs_le_supNorm_of_bddAbove hbdd_slice _
      have hle_Mb : u t (⟨y, hy⟩ : intervalDomain.Point) ≤ Mb :=
        le_trans (le_trans (le_abs_self _) habs_le) hsup_le_Mb
      exact le_trans hle_Mb (le_max_left _ _)
    have hrpow_le :
        (u t (⟨y, hy⟩ : intervalDomain.Point)) ^ rho ≤ M ^ rho :=
      Real.rpow_le_rpow hu_nonneg hpoint_le_M hrho
    have hsplit :
        (u t (⟨y, hy⟩ : intervalDomain.Point)) ^ (pExp + rho - 2) =
          (u t (⟨y, hy⟩ : intervalDomain.Point)) ^ rho *
            (u t (⟨y, hy⟩ : intervalDomain.Point)) ^ (pExp - 2) := by
      have hsum : pExp + rho - 2 = rho + (pExp - 2) := by ring
      rw [hsum, Real.rpow_add hu_pos]
    rw [hsplit]
    calc
      (u t (⟨y, hy⟩ : intervalDomain.Point)) ^ rho *
            (u t (⟨y, hy⟩ : intervalDomain.Point)) ^ (pExp - 2) *
          (intervalDomain.gradNorm (u t) (⟨y, hy⟩ : intervalDomain.Point)) ^ 2
          =
        (u t (⟨y, hy⟩ : intervalDomain.Point)) ^ rho *
          ((u t (⟨y, hy⟩ : intervalDomain.Point)) ^ (pExp - 2) *
            (intervalDomain.gradNorm (u t) (⟨y, hy⟩ : intervalDomain.Point)) ^ 2) := by
            ring
      _ ≤ M ^ rho *
          ((u t (⟨y, hy⟩ : intervalDomain.Point)) ^ (pExp - 2) *
            (intervalDomain.gradNorm (u t) (⟨y, hy⟩ : intervalDomain.Point)) ^ 2) :=
        mul_le_mul_of_nonneg_right hrpow_le
          (mul_nonneg (Real.rpow_nonneg hu_nonneg (pExp - 2)) (sq_nonneg _))

theorem intervalDomain_relativeMassGradient_of_classical_boundedBefore
    {params : CM2Params}
    {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u) :
    ∃ cGrad : ℝ → ℝ,
      (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
      (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
        LpMassGradientInterpolationEstimate intervalDomain
          (pExp + rho) eta Ceta T u) ∧
      (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
        intervalDomain.integral (fun x =>
          (u t x) ^ (pExp + rho - 2) *
            (intervalDomain.gradNorm (u t) x) ^ 2) ≤
        cGrad pExp * intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
      MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0 := by
  have hrho_pos : 0 < rho := AbstractLpBootstrapHypothesis.rho_pos hboot
  obtain ⟨M, hM_pos, hweighted⟩ :=
    intervalDomain_weightedGradient_rho_le_of_boundedBefore
      (params := params) (T := T) (rho := rho)
      (u := u) (v := v) hsol hbounded hrho_pos.le
  let cGrad : ℝ → ℝ := fun pExp => M ^ rho / ((pExp / 2) ^ 2)
  refine ⟨cGrad, ?_, ?_, ?_, ?_⟩
  · intro pExp hpExp
    have hpExp_pos : 0 < pExp :=
      pExp_pos_of_bootstrap hboot hpExp
    have hden_pos : 0 < (pExp / 2) ^ 2 :=
      sq_pos_of_pos (by positivity)
    dsimp [cGrad]
    exact div_pos (Real.rpow_pos_of_pos hM_pos rho) hden_pos
  · exact intervalDomain_massGradientInterpolation_of_classical hsol hcross hboot
  · intro pExp hpExp t ht0 htT
    set Wp : ℝ := intervalDomainLpWeightedGradientDissipation pExp u t
    set Gp : ℝ := intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)
    have hpExp_pos : 0 < pExp :=
      pExp_pos_of_bootstrap hboot hpExp
    have hden_pos : 0 < (pExp / 2) ^ 2 :=
      sq_pos_of_pos (by positivity)
    have hchain :
        Gp = (pExp / 2) ^ 2 * Wp := by
      dsimp [Gp, Wp]
      exact intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
        (params := params) (T := T) (t := t) (pExp := pExp)
        (u := u) (v := v) hsol ht0 htT
    have hweighted_t :
        intervalDomain.integral (fun x =>
          (u t x) ^ (pExp + rho - 2) *
            (intervalDomain.gradNorm (u t) x) ^ 2) ≤
          M ^ rho * Wp := by
      dsimp [Wp]
      exact hweighted pExp t ht0 htT
    have hrewrite :
        cGrad pExp * Gp = M ^ rho * Wp := by
      dsimp [cGrad]
      rw [hchain]
      field_simp [ne_of_gt hden_pos]
    exact le_trans hweighted_t (le_of_eq hrewrite.symm)
  · exact intervalDomain_moserMassPowerToCurrentLpLowerOrder_of_classical
      hsol hcross hboot

theorem intervalDomain_relativeMassGradient_components_BD_of_classical
    {params : CM2Params}
    {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
      LpMassGradientInterpolationEstimate intervalDomain
        (pExp + rho) eta Ceta T u) ∧
      MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0 :=
  ⟨intervalDomain_massGradientInterpolation_of_classical hsol hcross hboot,
    intervalDomain_moserMassPowerToCurrentLpLowerOrder_of_classical hsol hcross hboot⟩

#print axioms intervalDomain_massGradientInterpolation_of_classical
#print axioms intervalDomain_moserMassPowerToCurrentLpLowerOrder_of_classical
#print axioms intervalDomain_relativeMassGradient_of_classical_boundedBefore

end

end ShenWork.IntervalDomainExistence.P3MoserRelativeMassGradientProducer
