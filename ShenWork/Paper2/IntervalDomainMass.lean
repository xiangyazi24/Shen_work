import ShenWork.Paper2.IntervalDomainL2HalfEnergyTimeLeibniz
import ShenWork.Paper2.IntervalDomainL2CrossControl
import ShenWork.Paper2.IntervalDomainLpEnergyFrontiers
import Mathlib.Analysis.Convex.Integral

open ShenWork.IntervalDomain MeasureTheory
open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

def intervalDomainMassTimeDerivIntegrand
    (u : ℝ → intervalDomain.Point → ℝ) (s y : ℝ) : ℝ :=
  deriv (fun r : ℝ => intervalDomainLift (u r) y) s

theorem intervalDomainMassIntegrand_hasDerivAt_interior
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => intervalDomainLift (u r) y)
      (intervalDomainMassTimeDerivIntegrand u s y) s := by
  classical
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  set x : intervalDomain.Point := ⟨y, hyIcc⟩ with hx
  have hxIoo : (x.1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := hy
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r x := by
    intro r
    simp [intervalDomainLift, hyIcc, hx]
  have hw : HasDerivAt (fun r : ℝ => u r x) (intervalDomain.timeDeriv u s x) s :=
    intervalDomain_timeDeriv_isGenuine hsol hxIoo hs
  have hfun : (fun r : ℝ => intervalDomainLift (u r) y) = fun r : ℝ => u r x :=
    funext hlift
  have hval :
      intervalDomainMassTimeDerivIntegrand u s y = intervalDomain.timeDeriv u s x := by
    unfold intervalDomainMassTimeDerivIntegrand
    rw [hfun]
    rfl
  rw [hfun, hval]
  exact hw

theorem intervalDomainMass_hasDerivAt_of_slabContinuous
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball t δ ⊆ Set.Ioo (0 : ℝ) T)
    (hF_meas : ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable (fun y => intervalDomainLift (u s) y)
          intervalDomainInteriorMeasure)
    (hF_int : IntervalIntegrable (fun y => intervalDomainLift (u t) y) volume 0 1)
    (hF'_meas : AEStronglyMeasurable
        (intervalDomainMassTimeDerivIntegrand u t) intervalDomainInteriorMeasure)
    (hslab : ContinuousOn
        (Function.uncurry (intervalDomainMassTimeDerivIntegrand u))
        (Set.Icc (t - δ) (t + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt (fun s => intervalDomain.integral (u s))
      (∫ y in (0 : ℝ)..1, intervalDomainMassTimeDerivIntegrand u t y) t := by
  obtain ⟨bound, hbound_int, h_bound⟩ :=
    exists_bound_of_continuousOn_slab hδ hslab
  have h_diff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball t δ,
        HasDerivAt (fun r => intervalDomainLift (u r) y)
          (intervalDomainMassTimeDerivIntegrand u s y) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    exact Filter.Eventually.of_forall
      (fun y hy s hs => intervalDomainMassIntegrand_hasDerivAt_interior hsol hy (hball hs))
  have hderiv :
      HasDerivAt
        (fun s => ∫ y in (0 : ℝ)..1, intervalDomainLift (u s) y)
        (∫ y in (0 : ℝ)..1, intervalDomainMassTimeDerivIntegrand u t y) t :=
    intervalIntegral_hasDerivAt_time_of_local hδ hF_meas hF_int hF'_meas
      h_bound hbound_int h_diff
  change HasDerivAt
    (fun s => intervalDomainIntegral (u s))
    (∫ y in (0 : ℝ)..1, intervalDomainMassTimeDerivIntegrand u t y) t
  unfold intervalDomainIntegral
  exact hderiv

theorem intervalDomainMassTimeDerivIntegrand_integral_eq_timeDeriv
    (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    (∫ y in (0 : ℝ)..1, intervalDomainMassTimeDerivIntegrand u t y)
      = intervalDomain.integral (fun x => intervalDomain.timeDeriv u t x) := by
  classical
  change _ = intervalDomainIntegral (fun x => intervalDomain.timeDeriv u t x)
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le (zero_le_one)] at hy
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r ⟨y, hy⟩ := by
    intro r
    simp [intervalDomainLift, hy]
  have hfun : (fun r : ℝ => intervalDomainLift (u r) y) =
      fun r : ℝ => u r ⟨y, hy⟩ := funext hlift
  unfold intervalDomainMassTimeDerivIntegrand
  rw [hfun]
  simp [intervalDomain, intervalDomainLift, hy]

theorem intervalDomain_mass_hasDerivAt
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ => intervalDomain.integral (u τ))
      (intervalDomain.integral (fun x => intervalDomain.timeDeriv u t x)) t := by
  obtain ⟨δ, hδ, hball, hIcc⟩ := exists_closedSlab_subset ht
  have hjoint : ContinuousOn
      (Function.uncurry (intervalDomainMassTimeDerivIntegrand u))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.1.1
  have hslab : ContinuousOn
      (Function.uncurry (intervalDomainMassTimeDerivIntegrand u))
      (Set.Icc (t - δ) (t + δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hjoint.mono (Set.prod_mono hIcc (le_refl _))
  have hderiv_slice : ContinuousOn (intervalDomainMassTimeDerivIntegrand u t)
      (Set.Icc (0 : ℝ) 1) :=
    intervalDomain_continuousOn_timeSlice hjoint ht
  have hF'_meas : AEStronglyMeasurable
      (intervalDomainMassTimeDerivIntegrand u t) intervalDomainInteriorMeasure :=
    (hderiv_slice.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hfield : ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.2.1
  have hslice : ContinuousOn (fun x => intervalDomainLift (u t) x)
      (Set.Icc (0 : ℝ) 1) :=
    intervalDomain_continuousOn_timeSlice hfield ht
  have hF_int : IntervalIntegrable (fun y => intervalDomainLift (u t) y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one)]
  have hF_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun y => intervalDomainLift (u s) y)
        intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ((intervalDomain_continuousOn_timeSlice hfield hs).mono
      Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hHD := intervalDomainMass_hasDerivAt_of_slabContinuous hsol hδ hball
    hF_meas hF_int hF'_meas hslab
  convert hHD using 1
  exact (intervalDomainMassTimeDerivIntegrand_integral_eq_timeDeriv u t).symm

theorem intervalDomain_laplacian_integral_eq_zero
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomain.integral (fun x => intervalDomain.laplacian (u t) x) = 0 := by
  classical
  set w : ℝ → ℝ := intervalDomainLift (u t) with hw
  set w' : ℝ → ℝ := deriv w with hw'
  set w'' : ℝ → ℝ := fun y => deriv (fun z : ℝ => deriv w z) y with hw''
  have hCu : ContDiffOn ℝ 2 w (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hCuI : ContDiffOn ℝ 2 w (Set.Ioo (0 : ℝ) 1) :=
    (hsol.regularity.1 t ht).1
  have hw_cont : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.uIcc (0 : ℝ) 1) :=
    continuous_const.continuousOn
  have hw'_cont : ContinuousOn w' (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (zero_le_one)]
    rw [hw']
    exact solution_deriv_lift_continuousOn_Icc hsol ht
  have hconst_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := by
    intro x hx
    exact hasDerivAt_const x (1 : ℝ)
  have hwderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt w' (w'' x) x := by
    intro x hx
    rw [hw', hw'']
    exact (lift_hasDerivAt_interior hsol ht hx).2
  have hzero_int : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_const
  have hw''int : IntervalIntegrable w'' volume 0 1 := by
    rw [hw'']
    have hlap_int :
        IntervalIntegrable
          (intervalDomainLift (fun x => intervalDomain.laplacian (u t) x)) volume 0 1 :=
      intervalDomainLift_laplacian_intervalIntegrable_of_contDiffOn hCu
    refine IntervalIntegrable.congr ?_ hlap_int
    intro y hy
    rw [Set.uIoc_of_le (zero_le_one)] at hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, hy.2⟩
    simp [intervalDomain, intervalDomainLaplacian, intervalDomainLift, hyIcc, hw]
  have hbc0 : w' 0 = 0 := by
    rw [hw', hw]
    exact (hsol.regularity.2.2.2.2.1 t ht).1.2.1
  have hbc1 : w' 1 = 0 := by
    rw [hw', hw]
    exact (hsol.regularity.2.2.2.2.1 t ht).1.2.2
  have hmain :
      (∫ y in (0 : ℝ)..1, (1 : ℝ) * w'' y) =
        - ∫ y in (0 : ℝ)..1, (0 : ℝ) * w' y :=
    intervalFluxByParts_open hw_cont hw'_cont hconst_deriv hwderiv
      hzero_int hw''int hbc0 hbc1
  have hlap :
      intervalDomain.integral (fun x => intervalDomain.laplacian (u t) x)
        = ∫ y in (0 : ℝ)..1, w'' y := by
    change intervalDomainIntegral (fun x => intervalDomain.laplacian (u t) x) = _
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (zero_le_one)] at hy
    simp [intervalDomain, intervalDomainLaplacian, intervalDomainLift, hy, hw, hw'']
  rw [hlap]
  simpa using hmain

theorem intervalDomain_chemotaxisDiv_integral_eq_zero
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomain.integral (fun x => intervalDomain.chemotaxisDiv p (u t) (v t) x) = 0 := by
  classical
  set F : ℝ → ℝ := intervalFlux p (u t) (v t) with hF
  have hconst_cont : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.uIcc (0 : ℝ) 1) :=
    continuous_const.continuousOn
  have hF_cont : ContinuousOn F (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (zero_le_one)]
    exact (flux_contDiffOn_Icc hsol ht).continuousOn
  have hconst_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := by
    intro x hx
    exact hasDerivAt_const x (1 : ℝ)
  have hFderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (deriv F x) x := by
    intro x hx
    rw [hF]
    exact (((flux_contDiffOn_Ioo_of_solution hsol ht).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hzero_int : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_const
  have hF'int : IntervalIntegrable (deriv F) volume 0 1 := by
    rw [hF]
    exact solution_deriv_flux_intervalIntegrable hsol ht
  obtain ⟨hbc0, hbc1⟩ := flux_endpoint_zero hsol ht
  have hmain :
      (∫ y in (0 : ℝ)..1, (1 : ℝ) * deriv F y) =
        - ∫ y in (0 : ℝ)..1, (0 : ℝ) * F y :=
    intervalFluxByParts_open hconst_cont hF_cont hconst_deriv hFderiv
      hzero_int hF'int (by rwa [hF]) (by rwa [hF])
  have hchem :
      intervalDomain.integral (fun x => intervalDomain.chemotaxisDiv p (u t) (v t) x)
        = ∫ y in (0 : ℝ)..1, deriv F y := by
    change intervalDomainIntegral
      (fun x => intervalDomain.chemotaxisDiv p (u t) (v t) x) = _
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (zero_le_one)] at hy
    have hbranch :
        intervalDomainLift
          (fun x => intervalDomain.chemotaxisDiv p (u t) (v t) x) y
          = intervalDomain.chemotaxisDiv p (u t) (v t) ⟨y, hy⟩ := by
      simp [intervalDomainLift, hy]
    rw [hbranch]
    rw [hF]
    rfl
  rw [hchem]
  simpa using hmain

theorem intervalDomainLift_reaction_intervalIntegrable_of_regularity
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift
        (fun x => u t x * (p.a - p.b * (u t x) ^ p.α))) volume 0 1 := by
  classical
  have hreg7 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hcont_u : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    hreg7.continuousOn
  have hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u t) y ≠ 0 := by
    intro y hy
    have : intervalDomainLift (u t) y = u t ⟨y, hy⟩ := by
      simp [intervalDomainLift, hy]
    rw [this]
    exact ne_of_gt (hsol.u_pos' ht0 htT)
  have hpow : ContinuousOn (fun y => (intervalDomainLift (u t) y) ^ p.α)
      (Set.Icc (0 : ℝ) 1) :=
    hcont_u.rpow_const (fun y hy => Or.inl (hpos y hy))
  have hcomp : ContinuousOn
      (fun y => intervalDomainLift (u t) y *
        (p.a - p.b * (intervalDomainLift (u t) y) ^ p.α))
      (Set.Icc (0 : ℝ) 1) :=
    hcont_u.mul (continuousOn_const.sub (continuousOn_const.mul hpow))
  have hEq : Set.EqOn
      (intervalDomainLift
        (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)))
      (fun y => intervalDomainLift (u t) y *
        (p.a - p.b * (intervalDomainLift (u t) y) ^ p.α))
      (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    simp [intervalDomainLift, hy]
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (zero_le_one)]
  exact hcomp.congr hEq

theorem intervalDomain_timeDeriv_integral_eq_reaction
    {p : CM2Params} {T t : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (fun x => intervalDomain.timeDeriv u t x) =
      intervalDomain.integral
        (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) := by
  classical
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  let A : ℝ → ℝ :=
    intervalDomainLift (fun x => intervalDomain.laplacian (u t) x)
  let B : ℝ → ℝ :=
    intervalDomainLift (fun x => intervalDomain.chemotaxisDiv p (u t) (v t) x)
  let C : ℝ → ℝ :=
    intervalDomainLift (fun x => u t x * (p.a - p.b * (u t x) ^ p.α))
  have hAint : IntervalIntegrable A volume 0 1 := by
    dsimp [A]
    exact intervalDomainLift_laplacian_intervalIntegrable_of_contDiffOn
      ((hsol.regularity.2.2.2.2.1 t ht).1.1)
  have hBint : IntervalIntegrable B volume 0 1 := by
    dsimp [B]
    exact intervalDomainLift_chemDiv_intervalIntegrable_of_regularity hsol ht0 htT
  have hCint : IntervalIntegrable C volume 0 1 := by
    dsimp [C]
    exact intervalDomainLift_reaction_intervalIntegrable_of_regularity hsol ht0 htT
  have htime :
      intervalDomain.integral (fun x => intervalDomain.timeDeriv u t x) =
        ∫ y in (0 : ℝ)..1, (A y - p.χ₀ * B y + C y) := by
    change intervalDomainIntegral (fun x => intervalDomain.timeDeriv u t x) = _
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr_ae ?_
    have hne1 : ∀ᵐ y ∂volume, y ≠ (1 : ℝ) := by
      have heq : {y : ℝ | ¬ y ≠ 1} = ({1} : Set ℝ) := by
        ext y
        simp
      rw [MeasureTheory.ae_iff, heq]
      exact Real.volume_singleton
    filter_upwards [hne1] with y hyne hymem
    rw [Set.uIoc_of_le (zero_le_one)] at hymem
    have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hymem.1, lt_of_le_of_ne hymem.2 hyne⟩
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
    have hxin : (⟨y, hyIcc⟩ : intervalDomain.Point) ∈ intervalDomain.inside := hyIoo
    have hpde := hsol.pde_u ht0 htT hxin
    simp [A, B, C, intervalDomain, intervalDomainLift, hyIcc] at hpde ⊢
    rw [hpde]
  have hsplit :
      (∫ y in (0 : ℝ)..1, (A y - p.χ₀ * B y + C y)) =
        (∫ y in (0 : ℝ)..1, A y) -
          p.χ₀ * (∫ y in (0 : ℝ)..1, B y) +
            ∫ y in (0 : ℝ)..1, C y := by
    have hAB : IntervalIntegrable (fun y => A y - p.χ₀ * B y) volume 0 1 :=
      hAint.sub (hBint.const_mul p.χ₀)
    rw [intervalIntegral.integral_add hAB hCint,
      intervalIntegral.integral_sub hAint (hBint.const_mul p.χ₀),
      intervalIntegral.integral_const_mul]
  have hAzero : (∫ y in (0 : ℝ)..1, A y) = 0 := by
    dsimp [A]
    simpa [intervalDomainIntegral] using
      intervalDomain_laplacian_integral_eq_zero hsol ht
  have hBzero : (∫ y in (0 : ℝ)..1, B y) = 0 := by
    dsimp [B]
    simpa [intervalDomainIntegral] using
      intervalDomain_chemotaxisDiv_integral_eq_zero hsol ht
  have hCeq :
      (∫ y in (0 : ℝ)..1, C y) =
        intervalDomain.integral
          (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) := by
    rfl
  rw [htime, hsplit, hAzero, hBzero, hCeq]
  ring

theorem intervalDomain_Paper2MassDerivativeIdentity
    (p : CM2Params) :
    Paper2MassDerivativeIdentity intervalDomain p := by
  intro T hT u v hsol t ht0 htT
  have hderiv :=
    intervalDomain_mass_hasDerivAt hsol (t := t)
      (show t ∈ Set.Ioo (0 : ℝ) T from ⟨ht0, htT⟩)
  have hEq :=
    intervalDomain_timeDeriv_integral_eq_reaction hsol ht0 htT
  rwa [← hEq]

theorem intervalDomain_integral_abs_sub_le_supNorm
    (f g : intervalDomain.Point → ℝ)
    (hf : IntervalIntegrable (intervalDomainLift f) volume 0 1)
    (hg : IntervalIntegrable (intervalDomainLift g) volume 0 1)
    (hbdd : BddAbove (Set.range (fun x : intervalDomain.Point => |f x - g x|))) :
    |intervalDomain.integral f - intervalDomain.integral g| ≤
      intervalDomain.supNorm (fun x => f x - g x) := by
  classical
  change |intervalDomainIntegral f - intervalDomainIntegral g| ≤
    intervalDomainSupNorm (fun x => f x - g x)
  have hsub :
      intervalDomainIntegral f - intervalDomainIntegral g =
        ∫ y in (0 : ℝ)..1, (intervalDomainLift f y - intervalDomainLift g y) := by
    unfold intervalDomainIntegral
    rw [intervalIntegral.integral_sub hf hg]
  rw [hsub]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (C := intervalDomainSupNorm (fun x => f x - g x))
    (f := fun y => intervalDomainLift f y - intervalDomainLift g y) (by
      intro y hyu
      rw [Set.uIoc_of_le (zero_le_one)] at hyu
      have hy : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hyu.1, hyu.2⟩
      have hle :
          |f ⟨y, hy⟩ - g ⟨y, hy⟩| ≤
            intervalDomainSupNorm (fun x => f x - g x) := by
        unfold intervalDomainSupNorm
        exact le_csSup hbdd ⟨⟨y, hy⟩, rfl⟩
      simpa [intervalDomainLift, hy, Real.norm_eq_abs] using hle)
  simpa using hnorm

private theorem intervalDomainLift_continuousOn_Icc_of_continuous
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift f) = f := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    split_ifs
    exact congr_arg f (Subtype.ext rfl)
  rw [heq]
  exact hf

private theorem intervalDomain_solution_lift_continuousOn_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
  ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn

private theorem intervalDomain_solution_lift_pos_Icc
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) x := by
  intro x hx
  rw [intervalDomainLift]
  simp only [hx, dif_pos]
  exact hsol.u_pos' ht.1 ht.2

private theorem intervalDomain_solution_slice_abs_bddAbove
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
  classical
  have hcont := intervalDomain_solution_lift_continuousOn_Icc hsol ht
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  refine ⟨M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := hM ⟨x.1, x.2, rfl⟩
  have hlift : intervalDomainLift (u t) x.1 = u t x := by
    simp [intervalDomainLift]
  simpa [hlift] using hx

/-- A positive classical interval-domain slice has strictly positive mass. -/
theorem intervalDomain_classicalSolution_mass_pos
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    0 < intervalDomain.integral (u t) := by
  unfold intervalDomain intervalDomainIntegral
  exact intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
    (intervalDomain_solution_lift_continuousOn_Icc hsol ht)
    (fun y hy => (intervalDomain_solution_lift_pos_Icc hsol ht y
      ⟨le_of_lt hy.1, hy.2⟩).le)
    ⟨(1 : ℝ) / 2, ⟨by norm_num, by norm_num⟩,
      intervalDomain_solution_lift_pos_Icc hsol ht ((1 : ℝ) / 2)
        ⟨by norm_num, by norm_num⟩⟩

/-- On the unit interval, the mass of a positive classical slice is bounded by
its concrete supremum norm. -/
theorem intervalDomain_classicalSolution_mass_le_supNorm
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomain.integral (u t) ≤ intervalDomain.supNorm (u t) := by
  have hu_cont := intervalDomain_solution_lift_continuousOn_Icc hsol ht
  have hu_int : IntervalIntegrable (intervalDomainLift (u t)) volume 0 1 := by
    have hu_cont_uIcc : ContinuousOn (intervalDomainLift (u t))
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hu_cont
    exact hu_cont_uIcc.intervalIntegrable
  have hzero_int : IntervalIntegrable
      (intervalDomainLift (fun _ : intervalDomain.Point => (0 : ℝ))) volume 0 1 := by
    have hzero : intervalDomainLift (fun _ : intervalDomain.Point => (0 : ℝ)) =
        fun _ => 0 := by
      funext y
      simp [intervalDomainLift]
    rw [hzero]
    exact intervalIntegral.intervalIntegrable_const
  have hbdd := intervalDomain_solution_slice_abs_bddAbove hsol ht
  have hbdd_diff :
      BddAbove (Set.range (fun x : intervalDomain.Point => |u t x - 0|)) := by
    simpa using hbdd
  have hle := intervalDomain_integral_abs_sub_le_supNorm
    (f := u t) (g := fun _ => 0) hu_int hzero_int hbdd_diff
  have hzero_mass :
      intervalDomain.integral (fun _ : intervalDomain.Point => (0 : ℝ)) = 0 := by
    change intervalDomainIntegral (fun _ : intervalDomain.Point => (0 : ℝ)) = 0
    unfold intervalDomainIntegral
    have hzero : intervalDomainLift (fun _ : intervalDomain.Point => (0 : ℝ)) =
        fun _ => 0 := by
      funext y
      simp [intervalDomainLift]
    rw [hzero]
    simp
  rw [hzero_mass] at hle
  have habs :
      |intervalDomain.integral (u t)| ≤ intervalDomain.supNorm (u t) := by
    simpa using hle
  exact (le_abs_self _).trans habs

private theorem bddAbove_range_abs_diff_of_bddAbove
    {f g : intervalDomain.Point → ℝ}
    (hf : BddAbove (Set.range (fun x => |f x|)))
    (hg : BddAbove (Set.range (fun x => |g x|))) :
    BddAbove (Set.range (fun x => |f x - g x|)) := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf + Mg, ?_⟩
  rintro _ ⟨x, rfl⟩
  calc |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ Mf + Mg := add_le_add (hMf ⟨x, rfl⟩) (hMg ⟨x, rfl⟩)

private theorem intervalDomain_mass_tendsto_initial
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → t < T →
      |intervalDomain.integral (u t) - intervalDomain.integral u₀| < ε := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := htrace ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht0 htδ htT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hu_cont := intervalDomain_solution_lift_continuousOn_Icc hsol ht
  have hu0_cont := intervalDomainLift_continuousOn_Icc_of_continuous hu₀.admissible.2
  have hu_int : IntervalIntegrable (intervalDomainLift (u t)) volume 0 1 := by
    have hu_cont_uIcc : ContinuousOn (intervalDomainLift (u t)) (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hu_cont
    exact hu_cont_uIcc.intervalIntegrable
  have hu0_int : IntervalIntegrable (intervalDomainLift u₀) volume 0 1 :=
    by
      have hu0_cont_uIcc : ContinuousOn (intervalDomainLift u₀) (Set.uIcc (0 : ℝ) 1) := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hu0_cont
      exact hu0_cont_uIcc.intervalIntegrable
  have hbdd_u := intervalDomain_solution_slice_abs_bddAbove hsol ht
  have hbdd_diff :
      BddAbove (Set.range (fun x : intervalDomain.Point => |u t x - u₀ x|)) :=
    bddAbove_range_abs_diff_of_bddAbove hbdd_u hu₀.admissible.1
  have hle := intervalDomain_integral_abs_sub_le_supNorm
    (f := u t) (g := u₀) hu_int hu0_int hbdd_diff
  exact lt_of_le_of_lt hle (hδ t ht0 htδ)

theorem intervalDomain_mass_jensen
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    (intervalDomain.integral (u t)) ^ (1 + p.α) ≤
      intervalDomain.integral (fun x => (u t x) ^ (1 + p.α)) := by
  let f : ℝ → ℝ := intervalDomainLift (u t)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    exact intervalDomain_solution_lift_continuousOn_Icc hsol ht
  have hfpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x := by
    intro x hx
    dsimp [f]
    exact intervalDomain_solution_lift_pos_Icc hsol ht x hx
  have hpone : (1 : ℝ) ≤ 1 + p.α := by linarith [p.hα]
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ (1 + p.α)) :=
    convexOn_rpow hpone
  have hcontpow : ContinuousOn (fun x : ℝ => x ^ (1 + p.α)) (Set.Ici (0 : ℝ)) :=
    (Real.continuous_rpow_const (by linarith [p.hα] : 0 ≤ 1 + p.α)).continuousOn
  have hfs : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), f x ∈ Set.Ici (0 : ℝ) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx => (hfpos x ⟨le_of_lt hx.1, hx.2⟩).le
  have hfi_on : IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume :=
    hfcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpowcont_Icc : ContinuousOn (fun x => f x ^ (1 + p.α)) (Set.Icc (0 : ℝ) 1) :=
    hfcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hfpos x hx)))
  have hgi_on : IntegrableOn ((fun x : ℝ => x ^ (1 + p.α)) ∘ f)
      (Set.Ioc (0 : ℝ) 1) volume := by
    change IntegrableOn (fun x => f x ^ (1 + p.α)) (Set.Ioc (0 : ℝ) 1) volume
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
        (⨍ x in Set.Ioc (0 : ℝ) 1, f x ^ (1 + p.α) ∂volume) =
          ∫ x in (0 : ℝ)..1, f x ^ (1 + p.α) := by
      rw [MeasureTheory.setAverage_eq, hμ]
      simp [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    rw [hAvg_f, hAvg_pow] at hJ
    have hpow_int_eq :
        (∫ x in (0 : ℝ)..1, f x ^ (1 + p.α)) =
          intervalDomainIntegral (fun x => (u t x) ^ (1 + p.α)) := by
      unfold intervalDomainIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hx
      simp [f, intervalDomainLift, hxIcc]
    change (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x) ^ (1 + p.α) ≤
      intervalDomainIntegral (fun x => (u t x) ^ (1 + p.α))
    rwa [hpow_int_eq] at hJ
  · simp [Real.volume_Ioc]
  · simp [Real.volume_Ioc]

theorem intervalDomain_reaction_integral_eq
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomain.integral
        (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) =
      p.a * intervalDomain.integral (u t) -
        p.b * intervalDomain.integral (fun x => (u t x) ^ (1 + p.α)) := by
  let f : ℝ → ℝ := intervalDomainLift (u t)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    exact intervalDomain_solution_lift_continuousOn_Icc hsol ht
  have hfpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < f x := by
    intro x hx
    dsimp [f]
    exact intervalDomain_solution_lift_pos_Icc hsol ht x hx
  have hf_int : IntervalIntegrable f volume 0 1 := by
    have hfcont_uIcc : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hfcont
    exact hfcont_uIcc.intervalIntegrable
  have hpowα_cont : ContinuousOn (fun x => f x ^ p.α) (Set.Icc (0 : ℝ) 1) :=
    hfcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hfpos x hx)))
  have hpowα_int : IntervalIntegrable (fun x => f x ^ p.α) volume 0 1 :=
    by
      have hpowα_cont_uIcc :
          ContinuousOn (fun x => f x ^ p.α) (Set.uIcc (0 : ℝ) 1) := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hpowα_cont
      exact hpowα_cont_uIcc.intervalIntegrable
  have hpow1_cont : ContinuousOn (fun x => f x ^ (1 + p.α)) (Set.Icc (0 : ℝ) 1) :=
    hfcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hfpos x hx)))
  have hpow1_int : IntervalIntegrable (fun x => f x ^ (1 + p.α)) volume 0 1 :=
    by
      have hpow1_cont_uIcc :
          ContinuousOn (fun x => f x ^ (1 + p.α)) (Set.uIcc (0 : ℝ) 1) := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hpow1_cont
      exact hpow1_cont_uIcc.intervalIntegrable
  have hreact_congr :
      intervalDomain.integral
          (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) =
        ∫ y in (0 : ℝ)..1, f y * (p.a - p.b * f y ^ p.α) := by
    unfold intervalDomain intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hy
    simp [f, intervalDomainLift, hyIcc]
  have hpow_congr :
      intervalDomain.integral (fun x => (u t x) ^ (1 + p.α)) =
        ∫ y in (0 : ℝ)..1, f y ^ (1 + p.α) := by
    unfold intervalDomain intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hy
    simp [f, intervalDomainLift, hyIcc]
  have hmass_congr :
      intervalDomain.integral (u t) = ∫ y in (0 : ℝ)..1, f y := rfl
  rw [hreact_congr, hpow_congr, hmass_congr]
  have hprod :
      (∫ y in (0 : ℝ)..1, f y * (p.a - p.b * f y ^ p.α)) =
        ∫ y in (0 : ℝ)..1, (p.a * f y - p.b * f y ^ (1 + p.α)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hy
    have hfy : 0 < f y := hfpos y hyIcc
    have hpow : f y * (f y ^ p.α) = f y ^ (1 + p.α) := by
      have hpowadd : f y ^ (1 + p.α) = f y ^ 1 * f y ^ p.α := by
        simpa using Real.rpow_add hfy (1 : ℝ) p.α
      simpa [Real.rpow_one] using hpowadd.symm
    calc
      f y * (p.a - p.b * f y ^ p.α)
          = p.a * f y - p.b * (f y * f y ^ p.α) := by ring
      _ = p.a * f y - p.b * f y ^ (1 + p.α) := by rw [hpow]
  rw [hprod]
  rw [intervalIntegral.integral_sub (hf_int.const_mul p.a) (hpow1_int.const_mul p.b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

private theorem intervalDomain_reaction_integral_le_logistic
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    intervalDomain.integral
        (fun x => u t x * (p.a - p.b * (u t x) ^ p.α)) ≤
      intervalDomain.integral (u t) *
        (p.a - p.b * (intervalDomain.integral (u t)) ^ p.α) := by
  set M : ℝ := intervalDomain.integral (u t)
  set P : ℝ := intervalDomain.integral (fun x => (u t x) ^ (1 + p.α))
  have hJ : M ^ (1 + p.α) ≤ P := by
    dsimp [M, P]
    exact intervalDomain_mass_jensen hsol ht
  have hM_pos : 0 < M := by
    dsimp [M]
    unfold intervalDomain intervalDomainIntegral
    exact intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
      (intervalDomain_solution_lift_continuousOn_Icc hsol ht)
      (fun y hy => (intervalDomain_solution_lift_pos_Icc hsol ht y
        ⟨le_of_lt hy.1, hy.2⟩).le)
      ⟨(1 : ℝ) / 2, ⟨by norm_num, by norm_num⟩,
        intervalDomain_solution_lift_pos_Icc hsol ht ((1 : ℝ) / 2)
          ⟨by norm_num, by norm_num⟩⟩
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hEq := intervalDomain_reaction_integral_eq hsol ht
  rw [hEq]
  have hpow_add : M ^ (1 + p.α) = M * M ^ p.α := by
    rw [show (1 + p.α) = 1 + p.α by rfl, Real.rpow_add hM_pos,
      Real.rpow_one]
  have hRle : p.a * M - p.b * P ≤ p.a * M - p.b * (M ^ (1 + p.α)) := by
    nlinarith [mul_le_mul_of_nonneg_left hJ p.hb]
  rw [hpow_add] at hRle
  change p.a * M - p.b * P ≤ M * (p.a - p.b * M ^ p.α)
  nlinarith

theorem intervalDomain_Paper2MassComparisonPrinciple
    (p : CM2Params) :
    Paper2MassComparisonPrinciple intervalDomain p := by
  intro u₀ hu₀ T hT u v hsol htrace hmassDeriv
  let M : ℝ → ℝ := fun t => intervalDomain.integral (u t)
  have hM_cont : ContinuousOn M (Set.Ioo (0 : ℝ) T) := by
    intro t ht
    exact (hmassDeriv t ht.1 ht.2).continuousAt.continuousWithinAt
  have hM_initial :
      ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → t < T →
        |M t - intervalDomain.integral u₀| < ε := by
    simpa [M] using intervalDomain_mass_tendsto_initial hu₀ hsol htrace
  refine ⟨?_, ?_⟩
  · intro ha hb t ht0 htT
    have hderiv_zero :
        ∀ s ∈ Set.Ioo (0 : ℝ) T, deriv M s = 0 := by
      intro s hs
      have hder := hmassDeriv s hs.1 hs.2
      have hval :
          intervalDomain.integral
              (fun x => u s x * (p.a - p.b * (u s x) ^ p.α)) = 0 := by
        rw [ha, hb]
        unfold intervalDomain intervalDomainIntegral
        simp
      rw [hder.deriv, hval]
    have hdiff : DifferentiableOn ℝ M (Set.Ioo (0 : ℝ) T) := by
      intro s hs
      exact (hmassDeriv s hs.1 hs.2).differentiableAt.differentiableWithinAt
    have hconst :
        ∀ s₁ ∈ Set.Ioo (0 : ℝ) T, ∀ s₂ ∈ Set.Ioo (0 : ℝ) T,
          M s₁ = M s₂ := fun s₁ hs₁ s₂ hs₂ =>
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hdiff hderiv_zero hs₁ hs₂
    have h_abs : ∀ ε > 0, |M t - intervalDomain.integral u₀| < ε := by
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := hM_initial ε hε
      set s := min (δ / 2) (T / 2)
      have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
      have hs_lt_δ : s < δ :=
        lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hs_lt_T : s < T :=
        lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have h1 : M t = M s := hconst t ⟨ht0, htT⟩ s ⟨hs_pos, hs_lt_T⟩
      rw [h1]
      exact hδ s hs_pos hs_lt_δ hs_lt_T
    have h_eq : M t = intervalDomain.integral u₀ := by
      have hzero : M t - intervalDomain.integral u₀ = 0 := by
        by_contra hne
        have hpos : 0 < |M t - intervalDomain.integral u₀| := abs_pos.mpr hne
        exact absurd (h_abs _ hpos) (lt_irrefl _)
      linarith
    exact h_eq
  · intro ha hb t ht0 htT
    set K : ℝ := (p.a / p.b) ^ (1 / p.α)
    by_cases hle : M t ≤ K
    · have hvol : intervalDomain.volume = 1 := rfl
      change M t ≤
        max (intervalDomain.integral u₀) (K * intervalDomain.volume)
      rw [hvol, mul_one]
      exact le_trans hle (le_max_right _ _)
    push_neg at hle
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      exact Real.rpow_nonneg (div_nonneg ha.le hb.le) _
    have hM_deriv_nonpos :
        ∀ s ∈ Set.Ioo (0 : ℝ) T, K < M s →
          ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt M d s := by
      intro s hs hgt
      have hder := hmassDeriv s hs.1 hs.2
      have hle_log := intervalDomain_reaction_integral_le_logistic hsol hs
      have hMpos : 0 < M s := lt_of_le_of_lt hK_nonneg hgt
      have hα_ne : p.α ≠ 0 := ne_of_gt p.hα
      have h_lhs : K ^ p.α = p.a / p.b := by
        rw [show K = (p.a / p.b) ^ (1 / p.α) by rfl,
          ← Real.rpow_mul (div_nonneg ha.le hb.le), one_div_mul_cancel hα_ne,
          Real.rpow_one]
      have hMα_gt : p.a / p.b < (M s) ^ p.α := by
        have hraw := Real.rpow_lt_rpow hK_nonneg hgt p.hα
        rwa [h_lhs] at hraw
      have h_bMα : p.a < p.b * (M s) ^ p.α := by
        have hcalc := mul_lt_mul_of_pos_left hMα_gt hb
        rwa [mul_div_cancel₀ _ (ne_of_gt hb)] at hcalc
      have hreact_neg : p.a - p.b * (M s) ^ p.α < 0 := by linarith
      have hprod_neg : M s * (p.a - p.b * (M s) ^ p.α) < 0 :=
        mul_neg_of_pos_of_neg hMpos hreact_neg
      refine ⟨intervalDomain.integral
          (fun x => u s x * (p.a - p.b * (u s x) ^ p.α)), ?_, ?_⟩
      · exact le_trans hle_log (le_of_lt hprod_neg)
      · exact hder
    have hAbove : ∀ s ∈ Set.Ioc (0 : ℝ) t, K < M s :=
      threshold_persists_below_of_hasDerivAt_nonpos
        ht0 htT hM_cont hM_deriv_nonpos hle
    have hM_antitone : ∀ s ∈ Set.Ioc (0 : ℝ) t, M t ≤ M s := by
      intro s hs
      obtain ⟨hs_pos, hs_le⟩ := hs
      have hIcc_sub_Ioo : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T :=
        fun s' ⟨h1, h2⟩ =>
          ⟨lt_of_lt_of_le hs_pos h1, lt_of_le_of_lt h2 htT⟩
      have hIcc_sub_Ioc : Set.Icc s t ⊆ Set.Ioc (0 : ℝ) t :=
        fun s' ⟨h1, h2⟩ => ⟨lt_of_lt_of_le hs_pos h1, h2⟩
      have hM_cont_Icc : ContinuousOn M (Set.Icc s t) :=
        hM_cont.mono hIcc_sub_Ioo
      have hM_deriv_Ioo :
          ∀ s' ∈ Set.Ioo s t,
            DifferentiableAt ℝ M s' ∧ deriv M s' ≤ 0 := by
        intro s' hs'
        have hs'_in_Ioo : s' ∈ Set.Ioo (0 : ℝ) T :=
          hIcc_sub_Ioo ⟨hs'.1.le, hs'.2.le⟩
        have hs'_in_Ioc : s' ∈ Set.Ioc (0 : ℝ) t :=
          hIcc_sub_Ioc ⟨hs'.1.le, hs'.2.le⟩
        obtain ⟨d, hd_nonpos, hd⟩ :=
          hM_deriv_nonpos s' hs'_in_Ioo (hAbove s' hs'_in_Ioc)
        exact ⟨hd.differentiableAt, by rw [hd.deriv]; exact hd_nonpos⟩
      have hDiff_Ioo : DifferentiableOn ℝ M (Set.Ioo s t) :=
        fun s' hs' => (hM_deriv_Ioo s' hs').1.differentiableWithinAt
      have hDeriv_nonpos :
          ∀ s' ∈ interior (Set.Icc s t), deriv M s' ≤ 0 := by
        intro s' hs'
        rw [interior_Icc] at hs'
        exact (hM_deriv_Ioo s' hs').2
      have hAntitone : AntitoneOn M (Set.Icc s t) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hM_cont_Icc
        · rw [interior_Icc]; exact hDiff_Ioo
        · exact hDeriv_nonpos
      exact hAntitone (Set.left_mem_Icc.mpr hs_le)
        (Set.right_mem_Icc.mpr hs_le) hs_le
    have hM_t_le_u₀ : M t ≤ intervalDomain.integral u₀ := by
      have h_lt_all : ∀ ε > 0, M t < intervalDomain.integral u₀ + ε := by
        intro ε hε
        obtain ⟨δ, hδ_pos, hδ⟩ := hM_initial ε hε
        set s := min (δ / 2) (t / 2)
        have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
        have hs_lt_δ : s < δ :=
          lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hs_lt_t : s < t :=
          lt_of_le_of_lt (min_le_right _ _) (by linarith)
        have h1 : M t ≤ M s := hM_antitone s ⟨hs_pos, hs_lt_t.le⟩
        have h2 : |M s - intervalDomain.integral u₀| < ε :=
          hδ s hs_pos hs_lt_δ (lt_trans hs_lt_t htT)
        have h3 : M s < intervalDomain.integral u₀ + ε :=
          by linarith [(abs_sub_lt_iff.mp h2).1]
        exact lt_of_le_of_lt h1 h3
      by_contra hgt
      push_neg at hgt
      have := h_lt_all (M t - intervalDomain.integral u₀) (by linarith)
      linarith
    have hvol : intervalDomain.volume = 1 := rfl
    change M t ≤
      max (intervalDomain.integral u₀) (K * intervalDomain.volume)
    rw [hvol, mul_one]
    exact le_trans hM_t_le_u₀ (le_max_left _ _)

theorem intervalDomain_Proposition_2_4
    (p : CM2Params) :
    Proposition_2_4 intervalDomain p :=
  Proposition_2_4.of_mass_derivative_identity_and_comparison
    (intervalDomain_Paper2MassDerivativeIdentity p)
    (intervalDomain_Paper2MassComparisonPrinciple p)

#print axioms intervalDomain_Proposition_2_4

end

end ShenWork.Paper2
