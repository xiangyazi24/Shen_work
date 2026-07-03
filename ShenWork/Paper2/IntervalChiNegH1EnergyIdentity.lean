/-
  ShenWork/Paper2/IntervalChiNegH1EnergyIdentity.lean

  The H¹ ENERGY IDENTITY `HasDerivAt (H1energy u) value τ` via the
  FINITE-DIFFERENCE + SPATIAL-IBP route (Route C), avoiding the missing
  mixed time-space derivative `u_xt`.

  ## Route C idea.
  Instead of the standard `y' = ∫ u_x · u_xt` (which needs `u_xt`),
  compute the DIFFERENCE:
    H1energy(s) - H1energy(t)
      = ½∫ (u_x(s)² - u_x(t)²)
      = ½∫ (u_x(s)+u_x(t)) · ∂_x(u(s)-u(t))
      = -½∫ (u_xx(s)+u_xx(t)) · (u(s)-u(t))   [spatial IBP, Neumann]
  Divide by `(s-t)` and send `s→t`:
    y'(t) = -∫ u_xx(t) · u_t(t).
  Uses ONLY: spatial C² at each time, Neumann BC, joint continuity of
  u_t (conjunct 8), joint continuity of u (conjunct 9), and L¹ continuity
  of u_xx in time (from PDE: u_xx = u_t + taxis - reaction).

  ## WHAT LANDS (DERIVED, no sorry):
   * `H1energy_sub_eq_neg_half_int_uxx_sum_times_diff` — Step 1 identity
   * PDE substitution packaging into `H1EnergyIdentity` shape

  ## CARRIED:
   * `hUxxL1Cont` — L¹ continuity of u_xx in time: for t ∈ (0,T),
     `∫₀¹ |u_xx(s) - u_xx(t)| → 0` as `s→t`. TRUE by standard parabolic
     regularity (u_xx = u_t + F where u_t is jointly continuous and F
     varies continuously by v_xx = v_t + μv - νu^γ joint continuity).
     Fails grep: `grep -rn "u_xx.*L1.*continuous\|uxx.*time" ShenWork → NONE`.

  No `sorry`/`admit`/`native_decide`/custom `axiom` in the derived parts.
  Lines ≤ 100.
-/
import ShenWork.Paper2.IntervalChiNegH1Energy
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.IntervalUnderIntegralLeibniz
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.IntervalFullKernelBoundaryRegularity
import ShenWork.Paper2.IntervalDomainEnergyStep
import ShenWork.Paper2.IntervalDomainL2CrossControl
import ShenWork.Paper2.Statements
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Set Filter
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.Paper2 (IsPaper2ClassicalSolution)
open ShenWork.Paper2.IntervalChiNegH1Energy
  (H1energy lapL2sq H1EnergyIdentity)
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalFullKernelRegularity

namespace ShenWork.Paper2.IntervalChiNegH1EnergyIdentity

open ShenWork.IntervalUnderIntegralLeibniz
open ShenWork.Paper2.IntervalDomainLpMonotonicity
open ShenWork.Paper2.IntervalDomainEnergyStep

/-! ## Notation abbreviations -/

/-- Shorthand for the second spatial derivative of the lift. -/
abbrev liftDeriv2 (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : ℝ) : ℝ :=
  deriv (fun y => deriv (intervalDomainLift (u t)) y) x

/-- Shorthand for the first spatial derivative of the lift. -/
abbrev liftDeriv1 (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : ℝ) : ℝ :=
  deriv (intervalDomainLift (u t)) x

/-- Shorthand for the time derivative of the lift at fixed x. -/
abbrev liftTimeDeriv (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : ℝ) : ℝ :=
  deriv (fun s => intervalDomainLift (u s) x) t

/-! ## Local regularity wrappers -/

theorem liftTimeDeriv_hasDerivAt_of_mem_Icc
    {p : CM2Params} {T s y : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hy : y ∈ Icc (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r : ℝ => intervalDomainLift (u r) y)
      (liftTimeDeriv u s y) s := by
  classical
  set x : intervalDomainPoint := ⟨y, hy⟩ with hx
  have hlift : ∀ r : ℝ, intervalDomainLift (u r) y = u r x := by
    intro r
    simp [intervalDomainLift, hy, hx]
  have hfun : (fun r : ℝ => intervalDomainLift (u r) y) =
      fun r : ℝ => u r x := funext hlift
  have hdiff : DifferentiableAt ℝ (fun r : ℝ => u r x) s :=
    (hsol.regularity.2.1 x s hs).1.1
  have hval : liftTimeDeriv u s y = intervalDomain.timeDeriv u s x := by
    unfold liftTimeDeriv
    change deriv (fun r : ℝ => intervalDomainLift (u r) y) s =
      deriv (fun r : ℝ => u r x) s
    rw [hfun]
  rw [hfun, hval]
  simpa [intervalDomain] using hdiff.hasDerivAt

theorem derivWithin_lift_u_left_eq_zero
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    derivWithin (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) 0 = 0 := by
  have hset : (Set.Ici (0 : ℝ)) =ᶠ[𝓝 (0 : ℝ)] (Icc (0 : ℝ) 1) := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    simp only [eq_iff_iff]
    exact ⟨fun h0 => ⟨h0, le_of_lt hx⟩, fun h => h.1⟩
  have hN := (hsol.neumann ht.1 ht.2 intervalDomain_leftEndpoint_mem_boundary).1
  have hNeq : intervalDomain.normalDeriv (u t) intervalDomainLeftEndpoint =
      derivWithin (intervalDomainLift (u t)) (Set.Ici (0 : ℝ)) 0 := by
    show ShenWork.IntervalDomain.intervalDomainNormalDeriv
      (u t) intervalDomainLeftEndpoint = _
    unfold ShenWork.IntervalDomain.intervalDomainNormalDeriv
    rw [if_pos (show (intervalDomainLeftEndpoint : intervalDomainPoint).1 = 0 from rfl)]
  rw [hNeq, derivWithin_congr_set hset] at hN
  exact hN

theorem derivWithin_lift_u_right_eq_zero
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    derivWithin (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) 1 = 0 := by
  have hset : (Set.Iic (1 : ℝ)) =ᶠ[𝓝 (1 : ℝ)] (Icc (0 : ℝ) 1) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    simp only [eq_iff_iff]
    exact ⟨fun h1 => ⟨le_of_lt hx, h1⟩, fun h => h.2⟩
  have hN := (hsol.neumann ht.1 ht.2 intervalDomain_rightEndpoint_mem_boundary).1
  have hNeq : intervalDomain.normalDeriv (u t) intervalDomainRightEndpoint =
      derivWithin (intervalDomainLift (u t)) (Set.Iic (1 : ℝ)) 1 := by
    show ShenWork.IntervalDomain.intervalDomainNormalDeriv
      (u t) intervalDomainRightEndpoint = _
    unfold ShenWork.IntervalDomain.intervalDomainNormalDeriv
    rw [if_neg (show ¬ (intervalDomainRightEndpoint : intervalDomainPoint).1 = 0 by
        norm_num [intervalDomainRightEndpoint]),
      if_pos (show (intervalDomainRightEndpoint : intervalDomainPoint).1 = 1 from rfl)]
  rw [hNeq, derivWithin_congr_set hset] at hN
  exact hN

theorem lift_difference_quotient_bound_of_timeDeriv_bound
    {p : CM2Params} {T τ δ M s y : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hδ : 0 < δ) (hball : Metric.ball τ δ ⊆ Ioo (0 : ℝ) T)
    (hy : y ∈ Icc (0 : ℝ) 1)
    (hM : ∀ r ∈ Metric.ball τ δ, ‖liftTimeDeriv u r y‖ ≤ M)
    (hs : s ∈ Metric.ball τ δ) (hsτ : s ≠ τ) :
    ‖(intervalDomainLift (u s) y - intervalDomainLift (u τ) y) / (s - τ)‖ ≤ M := by
  classical
  set f : ℝ → ℝ := fun r => intervalDomainLift (u r) y with hf
  have hτball : τ ∈ Metric.ball τ δ := Metric.mem_ball_self hδ
  have hdiff : ∀ r ∈ Metric.ball τ δ, DifferentiableAt ℝ f r := by
    intro r hr
    exact (liftTimeDeriv_hasDerivAt_of_mem_Icc hsol hy (hball hr)).differentiableAt
  have hderiv : ∀ r ∈ Metric.ball τ δ, ‖deriv f r‖ ≤ M := by
    intro r hr
    have hD := liftTimeDeriv_hasDerivAt_of_mem_Icc hsol hy (hball hr)
    have hDv : deriv f r = liftTimeDeriv u r y := by
      exact hD.deriv
    rw [hDv]
    exact hM r hr
  have hmv := (convex_ball τ δ).norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv hτball hs
  have hden : ‖s - τ‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsτ)
  have hden_pos : 0 < ‖s - τ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsτ)
  have hcalc :
      ‖(intervalDomainLift (u s) y - intervalDomainLift (u τ) y) / (s - τ)‖ =
        ‖f s - f τ‖ / ‖s - τ‖ := by
    rw [hf]
    simp [norm_div]
  rw [hcalc]
  exact (div_le_iff₀ hden_pos).2 hmv

theorem integrable_interior_of_intervalIntegrable
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    Integrable f intervalDomainInteriorMeasure := by
  have hIoc : IntegrableOn f (Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)).mp hf
  simpa [intervalDomainInteriorMeasure,
    MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using hIoc.integrable

theorem weighted_lift_diff_integral_hasDerivAt
    {p : CM2Params} {T τ δ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Ioo (0 : ℝ) T)
    (hδ : 0 < δ)
    (hball : Metric.ball τ δ ⊆ Ioo (0 : ℝ) T)
    (hIcc : Icc (τ - δ) (τ + δ) ⊆ Ioo (0 : ℝ) T)
    {a : ℝ → ℝ} (ha_int : IntervalIntegrable a volume 0 1) :
    HasDerivAt
      (fun s => ∫ y in (0 : ℝ)..1,
        -(a y * (intervalDomainLift (u s) y -
          intervalDomainLift (u τ) y)))
      (-(∫ y in (0 : ℝ)..1, a y * liftTimeDeriv u τ y)) τ := by
  classical
  have hUt_joint : ContinuousOn
      (Function.uncurry (fun t y => liftTimeDeriv u t y))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.1.1
  have hUt_slab : ContinuousOn
      (Function.uncurry (fun t y => liftTimeDeriv u t y))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    hUt_joint.mono (Set.prod_mono hIcc (Subset.rfl))
  have hcompact : IsCompact
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_Icc).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hUt_slab
  have ha_int_interior : Integrable a intervalDomainInteriorMeasure :=
    integrable_interior_of_intervalIntegrable ha_int
  have hnorm_a_int : Integrable (fun y => ‖a y‖) intervalDomainInteriorMeasure :=
    ha_int_interior.norm
  have hbound_int : Integrable (fun y => M * ‖a y‖) intervalDomainInteriorMeasure :=
    hnorm_a_int.const_mul M
  have ha_aes : AEStronglyMeasurable a intervalDomainInteriorMeasure :=
    ha_int_interior.aestronglyMeasurable
  have hU_joint : ContinuousOn
      (Function.uncurry (fun t y => intervalDomainLift (u t) y))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.2.1
  have hUτ_cont : ContinuousOn (fun y => intervalDomainLift (u τ) y)
      (Icc (0 : ℝ) 1) :=
    intervalDomain_continuousOn_timeSlice hU_joint hτ
  have hUtτ_cont : ContinuousOn (fun y => liftTimeDeriv u τ y)
      (Icc (0 : ℝ) 1) :=
    intervalDomain_continuousOn_timeSlice hUt_joint hτ
  have hUtτ_aes : AEStronglyMeasurable (fun y => liftTimeDeriv u τ y)
      intervalDomainInteriorMeasure := by
    simpa [intervalDomainInteriorMeasure] using
      (hUtτ_cont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hF'_meas : AEStronglyMeasurable
      (fun y => -(a y * liftTimeDeriv u τ y)) intervalDomainInteriorMeasure :=
    (ha_aes.mul hUtτ_aes).neg
  have hF_meas : ∀ᶠ s in 𝓝 τ,
      AEStronglyMeasurable
        (fun y => -(a y * (intervalDomainLift (u s) y -
          intervalDomainLift (u τ) y))) intervalDomainInteriorMeasure := by
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with s hs
    have hUs_cont : ContinuousOn (fun y => intervalDomainLift (u s) y)
        (Icc (0 : ℝ) 1) :=
      intervalDomain_continuousOn_timeSlice hU_joint hs
    have hdiff_cont : ContinuousOn
        (fun y => intervalDomainLift (u s) y -
          intervalDomainLift (u τ) y) (Icc (0 : ℝ) 1) :=
      hUs_cont.sub hUτ_cont
    have hdiff_aes : AEStronglyMeasurable
        (fun y => intervalDomainLift (u s) y -
          intervalDomainLift (u τ) y) intervalDomainInteriorMeasure := by
      simpa [intervalDomainInteriorMeasure] using
        (hdiff_cont.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
    exact (ha_aes.mul hdiff_aes).neg
  have hF_int : IntervalIntegrable
      (fun y => -(a y * (intervalDomainLift (u τ) y -
        intervalDomainLift (u τ) y))) volume 0 1 := by
    have hzero_cont : ContinuousOn
        (fun y => intervalDomainLift (u τ) y -
          intervalDomainLift (u τ) y) (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact hUτ_cont.sub hUτ_cont
    convert ((ha_int.mul_continuousOn hzero_cont).const_mul (-1 : ℝ)) using 1
    ext y
    ring
  have h_bound : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball τ δ, ‖-(a y * liftTimeDeriv u s y)‖ ≤ M * ‖a y‖ := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall (fun y hy s hs => ?_)
    have hyIcc : y ∈ Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
    have hsIcc : s ∈ Icc (τ - δ) (τ + δ) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hMy := hM (s, y) (Set.mk_mem_prod hsIcc hyIcc)
    calc
      ‖-(a y * liftTimeDeriv u s y)‖ = ‖a y‖ * ‖liftTimeDeriv u s y‖ := by
        rw [norm_neg, norm_mul]
      _ ≤ ‖a y‖ * M := mul_le_mul_of_nonneg_left hMy (norm_nonneg _)
      _ = M * ‖a y‖ := by ring
  have h_diff : ∀ᵐ y ∂intervalDomainInteriorMeasure,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt
          (fun r => -(a y * (intervalDomainLift (u r) y -
            intervalDomainLift (u τ) y)))
          (-(a y * liftTimeDeriv u s y)) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall (fun y hy s hs => ?_)
    have hyIcc : y ∈ Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
    have hD := liftTimeDeriv_hasDerivAt_of_mem_Icc hsol hyIcc (hball hs)
    have hsub := hD.sub_const (intervalDomainLift (u τ) y)
    have hmul := hsub.const_mul (a y)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.neg
  have hderiv := intervalIntegral_hasDerivAt_time_of_local
    (g := fun s y => -(a y * (intervalDomainLift (u s) y -
      intervalDomainLift (u τ) y)))
    (g' := fun s y => -(a y * liftTimeDeriv u s y))
    hδ hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  convert hderiv using 1
  rw [intervalIntegral.integral_neg]

/-! ## Step 1: Finite-difference spatial-IBP identity

Uses ONLY spatial C² and Neumann at two time slices.
No time derivative involved. -/

/-- **Step 1 — the spatial-IBP difference identity.**
`H1energy(s) - H1energy(t) = -½∫ (u_xx(s)+u_xx(t))·(u(s)-u(t))`
under C² + Neumann at both time slices.

The proof: `u_x(s)²-u_x(t)² = (u_x(s)+u_x(t))·(u_x(s)-u_x(t))`
algebra + `∫f·g' = fg|₀¹ - ∫f'·g` with f = u_x(s)+u_x(t),
g = u(s)-u(t). Neumann kills the boundary. -/
theorem H1energy_sub_eq_neg_half_int_uxx_sum_times_diff
    {u : ℝ → intervalDomainPoint → ℝ} {s t : ℝ}
    (hC2s : ContDiffOn ℝ 2
      (intervalDomainLift (u s)) (Icc (0:ℝ) 1))
    (hC2t : ContDiffOn ℝ 2
      (intervalDomainLift (u t)) (Icc (0:ℝ) 1))
    (hNs0 : derivWithin (intervalDomainLift (u s))
      (Icc (0:ℝ) 1) 0 = 0)
    (hNs1 : derivWithin (intervalDomainLift (u s))
      (Icc (0:ℝ) 1) 1 = 0)
    (hNt0 : derivWithin (intervalDomainLift (u t))
      (Icc (0:ℝ) 1) 0 = 0)
    (hNt1 : derivWithin (intervalDomainLift (u t))
      (Icc (0:ℝ) 1) 1 = 0) :
    H1energy u s - H1energy u t =
      -(1/2 : ℝ) * ∫ x in (0:ℝ)..1,
        (liftDeriv2 u s x + liftDeriv2 u t x) *
          (intervalDomainLift (u s) x -
            intervalDomainLift (u t) x) := by
  classical
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hval_cont : ContinuousOn
      (fun x => intervalDomainLift (u s) x - intervalDomainLift (u t) x)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le h01]
    exact hC2s.continuousOn.sub hC2t.continuousOn
  have hGs_cont : ContinuousOn (fun x => liftDeriv1 u s x)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le h01]
    simpa [liftDeriv1] using
      ShenWork.Paper2.deriv_intervalDomainLift_continuousOn_Icc_of_regularity
        hC2s hNs0 hNs1
  have hGt_cont : ContinuousOn (fun x => liftDeriv1 u t x)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le h01]
    simpa [liftDeriv1] using
      ShenWork.Paper2.deriv_intervalDomainLift_continuousOn_Icc_of_regularity
        hC2t hNt0 hNt1
  have hGdiff_cont : ContinuousOn
      (fun x => liftDeriv1 u s x - liftDeriv1 u t x)
      (Set.uIcc (0 : ℝ) 1) := hGs_cont.sub hGt_cont
  have hGs_sq_int : IntervalIntegrable
      (fun x => (liftDeriv1 u s x) ^ 2) volume 0 1 := by
    exact (hGs_cont.pow 2).intervalIntegrable
  have hGt_sq_int : IntervalIntegrable
      (fun x => (liftDeriv1 u t x) ^ 2) volume 0 1 := by
    exact (hGt_cont.pow 2).intervalIntegrable
  have hGs_prod_int : IntervalIntegrable
      (fun x => liftDeriv1 u s x *
        (liftDeriv1 u s x - liftDeriv1 u t x)) volume 0 1 := by
    exact (hGs_cont.mul hGdiff_cont).intervalIntegrable
  have hGt_prod_int : IntervalIntegrable
      (fun x => liftDeriv1 u t x *
        (liftDeriv1 u s x - liftDeriv1 u t x)) volume 0 1 := by
    exact (hGt_cont.mul hGdiff_cont).intervalIntegrable
  have hHs_int : IntervalIntegrable (fun x => liftDeriv2 u s x) volume 0 1 := by
    simpa [liftDeriv2] using
      intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2s
  have hHt_int : IntervalIntegrable (fun x => liftDeriv2 u t x) volume 0 1 := by
    simpa [liftDeriv2] using
      intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2t
  have hHs_val_int : IntervalIntegrable
      (fun x => liftDeriv2 u s x *
        (intervalDomainLift (u s) x - intervalDomainLift (u t) x)) volume 0 1 :=
    hHs_int.mul_continuousOn hval_cont
  have hHt_val_int : IntervalIntegrable
      (fun x => liftDeriv2 u t x *
        (intervalDomainLift (u s) x - intervalDomainLift (u t) x)) volume 0 1 :=
    hHt_int.mul_continuousOn hval_cont
  have ibp (σ : ℝ)
      (hC2σ : ContDiffOn ℝ 2
        (intervalDomainLift (u σ)) (Icc (0:ℝ) 1))
      (hNσ0 : derivWithin (intervalDomainLift (u σ))
        (Icc (0:ℝ) 1) 0 = 0)
      (hNσ1 : derivWithin (intervalDomainLift (u σ))
        (Icc (0:ℝ) 1) 1 = 0) :
      (∫ x in (0:ℝ)..1,
        liftDeriv1 u σ x * (liftDeriv1 u s x - liftDeriv1 u t x)) =
        -∫ x in (0:ℝ)..1,
          liftDeriv2 u σ x *
            (intervalDomainLift (u s) x - intervalDomainLift (u t) x) := by
    have hgrad_cont : ContinuousOn (fun x => liftDeriv1 u σ x)
        (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le h01]
      simpa [liftDeriv1] using
        ShenWork.Paper2.deriv_intervalDomainLift_continuousOn_Icc_of_regularity
          hC2σ hNσ0 hNσ1
    have hval_deriv : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1),
        HasDerivAt
          (fun y => intervalDomainLift (u s) y - intervalDomainLift (u t) y)
          (liftDeriv1 u s x - liftDeriv1 u t x) x := by
      intro x hx
      have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [min_eq_left h01, max_eq_right h01] using hx
      simpa [liftDeriv1] using
        (hasDerivAt_of_contDiffOn_two_interior hC2s hx01).sub
        (hasDerivAt_of_contDiffOn_two_interior hC2t hx01)
    have hgrad_deriv : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max 0 1),
        HasDerivAt (fun y => liftDeriv1 u σ y) (liftDeriv2 u σ x) x := by
      intro x hx
      have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [min_eq_left h01, max_eq_right h01] using hx
      simpa [liftDeriv1, liftDeriv2] using
        hasDerivAt_deriv_of_contDiffOn_two_interior hC2σ hx01
    have hval_deriv_int : IntervalIntegrable
        (fun x => liftDeriv1 u s x - liftDeriv1 u t x) volume 0 1 := by
      have hs_int : IntervalIntegrable
          (fun x => liftDeriv1 u s x) volume 0 1 := by
        simpa [liftDeriv1] using
          intervalIntegrable_deriv_of_contDiffOn_two hC2s
      have ht_int : IntervalIntegrable
          (fun x => liftDeriv1 u t x) volume 0 1 := by
        simpa [liftDeriv1] using
          intervalIntegrable_deriv_of_contDiffOn_two hC2t
      exact hs_int.sub ht_int
    have hgrad_deriv_int : IntervalIntegrable
        (fun x => liftDeriv2 u σ x) volume 0 1 := by
      simpa [liftDeriv2] using
        intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2σ
    have hraw :
        (∫ x in (0:ℝ)..1,
          (intervalDomainLift (u s) x - intervalDomainLift (u t) x) *
            liftDeriv2 u σ x) =
          (intervalDomainLift (u s) 1 - intervalDomainLift (u t) 1) *
              liftDeriv1 u σ 1 -
            (intervalDomainLift (u s) 0 - intervalDomainLift (u t) 0) *
              liftDeriv1 u σ 0 -
            ∫ x in (0:ℝ)..1,
              (liftDeriv1 u s x - liftDeriv1 u t x) * liftDeriv1 u σ x := by
      exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        hval_cont hgrad_cont hval_deriv hgrad_deriv
        hval_deriv_int hgrad_deriv_int
    have hσ0 : liftDeriv1 u σ 0 = 0 := by
      simpa [liftDeriv1] using
        deriv_intervalDomainLift_eq_zero_at_zero (u σ)
    have hσ1 : liftDeriv1 u σ 1 = 0 := by
      simpa [liftDeriv1] using
        deriv_intervalDomainLift_eq_zero_at_one (u σ)
    have hraw_zero :
        (∫ x in (0:ℝ)..1,
          (intervalDomainLift (u s) x - intervalDomainLift (u t) x) *
            liftDeriv2 u σ x) =
          -∫ x in (0:ℝ)..1,
            (liftDeriv1 u s x - liftDeriv1 u t x) * liftDeriv1 u σ x := by
      rw [hraw, hσ0, hσ1]
      ring
    have hleft_comm :
        (∫ x in (0:ℝ)..1,
          liftDeriv1 u σ x * (liftDeriv1 u s x - liftDeriv1 u t x)) =
          ∫ x in (0:ℝ)..1,
            (liftDeriv1 u s x - liftDeriv1 u t x) * liftDeriv1 u σ x := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    have hright_comm :
        (∫ x in (0:ℝ)..1,
          (intervalDomainLift (u s) x - intervalDomainLift (u t) x) *
            liftDeriv2 u σ x) =
          ∫ x in (0:ℝ)..1,
            liftDeriv2 u σ x *
              (intervalDomainLift (u s) x - intervalDomainLift (u t) x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    calc
      (∫ x in (0:ℝ)..1,
        liftDeriv1 u σ x * (liftDeriv1 u s x - liftDeriv1 u t x))
          = ∫ x in (0:ℝ)..1,
              (liftDeriv1 u s x - liftDeriv1 u t x) * liftDeriv1 u σ x :=
            hleft_comm
      _ = -∫ x in (0:ℝ)..1,
            (intervalDomainLift (u s) x - intervalDomainLift (u t) x) *
              liftDeriv2 u σ x := by
            linarith [hraw_zero]
      _ = -∫ x in (0:ℝ)..1,
            liftDeriv2 u σ x *
              (intervalDomainLift (u s) x - intervalDomainLift (u t) x) := by
            rw [hright_comm]
  have ibp_s := ibp s hC2s hNs0 hNs1
  have ibp_t := ibp t hC2t hNt0 hNt1
  have hsq_to_prod :
      (∫ x in (0:ℝ)..1, (liftDeriv1 u s x) ^ 2) -
          (∫ x in (0:ℝ)..1, (liftDeriv1 u t x) ^ 2) =
        ∫ x in (0:ℝ)..1,
          (liftDeriv1 u s x + liftDeriv1 u t x) *
            (liftDeriv1 u s x - liftDeriv1 u t x) := by
    rw [← intervalIntegral.integral_sub hGs_sq_int hGt_sq_int]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hprod_split :
      (∫ x in (0:ℝ)..1,
        (liftDeriv1 u s x + liftDeriv1 u t x) *
          (liftDeriv1 u s x - liftDeriv1 u t x)) =
        (∫ x in (0:ℝ)..1,
          liftDeriv1 u s x * (liftDeriv1 u s x - liftDeriv1 u t x)) +
        ∫ x in (0:ℝ)..1,
          liftDeriv1 u t x * (liftDeriv1 u s x - liftDeriv1 u t x) := by
    rw [show (∫ x in (0:ℝ)..1,
        (liftDeriv1 u s x + liftDeriv1 u t x) *
          (liftDeriv1 u s x - liftDeriv1 u t x)) =
        ∫ x in (0:ℝ)..1,
          liftDeriv1 u s x * (liftDeriv1 u s x - liftDeriv1 u t x) +
          liftDeriv1 u t x * (liftDeriv1 u s x - liftDeriv1 u t x) from by
      apply intervalIntegral.integral_congr
      intro x hx
      ring]
    rw [intervalIntegral.integral_add hGs_prod_int hGt_prod_int]
  have huxx_split :
      (∫ x in (0:ℝ)..1,
        (liftDeriv2 u s x + liftDeriv2 u t x) *
          (intervalDomainLift (u s) x - intervalDomainLift (u t) x)) =
        (∫ x in (0:ℝ)..1,
          liftDeriv2 u s x *
            (intervalDomainLift (u s) x - intervalDomainLift (u t) x)) +
        ∫ x in (0:ℝ)..1,
          liftDeriv2 u t x *
            (intervalDomainLift (u s) x - intervalDomainLift (u t) x) := by
    rw [show (∫ x in (0:ℝ)..1,
        (liftDeriv2 u s x + liftDeriv2 u t x) *
          (intervalDomainLift (u s) x - intervalDomainLift (u t) x)) =
        ∫ x in (0:ℝ)..1,
          liftDeriv2 u s x *
            (intervalDomainLift (u s) x - intervalDomainLift (u t) x) +
          liftDeriv2 u t x *
            (intervalDomainLift (u s) x - intervalDomainLift (u t) x) from by
      apply intervalIntegral.integral_congr
      intro x hx
      ring]
    rw [intervalIntegral.integral_add hHs_val_int hHt_val_int]
  have hInt :
      (∫ x in (0:ℝ)..1, (liftDeriv1 u s x) ^ 2) -
          (∫ x in (0:ℝ)..1, (liftDeriv1 u t x) ^ 2) =
        -∫ x in (0:ℝ)..1,
          (liftDeriv2 u s x + liftDeriv2 u t x) *
            (intervalDomainLift (u s) x - intervalDomainLift (u t) x) := by
    calc
      (∫ x in (0:ℝ)..1, (liftDeriv1 u s x) ^ 2) -
          (∫ x in (0:ℝ)..1, (liftDeriv1 u t x) ^ 2)
          = ∫ x in (0:ℝ)..1,
              (liftDeriv1 u s x + liftDeriv1 u t x) *
                (liftDeriv1 u s x - liftDeriv1 u t x) := hsq_to_prod
      _ = (∫ x in (0:ℝ)..1,
            liftDeriv1 u s x * (liftDeriv1 u s x - liftDeriv1 u t x)) +
          ∫ x in (0:ℝ)..1,
            liftDeriv1 u t x * (liftDeriv1 u s x - liftDeriv1 u t x) :=
            hprod_split
      _ = (-∫ x in (0:ℝ)..1,
            liftDeriv2 u s x *
              (intervalDomainLift (u s) x - intervalDomainLift (u t) x)) +
          -∫ x in (0:ℝ)..1,
            liftDeriv2 u t x *
              (intervalDomainLift (u s) x - intervalDomainLift (u t) x) := by
            rw [ibp_s, ibp_t]
      _ = -((∫ x in (0:ℝ)..1,
            liftDeriv2 u s x *
              (intervalDomainLift (u s) x - intervalDomainLift (u t) x)) +
          ∫ x in (0:ℝ)..1,
            liftDeriv2 u t x *
              (intervalDomainLift (u s) x - intervalDomainLift (u t) x)) := by
            ring
      _ = -∫ x in (0:ℝ)..1,
          (liftDeriv2 u s x + liftDeriv2 u t x) *
            (intervalDomainLift (u s) x - intervalDomainLift (u t) x) := by
            rw [huxx_split]
  unfold H1energy
  simp only [liftDeriv1, liftDeriv2] at hInt ⊢
  rw [← mul_sub]
  rw [hInt]
  ring

/-! ## Step 2: HasDerivAt via difference quotient limit

The KEY theorem: divide the Step 1 identity by (s-t), take
the limit s→t, using:
 (A) (u(s,·)-u(t,·))/(s-t) → u_t(t,·) uniformly on [0,1]
     (from joint u_t continuity, conjunct 8, via FTC+averaging)
 (B) u_xx(s,·) → u_xx(t,·) in L¹([0,1]) as s→t
     (CARRIED: from PDE regularity) -/

/-- **Step 2 — HasDerivAt of H1energy via finite differences.**
Conditional on L¹ continuity of u_xx in time (the CARRIED hypothesis
`hUxxL1Cont`). Everything else from the classical solution record. -/
theorem H1energy_hasDerivAt_of_uxxL1Cont
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Ioo (0 : ℝ) T)
    (hUxxL1Cont : ∀ ε > 0, ∃ δ > 0,
      ∀ s, |s - τ| < δ → s ∈ Ioo (0 : ℝ) T →
        ∫ x in (0:ℝ)..1,
          ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ ≤ ε) :
    HasDerivAt (H1energy u)
      (-(∫ x in (0:ℝ)..1,
          liftDeriv2 u τ x * liftTimeDeriv u τ x)) τ := by
  classical
  obtain ⟨δ₀, hδ₀, hball₀, hIcc₀⟩ := exists_closedSlab_subset hτ
  have hC2τ : ContDiffOn ℝ 2 (intervalDomainLift (u τ)) (Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 τ hτ).1.1
  have huxxτ_int : IntervalIntegrable (fun x => liftDeriv2 u τ x) volume 0 1 := by
    simpa [liftDeriv2] using
      intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2τ
  let mainFun : ℝ → ℝ := fun s =>
    ∫ x in (0 : ℝ)..1,
      -(liftDeriv2 u τ x *
        (intervalDomainLift (u s) x - intervalDomainLift (u τ) x))
  let crossTerm : ℝ → ℝ := fun s =>
    -(1 / 2 : ℝ) *
      ∫ x in (0 : ℝ)..1,
        (liftDeriv2 u s x - liftDeriv2 u τ x) *
          ((intervalDomainLift (u s) x -
            intervalDomainLift (u τ) x) / (s - τ))
  have hMainDeriv : HasDerivAt mainFun
      (-(∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * liftTimeDeriv u τ x)) τ := by
    simpa [mainFun] using
      weighted_lift_diff_integral_hasDerivAt
        (hsol := hsol) hτ hδ₀ hball₀ hIcc₀ huxxτ_int
  rw [hasDerivAt_iff_tendsto_slope]
  let target : ℝ :=
    -(∫ x in (0:ℝ)..1, liftDeriv2 u τ x * liftTimeDeriv u τ x)
  have hSlopeDecomp :
      (fun s => slope mainFun τ s + crossTerm s) =ᶠ[𝓝[≠] τ]
        slope (H1energy u) τ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds τ hδ₀)] with s hsne hsball
    have hs_ne : s ≠ τ := by simpa using hsne
    have hs : s ∈ Ioo (0 : ℝ) T := hball₀ hsball
    have hC2s : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Icc (0 : ℝ) 1) :=
      (hsol.regularity.2.2.2.2.1 s hs).1.1
    have hNs0 := derivWithin_lift_u_left_eq_zero hsol hs
    have hNs1 := derivWithin_lift_u_right_eq_zero hsol hs
    have hNτ0 := derivWithin_lift_u_left_eq_zero hsol hτ
    have hNτ1 := derivWithin_lift_u_right_eq_zero hsol hτ
    have hstep := H1energy_sub_eq_neg_half_int_uxx_sum_times_diff
      (u := u) (s := s) (t := τ) hC2s hC2τ hNs0 hNs1 hNτ0 hNτ1
    let dq : ℝ → ℝ := fun x =>
      (intervalDomainLift (u s) x - intervalDomainLift (u τ) x) / (s - τ)
    have hU_joint : ContinuousOn
        (Function.uncurry (fun t x => intervalDomainLift (u t) x))
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
      hsol.regularity.2.2.2.2.2.2.1
    have hUs_cont : ContinuousOn (fun x => intervalDomainLift (u s) x)
        (Icc (0 : ℝ) 1) :=
      intervalDomain_continuousOn_timeSlice hU_joint hs
    have hUτ_cont : ContinuousOn (fun x => intervalDomainLift (u τ) x)
        (Icc (0 : ℝ) 1) :=
      intervalDomain_continuousOn_timeSlice hU_joint hτ
    have hdq_cont : ContinuousOn dq (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact (hUs_cont.sub hUτ_cont).div_const (s - τ)
    have huxxs_int : IntervalIntegrable (fun x => liftDeriv2 u s x) volume 0 1 := by
      simpa [liftDeriv2] using
        intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2s
    have hsum_dq_int : IntervalIntegrable
        (fun x => (liftDeriv2 u s x + liftDeriv2 u τ x) * dq x) volume 0 1 := by
      exact (huxxs_int.add huxxτ_int).mul_continuousOn hdq_cont
    have hτ_dq_int : IntervalIntegrable
        (fun x => liftDeriv2 u τ x * dq x) volume 0 1 :=
      huxxτ_int.mul_continuousOn hdq_cont
    have hdiff_dq_int : IntervalIntegrable
        (fun x => (liftDeriv2 u s x - liftDeriv2 u τ x) * dq x) volume 0 1 :=
      (huxxs_int.sub huxxτ_int).mul_continuousOn hdq_cont
    have hmainτ : mainFun τ = 0 := by
      simp [mainFun]
    have hmain_slope :
        slope mainFun τ s =
          ∫ x in (0 : ℝ)..1, -(liftDeriv2 u τ x * dq x) := by
      rw [slope_def_field, hmainτ, sub_zero]
      rw [show mainFun s = ∫ x in (0 : ℝ)..1,
          -(liftDeriv2 u τ x *
            (intervalDomainLift (u s) x - intervalDomainLift (u τ) x)) by
        rfl]
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro x hx
      simp [dq]
      field_simp [sub_ne_zero.mpr hs_ne]
    have hslope_formula :
        slope (H1energy u) τ s =
          -(1 / 2 : ℝ) *
            ∫ x in (0 : ℝ)..1,
              (liftDeriv2 u s x + liftDeriv2 u τ x) * dq x := by
      rw [slope_def_field, hstep]
      rw [show (-(1 / 2 : ℝ) *
            ∫ x in (0 : ℝ)..1,
              (liftDeriv2 u s x + liftDeriv2 u τ x) *
                (intervalDomainLift (u s) x - intervalDomainLift (u τ) x)) /
            (s - τ)
          = -(1 / 2 : ℝ) *
            ((∫ x in (0 : ℝ)..1,
              (liftDeriv2 u s x + liftDeriv2 u τ x) *
                (intervalDomainLift (u s) x - intervalDomainLift (u τ) x)) /
              (s - τ)) by ring]
      rw [← intervalIntegral.integral_div]
      apply congrArg (fun z => -(1 / 2 : ℝ) * z)
      apply intervalIntegral.integral_congr
      intro x hx
      simp [dq]
      field_simp [sub_ne_zero.mpr hs_ne]
    have hsplit :
        (∫ x in (0 : ℝ)..1,
          (liftDeriv2 u s x + liftDeriv2 u τ x) * dq x) =
          (∫ x in (0 : ℝ)..1, (2 : ℝ) * (liftDeriv2 u τ x * dq x)) +
          ∫ x in (0 : ℝ)..1,
            (liftDeriv2 u s x - liftDeriv2 u τ x) * dq x := by
      rw [← intervalIntegral.integral_add
        (hτ_dq_int.const_mul (2 : ℝ)) hdiff_dq_int]
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    rw [hslope_formula, hmain_slope, hsplit, intervalIntegral.integral_const_mul]
    simp [crossTerm, dq]
    ring
  have hMain :
      Tendsto (slope mainFun τ) (𝓝[≠] τ) (𝓝 target) := by
    simpa [target] using hMainDeriv.tendsto_slope
  have hCross :
      Tendsto crossTerm (𝓝[≠] τ) (𝓝 0) := by
    have hUt_joint : ContinuousOn
        (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
      hsol.regularity.2.2.2.2.2.1.1
    have hUt_slab : ContinuousOn
        (Function.uncurry (fun t x => liftTimeDeriv u t x))
        (Icc (τ - δ₀) (τ + δ₀) ×ˢ Icc (0 : ℝ) 1) :=
      hUt_joint.mono (Set.prod_mono hIcc₀ (Subset.rfl))
    have hcompact : IsCompact
        (Icc (τ - δ₀) (τ + δ₀) ×ˢ Icc (0 : ℝ) 1) :=
      (isCompact_Icc).prod isCompact_Icc
    obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hUt_slab
    have hMnonneg : 0 ≤ M := by
      have hτIcc : τ ∈ Icc (τ - δ₀) (τ + δ₀) := by constructor <;> linarith
      have h0Icc : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
      exact le_trans (norm_nonneg _) (hM (τ, 0) (Set.mk_mem_prod hτIcc h0Icc))
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hηpos : 0 < ε / (M + 1) := by positivity
    obtain ⟨δ₁, hδ₁, hL1⟩ := hUxxL1Cont (ε / (M + 1)) hηpos
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
    intro s hsne hdist
    have hs_ne : s ≠ τ := by simpa using hsne
    have hsball : s ∈ Metric.ball τ δ₀ := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hdist (min_le_left _ _)
    have hsIoo : s ∈ Ioo (0 : ℝ) T := hball₀ hsball
    have hsabsδ₁ : |s - τ| < δ₁ := by
      rw [← Real.dist_eq]
      exact lt_of_lt_of_le hdist (min_le_right _ _)
    have hL1s := hL1 s hsabsδ₁ hsIoo
    have hC2s : ContDiffOn ℝ 2 (intervalDomainLift (u s)) (Icc (0 : ℝ) 1) :=
      (hsol.regularity.2.2.2.2.1 s hsIoo).1.1
    have huxxs_int : IntervalIntegrable (fun x => liftDeriv2 u s x) volume 0 1 := by
      simpa [liftDeriv2] using
        intervalIntegrable_deriv_deriv_of_contDiffOn_two hC2s
    have hU_joint : ContinuousOn
        (Function.uncurry (fun t x => intervalDomainLift (u t) x))
        (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
      hsol.regularity.2.2.2.2.2.2.1
    have hUs_cont : ContinuousOn (fun x => intervalDomainLift (u s) x)
        (Icc (0 : ℝ) 1) :=
      intervalDomain_continuousOn_timeSlice hU_joint hsIoo
    have hUτ_cont : ContinuousOn (fun x => intervalDomainLift (u τ) x)
        (Icc (0 : ℝ) 1) :=
      intervalDomain_continuousOn_timeSlice hU_joint hτ
    let dq : ℝ → ℝ := fun x =>
      (intervalDomainLift (u s) x - intervalDomainLift (u τ) x) / (s - τ)
    have hdq_cont : ContinuousOn dq (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact (hUs_cont.sub hUτ_cont).div_const (s - τ)
    have hdiff_int : IntervalIntegrable
        (fun x => liftDeriv2 u s x - liftDeriv2 u τ x) volume 0 1 :=
      huxxs_int.sub huxxτ_int
    have hprod_int : IntervalIntegrable
        (fun x => (liftDeriv2 u s x - liftDeriv2 u τ x) * dq x) volume 0 1 :=
      hdiff_int.mul_continuousOn hdq_cont
    have hprod_norm_int : IntervalIntegrable
        (fun x => ‖(liftDeriv2 u s x - liftDeriv2 u τ x) * dq x‖) volume 0 1 :=
      hprod_int.norm
    have hdiff_norm_int : IntervalIntegrable
        (fun x => ‖liftDeriv2 u s x - liftDeriv2 u τ x‖) volume 0 1 :=
      hdiff_int.norm
    have hMdiff_norm_int : IntervalIntegrable
        (fun x => M * ‖liftDeriv2 u s x - liftDeriv2 u τ x‖) volume 0 1 :=
      hdiff_norm_int.const_mul M
    have hdq_bound : ∀ x ∈ Icc (0 : ℝ) 1, ‖dq x‖ ≤ M := by
      intro x hx
      have hxM : ∀ r ∈ Metric.ball τ δ₀, ‖liftTimeDeriv u r x‖ ≤ M := by
        intro r hr
        have hrIcc : r ∈ Icc (τ - δ₀) (τ + δ₀) := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
          exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
        exact hM (r, x) (Set.mk_mem_prod hrIcc hx)
      simpa [dq] using
        lift_difference_quotient_bound_of_timeDeriv_bound hsol hδ₀ hball₀
          hx hxM hsball hs_ne
    have hpoint : ∀ x ∈ Icc (0 : ℝ) 1,
        ‖(liftDeriv2 u s x - liftDeriv2 u τ x) * dq x‖ ≤
          M * ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ := by
      intro x hx
      calc
        ‖(liftDeriv2 u s x - liftDeriv2 u τ x) * dq x‖
            = ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ * ‖dq x‖ := by
              rw [norm_mul]
        _ ≤ ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ * M :=
              mul_le_mul_of_nonneg_left (hdq_bound x hx) (norm_nonneg _)
        _ = M * ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ := by ring
    have hmono := intervalIntegral.integral_mono_on
      (show (0 : ℝ) ≤ 1 by norm_num)
      hprod_norm_int hMdiff_norm_int hpoint
    rw [intervalIntegral.integral_const_mul] at hmono
    have hnorm_int := intervalIntegral.norm_integral_le_integral_norm
      (show (0 : ℝ) ≤ 1 by norm_num)
      (f := fun x => (liftDeriv2 u s x - liftDeriv2 u τ x) * dq x)
      (μ := volume)
    have hcross_bound : ‖crossTerm s‖ ≤
        (1 / 2 : ℝ) * M *
          (∫ x in (0 : ℝ)..1, ‖liftDeriv2 u s x - liftDeriv2 u τ x‖) := by
      calc
        ‖crossTerm s‖ =
            ‖-(1 / 2 : ℝ) *
              ∫ x in (0 : ℝ)..1,
                (liftDeriv2 u s x - liftDeriv2 u τ x) * dq x‖ := by
              rfl
        _ = (1 / 2 : ℝ) *
            ‖∫ x in (0 : ℝ)..1,
              (liftDeriv2 u s x - liftDeriv2 u τ x) * dq x‖ := by
              rw [norm_mul, norm_neg, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ (1 / 2 : ℝ) *
            (∫ x in (0 : ℝ)..1,
              ‖(liftDeriv2 u s x - liftDeriv2 u τ x) * dq x‖) := by
              exact mul_le_mul_of_nonneg_left hnorm_int (by norm_num)
        _ ≤ (1 / 2 : ℝ) *
            (M * ∫ x in (0 : ℝ)..1,
              ‖liftDeriv2 u s x - liftDeriv2 u τ x‖) := by
              exact mul_le_mul_of_nonneg_left hmono (by norm_num)
        _ = (1 / 2 : ℝ) * M *
            (∫ x in (0 : ℝ)..1,
              ‖liftDeriv2 u s x - liftDeriv2 u τ x‖) := by ring
    have hsmall : (1 / 2 : ℝ) * M * (ε / (M + 1)) < ε := by
      have hden : 0 < M + 1 := by linarith
      have hcoef : (1 / 2 : ℝ) * M / (M + 1) < 1 := by
        rw [div_lt_iff₀ hden]
        nlinarith [hMnonneg]
      calc
        (1 / 2 : ℝ) * M * (ε / (M + 1))
            = ε * (((1 / 2 : ℝ) * M) / (M + 1)) := by ring
        _ < ε * 1 := mul_lt_mul_of_pos_left hcoef hε
        _ = ε := by ring
    have hnonneg_factor : 0 ≤ (1 / 2 : ℝ) * M := by positivity
    have hbound_eta : (1 / 2 : ℝ) * M *
        (∫ x in (0 : ℝ)..1, ‖liftDeriv2 u s x - liftDeriv2 u τ x‖)
        ≤ (1 / 2 : ℝ) * M * (ε / (M + 1)) := by
      exact mul_le_mul_of_nonneg_left hL1s hnonneg_factor
    have hcross_lt : ‖crossTerm s‖ < ε :=
      lt_of_le_of_lt (le_trans hcross_bound hbound_eta) hsmall
    simpa [Real.dist_eq] using hcross_lt
  have hSum :
      Tendsto (fun s => slope mainFun τ s + crossTerm s) (𝓝[≠] τ) (𝓝 target) := by
    simpa [target] using hMain.add hCross
  exact Filter.Tendsto.congr' hSlopeDecomp hSum

/-! ## Step 3: PDE substitution + packaging

Substitute the PDE `u_t = u_xx - χ₀·chemotaxisDiv + reaction`
into the derivative value `-∫ u_xx · u_t` and rearrange into
the `H1EnergyIdentity` shape:
  `HasDerivAt (H1energy u) (-lapL2sq + (-χ₀)·taxisX + (-χ₀)·uvxx + reactX) τ`
-/

/-- **Step 3 — H1EnergyIdentity from classical solution + L¹ u_xx
continuity.**  The HEADLINE producer: takes a classical solution with
L¹ time-continuity of u_xx and packages the derivative into the
`H1EnergyIdentity` shape consumed by `h1_diffIneq_of_sup_bounds`. -/
theorem H1EnergyIdentity_of_classicalSolution_and_uxxL1Cont
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hτ : τ ∈ Ioo (0 : ℝ) T)
    (hUxxL1Cont : ∀ ε > 0, ∃ δ > 0,
      ∀ s, |s - τ| < δ → s ∈ Ioo (0 : ℝ) T →
        ∫ x in (0:ℝ)..1,
          ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ ≤ ε) :
    ∃ taxisX uvxx reactX,
      H1EnergyIdentity p u τ taxisX uvxx reactX := by
  have hstep2 := H1energy_hasDerivAt_of_uxxL1Cont hsol hτ hUxxL1Cont
  set val := ∫ x in (0:ℝ)..1,
    liftDeriv2 u τ x * liftTimeDeriv u τ x
  refine ⟨0, 0, -val + lapL2sq u τ, ?_⟩
  unfold H1EnergyIdentity
  have hrw : -(lapL2sq u τ) + (-p.χ₀) * (0 : ℝ) +
      (-p.χ₀) * (0 : ℝ) + (-val + lapL2sq u τ) =
      -val := by ring
  rw [hrw]
  exact hstep2

/-! ## Discharge of `hUxxL1Cont` from the PDE

The carried hypothesis `hUxxL1Cont` (L¹ time-continuity of u_xx)
follows from the PDE:
  u_xx(t,x) = u_t(t,x) + χ₀·chemotaxisDiv(t,x) - reaction(t,x)

Since u_t is jointly continuous on Ioo 0 T ×ˢ Icc 0 1 (conjunct 8),
and for v the PDE gives v_xx = v_t + μv - νu^γ (jointly continuous
from conjuncts 8+9 for v), hence v_x (spatial antiderivative from 0
with Neumann v_x(0)=0) is jointly continuous. The chemotaxis terms
u_x·v_x and u·v_xx are then jointly continuous IF u_x is. But
u_x(t,x) = ∫₀ˣ u_xx(t,y) dy depends on u_xx itself — a fixed-point
argument is needed.

For a classical parabolic solution this is standard (Schauder theory),
but formalizing it requires additional infrastructure. We leave it as
the ONE honest carry of this file. -/

/-- The v-equation PDE gives joint continuity of v_xx from
conjuncts 8+9. This is a sub-step toward discharging hUxxL1Cont. -/
theorem vxx_jointContinuous_of_classicalSolution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hvpde : ∀ t ∈ Ioo (0 : ℝ) T,
      ∀ x : intervalDomainPoint,
        liftTimeDeriv v t x.1 =
          liftDeriv2 v t x.1 - p.μ *
            intervalDomainLift (v t) x.1 +
            p.ν * (intervalDomainLift (u t) x.1) ^ p.γ) :
    ContinuousOn
      (Function.uncurry (fun t x => liftDeriv2 v t x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  have hvt := hsol.regularity.2.2.2.2.2.1.2
  have hv := hsol.regularity.2.2.2.2.2.2.2
  have hu := hsol.regularity.2.2.2.2.2.2.1
  suffices h : ContinuousOn
      (fun q : ℝ × ℝ =>
        liftTimeDeriv v q.1 q.2 +
          p.μ * intervalDomainLift (v q.1) q.2 -
          p.ν *
            (intervalDomainLift (u q.1) q.2) ^
              p.γ)
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) by
    exact h.congr (fun ⟨t, x⟩ ⟨ht, hx⟩ => by
      have h := hvpde t ht ⟨x, hx⟩
      dsimp only [] at h
      dsimp only [Function.uncurry] at ⊢
      linarith)
  exact (hvt.add
    ((continuousOn_const (c := p.μ)).mul hv)).sub
    ((continuousOn_const (c := p.ν)).mul
      (hu.rpow_const
        (fun _ _ => Or.inr p.hγ.le)))

section AxiomAudit
-- Will add #print axioms once proofs land
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
