import ShenWork.Paper2.IntervalDomainMSlowLpBound
import ShenWork.Paper2.IntervalChiNegH1EnergyDeriv
import ShenWork.Paper2.IntervalSourceBridgeOpen
import ShenWork.Paper2.IntervalBankChemSliceFix
import ShenWork.PDE.P3MoserGradientContinuityFromDx

/-!
# Classical restart for the faithful general-m interval equation

This file derives the cosine-mode evolution of an arbitrary positive classical
solution of `intervalDomainM`.  In particular, it uses the published flux
`u ^ m * vₓ / (1 + v) ^ β`; no theorem about the legacy linear-flux domain is
transported across this step.

The flux integration by parts is deliberately endpoint-safe.  It uses
continuity on the closed interval, differentiability only on `Ioo 0 1`, and
the genuine zero boundary values of the flux.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.IntervalConjugateCosineSeries
  (intervalSineInner)
open ShenWork.Paper2.IntervalSourceBridgeOpen
  (rawCosCoeff_deriv_eq_kpi_rawSinCoeff_open)
open ShenWork.Paper2.IntervalDivergenceModeIdentity
  (sineCoeffs sineCoeffs_zero sineCoeffs_pos)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_eq_factor_mul_integral cosineCoeffs_hasDerivAt_of_smooth_param)
/-- The lifted logistic source of the faithful equation. -/
def logisticLiftedM (p : CM2Params)
    (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  intervalDomainLift (fun x ↦ w x * (p.a - p.b * (w x) ^ p.α))

/-- The faithful B-form source coefficient: logistic source minus `χ₀` times
the divergence-mode coefficient of the general-`m` flux. -/
def sourceCoeffM (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (logisticLiftedM p (u s)) k -
    p.χ₀ * (((k : ℝ) * Real.pi) * intervalSineInner
      (intervalFluxM p (u s) (v s)) k)

/-- Cosine coefficient of one solution slice. -/
def solutionCoeffM
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (intervalDomainLift (u s)) k

/-- Endpoint-safe divergence-mode identity for the faithful flux.  No ambient
derivative is asserted at either endpoint. -/
theorem cosineCoeff_fluxM_deriv
    {p : CM2Params} {T s : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs0 : 0 < s) (hsT : s < T) (k : ℕ) :
    cosineCoeffs (deriv (intervalFluxM p (u s) (v s))) k =
      ((k : ℝ) * Real.pi) * intervalSineInner
        (intervalFluxM p (u s) (v s)) k := by
  have hQcont : ContinuousOn (intervalFluxM p (u s) (v s)) (Icc (0 : ℝ) 1) :=
    (fluxM_contDiffOn_Icc hsol hs0 hsT).continuousOn
  have hQderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (intervalFluxM p (u s) (v s))
        (deriv (intervalFluxM p (u s) (v s)) x) (Ioi x) x := by
    intro x hx
    have hdon : DifferentiableOn ℝ (intervalFluxM p (u s) (v s)) (Ioo 0 1) :=
      (fluxM_contDiffOn_Ioo hsol hs0 hsT).differentiableOn (by norm_num)
    have hd : DifferentiableAt ℝ (intervalFluxM p (u s) (v s)) x :=
      hdon.differentiableAt (isOpen_Ioo.mem_nhds hx)
    exact hd.hasDerivAt.hasDerivWithinAt
  have hQint : IntervalIntegrable
      (deriv (intervalFluxM p (u s) (v s))) volume 0 1 :=
    deriv_fluxM_intervalIntegrable hsol hs0 hsT
  obtain ⟨hQ0, hQ1⟩ := fluxM_endpoint_zero hsol hs0 hsT
  have hraw := rawCosCoeff_deriv_eq_kpi_rawSinCoeff_open k
    hQcont hQderiv hQint hQ0 hQ1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [cosineCoeffs_eq_factor_mul_integral]
    simp only [if_pos, Nat.cast_zero, zero_mul]
    simpa using hraw
  · have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [cosineCoeffs_eq_factor_mul_integral, if_neg hk0]
    rw [show intervalSineInner (intervalFluxM p (u s) (v s)) k =
        sineCoeffs (intervalFluxM p (u s) (v s)) k by rfl,
      sineCoeffs_pos hk0]
    have hcomm :
        (∫ x in (0 : ℝ)..1,
          Real.cos ((k : ℝ) * Real.pi * x) *
            deriv (intervalFluxM p (u s) (v s)) x) =
        ∫ x in (0 : ℝ)..1,
          deriv (intervalFluxM p (u s) (v s)) x *
            Real.cos ((k : ℝ) * Real.pi * x) := by
      refine intervalIntegral.integral_congr (fun x _ ↦ ?_)
      ring
    have hsincomm :
        (∫ x in (0 : ℝ)..1,
          intervalFluxM p (u s) (v s) x *
            Real.sin ((k : ℝ) * Real.pi * x)) =
        ∫ x in (0 : ℝ)..1,
          Real.sin ((k : ℝ) * Real.pi * x) *
            intervalFluxM p (u s) (v s) x := by
      refine intervalIntegral.integral_congr (fun x _ ↦ ?_)
      ring
    rw [hcomm, hraw, hsincomm]
    ring

/-- The time derivative of a solution cosine coefficient is the cosine
coefficient of the classical time-derivative field. -/
theorem solutionCoeffM_hasDerivAt
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (k : ℕ) :
    HasDerivAt (fun s ↦ solutionCoeffM u s k)
      (cosineCoeffs
        (fun x ↦ deriv (fun s : ℝ ↦ intervalDomainLift (u s) x) t) k) t := by
  let δ : ℝ := min t (T - t) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    have hm : 0 < min t (T - t) := lt_min ht0 (sub_pos.mpr htT)
    linarith
  let f : ℝ → ℝ → ℝ := fun s x ↦ intervalDomainLift (u s) x
  let f' : ℝ → ℝ → ℝ :=
    fun s x ↦ deriv (fun r : ℝ ↦ intervalDomainLift (u r) x) s
  have hball : Metric.ball t δ ⊆ Ioo (0 : ℝ) T := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hδt : δ ≤ t / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hδT : δ ≤ (T - t) / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    constructor <;> linarith [abs_lt.mp hs]
  have hf_int : ∀ᶠ s in nhds t,
      IntervalIntegrable (f s) volume (0 : ℝ) 1 := by
    filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
    have hsI := hball hs
    have hc : ContinuousOn (f s) (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact (hsol.regularity.2.2.2.2.1 s hsI).1.1.continuousOn
    exact hc.intervalIntegrable
  have hdiff : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball t δ,
      HasDerivAt (fun r ↦ f r x) (f' s x) s := by
    intro x hx s hs
    have hsI := hball hs
    let xp : intervalDomainPoint := ⟨x, Ioo_subset_Icc_self hx⟩
    have hd := (hsol.regularity.2.1 xp s hsI).1.1
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
    have hliftfun :
        (fun r : ℝ ↦ intervalDomainLift (u r) x) =
          fun r : ℝ ↦ u r xp := by
      funext r
      rw [intervalDomainLift, dif_pos hxIcc]
    have heq : (fun r : ℝ ↦ f r x) = fun r : ℝ ↦ u r xp := by
      simpa [f] using hliftfun
    have hf'eq : f' s x = deriv (fun r : ℝ ↦ u r xp) s := by
      dsimp [f']
      rw [hliftfun]
    rw [heq]
    simpa [hf'eq] using hd.hasDerivAt
  have hslab : Icc (t - δ) (t + δ) ×ˢ Icc (0 : ℝ) 1 ⊆
      Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1 := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have hδt : δ ≤ t / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hδT : δ ≤ (T - t) / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    constructor <;> linarith [hz.1.1, hz.1.2]
  have hcont : ContinuousOn (Function.uncurry f')
      (Icc (t - δ) (t + δ) ×ˢ Icc (0 : ℝ) 1) := by
    exact hsol.regularity.2.2.2.2.2.1.1.mono hslab
  simpa [solutionCoeffM, f, f'] using
    cosineCoeffs_hasDerivAt_of_smooth_param hδ hf_int hdiff hcont

/-- Linearity of the cosine coefficient under the minimal interval-integrable
hypotheses needed below.  This version is endpoint-insensitive. -/
theorem cosineCoeffs_sub_const_mul_add_of_intervalIntegrable
    {f g h : ℝ → ℝ} (c : ℝ) (k : ℕ)
    (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hh : IntervalIntegrable h volume 0 1) :
    cosineCoeffs (fun x ↦ f x - c * g x + h x) k =
      cosineCoeffs f k - c * cosineCoeffs g k + cosineCoeffs h k := by
  let w : ℝ → ℝ := fun x ↦ Real.cos ((k : ℝ) * Real.pi * x)
  have hw : ContinuousOn w (Set.uIcc (0 : ℝ) 1) := by
    exact (Real.continuous_cos.comp (by fun_prop)).continuousOn
  have hfw : IntervalIntegrable (fun x ↦ w x * f x) volume 0 1 :=
    hf.continuousOn_mul hw
  have hgw : IntervalIntegrable (fun x ↦ w x * g x) volume 0 1 :=
    hg.continuousOn_mul hw
  have hhw : IntervalIntegrable (fun x ↦ w x * h x) volume 0 1 :=
    hh.continuousOn_mul hw
  rw [cosineCoeffs_eq_factor_mul_integral,
    cosineCoeffs_eq_factor_mul_integral,
    cosineCoeffs_eq_factor_mul_integral,
    cosineCoeffs_eq_factor_mul_integral]
  have hsplit :
      (∫ x in (0 : ℝ)..1, w x * (f x - c * g x + h x)) =
        (∫ x in (0 : ℝ)..1, w x * f x) -
          c * (∫ x in (0 : ℝ)..1, w x * g x) +
            ∫ x in (0 : ℝ)..1, w x * h x := by
    calc
      (∫ x in (0 : ℝ)..1, w x * (f x - c * g x + h x)) =
          ∫ x in (0 : ℝ)..1,
            (w x * f x - c * (w x * g x)) + w x * h x := by
              refine intervalIntegral.integral_congr (fun x _ ↦ ?_)
              ring
      _ = (∫ x in (0 : ℝ)..1, w x * f x - c * (w x * g x)) +
          ∫ x in (0 : ℝ)..1, w x * h x := by
            rw [intervalIntegral.integral_add (hfw.sub (hgw.const_mul c)) hhw]
      _ = ((∫ x in (0 : ℝ)..1, w x * f x) -
            ∫ x in (0 : ℝ)..1, c * (w x * g x)) +
          ∫ x in (0 : ℝ)..1, w x * h x := by
            rw [intervalIntegral.integral_sub hfw (hgw.const_mul c)]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
  rw [hsplit]
  ring

/-- Per-mode diagonalized PDE for the faithful classical solution. -/
theorem solutionCoeffM_pde_mode
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (k : ℕ) :
    cosineCoeffs
        (fun x ↦ deriv (fun s : ℝ ↦ intervalDomainLift (u s) x) t) k =
      -(unitIntervalCosineEigenvalue k) * solutionCoeffM u t k +
        sourceCoeffM p u v t k := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let Q : ℝ → ℝ := intervalFluxM p (u t) (v t)
  let L : ℝ → ℝ := logisticLiftedM p (u t)
  let Ut : ℝ → ℝ :=
    fun x ↦ deriv (fun s : ℝ ↦ intervalDomainLift (u s) x) t
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hC2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
  have htend := (hsol.regularity.2.2.2.1 t ht).1
  have hbc := (hsol.regularity.2.2.2.2.1 t ht).1
  have hlapInt : IntervalIntegrable (deriv (deriv U)) volume 0 1 := by
    simpa [U] using
      ShenWork.IntervalEllipticCharacterization.intervalIntegrable_deriv_deriv_of_contDiffOn_two
        hC2
  have hQInt : IntervalIntegrable (deriv Q) volume 0 1 := by
    simpa [Q] using deriv_fluxM_intervalIntegrable hsol ht0 htT
  have hLcont : ContinuousOn L (Icc (0 : ℝ) 1) := by
    have hUcont : ContinuousOn U (Icc (0 : ℝ) 1) := by
      simpa [U] using solution_lift_continuousOn_Icc hsol ht
    have hUpow : ContinuousOn (fun x ↦ U x ^ p.α) (Icc (0 : ℝ) 1) :=
      hUcont.rpow_const (fun _ _ ↦ Or.inr p.hα.le)
    have hsrc : ContinuousOn
        (fun x ↦ U x * (p.a - p.b * U x ^ p.α)) (Icc (0 : ℝ) 1) :=
      hUcont.mul (continuousOn_const.sub (continuousOn_const.mul hUpow))
    refine hsrc.congr (fun x hx ↦ ?_)
    simp [L, logisticLiftedM, U, intervalDomainLift, hx]
  have hLInt : IntervalIntegrable L volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hLcont
  have hpde : ∀ x ∈ Ioo (0 : ℝ) 1,
      Ut x = deriv (deriv U) x - p.χ₀ * deriv Q x + L x := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
    let xp : intervalDomainPoint := ⟨x, hxIcc⟩
    have h := hsol.pde_u ht0 htT (x := xp) hx
    change deriv (fun s : ℝ ↦ u s xp) t =
      deriv (deriv (intervalDomainLift (u t))) x -
        p.χ₀ * deriv (intervalFluxM p (u t) (v t)) x +
          u t xp * (p.a - p.b * (u t xp) ^ p.α) at h
    have hliftTime :
        (fun s : ℝ ↦ intervalDomainLift (u s) x) =
          fun s : ℝ ↦ u s xp := by
      funext s
      rw [intervalDomainLift, dif_pos hxIcc]
    dsimp [Ut, U, Q, L]
    rw [hliftTime]
    simpa [logisticLiftedM, intervalDomainLift, hxIcc] using h
  have hcoeffPDE :
      cosineCoeffs Ut k = cosineCoeffs
        (fun x ↦ deriv (deriv U) x - p.χ₀ * deriv Q x + L x) k :=
    ShenWork.Paper2.BankChemSliceFix.cosineCoeffs_congr_on_Ioo hpde k
  have hsplit := cosineCoeffs_sub_const_mul_add_of_intervalIntegrable
    p.χ₀ k hlapInt hQInt hLInt
  have hlap : cosineCoeffs (deriv (deriv U)) k =
      -(unitIntervalCosineEigenvalue k) * solutionCoeffM u t k := by
    simpa [U, solutionCoeffM] using
      ShenWork.Paper2.IntervalChiNegH1EnergyDeriv.lapCoeff_eq_neg_lam_coeff
        (u := u) (τ := t) k hC2 htend.1 htend.2 hbc.2.1 hbc.2.2
  have hflux : cosineCoeffs (deriv Q) k =
      ((k : ℝ) * Real.pi) * intervalSineInner Q k := by
    simpa [Q] using cosineCoeff_fluxM_deriv hsol ht0 htT k
  rw [hcoeffPDE, hsplit, hlap, hflux]
  simp [sourceCoeffM, Q, L]
  ring

/-- The cosine coefficients of a faithful classical solution satisfy the scalar
variation-of-constants ODE on every positive-time window. -/
theorem solutionCoeffM_hasDerivAt_pde
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (k : ℕ) :
    HasDerivAt (fun s ↦ solutionCoeffM u s k)
      (-(unitIntervalCosineEigenvalue k) * solutionCoeffM u t k +
        sourceCoeffM p u v t k) t := by
  exact (solutionCoeffM_hasDerivAt hsol ht0 htT k).congr_deriv
    (solutionCoeffM_pde_mode hsol ht0 htT k)

/-- A solution cosine coefficient is continuous on every closed positive-time
window strictly inside the classical horizon. -/
theorem solutionCoeffM_continuousOn
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) (k : ℕ) :
    ContinuousOn (fun s ↦ solutionCoeffM u s k) (Icc a b) := by
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) T := fun s hs ↦
    ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have hjoint : ContinuousOn
      (Function.uncurry (fun s x ↦ intervalDomainLift (u s) x))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.2.1.mono
      (Set.prod_mono hsub (le_refl _))
  let F : ℝ → ℝ → ℝ := fun s x ↦
    Real.cos ((k : ℝ) * Real.pi * x) * intervalDomainLift (u s) x
  have hF : ContinuousOn (Function.uncurry F)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    have hcos : Continuous
        (fun z : ℝ × ℝ ↦ Real.cos ((k : ℝ) * Real.pi * z.2)) := by
      fun_prop
    exact hcos.continuousOn.mul hjoint
  have hint : ContinuousOn (fun s ↦ ∫ x in (0 : ℝ)..1, F s x) (Icc a b) :=
    ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability.continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod
      hF
  have hfactor : ContinuousOn
      (fun s ↦ (if k = 0 then 1 else 2) * ∫ x in (0 : ℝ)..1, F s x)
      (Icc a b) := continuousOn_const.mul hint
  simpa [solutionCoeffM, cosineCoeffs_eq_factor_mul_integral, F] using hfactor

/-- The cosine coefficient of the classical time-derivative field is continuous
on closed positive-time windows. -/
theorem timeDerivCoeffM_continuousOn
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) (k : ℕ) :
    ContinuousOn
      (fun s ↦ cosineCoeffs
        (fun x ↦ deriv (fun r : ℝ ↦ intervalDomainLift (u r) x) s) k)
      (Icc a b) := by
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) T := fun s hs ↦
    ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have hjoint : ContinuousOn
      (Function.uncurry
        (fun s x ↦ deriv (fun r : ℝ ↦ intervalDomainLift (u r) x) s))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hsol.regularity.2.2.2.2.2.1.1.mono
      (Set.prod_mono hsub (le_refl _))
  let F : ℝ → ℝ → ℝ := fun s x ↦
    Real.cos ((k : ℝ) * Real.pi * x) *
      deriv (fun r : ℝ ↦ intervalDomainLift (u r) x) s
  have hF : ContinuousOn (Function.uncurry F)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
    have hcos : Continuous
        (fun z : ℝ × ℝ ↦ Real.cos ((k : ℝ) * Real.pi * z.2)) := by
      fun_prop
    exact hcos.continuousOn.mul hjoint
  have hint : ContinuousOn (fun s ↦ ∫ x in (0 : ℝ)..1, F s x) (Icc a b) :=
    ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability.continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod
      hF
  have hfactor : ContinuousOn
      (fun s ↦ (if k = 0 then 1 else 2) * ∫ x in (0 : ℝ)..1, F s x)
      (Icc a b) := continuousOn_const.mul hint
  simpa [cosineCoeffs_eq_factor_mul_integral, F] using hfactor

/-- The faithful source coefficient is continuous on every closed positive-time
window. -/
theorem sourceCoeffM_continuousOn
    {p : CM2Params} {T a b : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (k : ℕ) :
    ContinuousOn (fun s ↦ sourceCoeffM p u v s k) (Icc a b) := by
  have hc := solutionCoeffM_continuousOn hsol ha hab hbT k
  have hct := timeDerivCoeffM_continuousOn hsol ha hab hbT k
  have hsum : ContinuousOn
      (fun s ↦ cosineCoeffs
          (fun x ↦ deriv (fun r : ℝ ↦ intervalDomainLift (u r) x) s) k +
        unitIntervalCosineEigenvalue k * solutionCoeffM u s k)
      (Icc a b) := hct.add (continuousOn_const.mul hc)
  refine hsum.congr (fun s hs ↦ ?_)
  have hmode := solutionCoeffM_pde_mode hsol
    (lt_of_lt_of_le ha hs.1) (lt_of_le_of_lt hs.2 hbT) k
  linarith

/-- Coefficient-level restart/variation-of-constants formula for an arbitrary
faithful classical solution. -/
theorem solutionCoeffM_restart
    {p : CM2Params} {T a t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hat : a ≤ t) (htT : t < T) (k : ℕ) :
    solutionCoeffM u t k =
      Real.exp (-(t - a) * unitIntervalCosineEigenvalue k) *
          solutionCoeffM u a k +
        ∫ s in a..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue k) *
            sourceCoeffM p u v s k := by
  let lam : ℝ := unitIntervalCosineEigenvalue k
  let c : ℝ → ℝ := fun s ↦ solutionCoeffM u s k
  let src : ℝ → ℝ := fun s ↦ sourceCoeffM p u v s k
  let G : ℝ → ℝ := fun s ↦ Real.exp (-(t - s) * lam) * c s
  have hccont : ContinuousOn c (Icc a t) := by
    simpa [c] using solutionCoeffM_continuousOn hsol ha hat htT k
  have hsrccont : ContinuousOn src (Icc a t) := by
    simpa [src] using sourceCoeffM_continuousOn hsol ha hat htT k
  have hGcont : ContinuousOn G (Icc a t) := by
    have hk : Continuous (fun s : ℝ ↦ Real.exp (-(t - s) * lam)) := by
      fun_prop
    exact hk.continuousOn.mul hccont
  have hderiv : ∀ s ∈ Ioo a t,
      HasDerivAt G (Real.exp (-(t - s) * lam) * src s) s := by
    intro s hs
    have hs0 : 0 < s := lt_trans ha hs.1
    have hsT : s < T := lt_trans hs.2 htT
    have hcder := solutionCoeffM_hasDerivAt_pde hsol hs0 hsT k
    have harg : HasDerivAt (fun r : ℝ ↦ -(t - r) * lam) lam s := by
      convert ((hasDerivAt_const s t).sub (hasDerivAt_id s)).neg.mul_const lam
        using 1 <;> ring_nf
    have hexp : HasDerivAt (fun r : ℝ ↦ Real.exp (-(t - r) * lam))
        (Real.exp (-(t - s) * lam) * lam) s := harg.exp
    have hprod := hexp.mul hcder
    convert hprod using 1
    dsimp [c, src, lam]
    ring
  have hint : IntervalIntegrable
      (fun s ↦ Real.exp (-(t - s) * lam) * src s) volume a t := by
    have hk : Continuous (fun s : ℝ ↦ Real.exp (-(t - s) * lam)) := by
      fun_prop
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hat]
    exact hk.continuousOn.mul hsrccont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hat hGcont hderiv hint
  dsimp [G, c, src, lam] at hFTC ⊢
  rw [hFTC]
  simp

end ShenWork.Paper2.IntervalDomainM

#print axioms ShenWork.Paper2.IntervalDomainM.cosineCoeff_fluxM_deriv
#print axioms ShenWork.Paper2.IntervalDomainM.solutionCoeffM_hasDerivAt_pde
#print axioms ShenWork.Paper2.IntervalDomainM.solutionCoeffM_restart
