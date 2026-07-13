import ShenWork.Paper2.IntervalDomainWeightedGradientEstimate
import ShenWork.Paper2.IntervalDomainLemma21

/-!
# Paper 2, Proposition 2.1 on the unit interval

This file proves the sharp Neumann elliptic-resolver contraction

`‖v(t)‖_q ≤ (ν / μ) ‖u(t)^γ‖_q`,  `1 ≤ q < ∞`,

directly from the classical elliptic equation.  The proof uses the already
established Neumann multiplier preestimate, sharp Hölder, and the integrated
elliptic equation at the endpoint `q = 1`.
-/

open MeasureTheory Set
open scoped ENNReal Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.Paper2.IntervalDomainLemma21

noncomputable section

namespace ShenWork.Paper2

/-- The concrete interval measure integral agrees with the oriented integral
on the unit interval. -/
lemma intervalMeasure_integral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ x, f x ∂ intervalMeasure 1) = ∫ x in (0 : ℝ)..1, f x := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- A continuous function on the compact unit interval belongs to every
finite real `L^q` space for the concrete interval measure. -/
lemma memLp_of_continuousOn_Icc
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (q : ℝ) :
    MemLp f (ENNReal.ofReal q) (intervalMeasure 1) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hfm : AEStronglyMeasurable f (intervalMeasure 1) := by
    unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
    exact hf.aestronglyMeasurable measurableSet_Icc
  refine MemLp.of_bound hfm C ?_
  unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

/-- For a positive continuous interval function, the concrete real `L^q`
seminorm is its usual integral power mean. -/
lemma intervalDomainLpNorm_eq_integral_rpow
    {q : ℝ} (hq : 0 < q) {f : intervalDomain.Point → ℝ}
    (hfcont : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    (hfpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift f x) :
    intervalDomainLpNorm q f =
      (∫ x in (0 : ℝ)..1, intervalDomainLift f x ^ q) ^ (1 / q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hqtop : ENNReal.ofReal q ≠ ⊤ := by simp
  have hfmeas : AEStronglyMeasurable (intervalDomainLift f) (intervalMeasure 1) := by
    unfold intervalMeasure ShenWork.IntervalDomain.intervalSet
    exact hfcont.aestronglyMeasurable measurableSet_Icc
  unfold intervalDomainLpNorm
  rw [lpNorm_eq_integral_norm_rpow_toReal hq0 hqtop hfmeas,
    ENNReal.toReal_ofReal hq.le, intervalMeasure_integral_eq_intervalIntegral]
  simp only [one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp
  rw [abs_of_pos (hfpos x (by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx))]

/-- The second derivative of the classical chemical slice has zero integral,
by the two Neumann endpoint conditions. -/
lemma intervalDomain_v_secondDeriv_integral_eq_zero
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    (∫ x in (0 : ℝ)..1,
      deriv (deriv (intervalDomainLift (v t))) x) = 0 := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using
      (resolverGradReal_contDiffOn_Icc hsol ht).continuousOn.congr
        (fun x hx => solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hx)
  have hV2deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv V) (deriv (deriv V) x) x := by
    intro x hx
    exact (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).2
  have hV2int : IntervalIntegrable (deriv (deriv V)) volume 0 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hV2
  have hNeu0 : deriv V 0 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.1
  have hNeu1 : deriv V 1 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.2
  have hmain :
      (∫ x in (0 : ℝ)..1, (1 : ℝ) * deriv (deriv V) x) =
        -∫ x in (0 : ℝ)..1, (0 : ℝ) * deriv V x :=
    intervalFluxByParts_open continuous_const.continuousOn
      (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hdVcont)
      (fun x _ => hasDerivAt_const x (1 : ℝ)) hV2deriv
      intervalIntegral.intervalIntegrable_const hV2int hNeu0 hNeu1
  simpa [V] using hmain

/-- The integrated elliptic equation, including the endpoint exponent
`q = 1` needed by Proposition 2.1. -/
lemma intervalDomain_chemical_mass_identity
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    p.μ * (∫ x in (0 : ℝ)..1, intervalDomainLift (v t) x) =
      p.ν * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ p.γ) := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos hsol ht x hx
  have hUint : IntervalIntegrable (fun x => U x ^ p.γ) volume 0 1 := by
    have hc : ContinuousOn (fun x => U x ^ p.γ) (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hUcont.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    exact hc.intervalIntegrable
  have hVint : IntervalIntegrable V volume 0 1 := by
    have hc : ContinuousOn V (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hVcont
    exact hc.intervalIntegrable
  have hPDE :
      (∫ x in (0 : ℝ)..1, deriv (deriv V) x) =
        ∫ x in (0 : ℝ)..1, p.μ * V x - p.ν * U x ^ p.γ := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
    refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    push Not at hx
    obtain ⟨hxIoc, hne⟩ := hx
    simp only [Set.mem_singleton_iff]
    by_contra hx1
    have hxoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx1⟩
    apply hne
    simpa [V, U] using
      intervalDomain_v_xx_eq_reaction_lift hsol ht0 htT hxoo.1 hxoo.2
  have hlap := intervalDomain_v_secondDeriv_integral_eq_zero hsol ht0 htT
  have hsplit :
      (∫ x in (0 : ℝ)..1, p.μ * V x - p.ν * U x ^ p.γ) =
        p.μ * (∫ x in (0 : ℝ)..1, V x) -
          p.ν * (∫ x in (0 : ℝ)..1, U x ^ p.γ) := by
    rw [intervalIntegral.integral_sub (hVint.const_mul p.μ)
        (hUint.const_mul p.ν),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hPDE, hsplit] at hlap
  dsimp [V, U] at hlap ⊢
  linarith

/-- Sharp Hölder estimate for the source term in the elliptic multiplier
identity. -/
lemma intervalDomain_elliptic_source_holder
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) (hq : 1 < q) :
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ p.γ *
          intervalDomainLift (v t) x ^ (q - 1)) ≤
      (∫ x in (0 : ℝ)..1, intervalDomainLift (v t) x ^ q) ^ ((q - 1) / q) *
        (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (p.γ * q)) ^ (1 / q) := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let r : ℝ := q / (q - 1)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hq1 : 0 < q - 1 := sub_pos.mpr hq
  have hr : 1 < r := by
    dsimp [r]
    rw [one_lt_div hq1]
    linarith
  have hconj : r.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hr, ?_⟩
    dsimp [r]
    field_simp [ne_of_gt hq1, ne_of_gt hqpos]
    ring
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos hsol ht x hx
  have hVrcont : ContinuousOn (fun x => V x ^ (q - 1)) (Set.Icc (0 : ℝ) 1) :=
    hVcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hVpos x hx)))
  have hUγcont : ContinuousOn (fun x => U x ^ p.γ) (Set.Icc (0 : ℝ) 1) :=
    hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hVrmem : MemLp (fun x => V x ^ (q - 1)) (ENNReal.ofReal r)
      (intervalMeasure 1) := memLp_of_continuousOn_Icc hVrcont r
  have hUγmem : MemLp (fun x => U x ^ p.γ) (ENNReal.ofReal q)
      (intervalMeasure 1) := memLp_of_continuousOn_Icc hUγcont q
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := intervalMeasure 1)
    (f := fun x => V x ^ (q - 1)) (g := fun x => U x ^ p.γ)
    hconj hVrmem hUγmem
  have hleft :
      (∫ x, ‖V x ^ (q - 1)‖ * ‖U x ^ p.γ‖ ∂intervalMeasure 1) =
        ∫ x in (0 : ℝ)..1, U x ^ p.γ * V x ^ (q - 1) := by
    rw [intervalMeasure_integral_eq_intervalIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    dsimp
    rw [abs_of_pos (Real.rpow_pos_of_pos (hVpos x hxIcc) _),
      abs_of_pos (Real.rpow_pos_of_pos (hUpos x hxIcc) _)]
    ring
  have hVpow :
      (∫ x, ‖V x ^ (q - 1)‖ ^ r ∂intervalMeasure 1) =
        ∫ x in (0 : ℝ)..1, V x ^ q := by
    rw [intervalMeasure_integral_eq_intervalIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    dsimp
    rw [abs_of_pos (Real.rpow_pos_of_pos (hVpos x hxIcc) _),
      ← Real.rpow_mul (hVpos x hxIcc).le]
    dsimp [r]
    congr 1
    field_simp [ne_of_gt hq1]
  have hUpow :
      (∫ x, ‖U x ^ p.γ‖ ^ q ∂intervalMeasure 1) =
        ∫ x in (0 : ℝ)..1, U x ^ (p.γ * q) := by
    rw [intervalMeasure_integral_eq_intervalIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    dsimp
    rw [abs_of_pos (Real.rpow_pos_of_pos (hUpos x hxIcc) _),
      ← Real.rpow_mul (hUpos x hxIcc).le]
  have hrinv : 1 / r = (q - 1) / q := by
    dsimp [r]
    field_simp [ne_of_gt hq1, ne_of_gt hqpos]
  rw [hleft, hVpow, hUpow, hrinv] at hholder
  simpa [V, U, mul_comm] using hholder

/-- Scalar cancellation behind the sharp elliptic `L^q` estimate. -/
lemma rpow_root_le_ratio_of_holder
    {mu nu q Iv Iu : ℝ} (hmu : 0 < mu) (hnu : 0 < nu) (hq : 1 < q)
    (hIv : 0 ≤ Iv) (hIu : 0 ≤ Iu)
    (hpre : mu * Iv ≤
      nu * (Iv ^ ((q - 1) / q) * Iu ^ (1 / q))) :
    Iv ^ (1 / q) ≤ (nu / mu) * Iu ^ (1 / q) := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  by_cases hIv0 : Iv = 0
  · subst Iv
    rw [Real.zero_rpow (one_div_pos.mpr hqpos).ne']
    exact mul_nonneg (div_pos hnu hmu).le (Real.rpow_nonneg hIu _)
  have hIvpos : 0 < Iv := lt_of_le_of_ne hIv (Ne.symm hIv0)
  have hBpos : 0 < Iv ^ ((q - 1) / q) :=
    Real.rpow_pos_of_pos hIvpos _
  have hpre' : mu * Iv ≤
      (nu * Iu ^ (1 / q)) * Iv ^ ((q - 1) / q) := by
    calc
      mu * Iv ≤ nu * (Iv ^ ((q - 1) / q) * Iu ^ (1 / q)) := hpre
      _ = (nu * Iu ^ (1 / q)) * Iv ^ ((q - 1) / q) := by ring
  have hdiv : mu * Iv / Iv ^ ((q - 1) / q) ≤ nu * Iu ^ (1 / q) :=
    (div_le_iff₀ hBpos).2 hpre'
  have hquot : Iv / Iv ^ ((q - 1) / q) = Iv ^ (1 / q) := by
    calc
      Iv / Iv ^ ((q - 1) / q) = Iv ^ (1 : ℝ) / Iv ^ ((q - 1) / q) := by
        rw [Real.rpow_one]
      _ = Iv ^ (1 - (q - 1) / q) :=
        (Real.rpow_sub hIvpos 1 ((q - 1) / q)).symm
      _ = Iv ^ (1 / q) := by
        congr 1
        field_simp [ne_of_gt hqpos]
        ring
  have hmu_root : mu * Iv ^ (1 / q) ≤ nu * Iu ^ (1 / q) := by
    rw [← hquot]
    simpa [mul_div_assoc] using hdiv
  rw [show (nu / mu) * Iu ^ (1 / q) =
      (nu * Iu ^ (1 / q)) / mu by ring]
  exact (le_div_iff₀ hmu).2 (by simpa [mul_comm] using hmu_root)

/-- Sharp integral-power form of the elliptic resolver estimate for `q > 1`. -/
lemma intervalDomain_elliptic_rpow_root_le
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) (hq : 1 < q) :
    (∫ x in (0 : ℝ)..1, intervalDomainLift (v t) x ^ q) ^ (1 / q) ≤
      (p.ν / p.μ) *
        (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (p.γ * q)) ^ (1 / q) := by
  let Iv : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (v t) x ^ q
  let Iu : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (p.γ * q)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hVpos := intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u t) x := fun x hx => solution_lift_pos hsol ht x hx
  have hIv : 0 ≤ Iv := by
    dsimp [Iv]
    exact intervalIntegral.integral_nonneg (by norm_num) fun x hx =>
      Real.rpow_nonneg (hVpos x hx).le _
  have hIu : 0 ≤ Iu := by
    dsimp [Iu]
    exact intervalIntegral.integral_nonneg (by norm_num) fun x hx =>
      Real.rpow_nonneg (hUpos x hx).le _
  have hpre := intervalDomain_elliptic_power_preestimate hsol ht0 htT hq
  have hholder := intervalDomain_elliptic_source_holder hsol ht0 htT hq
  have hsharp : p.μ * Iv ≤
      p.ν * (Iv ^ ((q - 1) / q) * Iu ^ (1 / q)) := by
    calc
      p.μ * Iv ≤ p.ν * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ p.γ *
            intervalDomainLift (v t) x ^ (q - 1)) := by
        simpa [Iv] using hpre
      _ ≤ p.ν * (Iv ^ ((q - 1) / q) * Iu ^ (1 / q)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [Iv, Iu] using hholder) p.hν.le
  simpa [Iv, Iu] using
    rpow_root_le_ratio_of_holder p.hμ p.hν hq hIv hIu hsharp

/-- The `L^q` norm of the pointwise power source is the corresponding
`γq` integral power mean of the lifted solution slice. -/
lemma intervalDomainLpNorm_solution_power_eq
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T) (hq : 0 < q) :
    intervalDomainLpNorm q (fun X => (u t X) ^ p.γ) =
      (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (p.γ * q)) ^ (1 / q) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let F : intervalDomain.Point → ℝ := fun X => (u t X) ^ p.γ
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos hsol ht x hx
  have hFlift : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift F x = U x ^ p.γ := by
    intro x hx
    simp [F, U, intervalDomainLift, hx]
  have hFcont : ContinuousOn (intervalDomainLift F) (Set.Icc (0 : ℝ) 1) := by
    exact (hUcont.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).congr
        (fun x hx => hFlift x hx)
  have hFpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift F x := by
    intro x hx
    rw [hFlift x hx]
    exact Real.rpow_pos_of_pos (hUpos x hx) _
  rw [show intervalDomainLpNorm q (fun X => (u t X) ^ p.γ) =
      intervalDomainLpNorm q F by rfl,
    intervalDomainLpNorm_eq_integral_rpow hq hFcont hFpos]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  dsimp
  rw [hFlift x hxIcc, ← Real.rpow_mul (hUpos x hxIcc).le]

/-- Genuine interval-domain realization of Paper 2, Proposition 2.1. -/
theorem intervalDomain_Proposition_2_1 (p : CM2Params) :
    Proposition_2_1 intervalDomain p intervalDomainSemigroupEstimateData := by
  intro T _hT u v hsol q hq t ht0 htT
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hVcont : ContinuousOn (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hVpos := intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  change intervalDomainLpNorm q (v t) ≤
    (p.ν / p.μ) * intervalDomainLpNorm q (fun x => (u t x) ^ p.γ)
  rw [intervalDomainLpNorm_eq_integral_rpow hqpos hVcont hVpos,
    intervalDomainLpNorm_solution_power_eq hsol ht0 htT hqpos]
  rcases eq_or_lt_of_le hq with rfl | hqgt
  · have hmass := intervalDomain_chemical_mass_identity hsol ht0 htT
    norm_num [one_div] at hmass ⊢
    rw [show (p.ν / p.μ) *
        (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ p.γ) =
      (p.ν * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ p.γ)) / p.μ by ring]
    exact le_of_eq ((eq_div_iff p.hμ.ne').2 (by simpa [mul_comm] using hmass))
  · exact intervalDomain_elliptic_rpow_root_le hsol ht0 htT hqgt

#print axioms intervalDomain_chemical_mass_identity
#print axioms intervalDomain_elliptic_rpow_root_le
#print axioms intervalDomain_Proposition_2_1

end ShenWork.Paper2
