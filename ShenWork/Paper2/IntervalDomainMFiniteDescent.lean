import ShenWork.Paper2.IntervalDomainMWeightedGradient
import ShenWork.Paper2.IntervalDomainLpMonotonicity

/-!
# Finite exponent descent for `0 < m < 1`

The exponent sequence in the source proof is
`r k = p + 2^k (m - 1)`.  A Young split sends `r k` to
`2 * r k - p = r (k+1)`, so the terminal choice is
`p = 2^n (1-m)`.  This file keeps that power-of-two recursion explicit.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

/-- Weighted `v_x` square appearing in the exponent descent. -/
def descentVGradient
    (r eta : ℝ) (u v : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ r *
      |deriv (intervalDomainLift (v t)) x| ^ 2 *
      (1 + intervalDomainLift (v t) x) ^ (-eta)

/-- Absolute mixed term produced by the elliptic multiplier. -/
def descentMixed
    (r beta : ℝ) (u v : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (r - 1) *
      |deriv (intervalDomainLift (u t)) x| *
      |deriv (intervalDomainLift (v t)) x| *
      (1 + intervalDomainLift (v t) x) ^ (-beta)

theorem elliptic_multiplier_hasDerivAt
    {p : CM2Params} {T t r : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    let U := intervalDomainLift (u t)
    let V := intervalDomainLift (v t)
    let H := fun y => U y ^ r * (1 + V y) ^ (-p.β)
    HasDerivAt H
      (r * U x ^ (r - 1) * deriv U x * (1 + V x) ^ (-p.β) -
        p.β * U x ^ r * deriv V x *
          (1 + V x) ^ (-(p.β + 1))) x := by
  dsimp
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hV2 := (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hU : HasDerivAt (intervalDomainLift (u t))
      (deriv (intervalDomainLift (u t)) x) x :=
    (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
    isOpen_Ioo (hU2.mono Set.Ioo_subset_Icc_self) hx).1
  have hV : HasDerivAt (intervalDomainLift (v t))
      (deriv (intervalDomainLift (v t)) x) x :=
    (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
    isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).1
  have hUx : 0 < intervalDomainLift (u t) x :=
    solution_lift_pos_Icc hsol ht x (Set.Ioo_subset_Icc_self hx)
  have hBx : 0 < 1 + intervalDomainLift (v t) x := by
    have := hsol.v_nonneg (x :=
      (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomain.Point)) ht0 htT
    have hlift : intervalDomainLift (v t) x =
        v t (⟨x, Set.Ioo_subset_Icc_self hx⟩ : intervalDomain.Point) := by
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hx]
    rw [hlift]
    linarith
  have hUr := hU.rpow_const (p := r) (Or.inl (ne_of_gt hUx))
  have hB : HasDerivAt (fun y => 1 + intervalDomainLift (v t) y)
      (deriv (intervalDomainLift (v t)) x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hV using 1 <;> simp
  have hBpow := hB.rpow_const (p := -p.β) (Or.inl (ne_of_gt hBx))
  convert hUr.mul hBpow using 1 <;> ring

theorem elliptic_multiplier_ibp_identity
    {p : CM2Params} {T t r : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    let U := intervalDomainLift (u t)
    let V := intervalDomainLift (v t)
    let Signed := ∫ x in (0 : ℝ)..1,
      U x ^ (r - 1) * deriv U x * deriv V x * (1 + V x) ^ (-p.β)
    p.β * descentVGradient r (p.β + 1) u v t =
      r * Signed +
        p.μ * (∫ x in (0 : ℝ)..1,
          U x ^ r * V x * (1 + V x) ^ (-p.β)) -
        p.ν * (∫ x in (0 : ℝ)..1,
          U x ^ (r + p.γ) * (1 + V x) ^ (-p.β)) := by
  dsimp only
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let H : ℝ → ℝ := fun x => U x ^ r * (1 + V x) ^ (-p.β)
  let H' : ℝ → ℝ := fun x =>
    r * U x ^ (r - 1) * deriv U x * (1 + V x) ^ (-p.β) -
      p.β * U x ^ r * deriv V x * (1 + V x) ^ (-(p.β + 1))
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU2 : ContDiffOn ℝ 2 U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using deriv_v_continuousOn_Icc hsol ht0 htT
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos_Icc hsol ht x hx
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    intro x hx
    simpa [V, intervalDomainLift, hx] using
      hsol.v_nonneg (x := (⟨x, hx⟩ : intervalDomain.Point)) ht0 htT
  have hHcont : ContinuousOn H (Set.Icc (0 : ℝ) 1) := by
    have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.add hV2.continuousOn
    exact (hU2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul
      (hbase.rpow_const (fun x hx => Or.inl
        (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx]))))
  have hH'cont : ContinuousOn H' (Set.Icc (0 : ℝ) 1) := by
    have hdUcont : ContinuousOn (deriv U) (Set.Icc (0 : ℝ) 1) := by
      simpa [U] using (deriv_lift_contDiffOn_one_Icc hU2
        (derivWithin_left_zero hsol ht0 htT u (Or.inl rfl))
        (derivWithin_right_zero hsol ht0 htT u (Or.inl rfl))).continuousOn
    have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.add hV2.continuousOn
    have hUr1 : ContinuousOn (fun x => U x ^ (r - 1)) (Set.Icc (0 : ℝ) 1) :=
      hU2.continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    have hUr : ContinuousOn (fun x => U x ^ r) (Set.Icc (0 : ℝ) 1) :=
      hU2.continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    have hB1 : ContinuousOn (fun x => (1 + V x) ^ (-p.β))
        (Set.Icc (0 : ℝ) 1) :=
      hbase.rpow_const (fun x hx => Or.inl
        (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx])))
    have hB2 : ContinuousOn (fun x => (1 + V x) ^ (-(p.β + 1)))
        (Set.Icc (0 : ℝ) 1) :=
      hbase.rpow_const (fun x hx => Or.inl
        (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx])))
    have hterm1 : ContinuousOn
        (fun x => r * U x ^ (r - 1) * deriv U x * (1 + V x) ^ (-p.β))
        (Set.Icc (0 : ℝ) 1) :=
      ((continuousOn_const.mul hUr1).mul hdUcont).mul hB1
    have hterm2 : ContinuousOn
        (fun x => p.β * U x ^ r * deriv V x * (1 + V x) ^ (-(p.β + 1)))
        (Set.Icc (0 : ℝ) 1) :=
      ((continuousOn_const.mul hUr).mul hdVcont).mul hB2
    exact hterm1.sub hterm2
  have hHderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt H (H' x) x := by
    intro x hx
    simpa [U, V, H, H'] using elliptic_multiplier_hasDerivAt hsol ht0 htT hx
  have hVderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (deriv V) (deriv (deriv V) x) x := by
    intro x hx
    exact (ShenWork.MinPersistenceAtoms.contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo (hV2.mono Set.Ioo_subset_Icc_self) hx).2
  have hH'int : IntervalIntegrable H' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hH'cont
  have hV2int : IntervalIntegrable (deriv (deriv V)) volume 0 1 :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hV2
  have hNeu0 : deriv V 0 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.1
  have hNeu1 : deriv V 1 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.2
  have hIBP : (∫ x in (0 : ℝ)..1, H x * deriv (deriv V) x) =
      -∫ x in (0 : ℝ)..1, H' x * deriv V x :=
    intervalFluxByParts_open
      (by simpa [Set.uIcc_of_le zero_le_one] using hHcont)
      (by simpa [Set.uIcc_of_le zero_le_one] using hdVcont)
      hHderiv hVderiv hH'int hV2int hNeu0 hNeu1
  have hBneg : ContinuousOn (fun x => (1 + V x) ^ (-p.β))
      (Set.Icc (0 : ℝ) 1) := by
    have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.add hV2.continuousOn
    exact hbase.rpow_const (fun x hx => Or.inl
      (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx])))
  have hBneg1 : ContinuousOn (fun x => (1 + V x) ^ (-(p.β + 1)))
      (Set.Icc (0 : ℝ) 1) := by
    have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.add hV2.continuousOn
    exact hbase.rpow_const (fun x hx => Or.inl
      (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx])))
  have hUr : ContinuousOn (fun x => U x ^ r) (Set.Icc (0 : ℝ) 1) :=
    hU2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hUr1 : ContinuousOn (fun x => U x ^ (r - 1)) (Set.Icc (0 : ℝ) 1) :=
    hU2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hUrg : ContinuousOn (fun x => U x ^ (r + p.γ))
      (Set.Icc (0 : ℝ) 1) :=
    hU2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hdUcont : ContinuousOn (deriv U) (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (deriv_lift_contDiffOn_one_Icc hU2
      (derivWithin_left_zero hsol ht0 htT u (Or.inl rfl))
      (derivWithin_right_zero hsol ht0 htT u (Or.inl rfl))).continuousOn
  let A : ℝ → ℝ := fun x => U x ^ r * V x * (1 + V x) ^ (-p.β)
  let B : ℝ → ℝ := fun x => U x ^ (r + p.γ) * (1 + V x) ^ (-p.β)
  let S : ℝ → ℝ := fun x =>
    U x ^ (r - 1) * deriv U x * deriv V x * (1 + V x) ^ (-p.β)
  let J : ℝ → ℝ := fun x =>
    U x ^ r * |deriv V x| ^ 2 * (1 + V x) ^ (-(p.β + 1))
  have hAint : IntervalIntegrable A volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (hUr.mul hV2.continuousOn).mul hBneg
  have hBint : IntervalIntegrable B volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hUrg.mul hBneg
  have hSint : IntervalIntegrable S volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (((hUr1.mul hdUcont).mul hdVcont).mul hBneg)
  have hJint : IntervalIntegrable J volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact ((hUr.mul (hdVcont.abs.pow 2)).mul hBneg1)
  have hleftEq :
      (∫ x in (0 : ℝ)..1, H x * deriv (deriv V) x) =
        p.μ * (∫ x in (0 : ℝ)..1, A x) -
          p.ν * (∫ x in (0 : ℝ)..1, B x) := by
    have hpoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        H x * deriv (deriv V) x = p.μ * A x - p.ν * B x := by
      intro x hx
      have hpde : deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
        simpa [U, V] using v_xx_eq_reaction_lift hsol ht0 htT hx.1 hx.2
      have hpow : U x ^ r * U x ^ p.γ = U x ^ (r + p.γ) := by
        rw [← Real.rpow_add (hUpos x (Set.Ioo_subset_Icc_self hx))]
      dsimp [H, A, B]
      rw [hpde]
      calc
        U x ^ r * (1 + V x) ^ (-p.β) *
            (p.μ * V x - p.ν * U x ^ p.γ) =
          p.μ * (U x ^ r * V x * (1 + V x) ^ (-p.β)) -
            p.ν * ((U x ^ r * U x ^ p.γ) * (1 + V x) ^ (-p.β)) := by ring
        _ = p.μ * (U x ^ r * V x * (1 + V x) ^ (-p.β)) -
            p.ν * (U x ^ (r + p.γ) * (1 + V x) ^ (-p.β)) := by rw [hpow]
    calc
      _ = ∫ x in (0 : ℝ)..1, p.μ * A x - p.ν * B x := by
        apply intervalIntegral.integral_congr_ae
        have hne1 : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by
          have heq : {x : ℝ | ¬ x ≠ 1} = ({1} : Set ℝ) := by ext x; simp
          rw [MeasureTheory.ae_iff, heq]
          exact Real.volume_singleton
        filter_upwards [hne1] with x hxne hxmem
        rw [Set.uIoc_of_le zero_le_one] at hxmem
        exact hpoint x ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hxne⟩
      _ = _ := by
        rw [intervalIntegral.integral_sub (hAint.const_mul p.μ)
            (hBint.const_mul p.ν),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hrightEq :
      (∫ x in (0 : ℝ)..1, H' x * deriv V x) =
        r * (∫ x in (0 : ℝ)..1, S x) -
          p.β * (∫ x in (0 : ℝ)..1, J x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, r * S x - p.β * J x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le zero_le_one] at hx
        dsimp [H', S, J]
        rw [sq_abs]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hSint.const_mul r)
            (hJint.const_mul p.β),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [hleftEq, hrightEq] at hIBP
  change p.β * (∫ x in (0 : ℝ)..1, J x) =
    r * (∫ x in (0 : ℝ)..1, S x) +
      p.μ * (∫ x in (0 : ℝ)..1, A x) -
      p.ν * (∫ x in (0 : ℝ)..1, B x)
  linarith

theorem descentVGradient_intervalIntegrable
    {p : CM2Params} {T t r eta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable (fun x =>
      intervalDomainLift (u t) x ^ r *
        |deriv (intervalDomainLift (v t)) x| ^ 2 *
        (1 + intervalDomainLift (v t) x) ^ (-eta)) volume 0 1 := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU := solution_lift_continuousOn_Icc hsol ht
  have hV := (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hdV := deriv_v_continuousOn_Icc hsol ht0 htT
  have hUpos := solution_lift_pos_Icc hsol ht
  have hVnonneg := lift_v_nonneg_Icc hsol ht0 htT
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  exact ((hU.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul
    (hdV.abs.pow 2)).mul
    ((continuousOn_const.add hV).rpow_const (fun x hx => Or.inl
      (ne_of_gt (show 0 < 1 + intervalDomainLift (v t) x by
        linarith [hVnonneg x hx]))))

theorem descentMixed_intervalIntegrable
    {p : CM2Params} {T t r beta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable (fun x =>
      intervalDomainLift (u t) x ^ (r - 1) *
        |deriv (intervalDomainLift (u t)) x| *
        |deriv (intervalDomainLift (v t)) x| *
        (1 + intervalDomainLift (v t) x) ^ (-beta)) volume 0 1 := by
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hU := hU2.continuousOn
  have hV := (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hdU := (deriv_lift_contDiffOn_one_Icc hU2
    (derivWithin_left_zero hsol ht0 htT u (Or.inl rfl))
    (derivWithin_right_zero hsol ht0 htT u (Or.inl rfl))).continuousOn
  have hdV := deriv_v_continuousOn_Icc hsol ht0 htT
  have hUpos := solution_lift_pos_Icc hsol ht
  have hVnonneg := lift_v_nonneg_Icc hsol ht0 htT
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  exact ((((hU.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul hdU.abs).mul hdV.abs).mul
    ((continuousOn_const.add hV).rpow_const (fun x hx => Or.inl
      (ne_of_gt (show 0 < 1 + intervalDomainLift (v t) x by
        linarith [hVnonneg x hx])))))

theorem descentVGradient_nonneg_of_solution
    {p : CM2Params} {T t r eta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    0 ≤ descentVGradient r eta u v t := by
  unfold descentVGradient
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg
        (lift_u_pos_Icc hsol ht0 htT x hx).le r) (sq_nonneg _))
      (Real.rpow_nonneg (by
        have hv := lift_v_nonneg_Icc hsol ht0 htT x hx
        linarith) _))

theorem descentMixed_nonneg_of_solution
    {p : CM2Params} {T t r beta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    0 ≤ descentMixed r beta u v t := by
  unfold descentMixed
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg
          (lift_u_pos_Icc hsol ht0 htT x hx).le (r - 1)) (abs_nonneg _))
        (abs_nonneg _))
      (Real.rpow_nonneg (by
        have hv := lift_v_nonneg_Icc hsol ht0 htT x hx
        linarith) _))

theorem theta_beta_sub_one_bound
    {p : CM2Params} (hbeta : 1 ≤ p.β) {V : ℝ} (hV : 0 ≤ V) :
    V * (1 + V) ^ (-p.β) ≤ Theta_beta (p.β - 1) := by
  have hbase : 0 < 1 + V := by linarith
  rw [Real.rpow_neg hbase.le]
  change V / (1 + V) ^ p.β ≤ Theta_beta (p.β - 1)
  have hb : 0 ≤ p.β - 1 := by linarith
  rcases lt_or_eq_of_le hb with hbpos | hbzero
  · by_cases hV0 : V = 0
    · subst V
      simp [Theta_beta_nonneg hb]
    · have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
      simpa [show 1 + (p.β - 1) = p.β by ring] using
        Lemma_2_5_normalized_Theta_bound hbpos hVpos
  · have hpβ : p.β = 1 := by linarith
    rw [hpβ, show (1 : ℝ) - 1 = 0 by ring, Theta_beta_zero, Real.rpow_one]
    exact (div_le_one hbase).2 (by linarith)

/-- One elliptic descent step before Young splitting. -/
theorem elliptic_descent_estimate
    {p : CM2Params} {T t r : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hbeta : 1 ≤ p.β) (hr : 0 < r) :
    descentVGradient r (2 * p.β) u v t ≤
      (r / p.β) * descentMixed r p.β u v t +
        (p.μ * Theta_beta (p.β - 1) / p.β) *
          (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ r) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hβpos : 0 < p.β := lt_of_lt_of_le zero_lt_one hbeta
  have hUpos := solution_lift_pos_Icc hsol ht
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    simpa [V] using lift_v_nonneg_Icc hsol ht0 htT
  have hIleJ : descentVGradient r (2 * p.β) u v t ≤
      descentVGradient r (p.β + 1) u v t := by
    unfold descentVGradient
    apply intervalIntegral.integral_mono_on (by norm_num)
      (descentVGradient_intervalIntegrable hsol ht0 htT)
      (descentVGradient_intervalIntegrable hsol ht0 htT)
    intro x hx
    have hbase : 1 ≤ 1 + V x := by linarith [hVnonneg x hx]
    have hexp : -(2 * p.β) ≤ -(p.β + 1) := by linarith
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase hexp)
      (mul_nonneg (Real.rpow_nonneg (hUpos x hx).le r) (sq_nonneg _))
  let Signed := ∫ x in (0 : ℝ)..1,
    U x ^ (r - 1) * deriv U x * deriv V x * (1 + V x) ^ (-p.β)
  let A := ∫ x in (0 : ℝ)..1,
    U x ^ r * V x * (1 + V x) ^ (-p.β)
  let B := ∫ x in (0 : ℝ)..1,
    U x ^ (r + p.γ) * (1 + V x) ^ (-p.β)
  have hid := elliptic_multiplier_ibp_identity
    (p := p) (T := T) (t := t) (r := r) (u := u) (v := v) hsol ht0 htT
  change p.β * descentVGradient r (p.β + 1) u v t =
    r * Signed + p.μ * A - p.ν * B at hid
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (Real.rpow_nonneg (hUpos x hx).le (r + p.γ))
        (Real.rpow_nonneg (by linarith [hVnonneg x hx]) _))
  have hSigned : Signed ≤ descentMixed r p.β u v t := by
    dsimp [Signed, descentMixed]
    have hU2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
    have hV2 := (hsol.regularity.2.2.2.2.1 t ht).2.1
    have hdU := (deriv_lift_contDiffOn_one_Icc hU2
      (derivWithin_left_zero hsol ht0 htT u (Or.inl rfl))
      (derivWithin_right_zero hsol ht0 htT u (Or.inl rfl))).continuousOn
    have hdV := deriv_v_continuousOn_Icc hsol ht0 htT
    have hSignedInt : IntervalIntegrable (fun x =>
        U x ^ (r - 1) * deriv U x * deriv V x * (1 + V x) ^ (-p.β))
        volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
        continuousOn_const.add hV2.continuousOn
      exact ((((hU2.continuousOn.rpow_const
          (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul hdU).mul hdV).mul
        (hbase.rpow_const (fun x hx => Or.inl
          (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx])))))
    apply intervalIntegral.integral_mono_on (by norm_num)
      hSignedInt
      (descentMixed_intervalIntegrable hsol ht0 htT)
    intro x hx
    have hw : 0 ≤ U x ^ (r - 1) * (1 + V x) ^ (-p.β) :=
      mul_nonneg (Real.rpow_nonneg (hUpos x hx).le _)
        (Real.rpow_nonneg (by linarith [hVnonneg x hx]) _)
    have hprod : deriv U x * deriv V x ≤
        |deriv U x| * |deriv V x| := by
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith [mul_le_mul_of_nonneg_left hprod hw]
  have hA : A ≤ Theta_beta (p.β - 1) *
      (∫ x in (0 : ℝ)..1, U x ^ r) := by
    dsimp [A]
    have hUint : IntervalIntegrable (fun x => U x ^ r) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (solution_lift_continuousOn_Icc hsol ht).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    have hleft : IntervalIntegrable
        (fun x => U x ^ r * V x * (1 + V x) ^ (-p.β)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      have hVcont := (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
      have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
        continuousOn_const.add hVcont
      have hbasepow : ContinuousOn (fun x => (1 + V x) ^ (-p.β))
          (Set.Icc (0 : ℝ) 1) :=
        hbase.rpow_const (fun x hx => Or.inl
          (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx])))
      exact (((solution_lift_continuousOn_Icc hsol ht).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul hVcont).mul hbasepow
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, Theta_beta (p.β - 1) * U x ^ r :=
        intervalIntegral.integral_mono_on (by norm_num) hleft
          (hUint.const_mul _) (fun x hx => by
            have hpow : 0 ≤ U x ^ r := Real.rpow_nonneg (hUpos x hx).le _
            have hv := theta_beta_sub_one_bound hbeta (hVnonneg x hx)
            calc
              U x ^ r * V x * (1 + V x) ^ (-p.β) =
                  U x ^ r * (V x * (1 + V x) ^ (-p.β)) := by ring
              _ ≤ U x ^ r * Theta_beta (p.β - 1) :=
                mul_le_mul_of_nonneg_left hv hpow
              _ = Theta_beta (p.β - 1) * U x ^ r := by ring)
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hJ : descentVGradient r (p.β + 1) u v t ≤
      (r / p.β) * descentMixed r p.β u v t +
        (p.μ * Theta_beta (p.β - 1) / p.β) *
          (∫ x in (0 : ℝ)..1, U x ^ r) := by
    apply le_of_mul_le_mul_right ?_ hβpos
    calc
      descentVGradient r (p.β + 1) u v t * p.β =
          p.β * descentVGradient r (p.β + 1) u v t := by ring
      _ = r * Signed + p.μ * A - p.ν * B := hid
      _ ≤ r * descentMixed r p.β u v t +
          p.μ * (Theta_beta (p.β - 1) *
            (∫ x in (0 : ℝ)..1, U x ^ r)) := by
        have hr0 := hr.le
        have hmu := p.hμ.le
        have hnuB : 0 ≤ p.ν * B := mul_nonneg p.hν.le hBnonneg
        nlinarith [mul_le_mul_of_nonneg_left hSigned hr0,
          mul_le_mul_of_nonneg_left hA hmu]
      _ = ((r / p.β) * descentMixed r p.β u v t +
          (p.μ * Theta_beta (p.β - 1) / p.β) *
            (∫ x in (0 : ℝ)..1, U x ^ r)) * p.β := by
        field_simp [ne_of_gt hβpos]
  simpa [U] using hIleJ.trans hJ

theorem descent_pointwise_young
    {U UX VX B C eps pExp r beta : ℝ}
    (hU : 0 < U) (hB : 0 < B) (heps : 0 < eps) :
    C * (U ^ (r - 1) * |UX| * |VX| * B ^ (-beta)) ≤
      eps * (U ^ (pExp - 2) * |UX| ^ 2) +
        (C ^ 2 / (4 * eps)) *
          (U ^ (2 * r - pExp) * |VX| ^ 2 * B ^ (-(2 * beta))) := by
  let X := U ^ ((pExp - 2) / 2) * |UX|
  let Y := C * U ^ (r - pExp / 2) * |VX| * B ^ (-beta)
  have hyoung : X * Y ≤ eps * X ^ 2 + Y ^ 2 / (4 * eps) := by
    have h4 : 0 < 4 * eps := by positivity
    have hsquare : 0 ≤ (2 * eps * X - Y) ^ 2 / (4 * eps) := by positivity
    have hid : eps * X ^ 2 + Y ^ 2 / (4 * eps) - X * Y =
        (2 * eps * X - Y) ^ 2 / (4 * eps) := by
      field_simp
      ring
    linarith
  have hXY : X * Y = C * (U ^ (r - 1) * |UX| * |VX| * B ^ (-beta)) := by
    dsimp [X, Y]
    have hp : U ^ ((pExp - 2) / 2) * U ^ (r - pExp / 2) = U ^ (r - 1) := by
      rw [← Real.rpow_add hU]
      congr 1
      ring
    rw [show U ^ ((pExp - 2) / 2) * |UX| *
        (C * U ^ (r - pExp / 2) * |VX| * B ^ (-beta)) =
      C * (U ^ ((pExp - 2) / 2) * U ^ (r - pExp / 2)) *
        |UX| * |VX| * B ^ (-beta) by ring, hp]
    ring
  have hX2 : X ^ 2 = U ^ (pExp - 2) * |UX| ^ 2 := by
    dsimp [X]
    rw [mul_pow, ← Real.rpow_mul_natCast hU.le ((pExp - 2) / 2) 2]
    congr 1
    ring
  have hY2 : Y ^ 2 / (4 * eps) =
      (C ^ 2 / (4 * eps)) *
        (U ^ (2 * r - pExp) * |VX| ^ 2 * B ^ (-(2 * beta))) := by
    dsimp [Y]
    have hUpow : (U ^ (r - pExp / 2)) ^ (2 : ℕ) = U ^ (2 * r - pExp) := by
      rw [← Real.rpow_mul_natCast hU.le]
      congr 1
      ring
    have hBpow : (B ^ (-beta)) ^ (2 : ℕ) = B ^ (-(2 * beta)) := by
      rw [← Real.rpow_mul_natCast hB.le]
      congr 1
      ring
    rw [show (C * U ^ (r - pExp / 2) * |VX| * B ^ (-beta)) ^ 2 =
      C ^ 2 * (U ^ (r - pExp / 2)) ^ 2 * |VX| ^ 2 *
        (B ^ (-beta)) ^ 2 by ring, hUpow, hBpow]
    ring
  calc
    C * (U ^ (r - 1) * |UX| * |VX| * B ^ (-beta)) = X * Y := hXY.symm
    _ ≤ eps * X ^ 2 + Y ^ 2 / (4 * eps) := hyoung
    _ = eps * (U ^ (pExp - 2) * |UX| ^ 2) +
        (C ^ 2 / (4 * eps)) *
          (U ^ (2 * r - pExp) * |VX| ^ 2 * B ^ (-(2 * beta))) := by
      rw [hX2, hY2]

theorem descentMixed_young
    {p : CM2Params} {T t pExp r C eps : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (heps : 0 < eps) :
    C * descentMixed r p.β u v t ≤
      eps * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (pExp - 2) *
          |deriv (intervalDomainLift (u t)) x| ^ 2) +
        (C ^ 2 / (4 * eps)) *
          descentVGradient (2 * r - pExp) (2 * p.β) u v t := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUpos := solution_lift_pos_Icc hsol ht
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    simpa [V] using lift_v_nonneg_Icc hsol ht0 htT
  have hDint : IntervalIntegrable (fun x =>
      U x ^ (pExp - 2) * |deriv U x| ^ 2) volume 0 1 := by
    have hU2 := (hsol.regularity.2.2.2.2.1 t ht).1.1
    have hdU := (deriv_lift_contDiffOn_one_Icc hU2
      (derivWithin_left_zero hsol ht0 htT u (Or.inl rfl))
      (derivWithin_right_zero hsol ht0 htT u (Or.inl rfl))).continuousOn
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (hU2.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul (hdU.abs.pow 2)
  have hMixInt := descentMixed_intervalIntegrable
    (r := r) (beta := p.β) hsol ht0 htT
  have hIInt := descentVGradient_intervalIntegrable
    (r := 2 * r - pExp) (eta := 2 * p.β) hsol ht0 htT
  unfold descentMixed descentVGradient
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have hright : IntervalIntegrable (fun x =>
      eps * (U x ^ (pExp - 2) * |deriv U x| ^ 2) +
        (C ^ 2 / (4 * eps)) *
          (U x ^ (2 * r - pExp) * |deriv V x| ^ 2 *
            (1 + V x) ^ (-(2 * p.β)))) volume 0 1 :=
    (hDint.const_mul eps).add (hIInt.const_mul (C ^ 2 / (4 * eps)))
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      C * (U x ^ (r - 1) * |deriv U x| * |deriv V x| *
        (1 + V x) ^ (-p.β)) ≤
      eps * (U x ^ (pExp - 2) * |deriv U x| ^ 2) +
        (C ^ 2 / (4 * eps)) *
          (U x ^ (2 * r - pExp) * |deriv V x| ^ 2 *
            (1 + V x) ^ (-(2 * p.β))) := by
    intro x hx
    simpa [mul_assoc] using descent_pointwise_young
      (U := U x) (UX := deriv U x) (VX := deriv V x) (B := 1 + V x)
      (C := C) (eps := eps) (pExp := pExp) (r := r) (beta := p.β)
      (hUpos x hx) (by linarith [hVnonneg x hx]) heps
  calc
    _ ≤ ∫ x in (0 : ℝ)..1,
        eps * (U x ^ (pExp - 2) * |deriv U x| ^ 2) +
          (C ^ 2 / (4 * eps)) *
            (U x ^ (2 * r - pExp) * |deriv V x| ^ 2 *
              (1 + V x) ^ (-(2 * p.β))) :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hMixInt.const_mul C) hright hpoint
    _ = _ := by
      rw [intervalIntegral.integral_add (hDint.const_mul eps)
        (hIInt.const_mul (C ^ 2 / (4 * eps)))]

/-- A complete recursive step: `r` is replaced by `2r-pExp`; the lower
`r`-moment is bounded by the target `pExp`-moment plus the unit volume. -/
def descentNextCoeff (p : CM2Params) (r C eps : ℝ) : ℝ :=
  (C * (r / p.β)) ^ 2 / (4 * eps)

def descentLowerCoeff (p : CM2Params) (C : ℝ) : ℝ :=
  C * (p.μ * Theta_beta (p.β - 1) / p.β)

theorem finite_descent_step
    {p : CM2Params} {T t pExp r C eps : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hbeta : 1 ≤ p.β) (hr : 0 < r) (hrp : r ≤ pExp)
    (hC : 0 ≤ C) (heps : 0 < eps) :
    C * descentVGradient r (2 * p.β) u v t ≤
      eps * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (pExp - 2) *
          |deriv (intervalDomainLift (u t)) x| ^ 2) +
      descentNextCoeff p r C eps *
        descentVGradient (2 * r - pExp) (2 * p.β) u v t +
      descentLowerCoeff p C * ((∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ pExp) + 1) := by
  let Cmix := C * (r / p.β)
  let Cnext := Cmix ^ 2 / (4 * eps)
  let A := C * (p.μ * Theta_beta (p.β - 1) / p.β)
  have hβpos : 0 < p.β := lt_of_lt_of_le zero_lt_one hbeta
  have htheta : 0 ≤ Theta_beta (p.β - 1) :=
    Theta_beta_nonneg (by linarith)
  have hCnext : 0 ≤ Cnext := by dsimp [Cnext]; positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg hC
      (div_nonneg (mul_nonneg p.hμ.le htheta) hβpos.le)
  change C * descentVGradient r (2 * p.β) u v t ≤
    eps * (∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (pExp - 2) *
        |deriv (intervalDomainLift (u t)) x| ^ 2) +
    Cnext * descentVGradient (2 * r - pExp) (2 * p.β) u v t +
    A * ((∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ pExp) + 1)
  have hell := elliptic_descent_estimate hsol ht0 htT hbeta hr
  have hmul := mul_le_mul_of_nonneg_left hell hC
  have hyoung := descentMixed_young
    (pExp := pExp) (r := r) (C := Cmix) (eps := eps)
    hsol ht0 htT heps
  have hlower : (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ r) ≤
      (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp) + 1 := by
    have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
    have hUpos := solution_lift_pos_Icc hsol ht
    have hr0 := hr.le
    have hrInt : IntervalIntegrable
        (fun x => intervalDomainLift (u t) x ^ r) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (solution_lift_continuousOn_Icc hsol ht).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    have hpInt : IntervalIntegrable
        (fun x => intervalDomainLift (u t) x ^ pExp) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (solution_lift_continuousOn_Icc hsol ht).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp + 1 :=
        intervalIntegral.integral_mono_on (by norm_num) hrInt
          (hpInt.add intervalIntegrable_const) (fun x hx =>
            IntervalDomainLpMonotonicity.rpow_le_one_add_rpow_of_nonneg_of_le
              (hUpos x hx).le hr0 hrp)
      _ = _ := by
        rw [intervalIntegral.integral_add hpInt intervalIntegrable_const,
          intervalIntegral.integral_const]
        norm_num [smul_eq_mul]
  dsimp [Cmix, Cnext, A] at hyoung ⊢
  calc
    C * descentVGradient r (2 * p.β) u v t ≤
        C * ((r / p.β) * descentMixed r p.β u v t +
          (p.μ * Theta_beta (p.β - 1) / p.β) *
            (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ r)) := hmul
    _ = (C * (r / p.β)) * descentMixed r p.β u v t +
        A * (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ r) := by
      dsimp [A]
      ring
    _ ≤ (eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        (C * (r / p.β)) ^ 2 / (4 * eps) *
          descentVGradient (2 * r - pExp) (2 * p.β) u v t) +
        A * ((∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp) + 1) :=
      add_le_add hyoung (mul_le_mul_of_nonneg_left hlower hA)
    _ = _ := by ring

theorem signedCross_abs_le_descentMixed
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    |lpSignedCrossIntegralM p pExp u v t| ≤
      descentMixed (pExp + p.m - 1) p.β u v t := by
  unfold lpSignedCrossIntegralM descentMixed
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUpos := solution_lift_pos_Icc hsol ht
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    simpa [V] using lift_v_nonneg_Icc hsol ht0 htT
  calc
    |∫ x in (0 : ℝ)..1,
        U x ^ (pExp + p.m - 2) * deriv U x * deriv V x /
          (1 + V x) ^ p.β| ≤
      ∫ x in (0 : ℝ)..1,
        |U x ^ (pExp + p.m - 2) * deriv U x * deriv V x /
          (1 + V x) ^ p.β| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ = ∫ x in (0 : ℝ)..1,
        U x ^ (pExp + p.m - 1 - 1) * |deriv U x| * |deriv V x| *
          (1 + V x) ^ (-p.β) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le zero_le_one] at hx
      have hB : 0 < 1 + V x := by linarith [hVnonneg x hx]
      change |U x ^ (pExp + p.m - 2) * deriv U x * deriv V x /
          (1 + V x) ^ p.β| =
        U x ^ (pExp + p.m - 1 - 1) * |deriv U x| * |deriv V x| *
          (1 + V x) ^ (-p.β)
      rw [abs_div, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (hUpos x hx).le _),
        abs_of_pos (Real.rpow_pos_of_pos hB _),
        Real.rpow_neg hB.le]
      simp only [div_eq_mul_inv]
      dsimp [U]
      ring
    _ = _ := by rfl

def doublingExponent (pExp r0 : ℝ) (k : ℕ) : ℝ :=
  pExp + (2 : ℝ) ^ k * (r0 - pExp)

theorem doublingExponent_zero (pExp r0 : ℝ) :
    doublingExponent pExp r0 0 = r0 := by
  simp [doublingExponent]

theorem doublingExponent_succ (pExp r0 : ℝ) (k : ℕ) :
    doublingExponent pExp r0 (k + 1) =
      2 * doublingExponent pExp r0 k - pExp := by
  simp only [doublingExponent, pow_succ]
  ring

def iteratedDescentCoeff
    (p : CM2Params) (pExp r0 eps C0 : ℝ) : ℕ → ℝ
  | 0 => C0
  | k + 1 => descentNextCoeff p (doublingExponent pExp r0 k)
      (iteratedDescentCoeff p pExp r0 eps C0 k) eps

def accumulatedDescentLower
    (p : CM2Params) (pExp r0 eps C0 : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => accumulatedDescentLower p pExp r0 eps C0 k +
      descentLowerCoeff p (iteratedDescentCoeff p pExp r0 eps C0 k)

theorem iteratedDescentCoeff_nonneg
    {p : CM2Params} {pExp r0 eps C0 : ℝ}
    (heps : 0 < eps) (hC0 : 0 ≤ C0) :
    ∀ k, 0 ≤ iteratedDescentCoeff p pExp r0 eps C0 k := by
  intro k
  induction k with
  | zero => exact hC0
  | succ k ih =>
      simp only [iteratedDescentCoeff]
      unfold descentNextCoeff
      positivity

theorem accumulatedDescentLower_nonneg
    {p : CM2Params} {pExp r0 eps C0 : ℝ}
    (hbeta : 1 ≤ p.β) (heps : 0 < eps) (hC0 : 0 ≤ C0) :
    ∀ k, 0 ≤ accumulatedDescentLower p pExp r0 eps C0 k := by
  intro k
  induction k with
  | zero => simp [accumulatedDescentLower]
  | succ k ih =>
      simp only [accumulatedDescentLower]
      apply add_nonneg ih
      unfold descentLowerCoeff
      have hcoeff := iteratedDescentCoeff_nonneg
        (p := p) (pExp := pExp) (r0 := r0) heps hC0 k
      have htheta := Theta_beta_nonneg (show 0 ≤ p.β - 1 by linarith)
      exact mul_nonneg hcoeff
        (div_nonneg (mul_nonneg p.hμ.le htheta) (by linarith))

/-- Iterate the exponent-doubling descent a prescribed finite number of
steps.  The exponent hypotheses are exactly what the terminal specialization
will discharge from `pExp = 2^n(1-m)`. -/
theorem finite_descent_iterate
    {p : CM2Params} {T t pExp r0 eps C0 : ℝ} {steps : ℕ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hbeta : 1 ≤ p.β) (heps : 0 < eps) (hC0 : 0 ≤ C0)
    (hexp : ∀ k < steps,
      0 < doublingExponent pExp r0 k ∧
        doublingExponent pExp r0 k ≤ pExp) :
    C0 * descentVGradient r0 (2 * p.β) u v t ≤
      (steps : ℝ) * eps * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (pExp - 2) *
          |deriv (intervalDomainLift (u t)) x| ^ 2) +
      iteratedDescentCoeff p pExp r0 eps C0 steps *
        descentVGradient (doublingExponent pExp r0 steps)
          (2 * p.β) u v t +
      accumulatedDescentLower p pExp r0 eps C0 steps *
        ((∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp) + 1) := by
  induction steps with
  | zero =>
      simp [doublingExponent, iteratedDescentCoeff, accumulatedDescentLower]
  | succ k ih =>
      have hexp0 : ∀ j < k,
          0 < doublingExponent pExp r0 j ∧
            doublingExponent pExp r0 j ≤ pExp :=
        fun j hj => hexp j (Nat.lt.step hj)
      have hih := ih hexp0
      have hk := hexp k (Nat.lt_succ_self k)
      have hcoeff := iteratedDescentCoeff_nonneg
        (p := p) (pExp := pExp) (r0 := r0) heps hC0 k
      have hstep := finite_descent_step
        (pExp := pExp) (r := doublingExponent pExp r0 k)
        (C := iteratedDescentCoeff p pExp r0 eps C0 k) (eps := eps)
        hsol ht0 htT hbeta hk.1 hk.2 hcoeff heps
      have hacc := accumulatedDescentLower_nonneg
        (p := p) (pExp := pExp) (r0 := r0) hbeta heps hC0 k
      simp only [Nat.cast_add, Nat.cast_one, iteratedDescentCoeff,
        accumulatedDescentLower, doublingExponent_succ]
      calc
        C0 * descentVGradient r0 (2 * p.β) u v t ≤
            (k : ℝ) * eps * (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (pExp - 2) *
                |deriv (intervalDomainLift (u t)) x| ^ 2) +
            iteratedDescentCoeff p pExp r0 eps C0 k *
              descentVGradient (doublingExponent pExp r0 k)
                (2 * p.β) u v t +
            accumulatedDescentLower p pExp r0 eps C0 k *
              ((∫ x in (0 : ℝ)..1,
                intervalDomainLift (u t) x ^ pExp) + 1) := hih
        _ ≤ (k : ℝ) * eps * (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (pExp - 2) *
                |deriv (intervalDomainLift (u t)) x| ^ 2) +
            (eps * (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (pExp - 2) *
                |deriv (intervalDomainLift (u t)) x| ^ 2) +
              descentNextCoeff p (doublingExponent pExp r0 k)
                  (iteratedDescentCoeff p pExp r0 eps C0 k) eps *
                descentVGradient
                  (2 * doublingExponent pExp r0 k - pExp)
                  (2 * p.β) u v t +
              descentLowerCoeff p
                  (iteratedDescentCoeff p pExp r0 eps C0 k) *
                ((∫ x in (0 : ℝ)..1,
                  intervalDomainLift (u t) x ^ pExp) + 1)) +
            accumulatedDescentLower p pExp r0 eps C0 k *
              ((∫ x in (0 : ℝ)..1,
                intervalDomainLift (u t) x ^ pExp) + 1) := by
          linarith
        _ = (↑k + 1) * eps * (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (pExp - 2) *
                |deriv (intervalDomainLift (u t)) x| ^ 2) +
            descentNextCoeff p (doublingExponent pExp r0 k)
                (iteratedDescentCoeff p pExp r0 eps C0 k) eps *
              descentVGradient
                (2 * doublingExponent pExp r0 k - pExp)
                (2 * p.β) u v t +
            (accumulatedDescentLower p pExp r0 eps C0 k +
              descentLowerCoeff p
                (iteratedDescentCoeff p pExp r0 eps C0 k)) *
              ((∫ x in (0 : ℝ)..1,
                intervalDomainLift (u t) x ^ pExp) + 1) := by ring

theorem doublingExponent_firstLevel
    (pExp m : ℝ) (k : ℕ) :
    doublingExponent pExp (pExp + 2 * (m - 1)) k =
      pExp + (2 : ℝ) ^ (k + 1) * (m - 1) := by
  unfold doublingExponent
  rw [pow_succ]
  ring

/-- Equations (4.1)--(4.4): the signed chemotaxis term descends to exponent
zero after finitely many power-of-two steps. -/
theorem slow_cross_finite_descent
    {p : CM2Params} {T t pExp : ℝ} {steps : ℕ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1)
    (hpdef : pExp = (2 : ℝ) ^ (steps + 1) * (1 - p.m))
    (hp : 1 < pExp) :
    ∃ Cterminal A, 0 ≤ Cterminal ∧ 0 ≤ A ∧
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) *
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (pExp - 2) *
              |deriv (intervalDomainLift (u t)) x| ^ 2) +
        Cterminal * descentVGradient 0 (2 * p.β) u v t +
        A * ((∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ pExp) + 1) := by
  let eps : ℝ := (pExp - 1) / ((steps : ℝ) + 2)
  let Cmix : ℝ := |p.χ₀| * (pExp - 1)
  let r0 : ℝ := pExp + p.m - 1
  let r1 : ℝ := pExp + 2 * (p.m - 1)
  let C0 : ℝ := Cmix ^ 2 / (4 * eps)
  have heps : 0 < eps := by
    dsimp [eps]
    exact div_pos (by linarith) (by positivity)
  have hCmix : 0 ≤ Cmix := mul_nonneg (abs_nonneg _) (by linarith)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hsigned := signedCross_abs_le_descentMixed
    (p := p) (T := T) (t := t) (pExp := pExp) (u := u) (v := v)
    hsol ht0 htT
  have hinitialScalar :
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        Cmix * descentMixed r0 p.β u v t := by
    have habs : |p.χ₀ * (pExp - 1) *
        lpSignedCrossIntegralM p pExp u v t| ≤
        Cmix * descentMixed r0 p.β u v t := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < pExp - 1)]
      dsimp [Cmix, r0]
      exact mul_le_mul_of_nonneg_left hsigned
        (mul_nonneg (abs_nonneg _) (by linarith))
    exact (le_abs_self _).trans habs
  have hinitialYoung := descentMixed_young
    (pExp := pExp) (r := r0) (C := Cmix) (eps := eps)
    hsol ht0 htT heps
  have hrnext : 2 * r0 - pExp = r1 := by dsimp [r0, r1]; ring
  rw [hrnext] at hinitialYoung
  have hexp : ∀ k < steps,
      0 < doublingExponent pExp r1 k ∧
        doublingExponent pExp r1 k ≤ pExp := by
    intro k hk
    have hk' : k + 1 < steps + 1 := Nat.add_lt_add_right hk 1
    have hpowlt : (2 : ℝ) ^ (k + 1) < (2 : ℝ) ^ (steps + 1) :=
      pow_lt_pow_right₀ (by norm_num) hk'
    have hd : 0 < 1 - p.m := by linarith
    have hformula : doublingExponent pExp r1 k =
        pExp + (2 : ℝ) ^ (k + 1) * (p.m - 1) := by
      dsimp [r1]
      exact doublingExponent_firstLevel pExp p.m k
    rw [hformula, hpdef]
    constructor
    · have hmul := mul_lt_mul_of_pos_right hpowlt hd
      nlinarith
    · have hpowpos : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hpowpos (by linarith : p.m - 1 ≤ 0)]
  have hiter := finite_descent_iterate
    (p := p) (T := T) (t := t) (pExp := pExp) (r0 := r1)
    (eps := eps) (C0 := C0) (steps := steps) (u := u) (v := v)
    hsol ht0 htT hbeta heps hC0 hexp
  have hterminal : doublingExponent pExp r1 steps = 0 := by
    have hformula : doublingExponent pExp r1 steps =
        pExp + (2 : ℝ) ^ (steps + 1) * (p.m - 1) := by
      dsimp [r1]
      exact doublingExponent_firstLevel pExp p.m steps
    rw [hformula, hpdef]
    ring
  rw [hterminal] at hiter
  let Cterminal := iteratedDescentCoeff p pExp r1 eps C0 steps
  let A := accumulatedDescentLower p pExp r1 eps C0 steps
  have hCt : 0 ≤ Cterminal := by
    dsimp [Cterminal]
    exact iteratedDescentCoeff_nonneg
      (p := p) (pExp := pExp) (r0 := r1) heps hC0 steps
  have hA : 0 ≤ A := by
    dsimp [A]
    exact accumulatedDescentLower_nonneg
      (p := p) (pExp := pExp) (r0 := r1) hbeta heps hC0 steps
  refine ⟨Cterminal, A, hCt, hA, ?_⟩
  calc
    p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        Cmix * descentMixed r0 p.β u v t := hinitialScalar
    _ ≤ eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        C0 * descentVGradient r1 (2 * p.β) u v t := by
      simpa [C0] using hinitialYoung
    _ ≤ eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        ((steps : ℝ) * eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        Cterminal * descentVGradient 0 (2 * p.β) u v t +
        A * ((∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ pExp) + 1)) := by
      simpa [Cterminal, A] using
        add_le_add_right hiter
          (eps * (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (pExp - 2) *
              |deriv (intervalDomainLift (u t)) x| ^ 2))
    _ = ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) *
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (pExp - 2) *
              |deriv (intervalDomainLift (u t)) x| ^ 2) +
        Cterminal * descentVGradient 0 (2 * p.β) u v t +
        A * ((∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ pExp) + 1) := by
      dsimp [eps]
      ring

end ShenWork.Paper2.IntervalDomainM
