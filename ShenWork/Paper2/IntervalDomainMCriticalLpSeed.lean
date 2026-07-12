import ShenWork.Paper2.IntervalDomainMSlowLpBound
import ShenWork.Paper2.IntervalDomainSharpCrossDiffusionBootstrap

/-!
# Critical `m = 1` seed for the faithful interval equation

This file formalizes Step 1 of the proof of Paper 2, Theorem 1.2(2).  The
elliptic equation is tested with the weight `(1 + v) ^ (-(2 * beta - 1))`.
For every exponent below `(2 * beta - 1) / chi`, the resulting coefficient
gap leaves a positive multiple of the weighted `u`-gradient energy.  The
uniform mass bound and the one-dimensional Agmon estimate then give a
uniform `L^p` seed.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

/-- The signed mixed term with an arbitrary signal weight. -/
def descentSignedMixed
    (r beta : ℝ) (u v : ℝ → intervalDomain.Point → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (r - 1) *
      deriv (intervalDomainLift (u t)) x *
      deriv (intervalDomainLift (v t)) x *
      (1 + intervalDomainLift (v t) x) ^ (-beta)

theorem descentSignedMixed_le_descentMixed
    {p : CM2Params} {T t r beta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    descentSignedMixed r beta u v t ≤ descentMixed r beta u v t := by
  unfold descentSignedMixed descentMixed
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
  have hsignedInt : IntervalIntegrable (fun x =>
      intervalDomainLift (u t) x ^ (r - 1) *
        deriv (intervalDomainLift (u t)) x *
        deriv (intervalDomainLift (v t)) x *
        (1 + intervalDomainLift (v t) x) ^ (-beta)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact ((((hU.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul hdU).mul hdV).mul
      ((continuousOn_const.add hV).rpow_const (fun x hx => Or.inl
        (ne_of_gt (show 0 < 1 + intervalDomainLift (v t) x by
          linarith [hVnonneg x hx])))))
  apply intervalIntegral.integral_mono_on (by norm_num)
    hsignedInt
    (descentMixed_intervalIntegrable hsol ht0 htT)
  intro x hx
  have hUposx := lift_u_pos_Icc hsol ht0 htT x hx
  have hVnonnegx := lift_v_nonneg_Icc hsol ht0 htT x hx
  have hweight : 0 ≤
      intervalDomainLift (u t) x ^ (r - 1) *
        (1 + intervalDomainLift (v t) x) ^ (-beta) :=
    mul_nonneg (Real.rpow_nonneg hUposx.le _)
      (Real.rpow_nonneg (by linarith) _)
  calc
    intervalDomainLift (u t) x ^ (r - 1) *
          deriv (intervalDomainLift (u t)) x *
          deriv (intervalDomainLift (v t)) x *
          (1 + intervalDomainLift (v t) x) ^ (-beta) =
        (intervalDomainLift (u t) x ^ (r - 1) *
          (1 + intervalDomainLift (v t) x) ^ (-beta)) *
          (deriv (intervalDomainLift (u t)) x *
            deriv (intervalDomainLift (v t)) x) := by ring
    _ ≤ (intervalDomainLift (u t) x ^ (r - 1) *
          (1 + intervalDomainLift (v t) x) ^ (-beta)) *
          |deriv (intervalDomainLift (u t)) x *
            deriv (intervalDomainLift (v t)) x| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hweight
    _ = intervalDomainLift (u t) x ^ (r - 1) *
          |deriv (intervalDomainLift (u t)) x| *
          |deriv (intervalDomainLift (v t)) x| *
          (1 + intervalDomainLift (v t) x) ^ (-beta) := by
      rw [abs_mul]
      ring

/-- Increasing the positive denominator exponent decreases the weighted
gradient integral because `1 + v >= 1`. -/
theorem descentVGradient_antitone_eta
    {p : CM2Params} {T t r eta₁ eta₂ : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (heta : eta₁ ≤ eta₂) :
    descentVGradient r eta₂ u v t ≤ descentVGradient r eta₁ u v t := by
  unfold descentVGradient
  apply intervalIntegral.integral_mono_on (by norm_num)
    (descentVGradient_intervalIntegrable hsol ht0 htT)
    (descentVGradient_intervalIntegrable hsol ht0 htT)
  intro x hx
  have hUpos := lift_u_pos_Icc hsol ht0 htT x hx
  have hVnonneg := lift_v_nonneg_Icc hsol ht0 htT x hx
  have hbase : 1 ≤ 1 + intervalDomainLift (v t) x := by linarith
  have hexp : -eta₂ ≤ -eta₁ := by linarith
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hbase hexp)
    (mul_nonneg (Real.rpow_nonneg hUpos.le r) (sq_nonneg _))

/-- The lower-order signal moment in the arbitrary-weight elliptic identity is
bounded by the corresponding `u` moment when the weight exponent is at least
one. -/
theorem elliptic_weighted_signal_moment_le
    {p : CM2Params} {T t r eta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (heta : 1 ≤ eta) :
    (∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ r * intervalDomainLift (v t) x *
        (1 + intervalDomainLift (v t) x) ^ (-eta)) ≤
      ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ r := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    simpa [U] using solution_lift_pos_Icc hsol ht
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    simpa [V] using lift_v_nonneg_Icc hsol ht0 htT
  have hUint : IntervalIntegrable (fun x => U x ^ r) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (solution_lift_continuousOn_Icc hsol ht).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hleft : IntervalIntegrable
      (fun x => U x ^ r * V x * (1 + V x) ^ (-eta)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    have hVcont := (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
    have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.add hVcont
    have hbasepow : ContinuousOn (fun x => (1 + V x) ^ (-eta))
        (Set.Icc (0 : ℝ) 1) :=
      hbase.rpow_const (fun x hx => Or.inl
        (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx])))
    exact (((solution_lift_continuousOn_Icc hsol ht).rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul hVcont).mul hbasepow
  have htheta : Theta_beta (eta - 1) ≤ 1 :=
    Theta_beta_le_one (by linarith)
  calc
    (∫ x in (0 : ℝ)..1, U x ^ r * V x * (1 + V x) ^ (-eta)) ≤
        ∫ x in (0 : ℝ)..1, U x ^ r :=
      intervalIntegral.integral_mono_on (by norm_num) hleft hUint
        (fun x hx => by
          have hpow : 0 ≤ U x ^ r := Real.rpow_nonneg (hUpos x hx).le _
          have hv := theta_sub_one_bound heta (hVnonneg x hx)
          calc
            U x ^ r * V x * (1 + V x) ^ (-eta) =
                U x ^ r * (V x * (1 + V x) ^ (-eta)) := by ring
            _ ≤ U x ^ r * Theta_beta (eta - 1) :=
              mul_le_mul_of_nonneg_left hv hpow
            _ ≤ U x ^ r * 1 :=
              mul_le_mul_of_nonneg_left htheta hpow
            _ = U x ^ r := by ring)
    _ = _ := by rfl

/-- The sharp elliptic estimate in Step 1 of the critical proof.  Its left
coefficient is positive enough precisely when `chi < (2 * beta - 1) / pExp`.
-/
theorem critical_elliptic_gradient_control
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hbeta : 1 ≤ p.β) (hp : 1 < pExp) (hchi : 0 < p.χ₀) :
    let eta := 2 * p.β - 1
    let J := descentVGradient pExp (2 * p.β) u v t
    let G := ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (pExp - 2) *
        |deriv (intervalDomainLift (u t)) x| ^ 2
    let Y := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp
    ((pExp - 1) * p.χ₀ * eta / pExp -
        (pExp - 1) * p.χ₀ ^ 2 / 2) * J ≤
      (pExp - 1) / 2 * G +
        ((pExp - 1) * p.χ₀ * p.μ / pExp) * Y := by
  dsimp only
  let eta : ℝ := 2 * p.β - 1
  let J : ℝ := descentVGradient pExp (2 * p.β) u v t
  let G : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (pExp - 2) *
      |deriv (intervalDomainLift (u t)) x| ^ 2
  let Y : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ pExp
  let S : ℝ := descentSignedMixed pExp eta u v t
  let A : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ pExp * intervalDomainLift (v t) x *
      (1 + intervalDomainLift (v t) x) ^ (-eta)
  let B : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (pExp + p.γ) *
      (1 + intervalDomainLift (v t) x) ^ (-eta)
  let C : ℝ := p.χ₀ * (pExp - 1)
  let eps : ℝ := (pExp - 1) / 2
  have hp0 : 0 < pExp := lt_trans zero_lt_one hp
  have hp1 : 0 < pExp - 1 := sub_pos.mpr hp
  have heta : 1 ≤ eta := by dsimp [eta]; linarith
  have hC : 0 < C := mul_pos hchi hp1
  have heps : 0 < eps := div_pos hp1 (by norm_num)
  have hJnonneg : 0 ≤ J := by
    dsimp [J]
    exact descentVGradient_nonneg_of_solution hsol ht0 htT
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (Real.rpow_nonneg
        (lift_u_pos_Icc hsol ht0 htT x hx).le _) (sq_nonneg _))
  have hYnonneg : 0 ≤ Y := by
    dsimp [Y]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (lift_u_pos_Icc hsol ht0 htT x hx).le _)
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (Real.rpow_nonneg
        (lift_u_pos_Icc hsol ht0 htT x hx).le _)
        (Real.rpow_nonneg (by
          have hv := lift_v_nonneg_Icc hsol ht0 htT x hx
          linarith) _))
  have hid := elliptic_multiplier_ibp_identity_eta
    (p := p) (T := T) (t := t) (r := pExp) (eta := eta)
      (u := u) (v := v) hsol ht0 htT
  change eta * descentVGradient pExp (eta + 1) u v t =
      pExp * S + p.μ * A - p.ν * B at hid
  have hJid : descentVGradient pExp (eta + 1) u v t = J := by
    dsimp [eta, J]
    congr 2
    ring
  rw [hJid] at hid
  have hscaled :
      (C * eta / pExp) * J =
        C * S + (C * p.μ / pExp) * A -
          (C * p.ν / pExp) * B := by
    calc
      (C * eta / pExp) * J = (C / pExp) * (eta * J) := by ring
      _ = (C / pExp) * (pExp * S + p.μ * A - p.ν * B) := by rw [hid]
      _ = C * S + (C * p.μ / pExp) * A -
          (C * p.ν / pExp) * B := by
        field_simp [ne_of_gt hp0]
  have hdrop :
      (C * eta / pExp) * J ≤ C * S + (C * p.μ / pExp) * A := by
    have hcoef : 0 ≤ C * p.ν / pExp :=
      div_nonneg (mul_nonneg hC.le p.hν.le) hp0.le
    have := mul_nonneg hcoef hBnonneg
    linarith
  have hS : S ≤ descentMixed pExp eta u v t := by
    dsimp [S]
    exact descentSignedMixed_le_descentMixed hsol ht0 htT
  have hCS : C * S ≤ eps * G +
      (C ^ 2 / (4 * eps)) *
        descentVGradient pExp (2 * eta) u v t := by
    calc
      C * S ≤ C * descentMixed pExp eta u v t :=
        mul_le_mul_of_nonneg_left hS hC.le
      _ ≤ eps * G + (C ^ 2 / (4 * eps)) *
          descentVGradient (2 * pExp - pExp) (2 * eta) u v t := by
        simpa [G] using descentMixed_young_beta
          (p := p) (T := T) (t := t) (pExp := pExp) (r := pExp)
          (C := C) (eps := eps) (beta := eta) (u := u) (v := v)
          hsol ht0 htT heps
      _ = eps * G + (C ^ 2 / (4 * eps)) *
          descentVGradient pExp (2 * eta) u v t := by ring
  have hJmono : descentVGradient pExp (2 * eta) u v t ≤ J := by
    dsimp [J, eta]
    apply descentVGradient_antitone_eta hsol ht0 htT
    linarith
  have hkNonneg : 0 ≤ C ^ 2 / (4 * eps) := by positivity
  have hCS' : C * S ≤ eps * G + (C ^ 2 / (4 * eps)) * J := by
    have hkmono := mul_le_mul_of_nonneg_left hJmono hkNonneg
    linarith
  have hA : A ≤ Y := by
    dsimp [A, Y]
    exact elliptic_weighted_signal_moment_le hsol ht0 htT heta
  have hAcoef : 0 ≤ C * p.μ / pExp :=
    div_nonneg (mul_nonneg hC.le p.hμ.le) hp0.le
  have hmain :
      (C * eta / pExp) * J ≤
        eps * G + (C ^ 2 / (4 * eps)) * J +
          (C * p.μ / pExp) * Y := by
    calc
      (C * eta / pExp) * J ≤ C * S + (C * p.μ / pExp) * A := hdrop
      _ ≤ (eps * G + (C ^ 2 / (4 * eps)) * J) +
          (C * p.μ / pExp) * Y :=
        add_le_add hCS' (mul_le_mul_of_nonneg_left hA hAcoef)
      _ = _ := by ring
  have hk : C ^ 2 / (4 * eps) = (pExp - 1) * p.χ₀ ^ 2 / 2 := by
    dsimp [C, eps]
    field_simp [ne_of_gt hp1]
    ring
  dsimp [C, eps, eta, J, G, Y] at hmain ⊢
  rw [hk] at hmain
  ring_nf at hmain ⊢
  linarith

/-- The first Young estimate in the critical weighted energy identity. -/
theorem critical_energy_cross_young
    {p : CM2Params} {T t pExp : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hm : p.m = 1) (hp : 1 < pExp) (hchi : 0 < p.χ₀) :
    p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
      (pExp - 1) / 2 *
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (pExp - 2) *
              |deriv (intervalDomainLift (u t)) x| ^ 2) +
        ((pExp - 1) * p.χ₀ ^ 2 / 2) *
          descentVGradient pExp (2 * p.β) u v t := by
  let C : ℝ := p.χ₀ * (pExp - 1)
  let eps : ℝ := (pExp - 1) / 2
  have hp1 : 0 < pExp - 1 := sub_pos.mpr hp
  have hC : 0 < C := mul_pos hchi hp1
  have heps : 0 < eps := div_pos hp1 (by norm_num)
  have habs := signedCross_abs_le_descentMixed
    (p := p) (T := T) (t := t) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT
  have hcross : lpSignedCrossIntegralM p pExp u v t ≤
      descentMixed pExp p.β u v t := by
    calc
      lpSignedCrossIntegralM p pExp u v t ≤
          |lpSignedCrossIntegralM p pExp u v t| := le_abs_self _
      _ ≤ descentMixed (pExp + p.m - 1) p.β u v t := habs
      _ = descentMixed pExp p.β u v t := by
        rw [hm]
        congr 2
        ring
  have hyoung := descentMixed_young
    (p := p) (T := T) (t := t) (pExp := pExp) (r := pExp)
      (C := C) (eps := eps) (u := u) (v := v) hsol ht0 htT heps
  have hmain : C * lpSignedCrossIntegralM p pExp u v t ≤
      eps * (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (pExp - 2) *
          |deriv (intervalDomainLift (u t)) x| ^ 2) +
        (C ^ 2 / (4 * eps)) *
          descentVGradient pExp (2 * p.β) u v t := by
    calc
      C * lpSignedCrossIntegralM p pExp u v t ≤
          C * descentMixed pExp p.β u v t :=
        mul_le_mul_of_nonneg_left hcross hC.le
      _ ≤ _ := by
        convert hyoung using 1 <;> ring
  have hk : C ^ 2 / (4 * eps) = (pExp - 1) * p.χ₀ ^ 2 / 2 := by
    dsimp [C, eps]
    field_simp [ne_of_gt hp1]
    ring
  dsimp [C, eps] at hmain ⊢
  rw [hk] at hmain
  exact hmain

/-- Autonomous `L^p` damping for every exponent in the critical seed range.
The constant is independent of time and of the maximal horizon. -/
theorem critical_lp_energy_damping
    {p : CM2Params} {T pExp : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hp : 1 < pExp)
    (hupper : p.χ₀ < (2 * p.β - 1) / pExp) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 < t → t < T →
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        intervalDomainLpEnergy pExp u t ≤ K := by
  let eta : ℝ := 2 * p.β - 1
  let D : ℝ := (pExp - 1) / 2
  let Acoef : ℝ := (pExp - 1) * p.χ₀ * eta / pExp
  let Bcoef : ℝ := (pExp - 1) * p.χ₀ ^ 2 / 2
  let Hcoef : ℝ := Acoef - Bcoef
  let cY : ℝ := (pExp - 1) * p.χ₀ * p.μ / pExp
  let theta : ℝ := Bcoef / Hcoef
  let delta : ℝ := D * (1 - theta)
  have hp0 : 0 < pExp := lt_trans zero_lt_one hp
  have hp1 : 0 < pExp - 1 := sub_pos.mpr hp
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hD : 0 < D := div_pos hp1 (by norm_num)
  have hBcoef : 0 < Bcoef := by
    dsimp [Bcoef]
    positivity
  have hgap : 0 < Hcoef - Bcoef := by
    have hsmall : 0 < eta / pExp - p.χ₀ := by
      dsimp [eta] at hupper ⊢
      linarith
    have heq : Hcoef - Bcoef =
        (pExp - 1) * p.χ₀ * (eta / pExp - p.χ₀) := by
      dsimp [Hcoef, Acoef, Bcoef]
      ring
    rw [heq]
    positivity
  have hHcoef : 0 < Hcoef := lt_trans hBcoef (sub_pos.mp hgap)
  have htheta : 0 < theta := div_pos hBcoef hHcoef
  have htheta1 : theta < 1 := by
    rw [div_lt_one hHcoef]
    linarith
  have hdelta : 0 < delta :=
    mul_pos hD (sub_pos.mpr htheta1)
  have hcY : 0 ≤ cY := by
    dsimp [cY]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hp1.le hchi.le) p.hμ.le) hp0.le
  obtain ⟨Cmass, hCmass, hmass⟩ :=
    uniform_mass_bound_of_guard hguard hu₀ hsol htrace
  let Bmain : ℝ := p.a + cY + 1
  have hBmain : 0 < Bmain := by
    dsimp [Bmain]
    linarith [p.ha, hcY]
  obtain ⟨Cagmon, hCagmon, hagmon⟩ :=
    unitIntervalPositiveAgmonInterpolation pExp hp (delta / Bmain)
      (div_pos hdelta hBmain)
  let K : ℝ := Bmain * Cagmon * Cmass ^ pExp
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hBmain.le hCagmon.le)
      (Real.rpow_nonneg hCmass _)
  refine ⟨K, hK, ?_⟩
  intro t ht0 htT
  let Y : ℝ := intervalDomainLpEnergy pExp u t
  let G : ℝ := intervalDomainLpWeightedGradientDissipation pExp u t
  let J : ℝ := descentVGradient pExp (2 * p.β) u v t
  let Z : ℝ := intervalDomain.integral (fun x => (u t x) ^ (pExp + p.α))
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hYeq : Y = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ pExp := by
    dsimp [Y]
    exact lpEnergy_eq_lift_power_of_solution hsol ht0 htT
  have hGeq : G = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (pExp - 2) *
        |deriv (intervalDomainLift (u t)) x| ^ 2 := by
    dsimp [G]
    exact weightedDissipation_eq_lift pExp u t
  have hYdomain : Y =
      intervalDomain.integral (fun x => (u t x) ^ pExp) := by
    rw [hYeq]
    exact (intervalDomain_integral_rpow_eq_lift_integral
      (q := pExp) (f := u t)).symm
  have hYnonneg : 0 ≤ Y := by
    rw [hYeq]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hGnonneg : 0 ≤ G := by
    rw [hGeq]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg
        (Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
        (sq_nonneg _))
  have hJnonneg : 0 ≤ J := by
    dsimp [J]
    exact descentVGradient_nonneg_of_solution hsol ht0 htT
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z]
    unfold intervalDomain intervalDomainIntegral
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      simp only [intervalDomainLift, hx, dif_pos]
      exact Real.rpow_nonneg (u_pos hsol ht0 htT ⟨x, hx⟩).le _)
  have hell := critical_elliptic_gradient_control
    (p := p) (T := T) (t := t) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT hbeta hp hchi
  dsimp only at hell
  rw [← hGeq, ← hYeq] at hell
  change Hcoef * J ≤ D * G + cY * Y at hell
  have hthetaH : theta * Hcoef = Bcoef := by
    dsimp [theta]
    field_simp [ne_of_gt hHcoef]
  have hBJ : Bcoef * J ≤ theta * D * G + cY * Y := by
    have hmul := mul_le_mul_of_nonneg_left hell htheta.le
    have htheta_le : theta ≤ 1 := htheta1.le
    have hcYY : 0 ≤ cY * Y := mul_nonneg hcY hYnonneg
    calc
      Bcoef * J = theta * (Hcoef * J) := by rw [← hthetaH]; ring
      _ ≤ theta * (D * G + cY * Y) := hmul
      _ = theta * D * G + theta * (cY * Y) := by ring
      _ ≤ theta * D * G + cY * Y := by
        have hthetaCY : theta * (cY * Y) ≤ cY * Y := by
          simpa using mul_le_mul_of_nonneg_right htheta_le hcYY
        linarith
  have hcross := critical_energy_cross_young
    (p := p) (T := T) (t := t) (pExp := pExp) (u := u) (v := v)
      hsol ht0 htT hm hp hchi
  rw [← hGeq] at hcross
  change p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
      D * G + Bcoef * J at hcross
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := pExp)
      (u := u) (v := v) (ne_of_gt hp0) hsol ht0 htT
  rw [← hYdomain] at henergy
  change (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
      (pExp - 1) * G + p.b * Z =
        p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t +
          p.a * Y at henergy
  have hbZ : 0 ≤ p.b * Z := mul_nonneg p.hb hZnonneg
  have hpre :
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        delta * G ≤ (p.a + cY) * Y := by
    dsimp [delta]
    dsimp [D] at hcross hBJ ⊢
    nlinarith
  have hmass_t : intervalDomain.integral (u t) ≤ Cmass :=
    hmass t ht0 htT
  have hmass_nonneg : 0 ≤ intervalDomain.integral (u t) :=
    (mass_pos hsol ht).le
  have hmass_pow : (intervalDomain.integral (u t)) ^ pExp ≤
      Cmass ^ pExp :=
    Real.rpow_le_rpow hmass_nonneg hmass_t hp0.le
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hag := hagmon (u t) (fun x => u_pos hsol ht0 htT x) hC2
  have hag' : Y ≤ (delta / Bmain) * G +
      Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
    rw [hYdomain]
    simpa [G, intervalDomainLpWeightedGradientDissipation] using hag
  have habsorb : Bmain * Y ≤ delta * G +
      Bmain * Cagmon * Cmass ^ pExp := by
    have hmul := mul_le_mul_of_nonneg_left hag' hBmain.le
    have hpowmul := mul_le_mul_of_nonneg_left hmass_pow
      (mul_nonneg hBmain.le hCagmon.le)
    calc
      Bmain * Y ≤ Bmain * ((delta / Bmain) * G +
          Cagmon * (intervalDomain.integral (u t)) ^ pExp) := hmul
      _ = delta * G +
          Bmain * Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
        field_simp [ne_of_gt hBmain]
      _ ≤ delta * G + Bmain * Cagmon * Cmass ^ pExp := by
        linarith
  dsimp [Y] at hpre habsorb ⊢
  dsimp [K, Bmain]
  nlinarith

/-- Every exponent in the critical seed range is uniformly bounded on the
maximal interval. -/
theorem critical_lp_power_bounded_before
    {p : CM2Params} {T pExp : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hp : 1 < pExp)
    (hupper : p.χ₀ < (2 * p.β - 1) / pExp) :
    LpPowerBoundedBefore intervalDomainM pExp T u := by
  obtain ⟨K, hK, hdamp⟩ := critical_lp_energy_damping
    hguard hu₀ hsol htrace hbeta hm hchi hp hupper
  let E : ℝ → ℝ := fun s => intervalDomainLpEnergy pExp u s
  have hEcont : ContinuousOn E (Set.Ioo (0 : ℝ) T) := by
    intro s hs
    exact (lpEnergy_hasDerivAt_of_solution hsol hs.1 hs.2).continuousAt.continuousWithinAt
  have hEderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T, K < E s →
      ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt E d s := by
    intro s hs hKs
    have hD := hdamp s hs.1 hs.2
    have hp0 : 0 < pExp := lt_trans zero_lt_one hp
    refine ⟨deriv E s, ?_, ?_⟩
    · dsimp [E] at hD ⊢
      have hinv : 0 < 1 / pExp := one_div_pos.mpr hp0
      nlinarith
    · simpa [E] using lpEnergy_hasDerivAt_of_solution hsol hs.1 hs.2
  obtain ⟨δ, hδ, htraceδ⟩ := htrace 1 (by norm_num)
  have hu0bdd :
      BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) := by
    simpa [intervalDomainM] using hu₀.admissible.1
  obtain ⟨M₀, hM₀⟩ := hu0bdd
  let R : ℝ := max 0 M₀ + 1
  have hM₀nonneg : 0 ≤ M₀ := by
    let x₀ : intervalDomainPoint :=
      ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    have hx := hM₀ ⟨x₀, rfl⟩
    exact (abs_nonneg (u₀ x₀)).trans hx
  have hR : 0 < R := by
    dsimp [R]
    linarith [le_max_left (0 : ℝ) M₀]
  have hinitial : ∀ s, 0 < s → s < δ → s < T → E s ≤ R ^ pExp := by
    intro s hs0 hsδ hsT
    have hs : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
    have hdiffBdd := bddAbove_range_abs_diff_of_bddAbove
      (solution_slice_abs_bddAbove hsol hs)
      (by simpa [intervalDomainM] using hu₀.admissible.1)
    have hsup : intervalDomain.supNorm (fun x => u s x - u₀ x) < 1 := by
      simpa [intervalDomainM, intervalDomain] using htraceδ s hs0 hsδ
    have hpoint : ∀ x : intervalDomain.Point, u s x ≤ R := by
      intro x
      have hdiff : |u s x - u₀ x| ≤
          intervalDomain.supNorm (fun y => u s y - u₀ y) := by
        change |u s x - u₀ x| ≤
          intervalDomainSupNorm (fun y => u s y - u₀ y)
        unfold intervalDomainSupNorm
        exact le_csSup hdiffBdd ⟨x, rfl⟩
      have hu₀x : |u₀ x| ≤ M₀ := hM₀ ⟨x, rfl⟩
      have htri : u s x ≤ |u s x - u₀ x| + |u₀ x| := by
        calc
          u s x = (u s x - u₀ x) + u₀ x := by ring
          _ ≤ |u s x - u₀ x| + |u₀ x| :=
            add_le_add (le_abs_self _) (le_abs_self _)
      dsimp [R]
      linarith [lt_of_le_of_lt hdiff hsup, le_max_right (0 : ℝ) M₀]
    have hint : IntervalIntegrable
        (fun x => intervalDomainLift (u s) x ^ pExp) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact power_continuousOn_timeSlice (q := pExp) hsol hs
    rw [show E s = ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u s) x ^ pExp by
      dsimp [E]
      exact lpEnergy_eq_lift_power_of_solution hsol hs0 hsT]
    calc
      (∫ x in (0 : ℝ)..1, intervalDomainLift (u s) x ^ pExp) ≤
          ∫ _x in (0 : ℝ)..1, R ^ pExp :=
        intervalIntegral.integral_mono_on (by norm_num) hint
          intervalIntegrable_const (fun x hx => by
            have hpos := solution_lift_pos_Icc hsol hs x hx
            have hle : intervalDomainLift (u s) x ≤ R := by
              simpa [intervalDomainLift, hx] using
                hpoint (⟨x, hx⟩ : intervalDomain.Point)
            exact Real.rpow_le_rpow hpos.le hle
              (le_of_lt (lt_trans zero_lt_one hp)))
      _ = R ^ pExp := by
        rw [intervalIntegral.integral_const]
        norm_num [smul_eq_mul]
  let C : ℝ := max K (R ^ pExp)
  refine ⟨C, ?_⟩
  intro t ht0 htT
  have hEt : E t ≤ C := by
    by_cases hle : E t ≤ K
    · exact hle.trans (le_max_left _ _)
    · push Not at hle
      have habove : ∀ s ∈ Set.Ioc (0 : ℝ) t, K < E s :=
        threshold_persists_below_of_hasDerivAt_nonpos
          ht0 htT hEcont hEderiv hle
      let s : ℝ := min (δ / 2) (t / 2)
      have hs0 : 0 < s := lt_min (by linarith) (by linarith)
      have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hst : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hsT : s < T := lt_trans hst htT
      have hsubIoo : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T := fun z hz =>
        ⟨lt_of_lt_of_le hs0 hz.1, lt_of_le_of_lt hz.2 htT⟩
      have hsubIoc : Set.Ioo s t ⊆ Set.Ioc (0 : ℝ) t := fun z hz =>
        ⟨lt_trans hs0 hz.1, hz.2.le⟩
      have hanti : AntitoneOn E (Set.Icc s t) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          (hEcont.mono hsubIoo)
        · intro z hz
          rw [interior_Icc] at hz
          exact (lpEnergy_hasDerivAt_of_solution hsol
            (lt_trans hs0 hz.1) (lt_trans hz.2 htT)).differentiableAt.differentiableWithinAt
        · intro z hz
          rw [interior_Icc] at hz
          have hzIoo : z ∈ Set.Ioo (0 : ℝ) T :=
            ⟨lt_trans hs0 hz.1, lt_trans hz.2 htT⟩
          obtain ⟨d, hd, hD⟩ := hEderiv z hzIoo (habove z (hsubIoc hz))
          rw [hD.deriv]
          exact hd
      have hEtEs : E t ≤ E s :=
        hanti (Set.left_mem_Icc.mpr hst.le)
          (Set.right_mem_Icc.mpr hst.le) hst.le
      exact (hEtEs.trans (hinitial s hs0 hsδ hsT)).trans (le_max_right _ _)
  have hdomain : intervalDomainM.integral (fun x => (u t x) ^ pExp) = E t := by
    change intervalDomain.integral (fun x => (u t x) ^ pExp) = E t
    rw [show E t = ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ pExp by
      dsimp [E]
      exact lpEnergy_eq_lift_power_of_solution hsol ht0 htT]
    exact intervalDomain_integral_rpow_eq_lift_integral
  rw [hdomain]
  exact hEt

/-- The printed critical threshold leaves a nonempty interval of admissible
seed exponents above the Corollary 2.1 threshold. -/
theorem exists_critical_seed_exponent
    (p : CM2Params) (hbeta : 1 ≤ p.β)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    ∃ pExp : ℝ,
      max 1 (p.γ * (p.N : ℝ) / 2) < pExp ∧
        pExp < (2 * p.β - 1) / p.χ₀ := by
  let eta : ℝ := 2 * p.β - 1
  let q : ℝ := p.γ * (p.N : ℝ)
  let d : ℝ := max 2 q
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hq : 0 < q := by
    dsimp [q]
    exact mul_pos p.hγ (by exact_mod_cast p.hN)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hthreshold' : p.χ₀ < 2 * eta / d := by
    simpa [chiBeta, eta, q, d] using hthreshold
  have hchid : p.χ₀ * d < 2 * eta :=
    (lt_div_iff₀ hd).mp hthreshold'
  have hdhalf : d / 2 < eta / p.χ₀ := by
    rw [div_lt_div_iff₀ (by norm_num) hchi]
    nlinarith
  have hmaxeq : d / 2 = max 1 (q / 2) := by
    by_cases hq2 : q ≤ 2
    · have hdEq : d = 2 := by simp [d, max_eq_left hq2]
      have hqhalf : q / 2 ≤ 1 := by linarith
      rw [hdEq, max_eq_left hqhalf]
      norm_num
    · have h2q : 2 ≤ q := (lt_of_not_ge hq2).le
      have hdEq : d = q := by simp [d, max_eq_right h2q]
      have hqhalf : 1 ≤ q / 2 := by linarith
      rw [hdEq, max_eq_right hqhalf]
  let lower : ℝ := max 1 (q / 2)
  let upper : ℝ := eta / p.χ₀
  let pExp : ℝ := (lower + upper) / 2
  have hlu : lower < upper := by
    dsimp [lower, upper]
    rw [← hmaxeq]
    exact hdhalf
  refine ⟨pExp, ?_, ?_⟩
  · dsimp [pExp]
    dsimp [lower, q]
    linarith
  · dsimp [pExp]
    dsimp [upper, eta]
    dsimp [lower, q] at hlu
    linarith

/-- A faithful critical solution with positive sensitivity has an `L^p` seed
strictly above the bootstrap threshold. -/
theorem exists_high_critical_lp_power_bounded_before
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    ∃ pExp : ℝ,
      max 1 (p.γ * (p.N : ℝ) / 2) < pExp ∧
        LpPowerBoundedBefore intervalDomainM pExp T u := by
  obtain ⟨pExp, hpLower, hpUpper⟩ :=
    exists_critical_seed_exponent p hbeta hchi hthreshold
  have hp : 1 < pExp := lt_of_le_of_lt (le_max_left _ _) hpLower
  have hp0 : 0 < pExp := lt_trans zero_lt_one hp
  have hupper : p.χ₀ < (2 * p.β - 1) / pExp := by
    rw [lt_div_iff₀ hp0]
    have hmul := (lt_div_iff₀ hchi).mp hpUpper
    nlinarith
  refine ⟨pExp, hpLower, ?_⟩
  exact critical_lp_power_bounded_before
    hguard hu₀ hsol htrace hbeta hm hchi hp hupper

/-- At `m = 1`, a faithful classical solution is a classical solution for the
legacy linear-flux interval domain. -/
theorem classicalSolution_intervalDomain_of_m_eq_one
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : p.m = 1)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v) :
    IsPaper2ClassicalSolution intervalDomain p T u v := by
  simpa [IsPaper2ClassicalSolution, intervalDomainM, intervalDomain,
    intervalDomainChemotaxisDivM, intervalDomainChemotaxisDiv, hm] using hsol

theorem crossDiffusionBootstrapEstimate_intervalDomainM_of_m_eq_one
    {p : CM2Params} {T rho : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : p.m = 1)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain p T rho u v) :
    CrossDiffusionBootstrapEstimate intervalDomainM p T rho u v := by
  intro eps heps pExp hpExp
  obtain ⟨Ceps, hCeps⟩ := hcross eps heps pExp hpExp
  refine ⟨Ceps, ?_⟩
  intro t ht0 htT
  have hterm :
      intervalDomainCrossDiffusionEnergyTermM p pExp (u t) (v t) =
        intervalDomainCrossDiffusionEnergyTerm p pExp (u t) (v t) := by
    unfold intervalDomainCrossDiffusionEnergyTermM
      intervalDomainCrossDiffusionEnergyTerm
    apply intervalIntegral.integral_congr
    intro x _hx
    rw [hm]
    congr 2
    ring
  simpa [intervalDomainM, intervalDomain, hterm] using hCeps t ht0 htT

/-- The sharp `rho = gamma` cross-diffusion estimate transported to the
faithful domain in the critical `m = 1` case. -/
theorem critical_crossDiffusionBootstrapEstimate_sharp
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hm : p.m = 1) (hbeta : 1 ≤ p.β) :
    CrossDiffusionBootstrapEstimate intervalDomainM p T p.γ u v := by
  apply crossDiffusionBootstrapEstimate_intervalDomainM_of_m_eq_one hm
  exact intervalDomain_crossDiffusionBootstrapEstimate_sharp
    (classicalSolution_intervalDomain_of_m_eq_one hm hsol) hbeta

/-- Complete positive-sensitivity critical bootstrap seed: the sharp
cross-diffusion estimate and an initial power above its dimensional threshold.
-/
theorem critical_bootstrap_seed_positive
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hchi : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p) :
    CrossDiffusionBootstrapEstimate intervalDomainM p T p.γ u v ∧
      ∃ p0 > max 1 (p.γ * (p.N : ℝ) / 2),
        LpPowerBoundedBefore intervalDomainM p0 T u := by
  refine ⟨critical_crossDiffusionBootstrapEstimate_sharp hsol hm hbeta, ?_⟩
  obtain ⟨p0, hp0, hLp⟩ := exists_high_critical_lp_power_bounded_before
    hguard hu₀ hsol htrace hbeta hm hchi hthreshold
  exact ⟨p0, hp0, hLp⟩

#print axioms critical_lp_power_bounded_before
#print axioms exists_high_critical_lp_power_bounded_before
#print axioms critical_crossDiffusionBootstrapEstimate_sharp
#print axioms critical_bootstrap_seed_positive

end ShenWork.Paper2.IntervalDomainM
