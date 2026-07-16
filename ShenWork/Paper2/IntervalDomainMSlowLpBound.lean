import ShenWork.Paper2.IntervalDomainMFiniteDescent
import ShenWork.PDE.IntervalAgmonInterpolation

/-!
# Uniform finite-Lp bound in the slow diffusion regime

This file completes the a-priori estimate behind the amended slow branch of
Theorem 1.2 for the faithful interval model.  The power-of-two descent leaves
one terminal weighted resolver-gradient integral.  At exponent zero that
integral is bounded directly by the elliptic logarithmic-gradient estimate.
The remaining positive fraction of the diffusion dissipation absorbs every
lower-order power by the proved unit-interval Agmon inequality.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

/-- The terminal resolver-gradient term in the finite descent is bounded by
the elliptic reaction coefficient. -/
theorem descentVGradient_zero_le_mu
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hbeta : 1 ≤ p.β) :
    descentVGradient 0 (2 * p.β) u v t ≤ p.μ := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    intro x hx
    simpa [V, intervalDomainLift, hx] using
      hsol.v_nonneg (x := (⟨x, hx⟩ : intervalDomain.Point)) ht0 htT
  have hlog : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv V x| ≤ Real.sqrt p.μ * V x := by
    simpa [V] using elliptic_log_gradient_bound hsol ht0 htT
  have hint : IntervalIntegrable (fun x =>
      intervalDomainLift (u t) x ^ (0 : ℝ) * |deriv V x| ^ 2 *
        (1 + V x) ^ (-(2 * p.β))) volume 0 1 := by
    simpa [V] using
      descentVGradient_intervalIntegrable
        (r := (0 : ℝ)) (eta := 2 * p.β) hsol ht0 htT
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x ^ (0 : ℝ) * |deriv V x| ^ 2 *
          (1 + V x) ^ (-(2 * p.β)) ≤ p.μ := by
    intro x hx
    have hB : 1 ≤ 1 + V x := by linarith [hVnonneg x hx]
    have hBpos : 0 < 1 + V x := lt_of_lt_of_le zero_lt_one hB
    have hsqrt : (Real.sqrt p.μ) ^ 2 = p.μ := Real.sq_sqrt p.hμ.le
    have hsq : |deriv V x| ^ 2 ≤ p.μ * V x ^ 2 := by
      have hnonneg : 0 ≤ |deriv V x| := abs_nonneg _
      have hright : 0 ≤ Real.sqrt p.μ * V x :=
        mul_nonneg (Real.sqrt_nonneg _) (hVnonneg x hx)
      have hraw : |deriv V x| ^ 2 ≤ (Real.sqrt p.μ * V x) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hnonneg (hlog x hx)
      calc
        |deriv V x| ^ 2 ≤ (Real.sqrt p.μ * V x) ^ 2 := hraw
        _ = p.μ * V x ^ 2 := by rw [mul_pow, hsqrt]
    have hVleB : V x ≤ 1 + V x := by linarith
    have hVsq : V x ^ 2 ≤ (1 + V x) ^ (2 : ℝ) := by
      simpa only [Real.rpow_two, pow_two] using
        mul_self_le_mul_self (hVnonneg x hx) hVleB
    have hpow : (1 + V x) ^ (2 : ℝ) ≤
        (1 + V x) ^ (2 * p.β) := by
      exact Real.rpow_le_rpow_of_exponent_le hB (by nlinarith)
    have hratio : V x ^ 2 * (1 + V x) ^ (-(2 * p.β)) ≤ 1 := by
      rw [Real.rpow_neg hBpos.le]
      rw [← div_eq_mul_inv]
      exact (div_le_one (Real.rpow_pos_of_pos hBpos _)).2 (hVsq.trans hpow)
    have hweight : 0 ≤ (1 + V x) ^ (-(2 * p.β)) :=
      Real.rpow_nonneg hBpos.le _
    have hmul := mul_le_mul_of_nonneg_right hsq hweight
    have hμ : 0 ≤ p.μ := p.hμ.le
    calc
      intervalDomainLift (u t) x ^ (0 : ℝ) * |deriv V x| ^ 2 *
          (1 + V x) ^ (-(2 * p.β))
          = |deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β)) := by
              rw [Real.rpow_zero, one_mul]
      _ ≤ (p.μ * V x ^ 2) * (1 + V x) ^ (-(2 * p.β)) := hmul
      _ = p.μ * (V x ^ 2 * (1 + V x) ^ (-(2 * p.β))) := by ring
      _ ≤ p.μ * 1 := mul_le_mul_of_nonneg_left hratio hμ
      _ = p.μ := mul_one _
  unfold descentVGradient
  change (∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (0 : ℝ) * |deriv V x| ^ 2 *
        (1 + V x) ^ (-(2 * p.β))) ≤ p.μ
  calc
    _ ≤ ∫ _x in (0 : ℝ)..1, p.μ :=
      intervalIntegral.integral_mono_on (by norm_num) hint
        intervalIntegrable_const hpoint
    _ = p.μ := by
      rw [intervalIntegral.integral_const]
      norm_num [smul_eq_mul]

/-- The complete finite descent after bounding its terminal exponent-zero
term.  Only the target power and a constant remain besides the absorbable
fraction of the diffusion dissipation. -/
theorem slow_cross_finite_descent_closed
    {p : CM2Params} {T t pExp : ℝ} {steps : ℕ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1)
    (hpdef : pExp = (2 : ℝ) ^ (steps + 1) * (1 - p.m))
    (hp : 1 < pExp) :
    ∃ A, 0 ≤ A ∧
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) *
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (pExp - 2) *
              |deriv (intervalDomainLift (u t)) x| ^ 2) +
        A * ((∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ pExp) + 1) := by
  obtain ⟨Cterminal, A, hCt, hA, hdescent⟩ :=
    slow_cross_finite_descent hsol ht0 htT hbeta hm1 hpdef hp
  let Y : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp
  let Afinal : ℝ := A + Cterminal * p.μ
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hAfinal : 0 ≤ Afinal := by
    dsimp [Afinal]
    exact add_nonneg hA (mul_nonneg hCt p.hμ.le)
  refine ⟨Afinal, hAfinal, ?_⟩
  have hterm := mul_le_mul_of_nonneg_left
    (descentVGradient_zero_le_mu hsol ht0 htT hbeta) hCt
  have hterm' : Cterminal * descentVGradient 0 (2 * p.β) u v t ≤
      Cterminal * p.μ * (Y + 1) := by
    calc
      Cterminal * descentVGradient 0 (2 * p.β) u v t
          ≤ Cterminal * p.μ := hterm
      _ ≤ Cterminal * p.μ * (Y + 1) := by
        have hcmu : 0 ≤ Cterminal * p.μ := mul_nonneg hCt p.hμ.le
        nlinarith
  dsimp [Afinal, Y]
  calc
    p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) *
            (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (pExp - 2) *
                |deriv (intervalDomainLift (u t)) x| ^ 2) +
          Cterminal * descentVGradient 0 (2 * p.β) u v t +
          A * ((∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ pExp) + 1) := hdescent
    _ ≤ ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) *
            (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (pExp - 2) *
                |deriv (intervalDomainLift (u t)) x| ^ 2) +
          Cterminal * p.μ * ((∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ pExp) + 1) +
          A * ((∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ pExp) + 1) := by
      dsimp [Y] at hterm'
      linarith
    _ = ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) *
            (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (pExp - 2) *
                |deriv (intervalDomainLift (u t)) x| ^ 2) +
          (A + Cterminal * p.μ) * ((∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ pExp) + 1) := by ring

/-! The explicit coefficients below make the descent estimate uniform in
time.  Their values are immaterial to the theorem, but exposing them avoids
placing an existential coefficient inside the time quantifier. -/

def slowDescentEps (pExp : ℝ) (steps : ℕ) : ℝ :=
  (pExp - 1) / ((steps : ℝ) + 2)

def slowDescentFirstExponent (p : CM2Params) (pExp : ℝ) : ℝ :=
  pExp + 2 * (p.m - 1)

def slowDescentInitialCoeff (p : CM2Params) (pExp : ℝ) : ℝ :=
  |p.χ₀| * (pExp - 1)

def slowDescentYoungCoeff (p : CM2Params) (pExp : ℝ) (steps : ℕ) : ℝ :=
  slowDescentInitialCoeff p pExp ^ 2 / (4 * slowDescentEps pExp steps)

def slowDescentTerminalCoeff
    (p : CM2Params) (pExp : ℝ) (steps : ℕ) : ℝ :=
  iteratedDescentCoeff p pExp (slowDescentFirstExponent p pExp)
    (slowDescentEps pExp steps) (slowDescentYoungCoeff p pExp steps) steps

def slowDescentAccumulatedCoeff
    (p : CM2Params) (pExp : ℝ) (steps : ℕ) : ℝ :=
  accumulatedDescentLower p pExp (slowDescentFirstExponent p pExp)
    (slowDescentEps pExp steps) (slowDescentYoungCoeff p pExp steps) steps

def slowDescentClosedCoeff
    (p : CM2Params) (pExp : ℝ) (steps : ℕ) : ℝ :=
  slowDescentAccumulatedCoeff p pExp steps +
    slowDescentTerminalCoeff p pExp steps * p.μ

/-- Uniform-in-time form of the closed finite descent. -/
theorem slow_cross_finite_descent_closed_uniform
    {p : CM2Params} {T pExp : ℝ} {steps : ℕ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1)
    (hpdef : pExp = (2 : ℝ) ^ (steps + 1) * (1 - p.m))
    (hp : 1 < pExp) :
    0 ≤ slowDescentClosedCoeff p pExp steps ∧
      ∀ t, 0 < t → t < T →
        p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
          ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) *
            (∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ (pExp - 2) *
                |deriv (intervalDomainLift (u t)) x| ^ 2) +
          slowDescentClosedCoeff p pExp steps *
            ((∫ x in (0 : ℝ)..1,
              intervalDomainLift (u t) x ^ pExp) + 1) := by
  let eps := slowDescentEps pExp steps
  let Cmix := slowDescentInitialCoeff p pExp
  let r0 := pExp + p.m - 1
  let r1 := slowDescentFirstExponent p pExp
  let C0 := slowDescentYoungCoeff p pExp steps
  let Cterminal := slowDescentTerminalCoeff p pExp steps
  let A := slowDescentAccumulatedCoeff p pExp steps
  have heps : 0 < eps := by
    dsimp [eps, slowDescentEps]
    exact div_pos (by linarith) (by positivity)
  have hCmix : 0 ≤ Cmix := by
    dsimp [Cmix, slowDescentInitialCoeff]
    exact mul_nonneg (abs_nonneg _) (by linarith)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0, slowDescentYoungCoeff]
    positivity
  have hCt : 0 ≤ Cterminal := by
    dsimp [Cterminal, slowDescentTerminalCoeff]
    exact iteratedDescentCoeff_nonneg
      (p := p) (pExp := pExp)
      (r0 := slowDescentFirstExponent p pExp) heps hC0 steps
  have hA : 0 ≤ A := by
    dsimp [A, slowDescentAccumulatedCoeff]
    exact accumulatedDescentLower_nonneg
      (p := p) (pExp := pExp)
      (r0 := slowDescentFirstExponent p pExp) hbeta heps hC0 steps
  have hclosed : 0 ≤ slowDescentClosedCoeff p pExp steps := by
    unfold slowDescentClosedCoeff
    exact add_nonneg hA (mul_nonneg hCt p.hμ.le)
  refine ⟨hclosed, ?_⟩
  intro t ht0 htT
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
      dsimp [Cmix, slowDescentInitialCoeff, r0]
      exact mul_le_mul_of_nonneg_left hsigned
        (mul_nonneg (abs_nonneg _) (by linarith))
    exact (le_abs_self _).trans habs
  have hinitialYoung := descentMixed_young
    (pExp := pExp) (r := r0) (C := Cmix) (eps := eps)
    hsol ht0 htT heps
  have hrnext : 2 * r0 - pExp = r1 := by
    dsimp [r0, r1, slowDescentFirstExponent]
    ring
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
      dsimp [r1, slowDescentFirstExponent]
      exact doublingExponent_firstLevel pExp p.m k
    rw [hformula, hpdef]
    constructor
    · have hmul := mul_lt_mul_of_pos_right hpowlt hd
      nlinarith
    · have hpowpos : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hpowpos
        (by linarith : p.m - 1 ≤ 0)]
  have hiter := finite_descent_iterate
    (p := p) (T := T) (t := t) (pExp := pExp) (r0 := r1)
    (eps := eps) (C0 := C0) (steps := steps) (u := u) (v := v)
    hsol ht0 htT hbeta heps hC0 hexp
  have hterminal : doublingExponent pExp r1 steps = 0 := by
    have hformula : doublingExponent pExp r1 steps =
        pExp + (2 : ℝ) ^ (steps + 1) * (p.m - 1) := by
      dsimp [r1, slowDescentFirstExponent]
      exact doublingExponent_firstLevel pExp p.m steps
    rw [hformula, hpdef]
    ring
  rw [hterminal] at hiter
  have hterm := mul_le_mul_of_nonneg_left
    (descentVGradient_zero_le_mu hsol ht0 htT hbeta) hCt
  let Y : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ pExp
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hterm' : Cterminal * descentVGradient 0 (2 * p.β) u v t ≤
      Cterminal * p.μ * (Y + 1) := by
    calc
      Cterminal * descentVGradient 0 (2 * p.β) u v t
          ≤ Cterminal * p.μ := hterm
      _ ≤ Cterminal * p.μ * (Y + 1) := by
        have hcmu : 0 ≤ Cterminal * p.μ := mul_nonneg hCt p.hμ.le
        nlinarith
  have hfirst :
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        C0 * descentVGradient r1 (2 * p.β) u v t := by
    calc
      _ ≤ Cmix * descentMixed r0 p.β u v t := hinitialScalar
      _ ≤ _ := by simpa [C0, slowDescentYoungCoeff] using hinitialYoung
  have hiter' :
      C0 * descentVGradient r1 (2 * p.β) u v t ≤
        (steps : ℝ) * eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        Cterminal * descentVGradient 0 (2 * p.β) u v t +
        A * (Y + 1) := by
    simpa [Cterminal, A, Y, slowDescentTerminalCoeff,
      slowDescentAccumulatedCoeff] using hiter
  have hcombined :
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        ((steps : ℝ) + 1) * eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        Cterminal * descentVGradient 0 (2 * p.β) u v t +
        A * (Y + 1) := by
    linarith
  have hclosedTerm :
      Cterminal * descentVGradient 0 (2 * p.β) u v t + A * (Y + 1) ≤
        (A + Cterminal * p.μ) * (Y + 1) := by
    nlinarith [hterm']
  calc
    p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        ((steps : ℝ) + 1) * eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        Cterminal * descentVGradient 0 (2 * p.β) u v t +
        A * (Y + 1) := hcombined
    _ ≤ ((steps : ℝ) + 1) * eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (pExp - 2) *
            |deriv (intervalDomainLift (u t)) x| ^ 2) +
        (A + Cterminal * p.μ) * (Y + 1) :=
      by linarith
    _ = ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) *
          (∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ (pExp - 2) *
              |deriv (intervalDomainLift (u t)) x| ^ 2) +
        slowDescentClosedCoeff p pExp steps *
          ((∫ x in (0 : ℝ)..1,
            intervalDomainLift (u t) x ^ pExp) + 1) := by
      dsimp [eps, slowDescentEps, A, Cterminal, Y,
        slowDescentClosedCoeff]

theorem lpEnergy_eq_lift_power_of_solution
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpEnergy q u t =
      ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ q := by
  rw [intervalDomainLpEnergy_eq_powerEnergy_of_pos
    (fun x => u_pos hsol ht0 htT x)]
  rfl

theorem weightedDissipation_eq_lift
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (t : ℝ) :
    intervalDomainLpWeightedGradientDissipation q u t =
      ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (q - 2) *
          |deriv (intervalDomainLift (u t)) x| ^ 2 := by
  unfold intervalDomainLpWeightedGradientDissipation
  unfold intervalDomain intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  simp [intervalDomainLift, intervalDomainGradNorm, hx, sq_abs]

/-- The slow-branch energy has a uniform linear damping term.  The constant is
independent of the horizon and of time. -/
theorem slow_lp_energy_damping
    {p : CM2Params} {T pExp : ℝ} {steps : ℕ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1)
    (hpdef : pExp = (2 : ℝ) ^ (steps + 1) * (1 - p.m))
    (hp : 1 < pExp) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 < t → t < T →
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        intervalDomainLpEnergy pExp u t ≤ K := by
  let A : ℝ := slowDescentClosedCoeff p pExp steps
  have hdescent := slow_cross_finite_descent_closed_uniform
    hsol hbeta hm1 hpdef hp
  have hA : 0 ≤ A := by simpa [A] using hdescent.1
  let delta : ℝ := (pExp - 1) / ((steps : ℝ) + 2)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos (by linarith) (by positivity)
  let B : ℝ := p.a + A + 1
  have hB : 0 < B := by dsimp [B]; linarith [p.ha]
  obtain ⟨Cmass, hCmass, hmass⟩ :=
    uniform_mass_bound_of_guard hguard hu₀ hsol htrace
  obtain ⟨Cagmon, hCagmon, hagmon⟩ :=
    unitIntervalPositiveAgmonInterpolation pExp hp (delta / B)
      (div_pos hdelta hB)
  let K : ℝ := A + B * Cagmon * Cmass ^ pExp
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg hA
      (mul_nonneg (mul_nonneg hB.le hCagmon.le)
        (Real.rpow_nonneg hCmass _))
  refine ⟨K, hK, ?_⟩
  intro t ht0 htT
  let Y : ℝ := intervalDomainLpEnergy pExp u t
  let G : ℝ := intervalDomainLpWeightedGradientDissipation pExp u t
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
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z]
    unfold intervalDomain intervalDomainIntegral
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      simp only [intervalDomainLift, hx, dif_pos]
      exact Real.rpow_nonneg (u_pos hsol ht0 htT ⟨x, hx⟩).le _)
  have hmass_t : intervalDomain.integral (u t) ≤ Cmass :=
    hmass t ht0 htT
  have hmass_nonneg : 0 ≤ intervalDomain.integral (u t) :=
    (mass_pos hsol ht).le
  have hmass_pow : (intervalDomain.integral (u t)) ^ pExp ≤
      Cmass ^ pExp :=
    Real.rpow_le_rpow hmass_nonneg hmass_t (by linarith : 0 ≤ pExp)
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hag := hagmon (u t) (fun x => u_pos hsol ht0 htT x) hC2
  have hag' : Y ≤ (delta / B) * G +
      Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
    rw [hYdomain]
    simpa [G, intervalDomainLpWeightedGradientDissipation] using hag
  have habsorb : B * Y ≤ delta * G +
      B * Cagmon * Cmass ^ pExp := by
    have hmul := mul_le_mul_of_nonneg_left hag' hB.le
    have hpowmul := mul_le_mul_of_nonneg_left hmass_pow
      (mul_nonneg hB.le hCagmon.le)
    calc
      B * Y ≤ B * ((delta / B) * G +
          Cagmon * (intervalDomain.integral (u t)) ^ pExp) := hmul
      _ = delta * G +
          B * Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
        field_simp [ne_of_gt hB]
      _ ≤ delta * G + B * Cagmon * Cmass ^ pExp :=
        by linarith
  have hcross :
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) * G +
          A * (Y + 1) := by
    simpa [A, hYeq, hGeq] using hdescent.2 t ht0 htT
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := pExp)
    (u := u) (v := v) (ne_of_gt (lt_trans zero_lt_one hp))
    hsol ht0 htT
  rw [← hYdomain] at henergy
  change (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
      (pExp - 1) * G + p.b * Z =
        p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t +
          p.a * Y at henergy
  have hcoeff : (pExp - 1) -
      ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) =
        delta := by
    dsimp [delta]
    field_simp
    ring
  have hpre :
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        delta * G ≤ (p.a + A) * Y + A := by
    have hbZ : 0 ≤ p.b * Z := mul_nonneg p.hb hZnonneg
    nlinarith
  dsimp [Y] at hpre habsorb ⊢
  dsimp [K, B]
  nlinarith

theorem lpEnergy_hasDerivAt_of_solution
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => intervalDomainLpEnergy q u s)
      (deriv (fun s => intervalDomainLpEnergy q u s) t) t := by
  have hpow := powerEnergy_hasDerivAt (q := q) hsol ⟨ht0, htT⟩
  have heq : (fun s => intervalDomainLpEnergy q u s) =ᶠ[nhds t]
      fun s => intervalDomainPowerEnergy q u s := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ht0, htT⟩] with s hs
    exact intervalDomainLpEnergy_eq_powerEnergy_of_pos
      (fun x => u_pos hsol hs.1 hs.2 x)
  exact (heq.hasDerivAt_iff.mpr hpow).differentiableAt.hasDerivAt

/-- The finite-descent exponent carries a uniform finite-Lp bound on every
maximal time interval. -/
theorem slow_lp_power_bounded_before
    {p : CM2Params} {T pExp : ℝ} {steps : ℕ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1)
    (hpdef : pExp = (2 : ℝ) ^ (steps + 1) * (1 - p.m))
    (hp : 1 < pExp) :
    LpPowerBoundedBefore intervalDomainM pExp T u := by
  obtain ⟨K, hK, hdamp⟩ := slow_lp_energy_damping
    hguard hu₀ hsol htrace hbeta hm1 hpdef hp
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
  have hR : 0 < R := by dsimp [R]; linarith [le_max_left (0 : ℝ) M₀]
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
            exact Real.rpow_le_rpow hpos.le hle (by linarith : 0 ≤ pExp))
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

/-- The power-of-two terminal exponents used by the finite descent are
cofinal.  In particular, one can choose a terminal exponent above any fixed
threshold while retaining the exact algebraic form required by the descent. -/
theorem exists_slow_descent_exponent_above
    {p : CM2Params} (hm1 : p.m < 1) (threshold : ℝ) :
    ∃ steps : ℕ, ∃ pExp : ℝ,
      pExp = (2 : ℝ) ^ (steps + 1) * (1 - p.m) ∧ threshold < pExp := by
  have hc : 0 < 1 - p.m := by linarith
  obtain ⟨steps, hsteps⟩ :=
    pow_unbounded_of_one_lt (threshold / (1 - p.m))
      (by norm_num : (1 : ℝ) < 2)
  refine ⟨steps, (2 : ℝ) ^ (steps + 1) * (1 - p.m), rfl, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hsteps hc
  have hcancel : threshold / (1 - p.m) * (1 - p.m) = threshold := by
    field_simp [ne_of_gt hc]
  rw [hcancel] at hmul
  rw [pow_succ]
  have hpowpos : 0 < (2 : ℝ) ^ steps := by positivity
  nlinarith

/-- In the slow-diffusion regime, a faithful interval solution admits a
uniform power bound at some exponent above the dimension, diffusion, and
signal exponents occurring in the paper's smoothing step. -/
theorem exists_high_slow_lp_power_bounded_before
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1) :
    ∃ pExp : ℝ,
      max 1 (max p.m p.γ) < pExp ∧
        LpPowerBoundedBefore intervalDomainM pExp T u := by
  obtain ⟨steps, pExp, hpdef, hp⟩ :=
    exists_slow_descent_exponent_above
      hm1 (max 1 (max p.m p.γ))
  refine ⟨pExp, hp, ?_⟩
  exact slow_lp_power_bounded_before hguard hu₀ hsol htrace hbeta hm1
    hpdef (lt_of_le_of_lt (le_max_left _ _) hp)

/-- The slow-branch damping constant can be chosen once for a global
solution.  The finite-descent coefficient, the Agmon constant, and the mass
cap are all fixed before the observation time; only the classical restriction
to `(0,t+1)` varies with `t`. -/
theorem slow_lp_energy_damping_global
    {p : CM2Params} {pExp : ℝ} {steps : ℕ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1)
    (hpdef : pExp = (2 : ℝ) ^ (steps + 1) * (1 - p.m))
    (hp : 1 < pExp) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 < t →
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        intervalDomainLpEnergy pExp u t ≤ K := by
  let A : ℝ := slowDescentClosedCoeff p pExp steps
  have hsol1 : IsPaper2ClassicalSolution intervalDomainM p 1 u v :=
    hglobal.classical (by norm_num)
  have hdescent1 := slow_cross_finite_descent_closed_uniform
    hsol1 hbeta hm1 hpdef hp
  have hA : 0 ≤ A := by simpa [A] using hdescent1.1
  let delta : ℝ := (pExp - 1) / ((steps : ℝ) + 2)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos (by linarith) (by positivity)
  let B : ℝ := p.a + A + 1
  have hB : 0 < B := by dsimp [B]; linarith [p.ha]
  let Cmass : ℝ := uniformMassBoundConstant p u₀
  have hCmass : 0 ≤ Cmass := by
    dsimp [Cmass]
    exact uniformMassBoundConstant_nonneg p u₀
  obtain ⟨Cagmon, hCagmon, hagmon⟩ :=
    unitIntervalPositiveAgmonInterpolation pExp hp (delta / B)
      (div_pos hdelta hB)
  let K : ℝ := A + B * Cagmon * Cmass ^ pExp
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg hA
      (mul_nonneg (mul_nonneg hB.le hCagmon.le)
        (Real.rpow_nonneg hCmass _))
  refine ⟨K, hK, ?_⟩
  intro t ht0
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    hglobal.classical hT
  have hdescent := slow_cross_finite_descent_closed_uniform
    hsol hbeta hm1 hpdef hp
  let Y : ℝ := intervalDomainLpEnergy pExp u t
  let G : ℝ := intervalDomainLpWeightedGradientDissipation pExp u t
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
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z]
    unfold intervalDomain intervalDomainIntegral
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      simp only [intervalDomainLift, hx, dif_pos]
      exact Real.rpow_nonneg (u_pos hsol ht0 htT ⟨x, hx⟩).le _)
  have hmass_t : intervalDomain.integral (u t) ≤ Cmass := by
    dsimp [Cmass]
    exact mass_le_uniformMassBoundConstant_of_guard
      hguard hu₀ hsol htrace t ht0 htT
  have hmass_nonneg : 0 ≤ intervalDomain.integral (u t) :=
    (mass_pos hsol ht).le
  have hmass_pow : (intervalDomain.integral (u t)) ^ pExp ≤
      Cmass ^ pExp :=
    Real.rpow_le_rpow hmass_nonneg hmass_t (by linarith : 0 ≤ pExp)
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hag := hagmon (u t) (fun x => u_pos hsol ht0 htT x) hC2
  have hag' : Y ≤ (delta / B) * G +
      Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
    rw [hYdomain]
    simpa [G, intervalDomainLpWeightedGradientDissipation] using hag
  have habsorb : B * Y ≤ delta * G +
      B * Cagmon * Cmass ^ pExp := by
    have hmul := mul_le_mul_of_nonneg_left hag' hB.le
    have hpowmul := mul_le_mul_of_nonneg_left hmass_pow
      (mul_nonneg hB.le hCagmon.le)
    calc
      B * Y ≤ B * ((delta / B) * G +
          Cagmon * (intervalDomain.integral (u t)) ^ pExp) := hmul
      _ = delta * G +
          B * Cagmon * (intervalDomain.integral (u t)) ^ pExp := by
        field_simp [ne_of_gt hB]
      _ ≤ delta * G + B * Cagmon * Cmass ^ pExp := by
        linarith
  have hcross :
      p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t ≤
        ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) * G +
          A * (Y + 1) := by
    simpa [A, hYeq, hGeq] using hdescent.2 t ht0 htT
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := pExp)
    (u := u) (v := v) (ne_of_gt (lt_trans zero_lt_one hp))
    hsol ht0 htT
  rw [← hYdomain] at henergy
  change (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
      (pExp - 1) * G + p.b * Z =
        p.χ₀ * (pExp - 1) * lpSignedCrossIntegralM p pExp u v t +
          p.a * Y at henergy
  have hcoeff : (pExp - 1) -
      ((steps : ℝ) + 1) * ((pExp - 1) / ((steps : ℝ) + 2)) =
        delta := by
    dsimp [delta]
    field_simp
    ring
  have hpre :
      (1 / pExp) * deriv (fun τ => intervalDomainLpEnergy pExp u τ) t +
        delta * G ≤ (p.a + A) * Y + A := by
    have hbZ : 0 ≤ p.b * Z := mul_nonneg p.hb hZnonneg
    nlinarith
  dsimp [Y] at hpre habsorb ⊢
  dsimp [K, B]
  nlinarith

#print axioms slow_lp_energy_damping_global

end ShenWork.Paper2.IntervalDomainM
