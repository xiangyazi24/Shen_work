import ShenWork.PDE.IntervalCriticalMassAgmon
import ShenWork.PDE.SignalSaturationFactor
import ShenWork.Paper3.IntervalDomainMMinimalEventualLp

/-!
# Critical `m = 2` minimal-model eventual `L^P` bound

The mass seed is scale-critical when `m = 2`.  The endpoint Agmon coefficient
from `IntervalCriticalMassAgmon` closes the energy estimate under the strict
condition

`χ₀ sqrt(μ) σβ P uStar < 1`,

where `σβ = signalSaturationFactor β`.  The quantifier order remains
orbit-independent: `P`, the strict margin, and the damping constant are all
chosen before the bounded global solution.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainM

namespace ShenWork.Paper3

noncomputable section

/-- Parameter-only admissibility condition that leaves room for a restarted
exponent strictly above two and at least `γ`. -/
def CriticalMinimalLpAdmissibility (p : CM2Params) (uStar : ℝ) : Prop :=
  p.χ₀ * Real.sqrt p.μ * ShenWork.signalSaturationFactor p.β *
      uStar * max 2 p.γ < 1

set_option maxHeartbeats 1000000 in
-- The pointwise signal-weight normalization uses several real-power rewrites.
/-- Sharp weighted-`v`-gradient bound.  The signal saturation factor improves
the crude coefficient `μ` to `μ σβ²`. -/
theorem descentVGradient_le_mu_saturation_moment
    {p : CM2Params} {T t s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hbeta : 1 ≤ p.β) :
    descentVGradient s (2 * p.β) u v t ≤
      p.μ * ShenWork.signalSaturationFactor p.β ^ 2 *
        ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let sigma : ℝ := ShenWork.signalSaturationFactor p.β
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    simpa [U] using solution_lift_pos_Icc hsol ht
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    intro x hx
    simpa [V, intervalDomainLift, hx] using
      hsol.v_nonneg (x := (⟨x, hx⟩ : intervalDomain.Point)) ht0 htT
  have hlog : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv V x| ≤ Real.sqrt p.μ * V x := by
    simpa [V] using elliptic_log_gradient_bound hsol ht0 htT
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact ShenWork.signalSaturationFactor_pos hbeta
  have hweight : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β)) ≤
        p.μ * sigma ^ 2 := by
    intro x hx
    have hBpos : 0 < 1 + V x := by linarith [hVnonneg x hx]
    have hsqrt : (Real.sqrt p.μ) ^ 2 = p.μ :=
      Real.sq_sqrt p.hμ.le
    have hsq : |deriv V x| ^ 2 ≤ p.μ * V x ^ 2 := by
      have hraw : |deriv V x| ^ 2 ≤
          (Real.sqrt p.μ * V x) ^ 2 := by
        simpa [pow_two] using
          mul_self_le_mul_self (abs_nonneg _) (hlog x hx)
      calc
        |deriv V x| ^ 2 ≤ (Real.sqrt p.μ * V x) ^ 2 := hraw
        _ = p.μ * V x ^ 2 := by rw [mul_pow, hsqrt]
    have hsat :=
      ShenWork.signal_mul_one_add_rpow_neg_le_factor
        hbeta (hVnonneg x hx)
    have hleft0 :
        0 ≤ V x * (1 + V x) ^ (-p.β) :=
      mul_nonneg (hVnonneg x hx)
        (Real.rpow_nonneg hBpos.le _)
    have hsatsq :
        V x ^ 2 * (1 + V x) ^ (-(2 * p.β)) ≤ sigma ^ 2 := by
      have hraw := mul_self_le_mul_self hleft0 hsat
      have hpow :
          ((1 + V x) ^ (-p.β)) ^ 2 =
            (1 + V x) ^ (-(2 * p.β)) := by
        rw [← Real.rpow_mul_natCast hBpos.le]
        congr 1
        ring
      have hident :
          (V x * (1 + V x) ^ (-p.β)) ^ 2 =
            V x ^ 2 * (1 + V x) ^ (-(2 * p.β)) := by
        rw [mul_pow, hpow]
      calc
        V x ^ 2 * (1 + V x) ^ (-(2 * p.β)) =
            (V x * (1 + V x) ^ (-p.β)) ^ 2 := hident.symm
        _ ≤ sigma ^ 2 := by
          simpa [sigma, pow_two] using hraw
    have hwnn : 0 ≤ (1 + V x) ^ (-(2 * p.β)) :=
      Real.rpow_nonneg hBpos.le _
    have hmul := mul_le_mul_of_nonneg_right hsq hwnn
    calc
      |deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β))
          ≤ (p.μ * V x ^ 2) *
              (1 + V x) ^ (-(2 * p.β)) := hmul
      _ = p.μ *
          (V x ^ 2 * (1 + V x) ^ (-(2 * p.β))) := by ring
      _ ≤ p.μ * sigma ^ 2 :=
        mul_le_mul_of_nonneg_left hsatsq p.hμ.le
  have hLint : IntervalIntegrable (fun x =>
      U x ^ s * |deriv V x| ^ 2 *
        (1 + V x) ^ (-(2 * p.β))) volume 0 1 := by
    simpa [U, V] using
      descentVGradient_intervalIntegrable
        (r := s) (eta := 2 * p.β) hsol ht0 htT
  have hRint : IntervalIntegrable (fun x =>
      (p.μ * sigma ^ 2) * U x ^ s) volume 0 1 := by
    have hcont : ContinuousOn (fun x => U x ^ s)
        (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact (solution_lift_continuousOn_Icc hsol ht).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    exact (hcont.intervalIntegrable).const_mul (p.μ * sigma ^ 2)
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      U x ^ s * |deriv V x| ^ 2 *
          (1 + V x) ^ (-(2 * p.β)) ≤
        (p.μ * sigma ^ 2) * U x ^ s := by
    intro x hx
    have hUs : 0 ≤ U x ^ s := Real.rpow_nonneg (hUpos x hx).le _
    calc
      U x ^ s * |deriv V x| ^ 2 *
          (1 + V x) ^ (-(2 * p.β)) =
          U x ^ s *
            (|deriv V x| ^ 2 *
              (1 + V x) ^ (-(2 * p.β))) := by ring
      _ ≤ U x ^ s * (p.μ * sigma ^ 2) :=
        mul_le_mul_of_nonneg_left (hweight x hx) hUs
      _ = (p.μ * sigma ^ 2) * U x ^ s := by ring
  unfold descentVGradient
  calc
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ s *
          |deriv (intervalDomainLift (v t)) x| ^ 2 *
          (1 + intervalDomainLift (v t) x) ^ (-(2 * p.β)))
        ≤ ∫ x in (0 : ℝ)..1,
            (p.μ * sigma ^ 2) * U x ^ s :=
      intervalIntegral.integral_mono_on
        (by norm_num) hLint hRint hpoint
    _ = (p.μ * sigma ^ 2) *
        ∫ x in (0 : ℝ)..1, U x ^ s := by
      rw [intervalIntegral.integral_const_mul]
    _ = p.μ * ShenWork.signalSaturationFactor p.β ^ 2 *
        ∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ s := by
      rfl

set_option maxHeartbeats 1000000 in
-- The endpoint coefficient is normalized against the retained energy dissipation.
/-- Orbit-independent critical `L^P` damping seed at `m = 2`. -/
theorem exists_intervalDomainM_minimal_critical_lp_damping_constant
    (p : CM2Params) {P uStar : ℝ}
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hP : 1 < P) (huStar : 0 < uStar)
    (hsmall :
      p.χ₀ * Real.sqrt p.μ *
        ShenWork.signalSaturationFactor p.β * P * uStar < 1) :
    ∃ K, 0 ≤ K ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomainM p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
        ∀ t, 0 < t →
          (1 / P) *
              deriv (fun τ => intervalDomainLpEnergy P u τ) t +
            intervalDomainLpEnergy P u t ≤ K := by
  let sigma : ℝ := ShenWork.signalSaturationFactor p.β
  let q0 : ℝ :=
    p.χ₀ * Real.sqrt p.μ * sigma * P * uStar
  let theta : ℝ := (1 - q0) / 2
  let q : ℝ := q0 / (1 - theta)
  let eps : ℝ := (P - 1) / 2
  let Ccross : ℝ := p.χ₀ * (P - 1)
  let Kcross : ℝ := Ccross ^ 2 / (4 * eps)
  let c : ℝ := eps * (1 - q ^ 2)
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hP1 : 0 < P - 1 := sub_pos.mpr hP
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact ShenWork.signalSaturationFactor_pos hbeta
  have hsqrt : 0 < Real.sqrt p.μ :=
    Real.sqrt_pos.2 p.hμ
  have hq0 : 0 < q0 := by
    dsimp [q0]
    positivity
  have hq01 : q0 < 1 := by
    simpa [q0, sigma] using hsmall
  have htheta0 : 0 < theta := by
    dsimp [theta]
    linarith
  have htheta1 : theta < 1 := by
    dsimp [theta]
    linarith
  have hden : 0 < 1 - theta := sub_pos.mpr htheta1
  have hq0den : q0 < 1 - theta := by
    dsimp [theta]
    linarith
  have hq : 0 < q := div_pos hq0 hden
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hden]
    exact hq0den
  have hqSq : q ^ 2 < 1 := by nlinarith
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  have hCcross : 0 < Ccross := mul_pos hchi hP1
  have hKcross : 0 < Kcross := by
    dsimp [Kcross]
    positivity
  have hc : 0 < c := mul_pos heps (sub_pos.mpr hqSq)
  obtain ⟨Cag, hCag, hag⟩ :=
    unitIntervalPositiveAgmonInterpolation P hP c hc
  let Rcrit : ℝ :=
    ShenWork.IntervalDomainExistence.IntervalCriticalMassAgmon.criticalMassAgmonRemainder
      P theta uStar
  let Dcrit : ℝ :=
    Kcross * (p.μ * sigma ^ 2) * Rcrit
  let Ky : ℝ := Cag * uStar ^ P
  let K : ℝ := max 0 (Dcrit + Ky)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact le_max_left _ _
  refine ⟨K, hK, ?_⟩
  intro u v huv hmass t ht0
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    huv.1.classical hT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  let G : ℝ := intervalDomainLpWeightedGradientDissipation P u t
  let Y : ℝ := intervalDomainLpEnergy P u t
  let d : ℝ :=
    (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t
  let Cross : ℝ := lpSignedCrossIntegralM p P u v t
  let VG : ℝ := descentVGradient (P + 2) (2 * p.β) u v t
  let Mom : ℝ :=
    intervalDomain.integral (fun x => (u t x) ^ (P + 2))
  have hG : 0 ≤ G := by
    dsimp [G]
    unfold intervalDomainLpWeightedGradientDissipation intervalDomain
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      simp only [intervalDomainLift, hx, dif_pos]
      exact mul_nonneg
        (Real.rpow_nonneg
          (u_pos hsol ht0 htT ⟨x, hx⟩).le _)
        (sq_nonneg _))
  have hGeq : G = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (P - 2) *
        |deriv (intervalDomainLift (u t)) x| ^ 2 := by
    dsimp [G]
    exact weightedDissipation_eq_lift P u t
  have hYeq :
      Y = intervalDomain.integral (fun x => (u t x) ^ P) := by
    dsimp [Y]
    rw [lpEnergy_eq_lift_power_of_solution hsol ht0 htT]
    exact
      (intervalDomain_integral_rpow_eq_lift_integral
        (q := P) (f := u t)).symm
  have hmass_t : intervalDomain.integral (u t) = uStar := by
    simpa [HasEquilibriumMassOnPositiveTimes, intervalDomainM, intervalDomain]
      using hmass t ht0
  have huC2 :
      ContDiffOn ℝ 2 (intervalDomainLift (u t))
        (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hupos : ∀ x : intervalDomainPoint, 0 < u t x :=
    fun x => u_pos hsol ht0 htT x
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := P)
      (u := u) (v := v) (ne_of_gt hP0) hsol ht0 htT
  rw [ha0, hb0] at henergy
  have hE : d + (P - 1) * G = Ccross * Cross := by
    dsimp only [d, G, Ccross, Cross]
    simp only [zero_mul, add_zero] at henergy
    linarith [henergy]
  have hcrossle :
      Cross ≤ descentMixed (P + p.m - 1) p.β u v t := by
    have habs := signedCross_abs_le_descentMixed
      (p := p) (T := T) (t := t) (pExp := P)
        (u := u) (v := v) hsol ht0 htT
    exact le_trans (le_abs_self _) habs
  have hCcrossle :
      Ccross * Cross ≤
        Ccross * descentMixed (P + p.m - 1) p.β u v t :=
    mul_le_mul_of_nonneg_left hcrossle hCcross.le
  have hyoung := descentMixed_young_beta
    (p := p) (T := T) (t := t) (pExp := P)
      (r := P + p.m - 1) (C := Ccross) (eps := eps)
      (beta := p.β) (u := u) (v := v)
      hsol ht0 htT heps
  rw [← hGeq] at hyoung
  have hs :
      2 * (P + p.m - 1) - P = P + 2 := by
    rw [hm]
    ring
  have hYoungCross :
      Ccross * Cross ≤ eps * G + Kcross * VG := by
    have hraw := hCcrossle.trans hyoung
    rw [hs] at hraw
    simpa [Kcross, VG] using hraw
  have hVG :
      VG ≤ p.μ * sigma ^ 2 *
        ∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ (P + 2) := by
    dsimp [VG, sigma]
    exact descentVGradient_le_mu_saturation_moment
      (s := P + 2) hsol ht0 htT hbeta
  have hMomEq :
      Mom = ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ (P + 2) := by
    dsimp [Mom]
    exact
      intervalDomain_integral_rpow_eq_lift_integral
        (q := P + 2) (f := u t)
  rw [← hMomEq] at hVG
  have hMomCrit :
      Mom ≤
        (P ^ 2 / (1 - theta) ^ 2) * uStar ^ 2 * G +
          Rcrit := by
    dsimp [Mom, G, Rcrit]
    exact
      ShenWork.IntervalDomainExistence.IntervalCriticalMassAgmon.intervalDomainM_mass_critical_agmon
        hsol ht0 htT hP huStar htheta0 htheta1 hmass_t
  have hCrossCrit :
      Ccross * Cross ≤
        (eps + Kcross * (p.μ * sigma ^ 2) *
          ((P ^ 2 / (1 - theta) ^ 2) * uStar ^ 2)) * G +
          Dcrit := by
    have hVGscaled :
        Kcross * VG ≤
          Kcross * (p.μ * sigma ^ 2) * Mom := by
      have hmul := mul_le_mul_of_nonneg_left hVG hKcross.le
      nlinarith [hmul]
    have hMomScaled :
        Kcross * (p.μ * sigma ^ 2) * Mom ≤
          Kcross * (p.μ * sigma ^ 2) *
              ((P ^ 2 / (1 - theta) ^ 2) * uStar ^ 2 * G +
                Rcrit) := by
      exact mul_le_mul_of_nonneg_left hMomCrit
        (mul_nonneg hKcross.le
          (mul_nonneg p.hμ.le (sq_nonneg sigma)))
    dsimp only [Dcrit]
    nlinarith [hYoungCross, hVGscaled, hMomScaled]
  have hcoef :
      Kcross * (p.μ * sigma ^ 2) *
          ((P ^ 2 / (1 - theta) ^ 2) * uStar ^ 2) =
        eps * q ^ 2 := by
    have hmusqrt : (Real.sqrt p.μ) ^ 2 = p.μ :=
      Real.sq_sqrt p.hμ.le
    dsimp [Kcross, Ccross, eps, q, q0]
    field_simp [
      ne_of_gt hP1,
      ne_of_gt hden,
      ne_of_gt (Real.sqrt_pos.2 p.hμ)]
    nlinarith [hmusqrt]
  rw [hcoef] at hCrossCrit
  have hdampGrad : d + c * G ≤ Dcrit := by
    have hpre :
        d + (P - 1) * G ≤
          (eps + eps * q ^ 2) * G + Dcrit := by
      calc
        d + (P - 1) * G = Ccross * Cross := hE
        _ ≤ (eps + eps * q ^ 2) * G + Dcrit := hCrossCrit
    have hsplit :
        P - 1 = (eps + eps * q ^ 2) + c := by
      dsimp [eps, c]
      ring
    calc
      d + c * G =
          (d + (P - 1) * G) -
            (eps + eps * q ^ 2) * G := by
              rw [hsplit]
              ring
      _ ≤ ((eps + eps * q ^ 2) * G + Dcrit) -
            (eps + eps * q ^ 2) * G :=
        sub_le_sub_right hpre _
      _ = Dcrit := by ring
  have hgradBridge :
      intervalDomain.integral
        (fun x => (u t x) ^ (P - 2) *
          intervalDomain.gradNorm (u t) x ^ 2) = G := rfl
  have hYabs : Y ≤ c * G + Ky := by
    have hagT := hag (u t) hupos huC2
    rw [hgradBridge, hmass_t] at hagT
    rw [hYeq]
    simpa [Ky] using hagT
  have hrawFinal : d + Y ≤ Dcrit + Ky := by
    linarith [hdampGrad, hYabs]
  have hmax : Dcrit + Ky ≤ K := by
    dsimp [K]
    exact le_max_right _ _
  calc
    (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t = d + Y := rfl
    _ ≤ Dcrit + Ky := hrawFinal
    _ ≤ K := hmax

/-- Eventual orbit-independent `L^P` power bound at any fixed admissible
critical exponent. -/
theorem exists_intervalDomainM_minimal_critical_eventual_lp_power_bound
    (p : CM2Params) {P uStar : ℝ}
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hP : 1 < P) (huStar : 0 < uStar)
    (hsmall :
      p.χ₀ * Real.sqrt p.μ *
        ShenWork.signalSaturationFactor p.β * P * uStar < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomainM p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
        ∀ᶠ t : ℝ in atTop,
          intervalDomainM.integral (fun x => (u t x) ^ P) ≤ C := by
  obtain ⟨K, hK, hdamp⟩ :=
    exists_intervalDomainM_minimal_critical_lp_damping_constant
      p hm ha0 hb0 hbeta hchi hP huStar hsmall
  refine ⟨K + 1, by linarith, ?_⟩
  intro u v huv hmass
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hderiv : ∀ t, 0 < t →
      HasDerivAt (fun τ => intervalDomainLpEnergy P u τ)
        (deriv (fun τ => intervalDomainLpEnergy P u τ) t) t := by
    intro t ht
    have hsol := huv.classical (t + 1) (by linarith)
    exact lpEnergy_hasDerivAt_of_solution hsol ht (by linarith)
  have hev := eventually_le_add_one_of_linear_damping
    hP0 hderiv (hdamp u v huv hmass)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with t ht hTpos
  have hsol := huv.classical (t + 1) (by linarith)
  have heq :
      intervalDomainLpEnergy P u t =
        ∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ P :=
    lpEnergy_eq_lift_power_of_solution
      hsol hTpos (by linarith)
  have hdomain :
      intervalDomainM.integral (fun x => (u t x) ^ P) =
        intervalDomainLpEnergy P u t := by
    rw [heq]
    exact intervalDomain_integral_rpow_eq_lift_integral
  rw [hdomain]
  exact ht

set_option maxHeartbeats 1000000 in
-- Choosing an exponent in the strict parameter-only interval uses real division.
/-- The parameter-only critical condition produces `P > 2`, `P ≥ γ`, and
`Q = P/2 > 1`, exactly the hypotheses required by the restarted
general-`m` `L^P → L∞` theorem. -/
theorem exists_intervalDomainM_minimal_critical_eventual_high_lp_power_bound
    (p : CM2Params) {uStar : ℝ}
    (hm : p.m = 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (huStar : 0 < uStar)
    (hadm : CriticalMinimalLpAdmissibility p uStar) :
    ∃ P Q C : ℝ,
      2 < P ∧ 1 < Q ∧ p.m * Q = P ∧ p.γ ≤ P ∧ 0 ≤ C ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomainM p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
        ∀ᶠ t : ℝ in atTop,
          intervalDomainM.integral (fun x => (u t x) ^ P) ≤ C := by
  let sigma : ℝ := ShenWork.signalSaturationFactor p.β
  let A : ℝ := p.χ₀ * Real.sqrt p.μ * sigma * uStar
  let L : ℝ := max 2 p.γ
  let U : ℝ := 1 / A
  let P : ℝ := (L + U) / 2
  let Q : ℝ := P / 2
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact ShenWork.signalSaturationFactor_pos hbeta
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos
      (mul_pos (mul_pos hchi (Real.sqrt_pos.2 p.hμ)) hsigma)
      huStar
  have hAL : A * L < 1 := by
    simpa [CriticalMinimalLpAdmissibility, A, L, sigma, mul_assoc]
      using hadm
  have hLU : L < U := by
    dsimp [U]
    rw [lt_div_iff₀ hA]
    simpa [mul_comm] using hAL
  have hLP : L < P := by
    dsimp [P]
    linarith
  have hPU : P < U := by
    dsimp [P]
    linarith
  have hL2 : (2 : ℝ) ≤ L := le_max_left _ _
  have hLgamma : p.γ ≤ L := le_max_right _ _
  have hP2 : 2 < P := lt_of_le_of_lt hL2 hLP
  have hP1 : 1 < P := lt_trans one_lt_two hP2
  have hgammaP : p.γ ≤ P :=
    hLgamma.trans hLP.le
  have hQ : 1 < Q := by
    dsimp [Q]
    linarith
  have hmQ : p.m * Q = P := by
    rw [hm]
    dsimp [Q]
    ring
  have hAU : A * U = 1 := by
    dsimp [U]
    field_simp [ne_of_gt hA]
  have hAP : A * P < 1 := by
    have hmul := mul_lt_mul_of_pos_left hPU hA
    rw [hAU] at hmul
    exact hmul
  have hsmall :
      p.χ₀ * Real.sqrt p.μ *
        ShenWork.signalSaturationFactor p.β * P * uStar < 1 := by
    dsimp [A, sigma] at hAP
    nlinarith [hAP]
  obtain ⟨C, hC, hbound⟩ :=
    exists_intervalDomainM_minimal_critical_eventual_lp_power_bound
      (p := p) (P := P) hm ha0 hb0 hbeta hchi
        hP1 huStar hsmall
  exact ⟨P, Q, C, hP2, hQ, hmQ, hgammaP, hC, hbound⟩

#print axioms descentVGradient_le_mu_saturation_moment
#print axioms exists_intervalDomainM_minimal_critical_lp_damping_constant
#print axioms
  exists_intervalDomainM_minimal_critical_eventual_high_lp_power_bound

end

end ShenWork.Paper3
