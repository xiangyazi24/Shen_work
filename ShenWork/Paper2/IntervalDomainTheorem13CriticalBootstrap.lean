import ShenWork.Paper2.IntervalDomainTheorem13CriticalThreshold
import ShenWork.PDE.P3MoserAgmonDirectRoute
import ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness

/-!
# Fixed-target bootstrap for Paper 2, Theorem 1.3

The critical threshold gives one finite `L^p0` seed.  In one dimension this
seed absorbs the single higher moment needed at any prescribed finite target
power.  No all-exponent Moser package is used.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants
open ShenWork.Paper2.IntervalDomainTheorem13CriticalSeed
open ShenWork.Paper2.IntervalDomainTheorem13CriticalThreshold
open ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer
open ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness
open ShenWork.Paper2.IntervalDomainMRestartedLpLinfGeneral
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

/-- The endpoint-safe Agmon estimate for a slice of the faithful general-`m`
equation.  Only positivity and spatial regularity are used. -/
theorem intervalDomainM_supNorm_rpow_le_energy_plus_weighted
    {p : CM2Params} {T t P : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hP : 0 < P) :
    intervalDomainSupNorm (u t) ^ P ≤
      2 * intervalDomain.integral (fun x => (u t x) ^ P) +
        2 * Real.sqrt (intervalDomain.integral (fun x => (u t x) ^ P)) *
          Real.sqrt ((P ^ 2 / 4) *
            intervalDomainLpWeightedGradientDissipation P u t) := by
  let C : ℝ :=
    2 * intervalDomain.integral (fun x => (u t x) ^ P) +
      2 * Real.sqrt (intervalDomain.integral (fun x => (u t x) ^ P)) *
        Real.sqrt ((P ^ 2 / 4) *
          intervalDomainLpWeightedGradientDissipation P u t)
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hfpos : ∀ x : intervalDomain.Point, 0 < u t x :=
    fun x => hsol.u_pos' ht0 htT
  have hC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hY0 : 0 ≤ intervalDomain.integral (fun x => (u t x) ^ P) :=
    intervalDomain_integral_rpow_nonneg hfpos
  have hG0 : 0 ≤ intervalDomainLpWeightedGradientDissipation P u t := by
    unfold intervalDomainLpWeightedGradientDissipation intervalDomain
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      simp only [intervalDomainLift, hx, dif_pos]
      exact mul_nonneg (Real.rpow_nonneg (hfpos ⟨x, hx⟩).le _)
        (sq_nonneg _))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (mul_nonneg (by norm_num) hY0)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hpointPow : ∀ x : intervalDomain.Point, (u t x) ^ P ≤ C := by
    intro x
    have hag := intervalDomainLift_rpow_agmon_bound
      (q := P) hfpos hC2 x.2
    have hlift : intervalDomainLift (u t) x.1 = u t x := by
      simp [intervalDomainLift]
    rw [hlift] at hag
    simpa [C, intervalDomainLpWeightedGradientDissipation] using hag
  let R : ℝ := C ^ P⁻¹
  have hR0 : 0 ≤ R := Real.rpow_nonneg hC0 _
  have hRpow : R ^ P = C := by
    dsimp [R]
    exact Real.rpow_inv_rpow hC0 hP.ne'
  have hpoint : ∀ x : intervalDomain.Point, |u t x| ^ P ≤ R ^ P := by
    intro x
    rw [hRpow]
    simpa [abs_of_pos (hfpos x)] using hpointPow x
  have hsup : intervalDomainSupNorm (u t) ≤ R :=
    intervalDomain_supNorm_le_of_pointwise_power_control hP hR0 hpoint
  calc
    intervalDomainSupNorm (u t) ^ P ≤ R ^ P :=
      Real.rpow_le_rpow (intervalDomainSupNorm_nonneg (u t)) hsup hP.le
    _ = C := hRpow

/-- A faithful general-`m` solution with one `L^p0` seed admits the
seed-relative one-dimensional interpolation used for a fixed target power. -/
theorem intervalDomainM_agmon_absorbed_of_lp_bound
    {p : CM2Params} {T rho p0 P C0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hrho : 0 < rho) (hp0 : 0 < p0) (hP : p0 ≤ P)
    (hrho2 : rho < 2 * p0)
    (hseed : ∀ t, 0 < t → t < T →
      intervalDomainM.integral (fun x => (u t x) ^ p0) ≤ C0) :
    ∀ eps > 0, ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ (P + rho)) ≤
        eps * ((P ^ 2 / 4) *
          intervalDomainLpWeightedGradientDissipation P u t) +
            scalarSeedAgmonAbsorbConstant (max C0 0) P p0 rho eps := by
  intro eps heps
  let M0 : ℝ := max C0 0
  have hM0 : 0 ≤ M0 := le_max_right _ _
  have hseedBound : ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ p0) ≤ M0 := by
    intro t ht0 htT
    exact (hseed t ht0 htT).trans (le_max_left _ _)
  have hPpos : 0 < P := hp0.trans_le hP
  intro t ht0 htT
  let U : ℝ := intervalDomainSupNorm (u t)
  let S : ℝ := U ^ P
  let Y : ℝ := intervalDomain.integral (fun x => (u t x) ^ P)
  let G : ℝ := (P ^ 2 / 4) *
    intervalDomainLpWeightedGradientDissipation P u t
  let seed : ℝ := intervalDomain.integral (fun x => (u t x) ^ p0)
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hfpos : ∀ x : intervalDomain.Point, 0 < u t x :=
    fun x => hsol.u_pos' ht0 htT
  have hf0 : ∀ x : intervalDomain.Point, 0 ≤ u t x := fun x => (hfpos x).le
  have hfbdd : BddAbove (range fun x : intervalDomain.Point => |u t x|) :=
    solution_slice_abs_bddAbove hsol ht
  have hpowerLiftCont : ∀ q : ℝ, ContinuousOn
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ q))
      (Icc (0 : ℝ) 1) := by
    intro q
    refine (power_continuousOn_timeSlice (q := q) hsol ht).congr ?_
    intro y hy
    simp [intervalDomainLift, hy]
  have hseedInt : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ p0))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hpowerLiftCont p0
  have hYInt : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ P))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hpowerLiftCont P
  have hhighInt : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ (P + rho)))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hpowerLiftCont (P + rho)
  have hYleftInt : IntervalIntegrable
      (intervalDomainLift
        (fun x : intervalDomain.Point => (u t x) ^ (p0 + (P - p0))))
      volume 0 1 := by
    simpa [show p0 + (P - p0) = P by ring] using hYInt
  have hhighLeftInt : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point =>
        (u t x) ^ (p0 + (P + rho - p0)))) volume 0 1 := by
    simpa [show p0 + (P + rho - p0) = P + rho by ring] using hhighInt
  have hU0 : 0 ≤ U := by dsimp [U]; exact intervalDomainSupNorm_nonneg _
  have hS0 : 0 ≤ S := Real.rpow_nonneg hU0 _
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (by positivity) (by
      unfold intervalDomainLpWeightedGradientDissipation intervalDomain
      exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
        simp only [intervalDomainLift, hx, dif_pos]
        exact mul_nonneg (Real.rpow_nonneg (hfpos ⟨x, hx⟩).le _)
          (sq_nonneg _)))
  have hYraw := intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
    (f := u t) hf0 hfbdd (pExp := p0) (rho := P - p0)
      hp0.le (sub_nonneg.mpr hP) hYleftInt hseedInt
  have hYseed : Y ≤ U ^ (P - p0) * seed := by
    simpa [Y, U, seed, show p0 + (P - p0) = P by ring] using hYraw
  have hUtheta : U ^ (P - p0) = S ^ ((P - p0) / P) := by
    have hmul : P * ((P - p0) / P) = P - p0 := by
      field_simp [hPpos.ne']
    calc
      U ^ (P - p0) = U ^ (P * ((P - p0) / P)) := by rw [hmul]
      _ = (U ^ P) ^ ((P - p0) / P) := by rw [Real.rpow_mul hU0]
      _ = S ^ ((P - p0) / P) := rfl
  have hYle : Y ≤ M0 * S ^ ((P - p0) / P) := by
    calc
      Y ≤ U ^ (P - p0) * seed := hYseed
      _ ≤ U ^ (P - p0) * M0 :=
        mul_le_mul_of_nonneg_left (hseedBound t ht0 htT)
          (Real.rpow_nonneg hU0 _)
      _ = M0 * S ^ ((P - p0) / P) := by rw [hUtheta]; ring
  have hsup : S ≤ 2 * Y + 2 * Real.sqrt Y * Real.sqrt G := by
    simpa [S, U, Y, G] using
      intervalDomainM_supNorm_rpow_le_energy_plus_weighted hsol ht0 htT hPpos
  have hSineq : S ≤
      2 * M0 * S ^ ((P - p0) / P) +
        2 * Real.sqrt (M0 * S ^ ((P - p0) / P)) * Real.sqrt G := by
    calc
      S ≤ 2 * Y + 2 * Real.sqrt Y * Real.sqrt G := hsup
      _ ≤ 2 * (M0 * S ^ ((P - p0) / P)) +
          2 * Real.sqrt (M0 * S ^ ((P - p0) / P)) * Real.sqrt G := by
        have hsqrt := Real.sqrt_le_sqrt hYle
        have hsqrtMul := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg G)
        nlinarith
      _ = _ := by ring
  have hhighRaw := intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
    (f := u t) hf0 hfbdd (pExp := p0) (rho := P + rho - p0)
      hp0.le (by linarith) hhighLeftInt hseedInt
  have hhighSeed : intervalDomain.integral (fun x => (u t x) ^ (P + rho)) ≤
      U ^ (P + rho - p0) * seed := by
    simpa [U, seed, show p0 + (P + rho - p0) = P + rho by ring] using hhighRaw
  have hUalpha : U ^ (P + rho - p0) =
      S ^ ((P + rho - p0) / P) := by
    have hmul : P * ((P + rho - p0) / P) = P + rho - p0 := by
      field_simp [hPpos.ne']
    calc
      U ^ (P + rho - p0) = U ^ (P * ((P + rho - p0) / P)) := by rw [hmul]
      _ = (U ^ P) ^ ((P + rho - p0) / P) := by rw [Real.rpow_mul hU0]
      _ = S ^ ((P + rho - p0) / P) := rfl
  have hhighLe : intervalDomain.integral (fun x => (u t x) ^ (P + rho)) ≤
      M0 * S ^ ((P + rho - p0) / P) := by
    calc
      _ ≤ U ^ (P + rho - p0) * seed := hhighSeed
      _ ≤ U ^ (P + rho - p0) * M0 :=
        mul_le_mul_of_nonneg_left (hseedBound t ht0 htT)
          (Real.rpow_nonneg hU0 _)
      _ = M0 * S ^ ((P + rho - p0) / P) := by rw [hUalpha]; ring
  exact hhighLe.trans (scalar_seed_agmon_absorb hM0 hS0 hG0
    hp0 hP hrho hrho2 heps hSineq)

/-- Existential wrapper retained for the finite-horizon boundedness chain. -/
theorem intervalDomainM_agmon_absorbed_of_lp_seed
    {p : CM2Params} {T rho p0 P : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hrho : 0 < rho) (hp0 : 0 < p0) (hP : p0 ≤ P)
    (hrho2 : rho < 2 * p0)
    (hseed : LpPowerBoundedBefore intervalDomainM p0 T u) :
    ∀ eps > 0, ∃ Ceps : ℝ, ∀ t, 0 < t → t < T →
      intervalDomain.integral (fun x => (u t x) ^ (P + rho)) ≤
        eps * ((P ^ 2 / 4) *
          intervalDomainLpWeightedGradientDissipation P u t) + Ceps := by
  obtain ⟨C0, hC0⟩ := hseed
  intro eps heps
  refine ⟨scalarSeedAgmonAbsorbConstant (max C0 0) P p0 rho eps, ?_⟩
  exact intervalDomainM_agmon_absorbed_of_lp_bound hsol hrho hp0 hP
    hrho2 hC0 eps heps

/-- Equation (5.3) at an arbitrary finite target exponent.  The threshold is
not used here; it was used only to create the low seed. -/
theorem critical_case_iii_cross_bound
    {p : CM2Params} {T P : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1) (hP : 1 < P) :
    ∀ t, 0 < t → t < T →
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        criticalCaseIIICoefficient p P *
          intervalDomain.integral (fun x => (u t x) ^ (P + p.α)) := by
  let r : ℝ := P + p.m - 1
  let s : ℝ := P + p.α
  let q : ℝ := s / p.γ
  let k : ℝ := p.χ₀ * (P - 1) / r
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hr : 0 < r := by dsimp [r]; linarith [p.hm]
  have hs : 0 < s := by dsimp [s]; linarith [p.hα]
  have hrs : s = r + p.γ := by dsimp [s, r]; linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div p.hγ, hrs]
    linarith
  have hk : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (mul_nonneg hchi.le (sub_pos.mpr hP).le) hr.le
  intro t ht0 htT
  let Z : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s
  let S : ℝ := descentSignedMixed r p.β u v t
  let J : ℝ := descentVGradient r (p.β + 1) u v t
  let Aell : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ r * intervalDomainLift (v t) x *
      (1 + intervalDomainLift (v t) x) ^ (-p.β)
  let Bell : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (r + p.γ) *
      (1 + intervalDomainLift (v t) x) ^ (-p.β)
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hA0 : 0 ≤ Aell := by
    dsimp [Aell]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (mul_nonneg
        (Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
        (lift_v_nonneg_Icc hsol ht0 htT x hx))
        (Real.rpow_nonneg (by
          linarith [lift_v_nonneg_Icc hsol ht0 htT x hx]) _))
  have hBell0 : 0 ≤ Bell := by
    dsimp [Bell]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg
        (Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
        (Real.rpow_nonneg (by
          linarith [lift_v_nonneg_Icc hsol ht0 htT x hx]) _))
  have hid := elliptic_multiplier_ibp_identity_eta
    (p := p) (T := T) (t := t) (r := r) (eta := p.β)
      (u := u) (v := v) hsol ht0 htT
  change p.β * J = r * S + p.μ * Aell - p.ν * Bell at hid
  have hraw : r * S ≤ p.β * J + p.ν * Bell := by
    have hmuA : 0 ≤ p.μ * Aell := mul_nonneg p.hμ.le hA0
    nlinarith
  have hkcancel : k * r = p.χ₀ * (P - 1) := by
    dsimp [k]
    field_simp [hr.ne']
  have hSeq := lpSignedCrossIntegralM_eq_descentSignedMixed
    (P := P) hsol ht0 htT
  have hcross0 :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        k * (p.β * J + p.ν * Bell) := by
    rw [hSeq]
    change p.χ₀ * (P - 1) * S ≤ k * (p.β * J + p.ν * Bell)
    rw [← hkcancel]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hraw hk
  have hJeq : J = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ r *
        (|deriv (intervalDomainLift (v t)) x| ^ 2 /
          (1 + intervalDomainLift (v t) x) ^ (1 + p.β)) := by
    simpa [J, add_comm] using descentVGradient_eq_div
      (r := r) (eta := p.β + 1) hsol ht0 htT
  have hJ := critical_weighted_gradient_moment_le_paperMstar
    (r := r) (s := s) (beta := p.β) hsol ht0 htT hbeta hr hrs
  dsimp only at hJ
  rw [← hJeq] at hJ
  have hroot : intervalPaperMstar p q ^ (1 / q) =
      theorem13CriticalProfile p P := by
    unfold theorem13CriticalProfile
    rw [show (P + p.α) / p.γ = q by rfl]
    congr 1
    dsimp [q, s]
    field_simp [p.hγ.ne', (add_pos hP0 p.hα).ne']
  rw [hroot] at hJ
  have hBdrop : Bell ≤ Z := by
    have hb := weighted_u_power_le_unweighted
      (r := r + p.γ) hsol ht0 htT hbeta
    simpa [Bell, Z, hrs] using hb
  have hPsi : p.β * Theta_beta p.β = Psi_beta p.β := by
    by_cases hb0 : p.β = 0
    · rw [hb0]
      simp [Psi_beta_zero]
    · exact (Psi_beta_eq_beta_mul_Theta_beta
        (lt_of_le_of_ne hbeta (Ne.symm hb0))).symm
  have hinner : p.β * J + p.ν * Bell ≤
      (p.ν + Psi_beta p.β * theorem13CriticalProfile p P) * Z := by
    have hJmul := mul_le_mul_of_nonneg_left hJ hbeta
    have hBmul := mul_le_mul_of_nonneg_left hBdrop p.hν.le
    have hJmul' : p.β * J ≤
        (Psi_beta p.β * theorem13CriticalProfile p P) * Z := by
      calc
        _ ≤ p.β * (Theta_beta p.β * theorem13CriticalProfile p P * Z) := hJmul
        _ = (Psi_beta p.β * theorem13CriticalProfile p P) * Z := by
          rw [← hPsi]
          ring
    nlinarith
  have hcross : p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
      criticalCaseIIICoefficient p P * Z := by
    calc
      _ ≤ k * (p.β * J + p.ν * Bell) := hcross0
      _ ≤ k * ((p.ν + Psi_beta p.β * theorem13CriticalProfile p P) * Z) :=
        mul_le_mul_of_nonneg_left hinner hk
      _ = criticalCaseIIICoefficient p P * Z := by
        dsimp [k, criticalCaseIIICoefficient, r]
        ring
  have hZdomain : Z = intervalDomain.integral
      (fun x => (u t x) ^ (P + p.α)) := by
    dsimp [Z, s]
    exact (intervalDomain_integral_power_lift
      (a := P + p.α) (f := u t)).symm
  rwa [hZdomain] at hcross

/-- Alternative (iv) at an arbitrary finite target.  Choosing any positive
Young parameter leaves part of the diffusion available for the fixed-target
interpolation. -/
theorem critical_case_iv_cross_bound
    {p : CM2Params} {T P eps : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2)
    (hP : 1 < P) (hvalid : 2 - 2 * p.m < P) (heps : 0 < eps) :
    ∀ t, 0 < t → t < T →
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        eps * intervalDomainLpWeightedGradientDissipation P u t +
          ((|p.χ₀| * (P - 1)) ^ 2 / (4 * eps) *
            Theta_beta (2 * p.β - 1) * theorem13CriticalProfile p P) *
            intervalDomain.integral (fun x => (u t x) ^ (P + p.α)) := by
  let r0 : ℝ := P + p.m - 1
  let r2 : ℝ := P + 2 * p.m - 2
  let s : ℝ := P + p.α
  let q : ℝ := s / p.γ
  let beta' : ℝ := 2 * p.β - 1
  let Cmix : ℝ := |p.χ₀| * (P - 1)
  let Cj : ℝ := Cmix ^ 2 / (4 * eps)
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hP1 : 0 < P - 1 := sub_pos.mpr hP
  have hr0 : 0 < r0 := by dsimp [r0]; linarith [p.hm]
  have hr2 : 0 < r2 := by dsimp [r2]; linarith
  have hs : 0 < s := by dsimp [s]; exact add_pos hP0 p.hα
  have hrs : s = r2 + p.γ := by dsimp [s, r2]; linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div p.hγ, hrs]
    linarith
  have hbeta' : 0 ≤ beta' := by dsimp [beta']; linarith
  have hCmix : 0 ≤ Cmix := by dsimp [Cmix]; positivity
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  intro t ht0 htT
  let G : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (P - 2) *
      |deriv (intervalDomainLift (u t)) x| ^ 2
  let Z : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s
  let J : ℝ := descentVGradient r2 (2 * p.β) u v t
  have hsigned := signedCross_abs_le_descentMixed
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      hsol ht0 htT
  have hcross0 : p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
      Cmix * descentMixed r0 p.β u v t := by
    have habs : |p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t| ≤
        Cmix * descentMixed r0 p.β u v t := by
      rw [abs_mul, abs_mul, abs_of_pos hP1]
      dsimp [Cmix, r0]
      exact mul_le_mul_of_nonneg_left hsigned
        (mul_nonneg (abs_nonneg _) hP1.le)
    exact (le_abs_self _).trans habs
  have hyoung := descentMixed_young
    (pExp := P) (r := r0) (C := Cmix) (eps := eps)
      hsol ht0 htT heps
  have hrYoung : 2 * r0 - P = r2 := by dsimp [r0, r2]; ring
  rw [hrYoung] at hyoung
  have hcross1 : p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
      eps * G + Cj * J := by
    calc
      _ ≤ Cmix * descentMixed r0 p.β u v t := hcross0
      _ ≤ eps * G + Cj * J := by simpa [G, Cj, J] using hyoung
  have hJeq : J = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ r2 *
        (|deriv (intervalDomainLift (v t)) x| ^ 2 /
          (1 + intervalDomainLift (v t) x) ^ (1 + beta')) := by
    have hj := descentVGradient_eq_div
      (r := r2) (eta := 2 * p.β) hsol ht0 htT
    simpa [J, beta'] using hj
  have hJ := critical_weighted_gradient_moment_le_paperMstar
    (r := r2) (s := s) (beta := beta') hsol ht0 htT hbeta' hr2 hrs
  dsimp only at hJ
  rw [← hJeq] at hJ
  have hroot : intervalPaperMstar p q ^ (1 / q) =
      theorem13CriticalProfile p P := by
    unfold theorem13CriticalProfile
    rw [show (P + p.α) / p.γ = q by rfl]
    congr 1
    dsimp [q, s]
    field_simp [p.hγ.ne', (add_pos hP0 p.hα).ne']
  rw [hroot] at hJ
  have hCJ : Cj * J ≤
      (Cj * Theta_beta beta' * theorem13CriticalProfile p P) * Z := by
    have hmul := mul_le_mul_of_nonneg_left hJ hCj
    simpa [Z, mul_assoc] using hmul
  have hcross : p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
      eps * G +
        (Cj * Theta_beta beta' * theorem13CriticalProfile p P) * Z := by
    nlinarith
  have hGeq : intervalDomainLpWeightedGradientDissipation P u t = G :=
    weightedDissipation_eq_lift P u t
  have hZeq : Z = intervalDomain.integral
      (fun x => (u t x) ^ (P + p.α)) := by
    dsimp [Z, s]
    exact (intervalDomain_integral_power_lift
      (a := P + p.α) (f := u t)).symm
  rw [← hGeq, hZeq] at hcross
  simpa [Cj, Cmix, beta'] using hcross

/-- Parameter-only target damping remainder after fixing a uniform low seed. -/
def criticalTargetDampingConstant
    (p : CM2Params) (p0 P epsCross Kcross C0 : ℝ) : ℝ :=
  let gap : ℝ := P - 1 - epsCross
  let cGrad : ℝ := P ^ 2 / 4
  let K : ℝ := Kcross + 1
  let epsInterp : ℝ := gap / (2 * K * cGrad)
  let Ceps : ℝ := scalarSeedAgmonAbsorbConstant
    (max C0 0) P p0 p.α epsInterp
  let K0 : ℝ := integralRpowAbsorbConstant P (P + p.α) (p.a + 1) 1
  max 0 (K * Ceps + K0)

/-- A fixed low-seed bound plus one target cross estimate yields autonomous
linear damping at that target. -/
theorem critical_target_lp_energy_damping_of_bound
    {p : CM2Params} {T p0 P epsCross Kcross C0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hP : 1 < P) (hp0 : 0 < p0) (hp0P : p0 ≤ P)
    (halpha2 : p.α < 2 * p0)
    (hseed : ∀ t, 0 < t → t < T →
      intervalDomainM.integral (fun x => (u t x) ^ p0) ≤ C0)
    (hepsGap : epsCross < P - 1)
    (hKcross : 0 ≤ Kcross)
    (hcross : ∀ t, 0 < t → t < T →
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        epsCross * intervalDomainLpWeightedGradientDissipation P u t +
          Kcross * intervalDomain.integral
            (fun x => (u t x) ^ (P + p.α))) :
    0 ≤ criticalTargetDampingConstant p p0 P epsCross Kcross C0 ∧
      ∀ t, 0 < t → t < T →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤
          criticalTargetDampingConstant p p0 P epsCross Kcross C0 := by
  let gap : ℝ := P - 1 - epsCross
  let cGrad : ℝ := P ^ 2 / 4
  let K : ℝ := Kcross + 1
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hcGrad : 0 < cGrad := by dsimp [cGrad]; positivity
  have hK : 0 < K := by dsimp [K]; linarith
  let epsInterp : ℝ := gap / (2 * K * cGrad)
  have hepsInterp : 0 < epsInterp := by
    dsimp [epsInterp]
    positivity
  let Ceps : ℝ := scalarSeedAgmonAbsorbConstant
    (max C0 0) P p0 p.α epsInterp
  have hinterp := intervalDomainM_agmon_absorbed_of_lp_bound
    hsol p.hα hp0 hp0P halpha2 hseed epsInterp hepsInterp
  let K0 : ℝ := integralRpowAbsorbConstant P (P + p.α) (p.a + 1) 1
  obtain ⟨hK0, hYabs⟩ := integral_rpow_absorb
    (r := P) (s := P + p.α) (A := p.a + 1) (eps := 1)
      hsol hP0 (by linarith [p.hα]) (by linarith [p.ha]) zero_lt_one
  let D : ℝ := max 0 (K * Ceps + K0)
  have hDfixed : D =
      criticalTargetDampingConstant p p0 P epsCross Kcross C0 := by
    simp only [D, criticalTargetDampingConstant, gap, cGrad, K, epsInterp,
      Ceps, K0]
  have hD : 0 ≤ D := le_max_left _ _
  refine ⟨by simpa [hDfixed] using hD, ?_⟩
  intro t ht0 htT
  let Y : ℝ := intervalDomainLpEnergy P u t
  let G : ℝ := intervalDomainLpWeightedGradientDissipation P u t
  let Z : ℝ := intervalDomain.integral (fun x => (u t x) ^ (P + p.α))
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hG0 : 0 ≤ G := by
    dsimp [G]
    rw [weightedDissipation_eq_lift P u t]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      exact mul_nonneg
        (Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
        (sq_nonneg _))
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    unfold intervalDomain intervalDomainIntegral
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      simp only [intervalDomainLift, hx, dif_pos]
      exact Real.rpow_nonneg (u_pos hsol ht0 htT ⟨x, hx⟩).le _)
  have hYlift : Y = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ P := by
    dsimp [Y]
    exact lpEnergy_eq_lift_power_of_solution hsol ht0 htT
  have hZlift : Z = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (P + p.α) := by
    dsimp [Z]
    exact intervalDomain_integral_power_lift (a := P + p.α) (f := u t)
  have hYeq : Y = intervalDomain.integral (fun x => (u t x) ^ P) := by
    rw [hYlift]
    exact (intervalDomain_integral_power_lift (a := P) (f := u t)).symm
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      hP0.ne' hsol ht0 htT
  rw [← hYeq] at henergy
  change (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
      (P - 1) * G + p.b * Z =
        p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t + p.a * Y
    at henergy
  have hcrossAt := hcross t ht0 htT
  change p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
      epsCross * G + Kcross * Z at hcrossAt
  have hYabsAt := hYabs t ht0 htT
  rw [← hYlift, ← hZlift] at hYabsAt
  norm_num at hYabsAt
  change (p.a + 1) * Y ≤ Z + K0 at hYabsAt
  have hinterpAt := hinterp t ht0 htT
  change Z ≤ epsInterp * (cGrad * G) + Ceps at hinterpAt
  have hKinterp : K * Z ≤ gap / 2 * G + K * Ceps := by
    have hmul := mul_le_mul_of_nonneg_left hinterpAt hK.le
    have hcoef : K * (epsInterp * cGrad) = gap / 2 := by
      dsimp [epsInterp]
      field_simp [hK.ne', hcGrad.ne']
    nlinarith
  have hbZ : 0 ≤ p.b * Z := mul_nonneg p.hb hZ0
  have hDtop : K * Ceps + K0 ≤ D := le_max_right _ _
  rw [← hDfixed]
  change (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t + Y ≤ D
  dsimp [gap, K] at hKinterp
  nlinarith

/-- Existential wrapper retained for the finite-horizon boundedness chain. -/
theorem critical_target_lp_energy_damping_of_cross
    {p : CM2Params} {T p0 P epsCross Kcross : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hP : 1 < P) (hp0 : 0 < p0) (hp0P : p0 ≤ P)
    (halpha2 : p.α < 2 * p0)
    (hseed : LpPowerBoundedBefore intervalDomainM p0 T u)
    (hepsGap : epsCross < P - 1)
    (hKcross : 0 ≤ Kcross)
    (hcross : ∀ t, 0 < t → t < T →
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        epsCross * intervalDomainLpWeightedGradientDissipation P u t +
          Kcross * intervalDomain.integral
            (fun x => (u t x) ^ (P + p.α))) :
    ∃ D ≥ 0, ∀ t, 0 < t → t < T →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤ D := by
  obtain ⟨C0, hseed0⟩ := hseed
  refine ⟨criticalTargetDampingConstant p p0 P epsCross Kcross C0, ?_⟩
  exact critical_target_lp_energy_damping_of_bound hsol hP hp0 hp0P
    halpha2 hseed0 hepsGap hKcross hcross

theorem critical_target_lp_power_bounded_before_of_cross
    {p : CM2Params} {T p0 P epsCross Kcross : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hP : 1 < P) (hp0 : 0 < p0) (hp0P : p0 ≤ P)
    (halpha2 : p.α < 2 * p0)
    (hseed : LpPowerBoundedBefore intervalDomainM p0 T u)
    (hepsGap : epsCross < P - 1)
    (hKcross : 0 ≤ Kcross)
    (hcross : ∀ t, 0 < t → t < T →
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        epsCross * intervalDomainLpWeightedGradientDissipation P u t +
          Kcross * intervalDomain.integral
            (fun x => (u t x) ^ (P + p.α))) :
    LpPowerBoundedBefore intervalDomainM P T u := by
  obtain ⟨D, _hD, hdamp⟩ := critical_target_lp_energy_damping_of_cross
    hsol hP hp0 hp0P halpha2 hseed hepsGap hKcross hcross
  exact lp_power_bounded_before_of_linear_damping hu₀ hsol htrace
    hP zero_lt_one (by simpa using hdamp)

/-- A target power above both the low seed and every restarted-endpoint
threshold. -/
def criticalEndpointExponent (p : CM2Params) (p0 : ℝ) : ℝ :=
  max (strictEndpointExponent p) p0 + 1

lemma criticalEndpointExponent_gt_seed (p : CM2Params) (p0 : ℝ) :
    p0 < criticalEndpointExponent p p0 := by
  unfold criticalEndpointExponent
  linarith [le_max_right (strictEndpointExponent p) p0]

lemma criticalEndpointExponent_gt_two (p : CM2Params) (p0 : ℝ) :
    2 < criticalEndpointExponent p p0 := by
  unfold criticalEndpointExponent
  linarith [le_max_left (strictEndpointExponent p) p0,
    strictEndpointExponent_gt_two p]

lemma criticalEndpointExponent_gt_m (p : CM2Params) (p0 : ℝ) :
    p.m < criticalEndpointExponent p p0 :=
  (strictEndpointExponent_gt_m p).trans (by
    unfold criticalEndpointExponent
    linarith [le_max_left (strictEndpointExponent p) p0])

lemma criticalEndpointExponent_ge_gamma (p : CM2Params) (p0 : ℝ) :
    p.γ ≤ criticalEndpointExponent p p0 :=
  (strictEndpointExponent_ge_gamma p).trans (by
    unfold criticalEndpointExponent
    linarith [le_max_left (strictEndpointExponent p) p0])

theorem boundedBefore_of_critical_endpoint_power
    {p : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hLp : LpPowerBoundedBefore intervalDomainM
      (criticalEndpointExponent p p0) T u) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  let P := criticalEndpointExponent p p0
  let Q := P / p.m
  have hP : 1 < P := one_lt_two.trans (criticalEndpointExponent_gt_two p p0)
  have hmP : p.m < P := criticalEndpointExponent_gt_m p p0
  have hQ : 1 < Q := by
    dsimp [Q]
    exact (lt_div_iff₀ p.hm).2 (by simpa using hmP)
  have hmQ : p.m * Q = P := by
    dsimp [Q]
    field_simp [p.hm.ne']
  exact boundedBefore_of_lp_restarted_affine_general hu₀ hsol htrace
    hP hQ hmQ (criticalEndpointExponent_ge_gamma p p0) hLp

/-- The original critical alternative (iii), with the literal paper constant,
closes on every finite classical horizon. -/
theorem boundedBefore_critical_case_iii
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * theorem13CriticalK p))) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  obtain ⟨p0, hqp0, hseed⟩ := critical_case_iii_threshold_lp_seed
    hN hb hu₀ hsol htrace hchi hbeta hcrit hthreshold
  let P := criticalEndpointExponent p p0
  have hp0 : 0 < p0 :=
    (theorem13CriticalQStar_pos p).trans hqp0
  have hp0P : p0 ≤ P := (criticalEndpointExponent_gt_seed p p0).le
  have hP : 1 < P := one_lt_two.trans (criticalEndpointExponent_gt_two p p0)
  have hqeq := theorem13CriticalQStar_eq_interval p hN
  have halphaHalf : p.α / 2 ≤ theorem13CriticalQStar p := by
    rw [hqeq]
    exact le_max_right _ _
  have halpha2 : p.α < 2 * p0 := by linarith
  let Kcross := criticalCaseIIICoefficient p P
  have hsP : 1 < (P + p.α) / p.γ := by
    rw [one_lt_div p.hγ, hcrit]
    linarith [p.hm]
  have hKcross : 0 ≤ Kcross := by
    dsimp [Kcross, criticalCaseIIICoefficient]
    have hden : 0 < P - 1 + p.m := by linarith [p.hm]
    have hpsi := Psi_beta_nonneg hbeta
    have hprof := (theorem13CriticalProfile_pos p hsP).le
    exact mul_nonneg
      (div_nonneg (mul_nonneg hchi.le (sub_pos.mpr hP).le) hden.le)
      (add_nonneg p.hν.le (mul_nonneg hpsi hprof))
  have hcross := critical_case_iii_cross_bound
    hsol hchi hbeta hcrit hP
  have hLp : LpPowerBoundedBefore intervalDomainM P T u :=
    critical_target_lp_power_bounded_before_of_cross
      hu₀ hsol htrace hP hp0 hp0P halpha2 hseed
      (by linarith : (0 : ℝ) < P - 1) hKcross (by
        intro t ht0 htT
        simpa [Kcross] using hcross t ht0 htT)
  exact boundedBefore_of_critical_endpoint_power hu₀ hsol htrace hLp

/-- Corrected critical alternative (iv).  The additional `q_* > 2-2m`
assumption is the missing Proposition-2.2 exponent-domain condition in the
printed proof. -/
theorem boundedBefore_critical_case_iv_corrected
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2)
    (hvalid : 2 - 2 * p.m < theorem13CriticalQStar p)
    (hthreshold :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ < Real.sqrt
          (8 * p.b /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              Theta_beta (2 * p.β - 1) * theorem13CriticalK p))) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  obtain ⟨p0, hqp0, hseed⟩ := critical_case_iv_threshold_lp_seed
    hN hb hu₀ hsol htrace hchi hbeta hcrit hvalid hthreshold
  let P := criticalEndpointExponent p p0
  have hp0 : 0 < p0 := (theorem13CriticalQStar_pos p).trans hqp0
  have hp0P : p0 ≤ P := (criticalEndpointExponent_gt_seed p p0).le
  have hP : 1 < P := one_lt_two.trans (criticalEndpointExponent_gt_two p p0)
  have hvalidP : 2 - 2 * p.m < P :=
    hvalid.trans (hqp0.trans (criticalEndpointExponent_gt_seed p p0))
  have hqeq := theorem13CriticalQStar_eq_interval p hN
  have halphaHalf : p.α / 2 ≤ theorem13CriticalQStar p := by
    rw [hqeq]
    exact le_max_right _ _
  have halpha2 : p.α < 2 * p0 := by linarith
  let epsCross : ℝ := (P - 1) / 2
  let Kcross : ℝ :=
    ((|p.χ₀| * (P - 1)) ^ 2 / (4 * epsCross) *
      Theta_beta (2 * p.β - 1) * theorem13CriticalProfile p P)
  have heps : 0 < epsCross := by dsimp [epsCross]; linarith
  have hepsGap : epsCross < P - 1 := by dsimp [epsCross]; linarith
  have hsP : 1 < (P + p.α) / p.γ := by
    rw [one_lt_div p.hγ, hcrit]
    linarith
  have hbeta' : 0 ≤ 2 * p.β - 1 := by linarith
  have hKcross : 0 ≤ Kcross := by
    dsimp [Kcross]
    exact mul_nonneg
      (mul_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) heps.le))
        (Theta_beta_nonneg hbeta'))
      (theorem13CriticalProfile_pos p hsP).le
  have hcross := critical_case_iv_cross_bound
    hsol hbeta hcrit hP hvalidP heps
  have hLp : LpPowerBoundedBefore intervalDomainM P T u :=
    critical_target_lp_power_bounded_before_of_cross
      hu₀ hsol htrace hP hp0 hp0P halpha2 hseed
      hepsGap hKcross (by
        intro t ht0 htT
        simpa [Kcross, epsCross] using hcross t ht0 htT)
  exact boundedBefore_of_critical_endpoint_power hu₀ hsol htrace hLp

#print axioms intervalDomainM_supNorm_rpow_le_energy_plus_weighted
#print axioms intervalDomainM_agmon_absorbed_of_lp_seed
#print axioms critical_case_iii_cross_bound
#print axioms critical_case_iv_cross_bound
#print axioms critical_target_lp_energy_damping_of_cross
#print axioms critical_target_lp_power_bounded_before_of_cross
#print axioms boundedBefore_of_critical_endpoint_power
#print axioms boundedBefore_critical_case_iii
#print axioms boundedBefore_critical_case_iv_corrected

end ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap
