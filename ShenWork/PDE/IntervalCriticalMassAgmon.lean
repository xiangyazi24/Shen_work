import ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap

/-!
# Critical mass Agmon absorption on the unit interval

At the endpoint where the excess population power is exactly two, the
physical `L¹` mass no longer absorbs the higher moment with an arbitrarily
small gradient coefficient.  This file keeps the endpoint coefficient
explicit.  For every `P > 1` and `0 < θ < 1`,

`∫ u^(P+2) ≤ P² M² / (1-θ)² · ∫ u^(P-2)|uₓ|² + C(P,θ,M)`.

The coefficient approaches the endpoint value `P² M²` as `θ ↓ 0`; the
remainder then diverges.  This is the strict-coefficient phenomenon needed
by the `m = 2` minimal-model energy estimate.
-/

open MeasureTheory Set
open scoped Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

namespace ShenWork.IntervalDomainExistence.IntervalCriticalMassAgmon

noncomputable section

/-- The scalar Young remainder before the final endpoint square-root
absorption.  Its expanded value is

`2^(P+1) P^P M^(P+2) / ((P+1)^(P+1) θ^P)`.

The unexpanded definition follows exactly the output shape of
`scalar_rpow_young_absorb`, which avoids any integer-exponent restriction on
the real test exponent `P`. -/
def criticalMassAgmonYoungRemainder (P theta M : ℝ) : ℝ :=
  let b : ℝ := (P + 1) / P
  ((2 * M ^ 2 /
      ((theta * M * (b / 1)) ^ (1 / b))) ^
        (b / (b - 1))) /
    (b / (b - 1))

/-- The complete lower-order remainder after division by
`a = (1-θ)/2`. -/
def criticalMassAgmonRemainder (P theta M : ℝ) : ℝ :=
  criticalMassAgmonYoungRemainder P theta M / ((1 - theta) / 2)

set_option maxHeartbeats 1000000 in
-- Real-power endpoint normalization and the weighted square-root split are expensive.
/-- Scalar endpoint Agmon absorption.  `S` represents `‖u‖∞^P` and `G`
represents `∫ |∂ₓ(u^(P/2))|²`. -/
theorem scalar_mass_critical_agmon
    {P theta M S G : ℝ}
    (hP : 1 < P) (hM : 0 < M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hS : 0 ≤ S) (hG : 0 ≤ G)
    (hSineq :
      S ≤ 2 * M * S ^ ((P - 1) / P) +
        2 * Real.sqrt (M * S ^ ((P - 1) / P)) * Real.sqrt G) :
    M * S ^ ((P + 1) / P) ≤
      (4 / (1 - theta) ^ 2) * M ^ 2 * G +
        criticalMassAgmonRemainder P theta M := by
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hPne : P ≠ 0 := ne_of_gt hP0
  let b : ℝ := (P + 1) / P
  let a : ℝ := (1 - theta) / 2
  let X : ℝ := M * S ^ b
  let C : ℝ := criticalMassAgmonYoungRemainder P theta M
  have hb1 : 1 < b := by
    dsimp [b]
    rw [one_lt_div hP0]
    linarith
  have hb0 : 0 < b := lt_trans zero_lt_one hb1
  have hbsub : 0 < b - 1 := sub_pos.mpr hb1
  have hbconj : 0 < b / (b - 1) := div_pos hb0 hbsub
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hthetaM : 0 < theta * M := mul_pos htheta0 hM
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg hM.le (Real.rpow_nonneg hS _)
  have hC : 0 ≤ C := by
    change 0 ≤
      ((2 * M ^ 2 /
          ((theta * M * (b / 1)) ^ (1 / b))) ^
            (b / (b - 1))) /
        (b / (b - 1))
    exact div_nonneg
      (Real.rpow_nonneg
        (div_nonneg (by positivity)
          (Real.rpow_nonneg
            (mul_nonneg hthetaM.le (div_nonneg hb0.le zero_le_one)) _)) _)
      hbconj.le
  by_cases hSz : S = 0
  · subst S
    have hrem : 0 ≤ criticalMassAgmonRemainder P theta M := by
      dsimp [criticalMassAgmonRemainder]
      exact div_nonneg hC ha.le
    change M * (0 : ℝ) ^ b ≤
      (4 / (1 - theta) ^ 2) * M ^ 2 * G +
        criticalMassAgmonRemainder P theta M
    rw [Real.zero_rpow (ne_of_gt hb0), mul_zero]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
          (sq_nonneg M)) hG)
      hrem
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
  have hpowOne :
      S ^ (1 / P) * S = S ^ b := by
    calc
      S ^ (1 / P) * S =
          S ^ (1 / P) * S ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = S ^ (1 / P + 1) := (Real.rpow_add hSpos _ _).symm
      _ = S ^ b := by
        congr 1
        dsimp [b]
        field_simp [hPne]
        ring
  have hsqrt_rpow (e : ℝ) :
      Real.sqrt (S ^ e) = S ^ (e / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hSpos.le]
    congr 1
    ring
  have hpowCross :
      S ^ (1 / P) *
          Real.sqrt (M * S ^ ((P - 1) / P)) =
        Real.sqrt X := by
    have hsqrtBase :
        Real.sqrt (M * S ^ ((P - 1) / P)) =
          Real.sqrt M * S ^ (((P - 1) / P) / 2) := by
      rw [Real.sqrt_mul hM.le]
      rw [hsqrt_rpow]
    have hsqrtX :
        Real.sqrt X = Real.sqrt M * S ^ (b / 2) := by
      dsimp [X]
      rw [Real.sqrt_mul hM.le]
      rw [hsqrt_rpow]
    rw [hsqrtBase, hsqrtX]
    calc
      S ^ (1 / P) *
          (Real.sqrt M * S ^ (((P - 1) / P) / 2)) =
          Real.sqrt M *
            (S ^ (1 / P) * S ^ (((P - 1) / P) / 2)) := by ring
      _ = Real.sqrt M *
          S ^ (1 / P + ((P - 1) / P) / 2) := by
            rw [(Real.rpow_add hSpos _ _).symm]
      _ = Real.sqrt M * S ^ (b / 2) := by
        congr 2
        dsimp [b]
        field_simp [hPne]
        ring
  have hmult := mul_le_mul_of_nonneg_left hSineq
    (mul_nonneg hM.le (Real.rpow_nonneg hS (1 / P)))
  have hXineq :
      X ≤ 2 * M ^ 2 * S + 2 * M * Real.sqrt X * Real.sqrt G := by
    calc
      X = M * (S ^ (1 / P) * S) := by rw [hpowOne]
      _ ≤ M * S ^ (1 / P) *
          (2 * M * S ^ ((P - 1) / P) +
            2 * Real.sqrt (M * S ^ ((P - 1) / P)) * Real.sqrt G) := by
              simpa [mul_assoc] using hmult
      _ = 2 * M ^ 2 * S + 2 * M * Real.sqrt X * Real.sqrt G := by
        have hpowExp :
            S ^ (1 / P) * S ^ ((P - 1) / P) = S := by
          rw [← Real.rpow_add hSpos]
          have hexp : 1 / P + (P - 1) / P = 1 := by
            field_simp [hPne]
            ring
          rw [hexp, Real.rpow_one]
        have hfirst :
            M * S ^ (1 / P) *
                (2 * M * S ^ ((P - 1) / P)) =
              2 * M ^ 2 * S := by
          calc
            M * S ^ (1 / P) *
                (2 * M * S ^ ((P - 1) / P)) =
                2 * M ^ 2 *
                  (S ^ (1 / P) * S ^ ((P - 1) / P)) := by ring
            _ = 2 * M ^ 2 * S := by rw [hpowExp]
        have hsecond :
            M * S ^ (1 / P) *
                (2 * Real.sqrt (M * S ^ ((P - 1) / P)) *
                  Real.sqrt G) =
              2 * M * Real.sqrt X * Real.sqrt G := by
          calc
            M * S ^ (1 / P) *
                (2 * Real.sqrt (M * S ^ ((P - 1) / P)) *
                  Real.sqrt G) =
                2 * M *
                  (S ^ (1 / P) *
                    Real.sqrt (M * S ^ ((P - 1) / P))) *
                  Real.sqrt G := by ring
            _ = 2 * M * Real.sqrt X * Real.sqrt G := by rw [hpowCross]
        rw [mul_add, hfirst, hsecond]
  have hyoungRaw := scalar_rpow_young_absorb
    (r := (1 : ℝ)) (s := b) (A := 2 * M ^ 2)
    (eps := theta * M) (x := S)
    (by norm_num) hb1 (by positivity) hthetaM hS
  have hyoung :
      2 * M ^ 2 * S ≤ theta * X + C := by
    simpa [X, C, criticalMassAgmonYoungRemainder, b,
      Real.rpow_one, mul_assoc] using hyoungRaw
  have hsqrtXsq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX
  have hsqrtGsq : (Real.sqrt G) ^ 2 = G := Real.sq_sqrt hG
  have hweightedYoung :
      2 * M * Real.sqrt X * Real.sqrt G ≤
        a * X + (M ^ 2 / a) * G := by
    have hsq := sq_nonneg
      (Real.sqrt X - (M / a) * Real.sqrt G)
    have hbase :
        2 * (M / a) * Real.sqrt X * Real.sqrt G ≤
          X + (M / a) ^ 2 * G := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hbase ha.le
    field_simp [ne_of_gt ha] at hmul ⊢
    nlinarith
  have hretain :
      a * X ≤ C + (M ^ 2 / a) * G := by
    have haeq : a = 1 - theta - a := by
      dsimp [a]
      ring
    have hsum :
        X ≤ theta * X + C + a * X + (M ^ 2 / a) * G := by
      calc
        X ≤ 2 * M ^ 2 * S +
            2 * M * Real.sqrt X * Real.sqrt G := hXineq
        _ ≤ (theta * X + C) +
            (a * X + (M ^ 2 / a) * G) :=
          add_le_add hyoung hweightedYoung
        _ = theta * X + C + a * X + (M ^ 2 / a) * G := by ring
    nlinarith [hsum, haeq]
  have hdivide :
      X ≤ C / a + (M ^ 2 / a ^ 2) * G := by
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hxdiv : X ≤ (C + (M ^ 2 / a) * G) / a :=
      (le_div_iff₀ ha).2 (by simpa [mul_comm] using hretain)
    calc
      X ≤ (C + (M ^ 2 / a) * G) / a := hxdiv
      _ = C / a + (M ^ 2 / a ^ 2) * G := by
        field_simp [ha_ne]
  have hcoef :
      M ^ 2 / a ^ 2 = (4 / (1 - theta) ^ 2) * M ^ 2 := by
    dsimp [a]
    field_simp [ne_of_gt (sub_pos.mpr htheta1)]
    ring
  rw [hcoef] at hdivide
  simpa [X, C, criticalMassAgmonRemainder, add_comm] using hdivide

set_option maxHeartbeats 1000000 in
-- The slice bridge carries three real-power interpolation rewrites.
/-- Endpoint mass Agmon inequality for a positive classical slice of the
faithful general-`m` equation. -/
theorem intervalDomainM_mass_critical_agmon
    {p : CM2Params} {T t P M theta : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hP : 1 < P) (hM : 0 < M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hmass : intervalDomain.integral (u t) = M) :
    intervalDomain.integral (fun x => (u t x) ^ (P + 2)) ≤
      (P ^ 2 / (1 - theta) ^ 2) * M ^ 2 *
          intervalDomainLpWeightedGradientDissipation P u t +
        criticalMassAgmonRemainder P theta M := by
  let U : ℝ := intervalDomainSupNorm (u t)
  let S : ℝ := U ^ P
  let Y : ℝ := intervalDomain.integral (fun x => (u t x) ^ P)
  let G : ℝ := (P ^ 2 / 4) *
    intervalDomainLpWeightedGradientDissipation P u t
  let seed : ℝ := intervalDomain.integral (fun x => (u t x) ^ (1 : ℝ))
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hPne : P ≠ 0 := ne_of_gt hP0
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hfpos : ∀ x : intervalDomain.Point, 0 < u t x :=
    fun x => hsol.u_pos' ht0 htT
  have hf0 : ∀ x : intervalDomain.Point, 0 ≤ u t x :=
    fun x => (hfpos x).le
  have hfbdd : BddAbove (range fun x : intervalDomain.Point => |u t x|) :=
    ShenWork.Paper2.IntervalDomainM.solution_slice_abs_bddAbove hsol ht
  have hpowerLiftCont : ∀ q : ℝ, ContinuousOn
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ q))
      (Icc (0 : ℝ) 1) := by
    intro q
    refine
      (ShenWork.Paper2.IntervalDomainM.power_continuousOn_timeSlice
        (q := q) hsol ht).congr ?_
    intro y hy
    simp [intervalDomainLift, hy]
  have hseedInt : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ (1 : ℝ)))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hpowerLiftCont 1
  have hYInt : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ P))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hpowerLiftCont P
  have hhighInt : IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ (P + 2)))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hpowerLiftCont (P + 2)
  have hYleftInt : IntervalIntegrable
      (intervalDomainLift
        (fun x : intervalDomain.Point => (u t x) ^ ((1 : ℝ) + (P - 1))))
      volume 0 1 := by
    simpa [show (1 : ℝ) + (P - 1) = P by ring] using hYInt
  have hhighLeftInt : IntervalIntegrable
      (intervalDomainLift
        (fun x : intervalDomain.Point => (u t x) ^ ((1 : ℝ) + (P + 1))))
      volume 0 1 := by
    simpa [show (1 : ℝ) + (P + 1) = P + 2 by ring] using hhighInt
  have hU0 : 0 ≤ U := by
    dsimp [U]
    exact intervalDomainSupNorm_nonneg _
  have hS0 : 0 ≤ S := Real.rpow_nonneg hU0 _
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (by positivity) (by
      unfold intervalDomainLpWeightedGradientDissipation intervalDomain
      exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
        simp only [intervalDomainLift, hx, dif_pos]
        exact mul_nonneg (Real.rpow_nonneg (hfpos ⟨x, hx⟩).le _)
          (sq_nonneg _)))
  have hseedEq : seed = M := by
    dsimp [seed]
    simpa only [Real.rpow_one] using hmass
  have hYraw := intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
    (f := u t) hf0 hfbdd (pExp := (1 : ℝ)) (rho := P - 1)
      (by norm_num) (sub_nonneg.mpr hP.le) hYleftInt hseedInt
  have hYseed : Y ≤ U ^ (P - 1) * seed := by
    simpa [Y, U, seed, show (1 : ℝ) + (P - 1) = P by ring] using hYraw
  have hUtheta :
      U ^ (P - 1) = S ^ ((P - 1) / P) := by
    have hmul : P * ((P - 1) / P) = P - 1 := by
      field_simp [hPne]
    calc
      U ^ (P - 1) = U ^ (P * ((P - 1) / P)) := by rw [hmul]
      _ = (U ^ P) ^ ((P - 1) / P) := by rw [Real.rpow_mul hU0]
      _ = S ^ ((P - 1) / P) := rfl
  have hYle :
      Y ≤ M * S ^ ((P - 1) / P) := by
    calc
      Y ≤ U ^ (P - 1) * seed := hYseed
      _ = M * S ^ ((P - 1) / P) := by rw [hseedEq, hUtheta]; ring
  have hsup :
      S ≤ 2 * Y + 2 * Real.sqrt Y * Real.sqrt G := by
    simpa [S, U, Y, G] using
      intervalDomainM_supNorm_rpow_le_energy_plus_weighted
        hsol ht0 htT hP0
  have hSineq :
      S ≤ 2 * M * S ^ ((P - 1) / P) +
        2 * Real.sqrt (M * S ^ ((P - 1) / P)) * Real.sqrt G := by
    calc
      S ≤ 2 * Y + 2 * Real.sqrt Y * Real.sqrt G := hsup
      _ ≤ 2 * (M * S ^ ((P - 1) / P)) +
          2 * Real.sqrt (M * S ^ ((P - 1) / P)) * Real.sqrt G := by
        have hsqrt := Real.sqrt_le_sqrt hYle
        have hsqrtMul :=
          mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg G)
        nlinarith
      _ = _ := by ring
  have hhighRaw := intervalDomain_higher_Lp_le_Linf_rpow_mul_seed
    (f := u t) hf0 hfbdd (pExp := (1 : ℝ)) (rho := P + 1)
      (by norm_num) (by linarith) hhighLeftInt hseedInt
  have hhighSeed :
      intervalDomain.integral (fun x => (u t x) ^ (P + 2)) ≤
        U ^ (P + 1) * seed := by
    simpa [U, seed, show (1 : ℝ) + (P + 1) = P + 2 by ring] using hhighRaw
  have hUalpha :
      U ^ (P + 1) = S ^ ((P + 1) / P) := by
    have hmul : P * ((P + 1) / P) = P + 1 := by
      field_simp [hPne]
    calc
      U ^ (P + 1) = U ^ (P * ((P + 1) / P)) := by rw [hmul]
      _ = (U ^ P) ^ ((P + 1) / P) := by rw [Real.rpow_mul hU0]
      _ = S ^ ((P + 1) / P) := rfl
  have hhighLe :
      intervalDomain.integral (fun x => (u t x) ^ (P + 2)) ≤
        M * S ^ ((P + 1) / P) := by
    calc
      _ ≤ U ^ (P + 1) * seed := hhighSeed
      _ = M * S ^ ((P + 1) / P) := by rw [hseedEq, hUalpha]; ring
  have hscalar := scalar_mass_critical_agmon
    hP hM htheta0 htheta1 hS0 hG0 hSineq
  calc
    intervalDomain.integral (fun x => (u t x) ^ (P + 2))
        ≤ M * S ^ ((P + 1) / P) := hhighLe
    _ ≤ (4 / (1 - theta) ^ 2) * M ^ 2 * G +
          criticalMassAgmonRemainder P theta M := hscalar
    _ = (P ^ 2 / (1 - theta) ^ 2) * M ^ 2 *
          intervalDomainLpWeightedGradientDissipation P u t +
          criticalMassAgmonRemainder P theta M := by
      dsimp [G]
      ring

#print axioms scalar_mass_critical_agmon
#print axioms intervalDomainM_mass_critical_agmon

end

end ShenWork.IntervalDomainExistence.IntervalCriticalMassAgmon
