/-
Direct strong-logistic finite-power producers for Paper 2, Theorem 1.3.

This file works only with the paper-faithful general-m domain.  The common
analytic atom below combines Proposition 2.2 with two scalar Young
inequalities: a weighted v-gradient moment whose u-exponent is strictly below
the logistic exponent can be absorbed with an arbitrarily small coefficient.
-/
import ShenWork.Paper2.IntervalDomainMWeightedGradient
import ShenWork.Paper2.IntervalDomainMCriticalLpBootstrap

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep

/-- Scalar Young with the second factor retained as its conjugate power. -/
theorem rpow_mul_young_absorb
    {r s eps U W : ℝ} (hr : 0 < r) (hrs : r < s)
    (heps : 0 < eps) (hU : 0 ≤ U) (hW : 0 ≤ W) :
    let q := s / (s - r)
    let d := (eps * (s / r)) ^ (r / s)
    U ^ r * W ≤ eps * U ^ s + (1 / (d ^ q * q)) * W ^ q := by
  dsimp only
  let q : ℝ := s / (s - r)
  let d : ℝ := (eps * (s / r)) ^ (r / s)
  have hs : 0 < s := lt_trans hr hrs
  have hsr : 0 < s - r := sub_pos.mpr hrs
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div hsr]
    linarith
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hsrdiv : 0 < s / r := div_pos hs hr
  have hd : 0 < d := by
    dsimp [d]
    exact Real.rpow_pos_of_pos (mul_pos heps hsrdiv) _
  have hy := scalar_rpow_young_absorb hr hrs hW heps hU
  have hquot :
      ((W / d) ^ q) / q = (1 / (d ^ q * q)) * W ^ q := by
    rw [Real.div_rpow hW hd.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hd q), ne_of_gt hq0]
  change W * U ^ r ≤ eps * U ^ s + ((W / d) ^ q) / q at hy
  rw [hquot] at hy
  calc
    U ^ r * W = W * U ^ r := by ring
    _ ≤ eps * U ^ s + (1 / (d ^ q * q)) * W ^ q := hy
    _ = eps * U ^ s +
        (1 / (((eps * (s / r)) ^ (r / s)) ^ (s / (s - r)) *
          (s / (s - r)))) * W ^ (s / (s - r)) := by
      dsimp [q, d]

/-- Algebra identifying the conjugate power of the weighted gradient
factor with the exact integrand in Proposition 2.2. -/
theorem weighted_gradient_factor_rpow
    {q beta Vx V : ℝ} (hq : 0 ≤ q) (hV : 0 ≤ V) :
    (|Vx| ^ 2 / (1 + V) ^ (1 + beta)) ^ q =
      |Vx| ^ (2 * q) / (1 + V) ^ ((1 + beta) * q) := by
  have hbase : 0 ≤ 1 + V := by linarith
  rw [Real.div_rpow (sq_nonneg _) (Real.rpow_nonneg hbase _),
    ← Real.rpow_mul hbase]
  have habs : 0 ≤ |Vx| := abs_nonneg _
  rw [show |Vx| ^ (2 : ℕ) = |Vx| ^ (2 : ℝ) by
      simp,
    ← Real.rpow_mul habs]

/-- Division form of the weighted signal-gradient integral. -/
theorem descentVGradient_eq_div
    {p : CM2Params} {T t r eta : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    descentVGradient r eta u v t =
      ∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ r *
          (|deriv (intervalDomainLift (v t)) x| ^ 2 /
            (1 + intervalDomainLift (v t) x) ^ eta) := by
  unfold descentVGradient
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  have hbase : 0 < 1 + intervalDomainLift (v t) x := by
    have hv := lift_v_nonneg_Icc hsol ht0 htT x hx
    linarith
  change intervalDomainLift (u t) x ^ r *
      |deriv (intervalDomainLift (v t)) x| ^ 2 *
        (1 + intervalDomainLift (v t) x) ^ (-eta) =
    intervalDomainLift (u t) x ^ r *
      (|deriv (intervalDomainLift (v t)) x| ^ 2 /
        (1 + intervalDomainLift (v t) x) ^ eta)
  rw [Real.rpow_neg hbase.le]
  simp only [div_eq_mul_inv]
  ring

/-- The signed cross term is the elliptic multiplier's signed mixed term at
`r = P + m - 1`. -/
theorem lpSignedCrossIntegralM_eq_descentSignedMixed
    {p : CM2Params} {T t P : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    lpSignedCrossIntegralM p P u v t =
      descentSignedMixed (P + p.m - 1) p.β u v t := by
  unfold lpSignedCrossIntegralM descentSignedMixed
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  have hbase : 0 < 1 + intervalDomainLift (v t) x := by
    have hv := lift_v_nonneg_Icc hsol ht0 htT x hx
    linarith
  change intervalDomainLift (u t) x ^ (P + p.m - 2) *
      deriv (intervalDomainLift (u t)) x *
        deriv (intervalDomainLift (v t)) x /
          (1 + intervalDomainLift (v t) x) ^ p.β =
    intervalDomainLift (u t) x ^ (P + p.m - 1 - 1) *
      deriv (intervalDomainLift (u t)) x *
        deriv (intervalDomainLift (v t)) x *
          (1 + intervalDomainLift (v t) x) ^ (-p.β)
  rw [Real.rpow_neg hbase.le]
  simp only [div_eq_mul_inv]
  ring

/-- A nonnegative denominator weight can only decrease a positive power
moment because the chemical signal is nonnegative. -/
theorem weighted_u_power_le_unweighted
    {p : CM2Params} {T t r beta : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hbeta : 0 ≤ beta) :
    (∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ r *
        (1 + intervalDomainLift (v t) x) ^ (-beta)) ≤
      ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ r := by
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUcont := solution_lift_continuousOn_Icc hsol ht
  have hVcont := (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hdInt : IntervalIntegrable (fun x =>
      intervalDomainLift (u t) x ^ r *
        (1 + intervalDomainLift (v t) x) ^ (-beta)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (hUcont.rpow_const (fun x hx => Or.inl
      (ne_of_gt (solution_lift_pos_Icc hsol ht x hx)))).mul
        ((continuousOn_const.add hVcont).rpow_const (fun x hx => Or.inl
          (ne_of_gt (show 0 < 1 + intervalDomainLift (v t) x by
            linarith [lift_v_nonneg_Icc hsol ht0 htT x hx]))))
  have huInt : IntervalIntegrable
      (fun x => intervalDomainLift (u t) x ^ r) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hUcont.rpow_const (fun x hx => Or.inl
      (ne_of_gt (solution_lift_pos_Icc hsol ht x hx)))
  exact intervalIntegral.integral_mono_on (by norm_num) hdInt huInt
    (fun x hx => by
      have hu : 0 ≤ intervalDomainLift (u t) x ^ r :=
        Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _
      have hw : (1 + intervalDomainLift (v t) x) ^ (-beta) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos
          (by linarith [lift_v_nonneg_Icc hsol ht0 htT x hx]) (by linarith)
      simpa using mul_le_mul_of_nonneg_left hw hu)

/-- A lower positive moment is absorbed into a higher one on the unit
interval, with an explicit time-independent remainder. -/
theorem integral_rpow_absorb
    {p : CM2Params} {T r s A eps : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hr : 0 < r) (hrs : r < s) (hA : 0 ≤ A) (heps : 0 < eps) :
    ∃ K ≥ 0, ∀ t, 0 < t → t < T →
      A * (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ r) ≤
        eps * (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s) + K := by
  let K : ℝ :=
    ((A / (eps * (s / r)) ^ (r / s)) ^ (s / (s - r))) /
      (s / (s - r))
  have hs : 0 < s := lt_trans hr hrs
  have hden : 0 < s / (s - r) := div_pos hs (sub_pos.mpr hrs)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg
      (Real.rpow_nonneg
        (div_nonneg hA (Real.rpow_nonneg
          (mul_nonneg heps.le (div_nonneg hs.le hr.le)) _)) _)
      hden.le
  refine ⟨K, hK, ?_⟩
  intro t ht0 htT
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < U x := by
    simpa [U] using solution_lift_pos_Icc hsol ht
  have hUcont := solution_lift_continuousOn_Icc hsol ht
  have hrInt : IntervalIntegrable (fun x => U x ^ r) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hsInt : IntervalIntegrable (fun x => U x ^ s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  calc
    A * (∫ x in (0 : ℝ)..1, U x ^ r) =
        ∫ x in (0 : ℝ)..1, A * U x ^ r := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ x in (0 : ℝ)..1, eps * U x ^ s + K :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hrInt.const_mul A) ((hsInt.const_mul eps).add intervalIntegrable_const)
        (fun x hx => by
          simpa [K] using scalar_rpow_young_absorb
            hr hrs hA heps (hUpos x hx).le)
    _ = eps * (∫ x in (0 : ℝ)..1, U x ^ s) + K := by
      rw [intervalIntegral.integral_add (hsInt.const_mul eps)
        intervalIntegrable_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      norm_num [smul_eq_mul]

/-- Strict exponent separation turns the signal-weighted gradient moment
into an arbitrarily small logistic moment plus a time-independent constant.
This is the shared analytic core of the two supercritical alternatives in
Theorem 1.3. -/
theorem weighted_gradient_moment_absorb
    {p : CM2Params} {T r s beta eps : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hbeta : 0 ≤ beta) (hr : 0 < r) (hrs : r < s)
    (hgamma : p.γ * (s / (s - r)) < s) (heps : 0 < eps) :
    ∃ K ≥ 0, ∀ t, 0 < t → t < T →
      (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ r *
          (|deriv (intervalDomainLift (v t)) x| ^ 2 /
            (1 + intervalDomainLift (v t) x) ^ (1 + beta))) ≤
        eps * (∫ x in (0 : ℝ)..1,
          intervalDomainLift (u t) x ^ s) + K := by
  let q : ℝ := s / (s - r)
  let eps1 : ℝ := eps / 2
  let d : ℝ := (eps1 * (s / r)) ^ (r / s)
  let A : ℝ := 1 / (d ^ q * q)
  have hs : 0 < s := lt_trans hr hrs
  have hsr : 0 < s - r := sub_pos.mpr hrs
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div hsr]
    linarith
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have heps1 : 0 < eps1 := div_pos heps (by norm_num)
  have hsrdiv : 0 < s / r := div_pos hs hr
  have hd : 0 < d := by
    dsimp [d]
    exact Real.rpow_pos_of_pos (mul_pos heps1 hsrdiv) _
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  obtain ⟨Mstar, hMstar, hweighted⟩ :=
    weighted_one_add_v_gradient_estimate hsol hq hbeta
  let B : ℝ := A * (Theta_beta beta) ^ q * Mstar
  have htheta : 0 ≤ Theta_beta beta :=
    (Theta_beta_pos_of_nonneg hbeta).le
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hgamma0 : 0 < p.γ * q := mul_pos p.hγ hq0
  let K : ℝ := ((B / (eps1 * (s / (p.γ * q))) ^
      ((p.γ * q) / s)) ^ (s / (s - p.γ * q))) /
        (s / (s - p.γ * q))
  have hK : 0 ≤ K := by
    dsimp [K]
    have hden1 : 0 ≤ eps1 * (s / (p.γ * q)) := by positivity
    have hden2 : 0 < s / (s - p.γ * q) :=
      div_pos hs (sub_pos.mpr (by simpa [q] using hgamma))
    exact div_nonneg
      (Real.rpow_nonneg (div_nonneg hB (Real.rpow_nonneg hden1 _)) _)
      hden2.le
  refine ⟨K, hK, ?_⟩
  intro t ht0 htT
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let W : ℝ → ℝ := fun x =>
    |deriv V x| ^ 2 / (1 + V x) ^ (1 + beta)
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < U x := by
    simpa [U] using solution_lift_pos_Icc hsol ht
  have hVnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ V x := by
    simpa [V] using lift_v_nonneg_Icc hsol ht0 htT
  have hWnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ W x := by
    intro x hx
    dsimp [W]
    exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hVnonneg x hx]) _)
  have hUcont := solution_lift_continuousOn_Icc hsol ht
  have hVcont : ContinuousOn V (Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hdVcont : ContinuousOn (deriv V) (Icc (0 : ℝ) 1) := by
    simpa [V] using deriv_v_continuousOn_Icc hsol ht0 htT
  have hWcont : ContinuousOn W (Icc (0 : ℝ) 1) := by
    dsimp [W]
    exact (hdVcont.abs.pow 2).div
      ((continuousOn_const.add hVcont).rpow_const (fun x hx => Or.inl
        (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx]))))
      (fun x hx => ne_of_gt
        (Real.rpow_pos_of_pos (by linarith [hVnonneg x hx]) _))
  have hleftInt : IntervalIntegrable (fun x => U x ^ r * W x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (hUcont.rpow_const (fun x hx => Or.inl
      (ne_of_gt (hUpos x hx)))).mul hWcont
  have hUsInt : IntervalIntegrable (fun x => U x ^ s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hWqInt : IntervalIntegrable (fun x => W x ^ q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hWcont.rpow_const (fun _ _ => Or.inr hq0.le)
  have hfirst :
      (∫ x in (0 : ℝ)..1, U x ^ r * W x) ≤
        eps1 * (∫ x in (0 : ℝ)..1, U x ^ s) +
          A * (∫ x in (0 : ℝ)..1, W x ^ q) := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1,
          eps1 * U x ^ s + A * W x ^ q :=
        intervalIntegral.integral_mono_on (by norm_num) hleftInt
          ((hUsInt.const_mul eps1).add (hWqInt.const_mul A))
          (fun x hx => by
            simpa [q, d, A, eps1] using rpow_mul_young_absorb
              hr hrs heps1 (hUpos x hx).le (hWnonneg x hx))
      _ = _ := by
        rw [intervalIntegral.integral_add (hUsInt.const_mul eps1)
          (hWqInt.const_mul A), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hWqeq : (∫ x in (0 : ℝ)..1, W x ^ q) =
      ∫ x in (0 : ℝ)..1,
        |deriv V x| ^ (2 * q) /
          (1 + V x) ^ ((1 + beta) * q) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact weighted_gradient_factor_rpow hq0.le (hVnonneg x hx)
  have hweighted_t := hweighted t ht0 htT
  rw [← hWqeq] at hweighted_t
  have hsecond0 : A * (∫ x in (0 : ℝ)..1, W x ^ q) ≤
      B * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) := by
    have hmul := mul_le_mul_of_nonneg_left hweighted_t hA
    simpa [B, U, V, mul_assoc] using hmul
  have hUgInt : IntervalIntegrable (fun x => U x ^ (p.γ * q)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hsecond1 :
      B * (∫ x in (0 : ℝ)..1, U x ^ (p.γ * q)) ≤
        eps1 * (∫ x in (0 : ℝ)..1, U x ^ s) + K := by
    calc
      _ = ∫ x in (0 : ℝ)..1, B * U x ^ (p.γ * q) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in (0 : ℝ)..1, eps1 * U x ^ s + K :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hUgInt.const_mul B) ((hUsInt.const_mul eps1).add intervalIntegrable_const)
          (fun x hx => by
            have hy := scalar_rpow_young_absorb hgamma0
              (by simpa [q] using hgamma) hB heps1 (hUpos x hx).le
            simpa [K, q] using hy)
      _ = eps1 * (∫ x in (0 : ℝ)..1, U x ^ s) + K := by
        rw [intervalIntegral.integral_add (hUsInt.const_mul eps1)
          intervalIntegrable_const, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        norm_num [smul_eq_mul]
  dsimp [U, V, W] at hfirst ⊢
  dsimp [eps1] at hfirst hsecond1
  nlinarith

set_option maxHeartbeats 800000 in
/-- Direct one-exponent damping in alternative (ii) of Theorem 1.3.  The
strict gap `alpha > 2m + gamma - 2` is used exactly once: it makes the
Proposition 2.2 source exponent strictly smaller than the logistic exponent.
-/
theorem strong_case_ii_lp_energy_damping
    {p : CM2Params} {T P : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hb : 0 < p.b) (hP : 2 < P) (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hgap : 2 * p.m + p.γ - 2 < p.α) :
    ∃ D ≥ 0, ∀ t, 0 < t → t < T →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤ D := by
  let r0 : ℝ := P + p.m - 1
  let r2 : ℝ := P + 2 * p.m - 2
  let s : ℝ := P + p.α
  let beta' : ℝ := 2 * p.β - 1
  let epsG : ℝ := (P - 1) / 2
  let Cmix : ℝ := |p.χ₀| * (P - 1)
  let Cj : ℝ := Cmix ^ 2 / (4 * epsG)
  let epsJ : ℝ := p.b / (2 * (Cj + 1))
  have hP0 : 0 < P := lt_trans zero_lt_two hP
  have hP1 : 1 < P := lt_trans one_lt_two hP
  have hr0 : 0 < r0 := by dsimp [r0]; linarith [p.hm]
  have hr2 : 0 < r2 := by dsimp [r2]; linarith [p.hm]
  have hs : 0 < s := by dsimp [s]; linarith [p.hα]
  have hrs : r2 < s := by
    dsimp [r2, s]
    linarith [p.hγ]
  have hbeta' : 0 ≤ beta' := by dsimp [beta']; linarith
  have hepsG : 0 < epsG := by dsimp [epsG]; linarith
  have hCmix : 0 ≤ Cmix := by
    dsimp [Cmix]
    exact mul_nonneg (abs_nonneg _) (by linarith)
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  have hCj1 : 0 < Cj + 1 := by linarith
  have hepsJ : 0 < epsJ := by
    dsimp [epsJ]
    positivity
  have hgammaDen : p.γ < s - r2 := by
    dsimp [s, r2]
    linarith
  have hden : 0 < s - r2 := lt_trans p.hγ hgammaDen
  have hgammaWeighted : p.γ * (s / (s - r2)) < s := by
    have hmul := mul_lt_mul_of_pos_right hgammaDen hs
    have heq : p.γ * (s / (s - r2)) =
        (p.γ * s) / (s - r2) := by ring
    rw [heq, div_lt_iff₀ hden]
    nlinarith
  obtain ⟨Kj, hKj, hJabs⟩ := weighted_gradient_moment_absorb
    hsol hbeta' hr2 hrs hgammaWeighted hepsJ
  obtain ⟨K0, hK0, hYabs⟩ := integral_rpow_absorb
    (r := P) (s := s) (A := p.a + 1) (eps := p.b / 2)
    hsol hP0 (by dsimp [s]; linarith [p.hα])
      (show 0 ≤ p.a + 1 by linarith [p.ha])
      (div_pos hb (by norm_num : (0 : ℝ) < 2))
  let D : ℝ := Cj * Kj + K0
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (mul_nonneg hCj hKj) hK0
  refine ⟨D, hD, ?_⟩
  intro t ht0 htT
  let Y : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ P
  let G : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (P - 2) *
      |deriv (intervalDomainLift (u t)) x| ^ 2
  let Z : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ s
  let J : ℝ := descentVGradient r2 (2 * p.β) u v t
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hYnonneg : 0 ≤ Y := by
    dsimp [Y]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (Real.rpow_nonneg
        (solution_lift_pos_Icc hsol ht x hx).le _) (sq_nonneg _))
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hJnonneg : 0 ≤ J := by
    dsimp [J]
    exact descentVGradient_nonneg_of_solution hsol ht0 htT
  have hsigned := signedCross_abs_le_descentMixed
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      hsol ht0 htT
  have hcross0 :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        Cmix * descentMixed r0 p.β u v t := by
    have habs : |p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t| ≤
        Cmix * descentMixed r0 p.β u v t := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < P - 1)]
      dsimp [Cmix, r0]
      exact mul_le_mul_of_nonneg_left hsigned
        (mul_nonneg (abs_nonneg _) (by linarith))
    exact (le_abs_self _).trans habs
  have hyoung := descentMixed_young
    (pExp := P) (r := r0) (C := Cmix) (eps := epsG)
      hsol ht0 htT hepsG
  have hrYoung : 2 * r0 - P = r2 := by dsimp [r0, r2]; ring
  rw [hrYoung] at hyoung
  have hcross1 :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        epsG * G + Cj * J := by
    calc
      _ ≤ Cmix * descentMixed r0 p.β u v t := hcross0
      _ ≤ epsG * G + Cj * J := by
        simpa [G, Cj, J] using hyoung
  have hJeq : J = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ r2 *
        (|deriv (intervalDomainLift (v t)) x| ^ 2 /
          (1 + intervalDomainLift (v t) x) ^ (1 + beta')) := by
    have hj := descentVGradient_eq_div
      (r := r2) (eta := 2 * p.β) hsol ht0 htT
    simpa [J, beta'] using hj
  have hJabs_t := hJabs t ht0 htT
  rw [← hJeq] at hJabs_t
  change J ≤ epsJ * Z + Kj at hJabs_t
  have hfrac : Cj / (Cj + 1) ≤ 1 :=
    (div_le_one hCj1).2 (by linarith)
  have hcoefEq : Cj * epsJ = (p.b / 2) * (Cj / (Cj + 1)) := by
    dsimp [epsJ]
    field_simp [ne_of_gt hCj1]
  have hcoef : Cj * epsJ ≤ p.b / 2 := by
    rw [hcoefEq]
    simpa using mul_le_mul_of_nonneg_left hfrac
      (div_nonneg p.hb (by norm_num : (0 : ℝ) ≤ 2))
  have hCJ : Cj * J ≤ (p.b / 2) * Z + Cj * Kj := by
    have hmul := mul_le_mul_of_nonneg_left hJabs_t hCj
    have hzmul := mul_le_mul_of_nonneg_right hcoef hZnonneg
    nlinarith
  have hcross :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        epsG * G + (p.b / 2) * Z + Cj * Kj := by
    nlinarith
  have hYabs_t := hYabs t ht0 htT
  change (p.a + 1) * Y ≤ (p.b / 2) * Z + K0 at hYabs_t
  have hYdomain : Y =
      intervalDomain.integral (fun x => (u t x) ^ P) := by
    dsimp [Y]
    exact (intervalDomain_integral_rpow_eq_lift_integral
      (q := P) (f := u t)).symm
  have hZdomain : Z =
      intervalDomain.integral (fun x => (u t x) ^ (P + p.α)) := by
    dsimp [Z, s]
    exact (intervalDomain_integral_rpow_eq_lift_integral
      (q := P + p.α) (f := u t)).symm
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      (ne_of_gt hP0) hsol ht0 htT
  rw [← hYdomain, ← hZdomain] at henergy
  have hGeq : intervalDomainLpWeightedGradientDissipation P u t = G := by
    simpa [G] using weightedDissipation_eq_lift P u t
  rw [hGeq] at henergy
  change (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
      (P - 1) * G + p.b * Z =
        p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t +
          p.a * Y at henergy
  have hEeq : intervalDomainLpEnergy P u t = Y :=
    lpEnergy_eq_lift_power_of_solution hsol ht0 htT
  rw [hEeq]
  dsimp [epsG, D] at hcross ⊢
  nlinarith

/-- Alternative (ii) supplies a genuine finite-power bound at every selected
`P > 2`; no Corollary 2.1 or package field is used. -/
theorem strong_case_ii_lp_power_bounded_before
    {p : CM2Params} {T P : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hb : 0 < p.b) (hP : 2 < P) (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hgap : 2 * p.m + p.γ - 2 < p.α) :
    LpPowerBoundedBefore intervalDomainM P T u := by
  obtain ⟨D, _hD, hdamp⟩ :=
    strong_case_ii_lp_energy_damping hsol hb hP hbeta hgap
  exact lp_power_bounded_before_of_linear_damping hu₀ hsol htrace
    (lt_trans one_lt_two hP) zero_lt_one (by simpa using hdamp)

set_option maxHeartbeats 900000 in
/-- Direct one-exponent damping in alternative (i) of Theorem 1.3.  Here the
elliptic multiplier identity is used before Young splitting; its two adverse
moments have powers `P + m - 1` and `P + m + gamma - 1`, both strictly below
`P + alpha` by the published hypothesis. -/
theorem strong_case_i_lp_energy_damping
    {p : CM2Params} {T P : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hb : 0 < p.b) (hchi : 0 ≤ p.χ₀) (hP : 2 < P)
    (hgap : p.m + p.γ - 1 < p.α) :
    ∃ D ≥ 0, ∀ t, 0 < t → t < T →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤ D := by
  let r0 : ℝ := P + p.m - 1
  let rb : ℝ := r0 + p.γ
  let s : ℝ := P + p.α
  let k : ℝ := p.χ₀ * (P - 1) / r0
  let Cj : ℝ := k * p.β
  let Cb : ℝ := k * p.ν
  let epsJ : ℝ := p.b / (4 * (Cj + 1))
  have hP0 : 0 < P := lt_trans zero_lt_two hP
  have hP1 : 1 < P := lt_trans one_lt_two hP
  have hr0 : 0 < r0 := by dsimp [r0]; linarith [p.hm]
  have hrb : 0 < rb := by dsimp [rb]; linarith [p.hγ]
  have hs : 0 < s := by dsimp [s]; linarith [p.hα]
  have hr0s : r0 < s := by
    dsimp [r0, s]
    linarith [p.hγ]
  have hrbs : rb < s := by dsimp [rb, r0, s]; linarith
  have hk : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (mul_nonneg hchi (by linarith)) hr0.le
  have hCj : 0 ≤ Cj := by dsimp [Cj]; exact mul_nonneg hk p.hβ
  have hCb : 0 ≤ Cb := by dsimp [Cb]; exact mul_nonneg hk p.hν.le
  have hCj1 : 0 < Cj + 1 := by linarith
  have hepsJ : 0 < epsJ := by dsimp [epsJ]; positivity
  have hgammaDen : p.γ < s - r0 := by
    dsimp [s, r0]
    linarith
  have hden : 0 < s - r0 := lt_trans p.hγ hgammaDen
  have hgammaWeighted : p.γ * (s / (s - r0)) < s := by
    have hmul := mul_lt_mul_of_pos_right hgammaDen hs
    have heq : p.γ * (s / (s - r0)) =
        (p.γ * s) / (s - r0) := by ring
    rw [heq, div_lt_iff₀ hden]
    nlinarith
  obtain ⟨Kj, hKj, hJabs⟩ := weighted_gradient_moment_absorb
    hsol p.hβ hr0 hr0s hgammaWeighted hepsJ
  obtain ⟨Kb, hKb, hBabs⟩ := integral_rpow_absorb
    (r := rb) (s := s) (A := Cb) (eps := p.b / 4)
    hsol hrb hrbs hCb (div_pos hb (by norm_num))
  obtain ⟨K0, hK0, hYabs⟩ := integral_rpow_absorb
    (r := P) (s := s) (A := p.a + 1) (eps := p.b / 2)
    hsol hP0 (by dsimp [s]; linarith [p.hα])
      (show 0 ≤ p.a + 1 by linarith [p.ha]) (div_pos hb (by norm_num))
  let D : ℝ := Cj * Kj + Kb + K0
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro t ht0 htT
  let Y : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ P
  let G : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (P - 2) *
      |deriv (intervalDomainLift (u t)) x| ^ 2
  let Z : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ s
  let S : ℝ := descentSignedMixed r0 p.β u v t
  let J : ℝ := descentVGradient r0 (p.β + 1) u v t
  let Aell : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ r0 * intervalDomainLift (v t) x *
      (1 + intervalDomainLift (v t) x) ^ (-p.β)
  let Bell : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ rb *
      (1 + intervalDomainLift (v t) x) ^ (-p.β)
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hYnonneg : 0 ≤ Y := by
    dsimp [Y]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hGnonneg : 0 ≤ G := by
    dsimp [G]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (Real.rpow_nonneg
        (solution_lift_pos_Icc hsol ht x hx).le _) (sq_nonneg _))
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hJnonneg : 0 ≤ J := by
    dsimp [J]
    exact descentVGradient_nonneg_of_solution hsol ht0 htT
  have hAell : 0 ≤ Aell := by
    dsimp [Aell]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (mul_nonneg
        (Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
        (lift_v_nonneg_Icc hsol ht0 htT x hx))
        (Real.rpow_nonneg (by
          linarith [lift_v_nonneg_Icc hsol ht0 htT x hx]) _))
  have hBell : 0 ≤ Bell := by
    dsimp [Bell]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg
        (Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
        (Real.rpow_nonneg (by
          linarith [lift_v_nonneg_Icc hsol ht0 htT x hx]) _))
  have hid := elliptic_multiplier_ibp_identity_eta
    (p := p) (T := T) (t := t) (r := r0) (eta := p.β)
      (u := u) (v := v) hsol ht0 htT
  change p.β * J = r0 * S + p.μ * Aell - p.ν * Bell at hid
  have hraw : r0 * S ≤ p.β * J + p.ν * Bell := by
    have hmuA : 0 ≤ p.μ * Aell := mul_nonneg p.hμ.le hAell
    nlinarith
  have hkcancel : k * r0 = p.χ₀ * (P - 1) := by
    dsimp [k]
    field_simp [ne_of_gt hr0]
  have hcross0 :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        Cj * J + Cb * Bell := by
    have hSeq := lpSignedCrossIntegralM_eq_descentSignedMixed
      (P := P) hsol ht0 htT
    have hmul := mul_le_mul_of_nonneg_left hraw hk
    rw [hSeq]
    dsimp [S, Cj, Cb]
    rw [← hkcancel]
    nlinarith
  have hJeq : J = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ r0 *
        (|deriv (intervalDomainLift (v t)) x| ^ 2 /
          (1 + intervalDomainLift (v t) x) ^ (1 + p.β)) := by
    simpa [J, add_comm] using descentVGradient_eq_div
      (r := r0) (eta := p.β + 1) hsol ht0 htT
  have hJabs_t := hJabs t ht0 htT
  rw [← hJeq] at hJabs_t
  change J ≤ epsJ * Z + Kj at hJabs_t
  have hfrac : Cj / (Cj + 1) ≤ 1 :=
    (div_le_one hCj1).2 (by linarith)
  have hcoefEq : Cj * epsJ =
      (p.b / 4) * (Cj / (Cj + 1)) := by
    dsimp [epsJ]
    field_simp [ne_of_gt hCj1]
  have hcoef : Cj * epsJ ≤ p.b / 4 := by
    rw [hcoefEq]
    simpa using mul_le_mul_of_nonneg_left hfrac
      (div_nonneg p.hb (by norm_num : (0 : ℝ) ≤ 4))
  have hCJ : Cj * J ≤ (p.b / 4) * Z + Cj * Kj := by
    have hmul := mul_le_mul_of_nonneg_left hJabs_t hCj
    have hzmul := mul_le_mul_of_nonneg_right hcoef hZnonneg
    nlinarith
  have hBdrop : Bell ≤ ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ rb := by
    dsimp [Bell]
    exact weighted_u_power_le_unweighted hsol ht0 htT p.hβ
  have hBabs_t := hBabs t ht0 htT
  change Cb * (∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ rb) ≤ (p.b / 4) * Z + Kb at hBabs_t
  have hCB : Cb * Bell ≤ (p.b / 4) * Z + Kb :=
    (mul_le_mul_of_nonneg_left hBdrop hCb).trans hBabs_t
  have hcross :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        (p.b / 2) * Z + Cj * Kj + Kb := by
    nlinarith
  have hYabs_t := hYabs t ht0 htT
  change (p.a + 1) * Y ≤ (p.b / 2) * Z + K0 at hYabs_t
  have hYdomain : Y =
      intervalDomain.integral (fun x => (u t x) ^ P) := by
    dsimp [Y]
    exact (intervalDomain_integral_rpow_eq_lift_integral
      (q := P) (f := u t)).symm
  have hZdomain : Z =
      intervalDomain.integral (fun x => (u t x) ^ (P + p.α)) := by
    dsimp [Z, s]
    exact (intervalDomain_integral_rpow_eq_lift_integral
      (q := P + p.α) (f := u t)).symm
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      (ne_of_gt hP0) hsol ht0 htT
  rw [← hYdomain, ← hZdomain] at henergy
  have hGeq : intervalDomainLpWeightedGradientDissipation P u t = G := by
    simpa [G] using weightedDissipation_eq_lift P u t
  rw [hGeq] at henergy
  change (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
      (P - 1) * G + p.b * Z =
        p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t +
          p.a * Y at henergy
  have hEeq : intervalDomainLpEnergy P u t = Y :=
    lpEnergy_eq_lift_power_of_solution hsol ht0 htT
  rw [hEeq]
  dsimp [D] at hcross ⊢
  nlinarith

/-- Alternative (i) supplies a genuine finite-power bound at every selected
`P > 2`. -/
theorem strong_case_i_lp_power_bounded_before
    {p : CM2Params} {T P : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hb : 0 < p.b) (hchi : 0 ≤ p.χ₀) (hP : 2 < P)
    (hgap : p.m + p.γ - 1 < p.α) :
    LpPowerBoundedBefore intervalDomainM P T u := by
  obtain ⟨D, _hD, hdamp⟩ :=
    strong_case_i_lp_energy_damping hsol hb hchi hP hgap
  exact lp_power_bounded_before_of_linear_damping hu₀ hsol htrace
    (lt_trans one_lt_two hP) zero_lt_one (by simpa using hdamp)

#print axioms rpow_mul_young_absorb
#print axioms weighted_gradient_factor_rpow
#print axioms descentVGradient_eq_div
#print axioms lpSignedCrossIntegralM_eq_descentSignedMixed
#print axioms weighted_u_power_le_unweighted
#print axioms integral_rpow_absorb
#print axioms weighted_gradient_moment_absorb
#print axioms strong_case_ii_lp_energy_damping
#print axioms strong_case_ii_lp_power_bounded_before
#print axioms strong_case_i_lp_energy_damping
#print axioms strong_case_i_lp_power_bounded_before

end ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer
