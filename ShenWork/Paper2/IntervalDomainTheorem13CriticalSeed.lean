import ShenWork.Paper2.IntervalDomainPaperWeightedGradientMstar
import ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer

/-!
# Paper 2, Theorem 1.3: critical finite-power seeds

This file implements the two borderline estimates (5.3) and (5.7) on the
paper-faithful general-`m` interval model.  The constants use the literal
`M*` from (1.18), rather than an existential weighted-gradient constant.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13CriticalSeed

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants
open ShenWork.Paper2.IntervalDomainPaperWeightedGradientMstar
open ShenWork.Paper2.IntervalDomainTheorem13StrongLogisticProducer

/-- Hölder on the unit interval, stated for nonnegative continuous functions
so every `MemLp` premise is discharged internally. -/
theorem unitInterval_integral_mul_le_holder
    {F G : ℝ → ℝ} {pH qH : ℝ}
    (hconj : pH.HolderConjugate qH)
    (hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1))
    (hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1))
    (hF0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ F x)
    (hG0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) :
    (∫ x in (0 : ℝ)..1, F x * G x) ≤
      (∫ x in (0 : ℝ)..1, F x ^ pH) ^ (1 / pH) *
        (∫ x in (0 : ℝ)..1, G x ^ qH) ^ (1 / qH) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hFmeas : AEStronglyMeasurable F μ := by
    dsimp [μ]
    exact hFcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hGmeas : AEStronglyMeasurable G μ := by
    dsimp [μ]
    exact hGcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  obtain ⟨CF, hCF⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hFcont
  obtain ⟨CG, hCG⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hGcont
  have hFbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ CF := by
    dsimp [μ]
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun x hx => hCF x ⟨le_of_lt hx.1, hx.2⟩
  have hGbound : ∀ᵐ x ∂μ, ‖G x‖ ≤ CG := by
    dsimp [μ]
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun x hx => hCG x ⟨le_of_lt hx.1, hx.2⟩
  have hFmem : MemLp F (ENNReal.ofReal pH) μ :=
    MemLp.of_bound hFmeas CF hFbound
  have hGmem : MemLp G (ENNReal.ofReal qH) μ :=
    MemLp.of_bound hGmeas CG hGbound
  have hFae : 0 ≤ᵐ[μ] F := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    exact hF0 x ⟨le_of_lt hx.1, hx.2⟩
  have hGae : 0 ≤ᵐ[μ] G := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    exact hG0 x ⟨le_of_lt hx.1, hx.2⟩
  have hh := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) hconj hFae hGae hFmem hGmem
  have hleft : (∫ x in (0 : ℝ)..1, F x * G x) = ∫ x, F x * G x ∂μ := by
    simp [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hFp : (∫ x in (0 : ℝ)..1, F x ^ pH) = ∫ x, F x ^ pH ∂μ := by
    simp [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hGq : (∫ x in (0 : ℝ)..1, G x ^ qH) = ∫ x, G x ^ qH ∂μ := by
    simp [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rwa [hleft, hFp, hGq]

/-- Critical Hölder step used in both (5.2) and (5.7).  When `s = r+gamma`,
the weighted gradient moment is exactly linear in the `s`-moment. -/
theorem critical_weighted_gradient_moment_le_paperMstar
    {p : CM2Params} {T t r s beta : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hbeta : 0 ≤ beta) (hr : 0 < r) (hrs : s = r + p.γ) :
    let q : ℝ := s / p.γ
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ r *
          (|deriv (intervalDomainLift (v t)) x| ^ 2 /
            (1 + intervalDomainLift (v t) x) ^ (1 + beta))) ≤
      Theta_beta beta * intervalPaperMstar p q ^ (1 / q) *
        (∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s) := by
  dsimp only
  let q : ℝ := s / p.γ
  let pH : ℝ := s / r
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let W : ℝ → ℝ := fun x =>
    |deriv V x| ^ 2 / (1 + V x) ^ (1 + beta)
  have hs : 0 < s := by rw [hrs]; exact add_pos hr p.hγ
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div p.hγ]
    rw [hrs]
    linarith
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hpH : 1 < pH := by
    dsimp [pH]
    rw [one_lt_div hr]
    rw [hrs]
    linarith [p.hγ]
  have hpH0 : 0 < pH := zero_lt_one.trans hpH
  have hconj : pH.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hpH, ?_⟩
    dsimp [pH, q]
    rw [hrs]
    field_simp [hr.ne', p.hγ.ne', (add_pos hr p.hγ).ne']
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    simpa [U] using solution_lift_pos_Icc hsol ht
  have hV0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    simpa [V] using lift_v_nonneg_Icc hsol ht0 htT
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using solution_lift_continuousOn_Icc hsol ht
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1.continuousOn
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using deriv_v_continuousOn_Icc hsol ht0 htT
  have hW0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ W x := by
    intro x hx
    dsimp [W]
    exact div_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by linarith [hV0 x hx]) _)
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) := by
    dsimp [W]
    exact (hdVcont.abs.pow 2).div
      ((continuousOn_const.add hVcont).rpow_const (fun x hx => Or.inl
        (ne_of_gt (show 0 < 1 + V x by linarith [hV0 x hx]))))
      (fun x hx => ne_of_gt
        (Real.rpow_pos_of_pos (by linarith [hV0 x hx]) _))
  have hFcont : ContinuousOn (fun x => U x ^ r) (Set.Icc (0 : ℝ) 1) :=
    hUcont.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hholder := unitInterval_integral_mul_le_holder hconj hFcont hWcont
    (fun x hx => Real.rpow_nonneg (hUpos x hx).le _)
    hW0
  have hUpow : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (U x ^ r) ^ pH = U x ^ s := by
    intro x hx
    rw [← Real.rpow_mul (hUpos x hx).le]
    dsimp [pH]
    have he : r * (s / r) = s := by field_simp [hr.ne']
    rw [he]
  have hWpow : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      W x ^ q = |deriv V x| ^ (2 * q) /
        (1 + V x) ^ ((1 + beta) * q) := by
    intro x hx
    exact weighted_gradient_factor_rpow hq0.le (hV0 x hx)
  have hholder' :
      (∫ x in (0 : ℝ)..1, U x ^ r * W x) ≤
        (∫ x in (0 : ℝ)..1, U x ^ s) ^ (1 / pH) *
          (∫ x in (0 : ℝ)..1,
            |deriv V x| ^ (2 * q) /
              (1 + V x) ^ ((1 + beta) * q)) ^ (1 / q) := by
    have hFint : (∫ x in (0 : ℝ)..1, (U x ^ r) ^ pH) =
        ∫ x in (0 : ℝ)..1, U x ^ s := by
      apply intervalIntegral.integral_congr
      intro x hx
      simpa [Set.uIcc_of_le zero_le_one] using
        hUpow x (by simpa [Set.uIcc_of_le zero_le_one] using hx)
    have hWint : (∫ x in (0 : ℝ)..1, W x ^ q) =
        ∫ x in (0 : ℝ)..1,
          |deriv V x| ^ (2 * q) /
            (1 + V x) ^ ((1 + beta) * q) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hWpow x (by simpa [Set.uIcc_of_le zero_le_one] using hx)
    rwa [hFint, hWint] at hholder
  have hweighted :=
    (intervalDomainM_weightedGradientEstimate_paperMstar
      (p := p) (T := T) (u := u) (v := v) hsol hq hbeta) t ht0 htT
  have hweightedLift :
      (∫ x in (0 : ℝ)..1,
          |deriv V x| ^ (2 * q) /
            (1 + V x) ^ ((1 + beta) * q)) ≤
        Theta_beta beta ^ q * intervalPaperMstar p q *
          (∫ x in (0 : ℝ)..1, U x ^ s) := by
    rw [← intervalDomainM_weighted_one_add_v_integral_lift,
      ← intervalDomainM_power_integral_lift]
    have he : p.γ * q = s := by
      dsimp [q]
      field_simp [p.hγ.ne']
    simpa [V, U, he] using hweighted.2
  let Z : ℝ := ∫ x in (0 : ℝ)..1, U x ^ s
  let A : ℝ := ∫ x in (0 : ℝ)..1,
    |deriv V x| ^ (2 * q) / (1 + V x) ^ ((1 + beta) * q)
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (hUpos x hx).le _)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      div_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.rpow_nonneg (by linarith [hV0 x hx]) _))
  have htheta : 0 < Theta_beta beta := Theta_beta_pos_of_nonneg hbeta
  have hM : 0 < intervalPaperMstar p q := intervalPaperMstar_pos p hq
  have hroot := Real.rpow_le_rpow hA0 (by simpa [A, Z] using hweightedLift)
    (one_div_nonneg.mpr hq0.le)
  have hfactor :
      (Theta_beta beta ^ q * intervalPaperMstar p q * Z) ^ (1 / q) =
        Theta_beta beta * intervalPaperMstar p q ^ (1 / q) * Z ^ (1 / q) := by
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg htheta.le _)
          hM.le) hZ0,
      Real.mul_rpow (Real.rpow_nonneg htheta.le _) hM.le]
    have hthetaCancel : (Theta_beta beta ^ q) ^ (1 / q) = Theta_beta beta := by
      rw [← Real.rpow_mul htheta.le]
      have he : q * (1 / q) = 1 := by field_simp [hq0.ne']
      rw [he, Real.rpow_one]
    rw [hthetaCancel]
  have hexp : 1 / pH + 1 / q = 1 := by
    dsimp [pH, q]
    rw [hrs]
    field_simp [hr.ne', p.hγ.ne', (add_pos hr p.hγ).ne']
  have hZfactor : Z ^ (1 / pH) * Z ^ (1 / q) = Z := by
    rw [← Real.rpow_add_of_nonneg hZ0
      (one_div_nonneg.mpr hpH0.le) (one_div_nonneg.mpr hq0.le),
      hexp, Real.rpow_one]
  calc
    (∫ x in (0 : ℝ)..1, U x ^ r * W x) ≤
        Z ^ (1 / pH) * A ^ (1 / q) := by simpa [Z, A] using hholder'
    _ ≤ Z ^ (1 / pH) *
        (Theta_beta beta ^ q * intervalPaperMstar p q * Z) ^ (1 / q) :=
      mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hZ0 _)
    _ = Theta_beta beta * intervalPaperMstar p q ^ (1 / q) * Z := by
      rw [hfactor]
      rw [show Z ^ (1 / pH) *
          (Theta_beta beta * intervalPaperMstar p q ^ (1 / q) * Z ^ (1 / q)) =
        (Theta_beta beta * intervalPaperMstar p q ^ (1 / q)) *
          (Z ^ (1 / pH) * Z ^ (1 / q)) by ring,
        hZfactor]
    _ = _ := by rfl

/-- The finite-exponent coefficient `F` in paper equation (5.3). -/
def criticalCaseIIICoefficient (p : CM2Params) (P : ℝ) : ℝ :=
  p.χ₀ * (P - 1) / (P - 1 + p.m) *
    (p.ν + Psi_beta p.β * theorem13CriticalProfile p P)

/-- The finite-exponent coefficient `F tilde` in paper equation (5.7). -/
def criticalCaseIVCoefficient (p : CM2Params) (P : ℝ) : ℝ :=
  (P - 1) * p.χ₀ ^ 2 / 4 *
    Theta_beta (2 * p.β - 1) * theorem13CriticalProfile p P

set_option maxHeartbeats 900000 in
/-- Fixed-exponent damping for the critical alternative (iii), assuming the
literal paper coefficient `F(P)` is below `b`. -/
theorem critical_case_iii_lp_energy_damping
    {p : CM2Params} {T P : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1) (hP : 1 < P)
    (hcoef : criticalCaseIIICoefficient p P < p.b) :
    ∃ D ≥ 0, ∀ t, 0 < t → t < T →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤ D := by
  let r : ℝ := P + p.m - 1
  let s : ℝ := P + p.α
  let q : ℝ := s / p.γ
  let k : ℝ := p.χ₀ * (P - 1) / r
  let F : ℝ := criticalCaseIIICoefficient p P
  let c : ℝ := p.b - F
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hr : 0 < r := by dsimp [r]; linarith [p.hm]
  have hs : 0 < s := by dsimp [s]; linarith [p.hα]
  have hrs : s = r + p.γ := by dsimp [s, r]; linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div p.hγ]
    rw [hrs]
    linarith [hr]
  have hk : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (mul_nonneg hchi.le (sub_pos.mpr hP).le) hr.le
  have hc : 0 < c := by dsimp [c, F]; exact sub_pos.mpr hcoef
  let K0 : ℝ := integralRpowAbsorbConstant P s (p.a + 1) c
  obtain ⟨hK0, hYabs⟩ := integral_rpow_absorb
    (r := P) (s := s) (A := p.a + 1) (eps := c)
    hsol hP0 (by dsimp [s]; linarith [p.hα])
      (by linarith [p.ha] : 0 ≤ p.a + 1) hc
  refine ⟨K0, hK0, ?_⟩
  intro t ht0 htT
  let Y : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ P
  let G : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (P - 2) *
      |deriv (intervalDomainLift (u t)) x| ^ 2
  let Z : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s
  let S : ℝ := descentSignedMixed r p.β u v t
  let J : ℝ := descentVGradient r (p.β + 1) u v t
  let Aell : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ r * intervalDomainLift (v t) x *
      (1 + intervalDomainLift (v t) x) ^ (-p.β)
  let Bell : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (r + p.γ) *
      (1 + intervalDomainLift (v t) x) ^ (-p.β)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
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
  have hcross :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤ F * Z := by
    calc
      _ ≤ k * (p.β * J + p.ν * Bell) := hcross0
      _ ≤ k * ((p.ν + Psi_beta p.β * theorem13CriticalProfile p P) * Z) :=
        mul_le_mul_of_nonneg_left hinner hk
      _ = F * Z := by
        dsimp [k, F, criticalCaseIIICoefficient, r]
        ring
  have hYdomain : Y = intervalDomain.integral (fun x => (u t x) ^ P) := by
    dsimp [Y]
    exact (intervalDomain_integral_power_lift
      (a := P) (f := u t)).symm
  have hZdomain : Z = intervalDomain.integral
      (fun x => (u t x) ^ (P + p.α)) := by
    dsimp [Z, s]
    exact (intervalDomain_integral_power_lift
      (a := P + p.α) (f := u t)).symm
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      hP0.ne' hsol ht0 htT
  rw [← hYdomain, ← hZdomain] at henergy
  have hGeq : intervalDomainLpWeightedGradientDissipation P u t = G := by
    simpa [G] using weightedDissipation_eq_lift P u t
  rw [hGeq] at henergy
  change (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
      (P - 1) * G + p.b * Z =
        p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t + p.a * Y at henergy
  have hYabs_t := hYabs t ht0 htT
  change (p.a + 1) * Y ≤ c * Z + K0 at hYabs_t
  have hEeq : intervalDomainLpEnergy P u t = Y :=
    lpEnergy_eq_lift_power_of_solution hsol ht0 htT
  rw [hEeq]
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (Real.rpow_nonneg
        (solution_lift_pos_Icc hsol ht x hx).le _) (sq_nonneg _))
  have hP1 : 0 ≤ P - 1 := (sub_pos.mpr hP).le
  dsimp [c] at hYabs_t
  nlinarith [mul_nonneg hP1 hG0]

theorem critical_case_iii_lp_power_bounded_before
    {p : CM2Params} {T P : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀) (hbeta : 0 ≤ p.β)
    (hcrit : p.α = p.m + p.γ - 1) (hP : 1 < P)
    (hcoef : criticalCaseIIICoefficient p P < p.b) :
    LpPowerBoundedBefore intervalDomainM P T u := by
  obtain ⟨D, _hD, hdamp⟩ := critical_case_iii_lp_energy_damping
    hsol hchi hbeta hcrit hP hcoef
  exact lp_power_bounded_before_of_linear_damping hu₀ hsol htrace
    hP zero_lt_one (by simpa using hdamp)

set_option maxHeartbeats 900000 in
/-- Fixed-exponent damping for the critical alternative (iv), assuming the
literal paper coefficient `F tilde(P)` is below `b`. -/
theorem critical_case_iv_lp_energy_damping
    {p : CM2Params} {T P : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2) (hP : 1 < P)
    (hvalid : 2 - 2 * p.m < P)
    (hcoef : criticalCaseIVCoefficient p P < p.b) :
    ∃ D ≥ 0, ∀ t, 0 < t → t < T →
      (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t ≤ D := by
  let r0 : ℝ := P + p.m - 1
  let r2 : ℝ := P + 2 * p.m - 2
  let s : ℝ := P + p.α
  let q : ℝ := s / p.γ
  let beta' : ℝ := 2 * p.β - 1
  let Cmix : ℝ := |p.χ₀| * (P - 1)
  let Cj : ℝ := Cmix ^ 2 / (4 * (P - 1))
  let F : ℝ := criticalCaseIVCoefficient p P
  let c : ℝ := p.b - F
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hP1 : 0 < P - 1 := sub_pos.mpr hP
  have hr0 : 0 < r0 := by dsimp [r0]; linarith [p.hm]
  have hr2 : 0 < r2 := by
    dsimp [r2]
    linarith
  have hs : 0 < s := by dsimp [s]; exact add_pos hP0 p.hα
  have hrs : s = r2 + p.γ := by dsimp [s, r2]; linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div p.hγ, hrs]
    linarith [hr2]
  have hbeta' : 0 ≤ beta' := by dsimp [beta']; linarith
  have hCmix : 0 ≤ Cmix := by dsimp [Cmix]; positivity
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  have hCjEq : Cj = (P - 1) * p.χ₀ ^ 2 / 4 := by
    dsimp [Cj, Cmix]
    rw [mul_pow, sq_abs]
    field_simp [hP1.ne']
  have hc : 0 < c := by dsimp [c, F]; exact sub_pos.mpr hcoef
  let K0 : ℝ := integralRpowAbsorbConstant P s (p.a + 1) c
  obtain ⟨hK0, hYabs⟩ := integral_rpow_absorb
    (r := P) (s := s) (A := p.a + 1) (eps := c)
    hsol hP0 (by dsimp [s]; linarith [p.hα])
      (by linarith [p.ha] : 0 ≤ p.a + 1) hc
  refine ⟨K0, hK0, ?_⟩
  intro t ht0 htT
  let Y : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ P
  let G : ℝ := ∫ x in (0 : ℝ)..1,
    intervalDomainLift (u t) x ^ (P - 2) *
      |deriv (intervalDomainLift (u t)) x| ^ 2
  let Z : ℝ := ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s
  let J : ℝ := descentVGradient r2 (2 * p.β) u v t
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      mul_nonneg (Real.rpow_nonneg
        (solution_lift_pos_Icc hsol ht x hx).le _) (sq_nonneg _))
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx =>
      Real.rpow_nonneg (solution_lift_pos_Icc hsol ht x hx).le _)
  have hsigned := signedCross_abs_le_descentMixed
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      hsol ht0 htT
  have hcross0 :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        Cmix * descentMixed r0 p.β u v t := by
    have habs : |p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t| ≤
        Cmix * descentMixed r0 p.β u v t := by
      rw [abs_mul, abs_mul, abs_of_pos hP1]
      dsimp [Cmix, r0]
      exact mul_le_mul_of_nonneg_left hsigned
        (mul_nonneg (abs_nonneg _) hP1.le)
    exact (le_abs_self _).trans habs
  have hyoung := descentMixed_young
    (pExp := P) (r := r0) (C := Cmix) (eps := P - 1)
      hsol ht0 htT hP1
  have hrYoung : 2 * r0 - P = r2 := by dsimp [r0, r2]; ring
  rw [hrYoung] at hyoung
  have hcross1 :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        (P - 1) * G + Cj * J := by
    calc
      _ ≤ Cmix * descentMixed r0 p.β u v t := hcross0
      _ ≤ (P - 1) * G + Cj * J := by
        simpa [G, Cj, J] using hyoung
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
  have hCJ : Cj * J ≤ F * Z := by
    have hmul := mul_le_mul_of_nonneg_left hJ hCj
    dsimp [F, criticalCaseIVCoefficient]
    rw [hCjEq] at hmul
    rw [hCjEq]
    simpa [beta', Z, mul_assoc] using hmul
  have hcross :
      p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t ≤
        (P - 1) * G + F * Z := by
    nlinarith
  have hYdomain : Y = intervalDomain.integral (fun x => (u t x) ^ P) := by
    dsimp [Y]
    exact (intervalDomain_integral_power_lift (a := P) (f := u t)).symm
  have hZdomain : Z = intervalDomain.integral
      (fun x => (u t x) ^ (P + p.α)) := by
    dsimp [Z, s]
    exact (intervalDomain_integral_power_lift
      (a := P + p.α) (f := u t)).symm
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      hP0.ne' hsol ht0 htT
  rw [← hYdomain, ← hZdomain] at henergy
  have hGeq : intervalDomainLpWeightedGradientDissipation P u t = G := by
    simpa [G] using weightedDissipation_eq_lift P u t
  rw [hGeq] at henergy
  change (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
      (P - 1) * G + p.b * Z =
        p.χ₀ * (P - 1) * lpSignedCrossIntegralM p P u v t + p.a * Y at henergy
  have hYabs_t := hYabs t ht0 htT
  change (p.a + 1) * Y ≤ c * Z + K0 at hYabs_t
  have hEeq : intervalDomainLpEnergy P u t = Y :=
    lpEnergy_eq_lift_power_of_solution hsol ht0 htT
  rw [hEeq]
  dsimp [c] at hYabs_t
  nlinarith

theorem critical_case_iv_lp_power_bounded_before
    {p : CM2Params} {T P : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbeta : (1 / 2 : ℝ) ≤ p.β)
    (hcrit : p.α = 2 * p.m + p.γ - 2) (hP : 1 < P)
    (hvalid : 2 - 2 * p.m < P)
    (hcoef : criticalCaseIVCoefficient p P < p.b) :
    LpPowerBoundedBefore intervalDomainM P T u := by
  obtain ⟨D, _hD, hdamp⟩ := critical_case_iv_lp_energy_damping
    hsol hbeta hcrit hP hvalid hcoef
  exact lp_power_bounded_before_of_linear_damping hu₀ hsol htrace
    hP zero_lt_one (by simpa using hdamp)

#print axioms unitInterval_integral_mul_le_holder
#print axioms critical_weighted_gradient_moment_le_paperMstar
#print axioms critical_case_iii_lp_energy_damping
#print axioms critical_case_iii_lp_power_bounded_before
#print axioms critical_case_iv_lp_energy_damping
#print axioms critical_case_iv_lp_power_bounded_before

end ShenWork.Paper2.IntervalDomainTheorem13CriticalSeed
