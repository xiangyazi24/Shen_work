import ShenWork.Paper3.IntervalDomainMinimalEventualLp
import ShenWork.Paper2.IntervalDomainMCriticalGlobalLpBootstrap
import ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap
import ShenWork.Paper3.EventualLinearDamping

/-!
# M-native orbit-independent eventual `L^p` bound for `1 ≤ m < 2`

This is the single genuinely-new analytic step of Paper 3 Theorem 2.5 for the
general-`m` minimal-equilibrium equation in the subcritical flux range
`1 ≤ m < 2`.  The `m = 1` argument closes through the exponent coincidence
`P + 2m - 2 = P`; for `1 ≤ m < 2` the excess `2m - 2 < 2` is absorbed by the
seed-relative one-dimensional Agmon interpolation with the **physical mass**
(`L^1`) as the seed exponent `p₀ = 1`.

The chemotaxis cross term produces, after one Young split, a weighted
`v`-gradient at the shifted power `P + 2m - 2`.  Because `β ≥ 1` the elliptic
log-gradient bound turns that weighted gradient into a bare `u`-moment
`∫ u^{P+2m-2}` with the harmless constant `μ`, and that moment is absorbed into
the diffusion dissipation by the seed-relative Agmon lemma
`intervalDomainM_agmon_absorbed_of_lp_bound` (`ρ = 2m-2 < 2·1`).  No smallness
of `χ₀` is required for the a-priori bound.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap

namespace ShenWork.Paper3

noncomputable section

/-- Crude weighted-`v`-gradient bound.  For `β ≥ 1` the signal weight
`|v'|² (1+v)^{-2β}` is pointwise below `μ`, so the weighted gradient at any
power `s` is dominated by `μ` times the bare `u`-moment `∫ u^s`. -/
theorem descentVGradient_le_mu_moment
    {p : CM2Params} {T t s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (hbeta : 1 ≤ p.β) :
    descentVGradient s (2 * p.β) u v t ≤
      p.μ * ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
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
  -- pointwise: the weight is ≤ μ
  have hweight : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β)) ≤ p.μ := by
    intro x hx
    have hB : 1 ≤ 1 + V x := by linarith [hVnonneg x hx]
    have hBpos : 0 < 1 + V x := lt_of_lt_of_le zero_lt_one hB
    have hsqrt : (Real.sqrt p.μ) ^ 2 = p.μ := Real.sq_sqrt p.hμ.le
    have hsq : |deriv V x| ^ 2 ≤ p.μ * V x ^ 2 := by
      have hnonneg : 0 ≤ |deriv V x| := abs_nonneg _
      have hraw : |deriv V x| ^ 2 ≤ (Real.sqrt p.μ * V x) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hnonneg (hlog x hx)
      calc
        |deriv V x| ^ 2 ≤ (Real.sqrt p.μ * V x) ^ 2 := hraw
        _ = p.μ * V x ^ 2 := by rw [mul_pow, hsqrt]
    have hVleB : V x ≤ 1 + V x := by linarith
    have hVsq : V x ^ 2 ≤ (1 + V x) ^ (2 : ℝ) := by
      simpa only [Real.rpow_two, pow_two] using
        mul_self_le_mul_self (hVnonneg x hx) hVleB
    have hpow : (1 + V x) ^ (2 : ℝ) ≤ (1 + V x) ^ (2 * p.β) :=
      Real.rpow_le_rpow_of_exponent_le hB (by nlinarith)
    have hratio : V x ^ 2 * (1 + V x) ^ (-(2 * p.β)) ≤ 1 := by
      rw [Real.rpow_neg hBpos.le, ← div_eq_mul_inv]
      exact (div_le_one (Real.rpow_pos_of_pos hBpos _)).2 (hVsq.trans hpow)
    have hwnn : 0 ≤ (1 + V x) ^ (-(2 * p.β)) := Real.rpow_nonneg hBpos.le _
    have hmul := mul_le_mul_of_nonneg_right hsq hwnn
    calc
      |deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β))
          ≤ (p.μ * V x ^ 2) * (1 + V x) ^ (-(2 * p.β)) := hmul
      _ = p.μ * (V x ^ 2 * (1 + V x) ^ (-(2 * p.β))) := by ring
      _ ≤ p.μ * 1 := mul_le_mul_of_nonneg_left hratio p.hμ.le
      _ = p.μ := mul_one _
  have hLint : IntervalIntegrable (fun x =>
      U x ^ s * |deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β))) volume 0 1 := by
    simpa [U, V] using
      descentVGradient_intervalIntegrable (r := s) (eta := 2 * p.β) hsol ht0 htT
  have hRint : IntervalIntegrable (fun x => p.μ * U x ^ s) volume 0 1 := by
    have hcont : ContinuousOn (fun x => U x ^ s) (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact (solution_lift_continuousOn_Icc hsol ht).rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    exact (hcont.intervalIntegrable).const_mul p.μ
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      U x ^ s * |deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β)) ≤ p.μ * U x ^ s := by
    intro x hx
    have hUs : 0 ≤ U x ^ s := Real.rpow_nonneg (hUpos x hx).le _
    calc
      U x ^ s * |deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β))
          = U x ^ s * (|deriv V x| ^ 2 * (1 + V x) ^ (-(2 * p.β))) := by ring
      _ ≤ U x ^ s * p.μ := mul_le_mul_of_nonneg_left (hweight x hx) hUs
      _ = p.μ * U x ^ s := by ring
  unfold descentVGradient
  calc
    (∫ x in (0 : ℝ)..1,
        intervalDomainLift (u t) x ^ s * |deriv (intervalDomainLift (v t)) x| ^ 2 *
          (1 + intervalDomainLift (v t) x) ^ (-(2 * p.β)))
        ≤ ∫ x in (0 : ℝ)..1, p.μ * U x ^ s :=
      intervalIntegral.integral_mono_on (by norm_num) hLint hRint hpoint
    _ = p.μ * ∫ x in (0 : ℝ)..1, U x ^ s := by
      rw [intervalIntegral.integral_const_mul]

set_option maxHeartbeats 1000000 in
/-- **M-native orbit-independent eventual `L^p` damping constant, `1 ≤ m < 2`.**
At a fixed exponent `P > 1`, the physical equilibrium mass alone produces one
autonomous linear-damping constant, before any global orbit is chosen.  No
smallness of `χ₀` is needed: the subcritical excess `2m-2 < 2` is absorbed into
the diffusion dissipation by the seed-relative Agmon lemma with the `L^1` mass
seed. -/
theorem exists_intervalDomainM_minimal_subcritical_lp_damping_constant
    (p : CM2Params) {P uStar : ℝ}
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hp : 1 < P) (huStar : 0 < uStar) :
    ∃ K, 0 ≤ K ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomainM p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
        ∀ t, 0 < t →
          (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
            intervalDomainLpEnergy P u t ≤ K := by
  obtain ⟨hm1, hm2⟩ := hm
  have hP0 : 0 < P := lt_trans zero_lt_one hp
  have hP1 : 0 < P - 1 := sub_pos.mpr hp
  let C : ℝ := p.χ₀ * (P - 1)
  have hC : 0 < C := mul_pos hchi hP1
  let eps0 : ℝ := (P - 1) / 4
  have heps0 : 0 < eps0 := by dsimp [eps0]; linarith
  let K0 : ℝ := C ^ 2 / (4 * eps0)
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  -- target Gw-coefficient for the absorbed moment
  let cMom : ℝ := (P - 1) / (4 * (K0 * p.μ + 1))
  have hden : 0 < 4 * (K0 * p.μ + 1) := by
    have h := mul_nonneg hK0.le p.hμ.le
    linarith
  have hcMom : 0 < cMom := by dsimp [cMom]; exact div_pos hP1 hden
  -- K0 * μ * cMom ≤ (P-1)/4
  have hcoefMom : K0 * p.μ * cMom ≤ (P - 1) / 4 := by
    dsimp [cMom]
    rw [← mul_div_assoc]
    rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
    nlinarith [mul_nonneg hK0.le p.hμ.le, hP1.le]
  -- the mass Agmon interpolation at exponent P
  obtain ⟨CagY, hCagY, hagY⟩ :=
    unitIntervalPositiveAgmonInterpolation P hp ((P - 1) / 2) (by linarith)
  -- the mass Agmon interpolation used for the m = 1 moment branch
  obtain ⟨CagM, hCagM, hagM⟩ :=
    unitIntervalPositiveAgmonInterpolation P hp cMom hcMom
  -- the seed-relative Agmon absorption constant (m > 1 branch), orbit-free
  let rho : ℝ := 2 * p.m - 2
  let epsM : ℝ := cMom * 4 / P ^ 2
  have hepsM : 0 < epsM := by dsimp [epsM]; positivity
  let CabsM : ℝ := ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute.scalarSeedAgmonAbsorbConstant (max uStar 0) P 1 rho epsM
  let Ky : ℝ := CagY * uStar ^ P
  let Kmom1 : ℝ := CagM * uStar ^ P
  let Cmom : ℝ := max CabsM Kmom1
  let K : ℝ := K0 * p.μ * Cmom + Ky
  have hKy : 0 ≤ Ky := mul_nonneg hCagY.le (Real.rpow_nonneg huStar.le _)
  have hKmom1 : 0 ≤ Kmom1 := mul_nonneg hCagM.le (Real.rpow_nonneg huStar.le _)
  have hCmom : 0 ≤ Cmom := le_trans hKmom1 (le_max_right _ _)
  have hKnonneg : 0 ≤ K := by
    have hp1 : 0 ≤ K0 * p.μ * Cmom :=
      mul_nonneg (mul_nonneg hK0.le p.hμ.le) hCmom
    dsimp only [K]
    linarith [hKy]
  refine ⟨K, hKnonneg, ?_⟩
  intro u v huv hmass t ht0
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p T u v :=
    huv.1.classical hT
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  -- named quantities
  let Gw : ℝ := intervalDomainLpWeightedGradientDissipation P u t
  let Ye : ℝ := intervalDomainLpEnergy P u t
  let d : ℝ := (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t
  let s : ℝ := 2 * (P + p.m - 1) - P
  let Mom : ℝ := intervalDomain.integral (fun x => (u t x) ^ s)
  have hsval : s = P + rho := by dsimp [s, rho]; ring
  -- nonnegativity facts
  have hGw : 0 ≤ Gw := by
    dsimp [Gw]
    unfold intervalDomainLpWeightedGradientDissipation intervalDomain
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => by
      simp only [intervalDomainLift, hx, dif_pos]
      exact mul_nonneg (Real.rpow_nonneg (u_pos hsol ht0 htT ⟨x, hx⟩).le _)
        (sq_nonneg _))
  have hGweq : Gw = ∫ x in (0 : ℝ)..1,
      intervalDomainLift (u t) x ^ (P - 2) *
        |deriv (intervalDomainLift (u t)) x| ^ 2 := by
    dsimp [Gw]; exact weightedDissipation_eq_lift P u t
  have hYeq : Ye = intervalDomain.integral (fun x => (u t x) ^ P) := by
    dsimp [Ye]
    rw [lpEnergy_eq_lift_power_of_solution hsol ht0 htT]
    exact (intervalDomain_integral_rpow_eq_lift_integral (q := P) (f := u t)).symm
  have hYnonneg : 0 ≤ Ye := by
    rw [hYeq]
    exact intervalDomain_integral_rpow_nonneg (fun x => u_pos hsol ht0 htT x)
  have hMomEq : Mom = ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s := by
    dsimp [Mom]
    exact intervalDomain_integral_rpow_eq_lift_integral (q := s) (f := u t)
  have hMomNonneg : 0 ≤ Mom := by
    dsimp [Mom]
    exact intervalDomain_integral_rpow_nonneg (fun x => u_pos hsol ht0 htT x)
  -- mass at time t
  have hmass_t : intervalDomain.integral (u t) = uStar := by
    simpa [HasEquilibriumMassOnPositiveTimes, intervalDomainM, intervalDomain] using
      hmass t ht0
  have huC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hupos : ∀ x : intervalDomainPoint, 0 < u t x :=
    fun x => u_pos hsol ht0 htT x
  -- (E) energy identity
  have henergy := weightedLpEnergy_identity
    (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v)
      (ne_of_gt hP0) hsol ht0 htT
  rw [ha0, hb0] at henergy
  -- henergy : d + (P-1)*Gw + 0*Z = C*Cross + 0*Y   (folded)
  -- (CY) cross ≤ young bound
  let Cross : ℝ := lpSignedCrossIntegralM p P u v t
  have hcrossle : Cross ≤ descentMixed (P + p.m - 1) p.β u v t := by
    have habs := signedCross_abs_le_descentMixed
      (p := p) (T := T) (t := t) (pExp := P) (u := u) (v := v) hsol ht0 htT
    exact le_trans (le_abs_self _) habs
  have hCcross : C * Cross ≤ C * descentMixed (P + p.m - 1) p.β u v t :=
    mul_le_mul_of_nonneg_left hcrossle hC.le
  have hyoung := descentMixed_young_beta
    (p := p) (T := T) (t := t) (pExp := P) (r := P + p.m - 1)
      (C := C) (eps := eps0) (beta := p.β) (u := u) (v := v)
      hsol ht0 htT heps0
  rw [← hGweq] at hyoung
  -- hyoung : C * descentMixed (P+m-1) β ≤ eps0*Gw + K0 * descentVGradient s (2β)
  have hVG : descentVGradient (2 * (P + p.m - 1) - P) (2 * p.β) u v t ≤
      p.μ * ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ s := by
    exact descentVGradient_le_mu_moment (s := 2 * (P + p.m - 1) - P)
      hsol ht0 htT hbeta
  rw [← hMomEq] at hVG
  -- gradient integral appearing in the mass Agmon interpolation equals `Gw`
  have hgradBridge :
      intervalDomain.integral
        (fun x => (u t x) ^ (P - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) = Gw :=
    rfl
  -- (Y) mass Agmon interpolation on the `L^P` energy itself
  have hYabs : Ye ≤ (P - 1) / 2 * Gw + Ky := by
    have h := hagY (u t) hupos huC2
    rw [hgradBridge, hmass_t] at h
    rw [hYeq]
    simpa [Ky] using h
  -- (M) moment absorption:  Mom ≤ cMom * Gw + Cmom
  have hMomAbsorb : Mom ≤ cMom * Gw + Cmom := by
    by_cases hmeq : p.m = 1
    · -- s = P, moment is the `L^P` energy; use mass Agmon
      have hsP : s = P := by dsimp only [s]; rw [hmeq]; ring
      have hfun : (fun x : intervalDomainPoint => (u t x) ^ s)
          = fun x => (u t x) ^ P := by funext x; rw [hsP]
      have hMomP : Mom = intervalDomain.integral (fun x => (u t x) ^ P) :=
        congrArg intervalDomain.integral hfun
      have h := hagM (u t) hupos huC2
      rw [hgradBridge, hmass_t] at h
      rw [hMomP]
      have hmombd : intervalDomain.integral (fun x => (u t x) ^ P) ≤ cMom * Gw + Kmom1 := by
        simpa [Kmom1] using h
      have hmax : cMom * Gw + Kmom1 ≤ cMom * Gw + Cmom := by
        dsimp only [Cmom]; linarith [le_max_right CabsM Kmom1]
      exact hmombd.trans hmax
    · -- 1 < m < 2 : seed-relative Agmon absorption of the strictly higher moment
      have hmgt : 1 < p.m := lt_of_le_of_ne hm1 (Ne.symm hmeq)
      have hrhopos : 0 < rho := by dsimp only [rho]; linarith
      have hrho2 : rho < 2 * (1 : ℝ) := by dsimp only [rho]; linarith
      have hseed : ∀ s', 0 < s' → s' < T →
          intervalDomainM.integral (fun x => (u s' x) ^ (1 : ℝ)) ≤ uStar := by
        intro s' hs0 _
        have hmassEq : intervalDomainM.integral (fun x => u s' x) = uStar := by
          simpa [HasEquilibriumMassOnPositiveTimes, intervalDomainM, intervalDomain]
            using hmass s' hs0
        simp only [Real.rpow_one]
        exact le_of_eq hmassEq
      have habsorb := intervalDomainM_agmon_absorbed_of_lp_bound
        (p := p) (T := T) (rho := rho) (p0 := 1) (P := P) (C0 := uStar)
        (u := u) (v := v) hsol hrhopos (by norm_num) hp.le hrho2 hseed
        epsM hepsM t ht0 htT
      -- rewrite the moment exponent  s = P + rho
      have hfun : (fun x : intervalDomainPoint => (u t x) ^ s)
          = fun x => (u t x) ^ (P + rho) := by funext x; rw [hsval]
      have hMomPr : Mom = intervalDomain.integral (fun x => (u t x) ^ (P + rho)) :=
        congrArg intervalDomain.integral hfun
      -- epsM * (P^2/4) = cMom
      have hepsMcoef : epsM * (P ^ 2 / 4) = cMom := by
        dsimp only [epsM]
        field_simp
      rw [hMomPr]
      have hstep : intervalDomain.integral (fun x => (u t x) ^ (P + rho)) ≤
          cMom * Gw + ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute.scalarSeedAgmonAbsorbConstant (max uStar 0) P 1 rho epsM := by
        calc
          intervalDomain.integral (fun x => (u t x) ^ (P + rho))
              ≤ epsM * ((P ^ 2 / 4) *
                  intervalDomainLpWeightedGradientDissipation P u t) +
                ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute.scalarSeedAgmonAbsorbConstant (max uStar 0) P 1 rho epsM := habsorb
          _ = (epsM * (P ^ 2 / 4)) * Gw +
                ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute.scalarSeedAgmonAbsorbConstant (max uStar 0) P 1 rho epsM := by
            dsimp only [Gw]; ring
          _ = cMom * Gw +
                ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute.scalarSeedAgmonAbsorbConstant (max uStar 0) P 1 rho epsM := by rw [hepsMcoef]
      refine hstep.trans ?_
      dsimp only [Cmom, CabsM]
      linarith [le_max_left
        (ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute.scalarSeedAgmonAbsorbConstant (max uStar 0) P 1 rho epsM) Kmom1]
  -- assemble the energy identity into linear-damping form
  have hE : d + (P - 1) * Gw = C * Cross := by
    dsimp only [d, Gw, C, Cross]
    have := henergy
    simp only [zero_mul, add_zero] at this
    linarith [this]
  have hCY : C * Cross ≤ eps0 * Gw + K0 * descentVGradient (2 * (P + p.m - 1) - P) (2 * p.β) u v t := by
    have h2 := hCcross.trans hyoung
    have hK0eq : C ^ 2 / (4 * eps0) = K0 := rfl
    rw [hK0eq] at h2
    exact h2
  -- combine (E)+(CY)+(VG)+(M)+(Y)
  have h1 : C * Cross ≤ eps0 * Gw + K0 * (p.μ * Mom) := by
    have hKVG : K0 * descentVGradient (2 * (P + p.m - 1) - P) (2 * p.β) u v t
        ≤ K0 * (p.μ * Mom) := mul_le_mul_of_nonneg_left hVG hK0.le
    linarith [hCY, hKVG]
  have h2 : K0 * (p.μ * Mom) ≤ K0 * p.μ * cMom * Gw + K0 * p.μ * Cmom := by
    have hmm : p.μ * Mom ≤ p.μ * (cMom * Gw + Cmom) :=
      mul_le_mul_of_nonneg_left hMomAbsorb p.hμ.le
    have := mul_le_mul_of_nonneg_left hmm hK0.le
    nlinarith [this]
  have hcoef2 : eps0 * Gw + K0 * p.μ * cMom * Gw ≤ (P - 1) / 2 * Gw := by
    have hsum : eps0 + K0 * p.μ * cMom ≤ (P - 1) / 2 := by
      dsimp only [eps0]; linarith [hcoefMom]
    nlinarith [mul_le_mul_of_nonneg_right hsum hGw]
  have hCrossFinal : C * Cross ≤ (P - 1) / 2 * Gw + K0 * p.μ * Cmom := by
    linarith [h1, h2, hcoef2]
  have hdbound : d ≤ -((P - 1) / 2 * Gw) + K0 * p.μ * Cmom := by
    linarith [hE, hCrossFinal]
  have hfinal : d + Ye ≤ K := by
    dsimp only [K]
    linarith [hdbound, hYabs]
  calc
    (1 / P) * deriv (fun τ => intervalDomainLpEnergy P u τ) t +
        intervalDomainLpEnergy P u t = d + Ye := rfl
    _ ≤ K := hfinal

/-- **Step 1 (M-native), `1 ≤ m < 2`.**  Apply the scalar eventual linear-damping
lemma to the done orbit-independent subcritical seed damping constant.  At any
fixed exponent `P > 1`, every physical-mass bounded global orbit eventually
satisfies one orbit-independent `L^P` power bound. -/
theorem exists_intervalDomainM_minimal_eventual_lp_power_bound
    (p : CM2Params) {P uStar : ℝ}
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀)
    (hp : 1 < P) (huStar : 0 < uStar) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomainM p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
        ∀ᶠ t : ℝ in atTop,
          intervalDomainM.integral (fun x => (u t x) ^ P) ≤ C := by
  obtain ⟨K, hK, hdamp⟩ :=
    exists_intervalDomainM_minimal_subcritical_lp_damping_constant
      p hm ha0 hb0 hbeta hchi hp huStar
  refine ⟨K + 1, by linarith, ?_⟩
  intro u v huv hmass
  have hP0 : 0 < P := lt_trans zero_lt_one hp
  have hderiv : ∀ t, 0 < t →
      HasDerivAt (fun τ => intervalDomainLpEnergy P u τ)
        (deriv (fun τ => intervalDomainLpEnergy P u τ) t) t := by
    intro t ht
    have hsol := huv.classical (t + 1) (by linarith)
    exact lpEnergy_hasDerivAt_of_solution hsol ht (by linarith)
  have hev := eventually_le_add_one_of_linear_damping hP0 hderiv
    (hdamp u v huv hmass)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with t ht hTpos
  have hsol := huv.classical (t + 1) (by linarith)
  have heq : intervalDomainLpEnergy P u t =
      ∫ x in (0 : ℝ)..1, intervalDomainLift (u t) x ^ P :=
    lpEnergy_eq_lift_power_of_solution hsol hTpos (by linarith)
  have hdomain : intervalDomainM.integral (fun x => (u t x) ^ P) =
      intervalDomainLpEnergy P u t := by
    rw [heq]
    exact intervalDomain_integral_rpow_eq_lift_integral
  rw [hdomain]; exact ht

/-- **Step 2 (M-native), `1 ≤ m < 2`.**  Instantiate the seed damping at an
exponent `P = m·Q` with `Q > 1` and `P > γ`, so that the general-`m`
`L^P → L^∞` restart machinery applies.  Because the subcritical seed is
orbit-independent at every `P > 1`, no separate finite-power bootstrap is
required; `P` and its diffusion-conjugate `Q` are produced directly. -/
theorem exists_intervalDomainM_minimal_eventual_high_lp_power_bound
    (p : CM2Params) {uStar : ℝ}
    (hm : 1 ≤ p.m ∧ p.m < 2) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (hbeta : 1 ≤ p.β) (hchi : 0 < p.χ₀) (huStar : 0 < uStar) :
    ∃ P Q C : ℝ, 1 < P ∧ 1 < Q ∧ p.m * Q = P ∧ p.γ ≤ P ∧ 0 ≤ C ∧
      ∀ (u v : ℝ → intervalDomainPoint → ℝ),
        PositiveGlobalBoundedSolution intervalDomainM p u v →
        HasEquilibriumMassOnPositiveTimes intervalDomainM u uStar →
        ∀ᶠ t : ℝ in atTop,
          intervalDomainM.integral (fun x => (u t x) ^ P) ≤ C := by
  obtain ⟨hm1, hm2⟩ := hm
  have hmpos : 0 < p.m := lt_of_lt_of_le zero_lt_one hm1
  let P : ℝ := max 2 (p.γ + 1)
  have hP2 : (2 : ℝ) ≤ P := le_max_left _ _
  have hPγ : p.γ + 1 ≤ P := le_max_right _ _
  have hp : 1 < P := lt_of_lt_of_le one_lt_two hP2
  have hγP : p.γ ≤ P := by linarith
  have hPm : p.m < P := lt_of_lt_of_le hm2 hP2
  let Q : ℝ := P / p.m
  have hQ : 1 < Q := by
    rw [lt_div_iff₀ hmpos]; linarith [hPm]
  have hmQ : p.m * Q = P := by
    show p.m * (P / p.m) = P
    rw [mul_comm]
    exact div_mul_cancel₀ P (ne_of_gt hmpos)
  obtain ⟨C, hC, hbound⟩ :=
    exists_intervalDomainM_minimal_eventual_lp_power_bound
      (p := p) (P := P) ⟨hm1, hm2⟩ ha0 hb0 hbeta hchi hp huStar
  exact ⟨P, Q, C, hp, hQ, hmQ, hγP, hC, hbound⟩

end

end ShenWork.Paper3
