import ShenWork.Paper2.IntervalDomainWeightedGradientEstimate
import ShenWork.Paper2.IntervalDomainCrossDiffusionBootstrap
import ShenWork.Paper2.IntervalDomainLpEnergyFrontiers

/-!
# Sharp interval-domain cross-diffusion bootstrap

The concrete weighted elliptic estimate is combined with two scalar Young
inequalities to obtain the Paper 2 bootstrap exponent `rho = gamma`.  This is
the exponent required by the printed critical threshold; the older resolver
sup-norm route only produced `rho = 2 * gamma`.
-/

open MeasureTheory Set
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization

noncomputable section

namespace ShenWork.Paper2

theorem crossDiffusion_pointwise_young_weighted
    {u ux vx den eps pExp : ℝ}
    (hu : 0 < u) (hden : 0 < den) (heps : 0 < eps) :
    u ^ (pExp - 1) * |ux| * |vx| / den ≤
      eps * (u ^ (pExp - 2) * |ux| ^ 2) +
        (1 / (4 * eps)) * (u ^ pExp * (|vx| ^ 2 / den ^ 2)) := by
  let A : ℝ := u ^ ((pExp - 2) / 2) * |ux|
  let B : ℝ := u ^ (pExp / 2) * |vx| / den
  have h4eps : 0 < 4 * eps := by positivity
  have hY : A * B ≤ eps * A ^ 2 + B ^ 2 / (4 * eps) := by
    have hmul : (4 * eps) * (A * B) ≤
        (4 * eps) * (eps * A ^ 2 + B ^ 2 / (4 * eps)) := by
      field_simp [ne_of_gt h4eps]
      nlinarith [sq_nonneg (2 * eps * A - B)]
    exact le_of_mul_le_mul_left hmul h4eps
  have hleft : A * B = u ^ (pExp - 1) * |ux| * |vx| / den := by
    dsimp [A, B]
    have hpow : u ^ ((pExp - 2) / 2) * u ^ (pExp / 2) = u ^ (pExp - 1) := by
      rw [← Real.rpow_add hu]
      congr 1
      ring
    calc
      u ^ ((pExp - 2) / 2) * |ux| * (u ^ (pExp / 2) * |vx| / den) =
          (u ^ ((pExp - 2) / 2) * u ^ (pExp / 2)) * |ux| * |vx| / den := by ring
      _ = u ^ (pExp - 1) * |ux| * |vx| / den := by rw [hpow]
  have hA2 : A ^ 2 = u ^ (pExp - 2) * |ux| ^ 2 := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_mul_natCast hu.le ((pExp - 2) / 2) 2]
    ring_nf
  have hB2 : B ^ 2 / (4 * eps) =
      (1 / (4 * eps)) * (u ^ pExp * (|vx| ^ 2 / den ^ 2)) := by
    dsimp [B]
    rw [div_pow, mul_pow, ← Real.rpow_mul_natCast hu.le (pExp / 2) 2]
    field_simp [ne_of_gt hden, ne_of_gt h4eps]
    ring
  calc
    u ^ (pExp - 1) * |ux| * |vx| / den = A * B := hleft.symm
    _ ≤ eps * A ^ 2 + B ^ 2 / (4 * eps) := hY
    _ = eps * (u ^ (pExp - 2) * |ux| ^ 2) +
        (1 / (4 * eps)) * (u ^ pExp * (|vx| ^ 2 / den ^ 2)) := by
      rw [hA2, hB2]

theorem crossDiffusion_power_product_young
    {u Z pExp gamma : ℝ}
    (hu : 0 < u) (hZ : 0 ≤ Z) (hp : 0 < pExp) (hgamma : 0 < gamma) :
    let r := (pExp + gamma) / pExp
    let q := (pExp + gamma) / gamma
    u ^ pExp * Z ≤ u ^ (pExp + gamma) / r + Z ^ q / q := by
  dsimp
  let r : ℝ := (pExp + gamma) / pExp
  let q : ℝ := (pExp + gamma) / gamma
  have hr : 1 < r := by
    dsimp [r]
    rw [one_lt_div hp]
    linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div hgamma]
    linarith
  have hrq : r.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hr, ?_⟩
    dsimp [r, q]
    field_simp [ne_of_gt hp, ne_of_gt hgamma, ne_of_gt (add_pos hp hgamma)]
  have hY := Real.young_inequality_of_nonneg
    (a := u ^ pExp) (b := Z) (Real.rpow_nonneg hu.le _) hZ hrq
  have hupow : (u ^ pExp) ^ r = u ^ (pExp + gamma) := by
    rw [← Real.rpow_mul hu.le]
    dsimp [r]
    have : pExp * ((pExp + gamma) / pExp) = pExp + gamma := by
      field_simp [ne_of_gt hp]
    rw [this]
  simpa [r, q, hupow] using hY

theorem crossDiffusion_weighted_factor_rpow
    {vx v beta q : ℝ} (hv : 0 ≤ v) :
    (|vx| ^ 2 / (1 + v) ^ (2 * beta)) ^ q =
      |vx| ^ (2 * q) / (1 + v) ^ ((2 * beta) * q) := by
  have hbase : 0 ≤ 1 + v := by linarith
  rw [Real.div_rpow (sq_nonneg _) (Real.rpow_nonneg hbase _),
    ← Real.rpow_mul hbase]
  have habs : 0 ≤ |vx| := abs_nonneg _
  rw [show |vx| ^ (2 : ℕ) = |vx| ^ (2 : ℝ) by simp [Real.rpow_natCast],
    ← Real.rpow_mul habs]

/-- Explicit coefficient in the sharp `rho = gamma` cross-diffusion
estimate.  It is independent of the solution and its time horizon. -/
def intervalDomainSharpCrossDiffusionConstant
    (p : CM2Params) (pExp eps : ℝ) : ℝ :=
  let q : ℝ := (pExp + p.γ) / p.γ
  let r : ℝ := (pExp + p.γ) / pExp
  let beta2 : ℝ := 2 * p.β - 1
  (1 / (4 * eps)) *
    (1 / r + (Theta_beta beta2) ^ q *
      intervalDomainWeightedGradientConstant p q / q)

/-- Pointwise-in-time sharp cross-diffusion estimate with its fixed
coefficient exposed. -/
theorem intervalDomain_crossDiffusionBootstrapEstimate_sharp_explicit
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hbeta : 1 ≤ p.β) {eps pExp : ℝ}
    (heps : 0 < eps) (hpExp : 1 < pExp) :
    ∀ t, 0 < t → t < T →
      intervalDomain.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
        eps * intervalDomain.integral (fun x =>
          (u t x) ^ (pExp - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) +
        intervalDomainSharpCrossDiffusionConstant p pExp eps *
          intervalDomain.integral (fun x => (u t x) ^ (pExp + p.γ)) := by
  let q : ℝ := (pExp + p.γ) / p.γ
  let r : ℝ := (pExp + p.γ) / pExp
  let beta2 : ℝ := 2 * p.β - 1
  have hp : 0 < pExp := zero_lt_one.trans hpExp
  have hq : 1 < q := by
    dsimp [q]
    rw [one_lt_div p.hγ]
    linarith [hp]
  have hr : 1 < r := by
    dsimp [r]
    rw [one_lt_div hp]
    linarith [p.hγ]
  have hbeta2 : 0 ≤ beta2 := by dsimp [beta2]; linarith
  let Mstar : ℝ := intervalDomainWeightedGradientConstant p q
  have hweighted :=
    intervalDomain_weightedGradientEstimate_of_classical_beta_explicit
      hsol hq hbeta2
  let Ceps : ℝ := (1 / (4 * eps)) *
    (1 / r + (Theta_beta beta2) ^ q * Mstar / q)
  intro t ht0 htT
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let UX : ℝ → ℝ := deriv U
  let VX : ℝ → ℝ := deriv V
  let Den : ℝ → ℝ := fun x => (1 + V x) ^ p.β
  let Z : ℝ → ℝ := fun x => |VX x| ^ 2 / (1 + V x) ^ (2 * p.β)
  let Cross : ℝ → ℝ := fun x => U x ^ (pExp - 1) * |UX x| * |VX x| / Den x
  let Grad : ℝ → ℝ := fun x => U x ^ (pExp - 2) * |UX x| ^ 2
  let High : ℝ → ℝ := fun x => U x ^ (pExp + p.γ)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hCu : ContDiffOn ℝ 2 U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hCv : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using solution_lift_pos hsol ht x hx
  have hVpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < V x := by
    simpa [V] using intervalDomain_solution_lift_v_pos_Icc hsol ht0 htT
  have hUXcont : ContinuousOn UX (Set.Icc (0 : ℝ) 1) := by
    have hd0 : derivWithin U (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      simpa [U] using intervalDomain_solution_derivWithin_u_left_zero hsol ht0 htT
    have hd1 : derivWithin U (Set.Icc (0 : ℝ) 1) 1 = 0 := by
      simpa [U] using intervalDomain_solution_derivWithin_u_right_zero hsol ht0 htT
    simpa [UX] using deriv_intervalDomainLift_continuousOn_Icc_of_regularity hCu hd0 hd1
  have hVXcont : ContinuousOn VX (Set.Icc (0 : ℝ) 1) := by
    simpa [VX, V] using
      (resolverGradReal_contDiffOn_Icc hsol ht).continuousOn.congr
        (fun x hx => solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hx)
  have hDenpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < Den x := by
    intro x hx
    exact Real.rpow_pos_of_pos (by have := hVpos x hx; linarith) _
  have hCrossCont : ContinuousOn Cross (Set.Icc (0 : ℝ) 1) := by
    dsimp [Cross]
    have huPow : ContinuousOn (fun x => U x ^ (pExp - 1))
        (Set.Icc (0 : ℝ) 1) :=
      hCu.continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
    have hdenCont : ContinuousOn Den (Set.Icc (0 : ℝ) 1) := by
      dsimp [Den]
      exact (continuousOn_const.add hCv.continuousOn).rpow_const
        (fun x hx => Or.inl (ne_of_gt (show 0 < 1 + V x by
          have := hVpos x hx
          linarith)))
    exact ((huPow.mul hUXcont.abs).mul hVXcont.abs).div hdenCont
      (fun x hx => ne_of_gt (hDenpos x hx))
  have hGradCont : ContinuousOn Grad (Set.Icc (0 : ℝ) 1) := by
    exact (hCu.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul (hUXcont.abs.pow 2)
  have hZCont : ContinuousOn Z (Set.Icc (0 : ℝ) 1) := by
    dsimp [Z]
    have hbase : ContinuousOn (fun x => 1 + V x) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.add hCv.continuousOn
    have hden : ContinuousOn (fun x => (1 + V x) ^ (2 * p.β))
        (Set.Icc (0 : ℝ) 1) :=
      hbase.rpow_const (fun x hx => Or.inl (by
        have := hVpos x hx
        linarith))
    exact (hVXcont.abs.pow 2).div hden (fun x hx => ne_of_gt
      (Real.rpow_pos_of_pos (by have := hVpos x hx; linarith) _))
  have hHighCont : ContinuousOn High (Set.Icc (0 : ℝ) 1) :=
    hCu.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))
  have hCrossInt : IntervalIntegrable Cross volume 0 1 := by
    have hc : ContinuousOn Cross (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hCrossCont
    exact hc.intervalIntegrable
  have hGradInt : IntervalIntegrable Grad volume 0 1 := by
    have hc : ContinuousOn Grad (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hGradCont
    exact hc.intervalIntegrable
  have hZContPow : ContinuousOn (fun x => Z x ^ q) (Set.Icc (0 : ℝ) 1) :=
    hZCont.rpow_const (fun _ _ => Or.inr (zero_lt_one.trans hq).le)
  have hZPowInt : IntervalIntegrable (fun x => Z x ^ q) volume 0 1 := by
    have hc : ContinuousOn (fun x => Z x ^ q) (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hZContPow
    exact hc.intervalIntegrable
  have hHighInt : IntervalIntegrable High volume 0 1 := by
    have hc : ContinuousOn High (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hHighCont
    exact hc.intervalIntegrable
  have hUZCont : ContinuousOn (fun x => U x ^ pExp * Z x) (Set.Icc (0 : ℝ) 1) :=
    (hCu.continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hUpos x hx)))).mul hZCont
  have hUZInt : IntervalIntegrable (fun x => U x ^ pExp * Z x) volume 0 1 := by
    have hc : ContinuousOn (fun x => U x ^ pExp * Z x) (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hUZCont
    exact hc.intervalIntegrable
  have hfirstPoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Cross x ≤ eps * Grad x + (1 / (4 * eps)) * (U x ^ pExp * Z x) := by
    intro x hx
    have hden2 : Den x ^ 2 = (1 + V x) ^ (2 * p.β) := by
      dsimp [Den]
      rw [← Real.rpow_mul_natCast (by have := hVpos x hx; linarith) p.β 2]
      congr 1
      ring
    simpa [Cross, Grad, Z, mul_assoc, hden2] using
      (crossDiffusion_pointwise_young_weighted
        (u := U x) (ux := UX x) (vx := VX x) (den := Den x)
        (eps := eps) (pExp := pExp) (hUpos x hx) (hDenpos x hx) heps)
  have hfirstInt :
      (∫ x in (0 : ℝ)..1, Cross x) ≤
        eps * (∫ x in (0 : ℝ)..1, Grad x) +
          (1 / (4 * eps)) * (∫ x in (0 : ℝ)..1, U x ^ pExp * Z x) := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1,
          eps * Grad x + (1 / (4 * eps)) * (U x ^ pExp * Z x) :=
        intervalIntegral.integral_mono_on (by norm_num) hCrossInt
          ((hGradInt.const_mul eps).add (hUZInt.const_mul (1 / (4 * eps))))
          hfirstPoint
      _ = _ := by
        rw [intervalIntegral.integral_add
            (hGradInt.const_mul eps) (hUZInt.const_mul (1 / (4 * eps))),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsecondPoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      U x ^ pExp * Z x ≤ High x / r + Z x ^ q / q := by
    intro x hx
    have hZnn : 0 ≤ Z x := by
      dsimp [Z]
      exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by
        have := hVpos x hx
        linarith) _)
    simpa [High, r, q] using crossDiffusion_power_product_young
      (hUpos x hx) hZnn hp p.hγ
  have hsecondInt :
      (∫ x in (0 : ℝ)..1, U x ^ pExp * Z x) ≤
        (1 / r) * (∫ x in (0 : ℝ)..1, High x) +
          (1 / q) * (∫ x in (0 : ℝ)..1, Z x ^ q) := by
    have hright : IntervalIntegrable
        (fun x => High x / r + Z x ^ q / q) volume 0 1 :=
      (hHighInt.div_const r).add (hZPowInt.div_const q)
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, High x / r + Z x ^ q / q :=
        intervalIntegral.integral_mono_on (by norm_num) hUZInt hright hsecondPoint
      _ = _ := by
        rw [intervalIntegral.integral_add (hHighInt.div_const r) (hZPowInt.div_const q),
          intervalIntegral.integral_div, intervalIntegral.integral_div]
        ring
  have hZpowEq :
      (∫ x in (0 : ℝ)..1, Z x ^ q) =
        ∫ x in (0 : ℝ)..1,
          |VX x| ^ (2 * q) / (1 + V x) ^ ((1 + beta2) * q) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hx
    dsimp [Z]
    rw [crossDiffusion_weighted_factor_rpow (hVpos x hx).le]
    congr 2
    dsimp [beta2]
    ring
  have hw := (hweighted t ht0 htT).2
  rw [intervalDomain_weighted_one_add_v_integral_lift,
    intervalDomain_power_integral_lift'] at hw
  have hgammaq : p.γ * q = pExp + p.γ := by
    dsimp [q]
    field_simp [ne_of_gt p.hγ]
  have hZbound :
      (∫ x in (0 : ℝ)..1, Z x ^ q) ≤
        (Theta_beta beta2) ^ q * Mstar *
          (∫ x in (0 : ℝ)..1, High x) := by
    rw [hZpowEq]
    simpa [V, U, VX, High, hgammaq] using hw
  have hUZbound :
      (∫ x in (0 : ℝ)..1, U x ^ pExp * Z x) ≤
        (1 / r + (Theta_beta beta2) ^ q * Mstar / q) *
          (∫ x in (0 : ℝ)..1, High x) := by
    calc
      _ ≤ (1 / r) * (∫ x in (0 : ℝ)..1, High x) +
          (1 / q) * (∫ x in (0 : ℝ)..1, Z x ^ q) := hsecondInt
      _ ≤ (1 / r) * (∫ x in (0 : ℝ)..1, High x) +
          (1 / q) * ((Theta_beta beta2) ^ q * Mstar *
            (∫ x in (0 : ℝ)..1, High x)) := by
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hZbound
            (show 0 ≤ (1 / q : ℝ) by positivity))
      _ = _ := by ring
  have hfinalRaw :
      (∫ x in (0 : ℝ)..1, Cross x) ≤
        eps * (∫ x in (0 : ℝ)..1, Grad x) +
          Ceps * (∫ x in (0 : ℝ)..1, High x) := by
    calc
      _ ≤ eps * (∫ x in (0 : ℝ)..1, Grad x) +
          (1 / (4 * eps)) * (∫ x in (0 : ℝ)..1, U x ^ pExp * Z x) := hfirstInt
      _ ≤ eps * (∫ x in (0 : ℝ)..1, Grad x) +
          (1 / (4 * eps)) *
            ((1 / r + (Theta_beta beta2) ^ q * Mstar / q) *
              (∫ x in (0 : ℝ)..1, High x)) := by
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hUZbound
            (show 0 ≤ (1 / (4 * eps) : ℝ) by positivity))
      _ = _ := by dsimp [Ceps]; ring
  change (∫ x in (0 : ℝ)..1, Cross x) ≤
    eps * intervalDomain.integral
      (fun x => (u t x) ^ (pExp - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) +
    Ceps * intervalDomain.integral (fun x => (u t x) ^ (pExp + p.γ))
  rw [intervalDomain_weightedGradient_integral_lift,
    intervalDomain_integral_power_lift]
  simpa [Cross, Grad, High, U, V, UX, VX, Den, Ceps, Mstar,
    intervalDomainSharpCrossDiffusionConstant, q, r, beta2] using hfinalRaw

theorem intervalDomain_crossDiffusionBootstrapEstimate_sharp
    {p : CM2Params} {T : ℝ} {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hbeta : 1 ≤ p.β) :
    CrossDiffusionBootstrapEstimate intervalDomain p T p.γ u v := by
  intro eps heps pExp hpExp
  exact ⟨intervalDomainSharpCrossDiffusionConstant p pExp eps,
    intervalDomain_crossDiffusionBootstrapEstimate_sharp_explicit
      hsol hbeta heps hpExp⟩

#print axioms intervalDomain_crossDiffusionBootstrapEstimate_sharp_explicit
#print axioms intervalDomain_crossDiffusionBootstrapEstimate_sharp

end ShenWork.Paper2
