import ShenWork.Paper3.IntervalDomainEntropySlopeIdentity

/-!
# Concrete entropy dissipation in the first strong-logistic branch

This file combines four proved ingredients on the faithful unit interval:

* the exact entropy-slope identity;
* pointwise Young absorption of the chemotactic cross term;
* the weighted elliptic gradient estimate;
* Paper 3 Lemma A.6 for the source-power difference.

The resulting coefficient is exactly the radicand defining
`chiStrong1Formula` when `m = 1`.
-/

open ShenWork.IntervalDomain MeasureTheory Set
open scoped Topology Interval

namespace ShenWork.Paper3

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep

/-- Pointwise diffusion--chemotaxis Young inequality in the exact entropy
weights. -/
theorem entropyCrossYoung_pointwise
    {uStar chi beta U V ux vx : ℝ}
    (huStar : 0 < uStar) (hU : 0 < U) (hV : 0 ≤ V) :
    -uStar * (U ^ (-2 : ℝ) * ux ^ 2) +
        chi * uStar *
          (U ^ (-1 : ℝ) * ux * vx / (1 + V) ^ beta) ≤
      chi ^ 2 * uStar / 4 *
        (vx ^ 2 * (1 + V) ^ (-2 * beta)) := by
  let A : ℝ := ux / U
  let B : ℝ := vx * (1 + V) ^ (-beta)
  have hbase : 0 < 1 + V := by linarith
  have hU2 : U ^ (-2 : ℝ) * ux ^ 2 = A ^ 2 := by
    dsimp [A]
    have hpow : U ^ (-2 : ℝ) = (U ^ (2 : ℕ))⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg hU.le, Real.rpow_two]
    rw [hpow]
    field_simp [hU.ne']
  have hcross :
      U ^ (-1 : ℝ) * ux * vx / (1 + V) ^ beta = A * B := by
    dsimp [A, B]
    rw [Real.rpow_neg_one, Real.rpow_neg hbase.le]
    field_simp [hU.ne', (Real.rpow_pos_of_pos hbase beta).ne']
  have hweight :
      vx ^ 2 * (1 + V) ^ (-2 * beta) = B ^ 2 := by
    dsimp [B]
    have hpow : (1 + V) ^ (-2 * beta) =
        ((1 + V) ^ (-beta)) ^ (2 : ℕ) := by
      rw [← Real.rpow_mul_natCast hbase.le (-beta) 2]
      congr 1
      ring
    rw [hpow]
    ring
  rw [hU2, hcross, hweight]
  have hsquare : 0 ≤ uStar * (A - chi / 2 * B) ^ 2 :=
    mul_nonneg huStar.le (sq_nonneg _)
  nlinarith

/-- At exponent zero, the weighted gradient dissipation is the lifted
`u^{-2}|u_x|^2` integral. -/
theorem intervalDomain_lpGradient_zero_eq_integral
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomainLpWeightedGradientDissipation 0 u t =
      ∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y) ^ (-2 : ℝ) *
          (deriv (intervalDomainLift (u t)) y) ^ 2 := by
  unfold intervalDomainLpWeightedGradientDissipation
  change intervalDomainIntegral _ = _
  unfold intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp [intervalDomain, intervalDomainGradNorm, intervalDomainLift, hy, sq_abs]

/-- Young absorption of the first two terms in the entropy identity. -/
theorem intervalDomain_entropyDiffusionChemotaxis_young
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : p.m = 1)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (huStar : 0 < uStar) :
    -uStar * intervalDomainLpWeightedGradientDissipation 0 u t +
        p.χ₀ * uStar *
          ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM p 0 u v t ≤
      p.χ₀ ^ 2 * uStar / 4 *
        (∫ y in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) y) ^ 2 *
            (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  let Ux : ℝ → ℝ := deriv U
  let Vx : ℝ → ℝ := deriv V
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU2 : ContDiffOn ℝ 2 U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hUxcont : ContinuousOn Ux (Set.Icc (0 : ℝ) 1) := by
    dsimp [Ux]
    exact (ShenWork.Paper2.IntervalDomainM.deriv_lift_contDiffOn_one_Icc
      hU2
      (ShenWork.Paper2.IntervalDomainM.derivWithin_left_zero
        hsol ht0 htT u (Or.inl rfl))
      (ShenWork.Paper2.IntervalDomainM.derivWithin_right_zero
        hsol ht0 htT u (Or.inl rfl))).continuousOn
  have hVxcont : ContinuousOn Vx (Set.Icc (0 : ℝ) 1) := by
    dsimp [Vx, V]
    exact ShenWork.Paper2.IntervalDomainM.deriv_v_continuousOn_Icc
      hsol ht0 htT
  have hUpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < U y := by
    intro y hy
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_pos_Icc hsol ht y hy
  have hVnonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V y := by
    intro y hy
    simpa [V, intervalDomainLift, hy] using
      hsol.v_nonneg (x := (⟨y, hy⟩ : intervalDomain.Point)) ht0 htT
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := hU2.continuousOn
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := hV2.continuousOn
  let g : ℝ → ℝ := fun y => U y ^ (-2 : ℝ) * Ux y ^ 2
  let xterm : ℝ → ℝ := fun y =>
    U y ^ (-1 : ℝ) * Ux y * Vx y / (1 + V y) ^ p.β
  let rterm : ℝ → ℝ := fun y =>
    Vx y ^ 2 * (1 + V y) ^ (-2 * p.β)
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    dsimp [g]
    exact (hUcont.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))).mul (hUxcont.pow 2)
  have hxcont : ContinuousOn xterm (Set.Icc (0 : ℝ) 1) := by
    dsimp [xterm]
    exact ((((hUcont.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))).mul hUxcont).mul hVxcont).div
        ((continuousOn_const.add hVcont).rpow_const
          (fun y hy => Or.inl (by
            simpa only [Pi.add_apply] using
              (ne_of_gt (show 0 < 1 + V y by linarith [hVnonneg y hy])))))
        (fun y hy => ne_of_gt (Real.rpow_pos_of_pos
          (by linarith [hVnonneg y hy]) p.β)))
  have hrcont : ContinuousOn rterm (Set.Icc (0 : ℝ) 1) := by
    dsimp [rterm]
    exact (hVxcont.pow 2).mul
      ((continuousOn_const.add hVcont).rpow_const
        (fun y hy => Or.inl (by
          simpa only [Pi.add_apply] using
            (ne_of_gt (show 0 < 1 + V y by linarith [hVnonneg y hy])))))
  have hgint : IntervalIntegrable g volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hgcont
  have hxint : IntervalIntegrable xterm volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hxcont
  have hrint : IntervalIntegrable rterm volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hrcont
  have hG := intervalDomain_lpGradient_zero_eq_integral hsol ht0 htT
  have hX : ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM p 0 u v t =
      ∫ y in (0 : ℝ)..1, xterm y := by
    unfold ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
    dsimp [xterm, U, V, Ux, Vx]
    rw [hm]
    congr 1
    funext y
    congr 1
    ring
  rw [hG, hX]
  change -uStar * (∫ y in (0 : ℝ)..1, g y) +
      p.χ₀ * uStar * (∫ y in (0 : ℝ)..1, xterm y) ≤
    p.χ₀ ^ 2 * uStar / 4 * (∫ y in (0 : ℝ)..1, rterm y)
  calc
    -uStar * (∫ y in (0 : ℝ)..1, g y) +
          p.χ₀ * uStar * (∫ y in (0 : ℝ)..1, xterm y) =
        ∫ y in (0 : ℝ)..1,
          -uStar * g y + p.χ₀ * uStar * xterm y := by
      rw [intervalIntegral.integral_add (hgint.const_mul (-uStar))
          (hxint.const_mul (p.χ₀ * uStar)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ ∫ y in (0 : ℝ)..1,
          p.χ₀ ^ 2 * uStar / 4 * rterm y := by
      exact intervalIntegral.integral_mono_on (by norm_num)
        ((hgint.const_mul (-uStar)).add
          (hxint.const_mul (p.χ₀ * uStar)))
        (hrint.const_mul (p.χ₀ ^ 2 * uStar / 4))
        (fun y hy => by
          exact entropyCrossYoung_pointwise huStar (hUpos y hy) (hVnonneg y hy))
    _ = p.χ₀ ^ 2 * uStar / 4 *
          (∫ y in (0 : ℝ)..1, rterm y) := by
      rw [intervalIntegral.integral_const_mul]

/-- Integrated Paper 3 Lemma A.6 on one positive classical slice. -/
theorem intervalDomain_powerDifference_integral_le_theta
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) (huStar : 0 < uStar)
    (hrel : 2 * p.γ ≤ p.α + 1) :
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2) ≤
      CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol ht
  have hUpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < U y := by
    intro y hy
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_pos_Icc hsol ht y hy
  have hleftCont : ContinuousOn
      (fun y => (U y ^ p.γ - uStar ^ p.γ) ^ 2) (Set.Icc (0 : ℝ) 1) :=
    ((hUcont.rpow_const
      (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))).sub continuousOn_const).pow 2
  have hthetaCont : ContinuousOn
      (fun y => (U y - uStar) * (U y ^ p.α - uStar ^ p.α))
      (Set.Icc (0 : ℝ) 1) :=
    (hUcont.sub continuousOn_const).mul
      ((hUcont.rpow_const
        (fun y hy => Or.inl (ne_of_gt (hUpos y hy)))).sub continuousOn_const)
  have hleftInt : IntervalIntegrable
      (fun y => (U y ^ p.γ - uStar ^ p.γ) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hleftCont
  have hthetaInt : IntervalIntegrable
      (fun y => CAlphaGamma p.α p.γ *
        uStar ^ (2 * p.γ - p.α - 1) *
          ((U y - uStar) * (U y ^ p.α - uStar ^ p.α))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_const.mul hthetaCont
  have hmono := intervalIntegral.integral_mono_on (by norm_num) hleftInt hthetaInt
    (fun y hy => Lemma_A_6.apply p.hα p.hγ hrel huStar (hUpos y hy))
  have hthetaLift :
      intervalDomainIntegral (fun x =>
          (u t x - uStar) * (u t x ^ p.α - uStar ^ p.α)) =
        ∫ y in (0 : ℝ)..1,
          (U y - uStar) * (U y ^ p.α - uStar ^ p.α) := by
    unfold intervalDomainIntegral
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le zero_le_one] at hy
    simp only [intervalDomainLift, hy, ↓reduceDIte, U]
  unfold chemotaxisThetaDissipation
  change _ ≤ CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
    intervalDomainIntegral _
  calc
    (∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2) ≤
        CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
          (∫ y in (0 : ℝ)..1,
            (U y - uStar) * (U y ^ p.α - uStar ^ p.α)) := by
      rw [← intervalIntegral.integral_const_mul]
      simpa [mul_assoc] using hmono
    _ = CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
          intervalDomainIntegral (fun x =>
            (u t x - uStar) * (u t x ^ p.α - uStar ^ p.α)) := by
      rw [hthetaLift]

/-- Entropy dissipation inequality with its exact positive-coefficient
frontier exposed. -/
theorem intervalDomain_entropySlope_le_strong1Coefficient
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : p.m = 1)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1) :
    intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) ≤
      -(p.b -
          p.χ₀ ^ 2 * p.ν ^ 2 * CAlphaGamma p.α p.γ *
              uStar ^ (2 * p.γ - p.α) /
            (16 * p.μ * (1 + betaTilde p.β * vStar))) *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  have hid := intervalDomain_entropySlope_identity hm hsol ht0 htT heq
  have hyoung := intervalDomain_entropyDiffusionChemotaxis_young
    hm hsolM ht0 htT heq.u_pos
  have hell := intervalDomain_entropyElliptic_gradient_estimate_of_classical
    hsolM ht0 htT heq
  have hpower := intervalDomain_powerDifference_integral_le_theta
    hsolM ht0 htT heq.u_pos hrel
  have hfactor : 0 < 1 + betaTilde p.β * vStar := by
    have := mul_nonneg (betaTilde_nonneg p.β) heq.v_nonneg
    linarith
  have hscale : 0 ≤ p.χ₀ ^ 2 * uStar / 4 := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) heq.u_pos.le) (by norm_num)
  have hell' :
      p.χ₀ ^ 2 * uStar / 4 *
          (∫ y in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) y) ^ 2 *
              (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)) ≤
        p.χ₀ ^ 2 * uStar / 4 *
          (p.ν ^ 2 / (4 * p.μ *
              (1 + betaTilde p.β * vStar)) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) := by
    have hrearrange :
        (∫ y in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) y) ^ 2 *
            (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)) ≤
          p.ν ^ 2 / (4 * p.μ *
              (1 + betaTilde p.β * vStar)) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2) := by
      have hcoeff : p.ν ^ 2 /
              (4 * p.μ * (1 + betaTilde p.β * vStar)) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2) =
          (p.ν ^ 2 / (4 * p.μ) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) /
            (1 + betaTilde p.β * vStar) := by
        field_simp [p.hμ.ne', hfactor.ne']
        <;> ring
      rw [hcoeff]
      apply (le_div_iff₀ hfactor).2
      simpa only [mul_comm] using hell
    exact mul_le_mul_of_nonneg_left hrearrange hscale
  have hpowerScale : 0 ≤
      p.χ₀ ^ 2 * uStar / 4 *
        (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar))) := by
    have hden : 0 < 4 * p.μ * (1 + betaTilde p.β * vStar) := by
      exact mul_pos (mul_pos (by norm_num) p.hμ) hfactor
    exact mul_nonneg hscale (div_nonneg (sq_nonneg _) hden.le)
  calc
    intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) =
        -uStar * intervalDomainLpWeightedGradientDissipation 0 u t +
          p.χ₀ * uStar *
            ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM p 0 u v t -
          p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := hid
    _ ≤ p.χ₀ ^ 2 * uStar / 4 *
          (∫ y in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) y) ^ 2 *
              (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      linarith
    _ ≤ p.χ₀ ^ 2 * uStar / 4 *
          (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      linarith
    _ ≤ p.χ₀ ^ 2 * uStar / 4 *
          (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)) *
            (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
              chemotaxisThetaDissipation intervalDomain uStar p.α (u t))) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      apply sub_le_sub_right
      calc
        p.χ₀ ^ 2 * uStar / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)) *
                (∫ y in (0 : ℝ)..1,
                  (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) =
            (p.χ₀ ^ 2 * uStar / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)))) *
              (∫ y in (0 : ℝ)..1,
                (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2) := by ring
        _ ≤ (p.χ₀ ^ 2 * uStar / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)))) *
              (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
                chemotaxisThetaDissipation intervalDomain uStar p.α (u t)) :=
          mul_le_mul_of_nonneg_left hpower hpowerScale
        _ = p.χ₀ ^ 2 * uStar / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)) *
                (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
                  chemotaxisThetaDissipation intervalDomain uStar p.α (u t))) := by ring
    _ = -(p.b -
          p.χ₀ ^ 2 * p.ν ^ 2 * CAlphaGamma p.α p.γ *
              uStar ^ (2 * p.γ - p.α) /
            (16 * p.μ * (1 + betaTilde p.β * vStar))) *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      have huPow :
          uStar * uStar ^ (2 * p.γ - p.α - 1) =
            uStar ^ (2 * p.γ - p.α) := by
        calc
          uStar * uStar ^ (2 * p.γ - p.α - 1) =
              uStar ^ (1 : ℝ) * uStar ^ (2 * p.γ - p.α - 1) := by
            rw [Real.rpow_one]
          _ = uStar ^ ((1 : ℝ) + (2 * p.γ - p.α - 1)) := by
            rw [← Real.rpow_add heq.u_pos]
          _ = uStar ^ (2 * p.γ - p.α) := by
            congr 1
            ring
      rw [← huPow]
      field_simp [p.hμ.ne', hfactor.ne']
      ring

#print axioms entropyCrossYoung_pointwise
#print axioms intervalDomain_lpGradient_zero_eq_integral
#print axioms intervalDomain_entropyDiffusionChemotaxis_young
#print axioms intervalDomain_powerDifference_integral_le_theta
#print axioms intervalDomain_entropySlope_le_strong1Coefficient

end

end ShenWork.Paper3
