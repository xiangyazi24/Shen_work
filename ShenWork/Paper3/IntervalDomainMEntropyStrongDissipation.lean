import ShenWork.Paper3.IntervalDomainMEntropySlopeIdentity
import ShenWork.Paper3.IntervalDomainEntropyEllipticGradient
import ShenWork.Paper3.IntervalDomainEntropyStrong1

/-!
# Concrete general-`m` entropy dissipation in the first strong-logistic branch

This file combines, on the faithful `u^m`-flux interval equation:

* the exact general-`m` entropy-slope inequality (File `IntervalDomainMEntropySlopeIdentity`);
* pointwise Young absorption of the chemotactic cross term at the general-`m`
  exponents `U^(-2m)`, `U^(-m)` — the paper's (7.5)–(7.6) with coefficient
  `(2m-1) uStar^(2m-1)`;
* the weighted elliptic gradient estimate (reused, exponent-free);
* Paper 3 Lemma A.6 for the source-power difference (reused).

The resulting coefficient is exactly the radicand defining
`chiStrong1Formula` for general `m ≥ 1`; no `p.m = 1` hypothesis occurs.
-/

open ShenWork.IntervalDomain MeasureTheory Set
open scoped Topology Interval

namespace ShenWork.Paper3

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep

/-- Pointwise diffusion–chemotaxis Young inequality in the general-`m`
entropy weights (paper (7.5)–(7.6)).  The scale `c` is the positive constant
`(2m-1) uStar^(2m-1)`. -/
theorem entropyCrossYoungM_pointwise
    {m c chi beta U V ux vx : ℝ}
    (hc : 0 ≤ c) (hU : 0 < U) (hV : 0 ≤ V) :
    -c * (U ^ ((2 - 2 * m) - 2) * ux ^ 2) +
        chi * c *
          (U ^ ((2 - 2 * m) + m - 2) * ux * vx / (1 + V) ^ beta) ≤
      chi ^ 2 * c / 4 *
        (vx ^ 2 * (1 + V) ^ (-2 * beta)) := by
  have he1 : ((2 - 2 * m) - 2 : ℝ) = -m + -m := by ring
  have he2 : ((2 - 2 * m) + m - 2 : ℝ) = -m := by ring
  rw [he1, he2]
  have hbase : 0 < 1 + V := by linarith
  set A : ℝ := U ^ (-m) * ux with hA
  set B : ℝ := vx * (1 + V) ^ (-beta) with hB
  have hU2 : U ^ (-m + -m) * ux ^ 2 = A ^ 2 := by
    dsimp [A]
    rw [Real.rpow_add hU]
    ring
  have hcross : U ^ (-m) * ux * vx / (1 + V) ^ beta = A * B := by
    dsimp [A, B]
    rw [Real.rpow_neg hbase.le, div_eq_mul_inv]
    ring
  have hweight : vx ^ 2 * (1 + V) ^ (-2 * beta) = B ^ 2 := by
    dsimp [B]
    have hsq : ((1 + V) ^ (-beta)) ^ 2 = (1 + V) ^ (-2 * beta) := by
      rw [sq, ← Real.rpow_add hbase]
      congr 1
      ring
    rw [← hsq]
    ring
  rw [hU2, hcross, hweight]
  nlinarith [mul_nonneg hc (sq_nonneg (A - chi / 2 * B))]

/-- The weighted gradient dissipation as a lifted interval integral, for an
arbitrary exponent. -/
theorem intervalDomainM_lpGradient_eq_integral
    {p : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (_ht0 : 0 < t) (_htT : t < T) :
    intervalDomainLpWeightedGradientDissipation q u t =
      ∫ y in (0 : ℝ)..1,
        (intervalDomainLift (u t) y) ^ (q - 2) *
          (deriv (intervalDomainLift (u t)) y) ^ 2 := by
  unfold intervalDomainLpWeightedGradientDissipation
  change intervalDomainIntegral _ = _
  unfold intervalDomainIntegral
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp [intervalDomain, intervalDomainGradNorm, intervalDomainLift, hy, sq_abs]

/-- Young absorption of the general-`m` diffusion and chemotaxis terms in the
entropy slope, with an arbitrary nonnegative scale. -/
theorem intervalDomainM_entropyDiffusionChemotaxis_young
    {p : CM2Params} {T t c : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hc : 0 ≤ c)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    -c * intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t +
        p.χ₀ * c *
          ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
            p (2 - 2 * p.m) u v t ≤
      p.χ₀ ^ 2 * c / 4 *
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
  let g : ℝ → ℝ := fun y => U y ^ ((2 - 2 * p.m) - 2) * Ux y ^ 2
  let xterm : ℝ → ℝ := fun y =>
    U y ^ ((2 - 2 * p.m) + p.m - 2) * Ux y * Vx y / (1 + V y) ^ p.β
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
  have hG := intervalDomainM_lpGradient_eq_integral
    (q := 2 - 2 * p.m) hsol ht0 htT
  have hX : ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
      p (2 - 2 * p.m) u v t = ∫ y in (0 : ℝ)..1, xterm y := rfl
  rw [hG, hX]
  change -c * (∫ y in (0 : ℝ)..1, g y) +
      p.χ₀ * c * (∫ y in (0 : ℝ)..1, xterm y) ≤
    p.χ₀ ^ 2 * c / 4 * (∫ y in (0 : ℝ)..1, rterm y)
  calc
    -c * (∫ y in (0 : ℝ)..1, g y) +
          p.χ₀ * c * (∫ y in (0 : ℝ)..1, xterm y) =
        ∫ y in (0 : ℝ)..1,
          -c * g y + p.χ₀ * c * xterm y := by
      rw [intervalIntegral.integral_add (hgint.const_mul (-c))
          (hxint.const_mul (p.χ₀ * c)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ ∫ y in (0 : ℝ)..1,
          p.χ₀ ^ 2 * c / 4 * rterm y := by
      exact intervalIntegral.integral_mono_on (by norm_num)
        ((hgint.const_mul (-c)).add
          (hxint.const_mul (p.χ₀ * c)))
        (hrint.const_mul (p.χ₀ ^ 2 * c / 4))
        (fun y hy => by
          exact entropyCrossYoungM_pointwise hc (hUpos y hy) (hVnonneg y hy))
    _ = p.χ₀ ^ 2 * c / 4 *
          (∫ y in (0 : ℝ)..1, rterm y) := by
      rw [intervalIntegral.integral_const_mul]

/-- Exact entropy-production coefficient in the general-`m` first strong
logistic branch: the radicand of `chiStrong1Formula`. -/
def strongMEntropyCoefficient
    (p : CM2Params) (uStar vStar : ℝ) : ℝ :=
  p.b -
    p.χ₀ ^ 2 * p.ν ^ 2 * (2 * p.m - 1) * CAlphaGamma p.α p.γ *
        uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) /
      (16 * p.μ * (1 + betaTilde p.β * vStar))

/-- General-`m` entropy dissipation inequality with its exact
positive-coefficient frontier exposed (paper (7.5)–(7.8)). -/
theorem intervalDomainM_entropySlope_le_strongMCoefficient
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1) :
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) ≤
      -strongMEntropyCoefficient p uStar vStar *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  set c : ℝ := (2 * p.m - 1) * uStar ^ (2 * p.m - 1) with hcdef
  have hc : 0 ≤ c := by
    have h2m : (0 : ℝ) < 2 * p.m - 1 := by linarith
    exact mul_nonneg h2m.le (Real.rpow_pos_of_pos heq.u_pos _).le
  have hid := intervalDomainM_entropySlope_le_of_classical
    hm hsol ht0 htT heq
  have hyoung := intervalDomainM_entropyDiffusionChemotaxis_young
    (c := c) hc hsol ht0 htT
  have hell := intervalDomain_entropyElliptic_gradient_estimate_of_classical
    hsol ht0 htT heq
  have hpower := intervalDomain_powerDifference_integral_le_theta
    hsol ht0 htT heq.u_pos hrel
  have hfactor : 0 < 1 + betaTilde p.β * vStar := by
    have := mul_nonneg (betaTilde_nonneg p.β) heq.v_nonneg
    linarith
  have hscale : 0 ≤ p.χ₀ ^ 2 * c / 4 := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) hc) (by norm_num)
  have hell' :
      p.χ₀ ^ 2 * c / 4 *
          (∫ y in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) y) ^ 2 *
              (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)) ≤
        p.χ₀ ^ 2 * c / 4 *
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
      p.χ₀ ^ 2 * c / 4 *
        (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar))) := by
    have hden : 0 < 4 * p.μ * (1 + betaTilde p.β * vStar) := by
      exact mul_pos (mul_pos (by norm_num) p.hμ) hfactor
    exact mul_nonneg hscale (div_nonneg (sq_nonneg _) hden.le)
  calc
    intervalDomain.integral (fun x =>
        chemotaxisEntropyIntegrand p.m uStar (u t x) *
          intervalDomain.timeDeriv u t x) ≤
        -c * intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t +
          p.χ₀ * c *
            ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
              p (2 - 2 * p.m) u v t -
          p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      rw [hcdef]
      exact hid
    _ ≤ p.χ₀ ^ 2 * c / 4 *
          (∫ y in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) y) ^ 2 *
              (1 + intervalDomainLift (v t) y) ^ (-2 * p.β)) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      linarith
    _ ≤ p.χ₀ ^ 2 * c / 4 *
          (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      linarith
    _ ≤ p.χ₀ ^ 2 * c / 4 *
          (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)) *
            (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
              chemotaxisThetaDissipation intervalDomain uStar p.α (u t))) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      apply sub_le_sub_right
      calc
        p.χ₀ ^ 2 * c / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)) *
                (∫ y in (0 : ℝ)..1,
                  (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) =
            (p.χ₀ ^ 2 * c / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)))) *
              (∫ y in (0 : ℝ)..1,
                (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2) := by ring
        _ ≤ (p.χ₀ ^ 2 * c / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)))) *
              (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
                chemotaxisThetaDissipation intervalDomain uStar p.α (u t)) :=
          mul_le_mul_of_nonneg_left hpower hpowerScale
        _ = p.χ₀ ^ 2 * c / 4 *
              (p.ν ^ 2 / (4 * p.μ * (1 + betaTilde p.β * vStar)) *
                (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
                  chemotaxisThetaDissipation intervalDomain uStar p.α (u t))) := by
          ring
    _ = -strongMEntropyCoefficient p uStar vStar *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      have huPow :
          uStar ^ (2 * p.m - 1) * uStar ^ (2 * p.γ - p.α - 1) =
            uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) := by
        rw [← Real.rpow_add heq.u_pos]
        congr 1
        ring
      unfold strongMEntropyCoefficient
      rw [hcdef, ← huPow]
      field_simp [p.hμ.ne', hfactor.ne']
      ring

/-- The paper's first strict sensitivity threshold makes the exact general-`m`
entropy coefficient positive. -/
theorem strongMEntropyCoefficient_pos_of_chi_lt
    (p : CM2Params) {uStar vStar : ℝ}
    (hm : 1 ≤ p.m) (hb : 0 < p.b)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p uStar vStar) :
    0 < strongMEntropyCoefficient p uStar vStar := by
  let factor : ℝ := 1 + betaTilde p.β * vStar
  let upow : ℝ := uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)
  let source : ℝ :=
    (2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ * upow
  let scale : ℝ := 16 * factor * p.μ
  let R : ℝ := p.b * (scale / source)
  have hfactor : 0 < factor := by
    dsimp [factor]
    have hmul := mul_nonneg (betaTilde_nonneg p.β) hvStar
    linarith
  have hupow : 0 < upow := by
    exact Real.rpow_pos_of_pos huStar _
  have h2m : (0 : ℝ) < 2 * p.m - 1 := by linarith
  have hsource : 0 < source := by
    exact mul_pos (mul_pos (mul_pos h2m (sq_pos_of_pos p.hν))
      (CAlphaGamma_pos p.hα p.hγ)) hupow
  have hscale : 0 < scale := by
    exact mul_pos (mul_pos (by norm_num) hfactor) p.hμ
  have hR : 0 < R := mul_pos hb (div_pos hscale hsource)
  have hformula : chiStrong1Formula p uStar vStar = Real.sqrt R := by
    unfold chiStrong1Formula
    dsimp [R, scale, source, upow, factor]
  rw [hformula] at hχ
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hχsq : p.χ₀ ^ 2 < R := by
    nlinarith [Real.sqrt_nonneg R]
  have hχsource : p.χ₀ ^ 2 * source < p.b * scale := by
    apply (lt_div_iff₀ hsource).mp
    convert hχsq using 1 <;> dsimp [R] <;> field_simp [hsource.ne'] <;> ring
  have hquot : p.χ₀ ^ 2 * source / scale < p.b :=
    (div_lt_iff₀ hscale).2 (by simpa [mul_comm] using hχsource)
  unfold strongMEntropyCoefficient
  dsimp [source, scale, factor, upow] at hquot ⊢
  have hdenEq :
      16 * (1 + betaTilde p.β * vStar) * p.μ =
        16 * p.μ * (1 + betaTilde p.β * vStar) := by ring
  rw [hdenEq] at hquot
  apply sub_pos.mpr
  convert hquot using 1 <;> ring

#print axioms entropyCrossYoungM_pointwise
#print axioms intervalDomainM_entropyDiffusionChemotaxis_young
#print axioms intervalDomainM_entropySlope_le_strongMCoefficient
#print axioms strongMEntropyCoefficient_pos_of_chi_lt

end

end ShenWork.Paper3
