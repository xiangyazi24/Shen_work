import ShenWork.Paper3.IntervalDomainMEntropyStrongDissipation
import ShenWork.Paper3.IntervalDomainEntropyStrong2
import ShenWork.Paper3.IntervalDomainMinimalPowerDifference
import ShenWork.Paper3.IntervalDomainMinimalPoincare

/-!
# M-native minimal-model entropy dissipation (minimal1 branch, general `1 ≤ m < 2`)

This mirrors the `m = 1` file `IntervalDomainMinimalEntropy.lean` on the faithful
`u^m`-flux domain `intervalDomainM`.  The χ₀>0 minimal equilibrium (`a = b = 0`)
has no logistic sign to spend, so instead of the full Young absorption used in
the strong branches we keep *half* of the general-`m` gradient dissipation and
convert it, through the conserved mass, into an `L²` distance (mass-Poincaré at
weight `2 − 2m`).  The retained fraction dominates the chemotactic term below the
`minimal1` threshold.
-/

open Filter MeasureTheory Set Topology
open scoped Topology Interval

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

/-- **Step 1 (pointwise).** Half-split Young inequality in the general-`m`
entropy weights: keep half the gradient dissipation `A² = U^(2−2m−2)·ux²`, pay
the signal energy `B² = vx²·(1+V)^(−2β)` at coefficient `χ²c/2`.  The residual
square is `(A − χ·B)²`. -/
theorem entropyCrossHalfYoungM_pointwise
    {m c chi beta U V ux vx : ℝ}
    (hc : 0 ≤ c) (hU : 0 < U) (hV : 0 ≤ V) :
    -c * (U ^ ((2 - 2 * m) - 2) * ux ^ 2) +
        chi * c *
          (U ^ ((2 - 2 * m) + m - 2) * ux * vx / (1 + V) ^ beta) ≤
      -(c / 2) * (U ^ ((2 - 2 * m) - 2) * ux ^ 2) +
      chi ^ 2 * c / 2 *
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
  nlinarith [mul_nonneg hc (sq_nonneg (A - chi * B))]

/-- **Step 1 (integrated).** Half-split Young absorption of the general-`m`
diffusion and chemotaxis terms in the entropy slope, retaining half the weighted
gradient dissipation.  Mirror of `intervalDomainM_entropyDiffusionChemotaxis_young`
with the split constant. -/
theorem intervalDomainM_entropyDiffusionChemotaxis_half_young
    {p : CM2Params} {T t c : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hc : 0 ≤ c)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T) :
    -c * intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t +
        p.χ₀ * c *
          ShenWork.Paper2.IntervalDomainM.lpSignedCrossIntegralM
            p (2 - 2 * p.m) u v t ≤
      -(c / 2) *
          intervalDomainLpWeightedGradientDissipation (2 - 2 * p.m) u t +
      p.χ₀ ^ 2 * c / 2 *
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
    -(c / 2) * (∫ y in (0 : ℝ)..1, g y) +
      p.χ₀ ^ 2 * c / 2 * (∫ y in (0 : ℝ)..1, rterm y)
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
          -(c / 2) * g y + p.χ₀ ^ 2 * c / 2 * rterm y := by
      exact intervalIntegral.integral_mono_on (by norm_num)
        ((hgint.const_mul (-c)).add
          (hxint.const_mul (p.χ₀ * c)))
        ((hgint.const_mul (-(c / 2))).add
          (hrint.const_mul (p.χ₀ ^ 2 * c / 2)))
        (fun y hy => by
          exact entropyCrossHalfYoungM_pointwise hc (hUpos y hy) (hVnonneg y hy))
    _ = -(c / 2) * (∫ y in (0 : ℝ)..1, g y) +
          p.χ₀ ^ 2 * c / 2 * (∫ y in (0 : ℝ)..1, rterm y) := by
      rw [intervalIntegral.integral_add (hgint.const_mul (-(c / 2)))
          (hrint.const_mul (p.χ₀ ^ 2 * c / 2)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

#print axioms entropyCrossHalfYoungM_pointwise
#print axioms intervalDomainM_entropyDiffusionChemotaxis_half_young

end

end ShenWork.Paper3
