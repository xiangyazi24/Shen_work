import ShenWork.Paper3.IntervalDomainEntropyStrong2Persistence

/-!
# Concrete entropy dissipation in the second strong-logistic branch

After the proved signal persistence floor is available, the chemotactic
weight is bounded by `(1 + vABLowerFormula p)^(-2*beta)`.  The ordinary
Neumann elliptic multiplier estimate and the same power-difference lemma as
in branch one then give the exact `chiStrong2Formula` coefficient.
-/

namespace ShenWork.Paper3

open MeasureTheory Set
open scoped Topology Interval
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep

noncomputable section

/-- Ordinary elliptic Neumann gradient estimate, obtained by specializing the
proved weighted multiplier to exponent zero. -/
theorem intervalDomain_unweightedElliptic_gradient_estimate_of_classical
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    (∫ x in (0 : ℝ)..1,
        (deriv (intervalDomainLift (v t)) x) ^ 2) ≤
      p.ν ^ 2 / (4 * p.μ) *
        (∫ x in (0 : ℝ)..1,
          (intervalDomainLift (u t) x ^ p.γ - uStar ^ p.γ) ^ 2) := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hUcont : ContinuousOn U (Set.Icc (0 : ℝ) 1) := by
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol ht
  have hUpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < U x := by
    intro x hx
    simpa [U] using
      ShenWork.Paper2.IntervalDomainM.solution_lift_pos_Icc hsol ht x hx
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using
      ShenWork.Paper2.IntervalDomainM.deriv_v_continuousOn_Icc hsol ht0 htT
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    intro x hx
    simpa [V, intervalDomainLift, hx] using
      hsol.v_nonneg (x := (⟨x, hx⟩ : intervalDomainPoint)) ht0 htT
  have hVxx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv V) x = p.μ * V x - p.ν * U x ^ p.γ := by
    intro x hx
    simpa [V, U] using
      ShenWork.Paper2.IntervalDomainM.v_xx_eq_reaction_lift
        hsol ht0 htT hx.1 hx.2
  have hNeu0 : deriv V 0 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.1
  have hNeu1 : deriv V 1 = 0 := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.2.2
  have hstatic := interval_entropyElliptic_gradient_estimate
    p.hμ p.hν (show (0 : ℝ) ≤ 0 by norm_num) p.hγ
    heq.u_pos heq.v_nonneg hUcont hUpos hV2 hdVcont hVnonneg
    hVxx hNeu0 hNeu1 heq.elliptic_relation
  simpa [U, V, betaTilde_eq_zero_of_beta_le_half
      (show (0 : ℝ) ≤ 1 / 2 by norm_num), Real.rpow_zero] using hstatic

/-- A pointwise signal floor converts the weighted gradient into the ordinary
gradient with the sharp constant floor weight. -/
theorem intervalDomain_weightedGradient_le_of_signalFloor
    {p : CM2Params} {T t floor : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hfloor : 0 ≤ floor)
    (hVfloor : ∀ x : intervalDomainPoint, floor ≤ v t x) :
    (∫ x in (0 : ℝ)..1,
        (deriv (intervalDomainLift (v t)) x) ^ 2 *
          (1 + intervalDomainLift (v t) x) ^ (-2 * p.β)) ≤
      (1 + floor) ^ (-2 * p.β) *
        (∫ x in (0 : ℝ)..1,
          (deriv (intervalDomainLift (v t)) x) ^ 2) := by
  let V : ℝ → ℝ := intervalDomainLift (v t)
  have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hV2 : ContDiffOn ℝ 2 V (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using (hsol.regularity.2.2.2.2.1 t ht).2.1
  have hdVcont : ContinuousOn (deriv V) (Set.Icc (0 : ℝ) 1) := by
    simpa [V] using
      ShenWork.Paper2.IntervalDomainM.deriv_v_continuousOn_Icc hsol ht0 htT
  have hVcont : ContinuousOn V (Set.Icc (0 : ℝ) 1) := hV2.continuousOn
  have hVnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ V x := by
    intro x hx
    simpa [V, intervalDomainLift, hx] using
      hsol.v_nonneg (x := (⟨x, hx⟩ : intervalDomainPoint)) ht0 htT
  have hbase : 0 < 1 + floor := by linarith
  have hweightCont : ContinuousOn
      (fun x => (deriv V x) ^ 2 * (1 + V x) ^ (-2 * p.β))
      (Set.Icc (0 : ℝ) 1) :=
    (hdVcont.pow 2).mul
      ((continuousOn_const.add hVcont).rpow_const
        (fun x hx => Or.inl (by
          simpa only [Pi.add_apply] using
            (ne_of_gt (show 0 < 1 + V x by linarith [hVnonneg x hx])))))
  have hgradCont : ContinuousOn (fun x => (deriv V x) ^ 2)
      (Set.Icc (0 : ℝ) 1) := hdVcont.pow 2
  have hweightInt : IntervalIntegrable
      (fun x => (deriv V x) ^ 2 * (1 + V x) ^ (-2 * p.β))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hweightCont
  have hgradInt : IntervalIntegrable (fun x => (deriv V x) ^ 2)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le zero_le_one] using hgradCont
  calc
    (∫ x in (0 : ℝ)..1,
        (deriv V x) ^ 2 * (1 + V x) ^ (-2 * p.β)) ≤
      ∫ x in (0 : ℝ)..1,
        (1 + floor) ^ (-2 * p.β) * (deriv V x) ^ 2 := by
      exact intervalIntegral.integral_mono_on (by norm_num) hweightInt
        (hgradInt.const_mul ((1 + floor) ^ (-2 * p.β)))
        (fun x hx => by
          have hxval : floor ≤ V x := by
            simpa [V, intervalDomainLift, hx] using
              hVfloor (⟨x, hx⟩ : intervalDomainPoint)
          have hw := Real.rpow_le_rpow_of_nonpos hbase
            (by linarith : 1 + floor ≤ 1 + V x)
            (by nlinarith [p.hβ] : -2 * p.β ≤ 0)
          nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg (deriv V x))])
    _ = (1 + floor) ^ (-2 * p.β) *
          (∫ x in (0 : ℝ)..1, (deriv V x) ^ 2) := by
      rw [intervalIntegral.integral_const_mul]

/-- Combined persistent-weight and ordinary elliptic estimate. -/
theorem intervalDomain_persistentWeightedElliptic_gradient_estimate
    {p : CM2Params} {T t uStar vStar floor : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hfloor : 0 ≤ floor)
    (hVfloor : ∀ x : intervalDomainPoint, floor ≤ v t x) :
    (∫ x in (0 : ℝ)..1,
        (deriv (intervalDomainLift (v t)) x) ^ 2 *
          (1 + intervalDomainLift (v t) x) ^ (-2 * p.β)) ≤
      p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β)) *
        (∫ x in (0 : ℝ)..1,
          (intervalDomainLift (u t) x ^ p.γ - uStar ^ p.γ) ^ 2) := by
  have hw := intervalDomain_weightedGradient_le_of_signalFloor
    hsol ht0 htT hfloor hVfloor
  have hell := intervalDomain_unweightedElliptic_gradient_estimate_of_classical
    hsol ht0 htT heq
  have hweightNonneg : 0 ≤ (1 + floor) ^ (-2 * p.β) :=
    Real.rpow_nonneg (by linarith : 0 ≤ 1 + floor) _
  have hscaled := mul_le_mul_of_nonneg_left hell hweightNonneg
  calc
    _ ≤ (1 + floor) ^ (-2 * p.β) *
          (∫ x in (0 : ℝ)..1,
            (deriv (intervalDomainLift (v t)) x) ^ 2) := hw
    _ ≤ (1 + floor) ^ (-2 * p.β) *
          (p.ν ^ 2 / (4 * p.μ) *
            (∫ x in (0 : ℝ)..1,
              (intervalDomainLift (u t) x ^ p.γ - uStar ^ p.γ) ^ 2)) := hscaled
    _ = p.ν ^ 2 / (4 * p.μ * (1 + floor) ^ (2 * p.β)) *
          (∫ x in (0 : ℝ)..1,
            (intervalDomainLift (u t) x ^ p.γ - uStar ^ p.γ) ^ 2) := by
      have hbase : 0 < 1 + floor := by linarith
      rw [show -2 * p.β = -(2 * p.β) by ring,
        Real.rpow_neg hbase.le]
      field_simp [p.hμ.ne', (Real.rpow_pos_of_pos hbase (2 * p.β)).ne']

/-- Exact entropy-production coefficient in the implemented second strong
logistic branch. -/
def strong2EntropyCoefficient
    (p : CM2Params) (uStar : ℝ) : ℝ :=
  p.b -
    p.χ₀ ^ 2 * p.ν ^ 2 * CAlphaGamma p.α p.γ *
        uStar ^ (2 * p.γ - p.α) /
      (16 * p.μ * (1 + vABLowerFormula p) ^ (2 * p.β))

/-- Entropy dissipation inequality at every slice on which the proved signal
floor is available. -/
theorem intervalDomain_entropySlope_le_strong2Coefficient
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : p.m = 1)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hrel : 2 * p.γ ≤ p.α + 1)
    (hvAB : 0 ≤ vABLowerFormula p)
    (hVfloor : ∀ x : intervalDomainPoint, vABLowerFormula p ≤ v t x) :
    intervalDomain.integral (fun x =>
        (1 - uStar / u t x) * intervalDomain.timeDeriv u t x) ≤
      -strong2EntropyCoefficient p uStar *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
  let hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  have hid := intervalDomain_entropySlope_identity hm hsol ht0 htT heq
  have hyoung := intervalDomain_entropyDiffusionChemotaxis_young
    hm hsolM ht0 htT heq.u_pos
  have hell := intervalDomain_persistentWeightedElliptic_gradient_estimate
    hsolM ht0 htT heq hvAB hVfloor
  have hpower := intervalDomain_powerDifference_integral_le_theta
    hsolM ht0 htT heq.u_pos hrel
  have hden : 0 < 16 * p.μ *
      (1 + vABLowerFormula p) ^ (2 * p.β) := by
    exact mul_pos (mul_pos (by norm_num) p.hμ)
      (Real.rpow_pos_of_pos (by linarith) _)
  have hscale : 0 ≤ p.χ₀ ^ 2 * uStar / 4 :=
    div_nonneg (mul_nonneg (sq_nonneg _) heq.u_pos.le) (by norm_num)
  have hell' := mul_le_mul_of_nonneg_left hell hscale
  have hpowerScale : 0 ≤ p.χ₀ ^ 2 * uStar / 4 *
      (p.ν ^ 2 /
        (4 * p.μ * (1 + vABLowerFormula p) ^ (2 * p.β))) := by
    have hden4 : 0 < 4 * p.μ *
        (1 + vABLowerFormula p) ^ (2 * p.β) :=
      mul_pos (mul_pos (by norm_num) p.hμ)
        (Real.rpow_pos_of_pos (by linarith) _)
    exact mul_nonneg hscale (div_nonneg (sq_nonneg _) hden4.le)
  have huPow : uStar * uStar ^ (2 * p.γ - p.α - 1) =
      uStar ^ (2 * p.γ - p.α) := by
    calc
      uStar * uStar ^ (2 * p.γ - p.α - 1) =
          uStar ^ (1 : ℝ) * uStar ^ (2 * p.γ - p.α - 1) := by
        rw [Real.rpow_one]
      _ = uStar ^ ((1 : ℝ) + (2 * p.γ - p.α - 1)) := by
        rw [← Real.rpow_add heq.u_pos]
      _ = uStar ^ (2 * p.γ - p.α) := by congr 1 <;> ring
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
          (p.ν ^ 2 /
              (4 * p.μ * (1 + vABLowerFormula p) ^ (2 * p.β)) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      linarith
    _ ≤ p.χ₀ ^ 2 * uStar / 4 *
          (p.ν ^ 2 /
              (4 * p.μ * (1 + vABLowerFormula p) ^ (2 * p.β)) *
            (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
              chemotaxisThetaDissipation intervalDomain uStar p.α (u t))) -
        p.b * chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      apply sub_le_sub_right
      calc
        p.χ₀ ^ 2 * uStar / 4 *
            (p.ν ^ 2 /
                (4 * p.μ * (1 + vABLowerFormula p) ^ (2 * p.β)) *
              (∫ y in (0 : ℝ)..1,
                (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2)) =
          (p.χ₀ ^ 2 * uStar / 4 *
            (p.ν ^ 2 /
              (4 * p.μ * (1 + vABLowerFormula p) ^ (2 * p.β)))) *
            (∫ y in (0 : ℝ)..1,
              (intervalDomainLift (u t) y ^ p.γ - uStar ^ p.γ) ^ 2) := by ring
        _ ≤ (p.χ₀ ^ 2 * uStar / 4 *
            (p.ν ^ 2 /
              (4 * p.μ * (1 + vABLowerFormula p) ^ (2 * p.β)))) *
            (CAlphaGamma p.α p.γ * uStar ^ (2 * p.γ - p.α - 1) *
              chemotaxisThetaDissipation intervalDomain uStar p.α (u t)) :=
          mul_le_mul_of_nonneg_left hpower hpowerScale
        _ = _ := by ring
    _ = -strong2EntropyCoefficient p uStar *
        chemotaxisThetaDissipation intervalDomain uStar p.α (u t) := by
      unfold strong2EntropyCoefficient
      rw [← huPow]
      field_simp [p.hμ.ne',
        (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vABLowerFormula p)
          (2 * p.β)).ne']
      ring

#print axioms intervalDomain_unweightedElliptic_gradient_estimate_of_classical
#print axioms intervalDomain_weightedGradient_le_of_signalFloor
#print axioms intervalDomain_persistentWeightedElliptic_gradient_estimate
#print axioms intervalDomain_entropySlope_le_strong2Coefficient

end

end ShenWork.Paper3
