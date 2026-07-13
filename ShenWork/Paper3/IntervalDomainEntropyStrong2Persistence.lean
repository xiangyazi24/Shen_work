import ShenWork.Paper3.IntervalDomainPersistenceActualLinearPart2Proved
import ShenWork.Paper3.IntervalDomainEntropyStrong1Global

/-!
# Concrete persistence input for the second strong-logistic branch

For `m = 1`, the `chiStrong2Formula` threshold lies below `chiBarFormula`.
The proved actual-linear minimum inequality then places the eventual signal
strictly above `vABLowerFormula`.  This file derives that pointwise lower
barrier directly from the PDE persistence producer; no persistence package
field is used.
-/

namespace ShenWork.Paper3

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- Nonnegativity of the elliptic signal gives the lower-boundedness input
needed by the liminf API. -/
theorem intervalDomain_infValue_v_isBoundedUnder_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    IsBoundedUnder GE.ge atTop (fun t => intervalDomain.infValue (v t)) := by
  have hfloor : ∀ᶠ t in atTop, 0 ≤ intervalDomain.infValue (v t) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hT : 0 < t + 1 := by linarith
    have hsol := huv.classical (t + 1) hT
    change 0 ≤ sInf (Set.range (v t))
    apply le_csInf
    · exact ⟨v t ⟨0, ⟨by norm_num, by norm_num⟩⟩,
        ⟨⟨0, ⟨by norm_num, by norm_num⟩⟩, rfl⟩⟩
    · rintro y ⟨x, rfl⟩
      exact hsol.v_nonneg ht0 (by linarith) (x := x)
  exact isBoundedUnder_of_eventually_ge hfloor

/-- Under the half-logistic `chiBar` threshold, the actual-linear signal
lower value is strictly larger than `vABLowerFormula`. -/
theorem vABLowerFormula_lt_part2SignalLower
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 1 ≤ p.β)
    (hχpos : 0 < p.χ₀)
    (hχbar : p.χ₀ < chiBarFormula p) :
    vABLowerFormula p <
      p.ν / p.μ * theorem21Part2LowerU p ^ p.γ := by
  let theta : ℝ := Theta_beta (p.β - 1)
  have htheta : 0 < theta := by
    exact Theta_beta_pos_of_nonneg (by linarith)
  have hχhalf : p.χ₀ < p.a / (2 * p.μ * theta) := by
    unfold chiBarFormula at hχbar
    rw [if_pos hm] at hχbar
    simpa [theta] using hχbar
  have hdenHalf : 0 < 2 * p.μ * theta :=
    mul_pos (mul_pos (by norm_num) p.hμ) htheta
  have htwoloss : p.χ₀ * (2 * p.μ * theta) < p.a :=
    (lt_div_iff₀ hdenHalf).mp hχhalf
  have hloss : p.χ₀ * p.μ * theta < p.a / 2 := by
    nlinarith
  let base0 : ℝ := p.a / (2 * p.b)
  let base1 : ℝ :=
    (p.a - p.χ₀ * p.μ * theta) / p.b
  have hbase0 : 0 < base0 := div_pos ha (mul_pos (by norm_num) hb)
  have hbase : base0 < base1 := by
    dsimp [base0, base1]
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) hb) hb]
    nlinarith
  have hexp : 0 < 1 / p.α := one_div_pos.mpr p.hα
  have hroot : base0 ^ (1 / p.α) < base1 ^ (1 / p.α) :=
    Real.rpow_lt_rpow hbase0.le hbase hexp
  have hrootGamma :
      (base0 ^ (1 / p.α)) ^ p.γ <
        (base1 ^ (1 / p.α)) ^ p.γ :=
    Real.rpow_lt_rpow (Real.rpow_nonneg hbase0.le _) hroot p.hγ
  have hscale : 0 < p.ν / p.μ := div_pos p.hν p.hμ
  have hscaled := mul_lt_mul_of_pos_left hrootGamma hscale
  have hbasePow :
      base0 ^ (p.γ / p.α) = (base0 ^ (1 / p.α)) ^ p.γ := by
    rw [← Real.rpow_mul hbase0.le]
    congr 1
    field_simp [p.hα.ne']
  have hlowerRoot : theorem21Part2LowerU p = base1 ^ (1 / p.α) := by
    simp [theorem21Part2LowerU, base1, theta]
  unfold vABLowerFormula
  rw [if_pos hm, hbasePow, hlowerRoot]
  exact hscaled

/-- The half-logistic `chiBar` threshold alone yields the concrete eventual
pointwise signal floor.  This is the common persistence input for the second
and fourth strict formula branches. -/
theorem intervalDomain_eventually_vABLower_of_chi_lt_chiBar
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 1 ≤ p.β)
    (hχpos : 0 < p.χ₀)
    (hχbar : p.χ₀ < chiBarFormula p)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∀ᶠ t in atTop, ∀ x : intervalDomainPoint,
      vABLowerFormula p ≤ v t x := by
  let theta : ℝ := Theta_beta (p.β - 1)
  have htheta : 0 < theta :=
    Theta_beta_pos_of_nonneg (by linarith)
  have hχhalf : p.χ₀ < p.a / (2 * p.μ * theta) := by
    unfold chiBarFormula at hχbar
    rw [if_pos hm] at hχbar
    simpa [theta] using hχbar
  have hden : 0 < p.μ * theta := mul_pos p.hμ htheta
  have hχpersistence : p.χ₀ < p.a / (p.μ * theta) := by
    have hmul : p.χ₀ * (2 * (p.μ * theta)) < p.a := by
      have hden2 : 0 < 2 * p.μ * theta :=
        mul_pos (mul_pos (by norm_num) p.hμ) htheta
      have := (lt_div_iff₀ hden2).mp hχhalf
      simpa [mul_assoc] using this
    apply (lt_div_iff₀ hden).2
    nlinarith [mul_pos hχpos hden]
  have hvlim :=
    (intervalDomain_part2_liminfUV_proven
      ha hb hχpos hm hβ (by simpa [theta] using hχpersistence)
      huv (by norm_num : 0 < (1 : ℝ))).2
  have hvstrict : vABLowerFormula p < liminfInfValue intervalDomain v :=
    (vABLowerFormula_lt_part2SignalLower
      p hm ha hb hβ hχpos hχbar).trans_le hvlim
  have hevInf : ∀ᶠ t in atTop,
      vABLowerFormula p < intervalDomain.infValue (v t) :=
    eventually_lt_of_lt_liminf hvstrict
      (intervalDomain_infValue_v_isBoundedUnder_of_positiveGlobalBoundedSolution huv)
  have hvABpos : 0 < vABLowerFormula p :=
    vABLowerFormula_pos p ha hb (by rw [hm])
  exact intervalDomain_eventually_pointwise_lower_of_eventuallyLowerBound
    ⟨hvABpos, hevInf.mono (fun _ ht => ht.le)⟩

/-- The second strict formula branch yields the concrete eventual pointwise
signal floor used in its entropy estimate. -/
theorem intervalDomain_strong2_eventually_vABLower
    (p : CM2Params) (hm : p.m = 1)
    (ha : 0 < p.a) (hb : 0 < p.b) (hβ : 1 ≤ p.β)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong2Formula p
      (positiveEquilibrium p ⟨ha, hb⟩).1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∀ᶠ t in atTop, ∀ x : intervalDomainPoint,
      vABLowerFormula p ≤ v t x := by
  exact intervalDomain_eventually_vABLower_of_chi_lt_chiBar
    p hm ha hb hβ hχpos
      (chi_lt_chiBarFormula_of_lt_chiStrong2Formula p hχ) huv

#print axioms
  intervalDomain_infValue_v_isBoundedUnder_of_positiveGlobalBoundedSolution
#print axioms vABLowerFormula_lt_part2SignalLower
#print axioms intervalDomain_eventually_vABLower_of_chi_lt_chiBar
#print axioms intervalDomain_strong2_eventually_vABLower

end

end ShenWork.Paper3
