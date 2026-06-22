import ShenWork.Paper3.IntervalDomainPersistenceDiniFrontier
import ShenWork.Paper2.Statements
open ShenWork.IntervalDomain
open ShenWork.Paper2
namespace ShenWork.Paper3
noncomputable section
def actualLinearChemLoss (p : CM2Params) : ℝ :=
  p.χ₀ * p.μ * Theta_beta (p.β - 1)
def actualLinearLogisticRhs (p : CM2Params) (z : ℝ) : ℝ :=
  (p.a - actualLinearChemLoss p) * z - p.b * z ^ (1 + p.α)
private theorem theta_linear_bound {p : CM2Params} {V : ℝ}
    (hβ : 1 ≤ p.β) (hV : 0 ≤ V) :
    V / (1 + V) ^ p.β ≤ Theta_beta (p.β - 1) := by
  have hb_nonneg : 0 ≤ p.β - 1 := by linarith
  rcases lt_or_eq_of_le hb_nonneg with hbpos | hbzero
  · by_cases hV0 : V = 0
    · subst hV0
      simp [Theta_beta_nonneg hb_nonneg]
    · have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
      have h := Lemma_2_5_normalized_Theta_bound
        (beta := p.β - 1) hbpos (v := V) hVpos
      simpa [show 1 + (p.β - 1) = p.β by ring] using h
  · have hpβ : p.β = 1 := by linarith
    rw [hpβ, show (1 : ℝ) - 1 = 0 by ring, Theta_beta_zero]
    have hpos : 0 < 1 + V := by linarith
    rw [Real.rpow_one, div_le_iff₀ hpos]
    linarith
theorem intervalDomain_actual_linear_minPoint_estimate
    {p : CM2Params} {u v : intervalDomain.Point → ℝ}
    {x : intervalDomain.Point} {vx vxx uxx uT : ℝ}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y)
    (hu_nonneg : 0 ≤ intervalDomainLift u x.1) (huxx : 0 ≤ uxx)
    (hpdev : vxx =
      p.μ * intervalDomainLift v x.1 -
        p.ν * (intervalDomainLift u x.1) ^ p.γ)
    (hpdeu : uT =
      uxx - p.χ₀ * intervalDomainChemotaxisDiv p u v x +
        intervalDomainLift u x.1 *
          (p.a - p.b * (intervalDomainLift u x.1) ^ p.α)) :
    actualLinearLogisticRhs p (intervalDomainLift u x.1) ≤ uT := by
  set U := intervalDomainLift u x.1
  set V := intervalDomainLift v x.1
  have htheta := theta_linear_bound (p := p) hβ (by exact hvnn x.1)
  have hcd := intervalDomain_chemDiv_critical_linear_factor
    (p := p) hux hv hvxx hvnn
  have hUγ_nonneg : 0 ≤ U ^ p.γ := Real.rpow_nonneg hu_nonneg _
  have hden_nonneg : 0 ≤ (1 + V) ^ (-p.β) :=
    Real.rpow_nonneg (by linarith [hvnn x.1] : 0 ≤ 1 + V) _
  have hterm_nonpos :
      -p.β * (1 + V) ^ (-p.β - 1) * vx ^ 2 ≤ 0 := by
    have hb : 0 ≤ p.β := le_trans (by norm_num) hβ
    have hp : 0 ≤ (1 + V) ^ (-p.β - 1) :=
      Real.rpow_nonneg (by linarith [hvnn x.1] : 0 ≤ 1 + V) _
    nlinarith [mul_nonneg hb hp, sq_nonneg vx]
  have hsecond :
      (1 + V) ^ (-p.β) * vxx ≤ p.μ * Theta_beta (p.β - 1) := by
    rw [hpdev]
    have hdrop :
        (1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ) ≤
          (1 + V) ^ (-p.β) * (p.μ * V) := by
      have hsub : p.μ * V - p.ν * U ^ p.γ ≤ p.μ * V := by
        have : 0 ≤ p.ν * U ^ p.γ := mul_nonneg p.hν.le hUγ_nonneg
        linarith
      exact mul_le_mul_of_nonneg_left hsub hden_nonneg
    have hpow_eq : (1 + V) ^ (-p.β) * (p.μ * V) =
        p.μ * (V / (1 + V) ^ p.β) := by
      rw [Real.rpow_neg (le_of_lt (by linarith [hvnn x.1] : 0 < 1 + V))]
      ring
    calc (1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ)
        ≤ (1 + V) ^ (-p.β) * (p.μ * V) := hdrop
      _ = p.μ * (V / (1 + V) ^ p.β) := hpow_eq
      _ ≤ p.μ * Theta_beta (p.β - 1) :=
        mul_le_mul_of_nonneg_left htheta p.hμ.le
  have hG : -p.β * (1 + V) ^ (-p.β - 1) * vx ^ 2 +
      (1 + V) ^ (-p.β) * vxx ≤ p.μ * Theta_beta (p.β - 1) := by
    linarith
  have hcd_le : intervalDomainChemotaxisDiv p u v x ≤
      U * (p.μ * Theta_beta (p.β - 1)) := by
    rw [hcd]
    exact mul_le_mul_of_nonneg_left hG hu_nonneg
  have hchem : -p.χ₀ * intervalDomainChemotaxisDiv p u v x ≥
      -p.χ₀ * (U * (p.μ * Theta_beta (p.β - 1))) :=
    mul_le_mul_of_nonpos_left hcd_le (by linarith : -p.χ₀ ≤ 0)
  have hpow : U * (p.b * U ^ p.α) = p.b * U ^ (1 + p.α) := by
    rw [Real.rpow_add_of_nonneg hu_nonneg (by norm_num : 0 ≤ (1 : ℝ)) p.hα.le]
    rw [Real.rpow_one]
    ring
  rw [hpdeu]
  simp only [actualLinearLogisticRhs, actualLinearChemLoss]
  nlinarith [huxx, hchem, hpow]
end
end ShenWork.Paper3
#print axioms ShenWork.Paper3.intervalDomain_actual_linear_minPoint_estimate
