import ShenWork.Paper3.IntervalDomainPersistenceActualLinearTheta
import ShenWork.Paper2.IntervalDomainMChemDivCritical
import ShenWork.Paper2.IntervalDomainInteriorArgmin
import ShenWork.Paper2.IntervalDomainInteriorDeriv2
import ShenWork.Paper2.IntervalDomainC2Extraction

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMMinPersistence

namespace ShenWork.Paper3

noncomputable section

/-!
# Faithful general-m spatial-minimum reaction

The legacy interval persistence chain uses the flux `u * vₓ`.  The published
model instead uses `u^m * vₓ`, represented by `intervalDomainM`.  At a positive
spatial critical point, the already proved factorization
`chemDivM_at_critical` leaves the exact scalar loss

`χ₀ μ Θ_{β-1} u^m`.
-/

/-- The coefficient in the faithful general-`m` minimum equation. -/
def generalMChemLoss (p : CM2Params) : ℝ :=
  p.χ₀ * p.μ * Theta_beta (p.β - 1)

/-- Scalar vector field seen by a positive spatial minimum of the faithful
general-`m` equation. -/
def generalMLogisticRhs (p : CM2Params) (z : ℝ) : ℝ :=
  p.a * z - p.b * z ^ (1 + p.α) - generalMChemLoss p * z ^ p.m

/-- Interior critical-point estimate for the paper-faithful `u^m` flux. -/
theorem intervalDomain_generalM_minPoint_estimate
    {p : CM2Params} {u v : intervalDomain.Point → ℝ}
    {x : intervalDomain.Point} {vx vxx uxx uT : ℝ}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hux : HasDerivAt (intervalDomainLift u) 0 x.1)
    (hv : HasDerivAt (intervalDomainLift v) vx x.1)
    (hvxx : HasDerivAt (deriv (intervalDomainLift v)) vxx x.1)
    (hvnn : ∀ y, 0 ≤ intervalDomainLift v y)
    (hu_pos : 0 < intervalDomainLift u x.1) (huxx : 0 ≤ uxx)
    (hpdev : vxx =
      p.μ * intervalDomainLift v x.1 -
        p.ν * (intervalDomainLift u x.1) ^ p.γ)
    (hpdeu : uT =
      uxx - p.χ₀ * intervalDomainChemotaxisDivM p u v x +
        intervalDomainLift u x.1 *
          (p.a - p.b * (intervalDomainLift u x.1) ^ p.α)) :
    generalMLogisticRhs p (intervalDomainLift u x.1) ≤ uT := by
  set U : ℝ := intervalDomainLift u x.1
  set V : ℝ := intervalDomainLift v x.1
  have htheta := theta_linear_bound_public (p := p) hβ (hvnn x.1)
  have hcd := chemDivM_at_critical (p := p) hu_pos hux hv hvxx hvnn
  have hUγ_nonneg : 0 ≤ U ^ p.γ := Real.rpow_nonneg hu_pos.le _
  have hden_nonneg : 0 ≤ (1 + V) ^ (-p.β) :=
    Real.rpow_nonneg (by linarith [hvnn x.1] : 0 ≤ 1 + V) _
  have hterm_nonpos :
      -p.β * (1 + V) ^ (-p.β - 1) * vx ^ 2 ≤ 0 := by
    have hb : 0 ≤ p.β := zero_le_one.trans hβ
    have hp : 0 ≤ (1 + V) ^ (-p.β - 1) :=
      Real.rpow_nonneg (by linarith [hvnn x.1] : 0 ≤ 1 + V) _
    nlinarith [mul_nonneg hb hp, sq_nonneg vx]
  have hsecond :
      (1 + V) ^ (-p.β) * vxx ≤
        p.μ * Theta_beta (p.β - 1) := by
    rw [hpdev]
    have hdrop :
        (1 + V) ^ (-p.β) * (p.μ * V - p.ν * U ^ p.γ) ≤
          (1 + V) ^ (-p.β) * (p.μ * V) := by
      have hsub : p.μ * V - p.ν * U ^ p.γ ≤ p.μ * V := by
        have hnonneg : 0 ≤ p.ν * U ^ p.γ :=
          mul_nonneg p.hν.le hUγ_nonneg
        linarith
      exact mul_le_mul_of_nonneg_left hsub hden_nonneg
    have hpow_eq :
        (1 + V) ^ (-p.β) * (p.μ * V) =
          p.μ * (V / (1 + V) ^ p.β) := by
      rw [Real.rpow_neg
        (le_of_lt (by linarith [hvnn x.1] : 0 < 1 + V))]
      ring
    exact hdrop.trans (by
      rw [hpow_eq]
      exact mul_le_mul_of_nonneg_left htheta p.hμ.le)
  have hG :
      -p.β * (1 + V) ^ (-p.β - 1) * vx ^ 2 +
          (1 + V) ^ (-p.β) * vxx ≤
        p.μ * Theta_beta (p.β - 1) := by
    linarith
  have hUm_nonneg : 0 ≤ U ^ p.m := Real.rpow_nonneg hu_pos.le _
  have hcd_le :
      intervalDomainChemotaxisDivM p u v x ≤
        U ^ p.m * (p.μ * Theta_beta (p.β - 1)) := by
    rw [hcd]
    exact mul_le_mul_of_nonneg_left hG hUm_nonneg
  have hchem :
      -p.χ₀ * intervalDomainChemotaxisDivM p u v x ≥
        -p.χ₀ *
          (U ^ p.m * (p.μ * Theta_beta (p.β - 1))) :=
    mul_le_mul_of_nonpos_left hcd_le (by linarith : -p.χ₀ ≤ 0)
  have hpow : U * (p.b * U ^ p.α) = p.b * U ^ (1 + p.α) := by
    rw [Real.rpow_add_of_nonneg hu_pos.le
      (by norm_num : 0 ≤ (1 : ℝ)) p.hα.le]
    rw [Real.rpow_one]
    ring
  rw [hpdeu]
  simp only [generalMLogisticRhs, generalMChemLoss]
  nlinarith [huxx, hchem, hpow]

private theorem lift_eq_interior (f : intervalDomain.Point → ℝ)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    intervalDomainLift f y = f ⟨y, Set.Ioo_subset_Icc_self hy⟩ := by
  rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hy)]

/-- Interior spatial-argmin slope bound for a faithful general-`m` classical
solution. -/
theorem intervalDomain_generalM_interior_min_point_of_solution
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ} {x : intervalDomain.Point}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : ShenWork.Paper2.IsPaper2ClassicalSolution
      intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hmin : ∀ y, u t x ≤ u t y) :
    generalMLogisticRhs p (u t x) ≤
      intervalDomainM.timeDeriv u t x := by
  open ShenWork.MinPersistenceAtoms in
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, _, _, _, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u t))
      (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t))
      (Set.Ioo (0 : ℝ) 1) := (hC2 t htmem).2
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hux := interior_argmin_deriv_zero hmin hint
    ((contDiffOn_two_hasDerivAt_pair
      isOpen_Ioo hu_c2 hint).1.differentiableAt)
  have hvpair := contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hint
  have huxx := interior_argmin_deriv2_nonneg hmin hint hu_c2
  have hux_lift : intervalDomainLift (u t) x.1 = u t x := by
    rw [lift_eq_interior (u t) hint]
    exact congrArg (u t) (Subtype.ext rfl)
  have hu_pos : 0 < intervalDomainLift (u t) x.1 := by
    rw [hux_lift]
    exact hsol.u_pos' ht0 htT
  have hpdev : deriv (deriv (intervalDomainLift (v t))) x.1 =
      p.μ * intervalDomainLift (v t) x.1 -
        p.ν * (intervalDomainLift (u t) x.1) ^ p.γ := by
    have hpv := ShenWork.Paper2.IsPaper2ClassicalSolution.pde_v
      (D := intervalDomainM) hsol ht0 htT
      (x := x) (by simpa [intervalDomainM] using hint)
    have hlap : intervalDomainM.laplacian (v t) x =
        deriv (deriv (intervalDomainLift (v t))) x.1 := rfl
    have hv_lift : intervalDomainLift (v t) x.1 = v t x := by
      rw [lift_eq_interior (v t) hint]
      exact congrArg (v t) (Subtype.ext rfl)
    rw [hlap, ← hux_lift, ← hv_lift] at hpv
    linarith [hpv]
  have hpdeu : intervalDomainM.timeDeriv u t x =
      deriv (deriv (intervalDomainLift (u t))) x.1 -
        p.χ₀ * intervalDomainChemotaxisDivM p (u t) (v t) x +
          intervalDomainLift (u t) x.1 *
            (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) := by
    rw [hux_lift]
    exact ShenWork.Paper2.IsPaper2ClassicalSolution.pde_u
      (D := intervalDomainM) hsol ht0 htT
        (by simpa [intervalDomainM] using hint)
  have hmain := intervalDomain_generalM_minPoint_estimate
    (p := p) (u := u t) (v := v t) (x := x)
    (vx := deriv (intervalDomainLift (v t)) x.1)
    (vxx := deriv (deriv (intervalDomainLift (v t))) x.1)
    (uxx := deriv (deriv (intervalDomainLift (u t))) x.1)
    (uT := intervalDomainM.timeDeriv u t x)
    hχ0 hβ hux hvpair.1 hvpair.2 hv_nn hu_pos huxx hpdev hpdeu
  rwa [hux_lift] at hmain

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomain_generalM_minPoint_estimate
#print axioms
  ShenWork.Paper3.intervalDomain_generalM_interior_min_point_of_solution
