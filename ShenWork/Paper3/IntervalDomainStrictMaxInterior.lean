import ShenWork.Paper3.IntervalDomainSolutionPowerResolverGap
import ShenWork.Paper2.IntervalDomainMaxPointSolution

open ShenWork.IntervalDomain ShenWork.Paper2 ShenWork.MinPersistenceAtoms
open ShenWork.MaxPrincipleAtoms
open Set

namespace ShenWork.Paper3

noncomputable section

/- At an interior spatial maximum, a quantitative elliptic signal gap is
retained as a strictly dissipative chemotaxis term. -/
theorem intervalDomain_interior_max_point_strict_signal
    {p : CM2Params} {T t q : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    {x : intervalDomainPoint}
    (hχ : p.χ₀ ≤ 0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hint : x.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hmax : ∀ y, u t y ≤ u t x)
    (hsignal : q ≤
      p.ν * (intervalDomainLift (u t) x.1) ^ p.γ / p.μ -
        intervalDomainLift (v t) x.1) :
    intervalDomain.timeDeriv u t x ≤
      intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) +
        p.χ₀ *
          (intervalDomainLift (u t) x.1 *
            ((1 + intervalDomainLift (v t) x.1) ^ (-p.β) * (p.μ * q))) := by
  have htmem : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  obtain ⟨hC2, _, _, _, _, _, _⟩ := hsol.regularity
  have hu_c2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Ioo (0 : ℝ) 1) :=
    (hC2 t htmem).1
  have hv_c2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0 : ℝ) 1) :=
    (hC2 t htmem).2
  have hux_lift : intervalDomainLift (u t) x.1 = u t x := by
    rw [intervalDomainLift, dif_pos (Set.Ioo_subset_Icc_self hint)]
    congr
  have hu_pos : 0 < intervalDomainLift (u t) x.1 := by
    rw [hux_lift]
    exact hsol.u_pos' ht0 htT
  have hv_nn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hvpair := contDiffOn_two_hasDerivAt_pair isOpen_Ioo hv_c2 hint
  have hux0 := interior_argmax_deriv_zero hmax hint
    ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo hu_c2 hint).1.differentiableAt)
  have hvxx_eq : deriv (deriv (intervalDomainLift (v t))) x.1 =
      p.μ * intervalDomainLift (v t) x.1 -
        p.ν * (intervalDomainLift (u t) x.1) ^ p.γ := by
    have hpv := hsol.pde_v ht0 htT hint
    have hlap : intervalDomain.laplacian (v t) x =
        deriv (deriv (intervalDomainLift (v t))) x.1 := rfl
    rw [hlap, hux_lift] at hpv
    linarith
  have hgap : deriv (deriv (intervalDomainLift (v t))) x.1 ≤ -p.μ * q := by
    rw [hvxx_eq]
    have hmul := (le_div_iff₀ p.hμ).mp hsignal
    nlinarith
  have hfirst :
      -p.β * (1 + intervalDomainLift (v t) x.1) ^ (-p.β - 1) *
          (deriv (intervalDomainLift (v t)) x.1) ^ 2 ≤ 0 := by
    have hvpos : 0 < 1 + intervalDomainLift (v t) x.1 := by
      linarith [hv_nn x.1]
    have hnonneg : 0 ≤
        p.β * ((1 + intervalDomainLift (v t) x.1) ^ (-p.β - 1) *
          (deriv (intervalDomainLift (v t)) x.1) ^ 2) :=
      mul_nonneg p.hβ
        (mul_nonneg (Real.rpow_pos_of_pos hvpos _).le
          (sq_nonneg (deriv (intervalDomainLift (v t)) x.1)))
    convert neg_nonpos.mpr hnonneg using 1 <;> ring
  have hrpow_nonneg : 0 ≤
      (1 + intervalDomainLift (v t) x.1) ^ (-p.β) :=
    (Real.rpow_pos_of_pos (by linarith [hv_nn x.1]) _).le
  have hsecond :
      (1 + intervalDomainLift (v t) x.1) ^ (-p.β) *
          deriv (deriv (intervalDomainLift (v t))) x.1 ≤
        (1 + intervalDomainLift (v t) x.1) ^ (-p.β) * (-p.μ * q) :=
    mul_le_mul_of_nonneg_left hgap hrpow_nonneg
  have hcoeff :
      -p.β * (1 + intervalDomainLift (v t) x.1) ^ (-p.β - 1) *
            (deriv (intervalDomainLift (v t)) x.1) ^ 2 +
          (1 + intervalDomainLift (v t) x.1) ^ (-p.β) *
            deriv (deriv (intervalDomainLift (v t))) x.1 ≤
        -((1 + intervalDomainLift (v t) x.1) ^ (-p.β) * (p.μ * q)) := by
    nlinarith
  have hcd := chemDiv_at_critical (p := p) (u := u t) (v := v t) (x := x)
    hux0 hvpair.1 hvpair.2 hv_nn
  have hcd_le : intervalDomainChemotaxisDiv p (u t) (v t) x ≤
      -(intervalDomainLift (u t) x.1 *
        ((1 + intervalDomainLift (v t) x.1) ^ (-p.β) * (p.μ * q))) := by
    rw [hcd]
    have := mul_le_mul_of_nonneg_left hcoeff hu_pos.le
    nlinarith
  have huxx := interior_argmax_deriv2_nonpos hmax hint hu_c2
  have hpde : intervalDomain.timeDeriv u t x =
      deriv (deriv (intervalDomainLift (u t))) x.1 -
        p.χ₀ * intervalDomainChemotaxisDiv p (u t) (v t) x +
        intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) := by
    rw [hux_lift]
    exact hsol.pde_u ht0 htT hint
  have hchem := mul_le_mul_of_nonneg_left hcd_le (by linarith : 0 ≤ -p.χ₀)
  rw [hpde]
  nlinarith

#print axioms intervalDomain_interior_max_point_strict_signal

end

end ShenWork.Paper3
