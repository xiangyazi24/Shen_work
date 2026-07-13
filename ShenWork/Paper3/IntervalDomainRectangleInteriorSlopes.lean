import ShenWork.Paper3.IntervalDomainRectangleSignalBounds
import ShenWork.Paper2.IntervalDomainMaxPointSolution
import ShenWork.Paper2.IntervalDomainInteriorArgmin
import ShenWork.Paper2.IntervalDomainInteriorDeriv2

/-!
# Interior slope bounds for the interval rectangle argument

At an interior spatial maximum or minimum of a positive classical population
slice, the exact elliptic order and gradient estimates give the two scalar
rectangle inequalities used in Paper 3, Section 7.3.  The estimates are for
the concrete unit-interval equation and contain no abstract constants package.
-/

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.PDE ShenWork.Paper2
open ShenWork.MinPersistenceAtoms ShenWork.MaxPrincipleAtoms

namespace ShenWork.Paper3

noncomputable section

/-- Lower flux-coefficient estimate used at a population maximum. -/
private theorem rectangle_fluxCoefficient_lower
    {β V Vx Vxx D L : ℝ}
    (hβ : 0 ≤ β) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (hVx : |Vx| ≤ L) (hVxx : -D ≤ Vxx) :
    -(D + β * L ^ 2) ≤
      -β * (1 + V) ^ (-β - 1) * Vx ^ 2 +
        (1 + V) ^ (-β) * Vxx := by
  have hbase : 1 ≤ 1 + V := by linarith
  have hφ0 : 0 ≤ (1 + V) ^ (-β) := Real.rpow_nonneg (by linarith) _
  have hφ1 : (1 + V) ^ (-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hψ0 : 0 ≤ (1 + V) ^ (-β - 1) :=
    Real.rpow_nonneg (by linarith) _
  have hψ1 : (1 + V) ^ (-β - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hVx_sq : Vx ^ 2 ≤ L ^ 2 := by
    have habs := abs_le.mp hVx
    nlinarith [sq_nonneg Vx, sq_nonneg L]
  have hgrad :
      -β * L ^ 2 ≤ -β * (1 + V) ^ (-β - 1) * Vx ^ 2 := by
    have hψVx : (1 + V) ^ (-β - 1) * Vx ^ 2 ≤ L ^ 2 := by
      calc
        (1 + V) ^ (-β - 1) * Vx ^ 2 ≤ 1 * Vx ^ 2 :=
          mul_le_mul_of_nonneg_right hψ1 (sq_nonneg _)
        _ ≤ L ^ 2 := by simpa using hVx_sq
    have := mul_le_mul_of_nonpos_left hψVx (by linarith : -β ≤ 0)
    nlinarith
  have hell : -D ≤ (1 + V) ^ (-β) * Vxx := by
    by_cases hxx : 0 ≤ Vxx
    · exact le_trans (by linarith) (mul_nonneg hφ0 hxx)
    · have hφxx : Vxx ≤ (1 + V) ^ (-β) * Vxx := by
        have hm := mul_le_mul_of_nonpos_right hφ1 (le_of_not_ge hxx)
        simpa using hm
      exact hVxx.trans hφxx
  linarith

/-- Upper flux-coefficient estimate used at a population minimum. -/
private theorem rectangle_fluxCoefficient_upper
    {β V Vx Vxx D : ℝ}
    (hβ : 0 ≤ β) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (hVxx : Vxx ≤ D) :
    -β * (1 + V) ^ (-β - 1) * Vx ^ 2 +
        (1 + V) ^ (-β) * Vxx ≤ D := by
  have hbase : 1 ≤ 1 + V := by linarith
  have hφ0 : 0 ≤ (1 + V) ^ (-β) := Real.rpow_nonneg (by linarith) _
  have hφ1 : (1 + V) ^ (-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hψ0 : 0 ≤ (1 + V) ^ (-β - 1) :=
    Real.rpow_nonneg (by linarith) _
  have hgrad : -β * (1 + V) ^ (-β - 1) * Vx ^ 2 ≤ 0 := by
    have : 0 ≤ β * ((1 + V) ^ (-β - 1) * Vx ^ 2) :=
      mul_nonneg hβ (mul_nonneg hψ0 (sq_nonneg _))
    nlinarith
  have hell : (1 + V) ^ (-β) * Vxx ≤ D := by
    by_cases hxx : Vxx ≤ 0
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hφ0 hxx) hD
    · have hφxx : (1 + V) ^ (-β) * Vxx ≤ Vxx := by
        have hm := mul_le_mul_of_nonneg_right hφ1 (le_of_not_ge hxx)
        simpa using hm
      exact hφxx.trans hVxx
  linarith

/-- At an interior spatial maximum, the population slope is bounded by the
upper rectangle vector field with the concrete resolver-gradient constant. -/
theorem intervalDomain_rectangle_interior_max_slope
    {p : CM2Params} {T t uMin : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
    (hint : x.1 ∈ Ioo (0 : ℝ) 1)
    (hmax : ∀ y, u t y ≤ u t x)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      uMin ≤ intervalDomainLift (u t) y) :
    intervalDomain.timeDeriv u t x ≤
      intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) +
        p.χ₀ * intervalDomainLift (u t) x.1 *
          (p.ν * ((intervalDomainLift (u t) x.1) ^ p.γ - uMin ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * ((intervalDomainLift (u t) x.1) ^ p.γ -
                uMin ^ p.γ))) ^ 2) := by
  have ht0 := ht.1
  have htT := ht.2
  obtain ⟨hC2, _, _, _, _, _, _⟩ := hsol.regularity
  have huC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Ioo (0 : ℝ) 1) :=
    (hC2 t ht).1
  have hvC2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Ioo (0 : ℝ) 1) :=
    (hC2 t ht).2
  have hUeq : intervalDomainLift (u t) x.1 = u t x := by
    rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hint)]
    congr
  set U : ℝ := intervalDomainLift (u t) x.1 with hU_def
  set D : ℝ := p.ν * (U ^ p.γ - uMin ^ p.γ) with hD_def
  set L : ℝ := unitIntervalResolverGradientOscillationConstant p * D with hL_def
  have hUpos : 0 < U := by
    rw [hUeq]
    exact hsol.u_pos' ht0 htT
  have hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ U := by
    intro y hy
    rw [hUeq, intervalDomainLift, dif_pos hy]
    exact hmax ⟨y, hy⟩
  have hD : 0 ≤ D := by
    have hp : uMin ^ p.γ ≤ U ^ p.γ :=
      Real.rpow_le_rpow huMin (hlo x.1 (Ioo_subset_Icc_self hint)) p.hγ.le
    exact mul_nonneg p.hν.le (sub_nonneg.mpr hp)
  have hL : 0 ≤ L := mul_nonneg
    (unitIntervalResolverGradientOscillationConstant_nonneg p) hD
  have hsig := intervalDomain_solution_signal_bounds_of_population_box
    p hsol ht huMin hlo hhi x.1 (Ioo_subset_Icc_self hint)
  have hvnn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hvpair := contDiffOn_two_hasDerivAt_pair isOpen_Ioo hvC2 hint
  have hvxxEq : deriv (deriv (intervalDomainLift (v t))) x.1 =
      p.μ * intervalDomainLift (v t) x.1 - p.ν * U ^ p.γ := by
    have hpde := hsol.pde_v ht0 htT (x := x) hint
    have hlap : intervalDomain.laplacian (v t) x =
        deriv (deriv (intervalDomainLift (v t))) x.1 := rfl
    have hVeq : intervalDomainLift (v t) x.1 = v t x := by
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hint)]
      congr
    rw [hlap, ← hUeq, ← hVeq] at hpde
    rw [hU_def]
    linarith
  have hvxxLower : -D ≤ deriv (deriv (intervalDomainLift (v t))) x.1 := by
    have hmul := mul_le_mul_of_nonneg_left hsig.1 p.hμ.le
    have hcancel : p.μ * (p.ν * uMin ^ p.γ / p.μ) =
        p.ν * uMin ^ p.γ := by field_simp [ne_of_gt p.hμ]
    rw [hcancel] at hmul
    rw [hvxxEq]
    rw [hD_def]
    linarith
  have hcoeffLower := rectangle_fluxCoefficient_lower p.hβ
    (hvnn x.1) hD (by simpa [hL_def, hD_def, hU_def] using hsig.2.2)
      hvxxLower
  have hux0 := interior_argmax_deriv_zero hmax hint
    ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hint).1.differentiableAt)
  have hcd := chemDiv_at_critical (p := p) (u := u t) (v := v t) (x := x)
    hux0 hvpair.1 hvpair.2 hvnn
  have hcdLower : -U * (D + p.β * L ^ 2) ≤
      intervalDomainChemotaxisDiv p (u t) (v t) x := by
    rw [hcd]
    have hm := mul_le_mul_of_nonneg_left hcoeffLower hUpos.le
    rw [hU_def] at hm
    convert hm using 1 <;> ring
  have huxx := interior_argmax_deriv2_nonpos hmax hint huC2
  have hpde : intervalDomain.timeDeriv u t x =
      deriv (deriv (intervalDomainLift (u t))) x.1 -
        p.χ₀ * intervalDomainChemotaxisDiv p (u t) (v t) x +
        U * (p.a - p.b * U ^ p.α) := by
    rw [hUeq]
    exact hsol.pde_u ht0 htT hint
  have hchem := mul_le_mul_of_nonpos_left hcdLower (by linarith : -p.χ₀ ≤ 0)
  change intervalDomain.timeDeriv u t x ≤
    U * (p.a - p.b * U ^ p.α) +
      p.χ₀ * U * (D + p.β * L ^ 2)
  rw [hpde]
  nlinarith

/-- At an interior spatial minimum, the population slope is bounded below by
the lower rectangle vector field. -/
theorem intervalDomain_rectangle_interior_min_slope
    {p : CM2Params} {T t uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hint : x.1 ∈ Ioo (0 : ℝ) 1)
    (hmin : ∀ y, u t x ≤ u t y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ uMax) :
    -p.χ₀ * intervalDomainLift (u t) x.1 *
          (p.ν * (uMax ^ p.γ -
            (intervalDomainLift (u t) x.1) ^ p.γ)) +
        intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) ≤
      intervalDomain.timeDeriv u t x := by
  have ht0 := ht.1
  have htT := ht.2
  obtain ⟨hC2, _, _, _, _, _, _⟩ := hsol.regularity
  have huC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Ioo (0 : ℝ) 1) :=
    (hC2 t ht).1
  have hvC2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Ioo (0 : ℝ) 1) :=
    (hC2 t ht).2
  have hUeq : intervalDomainLift (u t) x.1 = u t x := by
    rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hint)]
    congr
  set U : ℝ := intervalDomainLift (u t) x.1 with hU_def
  set D : ℝ := p.ν * (uMax ^ p.γ - U ^ p.γ) with hD_def
  have hUpos : 0 < U := by
    rw [hUeq]
    exact hsol.u_pos' ht0 htT
  have hlo : ∀ y ∈ Icc (0 : ℝ) 1, U ≤ intervalDomainLift (u t) y := by
    intro y hy
    rw [hUeq, intervalDomainLift, dif_pos hy]
    exact hmin ⟨y, hy⟩
  have hD : 0 ≤ D := by
    have hp : U ^ p.γ ≤ uMax ^ p.γ :=
      Real.rpow_le_rpow hUpos.le (hhi x.1 (Ioo_subset_Icc_self hint)) p.hγ.le
    exact mul_nonneg p.hν.le (sub_nonneg.mpr hp)
  have hsig := intervalDomain_solution_signal_bounds_of_population_box
    p hsol ht hUpos.le hlo hhi x.1 (Ioo_subset_Icc_self hint)
  have hvnn : ∀ y, 0 ≤ intervalDomainLift (v t) y := by
    intro y
    unfold intervalDomainLift
    split_ifs
    · exact hsol.v_nonneg ht0 htT
    · exact le_rfl
  have hvpair := contDiffOn_two_hasDerivAt_pair isOpen_Ioo hvC2 hint
  have hvxxEq : deriv (deriv (intervalDomainLift (v t))) x.1 =
      p.μ * intervalDomainLift (v t) x.1 - p.ν * U ^ p.γ := by
    have hpde := hsol.pde_v ht0 htT (x := x) hint
    have hlap : intervalDomain.laplacian (v t) x =
        deriv (deriv (intervalDomainLift (v t))) x.1 := rfl
    have hVeq : intervalDomainLift (v t) x.1 = v t x := by
      rw [intervalDomainLift, dif_pos (Ioo_subset_Icc_self hint)]
      congr
    rw [hlap, ← hUeq, ← hVeq] at hpde
    rw [hU_def]
    linarith
  have hvxxUpper : deriv (deriv (intervalDomainLift (v t))) x.1 ≤ D := by
    have hmul := mul_le_mul_of_nonneg_left hsig.2.1 p.hμ.le
    have hcancel : p.μ * (p.ν * uMax ^ p.γ / p.μ) =
        p.ν * uMax ^ p.γ := by field_simp [ne_of_gt p.hμ]
    rw [hcancel] at hmul
    rw [hvxxEq]
    rw [hD_def]
    linarith
  have hcoeffUpper := rectangle_fluxCoefficient_upper
    (Vx := deriv (intervalDomainLift (v t)) x.1)
    p.hβ (hvnn x.1) hD hvxxUpper
  have hux0 := interior_argmin_deriv_zero hmin hint
    ((contDiffOn_two_hasDerivAt_pair isOpen_Ioo huC2 hint).1.differentiableAt)
  have hcd := chemDiv_at_critical (p := p) (u := u t) (v := v t) (x := x)
    hux0 hvpair.1 hvpair.2 hvnn
  have hcdUpper : intervalDomainChemotaxisDiv p (u t) (v t) x ≤ U * D := by
    rw [hcd]
    have hm := mul_le_mul_of_nonneg_left hcoeffUpper hUpos.le
    simpa [hU_def] using hm
  have huxx := interior_argmin_deriv2_nonneg hmin hint huC2
  have hpde : intervalDomain.timeDeriv u t x =
      deriv (deriv (intervalDomainLift (u t))) x.1 -
        p.χ₀ * intervalDomainChemotaxisDiv p (u t) (v t) x +
        U * (p.a - p.b * U ^ p.α) := by
    rw [hUeq]
    exact hsol.pde_u ht0 htT hint
  have hchem := mul_le_mul_of_nonpos_left hcdUpper (by linarith : -p.χ₀ ≤ 0)
  change -p.χ₀ * U * D + U * (p.a - p.b * U ^ p.α) ≤
    intervalDomain.timeDeriv u t x
  rw [hpde]
  nlinarith

#print axioms intervalDomain_rectangle_interior_max_slope
#print axioms intervalDomain_rectangle_interior_min_slope

end

end ShenWork.Paper3
