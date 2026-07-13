import ShenWork.Paper3.IntervalDomainRectangleBoundarySlopes

/-!
# Closed-interval extremum slopes for the rectangle argument

The interior and two endpoint estimates are dispatched here for an arbitrary
attained spatial maximum or minimum of a positive classical slice.
-/

open Set
open ShenWork.IntervalDomain ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Rectangle upper slope at any attained closed-interval spatial maximum. -/
theorem intervalDomain_rectangle_max_slope_of_argmax
    {p : CM2Params} {T t uMin : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
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
  rcases lt_or_eq_of_le x.2.1 with hx0 | hx0
  · rcases lt_or_eq_of_le x.2.2 with hx1 | hx1
    · exact intervalDomain_rectangle_interior_max_slope
        hχ hsol ht huMin ⟨hx0, hx1⟩ hmax hlo
    · have hx11 : x.1 = 1 := hx1
      have hlift1 : intervalDomainLift (u t) 1 = u t x := by
        rw [intervalDomainLift,
          dif_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]
        exact congrArg (u t) (Subtype.ext hx11.symm)
      have hhi : ∀ y ∈ Icc (0 : ℝ) 1,
          intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 1 := by
        intro y hy
        rw [hlift1, intervalDomainLift, dif_pos hy]
        exact hmax ⟨y, hy⟩
      have hb := intervalDomain_rectangle_boundary_right_max_slope
        hχ hsol ht huMin hlo hhi
      have htd : intervalDomain.timeDeriv u t x =
          deriv (fun r => intervalDomainLift (u r) 1) t := by
        show deriv (fun s => u s x) t =
          deriv (fun r => intervalDomainLift (u r) 1) t
        congr 1
        funext r
        rw [intervalDomainLift,
          dif_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]
        exact (congrArg (u r) (Subtype.ext hx11.symm)).symm
      rw [hx11, htd]
      exact hb
  · have hx10 : x.1 = 0 := hx0.symm
    have hlift0 : intervalDomainLift (u t) 0 = u t x := by
      rw [intervalDomainLift,
        dif_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)]
      exact congrArg (u t) (Subtype.ext hx10.symm)
    have hhi : ∀ y ∈ Icc (0 : ℝ) 1,
        intervalDomainLift (u t) y ≤ intervalDomainLift (u t) 0 := by
      intro y hy
      rw [hlift0, intervalDomainLift, dif_pos hy]
      exact hmax ⟨y, hy⟩
    have hb := intervalDomain_rectangle_boundary_left_max_slope
      hχ hsol ht huMin hlo hhi
    have htd : intervalDomain.timeDeriv u t x =
        deriv (fun r => intervalDomainLift (u r) 0) t := by
      show deriv (fun s => u s x) t =
        deriv (fun r => intervalDomainLift (u r) 0) t
      congr 1
      funext r
      rw [intervalDomainLift,
        dif_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)]
      exact (congrArg (u r) (Subtype.ext hx10.symm)).symm
    rw [hx10, htd]
    exact hb

/-- Rectangle lower slope at any attained closed-interval spatial minimum. -/
theorem intervalDomain_rectangle_min_slope_of_argmin
    {p : CM2Params} {T t uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hmin : ∀ y, u t x ≤ u t y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ uMax) :
    -p.χ₀ * intervalDomainLift (u t) x.1 *
          (p.ν * (uMax ^ p.γ -
            (intervalDomainLift (u t) x.1) ^ p.γ)) +
        intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) ≤
      intervalDomain.timeDeriv u t x := by
  rcases lt_or_eq_of_le x.2.1 with hx0 | hx0
  · rcases lt_or_eq_of_le x.2.2 with hx1 | hx1
    · exact intervalDomain_rectangle_interior_min_slope
        hχ hsol ht ⟨hx0, hx1⟩ hmin hhi
    · have hx11 : x.1 = 1 := hx1
      have hlift1 : intervalDomainLift (u t) 1 = u t x := by
        rw [intervalDomainLift,
          dif_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]
        exact congrArg (u t) (Subtype.ext hx11.symm)
      have hlo : ∀ y ∈ Icc (0 : ℝ) 1,
          intervalDomainLift (u t) 1 ≤ intervalDomainLift (u t) y := by
        intro y hy
        rw [hlift1, intervalDomainLift, dif_pos hy]
        exact hmin ⟨y, hy⟩
      have hb := intervalDomain_rectangle_boundary_right_min_slope
        hχ hsol ht hlo hhi
      have htd : intervalDomain.timeDeriv u t x =
          deriv (fun r => intervalDomainLift (u r) 1) t := by
        show deriv (fun s => u s x) t =
          deriv (fun r => intervalDomainLift (u r) 1) t
        congr 1
        funext r
        rw [intervalDomainLift,
          dif_pos (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]
        exact (congrArg (u r) (Subtype.ext hx11.symm)).symm
      rw [hx11, htd]
      exact hb
  · have hx10 : x.1 = 0 := hx0.symm
    have hlift0 : intervalDomainLift (u t) 0 = u t x := by
      rw [intervalDomainLift,
        dif_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)]
      exact congrArg (u t) (Subtype.ext hx10.symm)
    have hlo : ∀ y ∈ Icc (0 : ℝ) 1,
        intervalDomainLift (u t) 0 ≤ intervalDomainLift (u t) y := by
      intro y hy
      rw [hlift0, intervalDomainLift, dif_pos hy]
      exact hmin ⟨y, hy⟩
    have hb := intervalDomain_rectangle_boundary_left_min_slope
      hχ hsol ht hlo hhi
    have htd : intervalDomain.timeDeriv u t x =
        deriv (fun r => intervalDomainLift (u r) 0) t := by
      show deriv (fun s => u s x) t =
        deriv (fun r => intervalDomainLift (u r) 0) t
      congr 1
      funext r
      rw [intervalDomainLift,
        dif_pos (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)]
      exact (congrArg (u r) (Subtype.ext hx10.symm)).symm
    rw [hx10, htd]
    exact hb

#print axioms intervalDomain_rectangle_max_slope_of_argmax
#print axioms intervalDomain_rectangle_min_slope_of_argmin

end

end ShenWork.Paper3
