import ShenWork.Paper3.IntervalDomainMRectangleBoundarySlopes

/-!
# Closed-interval extremum slopes for the faithful general-`m` rectangle argument

`intervalDomainM` counterpart of `IntervalDomainRectangleExtremumSlopes`.  The
interior and two endpoint estimates are dispatched here for an arbitrary
attained spatial maximum or minimum of a positive classical slice of the
`u^m`-flux equation.  The only change from the `m = 1` dispatcher is the
chemotaxis prefactor `U^m` (vs `U`) carried through from the interior and
boundary slope bounds.
-/

open Set
open ShenWork.IntervalDomain ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Weighted rectangle upper slope at any attained closed-interval spatial
maximum, faithful `u^m` flux. -/
theorem intervalDomainM_rectangle_max_slope_of_argmax_with_weight
    {p : CM2Params} {T t uMin : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (q : ℝ) (hq : 0 ≤ q)
    (hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ q)
    (hweightOne : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ q)
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
    (hmax : ∀ y, u t y ≤ u t x)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      uMin ≤ intervalDomainLift (u t) y) :
    intervalDomain.timeDeriv u t x ≤
      intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) +
        p.χ₀ * (intervalDomainLift (u t) x.1) ^ p.m *
          (q * (p.ν * ((intervalDomainLift (u t) x.1) ^ p.γ - uMin ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * ((intervalDomainLift (u t) x.1) ^ p.γ -
                uMin ^ p.γ))) ^ 2)) := by
  rcases lt_or_eq_of_le x.2.1 with hx0 | hx0
  · rcases lt_or_eq_of_le x.2.2 with hx1 | hx1
    · exact intervalDomainM_rectangle_interior_max_slope_with_weight
        q hq (hweight x.1 x.2) (hweightOne x.1 x.2)
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
      have hb := intervalDomainM_rectangle_boundary_right_max_slope_with_weight
        q hq (hweight 1 ⟨zero_le_one, le_rfl⟩) hχ hsol ht huMin hlo hhi
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
    have hb := intervalDomainM_rectangle_boundary_left_max_slope_with_weight
      q hq (hweight 0 ⟨le_rfl, zero_le_one⟩) hχ hsol ht huMin hlo hhi
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

/-- Rectangle upper slope at any attained closed-interval spatial maximum,
faithful `u^m` flux. -/
theorem intervalDomainM_rectangle_max_slope_of_argmax
    {p : CM2Params} {T t uMin : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) (huMin : 0 ≤ uMin)
    (hmax : ∀ y, u t y ≤ u t x)
    (hlo : ∀ y ∈ Icc (0 : ℝ) 1,
      uMin ≤ intervalDomainLift (u t) y) :
    intervalDomain.timeDeriv u t x ≤
      intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) +
        p.χ₀ * (intervalDomainLift (u t) x.1) ^ p.m *
          (p.ν * ((intervalDomainLift (u t) x.1) ^ p.γ - uMin ^ p.γ) +
            p.β * (unitIntervalResolverGradientOscillationConstant p *
              (p.ν * ((intervalDomainLift (u t) x.1) ^ p.γ -
                uMin ^ p.γ))) ^ 2) := by
  have hv : ∀ y ∈ Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (v t) y := by
    intro y hy
    rw [intervalDomainLift, dif_pos hy]
    exact hsol.v_nonneg ht.1 ht.2
  have hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ 1 := by
    intro y hy
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [hv y hy]) (neg_nonpos.mpr p.hβ)
  have hweightOne : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β - 1) ≤ 1 := by
    intro y hy
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [hv y hy]) (by linarith [p.hβ])
  simpa using intervalDomainM_rectangle_max_slope_of_argmax_with_weight
    (p := p) (T := T) (t := t) (uMin := uMin) (u := u) (v := v) (x := x)
      1 zero_le_one hweight hweightOne hχ hsol ht huMin hmax hlo

/-- Weighted rectangle lower slope at any attained closed-interval spatial
minimum, faithful `u^m` flux. -/
theorem intervalDomainM_rectangle_min_slope_of_argmin_with_weight
    {p : CM2Params} {T t uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (q : ℝ) (hq : 0 ≤ q)
    (hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ q)
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hmin : ∀ y, u t x ≤ u t y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ uMax) :
    -p.χ₀ * q * (intervalDomainLift (u t) x.1) ^ p.m *
          (p.ν * (uMax ^ p.γ -
            (intervalDomainLift (u t) x.1) ^ p.γ)) +
        intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) ≤
      intervalDomain.timeDeriv u t x := by
  rcases lt_or_eq_of_le x.2.1 with hx0 | hx0
  · rcases lt_or_eq_of_le x.2.2 with hx1 | hx1
    · exact intervalDomainM_rectangle_interior_min_slope_with_weight
        q hq (hweight x.1 x.2) hχ hsol ht ⟨hx0, hx1⟩ hmin hhi
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
      have hb := intervalDomainM_rectangle_boundary_right_min_slope_with_weight
        q hq (hweight 1 ⟨zero_le_one, le_rfl⟩) hχ hsol ht hlo hhi
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
    have hb := intervalDomainM_rectangle_boundary_left_min_slope_with_weight
      q hq (hweight 0 ⟨le_rfl, zero_le_one⟩) hχ hsol ht hlo hhi
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

/-- Rectangle lower slope at any attained closed-interval spatial minimum,
faithful `u^m` flux. -/
theorem intervalDomainM_rectangle_min_slope_of_argmin
    {p : CM2Params} {T t uMax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {x : intervalDomainPoint}
    (hχ : 0 ≤ p.χ₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hmin : ∀ y, u t x ≤ u t y)
    (hhi : ∀ y ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ uMax) :
    -p.χ₀ * (intervalDomainLift (u t) x.1) ^ p.m *
          (p.ν * (uMax ^ p.γ -
            (intervalDomainLift (u t) x.1) ^ p.γ)) +
        intervalDomainLift (u t) x.1 *
          (p.a - p.b * (intervalDomainLift (u t) x.1) ^ p.α) ≤
      intervalDomain.timeDeriv u t x := by
  have hv : ∀ y ∈ Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (v t) y := by
    intro y hy
    rw [intervalDomainLift, dif_pos hy]
    exact hsol.v_nonneg ht.1 ht.2
  have hweight : ∀ y ∈ Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ (-p.β) ≤ 1 := by
    intro y hy
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [hv y hy]) (neg_nonpos.mpr p.hβ)
  simpa using intervalDomainM_rectangle_min_slope_of_argmin_with_weight
    (p := p) (T := T) (t := t) (uMax := uMax) (u := u) (v := v) (x := x)
      1 zero_le_one hweight hχ hsol ht hmin hhi

#print axioms intervalDomainM_rectangle_max_slope_of_argmax
#print axioms intervalDomainM_rectangle_min_slope_of_argmin
#print axioms intervalDomainM_rectangle_max_slope_of_argmax_with_weight
#print axioms intervalDomainM_rectangle_min_slope_of_argmin_with_weight

end

end ShenWork.Paper3
