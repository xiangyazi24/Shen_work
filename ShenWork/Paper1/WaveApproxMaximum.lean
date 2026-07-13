/-
  Tail-free maximum-principle tool on the real line.

  Subtracting `eps * x^2` from a bounded function forces attainment without
  imposing endpoint limits.  At the attained point the first- and second-
  derivative errors are explicit.  This is the replacement for the tail-based
  global-maximum step in the whole-line Green construction.
-/
import ShenWork.Paper1.WaveRotheMaxPrincipleClosers

open Filter Topology Real Set

noncomputable section

namespace ShenWork.Paper1

/-- A bounded continuous function minus a positive quadratic penalty attains
its global maximum. -/
theorem exists_isMaxOn_sub_mul_sq_of_bounded
    {f : ℝ → ℝ} {A eps x₁ : ℝ}
    (hf : Continuous f) (hA : ∀ x, |f x| ≤ A) (heps : 0 < eps) :
    ∃ x₀,
      IsMaxOn (fun x => f x - eps * x ^ 2) Set.univ x₀ ∧
      f x₁ - eps * x₁ ^ 2 ≤ f x₀ - eps * x₀ ^ 2 := by
  have hAnn : 0 ≤ A := le_trans (abs_nonneg (f 0)) (hA 0)
  let t : ℝ := (2 * A + eps * x₁ ^ 2) / eps
  let R : ℝ := t + 1
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have het : eps * t = 2 * A + eps * x₁ ^ 2 := by
    dsimp [t]
    field_simp [ne_of_gt heps]
  have hescape : 2 * A + eps * x₁ ^ 2 < eps * R ^ 2 := by
    dsimp [R]
    nlinarith [mul_pos heps (by nlinarith : 0 < 2 * t + 1)]
  let g : ℝ → ℝ := fun x => f x - eps * x ^ 2
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hright : ∀ x, R ≤ x → g x ≤ g x₁ := by
    intro x hx
    have hx2 : R ^ 2 ≤ x ^ 2 := by nlinarith
    have hfx : f x ≤ A := (le_abs_self (f x)).trans (hA x)
    have hfx₁ : -A ≤ f x₁ := neg_le_of_abs_le (hA x₁)
    dsimp [g]
    nlinarith [hescape, mul_le_mul_of_nonneg_left hx2 heps.le]
  have hleft : ∀ x, x ≤ -R → g x ≤ g x₁ := by
    intro x hx
    have hx2 : R ^ 2 ≤ x ^ 2 := by nlinarith
    have hfx : f x ≤ A := (le_abs_self (f x)).trans (hA x)
    have hfx₁ : -A ≤ f x₁ := neg_le_of_abs_le (hA x₁)
    dsimp [g]
    nlinarith [hescape, mul_le_mul_of_nonneg_left hx2 heps.le]
  have hcoc : ∀ᶠ x in cocompact ℝ, g x ≤ g x₁ := by
    rw [cocompact_eq_atBot_atTop]
    exact eventually_sup.mpr
      ⟨eventually_atBot.2 ⟨-R, hleft⟩,
        eventually_atTop.2 ⟨R, hright⟩⟩
  obtain ⟨x₀, hx₀⟩ := hg.exists_forall_ge' x₁ hcoc
  exact ⟨x₀, isMaxOn_univ_iff.mpr hx₀, hx₀ x₁⟩

/-- At the penalized maximum the derivative errors are exactly those of the
quadratic penalty. -/
theorem exists_penalized_max_deriv_data
    {f : ℝ → ℝ} {A eps x₁ : ℝ}
    (hf : ContDiff ℝ 2 f) (hA : ∀ x, |f x| ≤ A) (heps : 0 < eps) :
    ∃ x₀,
      IsMaxOn (fun x => f x - eps * x ^ 2) Set.univ x₀ ∧
      f x₁ - eps * x₁ ^ 2 ≤ f x₀ - eps * x₀ ^ 2 ∧
      deriv f x₀ = 2 * eps * x₀ ∧
      deriv (deriv f) x₀ ≤ 2 * eps := by
  obtain ⟨x₀, hmax, hvalue⟩ :=
    exists_isMaxOn_sub_mul_sq_of_bounded (x₁ := x₁) hf.continuous hA heps
  have hlocal : IsLocalMax (fun x => f x - eps * x ^ 2) x₀ :=
    hmax.isLocalMax Filter.univ_mem
  have hf0 : HasDerivAt f (deriv f x₀) x₀ :=
    (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hsq0 : HasDerivAt (fun x : ℝ => eps * x ^ 2) (2 * eps * x₀) x₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x₀).pow 2).const_mul eps
  have hfirst : deriv f x₀ = 2 * eps * x₀ := by
    have hzero : deriv (fun x => f x - eps * x ^ 2) x₀ = 0 :=
      hlocal.deriv_eq_zero
    have hderiv :
        deriv (fun x => f x - eps * x ^ 2) x₀ =
          deriv f x₀ - 2 * eps * x₀ := (hf0.sub hsq0).deriv
    rw [hderiv] at hzero
    linarith
  have hpenC2 : ContDiff ℝ 2 (fun x : ℝ => eps * x ^ 2) := by fun_prop
  have hsecond_raw :
      iteratedDeriv 2 (fun x => f x - eps * x ^ 2) x₀ ≤ 0 :=
    iteratedDeriv2_nonpos_of_isLocalMax hlocal
      (hf.continuous.continuousAt.sub hpenC2.continuous.continuousAt)
  have hlin :
      iteratedDeriv 2 (fun x => f x - eps * x ^ 2) x₀ =
        iteratedDeriv 2 f x₀ - iteratedDeriv 2 (fun x : ℝ => eps * x ^ 2) x₀ :=
    iteratedDeriv_fun_sub hf.contDiffAt hpenC2.contDiffAt
  have hsq2 : iteratedDeriv 2 (fun x : ℝ => eps * x ^ 2) x₀ = 2 * eps := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
    ring
  have hf2 : iteratedDeriv 2 f x₀ = deriv (deriv f) x₀ := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hlin, hsq2, hf2] at hsecond_raw
  exact ⟨x₀, hmax, hvalue, hfirst, by linarith⟩

/-- A positive value of a bounded `C²` function produces an almost-critical
positive value, with arbitrarily small first- and upper second-derivative
errors.  No behavior at either end of the real line is assumed. -/
theorem exists_approx_positive_max_deriv_data
    {f : ℝ → ℝ} {A eta x₁ : ℝ}
    (hf : ContDiff ℝ 2 f) (hA : ∀ x, |f x| ≤ A)
    (hpos : 0 < f x₁) (heta : 0 < eta) :
    ∃ x₀,
      f x₁ / 2 < f x₀ ∧
      |deriv f x₀| < eta ∧
      deriv (deriv f) x₀ < eta := by
  have hApos : 0 < A := lt_of_lt_of_le hpos (le_trans (le_abs_self (f x₁)) (hA x₁))
  let D : ℝ := 2 * A + x₁ ^ 2 + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg x₁]
  let eps : ℝ :=
    min 1
      (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
        (min (eta / 2) (eta ^ 2 / (8 * D)))) / 2
  have hxden : 0 < 2 * (x₁ ^ 2 + 1) := by positivity
  have hetasq : 0 < eta ^ 2 := sq_pos_of_pos heta
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_one : eps < 1 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ 1 := min_le_left _ _
    nlinarith
  have heps_value : eps < f x₁ / (2 * (x₁ ^ 2 + 1)) := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤
          f x₁ / (2 * (x₁ ^ 2 + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    nlinarith [div_pos hpos hxden]
  have heps_eta : 2 * eps < eta := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    nlinarith
  have heps_sq : 4 * eps * D < eta ^ 2 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta ^ 2 / (8 * D) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hdiv : 0 < eta ^ 2 / (8 * D) := by positivity
    have hle : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤
          eta ^ 2 / (8 * D) := hmin
    have hmul := mul_le_mul_of_nonneg_right hle (show 0 ≤ 4 * D by positivity)
    field_simp [ne_of_gt hD] at hmul
    nlinarith
  obtain ⟨x₀, _hmax, hvalue, hfirst, hsecond⟩ :=
    exists_penalized_max_deriv_data hf hA heps (x₁ := x₁)
  have hvalue_pos : f x₁ / 2 < f x₀ := by
    have hxfrac : eps * x₁ ^ 2 < f x₁ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right heps_value.le (sq_nonneg x₁)
      have hfrac :
          f x₁ / (2 * (x₁ ^ 2 + 1)) * x₁ ^ 2 < f x₁ / 2 := by
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hxden).2
        nlinarith [sq_nonneg x₁]
      exact lt_of_le_of_lt (by simpa [mul_assoc] using hmul) hfrac
    nlinarith [mul_nonneg heps.le (sq_nonneg x₀)]
  have hx₀bound : eps * x₀ ^ 2 < D := by
    have hf₀ : f x₀ ≤ A := (le_abs_self (f x₀)).trans (hA x₀)
    have hf₁ : -A ≤ f x₁ := neg_le_of_abs_le (hA x₁)
    have hepsx : eps * x₁ ^ 2 ≤ x₁ ^ 2 := by
      exact mul_le_of_le_one_left (sq_nonneg x₁) heps_one.le
    dsimp [D]
    nlinarith
  have hderiv_sq : (deriv f x₀) ^ 2 < eta ^ 2 := by
    rw [hfirst]
    calc
      (2 * eps * x₀) ^ 2 = 4 * eps * (eps * x₀ ^ 2) := by ring
      _ < 4 * eps * D := by
        exact mul_lt_mul_of_pos_left hx₀bound (by positivity)
      _ < eta ^ 2 := heps_sq
  have hderiv : |deriv f x₀| < eta := by
    rw [← sq_lt_sq₀ (abs_nonneg (deriv f x₀)) heta.le, sq_abs]
    exact hderiv_sq
  exact ⟨x₀, hvalue_pos, hderiv, lt_of_le_of_lt hsecond heps_eta⟩

/-- A continuous function which is only bounded above still has a penalized
global maximum once a positive reference value is fixed.  This one-sided form
is needed for raw lower barriers, which diverge to `-∞` on the left and hence
are not bounded in absolute value. -/
theorem exists_isMaxOn_sub_mul_sq_of_upperBound
    {f : ℝ → ℝ} {A eps x₁ : ℝ}
    (hf : Continuous f) (hA : ∀ x, f x ≤ A)
    (hpos : 0 < f x₁) (heps : 0 < eps) :
    ∃ x₀,
      IsMaxOn (fun x => f x - eps * x ^ 2) Set.univ x₀ ∧
      f x₁ - eps * x₁ ^ 2 ≤ f x₀ - eps * x₀ ^ 2 := by
  have hApos : 0 < A := lt_of_lt_of_le hpos (hA x₁)
  let t : ℝ := (A + eps * x₁ ^ 2) / eps
  let R : ℝ := t + 1
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have het : eps * t = A + eps * x₁ ^ 2 := by
    dsimp [t]
    field_simp [ne_of_gt heps]
  have hescape : A + eps * x₁ ^ 2 < eps * R ^ 2 := by
    dsimp [R]
    nlinarith [mul_pos heps (by nlinarith : 0 < 2 * t + 1)]
  let g : ℝ → ℝ := fun x => f x - eps * x ^ 2
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hright : ∀ x, R ≤ x → g x ≤ g x₁ := by
    intro x hx
    have hx2 : R ^ 2 ≤ x ^ 2 := by nlinarith
    have hfx := hA x
    dsimp [g]
    nlinarith [hpos,
      hescape, mul_le_mul_of_nonneg_left hx2 heps.le]
  have hleft : ∀ x, x ≤ -R → g x ≤ g x₁ := by
    intro x hx
    have hx2 : R ^ 2 ≤ x ^ 2 := by nlinarith
    have hfx := hA x
    dsimp [g]
    nlinarith [hpos,
      hescape, mul_le_mul_of_nonneg_left hx2 heps.le]
  have hcoc : ∀ᶠ x in cocompact ℝ, g x ≤ g x₁ := by
    rw [cocompact_eq_atBot_atTop]
    exact eventually_sup.mpr
      ⟨eventually_atBot.2 ⟨-R, hleft⟩,
        eventually_atTop.2 ⟨R, hright⟩⟩
  obtain ⟨x₀, hx₀⟩ := hg.exists_forall_ge' x₁ hcoc
  exact ⟨x₀, isMaxOn_univ_iff.mpr hx₀, hx₀ x₁⟩

/-- Derivative data at the penalized maximum under a one-sided upper bound. -/
theorem exists_penalized_max_deriv_data_of_upperBound
    {f : ℝ → ℝ} {A eps x₁ : ℝ}
    (hf : ContDiff ℝ 2 f) (hA : ∀ x, f x ≤ A)
    (hpos : 0 < f x₁) (heps : 0 < eps) :
    ∃ x₀,
      IsMaxOn (fun x => f x - eps * x ^ 2) Set.univ x₀ ∧
      f x₁ - eps * x₁ ^ 2 ≤ f x₀ - eps * x₀ ^ 2 ∧
      deriv f x₀ = 2 * eps * x₀ ∧
      deriv (deriv f) x₀ ≤ 2 * eps := by
  obtain ⟨x₀, hmax, hvalue⟩ :=
    exists_isMaxOn_sub_mul_sq_of_upperBound
      (x₁ := x₁) hf.continuous hA hpos heps
  have hlocal : IsLocalMax (fun x => f x - eps * x ^ 2) x₀ :=
    hmax.isLocalMax Filter.univ_mem
  have hf0 : HasDerivAt f (deriv f x₀) x₀ :=
    (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hsq0 : HasDerivAt (fun x : ℝ => eps * x ^ 2) (2 * eps * x₀) x₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x₀).pow 2).const_mul eps
  have hfirst : deriv f x₀ = 2 * eps * x₀ := by
    have hzero : deriv (fun x => f x - eps * x ^ 2) x₀ = 0 :=
      hlocal.deriv_eq_zero
    have hderiv :
        deriv (fun x => f x - eps * x ^ 2) x₀ =
          deriv f x₀ - 2 * eps * x₀ := (hf0.sub hsq0).deriv
    rw [hderiv] at hzero
    linarith
  have hpenC2 : ContDiff ℝ 2 (fun x : ℝ => eps * x ^ 2) := by fun_prop
  have hsecond_raw :
      iteratedDeriv 2 (fun x => f x - eps * x ^ 2) x₀ ≤ 0 :=
    iteratedDeriv2_nonpos_of_isLocalMax hlocal
      (hf.continuous.continuousAt.sub hpenC2.continuous.continuousAt)
  have hlin :
      iteratedDeriv 2 (fun x => f x - eps * x ^ 2) x₀ =
        iteratedDeriv 2 f x₀ -
          iteratedDeriv 2 (fun x : ℝ => eps * x ^ 2) x₀ :=
    iteratedDeriv_fun_sub hf.contDiffAt hpenC2.contDiffAt
  have hsq2 :
      iteratedDeriv 2 (fun x : ℝ => eps * x ^ 2) x₀ = 2 * eps := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
    ring
  have hf2 : iteratedDeriv 2 f x₀ = deriv (deriv f) x₀ := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hlin, hsq2, hf2] at hsecond_raw
  exact ⟨x₀, hmax, hvalue, hfirst, by linarith⟩

/-- One-sided Omori-type approximate maximum principle.  A positive value of
a `C²` function bounded only from above yields an almost-critical positive
value with arbitrarily small first and upper second derivative errors. -/
theorem exists_approx_positive_max_deriv_data_of_upperBound
    {f : ℝ → ℝ} {A eta x₁ : ℝ}
    (hf : ContDiff ℝ 2 f) (hA : ∀ x, f x ≤ A)
    (hpos : 0 < f x₁) (heta : 0 < eta) :
    ∃ x₀,
      f x₁ / 2 < f x₀ ∧
      |deriv f x₀| < eta ∧
      deriv (deriv f) x₀ < eta := by
  have hApos : 0 < A := lt_of_lt_of_le hpos (hA x₁)
  let D : ℝ := A + x₁ ^ 2 + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg x₁]
  let eps : ℝ :=
    min 1
      (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
        (min (eta / 2) (eta ^ 2 / (8 * D)))) / 2
  have hxden : 0 < 2 * (x₁ ^ 2 + 1) := by positivity
  have hetasq : 0 < eta ^ 2 := sq_pos_of_pos heta
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_one : eps < 1 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ 1 := min_le_left _ _
    nlinarith
  have heps_value : eps < f x₁ / (2 * (x₁ ^ 2 + 1)) := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤
          f x₁ / (2 * (x₁ ^ 2 + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    nlinarith [div_pos hpos hxden]
  have heps_eta : 2 * eps < eta := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    nlinarith
  have heps_sq : 4 * eps * D < eta ^ 2 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta ^ 2 / (8 * D) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hdiv : 0 < eta ^ 2 / (8 * D) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hmin
      (show 0 ≤ 4 * D by positivity)
    field_simp [ne_of_gt hD] at hmul
    nlinarith
  obtain ⟨x₀, _hmax, hvalue, hfirst, hsecond⟩ :=
    exists_penalized_max_deriv_data_of_upperBound
      hf hA hpos heps (x₁ := x₁)
  have hvalue_pos : f x₁ / 2 < f x₀ := by
    have hxfrac : eps * x₁ ^ 2 < f x₁ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right heps_value.le (sq_nonneg x₁)
      have hfrac :
          f x₁ / (2 * (x₁ ^ 2 + 1)) * x₁ ^ 2 < f x₁ / 2 := by
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hxden).2
        nlinarith [sq_nonneg x₁]
      exact lt_of_le_of_lt (by simpa [mul_assoc] using hmul) hfrac
    nlinarith [mul_nonneg heps.le (sq_nonneg x₀)]
  have hx₀bound : eps * x₀ ^ 2 < D := by
    have hf₀ := hA x₀
    have hepsx : eps * x₁ ^ 2 ≤ x₁ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg x₁) heps_one.le
    dsimp [D]
    nlinarith [hvalue, hpos]
  have hderiv_sq : (deriv f x₀) ^ 2 < eta ^ 2 := by
    rw [hfirst]
    calc
      (2 * eps * x₀) ^ 2 = 4 * eps * (eps * x₀ ^ 2) := by ring
      _ < 4 * eps * D := by
        exact mul_lt_mul_of_pos_left hx₀bound (by positivity)
      _ < eta ^ 2 := heps_sq
  have hderiv : |deriv f x₀| < eta := by
    rw [← sq_lt_sq₀ (abs_nonneg (deriv f x₀)) heta.le, sq_abs]
    exact hderiv_sq
  exact ⟨x₀, hvalue_pos, hderiv, lt_of_le_of_lt hsecond heps_eta⟩

/-- Continuous version of the penalized almost-maximum construction.  It
controls the first and second derivatives of the *quadratic penalty* itself;
this is useful when `f` has a corner which can subsequently be excluded by a
one-sided contact argument. -/
theorem exists_penalized_max_small_quadratic_errors
    {f : ℝ → ℝ} {A eta x₁ : ℝ}
    (hf : Continuous f) (hA : ∀ x, |f x| ≤ A)
    (hpos : 0 < f x₁) (heta : 0 < eta) :
    ∃ eps x₀,
      0 < eps ∧
      IsMaxOn (fun x => f x - eps * x ^ 2) Set.univ x₀ ∧
      f x₁ / 2 < f x₀ ∧
      |2 * eps * x₀| < eta ∧
      2 * eps < eta := by
  have hApos : 0 < A := lt_of_lt_of_le hpos (le_trans (le_abs_self (f x₁)) (hA x₁))
  let D : ℝ := 2 * A + x₁ ^ 2 + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg x₁]
  let eps : ℝ :=
    min 1
      (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
        (min (eta / 2) (eta ^ 2 / (8 * D)))) / 2
  have hxden : 0 < 2 * (x₁ ^ 2 + 1) := by positivity
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_one : eps < 1 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ 1 := min_le_left _ _
    nlinarith
  have heps_value : eps < f x₁ / (2 * (x₁ ^ 2 + 1)) := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤
          f x₁ / (2 * (x₁ ^ 2 + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    nlinarith [div_pos hpos hxden]
  have heps_eta : 2 * eps < eta := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    nlinarith
  have heps_sq : 4 * eps * D < eta ^ 2 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * (x₁ ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta ^ 2 / (8 * D) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hmul := mul_le_mul_of_nonneg_right hmin (show 0 ≤ 4 * D by positivity)
    field_simp [ne_of_gt hD] at hmul
    nlinarith
  obtain ⟨x₀, hmax, hvalue⟩ :=
    exists_isMaxOn_sub_mul_sq_of_bounded (x₁ := x₁) hf hA heps
  have hvalue_pos : f x₁ / 2 < f x₀ := by
    have hxfrac : eps * x₁ ^ 2 < f x₁ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right heps_value.le (sq_nonneg x₁)
      have hfrac :
          f x₁ / (2 * (x₁ ^ 2 + 1)) * x₁ ^ 2 < f x₁ / 2 := by
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hxden).2
        nlinarith [sq_nonneg x₁]
      exact lt_of_le_of_lt (by simpa [mul_assoc] using hmul) hfrac
    nlinarith [mul_nonneg heps.le (sq_nonneg x₀)]
  have hx₀bound : eps * x₀ ^ 2 < D := by
    have hf₀ : f x₀ ≤ A := (le_abs_self (f x₀)).trans (hA x₀)
    have hf₁ : -A ≤ f x₁ := neg_le_of_abs_le (hA x₁)
    have hepsx : eps * x₁ ^ 2 ≤ x₁ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg x₁) heps_one.le
    dsimp [D]
    nlinarith
  have hpenalty_sq : (2 * eps * x₀) ^ 2 < eta ^ 2 := by
    calc
      (2 * eps * x₀) ^ 2 = 4 * eps * (eps * x₀ ^ 2) := by ring
      _ < 4 * eps * D := mul_lt_mul_of_pos_left hx₀bound (by positivity)
      _ < eta ^ 2 := heps_sq
  have hpenalty : |2 * eps * x₀| < eta := by
    rw [← sq_lt_sq₀ (abs_nonneg (2 * eps * x₀)) heta.le, sq_abs]
    exact hpenalty_sq
  exact ⟨eps, x₀, heps, hmax, hvalue_pos, hpenalty, heps_eta⟩

section AxiomAudit

#print axioms exists_isMaxOn_sub_mul_sq_of_bounded
#print axioms exists_penalized_max_deriv_data
#print axioms exists_approx_positive_max_deriv_data
#print axioms exists_isMaxOn_sub_mul_sq_of_upperBound
#print axioms exists_penalized_max_deriv_data_of_upperBound
#print axioms exists_approx_positive_max_deriv_data_of_upperBound
#print axioms exists_penalized_max_small_quadratic_errors

end AxiomAudit

end ShenWork.Paper1
