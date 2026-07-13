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

section AxiomAudit

#print axioms exists_isMaxOn_sub_mul_sq_of_bounded
#print axioms exists_penalized_max_deriv_data

end AxiomAudit

end ShenWork.Paper1
