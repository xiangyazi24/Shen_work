import ShenWork.Paper1.WaveApproxMaximum

open Filter Topology Real Set

noncomputable section

namespace ShenWork.Paper1

/-- Omori-type approximate maximum principle with one excluded regularity
point.  A small translated quadratic penalty is chosen so its derivative at
the bad point cannot agree with that of `f`; hence the maximizing contact lies
in the `C²` region. -/
theorem exists_approx_positive_max_deriv_data_away
    {f : ℝ → ℝ} {A eta x₁ a : ℝ}
    (hf1 : ContDiff ℝ 1 f)
    (hf2 : ∀ x, x ≠ a → DifferentiableAt ℝ (deriv f) x)
    (hA : ∀ x, |f x| ≤ A)
    (hpos : 0 < f x₁) (heta : 0 < eta) :
    ∃ x₀, x₀ ≠ a ∧
      f x₁ / 2 < f x₀ ∧
      |deriv f x₀| < eta ∧
      deriv (deriv f) x₀ < eta := by
  let b : ℝ := if deriv f a ≠ 0 then a else a + 1
  have hApos : 0 < A :=
    lt_of_lt_of_le hpos (le_trans (le_abs_self (f x₁)) (hA x₁))
  let D : ℝ := 2 * A + (x₁ - b) ^ 2 + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg (x₁ - b)]
  let eps : ℝ :=
    min 1
      (min (f x₁ / (2 * ((x₁ - b) ^ 2 + 1)))
        (min (eta / 2) (eta ^ 2 / (8 * D)))) / 2
  have hxden : 0 < 2 * ((x₁ - b) ^ 2 + 1) := by positivity
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_one : eps < 1 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * ((x₁ - b) ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ 1 := min_le_left _ _
    nlinarith
  have heps_value :
      eps < f x₁ / (2 * ((x₁ - b) ^ 2 + 1)) := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * ((x₁ - b) ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤
          f x₁ / (2 * ((x₁ - b) ^ 2 + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    nlinarith [div_pos hpos hxden]
  have heps_eta : 2 * eps < eta := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * ((x₁ - b) ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    nlinarith
  have heps_sq : 4 * eps * D < eta ^ 2 := by
    dsimp [eps]
    have hmin : min 1
        (min (f x₁ / (2 * ((x₁ - b) ^ 2 + 1)))
          (min (eta / 2) (eta ^ 2 / (8 * D)))) ≤ eta ^ 2 / (8 * D) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hmul := mul_le_mul_of_nonneg_right hmin
      (show 0 ≤ 4 * D by positivity)
    field_simp [ne_of_gt hD] at hmul
    nlinarith
  let ft : ℝ → ℝ := fun y => f (y + b)
  have hft : Continuous ft := hf1.continuous.comp
    (continuous_id.add continuous_const)
  have hftA : ∀ y, |ft y| ≤ A := fun y => hA (y + b)
  obtain ⟨y₀, hymax, hyvalue⟩ :=
    exists_isMaxOn_sub_mul_sq_of_bounded
      (f := ft) (A := A) (eps := eps) (x₁ := x₁ - b) hft hftA heps
  let x₀ : ℝ := y₀ + b
  have hmax : IsMaxOn (fun x => f x - eps * (x - b) ^ 2) Set.univ x₀ := by
    rw [isMaxOn_univ_iff]
    intro x
    have h := (isMaxOn_univ_iff.mp hymax) (x - b)
    simpa [ft, x₀] using h
  have hvalue :
      f x₁ - eps * (x₁ - b) ^ 2 ≤
        f x₀ - eps * (x₀ - b) ^ 2 := by
    simpa [ft, x₀] using hyvalue
  have hlocal : IsLocalMax (fun x => f x - eps * (x - b) ^ 2) x₀ :=
    hmax.isLocalMax Filter.univ_mem
  have hf0 : HasDerivAt f (deriv f x₀) x₀ :=
    (hf1.differentiable (by norm_num) x₀).hasDerivAt
  have hpen0 : HasDerivAt (fun x : ℝ => eps * (x - b) ^ 2)
      (2 * eps * (x₀ - b)) x₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x₀).sub_const b).pow 2).const_mul eps
  have hfirst : deriv f x₀ = 2 * eps * (x₀ - b) := by
    have hzero : deriv (fun x => f x - eps * (x - b) ^ 2) x₀ = 0 :=
      hlocal.deriv_eq_zero
    have heq : deriv (fun x => f x - eps * (x - b) ^ 2) x₀ =
        deriv f x₀ - 2 * eps * (x₀ - b) := by
      simpa only [Pi.sub_apply] using (hf0.sub hpen0).deriv
    rw [heq] at hzero
    linarith
  have hx₀ne : x₀ ≠ a := by
    intro heq
    have hscaled : deriv f a = eps * (2 * (a - b)) := by
      rw [← heq]
      rw [hfirst]
      ring
    by_cases hder : deriv f a = 0
    · have hb : b = a + 1 := by simp [b, hder]
      rw [hder, hb] at hscaled
      nlinarith
    · have hb : b = a := by simp [b, hder]
      rw [hb] at hscaled
      simp at hscaled
      exact hder hscaled
  have hpenC2 : ContDiff ℝ 2 (fun x : ℝ => eps * (x - b) ^ 2) := by
    fun_prop
  have hsecond_raw :
      iteratedDeriv 2 (fun x => f x - eps * (x - b) ^ 2) x₀ ≤ 0 :=
    iteratedDeriv2_nonpos_of_isLocalMax hlocal
      (hf1.continuous.continuousAt.sub hpenC2.continuous.continuousAt)
  have hlin :
      iteratedDeriv 2 (fun x => f x - eps * (x - b) ^ 2) x₀ =
        iteratedDeriv 2 f x₀ -
          iteratedDeriv 2 (fun x : ℝ => eps * (x - b) ^ 2) x₀ := by
    let P : ℝ → ℝ := fun x => eps * (x - b) ^ 2
    have hderivEq : deriv (fun x => f x - P x) =
        fun x => deriv f x - deriv P x := by
      funext x
      exact (((hf1.differentiable (by norm_num) x).hasDerivAt).sub
        ((hpenC2.differentiable (by norm_num) x).hasDerivAt)).deriv
    have hiter (g : ℝ → ℝ) :
        iteratedDeriv 2 g x₀ = deriv (deriv g) x₀ := by
      simp [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hiter (fun x => f x - P x), hiter f, hiter P]
    rw [hderivEq]
    have hf2has : HasDerivAt (deriv f) (deriv (deriv f) x₀) x₀ :=
      (hf2 x₀ hx₀ne).hasDerivAt
    have hp2has : HasDerivAt (deriv P) (deriv (deriv P) x₀) x₀ :=
      (hpenC2.differentiable_deriv_two x₀).hasDerivAt
    simpa only [Pi.sub_apply] using (hf2has.sub hp2has).deriv
  have hpen2 :
      iteratedDeriv 2 (fun x : ℝ => eps * (x - b) ^ 2) x₀ =
        2 * eps := by
    have hfirstfun : deriv (fun x : ℝ => eps * (x - b) ^ 2) =
        fun x => 2 * eps * (x - b) := by
      funext x
      exact (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          ((((hasDerivAt_id x).sub_const b).pow 2).const_mul eps).deriv)
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
    rw [hfirstfun]
    have hd : HasDerivAt (fun x : ℝ => 2 * eps * (x - b))
        (2 * eps) x₀ := by
      convert ((hasDerivAt_id x₀).sub_const b).const_mul (2 * eps) using 1
      <;> ring
    exact hd.deriv
  have hfsecond : iteratedDeriv 2 f x₀ = deriv (deriv f) x₀ := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hlin, hpen2, hfsecond] at hsecond_raw
  have hvalue_pos : f x₁ / 2 < f x₀ := by
    have hxfrac : eps * (x₁ - b) ^ 2 < f x₁ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right heps_value.le
        (sq_nonneg (x₁ - b))
      have hfrac :
          f x₁ / (2 * ((x₁ - b) ^ 2 + 1)) * (x₁ - b) ^ 2 <
            f x₁ / 2 := by
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hxden).2
        nlinarith [sq_nonneg (x₁ - b)]
      exact lt_of_le_of_lt (by simpa [mul_assoc] using hmul) hfrac
    nlinarith [mul_nonneg heps.le (sq_nonneg (x₀ - b))]
  have hy₀bound : eps * (x₀ - b) ^ 2 < D := by
    have hfx₀ : f x₀ ≤ A := (le_abs_self (f x₀)).trans (hA x₀)
    have hfx₁ : -A ≤ f x₁ := neg_le_of_abs_le (hA x₁)
    have hepsy : eps * (x₁ - b) ^ 2 ≤ (x₁ - b) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg (x₁ - b)) heps_one.le
    dsimp [D]
    nlinarith
  have hderiv_sq : (deriv f x₀) ^ 2 < eta ^ 2 := by
    rw [hfirst]
    calc
      (2 * eps * (x₀ - b)) ^ 2 =
          4 * eps * (eps * (x₀ - b) ^ 2) := by ring
      _ < 4 * eps * D := mul_lt_mul_of_pos_left hy₀bound (by positivity)
      _ < eta ^ 2 := heps_sq
  have hderiv : |deriv f x₀| < eta := by
    rw [← sq_lt_sq₀ (abs_nonneg (deriv f x₀)) heta.le, sq_abs]
    exact hderiv_sq
  exact ⟨x₀, hx₀ne, hvalue_pos, hderiv, by linarith⟩

section AxiomAudit

#print axioms exists_approx_positive_max_deriv_data_away

end AxiomAudit

end ShenWork.Paper1
