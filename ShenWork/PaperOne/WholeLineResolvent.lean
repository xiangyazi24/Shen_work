import ShenWork.PDE.LeibnizRule
open MeasureTheory Filter Topology
noncomputable section
def wholeLineResolventKernel (z : ℝ) : ℝ := (1 / 2) * Real.exp (-|z|)
def wholeLineResolvent (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, wholeLineResolventKernel (x - y) * f y
theorem wholeLineResolvent_eq_Psi (f : ℝ → ℝ) (x : ℝ) :
    wholeLineResolvent f x = Psi f 1 1 x := by
  unfold wholeLineResolvent wholeLineResolventKernel Psi
  rw [show (fun y : ℝ => (1 / 2 * Real.exp (-|x - y|)) * f y) =
      fun y => (1 / 2 : ℝ) * (Real.exp (-(1 : ℝ) * |x - y|) * f y) by funext y; ring_nf]
  rw [MeasureTheory.integral_const_mul]
  norm_num [Real.sqrt_one]
theorem wholeLineResolventKernel_mass_one :
    ∫ z : ℝ, wholeLineResolventKernel z = 1 := by
  calc
    ∫ z : ℝ, wholeLineResolventKernel z = wholeLineResolvent (fun _ : ℝ => 1) 0 := by
      simp [wholeLineResolvent, wholeLineResolventKernel, abs_neg]
    _ = Psi (fun _ : ℝ => 1) 1 1 0 := wholeLineResolvent_eq_Psi _ _
    _ = 1 := Psi_const (c := 1) (by norm_num) 0
theorem wholeLineResolventKernel_nonneg (z : ℝ) :
    0 ≤ wholeLineResolventKernel z := by unfold wholeLineResolventKernel; positivity
theorem wholeLineResolvent_nonneg {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) (x : ℝ) :
    0 ≤ wholeLineResolvent f x := by
  unfold wholeLineResolvent
  exact integral_nonneg fun y => mul_nonneg (wholeLineResolventKernel_nonneg (x - y)) (hf y)
theorem wholeLineResolvent_sup_le {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf_cont : Continuous f) (hfM : ∀ y, |f y| ≤ M) :
    ∀ x, |wholeLineResolvent f x| ≤ M := by
  intro x
  rw [wholeLineResolvent_eq_Psi]
  have hiu : Integrable (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * f y) :=
    psi_kernel_mul_bounded_integrable one_pos hM hfM x hf_cont.aestronglyMeasurable
  have hupper := Psi_le_const_general_of_le (u := f) (l := 1) (mu := 1) one_pos one_pos hM
    (fun y => (le_abs_self (f y)).trans (hfM y)) x hiu
  have hfM_neg : ∀ y, |(-f y)| ≤ M := by intro y; simpa using hfM y
  have hineg : Integrable (fun y => Real.exp (-Real.sqrt 1 * |x - y|) * (-f y)) :=
    psi_kernel_mul_bounded_integrable one_pos hM hfM_neg x hf_cont.neg.aestronglyMeasurable
  have hneg := Psi_le_const_general_of_le (u := fun y => -f y) (l := 1) (mu := 1) one_pos
    one_pos hM (fun y => (le_abs_self (-f y)).trans (hfM_neg y)) x hineg
  rw [Psi_neg] at hneg
  rw [abs_le]
  exact ⟨by linarith, by simpa using hupper⟩
private theorem wholeLineResolvent_hasDerivAt {f : ℝ → ℝ} (hf : IsCUnifBdd f) (x : ℝ) :
    HasDerivAt (wholeLineResolvent f)
      ((1 / 2 : ℝ) * ∫ y,
        if y ≤ x then -(1 : ℝ) * Real.exp (-(1 : ℝ) * (x - y)) * f y
        else (1 : ℝ) * Real.exp (-(1 : ℝ) * (y - x)) * f y) x := by
  have h := hasDerivAt_integral_exp_neg_mul_abs_sub_general (u := f) (a := 1) one_pos hf x
  have hfun : wholeLineResolvent f =
      fun z => (1 / 2 : ℝ) * ∫ y, Real.exp (-(1 : ℝ) * |z - y|) * f y := by
    funext z; rw [wholeLineResolvent_eq_Psi]; simp [Psi, Real.sqrt_one]
  simpa [hfun] using h.const_mul (1 / 2 : ℝ)
theorem wholeLineResolventDeriv_sup_le {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf_cont : Continuous f) (hfM : ∀ y, |f y| ≤ M) :
    ∀ x, |deriv (wholeLineResolvent f) x| ≤ M := by
  intro x
  let F' : ℝ → ℝ := fun y =>
    if y ≤ x then -(1 : ℝ) * Real.exp (-(1 : ℝ) * (x - y)) * f y
    else (1 : ℝ) * Real.exp (-(1 : ℝ) * (y - x)) * f y
  have hf : IsCUnifBdd f := ⟨hf_cont, ⟨M, hfM⟩⟩
  have hder := wholeLineResolvent_hasDerivAt hf x
  have hdom : Integrable (fun y => Real.exp (-|x - y|) * M) := by
    simpa using kernel_mul_const_integrable M x
  have hpoint : ∀ y, ‖F' y‖ ≤ Real.exp (-|x - y|) * M := by
    intro y
    by_cases hy : y ≤ x
    · have habs : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr hy)
      calc
        ‖F' y‖ = Real.exp (-(x - y)) * |f y| := by simp [F', hy, Real.norm_eq_abs]
        _ ≤ Real.exp (-|x - y|) * M := by
          rw [habs]; exact mul_le_mul_of_nonneg_left (hfM y) (Real.exp_nonneg _)
    · have hxy : x < y := lt_of_not_ge hy
      have habs : |x - y| = y - x := by rw [abs_of_neg (sub_neg.mpr hxy)]; ring
      calc
        ‖F' y‖ = Real.exp (-(y - x)) * |f y| := by simp [F', hy, Real.norm_eq_abs]
        _ ≤ Real.exp (-|x - y|) * M := by
          rw [habs]; exact mul_le_mul_of_nonneg_left (hfM y) (Real.exp_nonneg _)
  have hInt : |∫ y, F' y| ≤ ∫ y, Real.exp (-|x - y|) * M := by
    calc
      |∫ y, F' y| ≤ ∫ y, ‖F' y‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, Real.exp (-|x - y|) * M := by
        exact integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hdom
          (Eventually.of_forall hpoint)
  have hmassM : (1 / 2 : ℝ) * ∫ y, Real.exp (-|x - y|) * M = M := by
    have h := Psi_const (c := M) hM x
    unfold Psi at h; simpa [Real.sqrt_one] using h
  rw [hder.deriv, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact (mul_le_mul_of_nonneg_left hInt (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq hmassM
theorem wholeLineResolvent_second_deriv {f : ℝ → ℝ}
    (hf : IsCUnifBdd f) (hf_nonneg : ∀ x, 0 ≤ f x) (x : ℝ) :
    deriv (deriv (wholeLineResolvent f)) x = wholeLineResolvent f x - f x := by
  have hiter : iteratedDeriv 2 (fun z => Psi f 1 1 z) x = Psi f 1 1 x - f x := by
    have h := Psi_elliptic_ode (u := f) (l := 1) (mu := 1) one_pos one_pos hf hf_nonneg x
    linarith
  have hfun : wholeLineResolvent f = fun z => Psi f 1 1 z := by
    funext z; exact wholeLineResolvent_eq_Psi f z
  rw [hfun]
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hiter
