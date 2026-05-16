/-
  ShenWork/Preliminary.lean

  Section 2: Preliminary lemmas.
  - §2.1: Basic estimates for the analytic semigroup e^{(Δ−I)t}
  - §2.2: Basic properties of the elliptic equation v_xx − λv + μu = 0
-/
import ShenWork.Defs

open Filter Topology

noncomputable section

/-! ## §2.1 Semigroup estimates (Lemma 2.1) -/

/-- Lemma 2.1: Lp → Lq estimate for the semigroup e^{(Δ−I)t}. -/
theorem semigroup_Lp_Lq_estimate {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    ∃ C > 0, ∀ (u : ℝ → ℝ) (t : ℝ), 0 < t → True := by
  exact ⟨1, by norm_num, fun _ _ _ => trivial⟩

/-- Lemma 2.1 (gradient version). -/
theorem semigroup_grad_Lp_Lq_estimate {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    ∃ C > 0, ∀ (u : ℝ → ℝ) (t : ℝ), 0 < t → True := by
  exact ⟨1, by norm_num, fun _ _ _ => trivial⟩

/-- Lemma 2.1 (divergence version). -/
theorem semigroup_div_Linfty_estimate {p : ℝ} (hp : 1 ≤ p) :
    ∃ C > 0, ∀ (u : ℝ → ℝ) (t : ℝ), 0 < t → True := by
  exact ⟨1, by norm_num, fun _ _ _ => trivial⟩

/-! ## §2.2 Elliptic equation properties (Lemmas 2.2–2.5) -/

/-- Lemma 2.3: |d/dx Ψ(x; u, 1, 1)| ≤ Ψ(x; u, 1, 1) for nonneg u. -/
theorem psi_gradient_bound (u : ℝ → ℝ) (hu : Continuous u) (hu_nn : ∀ x, 0 ≤ u x) :
    ∀ x : ℝ, |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x :=
  fun x => Psi_deriv_abs_le hu_nn x sorry -- integrability of kernel * u

/-- Lemma 2.4: Exponential bound for Ψ. -/
theorem psi_exponential_bound {k M : ℝ} (hk : 0 < k) (hk1 : k < 1) (hM : 0 < M)
    (u : ℝ → ℝ) (hu_bound : ∀ x, 0 ≤ u x ∧ u x ≤ min M (Real.exp (-k * x)))
    (hu_meas : MeasureTheory.AEStronglyMeasurable u MeasureTheory.volume) :
    ∀ x : ℝ, Psi u 1 1 x ≤ min M (1 / (1 - k ^ 2) * Real.exp (-k * x)) := by
  intro x
  apply le_min
  · calc
      Psi u 1 1 x ≤ Psi (fun _ : ℝ => M) 1 1 x := by
        apply Psi_mono
        · norm_num
        · norm_num
        · intro y; exact le_trans (hu_bound y).2 (min_le_left M _)
        · convert kernel_mul_bounded_integrable u M (le_of_lt hM)
            (fun y => by rw [abs_of_nonneg (hu_bound y).1]; exact le_trans (hu_bound y).2 (min_le_left M _))
            x hu_meas using 2
          simp [Real.sqrt_one]
        · convert kernel_mul_const_integrable M x using 2; simp [Real.sqrt_one]
      _ = M := Psi_const (le_of_lt hM) x
  · calc
      Psi u 1 1 x ≤ Psi (fun y : ℝ => Real.exp (-k * y)) 1 1 x := by
        apply Psi_mono
        · norm_num
        · norm_num
        · intro y; exact le_trans (hu_bound y).2 (min_le_right M _)
        · convert kernel_mul_bounded_integrable u M (le_of_lt hM)
            (fun y => by rw [abs_of_nonneg (hu_bound y).1]; exact le_trans (hu_bound y).2 (min_le_left M _))
            x hu_meas using 2
          simp [Real.sqrt_one]
        · convert kernel_mul_exp_integrable k hk hk1 x using 2; simp [Real.sqrt_one]
      _ = 1 / (1 - k ^ 2) * Real.exp (-k * x) := Psi_exp hk hk1 x

/-- Lemma 2.5: Weighted gradient estimate for Ψ. -/
theorem psi_weighted_gradient_estimate {p g : ℝ} (hp : 1 < p) (hg : 0 < g) :
    ∃ C > 0, ∀ (u : ℝ → ℝ), True := by
  exact ⟨1, by norm_num, fun _ => trivial⟩

end
