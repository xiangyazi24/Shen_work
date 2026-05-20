/-
  ShenWork/Preliminary.lean

  Section 2: Preliminary lemmas.
  - §2.1: Basic estimates for the analytic semigroup e^{(Δ−I)t}
  - §2.2: Basic properties of the elliptic equation v_xx − λv + μu = 0
-/
import ShenWork.Defs
import ShenWork.PDE.LeibnizRule

open Filter Topology

noncomputable section

/-! ## §2.1 Semigroup estimates (Lemma 2.1) -/

/- The actual Paper1 Lemma 2.1 estimate target is `Paper1.Lemma_2_1`
in `Paper1/Statements.lean`; this file keeps only non-vacuous reusable facts. -/

/-! ## §2.2 Elliptic equation properties (Lemmas 2.2–2.5) -/

/-- Lemma 2.3: |d/dx Ψ(x; u, 1, 1)| ≤ Ψ(x; u, 1, 1) for nonneg u. -/
theorem psi_gradient_bound (u : ℝ → ℝ) (hu : Continuous u) (hu_nn : ∀ x, 0 ≤ u x)
    (hu_bdd : IsBddFun u) :
    ∀ x : ℝ, |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x := by
  intro x
  obtain ⟨M, hM⟩ := hu_bdd
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  have hint : MeasureTheory.Integrable (fun y => Real.exp (-|x - y|) * u y) := by
    have h := kernel_mul_bounded_integrable u M hM_nn hM x hu.aestronglyMeasurable
    convert h using 2 with y; simp [neg_one_mul]
  exact Psi_deriv_abs_le' hu_nn x hint hu.aestronglyMeasurable

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

end
